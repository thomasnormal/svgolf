#!/usr/bin/env python3
"""encode.py: the site's layout picture and thumbnail from a job's PNG render (score/pnr/README.md).

    python3.12 -I score/pnr/encode.py JOBDIR/img/JOB.png OUTDIR TASK SV16 [--json OUT.json]

Writes OUTDIR/TASK/SV16.webp (the picture) and OUTDIR/TASK/SV16.thumb.webp (the thumbnail), SV16 being the first 16
hex of the design file's sha256 (the name leaderboard/asap7pnr and site/layouts use), and prints (or writes to
--json) the record the routed entry's `layout` takes from them: the PNG's sha256 and pixel size, the picture's and the
thumbnail's sha256, bytes, pixel size, and the picture's WebP quality.

Encoding (the campaigns' encode_images.py, unchanged but for this interface): lossy WebP, method 6, at the LARGEST long
side of 1600 (as rendered), 1400, 1200, 1000 or 800 px (Lanczos) that fits: the highest quality of 80, 75, ..., 50 whose
file is at most 300,000 bytes; the thumbnail is the render at 640 px on the long side (Lanczos), quality 80, method 6.
No time and no metadata go in, so the same PNG bytes and the same Pillow and libwebp give the same files: the committed
pictures were made with Pillow 11.1.0 and libwebp 1.5.0 (`pillow_version()` says which are here). The PNG is read as
data (RGB); nothing in it is executed. Needs Pillow."""

import argparse
import hashlib
import io
import json
import os
import sys

LIMIT = 300_000
QUALITIES = list(range(80, 49, -5))
SIZES = (None, 1400, 1200, 1000, 800)
THUMB = 640
THUMB_QUALITY = 80
COMMITTED_WITH = ("11.1.0", "1.5.0")      # Pillow, libwebp: what the committed pictures were encoded with


def pillow_version():
    """(Pillow's version, its libwebp's version), or None without Pillow."""
    try:
        import PIL
        from PIL import features
    except ImportError:
        return None
    return PIL.__version__, features.version("webp")


def _sha(b):
    return hashlib.sha256(b).hexdigest()


def _webp(im, q):
    buf = io.BytesIO()
    im.save(buf, format="WEBP", quality=q, method=6, exact=False)
    return buf.getvalue()


def _scaled(im, long_side):
    from PIL import Image
    w, h = im.size
    if long_side is None or max(w, h) <= long_side:
        return im
    f = long_side / max(w, h)
    return im.resize((max(1, round(w * f)), max(1, round(h * f))), Image.Resampling.LANCZOS)


def encode(png):
    """(picture bytes, thumbnail bytes, record) of the PNG bytes `png`. The record: png_sha256, png_px, px, quality,
    bytes, sha256, thumb_px, thumb_bytes, thumb_sha256."""
    from PIL import Image
    im = Image.open(io.BytesIO(png)).convert("RGB")
    pic = None
    for size in SIZES:
        imz = _scaled(im, size)
        for q in QUALITIES:
            b = _webp(imz, q)
            if len(b) <= LIMIT:
                pic = (b, q, imz.size)
                break
        if pic:
            break
    if pic is None:
        raise ValueError(f"no encoding of at most {LIMIT} bytes")
    th_im = _scaled(im, THUMB)
    th = _webp(th_im, THUMB_QUALITY)
    b, q, size = pic
    return b, th, {"png_sha256": _sha(png), "png_px": list(im.size), "px": list(size), "quality": q, "bytes": len(b),
                   "sha256": _sha(b), "thumb_px": list(th_im.size), "thumb_bytes": len(th), "thumb_sha256": _sha(th)}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("png")
    ap.add_argument("out_dir")
    ap.add_argument("task")
    ap.add_argument("sv16")
    ap.add_argument("--json", help="write the record here (else stdout)")
    args = ap.parse_args(argv)
    if pillow_version() is None:
        print("error: encode.py needs Pillow", file=sys.stderr)
        return 2
    with open(args.png, "rb") as fh:
        png = fh.read()
    pic, thumb, rec = encode(png)
    d = os.path.join(args.out_dir, args.task)
    os.makedirs(d, exist_ok=True)
    rec = dict(rec, file=f"{args.task}/{args.sv16}.webp", thumb=f"{args.task}/{args.sv16}.thumb.webp",
               pillow=pillow_version()[0], libwebp=pillow_version()[1])
    for name, blob in ((f"{args.sv16}.webp", pic), (f"{args.sv16}.thumb.webp", thumb)):
        with open(os.path.join(d, name), "wb") as fh:
            fh.write(blob)
    text = json.dumps(rec, indent=1, sort_keys=True) + "\n"
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    if pillow_version() != COMMITTED_WITH:
        print(f"note: Pillow {pillow_version()[0]} / libwebp {pillow_version()[1]}: the committed pictures were made "
              f"with Pillow {COMMITTED_WITH[0]} / libwebp {COMMITTED_WITH[1]}; the bytes may differ", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
