#!/usr/bin/env python3.12
"""Fetch the Nangate45 (FreePDK45-derived) typical-corner liberty file at a PINNED
commit of OpenROAD-flow-scripts and verify its sha256. 6.7 MB, one file, no archive.

  python3.12 fetch_lib.py            # downloads to .cache/ if missing, prints the path
  PPA_NANGATE45_LIB=/path/to/file.lib   # use an existing copy (hash is still checked)
"""
import hashlib, os, sys, urllib.request

COMMIT = "6c6fc7e21b2d0b5b88b1a52d0a5860ea4d88e9e5"
URL = ("https://raw.githubusercontent.com/The-OpenROAD-Project/OpenROAD-flow-scripts/"
       f"{COMMIT}/flow/platforms/nangate45/lib/NangateOpenCellLibrary_typical.lib")
SHA256 = "8d540a4d4cf6d09d27c87ad067857a9c0c2eeb023ab7a56e058cd3113db4e9b1"
GIT_BLOB_SHA1 = "90e4afb274cfc6514c587c434c77903d554117d1"   # as listed by the GitHub contents API
HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.path.join(HERE, ".cache")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def lib_path():
    p = os.environ.get("PPA_NANGATE45_LIB") or os.path.join(CACHE, "NangateOpenCellLibrary_typical.lib")
    if not os.path.exists(p):
        os.makedirs(os.path.dirname(p), exist_ok=True)
        print(f"downloading {URL}", file=sys.stderr)
        urllib.request.urlretrieve(URL, p)
    if sha256(p) != SHA256:
        raise SystemExit(f"{p}: sha256 {sha256(p)} != pinned {SHA256}")
    return p


if __name__ == "__main__":
    print(lib_path())
