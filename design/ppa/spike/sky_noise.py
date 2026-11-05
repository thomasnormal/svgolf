#!/usr/bin/env python3.12
"""STRUCTURE NOISE of the scores (WP-X1): the same circuit written differently -- tests/canon/variants.py's layout,
rename, order and commute variants (imported read-only) -- through the pinned flow (legacy GE, depth), flow A0' and
flow A1' (u, s). Layout and rename variants must give a byte-identical canonical RTLIL (no noise by construction);
order and commute may not. The spread over variants is the noise floor a board must not rank below.

  python3.12 sky_noise.py [--designs add_sklansky ...] [--variants commute reverse hoist shuffle1 ...] [--workers 3]
      -> data/sky130/noise_N16.json
"""
import argparse, concurrent.futures as cf, hashlib, json, os, sys
import netlist as N, sky130 as S, sky130_designs as SD, sky_flow as F, sky_gen as G, sky_measure as M

sys.path.insert(0, os.path.join(SD.D.SVGOLF, "tests", "canon"))
import variants as V   # noqa: E402  (read-only import of the repository's own variant generator)

DEFAULT_DESIGNS = ["add_ripple", "add_sklansky", "add_kogge", "mul_array", "mul_tree_h", "mul_tree", "sbox_bp"]
DEFAULT_VARIANTS = ["oneline", "ren_random", "hoist", "reverse", "shuffle1", "shuffle2", "shuffle3", "shuffle4", "commute"]


def job(d, vname, vpath, lib):
    dd = dict(d, src=vpath, tag=f"{d['name']}__{vname}")
    base = os.path.join(SD.CACHE, "var")
    r = G.run(dd, base)
    nl = N.load(os.path.join(base, "netlists", dd["tag"] + ".v"))
    des = M.build(S.expand_generic_sky(nl), lib)
    m0 = M.static(des, lib)
    il = os.path.join(base, "rtlil", dd["tag"] + ".il")
    res = dict(name=d["name"], variant=vname, ge=r["area_ge"], depth=r["depth"], rtlil_sha256=r["rtlil_sha256"],
               a0_um2=m0["area_um2"], a0_t_ps=m0["t_ps"])
    for v in ("u", "s"):
        out = os.path.join(base, "a1", f"{dd['tag']}.{v}.v")
        F.run(il, d["top"], out, v, lib)
        m = M.static(M.build(N.load(out), lib), lib)
        res[f"a1{v}_um2"] = m["area_um2"]; res[f"a1{v}_t_ps"] = m["t_ps"]; res[f"a1{v}_cells"] = m["cells"]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--designs", nargs="*", default=DEFAULT_DESIGNS)
    ap.add_argument("--variants", nargs="*", default=DEFAULT_VARIANTS)
    ap.add_argument("--workers", type=int, default=3)
    a = ap.parse_args()
    lib = S.load_lib()
    jobs = []
    for name in a.designs:
        d = SD.get(name)
        paths = V.make_variants(d["src"], d["top"], os.path.join(SD.CACHE, "variants", name), a.variants)
        jobs.append((d, "base", d["src"]))
        for vn, p in paths.items():
            jobs.append((d, vn, p))
    rows = []
    with cf.ThreadPoolExecutor(a.workers) as ex:
        for f in cf.as_completed([ex.submit(job, d, vn, p, lib) for d, vn, p in jobs]):
            rows.append(f.result())
            r = rows[-1]
            print(f"{r['name']:14s} {r['variant']:10s} GE {r['ge']:9.3f} d {r['depth']:3d} | A0' {r['a0_um2']:8.1f} {r['a0_t_ps']:7.1f} | u {r['a1u_um2']:8.1f} {r['a1u_t_ps']:7.1f} | s {r['a1s_um2']:8.1f} {r['a1s_t_ps']:7.1f}", flush=True)
    rows.sort(key=lambda r: (r["name"], r["variant"]))
    with open(os.path.join(SD.DATA, "noise_N16.json"), "w") as fh:
        json.dump({"rows": rows}, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
