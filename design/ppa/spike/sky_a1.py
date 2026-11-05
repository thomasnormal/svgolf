#!/usr/bin/env python3.12
"""Flow A1' sweep (WP-X1): every design x mapper variant (sky_flow.py), measured under the fixed setup.

  python3.12 sky_a1.py [--n 16] [--variants u s f l h r] [--workers 3] [--only NAME ...] [--tag X]
      -> data/sky130/a1_N16<tag>.json     mapped netlists in .cache/sky130/a1/
"""
import argparse, concurrent.futures as cf, hashlib, json, os, sys, time
import netlist as N, sky130 as S, sky130_designs as SD, sky_flow as F, sky_measure as M

def one(d, v, lib, out_dir):
    il = os.path.join(SD.CACHE, "rtlil", d["tag"] + ".il")
    out = os.path.join(out_dir, f"{d['tag']}.{v}.v")
    r = F.run(il, d["top"], out, v, lib)
    return d, v, out, r

def measure(d, v, out, r, lib):
    nl = N.load(out)
    hist, bad = S.policy_report(nl, lib)
    des = M.build(nl, lib)
    m = M.static(des, lib)
    m.update(name=d["name"], variant=v, yosys_seconds=round(r["seconds"], 2), abc_stime_ps=r["abc_stime_ps"],
             stat_area_um2=r["stat_area_um2"], policy_violations=bad,
             netlist_sha256=hashlib.sha256(open(out, "rb").read()).hexdigest(),
             has_constants=("1'h" in open(out).read()))
    return m

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--variants", nargs="*", default=["u", "s", "f", "l", "h", "r"])
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--tag", default="")
    ap.add_argument("--outdir", default=os.path.join(SD.CACHE, "a1"))
    a = ap.parse_args()
    lib = S.load_lib()
    jobs = [(d, v) for d in SD.all_designs(a.n) if not a.only or d["name"] in a.only for v in a.variants]
    rows = []
    t0 = time.time()
    with cf.ThreadPoolExecutor(a.workers) as ex:
        futs = [ex.submit(one, d, v, lib, a.outdir) for d, v in jobs]
        for f in cf.as_completed(futs):
            d, v, out, r = f.result()
            m = measure(d, v, out, r, lib)
            rows.append(m)
            print(f"{d['tag']:18s} {v:2s} cells {m['cells']:5d} area {m['area_um2']:9.2f} um2 {m['area_ge']:8.2f} GE depth {m['unit_depth']:3d} "
                  f"T {m['t_ps']:8.1f} ps  yosys {m['yosys_seconds']:5.1f}s  viol {m['policy_violations'] or ''}", flush=True)
    rows.sort(key=lambda r: (r["name"], r["variant"]))
    os.makedirs(SD.DATA, exist_ok=True)
    with open(os.path.join(SD.DATA, f"a1_N{a.n}{a.tag}.json"), "w") as fh:
        json.dump({"pi_slew_ns": S.PI_SLEW_NS, "po_load_pf": S.PO_LOAD_PF, "dont_use": S.DONT_USE, "scripts": F.SCRIPTS,
                   "workers": a.workers, "wall_seconds": round(time.time() - t0, 1), "rows": rows}, fh, indent=1, sort_keys=True)

if __name__ == "__main__":
    main()
