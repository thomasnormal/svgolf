#!/usr/bin/env python3.12
"""Flow A0' (WP-X1): the PINNED `abc -g` scored netlist, every gate re-expressed as ONE sky130_fd_sc_hd _1 cell
(ANDNOT -> nor2b_1, ORNOT -> nand2b_1), measured under the fixed setup.

  python3.12 sky_a0.py [--n 16] [--energy]        # -> data/sky130/a0_N16.json
"""
import argparse, json, os, sys, time
import engine as E, netlist as N, sky130 as S, sky130_designs as SD, sky_measure as M

def a0(d, lib, energy=False, pairs=0, seed=1):
    p = os.path.join(SD.CACHE, "netlists", d["tag"] + ".v")
    nl = N.load(p)
    # NB engine.generic_depth (WP-X0) can UNDER-count on reconvergent DAGs (its reversed pre-order is not a topological
    # order): sbox_bp gives 18 against ltp's 21. The pinned score's ltp depth and Design.unit_depth() are used instead.
    pinned = json.load(open(os.path.join(SD.CACHE, "netlists", d["tag"] + ".score.json")))
    gd = pinned["depth"]
    t0 = time.time()
    x = S.expand_generic_sky(nl)
    des = M.build(x, lib)
    r = M.static(des, lib)
    r["generic_depth"] = gd
    assert r["unit_depth"] == gd, (d["tag"], r["unit_depth"], gd)
    r["seconds_measure"] = round(time.time() - t0, 3)
    if energy:
        r.update(M.energy(des, nl.pi, pairs=pairs, seed=seed))
    r["name"] = d["name"]
    return r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--energy", action="store_true")
    ap.add_argument("--pairs", type=int, default=0)
    ap.add_argument("--only", nargs="*")
    a = ap.parse_args()
    lib = S.load_lib()
    rows = []
    for d in SD.all_designs(a.n):
        if a.only and d["name"] not in a.only:
            continue
        r = a0(d, lib, a.energy, a.pairs)
        rows.append(r)
        print(f"{d['tag']:18s} cells {r['cells']:5d} area {r['area_um2']:9.2f} um2 {r['area_ge']:8.2f} GE depth {r['unit_depth']:3d} (generic {r['generic_depth']:3d}) T {r['t_ps']:8.1f} ps", flush=True)
    os.makedirs(SD.DATA, exist_ok=True)
    with open(os.path.join(SD.DATA, f"a0_N{a.n}.json"), "w") as fh:
        json.dump({"pi_slew_ns": S.PI_SLEW_NS, "po_load_pf": S.PO_LOAD_PF, "rows": rows}, fh, indent=1, sort_keys=True)

if __name__ == "__main__":
    main()
