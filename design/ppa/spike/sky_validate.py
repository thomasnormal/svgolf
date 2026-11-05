#!/usr/bin/env python3.12
"""Validation of the study's STA against ABC's own `stime -p` (WP-X1; WP-X0 did this for Nangate45).
Every design is mapped by variant `s` (sized, with -constr) at several delay targets D; the netlist ABC reports a
delay for is measured by sky130-STA of engine.py with (a) the proposed fixed setup (ideal 50 ps ramp at the inputs,
10 fF on every output) and (b) a driving-cell model close to ABC's (inputs driven by buf_1). The comparison is
engine T / ABC stime - 1. Also the area/delay curve of -D (does the delay target matter?).

  python3.12 sky_validate.py [--n 16] [--workers 3]      # -> data/sky130/validate_N16.json
"""
import argparse, concurrent.futures as cf, json, os, time
import engine as E, netlist as N, sky130 as S, sky130_designs as SD, sky_flow as F, sky_measure as M

DS = [None, 1500, 2500, 4000, 6000, 9000, 14000]

def sta_driven(des, drv_cell, pi_slew0=0.0, po_load=S.PO_LOAD_PF, lib=None):
    """STA with every primary input driven by `drv_cell` (a buffer): arrival = the buffer's delay, slew = its output
    transition, at the load of the PI net (sum of fan-out pin caps), input slew pi_slew0. This is what
    `set_driving_cell` does in OpenSTA and what ABC's stime assumes."""
    c = lib.cell(drv_cell)
    arc = c.arcs["X"][0]
    # patch the initial arrivals by running sta_nldm with an overridden dictionary: re-implement the PI seeding
    seeded = {}
    for n in des.nl.pi:
        load = des.load_ff(n, po_load)
        for e in "rf":
            dk = "cell_rise" if e == "r" else "cell_fall"; tk = "rise_transition" if e == "r" else "fall_transition"
            seeded[(n, e)] = (arc.tbl[dk].at(pi_slew0 or 0.01, load), arc.tbl[tk].at(pi_slew0 or 0.01, load), None)
    return seeded

def sta_with_seed(des, seeded, po_load=S.PO_LOAD_PF):
    # same algorithm as Design.sta_nldm, with the primary-input arrivals given
    orig = des.nl.pi
    t0, path, arr = None, None, None
    import types
    # temporarily run sta_nldm with PIs at slew 0 then overwrite: simplest is to copy the loop
    arr = dict(seeded)
    des.load_cache = {}
    des.gate_delay = {}
    for i in des.order:
        c = des.cells[i]
        for op, onet in des.outs[i].items():
            load = des.load_ff(onet, po_load)
            des.load_cache[onet] = load
            dly = {"r": 0.0, "f": 0.0}
            in_slew = 0.0
            for e in "rf":
                best = None; smax = 0.0
                for arc in c.arcs[op]:
                    inet = des.ins[i].get(arc.related)
                    if inet is None or inet in ("0", "1"):
                        continue
                    ies = (e,) if arc.sense == "positive_unate" else (("f" if e == "r" else "r"),) if arc.sense == "negative_unate" else ("r", "f")
                    for ie in ies:
                        a = arr.get((inet, ie))
                        if a is None:
                            continue
                        t0_, s0, _ = a
                        dkey = "cell_rise" if e == "r" else "cell_fall"; tkey = "rise_transition" if e == "r" else "fall_transition"
                        d = arc.tbl[dkey].at(s0, load); so = arc.tbl[tkey].at(s0, load)
                        smax = max(smax, so); in_slew = max(in_slew, s0); dly[e] = max(dly[e], d)
                        if best is None or t0_ + d > best[0]:
                            best = (t0_ + d, (inet, ie))
                if best is not None:
                    arr[(onet, e)] = (best[0], smax, best[1])
            des.gate_delay[(i, op)] = (dly["r"], dly["f"], in_slew)
    return max(arr[(n, e)][0] for n in des.po_nets for e in "rf" if (n, e) in arr)

def one(d, D, lib):
    il = os.path.join(SD.CACHE, "rtlil", d["tag"] + ".il")
    out = os.path.join(SD.CACHE, "a1", f"{d['tag']}.s.D{D}.v")
    r = F.run(il, d["top"], out, "s", lib, D=D)
    return d, D, out, r

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--workers", type=int, default=3)
    a = ap.parse_args()
    lib = S.load_lib()
    jobs = [(d, D) for d in SD.all_designs(a.n) for D in DS]
    rows = []
    with cf.ThreadPoolExecutor(a.workers) as ex:
        for f in cf.as_completed([ex.submit(one, d, D, lib) for d, D in jobs]):
            d, D, out, r = f.result()
            des = M.build(N.load(out), lib)
            t_fix = des.sta_nldm(S.PI_SLEW_NS, S.PO_LOAD_PF)[0] * 1000
            t_drv = sta_with_seed(des, sta_driven(des, S.PREFIX + "buf_1", 0.0, S.PO_LOAD_PF, lib)) * 1000
            rows.append(dict(name=d["name"], D=D, cells=len(des.cells), area_um2=round(des.area_um2(), 3), t_fixed_ps=round(t_fix, 2),
                             t_driven_ps=round(t_drv, 2), abc_stime_ps=r["abc_stime_ps"]))
    rows.sort(key=lambda r: (r["name"], r["D"] or 0))
    for k in ("t_fixed_ps", "t_driven_ps"):
        e = [abs(r[k] / r["abc_stime_ps"] - 1) for r in rows]
        print(f"{k}: mean |err| {100*sum(e)/len(e):.2f}%  max {100*max(e):.2f}%  n={len(e)}")
    os.makedirs(SD.DATA, exist_ok=True)
    with open(os.path.join(SD.DATA, f"validate_N{a.n}.json"), "w") as fh:
        json.dump({"rows": rows}, fh, indent=1, sort_keys=True)

if __name__ == "__main__":
    main()
