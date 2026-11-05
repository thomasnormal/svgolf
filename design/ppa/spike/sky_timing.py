#!/usr/bin/env python3.12
"""Run time of each flow per design on this machine (WP-X1), serial, median of 3, with wall and child CPU time
(user+sys). The machine is SHARED with a Lean job: the load average at start and end is recorded; wall times are upper
bounds, CPU times are the better estimate.   python3.12 sky_timing.py  -> data/sky130/timing_N16.json
"""
import json, os, resource, statistics, subprocess, sys, time
import netlist as N, sky130 as S, sky130_designs as SD, sky_flow as F, sky_gen as G, sky_measure as M, engine as E


def cpu():
    r = resource.getrusage(resource.RUSAGE_CHILDREN)
    return r.ru_utime + r.ru_stime


def med(f, k=3):
    w, c = [], []
    for _ in range(k):
        c0, t0 = cpu(), time.time()
        f()
        w.append(time.time() - t0); c.append(cpu() - c0)
    return statistics.median(w), statistics.median(c)


def main():
    t0 = time.time()
    la0 = os.getloadavg()
    tl = time.time(); lib = S.load_lib(); load_s = time.time() - tl
    rows = []
    for d in SD.all_designs(16):
        il = os.path.join(SD.CACHE, "rtlil", d["tag"] + ".il")
        tmp = os.path.join(SD.CACHE, "timing")
        row = dict(name=d["name"])
        row["pinned_wall"], row["pinned_cpu"] = med(lambda: G.run(d, tmp))
        nlp = os.path.join(tmp, "netlists", d["tag"] + ".v")
        def a0():
            nl = N.load(nlp)
            des = M.build(S.expand_generic_sky(nl), lib)
            M.static(des, lib)
        row["a0_wall"], _ = med(a0)
        for v in ("u", "s"):
            out = os.path.join(tmp, "a1", f"{d['tag']}.{v}.v")
            row[f"a1{v}_yosys_wall"], row[f"a1{v}_yosys_cpu"] = med(lambda: F.run(il, d["top"], out, v, lib))
            def meas():
                nl = N.load(out)
                M.static(M.build(nl, lib), lib)
            row[f"a1{v}_measure_wall"], _ = med(meas)
        # energy: activity over 2001 vectors and glitch over 300 pairs (one seed)
        nl = N.load(nlp); des = M.build(S.expand_generic_sky(nl), lib)
        row["energy_act_wall"], _ = med(lambda: M.energy(des, nl.pi, nvec=2001, seed=1, pairs=0), 1)
        row["energy_glitch300_wall"], _ = med(lambda: M.energy(des, nl.pi, nvec=2001, seed=1, pairs=300), 1)
        rows.append({k: (round(v, 3) if isinstance(v, float) else v) for k, v in row.items()})
        print(row["name"], {k: round(v, 2) for k, v in row.items() if k != "name"}, flush=True)
    json.dump({"load_average_start": la0, "load_average_end": os.getloadavg(), "liberty_load_s": round(load_s, 2),
               "wall_total_s": round(time.time() - t0, 1), "cores": os.cpu_count(), "rows": rows},
              open(os.path.join(SD.DATA, "timing_N16.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
