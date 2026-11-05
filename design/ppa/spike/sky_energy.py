#!/usr/bin/env python3.12
"""Energy of the studied designs under the fixed sky130 setup (WP-X1): activity-only (zero-delay toggle counts) and
glitch-aware (inertial-delay event simulation) energy per operation, over several stimulus seeds, for flows A0'
(scored netlist priced 1:1 in sky130 cells) and A1'u (abc -liberty). Seed 0 is the "public development seed" with a
short public set (201 vectors, 100 timed pairs); seeds 1..5 are stand-ins for hidden official seeds (2001 vectors,
300 timed pairs). Energies in fJ per operation: dynamic = 1/2 C V^2 (V = 1.8 V) per net toggle + liberty internal
energy (sky130.md section 2), leakage separate.

  python3.12 sky_energy.py [--designs ...] [--flows a0 u] [--seeds 0 1 2 3 4 5] [--workers 3]
      -> data/sky130/energy_N16.json
"""
import argparse, concurrent.futures as cf, json, os, sys, time
import netlist as N, sky130 as S, sky130_designs as SD, sky_measure as M

SEEDS = {0: dict(nvec=201, pairs=100), 1: dict(nvec=2001, pairs=300), 2: dict(nvec=2001, pairs=300), 3: dict(nvec=2001, pairs=300),
         4: dict(nvec=2001, pairs=300), 5: dict(nvec=2001, pairs=300)}


def path_of(name, flow):
    tag = SD.get(name)["tag"]
    return (os.path.join(SD.CACHE, "netlists", tag + ".v") if flow == "a0" else os.path.join(SD.CACHE, "a1", f"{tag}.{flow}.v"))


def job(name, flow, seed):
    lib = S.load_lib()
    nl = N.load(path_of(name, flow))
    des = M.build(S.expand_generic_sky(nl) if flow == "a0" else nl, lib)
    t0 = time.time()
    e = M.energy(des, nl.pi, nvec=SEEDS[seed]["nvec"], seed=seed, pairs=SEEDS[seed]["pairs"])
    e.update(name=name, flow=flow, seed=seed, nvec=SEEDS[seed]["nvec"], seconds=round(time.time() - t0, 2))
    return e


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--designs", nargs="*", default=[d["name"] for d in SD.all_designs(16)])
    ap.add_argument("--flows", nargs="*", default=["a0", "u"])
    ap.add_argument("--seeds", nargs="*", type=int, default=[0, 1, 2, 3, 4, 5])
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--tag", default="")
    a = ap.parse_args()
    rows = []
    with cf.ProcessPoolExecutor(a.workers) as ex:
        futs = [ex.submit(job, n, f, s) for n in a.designs for f in a.flows for s in a.seeds]
        for fu in cf.as_completed(futs):
            r = fu.result()
            rows.append(r)
            print(f"{r['name']:14s} {r['flow']:3s} seed {r['seed']} act {r['e_act_fj']:9.1f} glitch {r['e_glitch_fj']:9.1f} x{r['glitch_factor']:.2f} leak {r['e_leak_fj']:.3f} {r['seconds']:.1f}s", flush=True)
    rows.sort(key=lambda r: (r["name"], r["flow"], r["seed"]))
    with open(os.path.join(SD.DATA, f"energy_N16{a.tag}.json"), "w") as fh:
        json.dump({"vdd": S.VDD, "pi_slew_ns": S.PI_SLEW_NS, "po_load_pf": S.PO_LOAD_PF, "seeds": SEEDS, "rows": rows}, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
