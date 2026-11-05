#!/usr/bin/env python3.12
"""PPA spike: (area, unit depth) vs weighted delay, switching energy and the
derived figures AT, EDP, perf-per-energy, on the scored netlists of the existing
add/mul designs.

  python3.12 gen_netlists.py --n 16        # once: scored netlists (pinned flow)
  python3.12 run_spike.py --n 16           # -> data/results_N16.json + tables

Models (see README.md in the parent directory):
  unit    Yosys `ltp` depth (the present score)
  LE      textbook logical effort, unit-size gates, fan-out term, tau
  NLDM    Nangate45 typical liberty: rise/fall STA with slew propagation, ns
Energy per operation (fJ), uniform random inputs from a pinned SHA-256 stream:
  E_sw    sum over nets of toggles * 1/2 C V^2   (C = fan-out pin caps; POs +6.8 fF)
  E_int   liberty internal_power per output toggle (tables read as fJ)
  E_leak  leakage power * critical-path time
  glitch  same, from an inertial-delay event simulation with NLDM gate delays
"""
import argparse, glob, json, os, sys, time

import engine as E
import fetch_lib
import liberty as L
import netlist as N
import vectors

VDD = 1.1          # V, Nangate45 typical corner
PO_LOAD_FF = 6.8   # fF, 4 x INV_X1 input capacitance (FO4-style output load)
PI_SLEW_NS = 0.01
NAND2_UM2 = 0.798


def mean(xs):
    xs = list(xs)
    return sum(xs) / len(xs) if xs else 0.0


def internal_energy_fj(design, rises, falls):
    """Sum over gate outputs of toggles * liberty internal energy (mean over the
    cell's internal_power tables) at the gate's worst input slew and its load."""
    tot = 0.0
    for i, c in enumerate(design.cells):
        for op, onet in design.outs[i].items():
            r, f = rises.get(onet, 0), falls.get(onet, 0)
            if not (r or f):
                continue
            slew = design.gate_delay[(i, op)][2] or PI_SLEW_NS
            load = design.load_cache[onet]
            pw = c.power[op]
            er = mean(t.at(slew, load) for t in pw["rise_power"])
            ef = mean(t.at(slew, load) for t in pw["fall_power"])
            tot += r * er + f * ef
    return tot


def switching_energy_fj(design, rises, falls):
    tot = 0.0
    for net in sorted(set(rises) | set(falls)):
        if net in ("0", "1"):
            continue
        c = design.load_cache.get(net)
        if c is None:   # primary input: only its fan-out pins
            c = design.load_ff(net, PO_LOAD_FF)
        tot += (rises.get(net, 0) + falls.get(net, 0)) * 0.5 * c * VDD * VDD
    return tot


def analyze(name, path, score, lib, nvec, npairs, seed, timed=True):
    nl = N.load(path)
    gdepth = E.generic_depth(nl)
    assert gdepth == score["depth"], (name, gdepth, score["depth"])
    d = E.Design(E.expand_generic(nl), lib)
    t_nldm, crit, _ = d.sta_nldm(PI_SLEW_NS, PO_LOAD_FF)
    t_le = d.sta_le()
    # PIs also need loads for the energy of the input drivers
    sim = E.Sim(d)
    pis = nl.pi
    pv = vectors.pi_values(pis, nvec, seed)
    v = sim.run(pv, nvec)
    nets = [n for n in v if n not in ("0", "1")]
    tc = E.toggle_counts(v, nets, nvec)
    rises = {n: r / (nvec - 1) for n, (r, f) in tc.items()}
    falls = {n: f / (nvec - 1) for n, (r, f) in tc.items()}
    esw = switching_energy_fj(d, rises, falls)
    eint = internal_energy_fj(d, rises, falls)
    leak_nw = d.leakage_nw()
    eleak = leak_nw * t_nldm * 1e-3   # nW * ns = 1e-18 J = 1e-3 fJ
    toggles = sum(rises.values()) + sum(falls.values())
    gates_toggles = sum(rises.get(n, 0) + falls.get(n, 0) for n in d.driver)
    res = {
        "name": name,
        "area_ge": score["area_ge"], "depth": score["depth"], "gates": score["num_gates"],
        "lib_cells": sum(d.cell_counts().values()), "lib_area_um2": round(d.area_um2(), 3),
        "lib_area_ge": round(d.area_um2() / NAND2_UM2, 3),
        "unit_depth_expanded": d.unit_depth(),
        "t_le_tau": round(t_le, 3), "t_nldm_ns": round(t_nldm, 4),
        "crit_path_cells": len(crit),
        "toggles_per_op_gates": round(gates_toggles, 2), "toggles_per_op_all": round(toggles, 2),
        "e_sw_fj": round(esw, 2), "e_int_fj": round(eint, 2), "e_leak_fj": round(eleak, 3),
        "leak_nw": round(leak_nw, 1),
        "nvec": nvec, "seed": seed,
    }
    res["e_dyn_fj"] = round(esw + eint, 2)
    res["e_op_fj"] = round(esw + eint + eleak, 2)
    if timed:
        t0 = time.time()
        tt, zz = E.timed_toggle_counts(d, v, pis, nvec, npairs)
        tr = {n: tt[n][0] / npairs for n in tt}
        tf = {n: tt[n][1] / npairs for n in tt}
        zr = {n: zz[n][0] / npairs for n in zz}
        zf = {n: zz[n][1] / npairs for n in zz}
        esw_t = switching_energy_fj(d, tr, tf)
        eint_t = internal_energy_fj(d, tr, tf)
        esw_z = switching_energy_fj(d, zr, zf)
        eint_z = internal_energy_fj(d, zr, zf)
        res.update({
            "pairs_timed": npairs,
            "e_dyn_zero_same_pairs_fj": round(esw_z + eint_z, 2),
            "e_dyn_glitch_fj": round(esw_t + eint_t, 2),
            "glitch_factor": round((esw_t + eint_t) / (esw_z + eint_z), 3),
        })
        res["_timed_seconds"] = round(time.time() - t0, 1)   # printed, not stored (keeps the JSON reproducible)
        res["e_op_glitch_fj"] = round(esw_t + eint_t + eleak, 2)
    return res


def derived(r):
    """The combined figures. area in GE (library GE), T in ns (NLDM), E in fJ."""
    a = r["lib_area_ge"]
    t = r["t_nldm_ns"]
    e = r.get("e_op_glitch_fj", r["e_op_fj"])
    return {
        "AT": round(a * t, 2),                 # GE * ns
        "AT2": round(a * t * t, 2),
        "EDP": round(e * t, 2),                # fJ * ns
        "ED2P": round(e * t * t, 2),
        "perf_per_energy": round(1e3 / e, 4),  # operations per pJ  (= perf/W / 1e12 ... see README)
        "ops_per_ns": round(1.0 / t, 4),
        "power_mw_at_fmax": round(e / t * 1e-3, 4),   # fJ/ns = uW ; /1e3 -> mW
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--nvec", type=int, default=2001, help="vectors for the zero-delay toggle count")
    ap.add_argument("--pairs", type=int, default=300, help="vector pairs for the timed (glitch) simulation")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--no-timed", action="store_true")
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--tag", default="", help="suffix for the output file name (e.g. _seed2)")
    a = ap.parse_args()
    lib = L.Liberty.load(fetch_lib.lib_path())
    here = os.path.dirname(os.path.abspath(__file__))
    out = []
    for js in sorted(glob.glob(os.path.join(here, "data", "netlists", f"*_N{a.n}.score.json"))):
        name = os.path.basename(js)[: -len(f"_N{a.n}.score.json")]
        if a.only and name not in a.only:
            continue
        score = json.load(open(js))
        t = time.time()
        r = analyze(name, js.replace(".score.json", ".v"), score, lib, a.nvec, a.pairs, a.seed,
                    timed=not a.no_timed)
        r.update(derived(r))
        r.pop("_timed_seconds", None)
        out.append(r)
        print(f"{name:14s} GE {r['area_ge']:8.1f} d {r['depth']:3d} | LE {r['t_le_tau']:6.1f}t NLDM {r['t_nldm_ns']:.3f}ns | "
              f"E_dyn {r['e_dyn_fj']:8.1f} fJ glitchx{r.get('glitch_factor', 0):.2f} | {time.time()-t:.1f}s", flush=True)
    os.makedirs(os.path.join(here, "data"), exist_ok=True)
    with open(os.path.join(here, "data", f"results_N{a.n}{a.tag}.json"), "w") as fh:
        json.dump({"liberty_sha256": fetch_lib.SHA256, "vdd": VDD, "po_load_ff": PO_LOAD_FF,
                   "pi_slew_ns": PI_SLEW_NS, "rows": out}, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
