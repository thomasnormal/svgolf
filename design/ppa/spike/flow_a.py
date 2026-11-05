#!/usr/bin/env python3.12
"""Flow A of the study: ASIC-lite. The pinned canonical RTLIL of a design is
re-synthesised by the SAME Yosys + ABC but mapped onto a real liberty
(Nangate45) with `abc -liberty LIB [-D ps]` instead of `abc -g <gate list>`;
the mapped netlist is then measured by the spike engine (NLDM STA, area in um^2,
toggle energy). This shows what a library-based official flow would do to the
ranking: ABC optimises delay/area under the library's own numbers, with gate
sizing, instead of under the unit-gate cost of `abc -g`.

  python3.12 flow_a.py --n 16 [--D 0 400 800]     # -> data/flow_a_N16.json

`-D 0` means "no delay target" (ABC's default &nf: delay-oriented mapping with
area recovery). Yosys writes the mapped netlist; its own `stat -liberty` area
is recorded for cross-checking against the engine.
"""
import argparse, glob, json, os, re, subprocess, sys, tempfile, time

import engine as E
import fetch_lib
import liberty as L
import netlist as N
import vectors
from designs import SVGOLF, HERE, designs
import run_spike as R

CONSTR = os.path.join(HERE, "data", "abc.constr")
DONT_USE = ("FILLCELL_* TAPCELL_* ANTENNA_* LOGIC0_* LOGIC1_* CLKBUF_* CLKGATE* TBUF_* TINV_* "
            "DFF* SDFF* DLH_* DLL_* TLAT_* FA_* HA_* AOI211_X1 OAI211_X1")


def canon_rtlil(src, top, n, out):
    if os.path.exists(out):
        return
    os.makedirs(os.path.dirname(out), exist_ok=True)
    r = subprocess.run(["python3.12", os.path.join(SVGOLF, "score", "score.py"), src, "--top", top,
                        "--param", f"N={n}", "--rtlil", out], capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(r.stdout + r.stderr)


def map_liberty(rtlil, top, lib_path, D, out_v, sized=False):
    ds = f"-D {D} " if D else ""
    dont = " ".join(f"-dont_use {p}" for p in DONT_USE.split())
    constr = f"-constr {CONSTR} " if sized else ""
    script = f"""read_rtlil {rtlil}
synth -flatten -top {top}
abc -liberty {lib_path} {dont} {constr}{ds}
opt_clean
tee -o {out_v}.stat stat -liberty {lib_path}
write_verilog -noattr -noexpr {out_v}
"""
    with tempfile.NamedTemporaryFile("w", suffix=".ys", delete=False) as fh:
        fh.write(script)
        ys = fh.name
    try:
        r = subprocess.run(["yosys", "-q", "-l", out_v + ".log", ys], capture_output=True, text=True, timeout=1800)
        if r.returncode != 0:
            raise RuntimeError(r.stderr[-2000:] + r.stdout[-2000:])
    finally:
        os.unlink(ys)


def yosys_area(statfile):
    t = open(statfile).read()
    m = re.search(r"Chip area for (?:top )?module '[^']*': ([\d.]+)", t)
    return float(m.group(1)) if m else None


def measure(path, lib, nvec, npairs, seed):
    nl = N.load(path)
    d = E.Design(nl, lib)       # gate kinds are liberty cells already
    t_nldm, crit, _ = d.sta_nldm(R.PI_SLEW_NS, R.PO_LOAD_FF)
    sim = E.Sim(d)
    pv = vectors.pi_values(nl.pi, nvec, seed)
    v = sim.run(pv, nvec)
    nets = [n for n in v if n not in ("0", "1")]
    tc = E.toggle_counts(v, nets, nvec)
    rises = {n: r / (nvec - 1) for n, (r, f) in tc.items()}
    falls = {n: f / (nvec - 1) for n, (r, f) in tc.items()}
    esw = R.switching_energy_fj(d, rises, falls)
    eint = R.internal_energy_fj(d, rises, falls)
    eleak = d.leakage_nw() * t_nldm * 1e-3
    res = {"cells": sum(d.cell_counts().values()), "area_um2": round(d.area_um2(), 3),
           "area_ge": round(d.area_um2() / R.NAND2_UM2, 2), "unit_depth": d.unit_depth(),
           "t_nldm_ns": round(t_nldm, 4), "e_dyn_fj": round(esw + eint, 2), "e_leak_fj": round(eleak, 3),
           "cell_mix": d.cell_counts()}
    if npairs:
        tt, zz = E.timed_toggle_counts(d, v, nl.pi, nvec, npairs)
        tr = {n: tt[n][0] / npairs for n in tt}; tf = {n: tt[n][1] / npairs for n in tt}
        res["e_dyn_glitch_fj"] = round(R.switching_energy_fj(d, tr, tf) + R.internal_energy_fj(d, tr, tf), 2)
        zr = {n: zz[n][0] / npairs for n in zz}; zf = {n: zz[n][1] / npairs for n in zz}
        res["glitch_factor"] = round(res["e_dyn_glitch_fj"] / (R.switching_energy_fj(d, zr, zf) + R.internal_energy_fj(d, zr, zf)), 3)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--D", type=int, nargs="*", default=None,
                    help="delay targets in ps (0 = none); default per task: add 0 450 550 650 800 2000, mul 0 1500 2000 2500 3500 6000")
    ap.add_argument("--nvec", type=int, default=2001)
    ap.add_argument("--pairs", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--lib", default=None, help="liberty file to map onto (default: the pinned Nangate45); "
                    "a non-default library adds '_<stem>' to every output name")
    ap.add_argument("--tag", default="", help="suffix of the output json (e.g. _energy)")
    ap.add_argument("--sized", action="store_true", help="use -constr: buffer/upsize/dnsize/stime after &nf")
    a = ap.parse_args()
    lib_path = a.lib or fetch_lib.lib_path()
    lib = L.Liberty.load(lib_path)
    lname = "" if not a.lib else "_" + os.path.splitext(os.path.basename(a.lib))[0]
    rows = []
    for d in designs():
        if a.only and d["name"] not in a.only:
            continue
        src = os.path.join(SVGOLF, d["src"].format(N=a.n))
        if not os.path.exists(src):
            continue
        tag = f"{d['name']}_N{a.n}"
        rt = os.path.join(HERE, ".cache", "rtlil", tag + ".il")
        canon_rtlil(src, d["top"], a.n, rt)
        for D in (a.D if a.D is not None else ([0, 450, 550, 650, 800, 2000] if d["task"] == "add"
                                               else [0, 1500, 2000, 2500, 3500, 6000])):
            if not a.sized and D != 0:
                continue
            outv = os.path.join(HERE, "data", "flow_a", f"{tag}{lname}_D{D}{'_sized' if a.sized else ''}.v")
            os.makedirs(os.path.dirname(outv), exist_ok=True)
            t = time.time()
            map_liberty(rt, d["top"], lib_path, D, outv, a.sized)
            m = measure(outv, lib, a.nvec, a.pairs, a.seed)
            sm = re.findall(r"Delay =\s+([\d.]+) ps", open(outv + ".log").read())
            m.update(abc_stime_ps=float(sm[-1]) if sm else None, name=d["name"], D=D, sized=a.sized, yosys_area_um2=yosys_area(outv + ".stat"))
            rows.append(m)
            print(f"{tag:22s} D={D:5d} cells {m['cells']:5d} area {m['area_um2']:8.1f} um2 ({m['area_ge']:7.1f} GE) "
                  f"T {m['t_nldm_ns']:.3f} ns  E_dyn {m['e_dyn_fj']:8.1f} fJ  {time.time() - t:.1f}s", flush=True)
    with open(os.path.join(HERE, "data", f"flow_a_N{a.n}{lname}{'_sized' if a.sized else ''}{a.tag}.json"), "w") as fh:
        json.dump({"liberty_sha256": fetch_lib.SHA256, "dont_use": DONT_USE, "rows": rows}, fh, indent=1, sort_keys=True)


if __name__ == "__main__":
    main()
