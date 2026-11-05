#!/usr/bin/env python3.12
"""Sensitivity of the delay metric to the fixed timing setup (WP-X1): PI transition x PO load grid on the A0', A1'u and
A1's netlists; Kendall tau of the per-task delay ranking against the proposed setup (50 ps, 10 fF), and the largest
relative change of T.   python3.12 sky_setup_sens.py  -> data/sky130/setup_sensitivity_N16.json + Markdown"""
import json, os
import netlist as N, sky130 as S, sky130_designs as SD, sky_measure as M
from sky_report import tau, TASKS, ranks

lib = S.load_lib()
GRID = [(0.01, 0.005), (0.01, 0.010), (0.05, 0.005), (0.05, 0.010), (0.05, 0.020), (0.15, 0.010), (0.15, 0.020), (0.30, 0.040)]
des = {}
for d in SD.all_designs(16):
    nl = N.load(os.path.join(SD.CACHE, "netlists", d["tag"] + ".v"))
    des[(d["name"], "a0")] = M.build(S.expand_generic_sky(nl), lib)
    for v in ("u", "s"):
        des[(d["name"], v)] = M.build(N.load(os.path.join(SD.CACHE, "a1", f"{d['tag']}.{v}.v")), lib)
res = {}
for (sl, ld) in GRID:
    for k, dd in des.items():
        res[(sl, ld) + k] = dd.sta_nldm(sl, ld)[0] * 1000
out = ["### Delay-ranking sensitivity to the timing setup (Kendall tau against PI 50 ps / PO 10 fF; max |T/T0 - 1|)\n",
       "| PI slew ps | PO load fF | " + " | ".join(f"{t}/{f}" for t in ("add", "mul", "sbox") for f in ("A0'", "u", "s") if not (t == 'sbox' and False)) + " | max T change vs base (A0' / u / s) |", "|--:|--:|" + "--:|" * 10]
base = (0.05, 0.010)
for (sl, ld) in GRID:
    cells = []
    for t, names in TASKS.items():
        for f in ("a0", "u", "s"):
            b = {n: res[base + (n, f)] for n in names}
            x = {n: res[(sl, ld) + (n, f)] for n in names}
            cells.append(f"{tau(b, x, names):+.2f}" if len(names) > 2 else ("same" if ranks(b) == ranks(x) else "flip"))
    mx = [max(abs(res[(sl, ld) + (n, f)] / res[base + (n, f)] - 1) for t in TASKS.values() for n in t) for f in ("a0", "u", "s")]
    out.append(f"| {sl*1000:.0f} | {ld*1000:.0f} | " + " | ".join(cells) + f" | {mx[0]*100:.0f}% / {mx[1]*100:.0f}% / {mx[2]*100:.0f}% |")
text = "\n".join(out) + "\n"
open(os.path.join(SD.DATA, "setup_sensitivity_N16.md"), "w").write(text)
print(text)
