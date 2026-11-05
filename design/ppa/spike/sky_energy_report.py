#!/usr/bin/env python3.12
"""Seed-to-seed behaviour of the activity-only and glitch-aware energy (WP-X1), from data/sky130/energy_N16.json.
Writes data/sky130/report_energy_N16.md.   python3.12 sky_energy_report.py
"""
import itertools, json, math, os, statistics
import sky130_designs as SD
from sky_report import ranks, tau, TASKS, NOTE

rows = json.load(open(os.path.join(SD.DATA, "energy_N16.json")))["rows"]
by = {}
for r in rows:
    by.setdefault((r["name"], r["flow"]), {})[r["seed"]] = r
gm = lambda xs: math.exp(sum(math.log(x) for x in xs) / len(xs))
cv = lambda xs: statistics.pstdev(xs) / statistics.mean(xs)
out = []
P = out.append
OFF = [1, 2, 3, 4, 5]
for flow, fname in (("a0", "A0' (scored netlist priced in sky130 cells)"), ("u", "A1'u (abc -liberty)")):
    P(f"\n### Energy per operation, flow {fname}; fJ; seeds 1..5 = 2001 vectors / 300 timed pairs each; seed 0 = public dev set (201 vectors / 100 pairs)\n")
    P("| design | act mean | act CV | act range % | glitch mean | glitch CV | glitch range % | glitch factor | gm3 glitch (seeds 1-3) vs gm5 | dev seed 0 glitch vs gm5 | dev seed 0 act vs gm5 |\n|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
    for task, names in TASKS.items():
        for n in names:
            d = by[(n, flow)]
            act = [d[s]["e_act_fj"] for s in OFF]; gl = [d[s]["e_glitch_fj"] for s in OFF]
            g5, g3 = gm(gl), gm(gl[:3])
            P(f"| {n}{NOTE.get(n,'')} | {statistics.mean(act):.0f} | {cv(act)*100:.2f}% | {(max(act)/min(act)-1)*100:.1f} | {statistics.mean(gl):.0f} | {cv(gl)*100:.2f}% | {(max(gl)/min(gl)-1)*100:.1f} | "
              f"{statistics.mean(d[s]['glitch_factor'] for s in OFF):.2f} | {(g3/g5-1)*100:+.1f}% | {(d[0]['e_glitch_fj']/g5-1)*100:+.1f}% | {(d[0]['e_act_fj']/gm(act)-1)*100:+.1f}% |")
    # ranks per seed
    for task, names in TASKS.items():
        if len(names) < 3:
            continue
        for key, label in (("e_act_fj", "activity"), ("e_glitch_fj", "glitch-aware")):
            P(f"\n{task}, {label} energy ranks per seed (1 = lowest), flow {flow}:\n")
            P("| design | " + " | ".join(f"seed {s}" for s in [0] + OFF) + " | gm5 rank | rank interval over seeds |\n|---|" + "--:|" * 8)
            R = {s: ranks({n: by[(n, flow)][s][key] for n in names}) for s in [0] + OFF}
            G = ranks({n: gm([by[(n, flow)][s][key] for s in OFF]) for n in names})
            for n in names:
                rs = [R[s][n] for s in OFF]
                P(f"| {n}{NOTE.get(n,'')} | " + " | ".join(str(R[s][n]) for s in [0] + OFF) + f" | {G[n]} | {min(rs)}..{max(rs)} |")
            taus = [tau({n: by[(n, flow)][a][key] for n in names}, {n: by[(n, flow)][b][key] for n in names}, names) for a, b in itertools.combinations(OFF, 2)]
            P(f"\nKendall tau between seed pairs (seeds 1..5): min {min(taus):+.2f}, mean {statistics.mean(taus):+.2f}.")
# activity vs glitch tau and vs area
P("\n### Does the energy ranking carry information beyond area? Kendall tau, flow A0', gm5 of seeds 1..5\n")
import sky_report as SR
pinned, a0, a1, ng, ngu = SR.load()
for task, names in TASKS.items():
    if len(names) < 3:
        continue
    act = {n: gm([by[(n, 'a0')][s]['e_act_fj'] for s in OFF]) for n in names}
    gl = {n: gm([by[(n, 'a0')][s]['e_glitch_fj'] for s in OFF]) for n in names}
    area = {n: a0[n]['area_um2'] for n in names}
    dep = {n: pinned[n]['depth'] for n in names}
    T = {n: a0[n]['t_ps'] for n in names}
    P(f"{task}: tau(act, area) {tau(act, area, names):+.2f}; tau(glitch, area) {tau(gl, area, names):+.2f}; tau(glitch, depth_v1) {tau(gl, dep, names):+.2f}; tau(glitch, T) {tau(gl, T, names):+.2f}; tau(act, glitch) {tau(act, gl, names):+.2f}\n")
text = "\n".join(out) + "\n"
open(os.path.join(SD.DATA, "report_energy_N16.md"), "w").write(text)
print(text)
