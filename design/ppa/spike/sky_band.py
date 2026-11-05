#!/usr/bin/env python3.12
"""Where do rankings stop being trustworthy? (WP-X1 noise policy). For every pair of designs of a task and a gap
g = |m_i / m_j - 1| in the base flow, how often is the ORDER of the pair reversed (a) under another mapper of the
same netlist (A0', A1' u s l h r; the -fast `f` mapper listed separately), (b) when one of the two is rewritten
(order and commute variants of tests/canon/variants.py: same circuit)? The tie band is the smallest gap above which
fewer than 5% of pairs reverse.   python3.12 sky_band.py  -> data/sky130/report_band_N16.md"""
import itertools, json, os
import sky130_designs as SD
from sky_report import load, TASKS

pinned, a0, a1, ng, ngu = load()
names_by_task = TASKS
BUCKETS = [(0, .02), (.02, .05), (.05, .10), (.10, .20), (.20, .40), (.40, 9)]
get = {"A0'": lambda n, m: a0[n][m]}
for v in ("u", "s", "l", "h", "r", "f"):
    get[v] = (lambda v: lambda n, m: a1[v][n][m])(v)
noise = {}
for r in json.load(open(os.path.join(SD.DATA, "noise_N16.json")))["rows"]:
    noise.setdefault(r["name"], {})[r["variant"]] = r


def bucket(g):
    for lo, hi in BUCKETS:
        if lo <= g < hi:
            return (lo, hi)


def table(title, events):
    """events: [(gap, flipped)]"""
    out = [f"\n{title}\n", "| gap between the two designs | pairs-events | reversed | rate |\n|---|--:|--:|--:|"]
    for lo, hi in BUCKETS:
        e = [f for g, f in events if lo <= g < hi]
        lab = f"{lo*100:.0f}% .. {hi*100:.0f}%" if hi < 9 else f"> {lo*100:.0f}%"
        out.append(f"| {lab} | {len(e)} | {sum(e)} | {(sum(e)/len(e)*100 if e else float('nan')):.0f}% |")
    return "\n".join(out)


out = []
for metric, key_a, key_n in (("area (um^2)", "area_um2", None), ("delay T", "t_ps", None)):
    ev_map, ev_map_f = [], []
    for task, names in names_by_task.items():
        for i, j in itertools.combinations(names, 2):
            for X, Y in itertools.permutations(["A0'", "u", "s", "l", "h", "r"], 2):
                gi, gj = get[X](i, key_a), get[X](j, key_a)
                g = abs(gi / gj - 1)
                flip = (gi < gj) != (get[Y](i, key_a) < get[Y](j, key_a))
                ev_map.append((g, flip))
            for X in ["A0'", "u", "s"]:
                gi, gj = get[X](i, key_a), get[X](j, key_a)
                ev_map_f.append((abs(gi / gj - 1), (gi < gj) != (get["f"](i, key_a) < get["f"](j, key_a))))
    out.append(table(f"**{metric}, mapper-to-mapper** (X, Y in A0', u, s, l, h, r; ordered pairs of mappers; gap measured under X)", ev_map))
    out.append(table(f"{metric}, against the -fast mapper `f` (X in A0', u, s)", ev_map_f))
    # rewrite events: design i rewritten (variant v) against base j, flow-wise
    nm = {"area_um2": {"A0'": "a0_um2", "u": "a1u_um2", "s": "a1s_um2"}, "t_ps": {"A0'": "a0_t_ps", "u": "a1u_t_ps", "s": "a1s_t_ps"}}[key_a]
    ev_rw = {}
    for flow, fld in nm.items():
        ev = []
        for task, names in names_by_task.items():
            nn = [n for n in names if n in noise]
            for i, j in itertools.permutations(nn, 2):
                bi, bj = noise[i]["base"][fld], noise[j]["base"][fld]
                g = abs(bi / bj - 1)
                for v, r in noise[i].items():
                    if v == "base":
                        continue
                    ev.append((g, (bi < bj) != (r[fld] < bj)))
        ev_rw[flow] = ev
    for flow, ev in ev_rw.items():
        out.append(table(f"**{metric}, rewrite of one design** (flow {flow}; one design replaced by one of its 11 same-circuit variants; layout/rename variants are identical, so they dilute the rate)", ev))
text = "\n".join(out) + "\n"
open(os.path.join(SD.DATA, "report_band_N16.md"), "w").write(text)
print(text)
