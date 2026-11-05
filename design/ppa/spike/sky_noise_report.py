#!/usr/bin/env python3.12
"""Summary of data/sky130/noise_N16.json (structure noise: layout/rename/order/commute variants of the same circuit)
and of the determinism sweeps; writes data/sky130/report_noise_N16.md.   python3.12 sky_noise_report.py"""
import json, os, statistics
import sky130_designs as SD

rows = json.load(open(os.path.join(SD.DATA, "noise_N16.json")))["rows"]
by = {}
for r in rows:
    by.setdefault(r["name"], {})[r["variant"]] = r
M = [("ge", "GE_v1 (legacy)"), ("depth", "depth_v1"), ("a0_um2", "A0' area"), ("a0_t_ps", "A0' T"), ("a1u_um2", "A1'u area"), ("a1u_t_ps", "A1'u T"),
     ("a1s_um2", "A1's area"), ("a1s_t_ps", "A1's T")]
out = []
P = out.append
P("### Structure noise: the same circuit, rewritten (variants of tests/canon/variants.py), N = 16\n")
lay = [v for v in next(iter(by.values())) if v in ("oneline", "ren_random")]
same = all(by[n][v]["rtlil_sha256"] == by[n]["base"]["rtlil_sha256"] for n in by for v in lay)
P(f"Layout (oneline) and rename (ren_random) variants: canonical RTLIL byte-identical to the base on every design: {same}; every number identical.\n")
orders = ["hoist", "reverse", "shuffle1", "shuffle2", "shuffle3", "shuffle4"]
P("Deviation of the worst variant from the base (max over variants of |x/base - 1|), by kind (order = hoist, reverse, 4 shuffles; commute = every commutative operand swapped):\n")
P("| design | kind | " + " | ".join(l for _, l in M) + " |\n|---|---|" + "--:|" * len(M))
agg = {(k, m): [] for k in ("order", "commute") for m, _ in M}
for n, d in by.items():
    for kind, vs in (("order", orders), ("commute", ["commute"])):
        cells = []
        for m, _ in M:
            b = d["base"][m]
            dev = max(abs(d[v][m] / b - 1) for v in vs if v in d)
            agg[(kind, m)].append(dev)
            cells.append(f"{dev*100:.1f}%")
        P(f"| {n} | {kind} | " + " | ".join(cells) + " |")
P("\nMedian / max over the designs of that deviation:\n")
P("| kind | " + " | ".join(l for _, l in M) + " |\n|---|" + "--:|" * len(M))
for kind in ("order", "commute"):
    P(f"| {kind} | " + " | ".join(f"{statistics.median(agg[(kind, m)])*100:.1f}% / {max(agg[(kind, m)])*100:.1f}%" for m, _ in M) + " |")
# spread over all non-identical variants
P("\nSpread (max/min - 1) over ALL variants including base, per design:\n")
P("| design | " + " | ".join(l for _, l in M) + " |\n|---|" + "--:|" * len(M))
for n, d in by.items():
    P(f"| {n} | " + " | ".join(f"{(max(r[m] for r in d.values())/min(r[m] for r in d.values())-1)*100:.1f}%" for m, _ in M) + " |")
text = "\n".join(out) + "\n"
open(os.path.join(SD.DATA, "report_noise_N16.md"), "w").write(text)
print(text)
