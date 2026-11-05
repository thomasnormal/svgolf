#!/usr/bin/env python3.12
"""Tables of the sky130 study (WP-X1) from data/sky130/*.json and WP-X0's data/*.json (Markdown on stdout and in
data/sky130/report_N16.md): flows A0' and A1' against today's score and against WP-X0's Nangate45 A0.

  python3.12 sky_report.py
"""
import itertools, json, os, statistics, sys
import sky130_designs as SD

HERE = os.path.dirname(os.path.abspath(__file__))
D0 = os.path.join(HERE, "data")
DS = SD.DATA


def J(p):
    return json.load(open(p)) if os.path.exists(p) else None


def ranks(vals):
    """competition ranks, 1 = smallest; ties share the best rank."""
    order = sorted(vals, key=lambda k: vals[k])
    out, prev, rk = {}, None, 0
    for i, k in enumerate(order):
        if prev is None or vals[k] != prev:
            rk = i + 1
        out[k] = rk
        prev = vals[k]
    return out


def tau(a, b, keys):
    c = d = 0
    for x, y in itertools.combinations(keys, 2):
        s = (a[x] > a[y]) - (a[x] < a[y])
        t = (b[x] > b[y]) - (b[x] < b[y])
        if s * t > 0:
            c += 1
        elif s * t < 0:
            d += 1
    return (c - d) / (c + d) if c + d else float("nan")


def load():
    pinned = {r["name"]: r for r in J(os.path.join(DS, "pinned_N16.json"))["rows"]}
    a0 = {r["name"]: r for r in J(os.path.join(DS, "a0_N16.json"))["rows"]}
    a1 = {}
    for r in J(os.path.join(DS, "a1_N16.json"))["rows"]:
        a1.setdefault(r["variant"], {})[r["name"]] = r
    ng = {r["name"]: r for r in J(os.path.join(D0, "results_N16.json"))["rows"]}
    ngu = {r["name"]: r for r in J(os.path.join(D0, "flow_a_N16.json"))["rows"]}
    return pinned, a0, a1, ng, ngu


TASKS = {"add": ["add_ripple", "add_sklansky", "add_kogge", "add_cmpcarry", "add_yosys"],
         "mul": ["mul_array", "mul_tree", "mul_wallace", "mul_tree_h", "mul_dadda_rc", "mul_dadda_ks", "mul_yosys"],
         "sbox": ["sbox_bp", "sbox_table"]}
PROVED = {"add": ["add_ripple"], "mul": ["mul_array", "mul_tree", "mul_wallace", "mul_tree_h"]}
NOTE = {"add_yosys": " (banned)", "mul_yosys": " (banned)", "add_ripple": " (proved)", "mul_array": " (proved)", "mul_tree": " (proved)",
        "mul_wallace": " (proved)", "mul_tree_h": " (proved)"}


def main():
    pinned, a0, a1, ng, ngu = load()
    out = []
    P = out.append
    for task, names in TASKS.items():
        P(f"\n### {task}, N = 16 (sbox: fixed)\n")
        cols = "| design | GE_v1 | depth_v1 | A0' um^2 | A0' GE | A0' T ps | A1'u um^2 | A1'u cells | A1'u depth | A1'u T ps | A1's um^2 | A1's T ps |" + (" Nangate A0 GE | Nangate A0 T ps |" if task != "sbox" else "")
        P(cols)
        P("|---|" + "--:|" * (cols.count("|") - 2))
        for n in names:
            u, s = a1["u"][n], a1["s"][n]
            row = f"| {n}{NOTE.get(n, '')} | {pinned[n]['area_ge']:.1f} | {pinned[n]['depth']} | {a0[n]['area_um2']:.0f} | {a0[n]['area_ge']:.1f} | {a0[n]['t_ps']:.0f} | {u['area_um2']:.0f} | {u['cells']} | {u['unit_depth']} | {u['t_ps']:.0f} | {s['area_um2']:.0f} | {s['t_ps']:.0f} |"
            if task != "sbox":
                row += f" {ng[n]['lib_area_ge']:.1f} | {ng[n]['t_nldm_ns']*1000:.0f} |"
            P(row)

        metrics = {"GE_v1": {n: pinned[n]["area_ge"] for n in names}, "A0' um2": {n: a0[n]["area_um2"] for n in names},
                   "A1'u um2": {n: a1["u"][n]["area_um2"] for n in names}, "A1's um2": {n: a1["s"][n]["area_um2"] for n in names},
                   "A1'l um2": {n: a1["l"][n]["area_um2"] for n in names}, "A1'r um2": {n: a1["r"][n]["area_um2"] for n in names}}
        tmet = {"depth_v1": {n: pinned[n]["depth"] for n in names}, "A0' T": {n: a0[n]["t_ps"] for n in names},
                "A1'u T": {n: a1["u"][n]["t_ps"] for n in names}, "A1's T": {n: a1["s"][n]["t_ps"] for n in names},
                "A1'f T": {n: a1["f"][n]["t_ps"] for n in names}, "A1'l T": {n: a1["l"][n]["t_ps"] for n in names},
                "A1'h T": {n: a1["h"][n]["t_ps"] for n in names}}
        if task != "sbox":
            metrics["Nangate A0 GE"] = {n: ng[n]["lib_area_ge"] for n in names}
            tmet["Nangate A0 T"] = {n: ng[n]["t_nldm_ns"] for n in names}
        for title, mm in (("area", metrics), ("delay", tmet)):
            P(f"\nRanks by {title} (1 = best; ties share the best rank):\n")
            P("| design | " + " | ".join(mm) + " |\n|---|" + "--:|" * len(mm))
            R = {m: ranks(v) for m, v in mm.items()}
            for n in names:
                P(f"| {n}{NOTE.get(n, '')} | " + " | ".join(str(R[m][n]) for m in mm) + " |")
            if len(names) > 2:
                P(f"\nKendall tau of the {title} rankings over the {len(names)} designs:\n")
                P("| | " + " | ".join(mm) + " |\n|---|" + "--:|" * len(mm))
                for m1 in mm:
                    P(f"| {m1} | " + " | ".join(f"{tau(mm[m1], mm[m2], names):+.2f}" for m2 in mm) + " |")
        if task in PROVED and len(PROVED[task]) > 1:
            pn = PROVED[task]
            P(f"\nThe proved {task} references only ({', '.join(pn)}), ranks by area / delay:\n")
            P("| metric | " + " | ".join(pn) + " | order |\n|---|" + "--:|" * (len(pn) + 1))
            for m, v in list(metrics.items()) + list(tmet.items()):
                sub = {n: v[n] for n in pn}
                r = ranks(sub)
                P(f"| {m} | " + " | ".join(str(r[n]) for n in pn) + " | " + " < ".join(sorted(pn, key=lambda n: sub[n])) + " |")

    # ---- compound-cell gain
    P("\n### Compound-cell gain: full library (A1'u) against the 2-input + MUX sub-library (A1'r) and against A0'\n")
    P("| design | A0' um^2 | A1'r um^2 | A1'u um^2 | u / r | u / A0' | compound cells in u | share of u cells | a21oi+o21ai | mux2 | maj3 | inv | buf |\n|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
    gains = []
    for names in TASKS.values():
        for n in names:
            u, r, a = a1["u"][n], a1["r"][n], a0[n]
            h = u["hist"]
            ao = sum(v for k, v in h.items() if k.startswith(("a21oi_", "o21ai_")))
            mx = sum(v for k, v in h.items() if k.startswith("mux2_"))
            mj = sum(v for k, v in h.items() if k.startswith("maj3_"))
            gains.append(u["area_um2"] / r["area_um2"])
            P(f"| {n} | {a['area_um2']:.0f} | {r['area_um2']:.0f} | {u['area_um2']:.0f} | {u['area_um2']/r['area_um2']:.3f} | {u['area_um2']/a['area_um2']:.3f} | {u['n_compound']} | {u['n_compound']/u['cells']:.2f} | {ao} | {mx} | {mj} | {u['n_inv']} | {u['n_buf']} |")
    P(f"\nu / r area: min {min(gains):.3f}, median {statistics.median(gains):.3f}, max {max(gains):.3f}.")

    # ---- sizing / buffering
    P("\n### Sizing and buffering at the fixed loads: A1's (buffer; upsize; dnsize) against A1'u\n")
    P("| design | u um^2 | s um^2 | s/u area | u T ps | s T ps | s/u T | cells not _0/_1 in s | buffers s | buffers u |\n|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|")
    for names in TASKS.values():
        for n in names:
            u, s = a1["u"][n], a1["s"][n]
            big = sum(v for k, v in s["hist"].items() if not k.endswith(("_0", "_1")))
            P(f"| {n} | {u['area_um2']:.0f} | {s['area_um2']:.0f} | {s['area_um2']/u['area_um2']:.3f} | {u['t_ps']:.0f} | {s['t_ps']:.0f} | {s['t_ps']/u['t_ps']:.3f} | {big} | {s['n_buf']} | {u['n_buf']} |")

    # ---- mapper-to-mapper spread
    P("\n### Mapper-to-mapper spread per design (max / min - 1 over A0' and the A1' variants u s f l h r)\n")
    P("| design | area spread | T spread | area range um^2 | T range ps | area rank range (of mappers) | A0' vs best-T mapper: T |\n|---|--:|--:|---|---|---|---|")
    sp_a, sp_t = [], []
    allv = ["A0'"] + sorted(a1)
    get = lambda v, n: (a0[n] if v == "A0'" else a1[v][n])
    for names in TASKS.values():
        for n in names:
            ar = [get(v, n)["area_um2"] for v in allv]
            tt = [get(v, n)["t_ps"] for v in allv]
            sa, st = max(ar) / min(ar) - 1, max(tt) / min(tt) - 1
            sp_a.append(sa); sp_t.append(st)
            P(f"| {n} | {sa*100:.0f}% | {st*100:.0f}% | {min(ar):.0f}..{max(ar):.0f} | {min(tt):.0f}..{max(tt):.0f} | | |")
    P(f"\nSpread over designs: area median {statistics.median(sp_a)*100:.0f}%, max {max(sp_a)*100:.0f}%; T median {statistics.median(sp_t)*100:.0f}%, max {max(sp_t)*100:.0f}%.")
    text = "\n".join(out) + "\n"
    open(os.path.join(DS, "report_N16.md"), "w").write(text)
    print(text)


if __name__ == "__main__":
    main()
