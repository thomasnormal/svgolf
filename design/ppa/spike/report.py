#!/usr/bin/env python3.12
"""Turn data/*.json into the spike's tables and ranking comparisons (Markdown on stdout).

  python3.12 report.py --n 16
"""
import argparse, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    p = os.path.join(HERE, "data", name)
    return json.load(open(p)) if os.path.exists(p) else None


def ranks(vals, key, rev=False):
    """Dense-free competition ranks (1 = best); ties share the best rank."""
    order = sorted(vals, key=lambda r: key(r), reverse=rev)
    out, prev, rk = {}, None, 0
    for i, r in enumerate(order):
        k = key(r)
        if prev is None or k != prev:
            rk = i + 1
        out[r["name"]] = rk
        prev = k
    return out


def kendall(r1, r2):
    names = list(r1)
    c = d = 0
    for a, b in itertools.combinations(names, 2):
        x = (r1[a] > r1[b]) - (r1[a] < r1[b])
        y = (r2[a] > r2[b]) - (r2[a] < r2[b])
        if x * y > 0:
            c += 1
        elif x * y < 0:
            d += 1
    return (c - d) / (c + d) if c + d else 1.0


def pareto(rows, keys):
    out = []
    for r in rows:
        dom = any(all(o[k] <= r[k] for k in keys) and any(o[k] < r[k] for k in keys) for o in rows)
        if not dom:
            out.append(r["name"])
    return out


def md(rows, cols, fmt=None):
    fmt = fmt or {}
    s = "| " + " | ".join(c for c, _ in cols) + " |\n|" + "|".join("---" if i == 0 else "--:" for i, _ in enumerate(cols)) + "|\n"
    for r in rows:
        s += "| " + " | ".join(fmt.get(k, lambda v: str(v))(r[k]) if k in r else "" for _, k in cols) + " |\n"
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=16)
    a = ap.parse_args()
    res = load(f"results_N{a.n}.json")
    if not res:
        sys.exit("run run_spike.py first")
    rows = res["rows"]
    for r in rows:
        r["task"] = r["name"].split("_")[0]
        r["e_best"] = r.get("e_dyn_glitch_fj", r["e_dyn_fj"]) + r["e_leak_fj"]
        r["edp_zero"] = (r["e_dyn_fj"] + r["e_leak_fj"]) * r["t_nldm_ns"]
        r["edp_gl"] = r["e_best"] * r["t_nldm_ns"]
        r["at"] = r["lib_area_ge"] * r["t_nldm_ns"]
        r["at_ge_depth"] = r["area_ge"] * r["depth"]
    out = []
    f1 = lambda v: f"{v:.1f}"
    f2 = lambda v: f"{v:.2f}"
    f3 = lambda v: f"{v:.3f}"
    for task in ("add", "mul"):
        t = [r for r in rows if r["task"] == task]
        out.append(f"\n### {task}, N = {a.n}\n")
        out.append(md(t, [("design", "name"), ("GE (score)", "area_ge"), ("depth (ltp)", "depth"), ("gates", "gates"),
                          ("lib GE", "lib_area_ge"), ("depth, INV-expanded", "unit_depth_expanded"),
                          ("LE delay (tau)", "t_le_tau"), ("NLDM delay (ns)", "t_nldm_ns")],
                      {"area_ge": f1, "lib_area_ge": f1, "t_le_tau": f1, "t_nldm_ns": f3}))
        out.append("\nEnergy per operation (fJ), uniform random inputs, Nangate45 typical 1.1 V:\n\n")
        out.append(md(t, [("design", "name"), ("toggles/op", "toggles_per_op_gates"), ("E_sw", "e_sw_fj"), ("E_int", "e_int_fj"),
                          ("E_dyn (zero-delay)", "e_dyn_fj"), ("E_dyn (glitch-aware)", "e_dyn_glitch_fj"),
                          ("glitch x", "glitch_factor"), ("E_leak", "e_leak_fj")],
                      {"toggles_per_op_gates": f1, "e_sw_fj": f1, "e_int_fj": f1, "e_dyn_fj": f1, "e_dyn_glitch_fj": f1,
                       "glitch_factor": f2, "e_leak_fj": f2}))
        out.append("\nCombined figures (area in lib GE, T = NLDM ns, E = glitch-aware dynamic + leakage, fJ):\n\n")
        out.append(md(t, [("design", "name"), ("AT", "AT"), ("AT^2", "AT2"), ("EDP (fJ.ns)", "edp_gl"), ("EDP zero-delay E", "edp_zero"),
                          ("ED^2P", "ED2P"), ("ops per pJ", "perf_per_energy"), ("power at 1/T (mW)", "power_mw_at_fmax")],
                      {"AT": f1, "AT2": f1, "edp_gl": f1, "edp_zero": f1, "ED2P": f1, "perf_per_energy": f3, "power_mw_at_fmax": f3}))
        # rankings
        R = {
            "GE": ranks(t, lambda r: r["area_ge"]),
            "depth": ranks(t, lambda r: r["depth"]),
            "LE": ranks(t, lambda r: r["t_le_tau"]),
            "NLDM": ranks(t, lambda r: r["t_nldm_ns"]),
            "AT(GE x depth)": ranks(t, lambda r: r["at_ge_depth"]),
            "AT(NLDM)": ranks(t, lambda r: r["at"]),
            "E zero-delay": ranks(t, lambda r: r["e_dyn_fj"]),
            "E glitch-aware": ranks(t, lambda r: r["e_best"]),
            "EDP (zero-delay E)": ranks(t, lambda r: r["edp_zero"]),
            "EDP (glitch E)": ranks(t, lambda r: r["edp_gl"]),
        }
        out.append("\nRanks (1 = best; ties share a rank):\n\n| design | " + " | ".join(R) + " |\n|---|" + "--:|" * len(R) + "\n")
        for r in t:
            out.append(f"| {r['name']} | " + " | ".join(str(R[k][r["name"]]) for k in R) + " |\n")
        out.append("\nKendall tau against the present score components:\n\n| metric | tau vs GE | tau vs depth |\n|---|--:|--:|\n")
        for k in R:
            out.append(f"| {k} | {kendall(R[k], R['GE']):+.2f} | {kendall(R[k], R['depth']):+.2f} |\n")
        out.append("\nPareto frontiers (non-dominated designs):\n\n")
        for label, keys in (("(GE, depth) = present", ("area_ge", "depth")),
                            ("(GE, LE delay)", ("area_ge", "t_le_tau")),
                            ("(lib GE, NLDM delay)", ("lib_area_ge", "t_nldm_ns")),
                            ("(GE, depth, E zero-delay)", ("area_ge", "depth", "e_dyn_fj")),
                            ("(lib GE, NLDM delay, E glitch-aware)", ("lib_area_ge", "t_nldm_ns", "e_best")),
                            ("(E glitch-aware, NLDM delay)", ("e_best", "t_nldm_ns"))):
            out.append(f"* {label}: {', '.join(pareto(t, keys))}\n")
        legal = [r for r in t if not r["name"].endswith("yosys")]
        out.append("\nSame, without the banned-operator baseline (`*_yosys`):\n\n")
        for label, keys in (("(GE, depth)", ("area_ge", "depth")), ("(lib GE, NLDM delay)", ("lib_area_ge", "t_nldm_ns")),
                            ("(lib GE, NLDM delay, E glitch-aware)", ("lib_area_ge", "t_nldm_ns", "e_best")),
                            ("(E glitch-aware, NLDM delay)", ("e_best", "t_nldm_ns"))):
            out.append(f"* {label}: {', '.join(pareto(legal, keys))}\n")
    PROVED = {"add_ripple", "mul_array", "mul_tree", "mul_wallace", "mul_tree_h"}
    pr = [r for r in rows if r["name"] in PROVED]
    out.append("\n### Proved references only (the designs that can be entries today)\n\n")
    for label, keys in (("(GE, depth) = present", ("area_ge", "depth")), ("(lib GE, NLDM delay)", ("lib_area_ge", "t_nldm_ns")),
                        ("(lib GE, NLDM delay, E glitch-aware)", ("lib_area_ge", "t_nldm_ns", "e_best")),
                        ("(E glitch-aware, NLDM delay)", ("e_best", "t_nldm_ns")),
                        ("(E zero-delay, NLDM delay)", ("e_dyn_fj", "t_nldm_ns"))):
        out.append(f"* mul {label}: {', '.join(pareto([r for r in pr if r['task'] == 'mul'], keys))}\n")
    print("".join(out))
    print(sections(a.n))


def sections(n):
    out = []
    # ---- seeds
    base = {r["name"]: r for r in load(f"results_N{n}.json")["rows"]}
    sd = [load(f"results_N{n}_seed{k}.json") for k in (2, 3)]
    if all(sd):
        out.append("\n### Sampling noise of the zero-delay energy (seeds 1, 2, 3; 2000 vector transitions each)\n\n| design | E_dyn seed 1 | seed 2 | seed 3 | max spread |\n|---|--:|--:|--:|--:|\n")
        worst = 0
        for name, r in base.items():
            v = [r["e_dyn_fj"]] + [x["e_dyn_fj"] for s_ in sd for x in s_["rows"] if x["name"] == name]
            sp = (max(v) - min(v)) / (sum(v) / len(v))
            worst = max(worst, sp)
            out.append(f"| {name} | {v[0]:.1f} | {v[1]:.1f} | {v[2]:.1f} | {100*sp:.2f} % |\n")
        out.append(f"\nLargest spread: {100*worst:.2f} %.\n")
    # ---- flow A
    fa_u = load(f"flow_a_N{n}_energy.json")
    fa_s0 = load(f"flow_a_N{n}_sized_energy.json")
    fa_sw = load(f"flow_a_N{n}_sized.json")
    if fa_u and fa_s0 and fa_sw:
        U = {r["name"]: r for r in fa_u["rows"]}
        S0 = {r["name"]: r for r in fa_s0["rows"]}
        out.append("\n### Flow A: `abc -liberty` (Nangate45) re-mapping of the same canonical RTLIL\n\n")
        out.append("`&nf` = ABC's default liberty script (no sizing); `fast` = `-constr` flow with `buffer; upsize; dnsize` and no delay target; `loose` = same with the loosest target of the sweep. GE = um^2 / 0.798. T = engine NLDM STA (ABC `stime` agrees within 1.3 % on average).\n\n")
        out.append("| design | &nf GE | &nf T (ns) | &nf E_dyn zero (fJ) | &nf E_dyn glitch (fJ) | fast GE | fast T | fast E_dyn zero | fast E_dyn glitch | loose GE | loose T |\n|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|\n")
        loose = {}
        for r in fa_sw["rows"]:
            if r["name"] not in loose or r["D"] > loose[r["name"]]["D"]:
                loose[r["name"]] = r
        order = [r["name"] for r in load(f"results_N{n}.json")["rows"]]
        for name in order:
            u, f, l = U[name], S0[name], loose[name]
            out.append(f"| {name} | {u['area_ge']:.1f} | {u['t_nldm_ns']:.3f} | {u['e_dyn_fj']:.0f} | {u.get('e_dyn_glitch_fj', 0):.0f} | {f['area_ge']:.1f} | {f['t_nldm_ns']:.3f} | {f['e_dyn_fj']:.0f} | {f.get('e_dyn_glitch_fj', 0):.0f} | {l['area_ge']:.1f} | {l['t_nldm_ns']:.3f} |\n")
        errs = [abs(r["abc_stime_ps"] / 1000 - r["t_nldm_ns"]) / r["t_nldm_ns"] for r in fa_sw["rows"] if r.get("abc_stime_ps")]
        out.append(f"\nABC `stime` vs the engine's NLDM STA over {len(errs)} sized netlists: mean |difference| {100*sum(errs)/len(errs):.2f} %, max {100*max(errs):.2f} %.\n")
        for task in ("add", "mul"):
            pts = [r for r in fa_sw["rows"] if r["name"].startswith(task + "_")] + [dict(r, D="nf") for r in fa_u["rows"] if r["name"].startswith(task + "_")]
            pts = [dict(r, area=r["area_ge"], t=r["t_nldm_ns"]) for r in pts]
            front = [r for r in pts if not any((o["area"] <= r["area"] and o["t"] <= r["t"]) and (o["area"] < r["area"] or o["t"] < r["t"]) for o in pts)]
            seen, uniq = set(), []
            for r in sorted(front, key=lambda r: (r["area"], r["t"])):
                k = (r["name"], round(r["area"], 2), round(r["t"], 4))
                if k not in seen:
                    seen.add(k)
                    uniq.append(r)
            out.append(f"\nFlow A frontier over all designs and delay targets, {task} (area GE, T ns): " + "; ".join(f"{r['name']}@D{r['D']} ({r['area']:.0f}, {r['t']:.3f})" for r in uniq) + "\n")
    # ---- mapper comparison
    l8 = load(f"flow_a_N{n}_svgolf8_energy.json")
    if fa_u and l8:
        base = {r["name"]: r for r in load(f"results_N{n}.json")["rows"]}
        U = {r["name"]: r for r in fa_u["rows"]}
        L8 = {r["name"]: r for r in l8["rows"]}
        out.append("\n### Three mappings of the same canonical RTLIL (area in GE-equivalents = um^2 / 0.798; T by the same NLDM STA)\n\n")
        for task in ("add", "mul"):
            out.append("| design | `abc -g` + Nangate expansion (the scored netlist): GE / T | `abc -liberty` full Nangate45 (&nf): GE / T | `abc -liberty` 9-cell subset (&nf): GE / T |\n|---|--:|--:|--:|\n")
            names = [nm for nm in base if nm.startswith(task + "_")]
            for nm in names:
                out.append(f"| {nm} | {base[nm]['lib_area_ge']:.1f} / {base[nm]['t_nldm_ns']:.3f} | {U[nm]['area_ge']:.1f} / {U[nm]['t_nldm_ns']:.3f} | {L8[nm]['area_ge']:.1f} / {L8[nm]['t_nldm_ns']:.3f} |\n")
            rows_ = [dict(name=nm, a=base[nm]["t_nldm_ns"], b=U[nm]["t_nldm_ns"], c=L8[nm]["t_nldm_ns"],
                          ga=base[nm]["lib_area_ge"], gb=U[nm]["area_ge"], gc=L8[nm]["area_ge"]) for nm in names]
            ra, rb, rc = (ranks(rows_, lambda r, k=k: r[k]) for k in "abc")
            ga, gb, gc = (ranks(rows_, lambda r, k=k: r[k]) for k in ("ga", "gb", "gc"))
            out.append(f"\n{task}: Kendall tau of the delay ranking between mappings: scored-vs-full {kendall(ra, rb):+.2f}, scored-vs-subset {kendall(ra, rc):+.2f}, full-vs-subset {kendall(rb, rc):+.2f}; of the area ranking: {kendall(ga, gb):+.2f}, {kendall(ga, gc):+.2f}, {kendall(gb, gc):+.2f}.\n\n")
    # ---- N sweep
    out.append("\n### Sensitivity to N (NLDM delay in ns, GE, ltp depth)\n\n")
    for task in ("add", "mul"):
        out.append(f"\n{task}:\n\n| design | " + " | ".join(f"N={k}: GE / depth / T" for k in (8, 16, 32, 64)) + " |\n|---|" + "--:|" * 4 + "\n")
        names = []
        data = {}
        for k in (8, 16, 32, 64):
            d = load(f"results_N{k}.json")
            if not d:
                continue
            for r in d["rows"]:
                if r["name"].startswith(task + "_"):
                    data[(r["name"], k)] = r
                    if r["name"] not in names:
                        names.append(r["name"])
        for nm in names:
            cells = []
            for k in (8, 16, 32, 64):
                r = data.get((nm, k))
                cells.append(f"{r['area_ge']:.0f} / {r['depth']} / {r['t_nldm_ns']:.2f}" if r else "-")
            out.append(f"| {nm} | " + " | ".join(cells) + " |\n")
        for k in (8, 16, 32, 64):
            rs = [data[(nm, k)] for nm in names if (nm, k) in data]
            if len(rs) < 2:
                continue
            rd = ranks(rs, lambda r: r["depth"]); rt = ranks(rs, lambda r: r["t_nldm_ns"]); rl = ranks(rs, lambda r: r["t_le_tau"])
            diff = [nm for nm in rd if rd[nm] != rt[nm]]
            out.append(f"\nN={k}: delay rank by depth vs NLDM differs for: {', '.join(diff) or 'none'}; Kendall tau(depth, NLDM) = {kendall(rd, rt):+.2f}, tau(depth, LE) = {kendall(rd, rl):+.2f}, tau(LE, NLDM) = {kendall(rl, rt):+.2f}\n")
    # ---- FPGA
    fp = load(f"fpga_N{n}.json")
    if fp:
        out.append("\n### FPGA lane (Yosys only): LUT count and LUT levels\n\n| design | GE | LUT4 | LUT4 levels | LUT6 | LUT6 levels | synth_ice40 LUT4 (+CARRY) | synth_xilinx xc7 LUT (+MUXF, CARRY4) |\n|---|--:|--:|--:|--:|--:|--:|--:|\n")
        ge = {r["name"]: r["area_ge"] for r in load(f"results_N{n}.json")["rows"]}
        for r in fp:
            out.append(f"| {r['name']} | {ge[r['name']]:.0f} | {r['lut4']} | {r['lut4_levels']} | {r['lut6']} | {r['lut6_levels']} | {r['ice40_lut4']} (+{r['ice40_carry']}) | {r['xc7_lut']} (+{r['xc7_muxf']}, {r['xc7_carry']}) |\n")
    return "".join(out)


if __name__ == "__main__":
    main()
