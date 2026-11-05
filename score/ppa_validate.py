#!/usr/bin/env python3.12
"""Validation of the PPA columns (score/ppa.py): the (GE, depth) against (um^2, ps) table with rank correlations, the same
for flow A1' against A0', and the agreement of the STA with ABC's own `stime -p` on netlists mapped by `abc -liberty`.
Research tool, not part of the checker; every number of score/PPA.md comes from one of these two commands.

  python3.12 score/ppa_validate.py table [--only NAME ...] [--designs FILE] [--json OUT] [--expected-out OUT]
                                         [--mapped] [--mapped-expected-out OUT]
      the pinned flow of score.py + ppa.py on every design of score/tests/ppa/designs.json (sequential, 1 to 20 s each);
      prints a Markdown table per task and Kendall's tau-b between GE and um^2, depth and ps (ties are handled).
      With --mapped (implied by --mapped-expected-out) it also maps every design (flow A1') and prints, per task, A1'
      against A0' (um^2, ps, cells, levels, ranks) with the rank correlations of GE, A0' and A1'; --mapped-expected-out
      re-records the goldens of the A1' columns (score/tests/ppa/expected_ppa_mapped.json).
  python3.12 score/ppa_validate.py stime [--only NAME ...] [--targets none,1500,...] [--json OUT]
      the canonical RTLIL of each design is mapped by `abc -liberty` (sized script, -constr buf_1 / 10 fF, several delay
      targets), ABC reports its own `stime -p` delay, and ppa.py's STA times the very same mapped netlist under the fixed
      setup (50 ps ideal ramp, 10 fF per output): the figure is |STA / stime - 1|.
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import ppa  # noqa: E402

DESIGNS = os.path.join(HERE, "tests", "ppa", "designs.json")
TARGETS = [None, 1500, 2500, 4000, 6000, 9000, 14000]   # the spike's delay targets (ps) for the sized script
# `abc -dont_use` globs equivalent to the cell policy of ppa.POLICY (everything but class "logic")
DONT_USE = ["lpflow_*", "fill_*", "decap_*", "tap*", "diode_*", "probe*", "macro_sparecell*", "df*", "sdf*", "edf*",
            "sedf*", "dlr*", "dlx*", "dlclkp_*", "sdlclkp_*", "dly*", "clk*", "ebufn_*", "einvn_*", "einvp_*",
            "fa_*", "fah*", "ha_*", "conb_*"]
SIZED = ("strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf {D}; &put; "
         "buffer; upsize {D}; dnsize {D}; stime -p")


def load_designs(only=None, path=None):
    """The designs of `path` (default designs.json; a bare file name is looked up in score/tests/ppa/; several files,
    comma-separated, are concatenated: `designs.json,idioms.json`)."""
    ds = []
    for one in (path.split(",") if path else [None]):
        if one and not os.path.dirname(one):
            one = os.path.join(os.path.dirname(DESIGNS), one)
        with open(one or DESIGNS) as fh:
            ds += json.load(fh)["designs"]
    if only:
        missing = set(only) - {d["name"] for d in ds}
        if missing:
            raise SystemExit(f"unknown designs: {sorted(missing)}")
        ds = [d for d in ds if d["name"] in only]
    return ds


def kendall_tau(xs, ys):
    """Kendall's tau-b of two equally long sequences (tie-corrected); None when one of them is constant."""
    n = len(xs)
    conc = disc = tx = ty = 0
    for i in range(n):
        for j in range(i + 1, n):
            dx, dy = xs[i] - xs[j], ys[i] - ys[j]
            if dx == 0 and dy == 0:
                continue
            if dx == 0:
                tx += 1
            elif dy == 0:
                ty += 1
            elif (dx > 0) == (dy > 0):
                conc += 1
            else:
                disc += 1
    den = ((conc + disc + tx) * (conc + disc + ty)) ** 0.5
    return None if den == 0 else (conc - disc) / den


def task_input_drive(d):
    """The input drive of the design's task (sky130_a0_v3: tasks/<task>/task.json `input_drive`, else the pins' default;
    a design of no task, the idioms, the default)."""
    path = os.path.join(SVGOLF, "tasks", d["task"], "task.json")
    task = None
    if os.path.isfile(path):
        with open(path) as fh:
            task = json.load(fh)
    return ppa.input_drive_of(task, ppa.Pins())


def measure(d, liberty=None, mapped=False):
    """One design through the pinned flow and ppa.py, its inputs driven by its task's input drive. With `mapped`, the row
    also carries the A1' columns (`m_*`; `m_error` instead when the mapping could not weigh the design)."""
    import score
    sources = [os.path.join(SVGOLF, d["src"])]
    t = time.time()
    r = ppa.score_and_weigh(sources, d["top"], d["params"], liberty, mapped=mapped, input_drive=task_input_drive(d))
    s, p = r["score"], r["ppa"]
    row = {"name": d["name"], "task": d["task"], "ref": d.get("ref", False), "banned": d.get("banned", False),
           "area_ge": s["area_ge"], "depth": s["depth"], "gates": s["num_gates"], "cells": p["cells_sky130"],
           "area_e4um2": p["area_e4um2_sky130"], "area_um2": p["area_um2_sky130"], "delay_ps": p["delay_ps_sky130"],
           "unit_depth": p["unit_depth"], "rtlil_sha256": s["rtlil_sha256"], "netlist_sha256": p["netlist_sha256"],
           "cells_before": p["repair"]["cells_before"], "repaired_sha256": p["repair"]["netlist_sha256"],
           "worst_load_ratio": p["legality"]["worst_load_ratio"]}
    m = p.get("mapped")
    if m is not None and m.get("available"):
        row.update(m_area_e4um2=m["area_e4um2_sky130_mapped_v1"], m_area_um2=m["area_um2_sky130_mapped_v1"],
                   m_delay_ps=m["mapped_delay_sky130_v1"], m_cells=m["mapped_cells_sky130_v1"],
                   m_levels=m["mapped_levels_sky130_v1"], m_buffers=m["mapped_buffers_sky130_v1"],
                   m_inverters=m["mapped_inverters_sky130_v1"], m_constants=m["constants"],
                   m_netlist_sha256=m["netlist_sha256"])
    elif m is not None:
        row["m_error"] = m["reason"]
    row["seconds"] = round(time.time() - t, 2)
    return row


def fmt_tau(x):
    return "n/a" if x is None else f"{x:+.2f}"


def table(rows):
    lines = []
    tasks = []
    for r in rows:
        if r["task"] not in tasks:
            tasks.append(r["task"])
    for task in tasks:
        rs = [r for r in rows if r["task"] == task]
        lines.append(f"\n**{task}**\n")
        lines.append("| design | GE | depth | gates | um^2 | ps | um^2 / GE | ps / level | GE rank | um^2 rank | depth rank | ps rank |")
        lines.append("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|")

        def rank(key):
            vs = sorted(r[key] for r in rs)
            return {r["name"]: 1 + vs.index(r[key]) for r in rs}      # ties share the best rank
        rg, ru, rd, rp = rank("area_ge"), rank("area_um2"), rank("depth"), rank("delay_ps")
        for r in rs:
            tag = r["name"] + (" (ref)" if r["ref"] else "") + (" (banned)" if r["banned"] else "")
            per = r["delay_ps"] / r["unit_depth"] if r["unit_depth"] else float("nan")
            lines.append(f"| {tag} | {r['area_ge']:.1f} | {r['depth']} | {r['gates']} | {r['area_um2']:.1f} | "
                         f"{r['delay_ps']} | {r['area_um2'] / r['area_ge']:.3f} | {per:.1f} | {rg[r['name']]} | "
                         f"{ru[r['name']]} | {rd[r['name']]} | {rp[r['name']]} |")
        if len(rs) >= 3:
            ta = kendall_tau([r["area_ge"] for r in rs], [r["area_um2"] for r in rs])
            td = kendall_tau([r["depth"] for r in rs], [r["delay_ps"] for r in rs])
            lines.append(f"\nKendall tau-b over {len(rs)} designs: GE vs um^2 {fmt_tau(ta)}, depth vs ps {fmt_tau(td)}.")
    return "\n".join(lines)


def mapped_table(rows):
    """Flow A1' against A0' per task: area, delay, cells, cell levels and ranks, then Kendall's tau-b of the rankings."""
    lines = []
    tasks = []
    for r in rows:
        if r["task"] not in tasks:
            tasks.append(r["task"])
    for task in tasks:
        rs = [r for r in rows if r["task"] == task and "m_area_um2" in r]
        if not rs:
            continue
        lines.append(f"\n**{task}: A1' (real abc -liberty mapping) against A0'**\n")
        lines.append("| design | GE | A0' um^2 | A1' um^2 | A1'/A0' | A0' ps | A1' ps | A1'/A0' | A0' cells | A1' cells | "
                     "A1' levels | A1' buf+inv | A0' area rank | A1' area rank | A0' ps rank | A1' ps rank |")
        lines.append("|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|")

        def rank(key):
            vs = sorted(r[key] for r in rs)
            return {r["name"]: 1 + vs.index(r[key]) for r in rs}
        ra0, ra1, rp0, rp1 = rank("area_um2"), rank("m_area_um2"), rank("delay_ps"), rank("m_delay_ps")
        for r in rs:
            tag = r["name"] + (" (ref)" if r["ref"] else "") + (" (banned)" if r["banned"] else "")
            lines.append(f"| {tag} | {r['area_ge']:.1f} | {r['area_um2']:.1f} | {r['m_area_um2']:.1f} | "
                         f"{r['m_area_um2'] / r['area_um2']:.3f} | {r['delay_ps']} | {r['m_delay_ps']} | "
                         f"{r['m_delay_ps'] / r['delay_ps']:.3f} | {r['cells']} | {r['m_cells']} | {r['m_levels']} | "
                         f"{r['m_buffers'] + r['m_inverters']} | {ra0[r['name']]} | {ra1[r['name']]} | "
                         f"{rp0[r['name']]} | {rp1[r['name']]} |")
        if len(rs) >= 3:
            def t(x, y):
                return fmt_tau(kendall_tau([r[x] for r in rs], [r[y] for r in rs]))
            lines.append(f"\nKendall tau-b over {len(rs)} designs: area GE vs A0' {t('area_ge', 'area_um2')}, "
                         f"GE vs A1' {t('area_ge', 'm_area_um2')}, A0' vs A1' {t('area_um2', 'm_area_um2')}; "
                         f"delay depth vs A0' {t('depth', 'delay_ps')}, depth vs A1' {t('depth', 'm_delay_ps')}, "
                         f"A0' vs A1' {t('delay_ps', 'm_delay_ps')}.")
    return "\n".join(lines)


def cmd_table(args):
    lib, pins = ppa.open_library(args.liberty)
    mapped = bool(args.mapped or args.mapped_expected_out)
    rows = []
    for d in load_designs(args.only, args.designs):
        try:
            r = measure(d, args.liberty, mapped)
        except Exception as e:                                   # a design that does not score is reported, not hidden
            print(f"{d['name']}: FAILED: {e}", file=sys.stderr)
            continue
        rows.append(r)
        print(f"# {r['name']}: GE {r['area_ge']} depth {r['depth']} -> {r['area_um2']} um^2, {r['delay_ps']} ps "
              f"({r['seconds']} s)", file=sys.stderr, flush=True)
    print(table(rows))
    if mapped:
        print(mapped_table(rows))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"liberty_sha256": lib.sha256, "ppa_version": pins.version, "rows": rows}, fh, indent=1, sort_keys=True)
    if args.expected_out:
        gold = {r["name"]: {k: r[k] for k in ("area_ge", "depth", "gates", "cells", "area_e4um2", "delay_ps",
                                              "unit_depth", "rtlil_sha256", "netlist_sha256", "repaired_sha256")}
                for r in rows}
        with open(args.expected_out, "w") as fh:
            json.dump({"ppa_version": pins.version, "liberty_sha256": lib.sha256, "designs": gold}, fh, indent=1, sort_keys=True)
    if args.mapped_expected_out:
        bad = [r["name"] for r in rows if "m_area_um2" not in r]
        if bad:
            print(f"error: not recording goldens, the mapping did not weigh {bad}", file=sys.stderr)
            return 1
        import score
        mpins = ppa.MappedPins(pins)
        yv = score.yosys_version(score.yosys_bin())
        gold = {r["name"]: {"rtlil_sha256": r["rtlil_sha256"], "area_e4um2": r["m_area_e4um2"],
                            "delay_ps": r["m_delay_ps"], "cells": r["m_cells"], "levels": r["m_levels"],
                            "buffers": r["m_buffers"], "inverters": r["m_inverters"], "constants": r["m_constants"],
                            "netlist_sha256": r["m_netlist_sha256"]} for r in rows}
        with open(args.mapped_expected_out, "w") as fh:
            json.dump({"ppa_mapped_version": mpins.version, "liberty_sha256": lib.sha256,
                       "ppa_mapped_script_sha256": mpins.script_sha256, "yosys_version": yv,
                       "abc_version": ppa.abc_version(score.yosys_bin()), "designs": gold}, fh, indent=1, sort_keys=True)
    return 0


def abc_map(rtlil, top, out_v, libp, constr, D, yosys, prefix):
    dont = " ".join(f"-dont_use {prefix}{p}" for p in DONT_USE)
    script = SIZED.replace(" ", ",")
    abc = f"abc -liberty {libp} {dont} -constr {constr}" + (f" -D {D}" if D else "") + f" -script +{script}"
    ys = (f"read_rtlil {rtlil}\nsynth -flatten -top {top}\n{abc}\nopt_clean -purge\n"
          f"write_verilog -noattr -noexpr {out_v}\n")
    ysf = out_v + ".ys"
    with open(ysf, "w") as fh:
        fh.write(ys)
    log = out_v + ".log"
    r = subprocess.run([yosys, "-q", "-l", log, ysf], capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        raise SystemExit(f"yosys failed: {r.stderr[-800:]}{r.stdout[-800:]}")
    with open(log) as fh:
        m = re.findall(r"Delay =\s+([\d.]+) ps", fh.read())
    if not m:
        raise SystemExit(f"no `stime` delay in {log}")
    return float(m[-1])



def cmd_stime(args):
    import score
    lib, pins = ppa.open_library(args.liberty)
    yosys = args.yosys or score.yosys_bin()
    targets = TARGETS if not args.targets else [None if t == "none" else int(t) for t in args.targets.split(",")]
    rows = []
    with tempfile.TemporaryDirectory(prefix="svgolf-ppa-val-") as work:
        constr = os.path.join(work, "abc.constr")
        with open(constr, "w") as fh:
            fh.write(f"set_driving_cell {pins.prefix}buf_1\nset_load {round(pins.po_load_pf * 1000):g}\n")
        for d in load_designs(args.only, args.designs):
            il = os.path.join(work, d["name"] + ".il")
            score.score([os.path.join(SVGOLF, d["src"])], d["top"], d["params"], yosys, rtlil_out=il)
            for D in targets:
                out = os.path.join(work, f"{d['name']}.D{D}.v")
                stime = abc_map(il, d["top"], out, lib.path, constr, D, yosys, pins.prefix)
                with open(out) as fh:
                    a = ppa.analyze_cells(ppa.parse_netlist(fh.read()), lib, pins)
                t_ps = a.t_ns * 1000
                row = {"name": d["name"], "D": D, "cells": a.cells, "area_um2": a.area_e4 / 10000,
                       "sta_ps": round(t_ps, 2), "abc_stime_ps": stime, "err": t_ps / stime - 1}
                rows.append(row)
                print(f"{d['name']:14s} D={str(D):6s} cells {a.cells:5d} STA {t_ps:9.2f} ps  ABC stime {stime:9.2f} ps  "
                      f"{100 * row['err']:+6.2f}%", file=sys.stderr, flush=True)
    errs = [abs(r["err"]) for r in rows]
    summary = {"netlists": len(rows), "mean_abs_err": sum(errs) / len(errs), "max_abs_err": max(errs),
               "mean_signed_err": sum(r["err"] for r in rows) / len(rows)}
    by = {}
    for r in rows:
        by.setdefault(r["name"], []).append(abs(r["err"]))
    summary["per_design_mean_abs_err"] = {k: sum(v) / len(v) for k, v in by.items()}
    print(f"STA against ABC stime -p, fixed setup, {len(rows)} abc -liberty netlists (sized script, "
          f"{len(targets)} delay targets): mean |err| {100 * summary['mean_abs_err']:.2f}%, "
          f"max {100 * summary['max_abs_err']:.2f}%, mean signed {100 * summary['mean_signed_err']:+.2f}%")
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"liberty_sha256": lib.sha256, "summary": summary, "rows": rows}, fh, indent=1, sort_keys=True)
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("table", "stime"):
        p = sub.add_parser(name)
        p.add_argument("--only", nargs="*")
        p.add_argument("--designs", help="a designs file (default designs.json; idioms.json: the netlist-reader idioms; "
                       "several, comma-separated: designs.json,idioms.json)")
        p.add_argument("--liberty")
        p.add_argument("--json")
        if name == "table":
            p.add_argument("--expected-out")
            p.add_argument("--mapped", action="store_true")
            p.add_argument("--mapped-expected-out")
        else:
            p.add_argument("--targets")
            p.add_argument("--yosys")
    args = ap.parse_args(argv)
    try:
        return {"table": cmd_table, "stime": cmd_stime}[args.cmd](args)
    except ppa.PpaError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
