#!/usr/bin/env python3.12
"""svGolf scorer: area (NAND2 gate equivalents) and depth of a SystemVerilog design.

The design is synthesized by the PINNED two-stage flow (Yosys + ABC onto
two-input gates and MUX), the gate counts are weighted by the PINNED table
`score/ge.json`, and depth is the `ltp -noff` length (gates on the longest
input-to-output path). Lower is better on both axes. These two are EXTRA
columns: the ranked score is sky130 A0' (score/ppa.py: cell area in um^2 and
delay in ps of the same scored netlist), which the leaderboard ranks;
`--pareto` lists the (area, depth) Pareto frontier of these columns.

The two stages run in two Yosys processes:

1. `score/canon.ys` (CANONICALIZATION): read the sources, elaborate at the
   parameter point, lower processes, flatten, strip every source location and
   original name, number every non-port wire and cell, and write the CANONICAL
   RTLIL;
2. `score/svgolf.ys` (SYNTHESIS AND MEASUREMENT), in a FRESH process: read the
   canonical RTLIL, `synth -flatten`, `abc -g ...`, `opt_clean`, `stat -json`,
   `ltp -noff`, and write the scored gate netlist (for the checker's
   `postsynth` stage).

A fresh process matters: Yosys's results depend on process-global state that
the frontend's history of names leaves behind, so with one process the same
circuit scored differently under a different layout, different names or a
different item order (README.md, "Scoring"). Every result records the sha256
of the canonical RTLIL (`rtlil_sha256`): equal canonical RTLIL, equal score.

Every source first goes through the source gate (`srcgate.py`): a file with
preprocessor directives, attributes, synthesis-pragma comments or
`unique`/`priority` qualifiers is refused, and Yosys reads the gate's
CANONICAL text (comments stripped), the same text the extractor reads. Without
the gate, `` `ifdef SYNTHESIS `` or `// synopsys translate_off` would let Yosys
score a different program from the one that was proved.

Usage:
  python3.12 score/score.py SOLUTION.sv [MORE.sv ...] --top TOP [--param N=16 ...]
  python3.12 score/score.py SOLUTION.sv --task tasks/<name>   # top + scoring point
  python3.12 score/score.py --pareto RESULT.json [RESULT.json ...]

Options:
  --json OUT      also write the result JSON to OUT
  --netlist OUT   also write the scored gate netlist (Verilog) to OUT
  --rtlil OUT     also write the canonical RTLIL (stage 1's output) to OUT
  --repeat K      synthesize K times and fail unless all K results are identical
  --yosys PATH    the Yosys binary (default: $SVGOLF_YOSYS, else `yosys` on PATH)
  --no-gate       score the files as they are (research only: an ungated
                  score is not an svGolf score, and the result says so)
  --seq           the CLOCKED flow: score/svgolf_seq.ys (svgolf.ys plus
                  `dfflegalize -cell $_DFF_P_ x`) and score/ge_seq.json (the
                  legacy weights plus DFF_P, derived from the pinned sky130
                  liberty by derive_seq_prices.py); the result adds flow,
                  ffs, area_ff_mge, area_comb_mge, reg_overhead_nand2 and
                  period (= depth)
  --reg-overhead  with --seq: period = depth + ceil(reg_overhead_nand2)
                  (dfxtp_1 clock-to-Q + setup in nand2 delays; not ruled)

The result JSON (stdout) has: top, params, gates (count per gate type),
num_gates, area_ge, area_mge (integer milli-GE, the exact value), depth,
rtlil_sha256, yosys_version, script_sha256 (svgolf.ys), canon_script_sha256
(canon.ys), ge_table_sha256, gated, sources (path, sha256 of the file, sha256
of the canonical text Yosys read).
Exit status: 0 = scored, 1 = the gate refused a source, synthesis failed, or
the netlist has a cell the GE table does not price (a latch or flip-flop, for
instance), 2 = usage error.
"""

import argparse
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile

# the checker's sandbox package (environment scrub: no checker secret reaches a child process)
_CHECK_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "check")
if _CHECK_DIR not in sys.path:
    sys.path.insert(0, _CHECK_DIR)
import sandbox  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "svgolf.ys")         # stage 2: synthesis and measurement
CANON_SCRIPT = os.path.join(HERE, "canon.ys")    # stage 1: canonicalization
GE_TABLE = os.path.join(HERE, "ge.json")
# The CLOCKED flow (`--seq`): svgolf.ys plus `dfflegalize` (svgolf_seq.ys) and the legacy weights plus the flop price
# derived from the pinned sky130 liberty (ge_seq.json, written by derive_seq_prices.py). Separate files, so the
# combinational flow, its hashes and every combinational record are untouched.
SCRIPT_SEQ = os.path.join(HERE, "svgolf_seq.ys")
GE_SEQ = os.path.join(HERE, "ge_seq.json")
FLOP_TYPES = {"DFF_P"}
FLOWS = {"comb": (SCRIPT, GE_TABLE), "seq": (SCRIPT_SEQ, GE_SEQ)}
# Cell types that carry no logic and are not scored (Yosys keeps one
# `$scopeinfo` cell per flattened instance, for debug info only).
IGNORED_CELLS = {"$scopeinfo"}
YOSYS_TIMEOUT_S = 1800


class ScoreError(Exception):
    pass


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load_ge_table(path=GE_TABLE):
    with open(path) as fh:
        table = json.load(fh)
    # Integer milli-GE weights, so that areas add up exactly.
    return {k: round(v * 1000) for k, v in table.items() if not k.startswith("_")}


def yosys_bin(explicit=None):
    return explicit or os.environ.get("SVGOLF_YOSYS") or "yosys"


def yosys_version(yosys):
    out = subprocess.run([yosys, "-V"], capture_output=True, text=True, check=True,
                         env=sandbox.scrubbed_env())
    return out.stdout.strip()


def fill_template(template_path, fill):
    """A pinned script with its @NAME@ placeholders filled (comment lines dropped)."""
    with open(template_path) as fh:
        text = fh.read()
    body = [ln for ln in text.splitlines() if not ln.lstrip().startswith("#")]
    out = "\n".join(body) + "\n"
    for k, v in fill.items():
        out = out.replace(k, v)
    if re.search(r"@[A-Z]+@", out):
        raise ScoreError(f"unfilled placeholder in {template_path}")
    return out


def render_canon(sources, top, params, rtlil_path, template_path=CANON_SCRIPT):
    """Stage 1 (canon.ys), filled."""
    return fill_template(template_path, {
        "@SOURCES@": "\n".join(f'read_verilog -sv "{os.path.abspath(s)}"' for s in sources),
        "@TOP@": top,
        "@CHPARAM@": "".join(f" -chparam {k} {int(v)}" for k, v in params.items()),
        "@RTLIL@": f'"{rtlil_path}"',
    })


def render_script(rtlil_path, top, stat_path, ltp_path, netlist_path, template_path=SCRIPT):
    """Stage 2 (svgolf.ys), filled."""
    return fill_template(template_path, {
        "@RTLIL@": f'"{rtlil_path}"',
        "@TOP@": top,
        "@STAT@": f'"{stat_path}"',
        "@LTP@": f'"{ltp_path}"',
        "@NETLIST@": f'"{netlist_path}"',
    })


def yosys_run(cmd, yosys, workdir, reads=(), timeout=None, label="yosys"):
    """One Yosys process on submitted text, through the sandbox (check/sandbox): it may read `reads` (the
    sources, the netlist) and the system and package trees, and write `workdir` only. Without an active
    sandbox this is `subprocess.run` with the scrubbed environment."""
    exe = shutil.which(yosys) or yosys
    spec = sandbox.tool_spec([exe], read=[os.path.abspath(r) for r in reads] + [workdir], write=[workdir],
                             label=label)
    return sandbox.run(cmd, spec, env=sandbox.tool_env(workdir) if sandbox.policy().active else None,
                       cwd=workdir, timeout=timeout, kind="tool", label=label)


def run_yosys(yosys, script_text, workdir, name="run", reads=()):
    path = os.path.join(workdir, f"{name}.ys")
    with open(path, "w") as fh:
        fh.write(script_text)
    log = os.path.join(workdir, f"{name}.log")
    try:
        proc = yosys_run([yosys, "-q", "-l", log, "-s", path], yosys, workdir, reads, YOSYS_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        raise ScoreError(f"yosys timed out after {YOSYS_TIMEOUT_S}s")
    if proc.returncode != 0:
        tail = (proc.stderr or proc.stdout)[-3000:]
        raise ScoreError(f"yosys failed (exit {proc.returncode}):\n{tail}")


def parse_stat(path, top):
    with open(path) as fh:
        data = json.load(fh)
    mods = data.get("modules", {})
    key = "\\" + top
    if key not in mods:
        raise ScoreError(f"`stat -json` has no module {top!r} (modules: {sorted(mods)})")
    return mods[key].get("num_cells_by_type", {})


LTP_RE = re.compile(r"Longest topological path in \S+ \(length=(\d+)\)")


def parse_ltp(path):
    with open(path) as fh:
        text = fh.read()
    m = LTP_RE.search(text)
    if not m:
        raise ScoreError(f"could not parse `ltp -noff` output:\n{text[-1000:]}")
    return int(m.group(1))


def gate_sources(sources, workdir):
    """Canonical copies of `sources` in `workdir` (source gate, srcgate.py),
    and their sha256s. Raises ScoreError with the gate's findings."""
    if HERE not in sys.path:
        sys.path.insert(0, HERE)
    try:
        import srcgate
    except ImportError as e:
        raise ScoreError(f"the source gate needs pyslang (python3.12): {e}")
    out, shas, findings = [], [], []
    for i, s in enumerate(sources):
        dst = os.path.join(workdir, f"src{i}_{os.path.basename(s)}")
        try:
            shas.append(srcgate.canonicalize(s, dst, name=s))
        except srcgate.GateError as e:
            findings += str(e).splitlines()
        out.append(dst)
    if findings:
        raise ScoreError("the source gate refused the design (Yosys and the extractor "
                         "would read different programs):\n" + "\n".join(findings))
    return out, shas


def score_once(sources, top, params, yosys, netlist_out=None, rtlil_out=None, flow="comb"):
    """One run of the two-stage flow. With `netlist_out` / `rtlil_out`, the
    scored netlist / the canonical RTLIL are copied there. `flow` is "comb"
    (svgolf.ys, ge.json) or "seq" (svgolf_seq.ys, ge_seq.json)."""
    script, table = FLOWS[flow]
    ge = load_ge_table(table)
    workdir = tempfile.mkdtemp(prefix="svgolf-score-")
    try:
        rtlil = os.path.join(workdir, "canon.il")
        stat_path = os.path.join(workdir, "stat.json")
        ltp_path = os.path.join(workdir, "ltp.txt")
        netlist = os.path.join(workdir, "netlist.v")
        # two processes: stage 2 must not inherit stage 1's interned names
        run_yosys(yosys, render_canon(sources, top, params, rtlil), workdir, "canon", sources)
        run_yosys(yosys, render_script(rtlil, top, stat_path, ltp_path, netlist, script), workdir,
                  "synth")
        cells = parse_stat(stat_path, top)
        depth = parse_ltp(ltp_path)
        rtlil_sha = sha256_file(rtlil)
        if netlist_out:
            shutil.copyfile(netlist, netlist_out)
        if rtlil_out:
            shutil.copyfile(rtlil, rtlil_out)
    finally:
        shutil.rmtree(workdir, ignore_errors=True)
    gates, ignored, unpriced = {}, {}, {}
    for ctype, n in cells.items():
        m = re.fullmatch(r"\$_(\w+?)_", ctype)
        if ctype in IGNORED_CELLS:
            ignored[ctype] = n
        elif m and m.group(1) in ge:
            gates[m.group(1)] = n
        else:
            unpriced[ctype] = n
    if unpriced:
        raise ScoreError(f"the netlist has cells the GE table does not price: {unpriced} "
                         "(a combinational task's netlist should contain only the gates of "
                         "`abc -g`; latches and flip-flops are not scored)")
    area_mge = sum(ge[g] * n for g, n in gates.items())
    extra = {}
    if flow == "seq":
        ff_mge = sum(ge[g] * n for g, n in gates.items() if g in FLOP_TYPES)
        extra = {"ffs": sum(n for g, n in gates.items() if g in FLOP_TYPES),
                 "area_ff_mge": ff_mge, "area_comb_mge": area_mge - ff_mge}
    return {**extra,
        "top": top,
        "params": dict(params),
        "gates": dict(sorted(gates.items())),
        "ignored_cells": dict(sorted(ignored.items())),
        "num_gates": sum(gates.values()),
        "area_mge": area_mge,
        "area_ge": round(area_mge / 1000, 3),
        "depth": depth,
        "rtlil_sha256": rtlil_sha,
    }


def score(sources, top, params, yosys=None, repeat=1, gate=True, netlist_out=None,
          rtlil_out=None, flow="comb", reg_overhead=False):
    """Score `sources` (list of .sv paths) with top module `top` and parameter
    overrides `params` (dict name -> int). With `gate` (the default), Yosys
    reads the source gate's canonical text. With `netlist_out`, the scored
    gate netlist is written there (with `rtlil_out`, the canonical RTLIL).
    Raises ScoreError."""
    yosys = yosys_bin(yosys)
    gatedir = tempfile.mkdtemp(prefix="svgolf-gate-")
    try:
        if gate:
            read, canon_shas = gate_sources(sources, gatedir)
        else:
            read, canon_shas = list(sources), [None] * len(sources)
        results = [score_once(read, top, params, yosys, netlist_out if k == 0 else None,
                              rtlil_out if k == 0 else None, flow)
                   for k in range(max(1, repeat))]
    finally:
        shutil.rmtree(gatedir, ignore_errors=True)
    for r in results[1:]:
        if r != results[0]:
            raise ScoreError(f"non-deterministic synthesis: {results[0]} vs {r}")
    res = dict(results[0])
    res["yosys_version"] = yosys_version(yosys)
    script, table = FLOWS[flow]
    res["script_sha256"] = sha256_file(script)
    res["canon_script_sha256"] = sha256_file(CANON_SCRIPT)
    res["ge_table_sha256"] = sha256_file(table)
    if flow == "seq":
        # the per-cycle register overhead (clock-to-Q + setup in nand2 delays, ge_seq.json): reported always,
        # added to the period only with `reg_overhead` (not ruled)
        with open(table) as fh:
            ovh = json.load(fh)["_reg_overhead"]["nand2_delays"]
        res["flow"] = "seq"
        # the ABC that Yosys's `abc` pass runs (`yosys-abc` beside the Yosys binary): its version line and bytes
        abc = os.path.join(os.path.dirname(os.path.realpath(shutil.which(yosys) or yosys)), "yosys-abc")
        res["abc"] = {"version": subprocess.run([abc, "-q", "version"], capture_output=True, text=True,
                                                env=sandbox.scrubbed_env()).stdout.strip(),
                      "sha256": sha256_file(abc)} if os.path.isfile(abc) else None
        res["reg_overhead_nand2"] = ovh
        res["reg_overhead_included"] = bool(reg_overhead)
        res["period"] = res["depth"] + (math.ceil(ovh) if reg_overhead else 0)
    res["gated"] = bool(gate)
    res["sources"] = [{"path": s, "sha256": sha256_file(s), "canonical_sha256": c}
                      for s, c in zip(sources, canon_shas)]
    if repeat > 1:
        res["repeat_identical"] = repeat
    return res


def load_task(task_dir):
    with open(os.path.join(task_dir, "task.json")) as fh:
        return json.load(fh)


def task_scoring_point(task):
    return task["top"], {k: int(v) for k, v in task["scoring"]["params"].items()}


def pareto(records):
    """The (area_mge, depth) Pareto frontier of `records` (dicts with those
    keys): those no other record beats or ties on both axes while beating on
    one. Sorted by area."""
    front = []
    for r in records:
        dominated = any(
            (o["area_mge"] <= r["area_mge"] and o["depth"] <= r["depth"]) and
            (o["area_mge"] < r["area_mge"] or o["depth"] < r["depth"])
            for o in records)
        if not dominated:
            front.append(r)
    return sorted(front, key=lambda r: (r["area_mge"], r["depth"]))


def parse_params(items):
    params = {}
    for item in items or []:
        if "=" not in item:
            raise SystemExit(f"--param wants NAME=VALUE, got {item!r}")
        k, v = item.split("=", 1)
        params[k.strip()] = int(v)
    return params


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("sources", nargs="*")
    ap.add_argument("--top")
    ap.add_argument("--param", action="append")
    ap.add_argument("--task")
    ap.add_argument("--json")
    ap.add_argument("--netlist")
    ap.add_argument("--rtlil")
    ap.add_argument("--repeat", type=int, default=1)
    ap.add_argument("--yosys")
    ap.add_argument("--pareto", nargs="+", metavar="RESULT.json")
    ap.add_argument("--no-gate", action="store_true")
    ap.add_argument("--seq", action="store_true", help="the clocked flow (svgolf_seq.ys, ge_seq.json)")
    ap.add_argument("--reg-overhead", action="store_true",
                    help="with --seq: add the register overhead (ceil, nand2 delays) to the period")
    args = ap.parse_args(argv)
    if args.reg_overhead and not args.seq:
        ap.error("--reg-overhead needs --seq")

    if args.pareto:
        recs = []
        for p in args.pareto:
            with open(p) as fh:
                r = json.load(fh)
            r.setdefault("_file", p)
            recs.append(r)
        print(json.dumps(pareto(recs), indent=2, sort_keys=True))
        return 0
    if not args.sources:
        ap.error("no source files")
    if args.task:
        top, params = task_scoring_point(load_task(args.task))
        params.update(parse_params(args.param))
        if args.top and args.top != top:
            ap.error(f"--top {args.top} contradicts the task's top {top}")
    else:
        if not args.top:
            ap.error("--top (or --task) is required")
        top, params = args.top, parse_params(args.param)
    try:
        res = score(args.sources, top, params, args.yosys, args.repeat, gate=not args.no_gate,
                    netlist_out=args.netlist, rtlil_out=args.rtlil,
                    flow="seq" if args.seq else "comb", reg_overhead=args.reg_overhead)
    except ScoreError as e:
        print(json.dumps({"error": str(e)}, indent=2), file=sys.stdout)
        return 1
    text = json.dumps(res, indent=2, sort_keys=True)
    print(text)
    if args.json:
        with open(args.json, "w") as fh:
            fh.write(text + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
