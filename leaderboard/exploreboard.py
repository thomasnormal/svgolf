#!/usr/bin/env python3.12
"""svGolf exploration boards: the UNPROVED entries of the tasks that have no statement yet (kind `explore-stream`).

An exploration board is `leaderboard/explore/<task>.json`: the entries of one task, each a design file, its
declaration, and the composed score of a clean `check.py --unproved --declare` run. It is NOT a leaderboard: nothing
on it is proved, nothing on it is a record or par of a ranked board, and the site shows it apart from the proved
records, every number labelled `composed` and `unproved`. The entry named in the task's `par` line is the task's
reference point (the plain design), shown first.

    python3.12 leaderboard/exploreboard.py add --task gemm --name par --sv tasks/gemm/reference/par.sv \\
        --declare tasks/gemm/reference/par.json --result RESULT.json --title "..." --note "..." [--par]
    python3.12 leaderboard/exploreboard.py verify [--task gemm]      # the files are the ones the entries were checked on
    python3.12 leaderboard/exploreboard.py show --task gemm

`add` takes the result JSON of `python3.12 check.py tasks/<task> DESIGN.sv --unproved --declare DECLARE.json
--json RESULT.json` and refuses anything but a clean exploration run (stage `unproved`, `exploration`, a composed
score) of exactly these files. An entry with the same name is replaced.
"""
import argparse
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
BOARD_DIR = os.path.join(HERE, "explore")
KIND = "explore-stream"
VERSION = 1
SCORE_KEYS = ("label", "version", "area_um2", "area_e5um2", "period_ps", "cycles", "cycles_measured", "time_ps",
              "params", "job",
              "module_period_ps", "slowest_module", "flat_period_ps", "flat_period_at", "sram_area_um2", "sram_bits",
              "flops", "cells")


class BoardError(Exception):
    pass


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def task_names(tasks_dir=None):
    """The exploration tasks: every task directory whose task.json has the exploration kind."""
    tasks_dir = tasks_dir or os.path.join(SVGOLF, "tasks")
    out = []
    for t in sorted(os.listdir(tasks_dir)):
        path = os.path.join(tasks_dir, t, "task.json")
        if os.path.isfile(path):
            with open(path) as fh:
                if json.load(fh).get("kind") == KIND:
                    out.append(t)
    return out


def board_path(task, board_dir=None):
    return os.path.join(board_dir or BOARD_DIR, f"{task}.json")


def load(task, board_dir=None):
    """The board of `task` ({"task", "version", "entries"}); an empty one when there is no file."""
    path = board_path(task, board_dir)
    if not os.path.isfile(path):
        return {"task": task, "version": VERSION, "entries": []}
    with open(path) as fh:
        board = json.load(fh)
    if board.get("task") != task or board.get("version") != VERSION or not isinstance(board.get("entries"), list):
        raise BoardError(f"{path}: not an exploration board of {task} (version {VERSION})")
    return board


def score_value(entry):
    """The composed score of an entry, exactly: area (1e-5 um^2) x cycles x period (ps). Lower is better."""
    s = entry["score"]
    return s["area_e5um2"] * s["cycles"] * s["period_ps"]


def mm2ms(entry):
    """The composed score in mm^2 * ms per job (for display)."""
    return score_value(entry) / 1e5 / 1e6 / 1e9


def ordered(board):
    """The entries by score, best first (ties by name)."""
    return sorted(board["entries"], key=lambda e: (score_value(e), e["name"]))


def par_entry(board):
    return next((e for e in board["entries"] if e.get("par")), None)


def entry_from_result(task, name, sv, declare, result, title, note, par=False, root=None):
    """The board entry of a clean exploration run `result` (check.py's JSON) on the files `sv` and `declare`
    (paths relative to the svGolf root `root`). Raises BoardError when the run is not one."""
    root = root or SVGOLF
    if result.get("task") != task:
        raise BoardError(f"the result is of task {result.get('task')!r}, not {task}")
    if not (result.get("exploration") and result.get("unproved_ok") and result.get("stage") == "unproved"):
        raise BoardError("the result is not a clean exploration run (stage `unproved` of check.py --unproved "
                         f"--declare): stage {result.get('stage')!r}, errors {result.get('errors')}")
    sc = result.get("score") or {}
    if sc.get("label") != "composed":
        raise BoardError("the result has no composed score (it was run with --no-score)")
    st = result.get("stages") or {}
    if sha256_file(os.path.join(root, sv)) != (st.get("source") or {}).get("sha256"):
        raise BoardError(f"{sv} is not the design the result was made on")
    if sha256_file(os.path.join(root, declare)) != (st.get("declare") or {}).get("sha256"):
        raise BoardError(f"{declare} is not the declaration the result was made on")
    netlist = [p for p in (st.get("explore") or {}).get("points") or [] if "seeds" in (p.get("netlist") or {})]
    if sc.get("cycles_measured") != sc.get("cycles"):
        raise BoardError("the result's cycles are not a measured count of the scored job (a run of an older check)")
    return {
        "name": name, "title": title, "note": note, "par": bool(par), "proved": False,
        "sv": sv, "declare": declare,
        "sv_sha256": st["source"]["sha256"], "declare_sha256": st["declare"]["sha256"],
        "layout": st["declare"]["layout"], "cycles_formula": st["declare"]["cycles"],
        "score": {k: sc[k] for k in SCORE_KEYS if k in sc},
        "checked": {"points": [p["params"] for p in st["explore"]["points"]],
                    "netlist_points": [p["params"] for p in netlist],
                    "hier_rule": (st.get("hier") or {}).get("rule"),
                    "flow": {k: (st.get("hier") or {}).get("flow", {}).get(k)
                             for k in ("yosys_version", "rating_build", "canon_script_sha256", "script_sha256")},
                    "hier_script_sha256": (st.get("hier") or {}).get("hier_script_sha256"),
                    "ppa_version": (st.get("hier") or {}).get("ppa_version")},
    }


def add(task, entry, board_dir=None):
    board = load(task, board_dir)
    if entry.get("par"):
        for e in board["entries"]:
            if e["name"] != entry["name"] and e.get("par"):
                raise BoardError(f"{e['name']} is already this board's par")
    board["entries"] = [e for e in board["entries"] if e["name"] != entry["name"]] + [entry]
    board["entries"].sort(key=lambda e: e["name"])
    os.makedirs(board_dir or BOARD_DIR, exist_ok=True)
    with open(board_path(task, board_dir), "w") as fh:
        fh.write(json.dumps(board, indent=1, sort_keys=True) + "\n")
    return board


def problems(task, board_dir=None, root=None):
    """What is wrong with a board, in words: an entry whose files are missing or changed, a board without its par,
    a name twice, an entry that claims a proof, an entry whose cycle count was not measured on the scored job."""
    root = root or SVGOLF
    try:
        board = load(task, board_dir)
    except (BoardError, ValueError) as e:
        return [str(e)]
    bad, seen = [], set()
    for e in board["entries"]:
        if e["name"] in seen:
            bad.append(f"{task}: entry {e['name']} twice")
        seen.add(e["name"])
        if e.get("proved") is not False or (e.get("score") or {}).get("label") != "composed":
            bad.append(f"{task}: entry {e['name']} must be unproved with a composed score")
        if (e.get("score") or {}).get("cycles_measured") != (e.get("score") or {}).get("cycles"):
            bad.append(f"{task}: entry {e['name']}: its cycles are not the measured count of the scored job (check it "
                       "again and `add` the new result)")
        for key in ("sv", "declare"):
            path = os.path.join(root, e[key])
            if not os.path.isfile(path):
                bad.append(f"{task}: entry {e['name']}: no file {e[key]}")
            elif sha256_file(path) != e[f"{key}_sha256"]:
                bad.append(f"{task}: entry {e['name']}: {e[key]} is not the file the entry was checked on "
                           "(check it again and `add` the new result)")
    if board["entries"] and len([e for e in board["entries"] if e.get("par")]) != 1:
        bad.append(f"{task}: the board needs exactly one par entry")
    return bad


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("add")
    a.add_argument("--task", required=True)
    a.add_argument("--name", required=True)
    a.add_argument("--sv", required=True)
    a.add_argument("--declare", required=True)
    a.add_argument("--result", required=True)
    a.add_argument("--title", required=True)
    a.add_argument("--note", default="")
    a.add_argument("--par", action="store_true")
    v = sub.add_parser("verify")
    v.add_argument("--task")
    s = sub.add_parser("show")
    s.add_argument("--task", required=True)
    args = ap.parse_args(argv)
    try:
        if args.cmd == "add":
            with open(args.result) as fh:
                result = json.load(fh)
            rel = [os.path.relpath(os.path.abspath(p), SVGOLF) for p in (args.sv, args.declare)]
            entry = entry_from_result(args.task, args.name, rel[0], rel[1], result, args.title, args.note, args.par)
            add(args.task, entry)
            print(f"[ok] {args.task}: {args.name}: {mm2ms(entry):.3f} mm2*ms per job (composed, unproved)")
            return 0
        if args.cmd == "verify":
            names = [args.task] if args.task else task_names()
            bad = [b for t in names for b in problems(t)]
            for b in bad:
                print(f"[FAIL] {b}")
            if not bad:
                print(f"[ok] exploration boards: {', '.join(f'{t} ({len(load(t)['entries'])} entries)' for t in names) or 'none'}")
            return 1 if bad else 0
        board = load(args.task)
        par = par_entry(board)
        for e in ordered(board):
            rel = f"  {score_value(e) / score_value(par):.3f} x par" if par else ""
            print(f"{e['name']:10s} {e['score']['area_um2'] / 1e6:8.4f} mm2  {e['score']['cycles']:>9d} cycles  "
                  f"{e['score']['period_ps']:5d} ps  {mm2ms(e):8.3f} mm2*ms{rel}{'  (par)' if e.get('par') else ''}")
        return 0
    except (BoardError, OSError, ValueError) as e:
        print(f"[FAIL] {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
