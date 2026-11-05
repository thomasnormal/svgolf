#!/usr/bin/env python3
"""The proof time limit of every task, and the measurements that test it (README.md, "Proof effort").

    python3 score/time_limits.py                       # print the table
    python3 score/time_limits.py --check               # exit 1 if a task breaks the rule
    python3 score/time_limits.py --write               # set `time_limit_s` in task.json
    python3 score/time_limits.py --selftest
    python3 score/time_limits.py --measurements FILE   # default: score/time_limits.json

THE RULE (decided 2026-11-02, replacing the 10/30 rule `max(120, ceil(4 x T))`):

    time_limit_s = 120, the same for every task

All proofs should be checkable quickly, so the limit is a ceiling and does not follow how slow a
reference happens to be. T is the MAXIMUM of the controlled COLD runs of the SLOWEST honest
reference of the task: `check.py`'s `stages.solution.seconds` (the compile of the reference's
`Solution.lean` under the limit, nothing else). A reference over the limit is a defect of that
proof or of our scaffolding: `--check` fails, and the fix is the proof or the scaffold, never a
larger limit. The target is T <= 60 s, a 2x margin for a slower or busier machine; a reference
above it is flagged and does not fail.

The measurements file (`score/time_limits.json`) records WHAT was controlled: machine class,
whether the build was cold or warm, the Lean cache state, the post-synthesis mode and the
reference commit. When the proof tactics, the toolchain or the machine change: measure again and
put the new runs in the file. `tests/run.py` (step `layout`) runs `--check`.

This file is not part of what the checker hashes (`check.py`'s integrity snapshot and a
leaderboard record's `checker.files`): changing a limit is a task.json edit.
"""

import argparse
import json
import math
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
DEFAULT_MEASUREMENTS = os.path.join(HERE, "time_limits.json")
LIMIT_S = 120
TARGET_S = 60


def slowest(refs):
    """(reference stem, T) of `refs` = {stem: [seconds of each cold run]}: the reference
    with the largest maximum run, and that maximum."""
    best = max(refs.items(), key=lambda kv: (max(kv[1]), kv[0]))
    return best[0], max(best[1])


def table(measurements):
    """One row per task of the measurements file: task, slowest reference, T, the limit, the runs
    of every reference. A task with no measurement has no T and the same limit."""
    rows = []
    for task, entry in sorted(measurements["tasks"].items()):
        refs = entry.get("references")
        if not refs:
            rows.append({"task": task, "reference": None, "T": None, "limit": LIMIT_S, "runs": {},
                         "why": entry.get("why", "no measurement")})
            continue
        stem, t = slowest(refs)
        rows.append({"task": task, "reference": stem, "T": t, "limit": LIMIT_S, "runs": refs,
                     "why": entry.get("why", "")})
    return rows


def task_json_path(task):
    return os.path.join(SVGOLF, "tasks", task, "task.json")


def current_limit(task):
    with open(task_json_path(task)) as fh:
        return json.load(fh).get("time_limit_s")


def write_limit(task, limit):
    """Set `time_limit_s` in the task's task.json, touching nothing else of its text."""
    path = task_json_path(task)
    with open(path) as fh:
        text = fh.read()
    new, n = re.subn(r'("time_limit_s"\s*:\s*)\d+', rf"\g<1>{limit}", text, count=1)
    if n != 1:
        raise SystemExit(f"{path}: no top-level \"time_limit_s\" to rewrite")
    # the first match must be the task's own, not the nested postsynth one
    json.loads(new)
    if json.loads(new).get("time_limit_s") != limit:
        raise SystemExit(f"{path}: rewrote a nested time_limit_s; edit it by hand")
    with open(path, "w") as fh:
        fh.write(new)


def flag(r):
    """How a row stands against the limit and the target."""
    if r["T"] is None:
        return ""
    if r["T"] > LIMIT_S:
        return "OVER THE LIMIT: fix the proof or the scaffold"
    return f"over the {TARGET_S} s target" if r["T"] > TARGET_S else ""


def render(rows, m):
    env = m.get("environment", {})
    out = [f"time_limit_s = {LIMIT_S} for every task; target T <= {TARGET_S} s; "
           "T = the largest cold run of the slowest reference",
           f"{'task':<10} {'slowest reference':<20} {'T (s)':>7} {'limit':>6} {'task.json':>9}"]
    for r in rows:
        cur = current_limit(r["task"])
        t = "" if r["T"] is None else f"{r['T']:.1f}"
        note = "   <-- differs" if cur != r["limit"] else ""
        out.append(f"{r['task']:<10} {r['reference'] or '(none)':<20} {t:>7} {r['limit']:>6} "
                   f"{cur if cur is not None else '-':>9}{note}   {flag(r)}".rstrip())
    for r in rows:
        if r["runs"]:
            out.append(f"  {r['task']}: " + "; ".join(
                f"{k} {', '.join(f'{x:g}' for x in v)}" for k, v in sorted(r["runs"].items())))
    for k in ("machine", "build", "lean_cache", "postsynth_mode", "reference_commit", "date",
              "load"):
        if k in env:
            out.append(f"  {k}: {env[k]}")
    return "\n".join(out)


def selftest():
    assert slowest({"a": [1, 9], "b": [8, 8, 8]}) == ("a", 9)
    assert slowest({"a": [5], "b": [5]}) == ("b", 5)       # a tie: the later name, deterministic
    rows = table({"tasks": {"t": {"references": {"x": [10.0, 12.5, 11.0], "y": [3.0]}},
                            "d": {"references": None, "why": "a draft"}}})
    assert [(r["task"], r["reference"], r["T"], r["limit"]) for r in rows] == \
        [("d", None, None, LIMIT_S), ("t", "x", 12.5, LIMIT_S)]
    assert flag({"T": None}) == "" and flag({"T": 60.0}) == ""
    assert "target" in flag({"T": 60.1}) and "OVER" not in flag({"T": 120.0})
    assert "OVER" in flag({"T": 120.1})
    print("time_limits.py: selftest ok")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--measurements", default=DEFAULT_MEASUREMENTS)
    ap.add_argument("--check", action="store_true", help="exit 1 if a task.json disagrees")
    ap.add_argument("--write", action="store_true", help="set time_limit_s in each task.json")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        selftest()
        return 0
    with open(args.measurements) as fh:
        m = json.load(fh)
    rows = table(m)
    print(render(rows, m))
    bad = [r for r in rows if current_limit(r["task"]) != r["limit"]]
    over = [r for r in rows if r["T"] is not None and r["T"] > LIMIT_S]
    if args.write:
        for r in bad:
            write_limit(r["task"], r["limit"])
            print(f"wrote {r['task']}: time_limit_s {r['limit']}")
        return 0
    if args.check and (bad or over):
        msgs = [f"{r['task']} has {current_limit(r['task'])}, the rule gives {r['limit']}" for r in bad]
        msgs += [f"{r['task']}: {r['reference']} needs {r['T']:g} s, over the {LIMIT_S} s limit" for r in over]
        print("time_limits.py: " + ", ".join(msgs), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
