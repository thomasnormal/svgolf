#!/usr/bin/env python3
"""The proof time limit of every task, and the measurements that test it (README.md, "Proof effort").

    python3 score/time_limits.py                       # print the table
    python3 score/time_limits.py --check               # exit 1 if a task breaks the rule
    python3 score/time_limits.py --write               # set `time_limit_s` in task.json
    python3 score/time_limits.py --selftest
    python3 score/time_limits.py --measurements FILE   # default: score/time_limits.json

THE RULE (decided 2026-11-02, the value 2026-11-06; it replaced the 10/30 rule `max(120, ceil(4 x T))`):

    time_limit_s = 300, the same for every task

300 CPU seconds: the limit was 120 wall-clock seconds, and CPU seconds count every elaboration thread
(Lean elaborates in parallel: the references use up to 3.5 CPU seconds per wall-clock second, measured
2026-11-06).

All proofs should be checkable quickly, so the limit is a ceiling and does not follow how slow a
reference happens to be. The limit counts the CPU seconds of the Lean process (decided 2026-11-05;
`check.py`'s `stages.solution.cpu_seconds`, with a wall-clock backstop of 5 times it). T is the
MAXIMUM of the controlled COLD runs of the SLOWEST honest reference of the task, in CPU SECONDS:
`check.py`'s `stages.solution.cpu_seconds` (the compile of the reference's `Solution.lean` under the
limit, nothing else), the quantity the limit counts. The wall clock of each run (`stages.solution.seconds`)
is recorded beside it and only informs. A reference over the limit is a defect of that proof or of our
scaffolding: `--check` fails, and the fix is the proof or the scaffold, never a larger limit. The
target is T <= 150 CPU s, a 2x margin for a slower machine; `--check` compares every reference's
largest run with it and names each one above it, which is flagged and does not fail.

`--check` also fails when a measurement is not in CPU seconds (the file's `unit` must be `cpu_s`
and every reference's runs `{"cpu_s": [...], "wall_s": [...]}`: a wall-clock run says nothing about
the CPU limit; the runs recorded before 2026-11-06 were wall clock), and when a reference that a
task.json lists has no measurement (T is the slowest reference's: an unmeasured one could be it).

The measurements file (`score/time_limits.json`) records WHAT was controlled: the machine class,
whether the build was cold or warm, the Lean cache state, the thread budget, the reference commit.
When the proof tactics, the toolchain or the machine change: measure again and put the new runs in
the file. `tests/run.py` (step `layout`) runs `--check`.

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
LIMIT_S = 300
TARGET_S = 150
UNIT = "cpu_s"      # the measurements file's unit: CPU seconds, what the limit counts


def cpu_runs(v):
    """The CPU-second runs of one reference's entry `v` (`{"cpu_s": [...], "wall_s": [...]}`), or None when the
    entry has none (a bare list is the old file's wall-clock runs)."""
    if isinstance(v, dict) and isinstance(v.get("cpu_s"), list) and v["cpu_s"] and all(
            isinstance(x, (int, float)) for x in v["cpu_s"]):
        return v["cpu_s"]
    return None


def wall_runs(v):
    """The wall-clock seconds of the same runs (informative), or []."""
    return list(v.get("wall_s") or []) if isinstance(v, dict) else list(v or [])


def slowest(refs):
    """(reference stem, T) of `refs` = {stem: {"cpu_s": [CPU seconds of each cold run], ...}}: the reference
    with the largest maximum run, and that maximum. Entries without CPU runs are skipped (`unmeasured`)."""
    got = {k: cpu_runs(v) for k, v in refs.items()}
    got = {k: v for k, v in got.items() if v}
    if not got:
        return None, None
    best = max(got.items(), key=lambda kv: (max(kv[1]), kv[0]))
    return best[0], max(best[1])


def unmeasured(refs):
    """The references of `refs` whose entry carries no CPU-second runs, sorted."""
    return sorted(k for k, v in refs.items() if not cpu_runs(v))


def table(measurements):
    """One row per task of the measurements file: task, slowest reference, T (CPU s), the limit, the runs
    of every reference. A task with no measurement has no T and the same limit."""
    rows = []
    for task, entry in sorted(measurements["tasks"].items()):
        refs = entry.get("references")
        if not refs:
            rows.append({"task": task, "reference": None, "T": None, "limit": LIMIT_S, "runs": {},
                         "unmeasured": [], "why": entry.get("why", "no measurement")})
            continue
        stem, t = slowest(refs)
        rows.append({"task": task, "reference": stem, "T": t, "limit": LIMIT_S, "runs": refs,
                     "unmeasured": unmeasured(refs), "why": entry.get("why", "")})
    return rows


def over_target(rows):
    """(task, reference, largest CPU run) of every measured reference above TARGET_S, in task order."""
    out = []
    for r in rows:
        for stem, v in sorted(r["runs"].items()):
            c = cpu_runs(v)
            if c and max(c) > TARGET_S:
                out.append((r["task"], stem, max(c)))
    return out


def listed_references(task):
    """The reference stems a task's task.json lists (`references[].sv`), or [] when there is no task.json."""
    path = task_json_path(task)
    if not os.path.isfile(path):
        return []
    with open(path) as fh:
        tj = json.load(fh)
    return [os.path.splitext(os.path.basename(r["sv"]))[0] for r in tj.get("references") or []]


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
    """How a row stands against the limit and the target (CPU seconds)."""
    if r["T"] is None:
        return ""
    if r["T"] > LIMIT_S:
        return "OVER THE LIMIT: fix the proof or the scaffold"
    return f"over the {TARGET_S} CPU s target" if r["T"] > TARGET_S else ""


def tasks_on_disk():
    """The task directories under tasks/ that have a task.json."""
    root = os.path.join(SVGOLF, "tasks")
    return sorted(d for d in os.listdir(root) if os.path.isfile(os.path.join(root, d, "task.json")))


def unit_problems(m, rows, listed=listed_references, tasks=tasks_on_disk):
    """Why the measurements cannot be compared with the CPU limit: the file's unit is not CPU seconds, a reference's
    runs are not CPU seconds, or a reference a task.json lists has no measurement (`listed`: task -> stems; `tasks`:
    the tasks on disk, each of which with a listed reference needs an entry)."""
    p = []
    if m.get("unit") != UNIT:
        p.append(f"the measurements file's unit is {m.get('unit')!r}, not {UNIT!r}: the limit counts CPU seconds, "
                 "so wall-clock runs cannot be compared with it (re-measure: README.md, \"Proof effort\")")
    for task in tasks():
        if task not in m.get("tasks", {}) and listed(task):
            p.append(f"{task}: no entry, but task.json lists the references {listed(task)}")
    for r in rows:
        for stem in r["unmeasured"]:
            p.append(f"{r['task']}: {stem} has no CPU-second runs (`cpu_s`)")
        for stem in listed(r["task"]):
            if stem not in r["runs"]:
                p.append(f"{r['task']}: the reference {stem} (task.json) has no measurement")
    return p


def render(rows, m):
    env = m.get("environment", {})
    out = [f"time_limit_s = {LIMIT_S} CPU s for every task; target T <= {TARGET_S} CPU s; "
           "T = the largest cold run of the slowest reference, in CPU seconds (the wall clock of each run beside it)",
           f"{'task':<10} {'slowest reference':<20} {'T (CPU s)':>9} {'limit':>6} {'task.json':>9}"]
    for r in rows:
        cur = current_limit(r["task"])
        t = "" if r["T"] is None else f"{r['T']:.1f}"
        note = "   <-- differs" if cur != r["limit"] else ""
        out.append(f"{r['task']:<10} {r['reference'] or '(none)':<20} {t:>9} {r['limit']:>6} "
                   f"{cur if cur is not None else '-':>9}{note}   {flag(r)}".rstrip())
    for r in rows:
        if r["runs"]:
            out.append(f"  {r['task']}: " + "; ".join(
                f"{k} " + (", ".join(f"{x:g}" for x in cpu_runs(v)) + " CPU s (wall "
                           + ", ".join(f"{x:g}" for x in wall_runs(v)) + " s)" if cpu_runs(v) else
                           "NOT IN CPU SECONDS: " + ", ".join(f"{x:g}" for x in wall_runs(v)) + " s")
                for k, v in sorted(r["runs"].items())))
    for task, stem, c in over_target(rows):
        out.append(f"  over the {TARGET_S} CPU s target (flagged, not a failure): {task}/{stem} {c:g} CPU s")
    for k in ("machine", "build", "lean_cache", "threads", "postsynth_mode", "reference_commit", "date",
              "load"):
        if k in env:
            out.append(f"  {k}: {env[k]}")
    return "\n".join(out)


def selftest():
    c = lambda *xs: {"cpu_s": list(xs), "wall_s": [x / 2 for x in xs]}
    assert slowest({"a": c(1, 9), "b": c(8, 8, 8)}) == ("a", 9)
    assert slowest({"a": c(5), "b": c(5)}) == ("b", 5)       # a tie: the later name, deterministic
    # T reads the CPU runs, never the wall clock beside them
    assert slowest({"a": {"cpu_s": [10.0], "wall_s": [50.0]}, "b": {"cpu_s": [20.0], "wall_s": [9.0]}}) == ("b", 20.0)
    # an old wall-clock entry (a bare list) is not a CPU measurement
    assert cpu_runs([12.0]) is None and unmeasured({"a": [12.0], "b": c(3)}) == ["a"]
    rows = table({"tasks": {"t": {"references": {"x": c(10.0, 12.5, 11.0), "y": c(3.0)}},
                            "d": {"references": None, "why": "a draft"}}})
    assert [(r["task"], r["reference"], r["T"], r["limit"]) for r in rows] == \
        [("d", None, None, LIMIT_S), ("t", "x", 12.5, LIMIT_S)]
    assert flag({"T": None}) == "" and flag({"T": float(TARGET_S)}) == ""
    assert "target" in flag({"T": TARGET_S + 0.1}) and "OVER" not in flag({"T": float(LIMIT_S)})
    assert "OVER" in flag({"T": LIMIT_S + 0.1})
    # every reference over the target is named, not only the slowest of its task
    rows = table({"tasks": {"t": {"references": {"x": c(170.0), "y": c(151.0), "z": c(149.9)}}}})
    assert over_target(rows) == [("t", "x", 170.0), ("t", "y", 151.0)]
    # the unit and the coverage problems
    m = {"unit": UNIT, "tasks": {"t": {"references": {"x": c(1.0), "w": [2.0]}}}}
    probs = unit_problems(m, table(m), listed=lambda t: ["x", "w", "v"], tasks=lambda: ["t"])
    assert probs == ["t: w has no CPU-second runs (`cpu_s`)", "t: the reference v (task.json) has no measurement"], probs
    m2 = dict(m, unit="wall_s")
    assert unit_problems(m2, table(m2), listed=lambda t: [], tasks=lambda: [])[0].startswith(
        "the measurements file's unit is 'wall_s'")
    # a task on disk with references but no entry at all; one without references (a draft) needs none
    assert unit_problems(m, table(m), listed=lambda t: {"t": ["x", "w"], "u": ["y"]}.get(t, []),
                         tasks=lambda: ["d", "t", "u"]) == ["u: no entry, but task.json lists the references ['y']",
                                                            "t: w has no CPU-second runs (`cpu_s`)"]
    print("time_limits.py: selftest ok")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--measurements", default=DEFAULT_MEASUREMENTS)
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if a task.json disagrees, a T is over the limit, or a measurement is not in CPU seconds")
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
    units = unit_problems(m, rows)
    if args.write:
        for r in bad:
            write_limit(r["task"], r["limit"])
            print(f"wrote {r['task']}: time_limit_s {r['limit']}")
        return 0
    if args.check:
        hot = over_target(rows)
        if hot:
            print(f"time_limits.py: over the {TARGET_S} CPU s target (flagged, not a failure): "
                  + ", ".join(f"{t}/{s} {c:g} CPU s" for t, s, c in hot))
        if bad or over or units:
            msgs = [f"{r['task']} has {current_limit(r['task'])}, the rule gives {r['limit']}" for r in bad]
            msgs += [f"{r['task']}: {r['reference']} needs {r['T']:g} CPU s, over the {LIMIT_S} s limit"
                     for r in over]
            msgs += units
            print("time_limits.py: " + ", ".join(msgs), file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
