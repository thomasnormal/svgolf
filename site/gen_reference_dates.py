"""The date each proved reference joined its task, for the site's score charts.

A reference's date is the author date (UTC) of the first commit that listed it in its task's
`task.json` `references`, read from git history. `site/content/reference_dates.json` keeps them,
because a fresh-history copy of the repository (the public export) has no such history: every
reference there would share the export's one commit date.

    python3.12 site/gen_reference_dates.py           # add the missing references' dates
    python3.12 site/gen_reference_dates.py --check   # exit 1 if a reference has no date

Dates already in the file are kept as they are; a reference that left its task is dropped.
Run from svgolf/ or anywhere (paths are resolved from this file).
"""
import argparse
import datetime
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
OUT = os.path.join(HERE, "content", "reference_dates.json")
COMMENT = ("When each proved reference joined its task (UTC): the author date of the first commit that listed it in "
           "the task's task.json. The score chart plots references at these times. Written by "
           "site/gen_reference_dates.py, which keeps existing entries; add a new reference's date with it.")


def references():
    """{task: [stem, ...]} from every tasks/<t>/task.json, in the task's order."""
    out = {}
    tasks = os.path.join(SVGOLF, "tasks")
    for t in sorted(os.listdir(tasks)):
        path = os.path.join(tasks, t, "task.json")
        if os.path.isfile(path):
            with open(path, encoding="utf-8") as fh:
                refs = json.load(fh).get("references", [])
            out[t] = [os.path.splitext(os.path.basename(r["sv"]))[0] for r in refs]
    return out


def first_listed(task, stem):
    """The UTC author date (YYYY-MM-DDTHH:MM:SSZ) of the oldest commit whose diff adds or removes
    the string `reference/<stem>.sv"` in tasks/<task>/task.json, or None without such history."""
    path = os.path.join("tasks", task, "task.json")
    try:
        out = subprocess.run(["git", "-C", SVGOLF, "log", "--format=%at", f'-Sreference/{stem}.sv"', "--", path],
                             capture_output=True, text=True, timeout=120, env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))
    except (OSError, subprocess.SubprocessError):
        return None
    stamps = out.stdout.split() if out.returncode == 0 else []
    if not stamps:
        return None
    when = datetime.datetime.fromtimestamp(int(stamps[-1]), tz=datetime.timezone.utc)
    return when.strftime("%Y-%m-%dT%H:%M:%SZ")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--check", action="store_true", help="only report references without a date")
    args = ap.parse_args(argv)
    try:
        with open(OUT, encoding="utf-8") as fh:
            old = json.load(fh)
    except FileNotFoundError:
        old = {}
    refs = references()
    missing = [(t, s) for t, stems in refs.items() for s in stems if s not in old.get(t, {})]
    if args.check:
        for t, s in missing:
            print(f"{t}/{s}: no date in {os.path.relpath(OUT, SVGOLF)} (run site/gen_reference_dates.py)")
        return 1 if missing else 0
    new = {"_comment": COMMENT}
    for t, stems in refs.items():
        dates = {s: old.get(t, {}).get(s) or first_listed(t, s) for s in stems}
        unknown = [s for s, d in dates.items() if d is None]
        if unknown:
            print(f"{t}: no git history lists {unknown} in task.json; add their dates by hand", file=sys.stderr)
        dates = {s: d for s, d in dates.items() if d is not None}
        if dates:
            new[t] = dates
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(new, indent=1, ensure_ascii=False) + "\n")
    print(f"wrote {os.path.relpath(OUT, SVGOLF)}: {sum(len(v) for k, v in new.items() if k != '_comment')} references")
    return 0


if __name__ == "__main__":
    sys.exit(main())
