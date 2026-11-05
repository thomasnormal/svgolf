#!/usr/bin/env python3
"""svGolf's nightly regression: one command, one report, a diff against the last run.

    python3.12 nightly.py                  # the whole suite (tests/run.py) + the repo checks
    python3.12 nightly.py --only add,mul   # passthrough to tests/run.py (also --skip, --full)
    python3.12 nightly.py --no-repo-checks # only tests/run.py

What it does, in order:
  1. `tests/run.py [passthrough]` (every Lean invocation goes through $SVGOLF_LEAN_WRAP when set,
     see tests/run.py: the single-slot queue of a shared machine);
  2. the repository checks that keep the docs and the refusal register honest and are cheap:
     inside lean-surfaces (check/layout.py) its `tools/gen_sv_refusals.py --check` and
     `tools/docs_check.py`; standalone, REFUSALS.md compared byte for byte (`cmp`) with what the
     lean-surfaces dependency's `tools/gen_sv_refusals.py --emit-svgolf` writes from its register;
     in both, `score/time_limits.py --check`;
  3. a report: `nightly/<stamp>/{run.log, checks.json, report.md}`, and a comparison with the newest
     earlier run in `nightly/`:
       REGRESSION  a check that was ok and now FAILS (or vanished);
       FIXED       a check that failed and is now ok;
       NEW         a check the earlier run did not have;
       SLOWER      an ok check that took more than 1.5 x its earlier time and more than 30 s more.
Exit status: 0 when nothing failed and nothing regressed, 1 otherwise, 2 for a harness error.

Checks are keyed by `step: name` (the first two fields of run.py's `[ok] step: name: detail [Ns]` lines:
the detail carries temporary directory names and is never compared). `nightly/` is not committed.

Scheduling (cron or launchd are the operator's business): run it from svgolf/ with the same environment
a developer uses, e.g. `0 3 * * * cd /path/to/repo/svgolf && SVGOLF_LEAN_WRAP=... python3.12 nightly.py`.
This script edits nothing under svgolf/ except `nightly/`.
"""
import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "check"))
import layout  # noqa: E402  (check/layout.py: where lean-surfaces is, in either layout)

REPO = layout.LS_ROOT             # lean-surfaces: the parent inside it, the dependency standalone
LINE = re.compile(r"^\[(ok|FAIL)\] ([^:]+): (.*?)(?: \[(\d+)s\])?$")
SLOWER_FACTOR, SLOWER_MIN = 1.5, 30


def parse_log(text):
    """{ "step: name": {"ok": bool, "seconds": int | None} } from run.py's output."""
    out = {}
    for ln in text.splitlines():
        m = LINE.match(ln)
        if not m:
            continue
        status, step, rest, secs = m.groups()
        name = rest.split(": ", 1)[0]
        key = f"{step}: {name}"
        ok = status == "ok"
        # a repeated key (a check that records twice) fails if any of them failed
        prev = out.get(key)
        out[key] = {"ok": ok and (prev["ok"] if prev else True),
                    "seconds": int(secs) if secs else (prev["seconds"] if prev else None)}
    return out


def summary_table(text):
    """The `== summary ==` block of run.py, verbatim, or ''."""
    i = text.rfind("== summary")
    return text[i:].strip() if i >= 0 else ""


def newest_earlier(outdir, stamp):
    if not os.path.isdir(outdir):
        return None
    runs = sorted(d for d in os.listdir(outdir)
                  if d < stamp and os.path.isfile(os.path.join(outdir, d, "checks.json")))
    return os.path.join(outdir, runs[-1]) if runs else None


def compare(old, new):
    reg = sorted(k for k, v in old.items() if v["ok"] and (k not in new or not new[k]["ok"]))
    fixed = sorted(k for k, v in old.items() if not v["ok"] and k in new and new[k]["ok"])
    added = sorted(k for k in new if k not in old)
    slower = []
    for k, v in new.items():
        o = old.get(k)
        if o and v["ok"] and o["ok"] and v["seconds"] and o["seconds"]:
            if v["seconds"] > SLOWER_FACTOR * o["seconds"] and v["seconds"] - o["seconds"] > SLOWER_MIN:
                slower.append(f"{k}: {o['seconds']} s -> {v['seconds']} s")
    return reg, fixed, added, sorted(slower)


def run_logged(cmd, cwd, logpath, env=None):
    with open(logpath, "w") as fh:
        p = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, env=env)
    return p.returncode


def main(argv):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--out", default=os.path.join(HERE, "nightly"), help="report directory (default: nightly/)")
    ap.add_argument("--only", help="passed to tests/run.py")
    ap.add_argument("--skip", help="passed to tests/run.py")
    ap.add_argument("--full", action="store_true", help="passed to tests/run.py (hours)")
    ap.add_argument("--no-repo-checks", action="store_true", help="skip gen_sv_refusals/docs_check/time_limits")
    ap.add_argument("--stamp", help="run id (default: UTC time); runs compare against the newest smaller id")
    args = ap.parse_args(argv)

    stamp = args.stamp or datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    rundir = os.path.join(args.out, stamp)
    os.makedirs(rundir, exist_ok=True)
    py = sys.executable

    cmd = [py, os.path.join("tests", "run.py")]
    for flag, val in (("--only", args.only), ("--skip", args.skip)):
        if val:
            cmd += [flag, val]
    if args.full:
        cmd.append("--full")
    rc = run_logged(cmd, HERE, os.path.join(rundir, "run.log"))
    text = open(os.path.join(rundir, "run.log")).read()
    checks = parse_log(text)

    repo = []
    if not args.no_repo_checks:
        gen = [py, os.path.join(REPO, "tools", "gen_sv_refusals.py")]
        if layout.LAYOUT == "inside":
            repo_checks = [("sv-refusals register", gen + ["--check"], REPO),
                           ("docs_check", [py, os.path.join("tools", "docs_check.py")], REPO)]
        else:
            # the dependency's register is checked in its own repository; here, only that
            # REFUSALS.md is what it renders
            emitted = os.path.join(tempfile.mkdtemp(prefix="svgolf-refusals-"), "REFUSALS.md")
            repo_checks = [("sv-refusals register", gen + ["--root", REPO, "--emit-svgolf", emitted], HERE),
                           ("REFUSALS.md", ["cmp", emitted, os.path.join(HERE, "REFUSALS.md")], HERE)]
        for label, c, cwd in repo_checks + [
                ("time limits", [py, os.path.join("score", "time_limits.py"), "--check"], HERE)]:
            r = run_logged(c, cwd, os.path.join(rundir, label.replace(" ", "_") + ".log"))
            repo.append((label, r == 0))
            checks[f"repo: {label}"] = {"ok": r == 0, "seconds": None}

    with open(os.path.join(rundir, "checks.json"), "w") as fh:
        json.dump({"stamp": stamp, "run_py_exit": rc, "args": vars(args), "checks": checks}, fh,
                  indent=1, sort_keys=True)

    prev_dir = newest_earlier(args.out, stamp)
    reg = fixed = added = slower = []
    if prev_dir:
        prev = json.load(open(os.path.join(prev_dir, "checks.json")))["checks"]
        reg, fixed, added, slower = compare(prev, checks)
    failed = sorted(k for k, v in checks.items() if not v["ok"])

    lines = [f"# svGolf nightly {stamp}", "",
             f"tests/run.py exit {rc}; {len(checks)} checks, {len(failed)} failed; compared with "
             f"{os.path.basename(prev_dir) if prev_dir else 'nothing (first run)'}", ""]
    st = summary_table(text)
    if st:
        lines += ["```", st, "```", ""]
    for title, items in (("FAILED", failed), ("REGRESSION", reg), ("FIXED", fixed), ("NEW", added),
                         ("SLOWER", slower)):
        if items:
            lines += [f"## {title} ({len(items)})", ""] + [f"- {i}" for i in items] + [""]
    if repo:
        lines += ["## repository checks", ""] + [f"- {l}: {'ok' if ok else 'FAIL'}" for l, ok in repo] + [""]
    report = "\n".join(lines)
    with open(os.path.join(rundir, "report.md"), "w") as fh:
        fh.write(report)
    print(report)
    if rc not in (0, 1) and not checks:
        return 2
    return 0 if (rc == 0 and not failed and not reg) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
