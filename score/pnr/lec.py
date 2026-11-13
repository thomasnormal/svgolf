#!/usr/bin/env python3
"""lec.py: the reference-against-routed equivalence job of a routed-course run, and its log reader
(score/pnr/README.md, "The reference-against-routed equivalence job"). A TOOL ONLY: it is not a step of the pinned flow,
not part of a run's validity and not pinned (whether it should be is open).

    python3.12 score/pnr/lec.py config  JOBDIR JOB              # writes JOBDIR/lec/JOB.yml
    python3.12 score/pnr/lec.py run     JOBDIR JOB [--runtime docker] [--cpuset 0-1] [--dry-run]
    python3.12 score/pnr/lec.py verdict LOG                     # IDENTICAL (exit 0), DIFFERENT (1), NO VERDICT (3)

Why: the flow's own equivalence step (step 6_report, `LEC_CHECK=1`) compares the routed netlist with the flow's
rendering of the netlist the run was given, so it shows that place and route preserved the run's input, not that the
input was the design's netlist (that is checked by sha256). This job compares the routed netlist with the netlist FILE
the course binds (JOBDIR/designs/<nick>.v, whose sha256 is the ASAP7 view's `repaired_sha256`), with the same tool,
kepler-formal, inside the pinned image, and the flow's own configuration of the run
(run/objects/asap7/<nick>/<variant>/6_final_lec_test.yml) changed in three lines only: the first input (the reference)
is the bound netlist file, the second the run's routed `6_final_lec.v`, and the log file is JOBDIR/lec/JOB_lec_check.log.
The negative control of 2026-11-13 ran exactly this (score/PPA.md): 4 of 4 changed netlists DIFFERENT, 4 of 4
unchanged ones IDENTICAL.

The verdict: kepler-formal exits 0 whether the circuits are equal or not, so the verdict is read from its log.
IDENTICAL: the log prints "Circuits are IDENTICAL" and neither "Found difference" nor "Circuits are DIFFERENT".
DIFFERENT: it prints "Found difference" and "Circuits are DIFFERENT", and not "Circuits are IDENTICAL". Anything else
(an empty or cut-off log, both lines, neither) is NO VERDICT. Only IDENTICAL is a pass."""

import argparse
import os
import shlex
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pnr  # noqa: E402

IDENTICAL, DIFFERENT, NO_VERDICT = "IDENTICAL", "DIFFERENT", "NO VERDICT"
EXIT = {IDENTICAL: 0, DIFFERENT: 1, NO_VERDICT: 3}


def verdict(text):
    """IDENTICAL, DIFFERENT or NO VERDICT of a kepler-formal log's text (see the module text)."""
    same = "Circuits are IDENTICAL" in text
    found, differ = "Found difference" in text, "Circuits are DIFFERENT" in text
    if same and not found and not differ:
        return IDENTICAL
    if found and differ and not same:
        return DIFFERENT
    return NO_VERDICT


def config(flow_config, reference, routed, log_file):
    """The flow's own kepler-formal configuration (its text) with its two inputs and its log file replaced: the
    reference first, the routed netlist second. ValueError when the text is not of the flow's shape (an
    `input_paths:` line with exactly two `  - ` entries after it, one `log_file: ` line)."""
    lines = flow_config.splitlines()
    try:
        i = lines.index("input_paths:")
    except ValueError:
        raise ValueError("no `input_paths:` line")
    if len(lines) < i + 4 or not all(x.startswith("  - ") for x in lines[i + 1:i + 3]) or lines[i + 3].startswith("  - "):
        raise ValueError("`input_paths:` is not followed by exactly two inputs")
    k = [n for n, x in enumerate(lines) if x.startswith("log_file: ")]
    if len(k) != 1:
        raise ValueError("not exactly one `log_file:` line")
    out = list(lines)
    out[i + 1], out[i + 2], out[k[0]] = f"  - {reference}", f"  - {routed}", f"log_file: {log_file}"
    return "\n".join(out) + "\n"


def job_paths(job):
    """(reference, routed, log file) of a job's equivalence job, as the container sees them."""
    nick, variant, _ = pnr.parse_job(job)
    return (f"/work/designs/{nick}.v", f"/work/run/results/{pnr.PLATFORM_DIR}/{nick}/{variant}/6_final_lec.v",
            f"/work/lec/{job}_lec_check.log")


def write_config(job_dir, job):
    """JOBDIR/lec/JOB.yml from the run's own configuration; returns its path."""
    flow = os.path.join(pnr.work_dirs(job_dir, job)["objects"], "6_final_lec_test.yml")
    with open(flow, encoding="utf-8") as fh:
        text = config(fh.read(), *job_paths(job))
    os.makedirs(os.path.join(job_dir, "lec"), exist_ok=True)
    path = os.path.join(job_dir, "lec", job + ".yml")
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)
    return path


def run_command(job_dir, job, pins, runtime="docker", cpuset=None):
    """The container command: kepler-formal on JOBDIR/lec/JOB.yml in the pinned image, the bound netlist and the run's
    tree read-only."""
    nick, _variant, _ = pnr.parse_job(job)
    if not os.path.isfile(os.path.join(job_dir, "lec", job + ".yml")):
        raise ValueError(f"{job}: no JOBDIR/lec/{job}.yml (`lec.py config` first)")
    if not os.path.isfile(os.path.join(job_dir, "designs", nick + ".v")):
        raise ValueError(f"{job}: the bound netlist designs/{nick}.v is missing")
    mounts = [(os.path.join(job_dir, "designs"), "/work/designs", True), (os.path.join(job_dir, "run"), "/work/run", True),
              (os.path.join(job_dir, "lec"), "/work/lec", False), (os.path.join(job_dir, "tmp", job + ".lec"), "/tmp", False)]
    env = {k: v for k, v in pnr.IMAGE_ENV.items() if k != "QT_QPA_PLATFORM"}
    return pnr.container_command(runtime, pins, mounts, env, pnr.FLOW_DIR,
                                 ["bash", "-c", f"source ../env.sh >/dev/null && kepler-formal --config /work/lec/{job}.yml"],
                                 cpuset=cpuset)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("config")
    c.add_argument("job_dir")
    c.add_argument("job")
    r = sub.add_parser("run")
    r.add_argument("job_dir")
    r.add_argument("job")
    r.add_argument("--runtime", default=os.environ.get("SVGOLF_CONTAINER_RUNTIME", "docker"))
    r.add_argument("--cpuset")
    r.add_argument("--dry-run", action="store_true")
    v = sub.add_parser("verdict")
    v.add_argument("log")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "verdict":
            with open(args.log, encoding="utf-8", errors="replace") as fh:
                word = verdict(fh.read())
            print(word)
            return EXIT[word]
        if args.cmd == "config":
            print(write_config(args.job_dir, args.job))
            return 0
        cmd = run_command(args.job_dir, args.job, pnr.load_pins(), runtime=args.runtime, cpuset=args.cpuset)
    except (OSError, ValueError, KeyError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.dry_run:
        print(" ".join(shlex.quote(x) for x in cmd))
        return 0
    import run_job
    if not run_job.host_ok():
        print("error: the course's image is x86-64 Linux only; use --dry-run elsewhere", file=sys.stderr)
        return 2
    rc = run_job.execute(args.job_dir, args.job, cmd, f"{args.job}.lec.out", args.runtime, args.cpuset,
                         pnr.load_pins(), clean=False)
    log = os.path.join(args.job_dir, "lec", f"{args.job}_lec_check.log")
    word = NO_VERDICT
    if os.path.isfile(log):
        with open(log, encoding="utf-8", errors="replace") as fh:
            word = verdict(fh.read())
    print(f"{args.job}: kepler-formal exit {rc}; reference-against-routed: {word}")
    return EXIT[word] if rc == 0 else 2


if __name__ == "__main__":
    sys.exit(main())
