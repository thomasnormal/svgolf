#!/usr/bin/env python3
"""run_job.py: run one routed-course job, or draw its picture, in the pinned image (score/pnr/README.md).

    python3.12 score/pnr/run_job.py run    JOBDIR JOB [--runtime docker] [--cpuset 0-1] [--dry-run]
    python3.12 score/pnr/run_job.py render JOBDIR JOB [--runtime docker] [--cpuset 0-1] [--dry-run]

`run`: OpenROAD-flow-scripts' `make` on JOBDIR/cfg/JOB.mk (written by job.py) in the image score/pnr/pins.json pins,
pulled by its amd64 manifest digest (never by tag), with no network, the pinned number of CPUs (`--cpus` and a
`--cpuset-cpus` of that size), the pinned memory cap and no swap. The netlist, SDC and config.mk are mounted
read-only, ORFS's work tree (JOBDIR/run) read-write, a per-job /tmp. Before it starts, the config.mk is checked
against the pins (every pinned ORFS variable with its pinned value and no other, the pinned thread count, the job's
own name and seed): a job made under other pins is refused, not run. The job's earlier ORFS directories are removed
first (a clean run every time). Writes JOBDIR/logs/JOB.out (everything the job printed), appends
`JOB rc=N seconds=S cpus=C date=YYYY-MM-DD` to JOBDIR/logs/status.txt and writes JOBDIR/logs/JOB.host.json (the CPU
model, the OS, the kernel, the runtime; never the host's name). Exit status: the job's.

`render`: the layout picture of a finished job: OpenROAD's own GUI renderer, off-screen (QT_QPA_PLATFORM=offscreen),
draws the job's 6_final.odb (its run tree mounted READ-ONLY, so drawing cannot change a scored run) with
score/pnr/layout.tcl and draw.tcl (the flow's routing view, power and ground nets hidden) at 1600 px:
JOBDIR/img/JOB.png, log JOBDIR/logs/JOB.render.out (layout.tcl prints the die and core boxes the caption uses).
Then score/pnr/encode.py makes the WebP picture and thumbnail.

`--dry-run` prints the command and the checks' verdict and runs nothing (it works on any machine). A real run needs
x86-64 Linux and a container runtime (docker or podman) that can pull or already holds the image by digest; it is
refused elsewhere."""

import argparse
import datetime
import json
import os
import platform
import shlex
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pnr  # noqa: E402

PICTURE_WIDTH = 1600


def run_command(job_dir, job, pins, runtime="docker", cpuset=None):
    """The container command of `run` (a list), after the config.mk's check; ValueError when it is not a course job."""
    nick, variant, seed = pnr.parse_job(job)
    with open(os.path.join(job_dir, "cfg", job + ".mk"), encoding="utf-8") as fh:
        bad = pnr.config_problems(fh.read(), pins, job)
    if bad:
        raise ValueError(f"{job}: not a job of the pinned course: " + "; ".join(bad))
    for need in (os.path.join(job_dir, "designs", nick + ".v"), os.path.join(job_dir, "sdc", nick + ".sdc")):
        if not os.path.isfile(need):
            raise ValueError(f"{job}: {need} is missing")
    mounts = [(os.path.join(job_dir, "designs"), "/work/designs", True), (os.path.join(job_dir, "sdc"), "/work/sdc", True),
              (os.path.join(job_dir, "cfg"), "/work/cfg", True), (os.path.join(job_dir, "run"), "/work/run", False),
              (os.path.join(job_dir, "tmp", job), "/tmp", False)]
    return pnr.container_command(runtime, pins, mounts, pnr.IMAGE_ENV, pnr.FLOW_DIR,
                                 ["bash", "-c", f"source ../env.sh >/dev/null && make DESIGN_CONFIG=/work/cfg/{job}.mk"],
                                 cpuset=cpuset)


def render_command(job_dir, job, pins, runtime="docker", cpuset=None):
    """The container command of `render` (a list)."""
    nick, variant, _ = pnr.parse_job(job)
    odb = os.path.join(pnr.work_dirs(job_dir, job)["results"], "6_final.odb")
    if not os.path.isfile(odb):
        raise ValueError(f"{job}: no 6_final.odb (has the job run?)")
    env = dict(pnr.IMAGE_ENV, ODB_FILE=f"/srv/results/{pnr.PLATFORM_DIR}/{nick}/{variant}/6_final.odb",
               OUT_PNG=f"/work/img/{job}.png", IMG_WIDTH=str(PICTURE_WIDTH))
    mounts = [(os.path.join(job_dir, "run"), "/srv", True), (pnr.HERE, "/work/tools", True),
              (os.path.join(job_dir, "img"), "/work/img", False), (os.path.join(job_dir, "tmp", job + ".render"), "/tmp", False)]
    return pnr.container_command(runtime, pins, mounts, env, pnr.FLOW_DIR,
                                 ["bash", "-c", "source ../env.sh >/dev/null && openroad -no_init -threads "
                                  f"{int(pins['threads'])} -exit /work/tools/layout.tcl"], cpuset=cpuset)


def host_ok():
    return sys.platform.startswith("linux") and platform.machine() in ("x86_64", "AMD64")


def execute(job_dir, job, cmd, log_name, runtime, cpuset, pins, clean):
    """Run `cmd`, its output to JOBDIR/logs/<log_name>; record the status line and the host. Returns its exit status."""
    logs = os.path.join(job_dir, "logs")
    os.makedirs(logs, exist_ok=True)
    if clean:                                            # a clean run every time
        for d in pnr.work_dirs(job_dir, job).values():
            shutil.rmtree(d, ignore_errors=True)
    for host, _inside, ro in _mounts_of(cmd):
        if not ro:
            os.makedirs(host, exist_ok=True)
    ver = subprocess.run([runtime, "--version"], capture_output=True, text=True).stdout.strip() or runtime
    t0 = time.monotonic()
    with open(os.path.join(logs, log_name), "w", encoding="utf-8") as out:
        rc = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT).returncode
    sec = time.monotonic() - t0
    n = int(pins["cpu_affinity"])
    with open(os.path.join(logs, "status.txt"), "a", encoding="utf-8") as fh:
        fh.write(f"{job if log_name == job + '.out' else log_name[:-4]} rc={rc} seconds={sec:.4f} "
                 f"cpus={cpuset or f'0-{n - 1}'} date={datetime.datetime.now(datetime.timezone.utc).date()}\n")
    if clean:                                            # the run's host (a picture's host is not recorded)
        with open(os.path.join(logs, f"{job}.host.json"), "w", encoding="utf-8") as fh:
            fh.write(json.dumps(pnr.host_description(ver), indent=1, sort_keys=True) + "\n")
    for host, inside, _ro in _mounts_of(cmd):            # this job's own /tmp only
        if inside == "/tmp":
            shutil.rmtree(host, ignore_errors=True)
    return rc


def _mounts_of(cmd):
    """[(host, container, read_only)] of a container command's -v options."""
    out = []
    for i, a in enumerate(cmd):
        if a == "-v":
            spec = cmd[i + 1]
            ro = spec.endswith(":ro")
            host, inside = (spec[:-3] if ro else spec).rsplit(":", 1)
            out.append((host, inside, ro))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("what", choices=("run", "render"))
    ap.add_argument("job_dir")
    ap.add_argument("job")
    ap.add_argument("--runtime", default=os.environ.get("SVGOLF_CONTAINER_RUNTIME", "docker"),
                    help="docker (default, or $SVGOLF_CONTAINER_RUNTIME) or podman")
    ap.add_argument("--cpuset", help="the CPUs to pin the job to, e.g. 2-3 (default: the first ones)")
    ap.add_argument("--dry-run", action="store_true", help="print the command; run nothing")
    args = ap.parse_args(argv)
    try:
        pins = pnr.load_pins()
        build = run_command if args.what == "run" else render_command
        cmd = build(args.job_dir, args.job, pins, runtime=args.runtime, cpuset=args.cpuset)
    except (OSError, ValueError, KeyError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    if args.dry_run:
        print(" ".join(shlex.quote(c) for c in cmd))
        return 0
    if not host_ok():
        print("error: the course's image is x86-64 Linux only (score/pnr/README.md); use --dry-run elsewhere",
              file=sys.stderr)
        return 2
    if shutil.which(args.runtime) is None:
        print(f"error: no container runtime {args.runtime!r} on PATH", file=sys.stderr)
        return 2
    log = f"{args.job}.out" if args.what == "run" else f"{args.job}.render.out"
    rc = execute(args.job_dir, args.job, cmd, log, args.runtime, args.cpuset, pins, clean=args.what == "run")
    print(f"{args.job}: {args.what} rc={rc} (JOBDIR/logs/{log})")
    return rc


if __name__ == "__main__":
    sys.exit(main())
