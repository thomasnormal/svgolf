#!/usr/bin/env python3.12
"""host.py: the second of a round's three place-and-route steps (score/pnr/README.md, "A round's runs, in one
sequence"), on the course host: every job prepare.py made, by the course's own commands, then the files finish.py
reads, packed. The round's directory is copied to the host and its tree unpacked there first:

    tar -xf ROUND/tree.tar -C ROUND          # ROUND/svgolf: the tree prepare.py packed
    python3.12 ROUND/svgolf/score/pnr/campaign/host.py run ROUND [--runtime docker|podman|chroot] [--rootfs DIR]
    python3.12 ROUND/svgolf/score/pnr/campaign/host.py pack ROUND          # ROUND/back.tar, for finish.py

`run` is a FOREGROUND scheduler for a shared machine (no daemon: it runs while the command that started it runs, and on
SIGTERM, SIGHUP or SIGINT kills its own jobs, each by its process group, and stops): at most --max-jobs (at most 4) jobs
at once, each with the pinned number of CPUs (pins.json `cpu_affinity`, a CPU set of its own) and the pinned memory
cap, at nice 19; a job is started only when MemAvailable is at least --launch-gb (150) GB, the other users' summed CPU
is at most 25 % of the cores and, while another user has a terminal session idle under five minutes, fewer than two of
its jobs run; every job is killed when MemAvailable falls under --kill-gb (100) GB or the one-minute load passes the
larger of 64 and half the core count; a job over --wall-hours (4) is killed. It resumes: a job whose row (job/rows/JOB.json)
exists is done. Log: ROUND/logs/runner.log (an observation a minute) and ROUND/logs/JOB.steps.log.

`job ROUND JOB` (what `run` starts for each job) makes the job's steps in run_job.py's order (README, "The commands,
for one design", 2 and 3): the flow, the run's host block and, when the flow exited 0, the reference-against-routed
check (lec.py), then the picture, then `collect.py row` (also for a failed run: the row records the flow's reason).
With --runtime docker or podman these are run_job.py's own commands. With --runtime chroot (a host with no container
runtime: the method of the 2026-11-13 calibration and of the 2026-11-27 round) each container command run_job.py and
lec.py build is run with the SAME mounts, environment, working directory and command under a rootless user namespace
and chroot of the pinned image unpacked at --rootfs (its PATH, --image-path), in a systemd user scope with the pinned
memory cap and no swap, at nice 19, on the job's CPU set; the run's host block then says "rootless userns+chroot".

`pack ROUND` writes ROUND/back.tar: what finish.py and check_sitedata.py read (job/ rows, logs, img, lec, cfg, sdc,
designs and jobs; each run's routed 6_final_lec.v, the flow's own check configuration 6_final_lec_test.yml and ORFS's
logs and reports; ROUND/logs). The databases stay on the host (their sha256 are in the rows)."""

import argparse
import datetime
import getpass
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PNR_DIR = os.path.dirname(HERE)
sys.path.insert(0, PNR_DIR)
import lec  # noqa: E402
import pnr  # noqa: E402
import run_job  # noqa: E402

# the pinned image's PATH (its configuration's Env), which `docker run` keeps and a chroot has to set
IMAGE_PATH = "/usr/local/bin/wrapped-cc:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
CHROOT_RUNTIME = "rootless userns+chroot"
MAX_JOBS = 4
# the in-namespace part of a chroot command: proc, the skeleton on /work, each mount (read-only ones remounted so), /sys
# and five device nodes, then chroot with a clean environment
CHROOT_SCRIPT = r'''set -e
R=$1; SK=$2; shift 2
mount -t proc proc "$R/proc"
mount --bind "$SK" "$R/work"
while [ "$1" != "--" ]; do
  mount --bind "$1" "$R$2"
  if [ "$3" = ro ]; then mount -o remount,bind,ro "$R$2"; fi
  shift 3
done
shift
mount --rbind /sys "$R/sys"
for d in null zero random urandom full; do mount --bind /dev/$d "$R/dev/$d"; done
exec chroot "$R" "$@"'''


def parse_container_command(cmd):
    """(mounts [(host, inside, read_only)], env ["K=V"], workdir, argv) of pnr.container_command's docker form."""
    env = [cmd[i + 1] for i, a in enumerate(cmd) if a == "-e"]
    w = cmd.index("-w")
    return run_job._mounts_of(cmd), env, cmd[w + 1], cmd[w + 3:]


def chroot_command(cmd, rootfs, skeleton, pins, cpuset, image_path=IMAGE_PATH):
    """The container command `cmd` as the rootless chroot of the unpacked image `rootfs`: the same mounts (`skeleton`, an
    empty directory with one subdirectory per mount under /work, stands in for the image's /work), environment, working
    directory and command; a systemd user scope with the pinned memory cap and no swap; nice 19; CPU set `cpuset`."""
    mounts, env, workdir, argv = parse_container_command(cmd)
    cap = int(pins["memory_cap_gb"])
    spec = []
    for host, inside, ro in mounts:
        spec += [os.path.abspath(host), inside, "ro" if ro else "rw"]
    inner = ["/usr/bin/env", "-i", f"PATH={image_path}"] + env + ["/bin/bash", "-c", 'cd "$1" && shift && exec "$@"',
                                                                   "chroot-cd", workdir] + list(argv)
    return (["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={cap}G", "-p", "MemorySwapMax=0", "nice", "-n",
             "19", "taskset", "-c", cpuset, "unshare", "-U", "-r", "-m", "-p", "-f", "bash", "-c", CHROOT_SCRIPT,
             "chroot-mounts", os.path.abspath(rootfs), os.path.abspath(skeleton)] + spec + ["--"] + inner)


def execute(job_dir, job, cmd, log_name, cpuset):
    """Run `cmd`, its output to JOBDIR/logs/<log_name>, and append the status line in run_job.py's format
    (`JOB[.lec|.render] rc=N seconds=S cpus=C date=YYYY-MM-DD`). Returns the exit status."""
    logs = os.path.join(job_dir, "logs")
    os.makedirs(logs, exist_ok=True)
    t0 = time.monotonic()
    with open(os.path.join(logs, log_name), "w", encoding="utf-8") as out:
        rc = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT).returncode
    sec = time.monotonic() - t0
    with open(os.path.join(logs, "status.txt"), "a", encoding="utf-8") as fh:
        fh.write(f"{job if log_name == job + '.out' else log_name[:-4]} rc={rc} seconds={sec:.4f} cpus={cpuset} "
                 f"date={datetime.datetime.now(datetime.timezone.utc).date()}\n")
    return rc


def chroot_step(job_dir, job, cmd, log_name, args, pins, clean):
    """One container command of a job under the chroot, as run_job.execute runs it under docker: with `clean` (the
    flow) the job's earlier ORFS directories removed first and the run's host block written after; the read-write
    mount directories and the skeleton made; the job's own /tmp removed after."""
    mounts = parse_container_command(cmd)[0]
    if clean:
        for d in pnr.work_dirs(job_dir, job).values():
            shutil.rmtree(d, ignore_errors=True)
    skeleton = os.path.join(args.round, "host", "skeleton", job)
    for host, inside, ro in mounts:
        if not ro:
            os.makedirs(host, exist_ok=True)
        if inside.startswith("/work/"):
            os.makedirs(os.path.join(skeleton, inside[len("/work/"):]), exist_ok=True)
    full = chroot_command(cmd, args.rootfs, skeleton, pins, args.cpuset, args.image_path)
    rc = execute(job_dir, job, full, log_name, args.cpuset)
    if clean:
        with open(os.path.join(job_dir, "logs", f"{job}.host.json"), "w", encoding="utf-8") as fh:
            fh.write(json.dumps(pnr.host_description(CHROOT_RUNTIME), indent=1, sort_keys=True) + "\n")
    for host, inside, _ro in mounts:
        if inside == "/tmp":
            shutil.rmtree(host, ignore_errors=True)
    return rc


def flow_rc(job_dir, job):
    """The flow's exit status from the job's last status line (`JOB rc=N ...`), or None."""
    rc = None
    try:
        with open(os.path.join(job_dir, "logs", "status.txt"), encoding="utf-8") as fh:
            for ln in fh:
                f = ln.split()
                if len(f) > 1 and f[0] == job and f[1].startswith("rc="):
                    rc = int(f[1][3:])
    except OSError:
        pass
    return rc


def cmd_job(args):
    """One job's steps (see the module text). Exit 0 when the row was written."""
    jd = os.path.join(args.round, "job")
    pins = pnr.load_pins()
    py = [sys.executable, "-I"]
    if args.runtime == "chroot":
        if not args.rootfs:
            print("error: --runtime chroot needs --rootfs (the pinned image unpacked)", file=sys.stderr)
            return 2
        rc = chroot_step(jd, args.job, run_job.run_command(jd, args.job, pins, cpuset=args.cpuset), f"{args.job}.out",
                         args, pins, clean=True)
        if rc == 0:
            lec.write_config(jd, args.job)
            chroot_step(jd, args.job, lec.run_command(jd, args.job, pins, cpuset=args.cpuset), f"{args.job}.lec.out",
                        args, pins, clean=False)
            chroot_step(jd, args.job, run_job.render_command(jd, args.job, pins, cpuset=args.cpuset),
                        f"{args.job}.render.out", args, pins, clean=False)
    else:
        rj = os.path.join(PNR_DIR, "run_job.py")
        subprocess.run(["nice", "-n", "19"] + py + [rj, "run", jd, args.job, "--runtime", args.runtime, "--cpuset",
                                                    args.cpuset])
        if flow_rc(jd, args.job) == 0:
            subprocess.run(["nice", "-n", "19"] + py + [rj, "render", jd, args.job, "--runtime", args.runtime,
                                                        "--cpuset", args.cpuset])
    os.makedirs(os.path.join(jd, "rows"), exist_ok=True)
    p = subprocess.run(["nice", "-n", "19"] + py + [os.path.join(PNR_DIR, "collect.py"), "row", jd, args.job, "--out",
                                                    os.path.join(jd, "rows", args.job + ".json")])
    print(f"{args.job}: steps done, flow rc={flow_rc(jd, args.job)}, row rc={p.returncode}")
    return p.returncode


# --- the scheduler ---------------------------------------------------------------------------------------------------

def mem_avail_gb():
    with open("/proc/meminfo", encoding="utf-8") as fh:
        for ln in fh:
            if ln.startswith("MemAvailable:"):
                return int(ln.split()[1]) / 1048576
    return 0.0


def others_cpu_pct(me):
    out = subprocess.run(["ps", "-eo", "user:32,pcpu", "--no-headers"], capture_output=True, text=True).stdout
    return sum(float(c) for u, c in (ln.split() for ln in out.splitlines() if len(ln.split()) == 2) if u != me)


def interactive_others(me):
    """Other users' terminal sessions idle under five minutes (`w -h -s`: USER TTY FROM IDLE WHAT)."""
    out = subprocess.run(["w", "-h", "-s"], capture_output=True, text=True).stdout
    n = 0
    for ln in out.splitlines():
        f = ln.split()
        if len(f) < 4 or f[0] == me:
            continue
        idle = f[3]
        if idle.endswith("s") and not idle.endswith("days"):
            n += 1
        elif ":" in idle and not idle.endswith("m"):
            n += int(idle.split(":")[0]) < 5
    return n


def cmd_run(args):
    """The scheduler (see the module text). Exit 0 when every job has its row, 1 when one has none, 3 when stopped."""
    rnd = args.round
    jd = os.path.join(rnd, "job")
    logs = os.path.join(rnd, "logs")
    os.makedirs(logs, exist_ok=True)
    me, ncpu = getpass.getuser(), os.cpu_count() or 1
    n = int(pnr.load_pins()["cpu_affinity"])
    maxj = max(1, min(args.max_jobs, MAX_JOBS))
    stride = 8 if ncpu >= 8 * maxj else n
    max_load = max(64, ncpu // 2)
    slots = {i: None for i in range(maxj)}

    def log(msg):
        with open(os.path.join(logs, "runner.log"), "a", encoding="utf-8") as fh:
            fh.write(time.strftime("%Y-%m-%dT%H:%M:%S ") + msg + "\n")

    def stop(why, _frame=None):
        for s, v in slots.items():
            if v:
                log(f"STOP ({why}): kill process group {v[1].pid} ({v[0]})")
                try:
                    os.killpg(v[1].pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        log("stopped")
        sys.exit(3)

    for sig in (signal.SIGTERM, signal.SIGHUP, signal.SIGINT):
        signal.signal(sig, stop)
    with open(os.path.join(rnd, "jobs.txt"), encoding="utf-8") as fh:
        jobs = [ln.strip() for ln in fh if ln.strip() and not ln.startswith("#")]
    queue = [j for j in jobs if not os.path.exists(os.path.join(jd, "rows", j + ".json"))]
    log(f"start jobs={len(jobs)} todo={len(queue)} max_jobs={maxj} cpus={ncpu} runtime={args.runtime} pid={os.getpid()}")
    last = 0.0
    while queue or any(slots.values()):
        for s, v in slots.items():
            if v and v[1].poll() is not None:
                log(f"done {v[0]} rc={v[1].returncode} slot={s} seconds={time.time() - v[2]:.1f}")
                slots[s] = None
            elif v and time.time() - v[2] > args.wall_hours * 3600:
                log(f"KILL {v[0]}: over {args.wall_hours} h")
                os.killpg(v[1].pid, signal.SIGKILL)
        ma, oc, io = mem_avail_gb(), others_cpu_pct(me), interactive_others(me)
        with open("/proc/loadavg", encoding="utf-8") as fh:
            load = float(fh.read().split()[0])
        ours = sum(1 for v in slots.values() if v)
        if time.time() - last > 60:
            log(f"obs mem_avail_gb={ma:.0f} others_cpu_pct={oc:.0f} interactive_others={io} ours={ours} "
                f"queue={len(queue)} load={load}")
            last = time.time()
        if ma < args.kill_gb:
            stop(f"MemAvailable under {args.kill_gb} GB")
        if load > max_load:
            stop(f"load over {max_load}")
        cap = maxj if io == 0 else min(maxj, 2)
        free = [s for s, v in slots.items() if v is None]
        if queue and free and ours < cap and ma >= args.launch_gb and oc <= 0.25 * ncpu * 100:
            job, s = queue.pop(0), free[0]
            cpus = f"{stride * s}-{stride * s + n - 1}"
            cmd = [sys.executable, "-I", os.path.abspath(__file__), "job", rnd, job, "--runtime", args.runtime,
                   "--cpuset", cpus, "--image-path", args.image_path] + (["--rootfs", args.rootfs] if args.rootfs else [])
            with open(os.path.join(logs, job + ".steps.log"), "w", encoding="utf-8") as out:
                p = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT, start_new_session=True)
            slots[s] = (job, p, time.time())
            log(f"launch {job} slot={s} cpus={cpus} pid={p.pid} mem_avail_gb={ma:.0f} others_cpu_pct={oc:.0f}")
            continue
        time.sleep(2)
    missing = [j for j in jobs if not os.path.exists(os.path.join(jd, "rows", j + ".json"))]
    log(f"all done: {len(jobs) - len(missing)} of {len(jobs)} jobs have their row")
    print(f"{len(jobs) - len(missing)} of {len(jobs)} jobs have their row" + "".join(f"\n  no row: {j}" for j in missing))
    return 1 if missing else 0


def cmd_pack(args):
    """ROUND/back.tar (see the module text)."""
    rnd = os.path.abspath(args.round)
    jd = os.path.join(rnd, "job")
    names = []
    for sub in ("rows", "logs", "img", "lec", "cfg", "sdc", "designs", "jobs"):
        for root, _dirs, files in os.walk(os.path.join(jd, sub)):
            names += [os.path.join(root, f) for f in files]
    for root, _dirs, files in os.walk(os.path.join(jd, "run")):
        rel = os.path.relpath(root, jd).split(os.sep)
        for f in files:
            if f in ("6_final_lec.v", "6_final_lec_test.yml") or (len(rel) > 1 and rel[1] in ("logs", "reports")):
                names.append(os.path.join(root, f))
    for root, _dirs, files in os.walk(os.path.join(rnd, "logs")):
        names += [os.path.join(root, f) for f in files]
    out = os.path.join(rnd, "back.tar")
    with tarfile.open(out, "w") as tar:
        for p in sorted(names):
            tar.add(p, arcname=os.path.relpath(p, rnd), recursive=False)
    print(f"wrote {out}: {len(names)} files")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("run", "job"):
        s = sub.add_parser(name)
        s.add_argument("round", help="the round's directory (prepare.py --out)")
        if name == "job":
            s.add_argument("job")
            s.add_argument("--cpuset", required=True)
        s.add_argument("--runtime", default=os.environ.get("SVGOLF_CONTAINER_RUNTIME", "docker"),
                       choices=("docker", "podman", "chroot"))
        s.add_argument("--rootfs", help="with --runtime chroot: the pinned image unpacked")
        s.add_argument("--image-path", default=IMAGE_PATH, help="with --runtime chroot: the image's PATH")
        if name == "run":
            s.add_argument("--max-jobs", type=int, default=MAX_JOBS, help=f"at most {MAX_JOBS}")
            s.add_argument("--launch-gb", type=float, default=150.0)
            s.add_argument("--kill-gb", type=float, default=100.0)
            s.add_argument("--wall-hours", type=float, default=4.0)
    s = sub.add_parser("pack")
    s.add_argument("round")
    args = ap.parse_args(argv)
    args.round = os.path.abspath(args.round)
    if args.cmd == "pack":
        return cmd_pack(args)
    if args.runtime == "chroot" and not args.rootfs:
        print("error: --runtime chroot needs --rootfs (the pinned image unpacked)", file=sys.stderr)
        return 2
    if not run_job.host_ok():
        print("error: the course's image is x86-64 Linux only (score/pnr/README.md)", file=sys.stderr)
        return 2
    return cmd_run(args) if args.cmd == "run" else cmd_job(args)


if __name__ == "__main__":
    sys.exit(main())
