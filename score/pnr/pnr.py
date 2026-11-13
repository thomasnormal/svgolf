#!/usr/bin/env python3
"""What the routed course's run tools share (score/pnr/README.md): the pins, the paths of a job directory, the
container command that runs the pinned image, and a few hashes. Standard library only.

A JOB DIRECTORY (one per campaign, any number of jobs) is mounted at /work inside the image, so the paths in each
config.mk are the ones the committed runs were made with:

    designs/<nick>.v      the design's ASAP7 netlist (the ASAP7 view's repaired netlist), read-only in the container
    sdc/<nick>.sdc        its timing setup, read-only
    cfg/<job>.mk          the job's config.mk, read-only
    jobs/<job>.json       what job.py wrote about the job (not read by the image)
    run/                  ORFS's WORK_HOME (results/, logs/, reports/, objects/ under asap7/<nick>/<variant>/)
    logs/                 <job>.out (the job's output), status.txt (one line per finished job), <job>.host.json
    img/, rows/, lec/     the picture, the collected row and the equivalence job (lec.py) of a job

<nick> = <task>_<first 12 hex of the netlist's sha256>, <variant> = min_s<seed>, <job> = <nick>__<variant>."""

import hashlib
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
PINS = os.path.join(HERE, "pins.json")
PLATFORM_DIR = "asap7"                    # ORFS's platform name in its work tree (pins.json `platform`)
FLOW_DIR = "/OpenROAD-flow-scripts/flow"  # inside the image
SEED_MAX = 2 ** 31 - 1
JOB_RE = re.compile(r"(?P<nick>[a-z_][a-z0-9_]*_[0-9a-f]{12})__(?P<variant>min_s(?P<seed>[1-9][0-9]{0,9}))")
# the variables of a config.mk that name the job itself; every other one is a pinned ORFS variable
PER_JOB = ("DESIGN_NAME", "DESIGN_NICKNAME", "PLATFORM", "SYNTH_NETLIST_FILES", "VERILOG_FILES", "SDC_FILE",
           "FLOW_VARIANT", "WORK_HOME", "GPL_RANDOM_SEED")


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def load_pins(path=PINS):
    """score/pnr/pins.json's `course`: the pins every routed result is made under."""
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)["course"]


def image_ref(pins):
    """The pinned image by digest: its amd64 manifest (pins `image.manifest_digest`), never by tag."""
    img = pins["image"]
    return f"docker.io/{img['repo']}@{img['manifest_digest']}"


def parse_job(job):
    """(nick, variant, seed) of a job name, or ValueError."""
    m = JOB_RE.fullmatch(job or "")
    if not m:
        raise ValueError(f"{job!r} is not a job name <task>_<12 hex>__min_s<seed>")
    seed = int(m.group("seed"))
    if seed > SEED_MAX:
        raise ValueError(f"{job!r}: seed out of 1..2^31-1")
    return m.group("nick"), m.group("variant"), seed


def work_dirs(job_dir, job):
    """{results, logs, reports, objects}: the job's ORFS directories under job_dir/run."""
    nick, variant, _ = parse_job(job)
    return {k: os.path.join(job_dir, "run", k, PLATFORM_DIR, nick, variant)
            for k in ("results", "logs", "reports", "objects")}


def config_vars(text):
    """The `export NAME = VALUE` lines of a config.mk, as a dict (later lines win, as in make)."""
    return {m.group(1): m.group(2) for m in re.finditer(r"^export (\w+) = (.*)$", text, re.M)}


def config_problems(text, pins, job=None):
    """What makes a config.mk not a course job: a pinned ORFS variable missing or another value, a variable the pins
    do not have, a thread count other than the pins', or (with `job`) a nickname, variant or seed other than the job
    name's. [] for a good one."""
    v = config_vars(text)
    p = []
    want = pins["orfs_variables"]
    for k in sorted(set(want) | (set(v) - set(PER_JOB))):
        if v.get(k) != want.get(k):
            p.append(f"{k} is {v.get(k)!r}, the pins say {want.get(k)!r}")
    for k in PER_JOB:
        if k not in v:
            p.append(f"{k} missing")
    if v.get("NUM_CORES") != str(pins["threads"]):
        p.append(f"NUM_CORES is not the pinned {pins['threads']} threads")
    if v.get("PLATFORM") != pins["platform"]:
        p.append(f"PLATFORM is not {pins['platform']}")
    if v.get("WORK_HOME") != "/work/run":
        p.append("WORK_HOME is not /work/run")
    if job is not None:
        nick, variant, seed = parse_job(job)
        if (v.get("DESIGN_NICKNAME"), v.get("FLOW_VARIANT"), v.get("GPL_RANDOM_SEED")) != (nick, variant, str(seed)):
            p.append(f"DESIGN_NICKNAME, FLOW_VARIANT or GPL_RANDOM_SEED is not the job name's ({job})")
        for k, want_path in (("SYNTH_NETLIST_FILES", f"/work/designs/{nick}.v"), ("VERILOG_FILES", f"/work/designs/{nick}.v"),
                             ("SDC_FILE", f"/work/sdc/{nick}.sdc")):
            if v.get(k) != want_path:
                p.append(f"{k} is not {want_path}")
    return p


def container_command(runtime, pins, mounts, env, workdir, argv, *, cpuset=None):
    """The command that runs `argv` in the pinned image: by digest, amd64, no network, the pinned thread count as CPUs
    (and `cpuset`, else the first ones), the pinned memory cap with no swap. `mounts` is [(host path, container path,
    read_only)], `env` {name: value} (the image's own PATH is kept)."""
    n = int(pins["cpu_affinity"])
    cap = f"{int(pins['memory_cap_gb'])}g"
    cmd = [runtime, "run", "--rm", "--network", "none", "--platform", f"linux/{pins['image']['arch']}",
           "--cpus", str(n), "--cpuset-cpus", cpuset or f"0-{n - 1}", "--memory", cap, "--memory-swap", cap]
    for host, inside, ro in mounts:
        cmd += ["-v", f"{os.path.abspath(host)}:{inside}" + (":ro" if ro else "")]
    for k in sorted(env):
        cmd += ["-e", f"{k}={env[k]}"]
    return cmd + ["-w", workdir, image_ref(pins)] + list(argv)


# the environment of every command in the image (the committed runs': a clean environment with these and the image's
# PATH; QT_QPA_PLATFORM=offscreen is the flow's own setting for drawing without a display)
IMAGE_ENV = {"HOME": "/tmp", "TMPDIR": "/tmp", "TERM": "dumb", "QT_QPA_PLATFORM": "offscreen",
             "PYTHONDONTWRITEBYTECODE": "1"}


def host_description(runtime_text):
    """The host block a run records ({cpu, os, kernel, runtime}), read from the machine (Linux): the CPU model, the
    OS's PRETTY_NAME, the kernel release and the container runtime. Never the host's name."""
    cpu = osname = "unknown"
    try:
        with open("/proc/cpuinfo", encoding="utf-8", errors="replace") as fh:
            m = re.search(r"^model name\s*:\s*(.+)$", fh.read(), re.M)
            cpu = m.group(1).strip() if m else cpu
    except OSError:
        pass
    try:
        with open("/etc/os-release", encoding="utf-8", errors="replace") as fh:
            m = re.search(r'^PRETTY_NAME="?([^"\n]*)"?$', fh.read(), re.M)
            osname = m.group(1) if m else osname
    except OSError:
        pass
    return {"cpu": cpu, "os": osname, "kernel": os.uname().release, "runtime": runtime_text}
