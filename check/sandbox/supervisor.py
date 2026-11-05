"""The supervisor: one command, hard limits, from OUTSIDE the sandbox.

    python3.12 check.py --_timed WALL_S [--rss-mb N] [--out-mb N] [--cpu-s N] [--fsize-mb N]
                        [--nofile N] [--merge] [--cwd DIR] [--forward-env NAME ...] -- COMMAND...

It runs COMMAND in a new session and enforces, in the parent of the sandboxed process (which
cannot touch it):

  * a wall-clock limit (kill the whole process group; exit status 124, `SVGOLF_TIMEOUT` on stderr);
    the clock starts when the command does, so it excludes the wait in a slot wrapper in front of it;
  * a resident-memory limit summed over the process group, POLLED (macOS cannot enforce RLIMIT_AS at all,
    and an address-space limit would break the mmap of Mathlib's oleans anyway; exit status 125,
    `SVGOLF_MEMORY`). Measured 2026-10-31: a Lean memory bomb allocates 1.2 GB in 0.6 s, so the
    poll is 0.1 s and the limit has headroom for one interval;
  * a cap on the bytes of output the checker will ever buffer (`capture_output=True` in the callers
    would otherwise let a flood to /dev/fd/1 exhaust the CHECKER; exit status 126, `SVGOLF_OUTPUT`);
  * RLIMIT_CPU, RLIMIT_FSIZE (a disk bomb is stopped by SIGXFSZ), RLIMIT_NOFILE, RLIMIT_CORE=0.

The command's stdout goes to this process's stdout (capped), its stderr to stderr, or into stdout with
`--merge`. When the command ends, one control line is printed on stderr:

    SVGOLF_ELAPSED <seconds> peak_rss_mb=<n> out_bytes=<n> verdict=<none|memory|output>

The genuine line is the LAST one (a command can print the same words earlier, which `split_status`
in check.py ignores); on a timeout `SVGOLF_TIMEOUT after <s>s` is printed instead and the status is 124.
Whatever the command left running in its process group dies with it.
"""

import os
import resource
import signal
import subprocess
import sys
import threading
import time

POLL_S = 0.1
READ_CHUNK = 65536


def group_rss_kb(pgid):
    """Resident set (KB) of the processes in process group `pgid` (ps works on macOS and Linux)."""
    try:
        out = subprocess.run(["ps", "-axo", "pgid=,rss="], capture_output=True, text=True,
                             timeout=5, env={"PATH": "/usr/bin:/bin"}).stdout
    except (OSError, subprocess.SubprocessError):
        return 0
    tot = 0
    for ln in out.splitlines():
        f = ln.split()
        if len(f) == 2 and f[0] == str(pgid) and f[1].isdigit():
            tot += int(f[1])
    return tot


def forward_env(cmd, environ, names):
    """`cmd` with the variables `names` that are set in `environ` added to the environment a sandboxed
    command is given. A slot wrapper in front of the supervisor sets LEAN_NUM_THREADS for ITS child, and the
    sandboxed command's environment is built to the last variable (`env -i ...` on macOS, `--clearenv
    --setenv ...` for bubblewrap), so the supervisor, which sees the wrapper's variable, passes it on."""
    extra = [(n, environ[n]) for n in names if n in environ]
    if not extra:
        return list(cmd)
    if cmd[:2] == ["/usr/bin/env", "-i"]:
        return cmd[:2] + [f"{k}={v}" for k, v in extra] + cmd[2:]
    if "--clearenv" in cmd:
        i = cmd.index("--clearenv") + 1
        return cmd[:i] + [x for k, v in extra for x in ("--setenv", k, v)] + cmd[i:]
    return list(cmd)


def parse(argv):
    """argv after `--_timed`: WALL_S [--opt value ...] [--merge] -- COMMAND..."""
    o = {"wall": float(argv[0]), "rss_mb": 0.0, "out_mb": 0.0, "cpu_s": 0.0, "fsize_mb": 0.0,
         "nofile": 4096.0, "merge": False, "cwd": None, "forward_env": []}
    i = 1
    while i < len(argv) and argv[i] != "--":
        k = argv[i].lstrip("-").replace("-", "_")
        if k == "merge":
            o["merge"] = True
            i += 1
        elif k == "cwd":
            o["cwd"] = argv[i + 1]
            i += 2
        elif k == "forward_env":
            o["forward_env"].append(argv[i + 1])
            i += 2
        else:
            o[k] = float(argv[i + 1])
            i += 2
    return o, argv[i + 1:]


def _limits(o):
    def f():
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if o["nofile"]:
            n = int(o["nofile"])
            soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)
            resource.setrlimit(resource.RLIMIT_NOFILE, (min(n, hard) if hard >= 0 else n, hard))
        if o["cpu_s"]:
            resource.setrlimit(resource.RLIMIT_CPU, (int(o["cpu_s"]), int(o["cpu_s"]) + 5))
        if o["fsize_mb"]:
            b = int(o["fsize_mb"] * 1048576)
            resource.setrlimit(resource.RLIMIT_FSIZE, (b, b))
    return f


def main(argv):
    o, cmd = parse(argv)
    if not cmd:
        print("usage: --_timed WALL_S [limits] -- COMMAND...", file=sys.stderr)
        return 2
    cmd = forward_env(cmd, os.environ, o["forward_env"])
    t0 = time.time()
    # The command runs in its own session, so a signal to this process or to its group does not reach it. If the
    # checker dies or this process is told to stop, the command must not live on: an orphaned `yosys-abc` once ran
    # for eleven hours after the job that started it had gone.
    parent = os.getppid()
    stopped = []
    for sig in (signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, lambda signum, _frame: stopped.append(signum))
    try:
        p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, cwd=o["cwd"],
                             stderr=subprocess.STDOUT if o["merge"] else subprocess.PIPE,
                             start_new_session=True, preexec_fn=_limits(o))
    except OSError as e:
        print(f"SVGOLF_SPAWN_FAILED {e}", file=sys.stderr)
        return 127
    cap = int(o["out_mb"] * 1048576)
    state = {"bytes": 0, "over": False}
    lock = threading.Lock()

    def pump(src, dst):
        while True:
            b = os.read(src.fileno(), READ_CHUNK)
            if not b:
                break
            with lock:
                room = (cap - state["bytes"]) if cap else len(b)
                state["bytes"] += len(b)
                over = bool(cap) and state["bytes"] > cap
            if room > 0:
                dst.write(b[:room])
                dst.flush()
            if over and not state["over"]:
                state["over"] = True
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    pass
    threads = [threading.Thread(target=pump, args=(p.stdout, sys.stdout.buffer), daemon=True)]
    if not o["merge"]:
        threads.append(threading.Thread(target=pump, args=(p.stderr, sys.stderr.buffer), daemon=True))
    for t in threads:
        t.start()
    verdict, peak = None, 0
    while p.poll() is None:
        time.sleep(POLL_S)
        if stopped or os.getppid() != parent:
            verdict = "abandoned"
            break
        if o["wall"] and time.time() - t0 > o["wall"]:
            verdict = "timeout"
            break
        if o["rss_mb"]:
            kb = group_rss_kb(p.pid)
            peak = max(peak, kb)
            if kb > o["rss_mb"] * 1024:
                verdict = "memory"
                break
        if state["over"]:
            verdict = "output"
            break
    try:
        os.killpg(p.pid, signal.SIGKILL)     # whatever the command left in its group dies with it
    except (ProcessLookupError, PermissionError):
        pass
    p.wait()
    for t in threads:
        t.join(timeout=5)
    if state["over"]:
        verdict = verdict or "output"
    sys.stdout.flush()
    sys.stderr.flush()
    if verdict == "timeout":
        print(f"SVGOLF_TIMEOUT after {o['wall']:.0f}s", file=sys.stderr)
        return 124
    if verdict == "abandoned":
        print("SVGOLF_ABANDONED the checker went away or asked this run to stop", file=sys.stderr)
        return 143
    el = time.time() - t0
    rc = p.returncode if p.returncode >= 0 else 128 - p.returncode
    if verdict == "memory":
        print(f"SVGOLF_MEMORY over {o['rss_mb']:.0f} MB (the process group reached {peak/1024:.0f} MB)",
              file=sys.stderr)
        rc = 125
    elif verdict == "output":
        print(f"SVGOLF_OUTPUT over {o['out_mb']:.0f} MB", file=sys.stderr)
        rc = 126
    print(f"SVGOLF_ELAPSED {el:.2f} peak_rss_mb={peak/1024:.0f} out_bytes={state['bytes']} "
          f"verdict={verdict or 'none'}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
