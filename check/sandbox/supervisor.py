"""The supervisor: one command, hard limits, from OUTSIDE the sandbox.

    python3.12 check.py --_timed WALL_S [--cpu-limit-s N] [--rss-mb N] [--out-mb N] [--cpu-s N] [--fsize-mb N]
                        [--nofile N] [--merge] [--pty] [--cwd DIR] [--forward-env NAME ...] -- COMMAND...

It runs COMMAND in a new session and enforces, in the parent of the sandboxed process (which
cannot touch it):

  * a wall-clock limit (kill the whole process group; exit status 124, `SVGOLF_TIMEOUT` on stderr);
    the clock starts when the command does, so it excludes the wait in a slot wrapper in front of it;
  * with `--cpu-limit-s`, a limit on the CPU seconds (user + system, every thread) of the command's process
    tree: the live members of its process group, POLLED (every 0.1 s with a memory limit, else every 0.5 s;
    on Linux `/proc` adds the children each member has reaped), and at its end the resource usage of the
    whole tree the command waited for (`wait4`), so CPU spent in a short-lived child is counted when the
    command ends even where the poll cannot see it (macOS). Over the limit the group is killed: exit status
    124, `SVGOLF_TIMEOUT ... by=cpu`. The CPU limit does not count time spent waiting (a `sleep`, blocked
    I/O, a loaded machine), which only the wall-clock limit, then a backstop, bounds (`by=wall`). The
    command also gets RLIMIT_CPU at the limit plus CPU_RLIMIT_SLACK_S, so one process that outran the poll
    still dies (SIGXCPU, reported as `by=cpu`);
  * a resident-memory limit summed over the process group, POLLED (macOS cannot enforce RLIMIT_AS at all,
    and an address-space limit would break the mmap of Mathlib's oleans anyway; exit status 125,
    `SVGOLF_MEMORY`). Measured 2026-10-31: a Lean memory bomb allocates 1.2 GB in 0.6 s, so the
    poll is 0.1 s and the limit has headroom for one interval;
  * a cap on the bytes of output the checker will ever buffer (`capture_output=True` in the callers
    would otherwise let a flood to /dev/fd/1 exhaust the CHECKER; exit status 126, `SVGOLF_OUTPUT`);
  * RLIMIT_CPU, RLIMIT_FSIZE (a disk bomb is stopped by SIGXFSZ), RLIMIT_NOFILE, RLIMIT_CORE=0.

The command's stdout goes to this process's stdout (capped), its stderr to stderr, or into stdout with
`--merge`. With `--pty` the command's stdout (and, with `--merge`, its stderr) is the slave end of a fresh
pseudo-terminal in raw mode (no newline translation, no echo), whose master this process reads: a program that
buffers its output by C stdio's rule (fully when stdout is a pipe, by line when it is a terminal), Lean among
them, then writes each line as it ends, so output written before a kill is not lost in its buffer (measured
2026-11-05: with a pipe, the messages of a Lean compile stopped at its limit never arrive; with the pseudo-terminal
each arrives when Lean prints it, inside the Seatbelt profile too). The pseudo-terminal is not the command's
controlling terminal (it runs in a new session). When the command ends, one control line is printed on stderr:

    SVGOLF_ELAPSED <seconds> cpu_s=<cpu seconds> peak_rss_mb=<n> out_bytes=<n> verdict=<none|memory|output>

The genuine line is the LAST one (a command can print the same words earlier, which `split_status`
in check.py ignores); on a timeout

    SVGOLF_TIMEOUT after <wall seconds>s cpu_s=<cpu seconds> by=<wall|cpu>

is printed instead and the status is 124 (`by` names the limit that stopped it). Whatever the command left running in its
process group dies with it.
"""

import os
import resource
import signal
import subprocess
import sys
import threading
import time

POLL_S = 0.1
# how often the CPU of the process group is read when no memory limit makes the poll read it every POLL_S anyway
# (one `ps` of every process costs about 35 ms on the development machine)
CPU_POLL_S = 0.5
# RLIMIT_CPU is the CPU limit plus this (per process): the backstop of the poll, never the limit itself
CPU_RLIMIT_SLACK_S = 10
READ_CHUNK = 65536


def ps_time_s(text):
    """`ps`'s accumulated CPU time (`[dd-][hh:]mm:ss[.ss]`, macOS `122:08.37`, Linux `00:02:05`) in seconds."""
    days, _, rest = text.rpartition("-")
    parts = rest.split(":")
    secs = 0.0
    for p in parts:
        secs = secs * 60 + float(p)
    return secs + (int(days) * 86400 if days else 0)


def _proc_group_usage(pgid):
    """(resident KB, CPU seconds) of process group `pgid` from Linux's `/proc`: each member's own user + system time
    and that of the children it has reaped (`cutime`, `cstime`)."""
    tick = os.sysconf("SC_CLK_TCK")
    page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
    rss = cpu = 0
    for name in os.listdir("/proc"):
        if not name.isdigit():
            continue
        try:
            with open(f"/proc/{name}/stat") as fh:
                f = fh.read().rpartition(")")[2].split()
        except OSError:
            continue
        if len(f) > 21 and f[2] == str(pgid):
            cpu += sum(int(x) for x in f[11:15])
            rss += int(f[21]) * page_kb
    return rss, cpu / tick


def group_usage(pgid):
    """(resident set in KB, CPU seconds) summed over the live processes of process group `pgid`: `/proc` on Linux
    (`_proc_group_usage`), `ps` elsewhere (macOS: the members' own time; a reaped child's time is counted by the
    caller's `wait4` reading at the end). (0, 0.0) when neither can be read."""
    if os.path.isdir("/proc/self") and os.path.exists("/proc/self/stat"):
        try:
            return _proc_group_usage(pgid)
        except (OSError, ValueError):
            pass
    try:
        out = subprocess.run(["ps", "-axo", "pgid=,rss=,time="], capture_output=True, text=True,
                             timeout=5, env={"PATH": "/usr/bin:/bin"}).stdout
    except (OSError, subprocess.SubprocessError):
        return 0, 0.0
    rss, cpu = 0, 0.0
    for ln in out.splitlines():
        f = ln.split()
        if len(f) == 3 and f[0] == str(pgid) and f[1].isdigit():
            rss += int(f[1])
            try:
                cpu += ps_time_s(f[2])
            except ValueError:
                pass
    return rss, cpu


def group_rss_kb(pgid):
    """Resident set (KB) of the processes in process group `pgid` (ps works on macOS and Linux)."""
    return group_usage(pgid)[0]


def reap(p, block=False):
    """Wait for `p` (a Popen) with `wait4`: its resource usage, which covers every descendant the tree waited for, or
    None while it runs. Sets `p.returncode` as Popen would, so `p.poll()` and `p.wait()` stay valid."""
    if p.returncode is not None:
        return None
    try:
        pid, status, ru = os.wait4(p.pid, 0 if block else os.WNOHANG)
    except ChildProcessError:
        p.returncode = p.returncode if p.returncode is not None else 0
        return None
    if pid == 0:
        return None
    p.returncode = os.waitstatus_to_exitcode(status)
    return ru


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
    o = {"wall": float(argv[0]), "cpu_limit_s": 0.0, "rss_mb": 0.0, "out_mb": 0.0, "cpu_s": 0.0, "fsize_mb": 0.0,
         "nofile": 4096.0, "merge": False, "pty": False, "cwd": None, "forward_env": []}
    i = 1
    while i < len(argv) and argv[i] != "--":
        k = argv[i].lstrip("-").replace("-", "_")
        if k in ("merge", "pty"):
            o[k] = True
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
        cpu = int(o["cpu_s"]) if o["cpu_s"] else 0
        if o["cpu_limit_s"]:                # the poll's backstop, per process: never below the counted limit
            backup = int(o["cpu_limit_s"]) + CPU_RLIMIT_SLACK_S
            cpu = min(cpu, backup) if cpu else backup
        if cpu:
            resource.setrlimit(resource.RLIMIT_CPU, (cpu, cpu + 5))
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
    master = slave = None
    if o["pty"]:
        import pty
        import tty
        master, slave = pty.openpty()
        tty.setraw(slave)
    try:
        p = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=slave if o["pty"] else subprocess.PIPE,
                             cwd=o["cwd"], stderr=subprocess.STDOUT if o["merge"] else subprocess.PIPE,
                             start_new_session=True, preexec_fn=_limits(o))
    except OSError as e:
        print(f"SVGOLF_SPAWN_FAILED {e}", file=sys.stderr)
        return 127
    finally:
        if slave is not None:
            os.close(slave)               # the command holds it now: the master reads EOF (or EIO) when it is gone
    cap = int(o["out_mb"] * 1048576)
    state = {"bytes": 0, "over": False}
    lock = threading.Lock()

    def pump(src, dst):
        while True:
            try:
                b = os.read(src, READ_CHUNK)
            except OSError:               # a pseudo-terminal's master once every slave end is closed (EIO)
                b = b""
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
    threads = [threading.Thread(target=pump, args=(master if o["pty"] else p.stdout.fileno(), sys.stdout.buffer),
                                daemon=True)]
    if not o["merge"]:
        threads.append(threading.Thread(target=pump, args=(p.stderr.fileno(), sys.stderr.buffer), daemon=True))
    for t in threads:
        t.start()
    verdict, peak, cpu_seen, ru = None, 0, 0.0, None
    cpu_limit = o["cpu_limit_s"]
    next_cpu = t0
    while True:
        ru = reap(p)
        if p.returncode is not None:
            break
        time.sleep(POLL_S)
        if stopped or os.getppid() != parent:
            verdict = "abandoned"
            break
        now = time.time()
        if o["wall"] and now - t0 > o["wall"]:
            verdict = "timeout"
            break
        if o["rss_mb"] or (cpu_limit and now >= next_cpu):
            kb, cpu = group_usage(p.pid)
            next_cpu = now + CPU_POLL_S
            peak = max(peak, kb)
            cpu_seen = max(cpu_seen, cpu)
            if o["rss_mb"] and kb > o["rss_mb"] * 1024:
                verdict = "memory"
                break
            if cpu_limit and cpu_seen > cpu_limit:
                verdict = "cpu"
                break
        if state["over"]:
            verdict = "output"
            break
    try:
        os.killpg(p.pid, signal.SIGKILL)     # whatever the command left in its group dies with it
    except (ProcessLookupError, PermissionError):
        pass
    ru = reap(p, block=True) or ru
    p.wait()
    for t in threads:
        t.join(timeout=5)
    if master is not None:
        os.close(master)
    if state["over"]:
        verdict = verdict or "output"
    # the CPU seconds: the poll's last reading, or the tree's own usage at its end (every descendant it waited for)
    cpu = max(cpu_seen, (ru.ru_utime + ru.ru_stime) if ru else 0.0)
    if cpu_limit and verdict is None and (cpu > cpu_limit or p.returncode == -signal.SIGXCPU):
        verdict = "cpu"                      # over the limit between two polls, or stopped by the RLIMIT_CPU backstop
    sys.stdout.flush()
    sys.stderr.flush()
    el = time.time() - t0
    if verdict in ("timeout", "cpu"):
        print(f"SVGOLF_TIMEOUT after {el:.2f}s cpu_s={cpu:.2f} by={'cpu' if verdict == 'cpu' else 'wall'}",
              file=sys.stderr)
        return 124
    if verdict == "abandoned":
        print("SVGOLF_ABANDONED the checker went away or asked this run to stop", file=sys.stderr)
        return 143
    rc = p.returncode if p.returncode >= 0 else 128 - p.returncode
    if verdict == "memory":
        print(f"SVGOLF_MEMORY over {o['rss_mb']:.0f} MB (the process group reached {peak/1024:.0f} MB)",
              file=sys.stderr)
        rc = 125
    elif verdict == "output":
        print(f"SVGOLF_OUTPUT over {o['out_mb']:.0f} MB", file=sys.stderr)
        rc = 126
    print(f"SVGOLF_ELAPSED {el:.2f} cpu_s={cpu:.2f} peak_rss_mb={peak/1024:.0f} out_bytes={state['bytes']} "
          f"verdict={verdict or 'none'}", file=sys.stderr)
    return rc

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
