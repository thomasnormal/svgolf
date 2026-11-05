"""The self-test: does the mechanism, on THIS machine, deny what it must?

A sandbox that is not there is worse than none (the checker would say "sandboxed"), so `auto` and
`require` start by running a canary: a small Python program, under a Spec like a Lean run's, that

  reads a file inside the allowed tree           must succeed   (a sandbox that denies everything is useless)
  writes a file inside the output tree           must succeed
  reads a file the TEST created outside it       must be denied
  lists a directory outside it                   must be denied
  writes a file outside it                       must not reach the host (denied, or lost in a private tmpfs)
  connects to a loopback listener the TEST runs  must be denied (and the listener must see nothing)
  starts /bin/sh                                 must be denied
  sees an SVGOLF_* variable                      must not (the environment is the one it was given)

Everything it touches the test created itself: no real host secret is in reach, so a mechanism that
does NOT work (a nested sandbox, user namespaces switched off, a profile Apple changed) costs nothing.
Result: (ok, detail). Takes about 0.2 s.
"""

import json
import os
import shutil
import socket
import subprocess
import sys
import sysconfig
import tempfile
import time

from .spec import Spec

PROBE = r'''
import json, os, socket, subprocess, sys
A, S, SD, OUTSIDE, INSIDE, PORT = sys.argv[1:7]
r = {}
def t(name, f):
    try:
        f(); r[name] = "ok"
    except BaseException as e:
        r[name] = "denied:" + type(e).__name__
t("read_allowed", lambda: open(A).read())
t("write_inside", lambda: open(INSIDE, "w").write("x"))
t("read_secret", lambda: open(S).read())
t("list_secret_dir", lambda: os.listdir(SD))
t("write_outside", lambda: open(OUTSIDE, "w").write("x"))
def tcp():
    c = socket.create_connection(("127.0.0.1", int(PORT)), 3); c.send(b"canary"); c.close()
t("tcp_connect", tcp)
def spawn():
    subprocess.run(["/bin/sh", "-c", "true"], check=True, timeout=5)
t("spawn_sh", spawn)
r["env_secret_visible"] = any(k.startswith("SVGOLF_") for k in os.environ)
print(json.dumps(r))
'''
EXPECT_OK = ("read_allowed", "write_inside")
# `write_outside` is judged on the HOST (the file must not exist afterwards): bubblewrap lets the call succeed
# into its private tmpfs, Seatbelt denies it
EXPECT_DENIED = ("read_secret", "list_secret_dir", "tcp_connect", "spawn_sh")


def run(policy_command, scratch, timeout=30):
    """Run the canary through `policy_command(spec, cmd, env, scratch, cwd)` -> (argv, tag).
    Returns (ok, detail dict)."""
    t0 = time.time()
    root = tempfile.mkdtemp(prefix="canary-", dir=scratch)
    try:
        allowed = os.path.join(root, "allowed")
        out = os.path.join(root, "out")
        secret_dir = os.path.join(root, "secret")
        for d in (allowed, out, secret_dir):
            os.makedirs(d)
        a = os.path.join(allowed, "readable.txt")
        s = os.path.join(secret_dir, "secret.txt")
        outside = os.path.join(root, "written-outside.txt")
        inside = os.path.join(out, "written-inside.txt")
        for p, text in ((a, "allowed\n"), (s, "this file is outside the sandbox's reach\n")):
            with open(p, "w") as fh:
                fh.write(text)
        py = os.path.realpath(sys.executable)
        prefix = os.path.realpath(sys.base_prefix)
        # a framework build (macOS, Homebrew) re-executes its real binary inside the prefix; a system
        # Python (/usr) is NOT mounted whole, or /bin/sh would come with it and the canary could not tell
        private = prefix not in (os.sep, "/usr")
        libs = {os.path.realpath(sysconfig.get_path(k)) for k in ("stdlib", "platstdlib")}
        spec = Spec(exec_paths=[py], exec_subpaths=[prefix] if private else [],
                    read=[allowed] + sorted(libs) + ([prefix] if private else []), write=[out], label="canary")
        lsock = socket.socket()
        lsock.bind(("127.0.0.1", 0))
        lsock.listen(4)
        lsock.settimeout(0.3)
        port = lsock.getsockname()[1]
        env = {"PATH": "/usr/bin:/bin", "HOME": "/nonexistent", "LC_ALL": "C"}   # no SVGOLF_ variable is given
        argv, tag = policy_command(spec, [py, "-I", "-S", "-B", "-c", PROBE, a, s, secret_dir, outside,
                                          inside, str(port)], env, scratch, None)
        try:
            proc = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                                  env={"PATH": "/usr/bin:/bin", "SVGOLF_CANARY": "outer"},
                                  stdin=subprocess.DEVNULL, cwd=allowed)
        except (OSError, subprocess.SubprocessError) as e:
            return False, {"error": f"the canary could not run: {e}", "seconds": round(time.time() - t0, 2)}
        accepted = 0
        try:
            while True:
                c, _ = lsock.accept()
                accepted += 1
                c.close()
        except (socket.timeout, OSError):
            pass
        lsock.close()
        try:
            r = json.loads(proc.stdout.strip().splitlines()[-1])
        except (ValueError, IndexError):
            return False, {"error": "the canary printed no result (the mechanism refused to start it?): "
                           + (proc.stderr or proc.stdout).strip()[-300:], "exit": proc.returncode,
                           "seconds": round(time.time() - t0, 2)}
        bad = [k for k in EXPECT_OK if r.get(k) != "ok"]
        bad += [k for k in EXPECT_DENIED if not str(r.get(k, "")).startswith("denied")]
        if accepted:
            bad.append("listener_saw_a_connection")
        if os.path.exists(outside):
            bad.append("file_written_outside_exists")
        if r.get("env_secret_visible"):
            bad.append("env_secret_visible")
        detail = {"results": r, "wrong": bad, "seconds": round(time.time() - t0, 2), "profile": tag}
        return not bad, detail
    finally:
        shutil.rmtree(root, ignore_errors=True)
