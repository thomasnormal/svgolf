"""The sandbox policy: which mechanism, whether it works here, and `run`.

    pol = configure("auto")        # once, in check.py's main: detect, self-test, say so on stderr
    pol.command(spec, cmd, env)    # the argument vector that runs `cmd` under the Spec
    run(cmd, spec, ...)            # a subprocess.run that goes through all of it

Modes: `off` (no sandbox; the environment is still scrubbed), `auto` (use it when the mechanism exists and
passes the self-test, else say so and run without), `require` (an infrastructure error when it is not
there: competitions, `leaderboard.py add`/`verify`). Before `configure` the policy is `off`, so a unit
test or a library caller that never configures one sees exactly the old behaviour.
"""

import atexit
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile

from . import bwrap, seatbelt, selftest
from .envscrub import scrubbed_env

MODES = ("off", "auto", "require")
SUPERVISOR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "supervisor.py")
ELAPSED = re.compile(r"^SVGOLF_ELAPSED ([\d.]+)([^\n]*)\n?", re.M)


class Unavailable(RuntimeError):
    """`--sandbox require` and the mechanism is missing or failed its self-test."""


def physical_mb():
    try:
        return os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // (1 << 20)
    except (ValueError, OSError, AttributeError):
        return 8192


def env_int(name, default):
    try:
        return int(os.environ[name])
    except (KeyError, ValueError):
        return default


def limits(wall, kind="lean"):
    """The supervisor's limits for one process (module docstring of supervisor.py). Overridable:
    SVGOLF_SANDBOX_RSS_MB, _OUT_MB, _FSIZE_MB. Generous: the largest legitimate run (Mathlib.Tactic) peaks at
    3 to 5 GB; the limits stop a bomb, not a big proof."""
    rss = env_int("SVGOLF_SANDBOX_RSS_MB", max(2048, min(12288, int(physical_mb() * 0.6))))
    out = env_int("SVGOLF_SANDBOX_OUT_MB", 16 if kind == "lean" else 64)
    fsize = env_int("SVGOLF_SANDBOX_FSIZE_MB", 2048 if kind == "lean" else 4096)
    cpu = int(wall * max(2, os.cpu_count() or 2) + 60) if wall else 0
    return {"wall_s": wall, "rss_mb": rss, "out_mb": out, "fsize_mb": fsize, "cpu_s": cpu}


class Policy:
    def __init__(self, mode="off"):
        self.mode = mode
        self.mechanism = None
        self.active = False
        self.reason = None
        self.selftest = None
        self.scratch = None
        self.debug = bool(os.environ.get("SVGOLF_SANDBOX_DEBUG"))
        self.reset_note()

    # ---- what ran sandboxed (the result's `stages.sandbox`)
    def reset_note(self):
        self.note = {"sandboxed": {}, "unsandboxed": [], "profiles": {}, "stray_outputs": []}

    def sandboxed(self, label, tag):
        self.note["sandboxed"][label] = self.note["sandboxed"].get(label, 0) + 1
        self.note["profiles"].setdefault(label, set()).add(tag)

    def unsandboxed(self, what):
        if what not in self.note["unsandboxed"]:
            self.note["unsandboxed"].append(what)

    def report(self):
        """The result key `sandbox` (and the head of `stages.sandbox`)."""
        r = {"mode": self.mode, "mechanism": self.mechanism if self.active else None, "active": self.active}
        if self.mode != "off" and not self.active:
            r["reason"] = self.reason
        return r

    def stage_note(self):
        """`stages.sandbox`: LIVE (it fills as the stages run)."""
        n = dict(self.report())
        if self.selftest:
            n["self_test"] = {"ok": self.active, "seconds": self.selftest.get("seconds"),
                              "wrong": self.selftest.get("wrong")}
        n["sandboxed"] = self.note["sandboxed"]
        n["profiles"] = {k: sorted(v) for k, v in self.note["profiles"].items()}
        n["unsandboxed"] = self.note["unsandboxed"]
        n["peak_rss_mb"] = self.note.get("peak_rss_mb")
        n["stray_outputs"] = self.note["stray_outputs"]
        return n

    # ---- commands
    def _mod(self):
        return seatbelt if self.mechanism == "seatbelt" else bwrap

    def raw_command(self, spec, cmd, env, scratch, cwd):
        return self._mod().command(spec, cmd, env, scratch, cwd, self.debug)

    def command(self, spec, cmd, env, cwd=None, label=None):
        argv, tag = self.raw_command(spec, cmd, env, self.scratch, cwd)
        self.sandboxed(label or spec.label or "process", tag)
        return argv

    def mkdtemp(self, prefix):
        """A fresh directory inside the scratch area (outside the stage; removed at the end)."""
        return tempfile.mkdtemp(prefix=prefix, dir=self.scratch)

    def close(self):
        if self.scratch:
            shutil.rmtree(self.scratch, ignore_errors=True)
            self.scratch = None


_POLICY = Policy("off")


def policy():
    return _POLICY


def configure(mode="auto", log=None):
    """Detect the mechanism and self-test it; install and return the policy. `require` raises
    `Unavailable`; `auto` degrades to no sandbox and says so through `log`."""
    global _POLICY
    if mode not in MODES:
        raise ValueError(f"sandbox mode {mode!r} is not one of {MODES}")
    log = log or (lambda *a: print(*a, file=sys.stderr, flush=True))
    if _POLICY.scratch:
        _POLICY.close()
    pol = Policy(mode)
    if mode != "off":
        if sys.platform == "darwin" and seatbelt.available():
            pol.mechanism = "seatbelt"
        elif sys.platform.startswith("linux") and bwrap.available():
            pol.mechanism = "bwrap"
        if pol.mechanism is None:
            pol.reason = ("no sandbox mechanism on this machine (macOS needs /usr/bin/sandbox-exec, "
                          "Linux needs bubblewrap: `bwrap`)")
        else:
            pol.scratch = tempfile.mkdtemp(prefix="svgolf-sandbox-")
            atexit.register(pol.close)
            ok, detail = selftest.run(pol.raw_command, pol.scratch)
            pol.selftest = detail
            if ok:
                pol.active = True
            else:
                pol.reason = (f"the {pol.mechanism} self-test failed: "
                              + (detail.get("error") or f"wrong: {detail.get('wrong')}, results {detail.get('results')}"))
        if pol.active:
            log(f"sandbox: {pol.mechanism}, self-test passed [{pol.selftest['seconds']} s]: every process that "
                "runs submitted text (Lean, the extractor, Yosys, Verilator, the model) has no network, no "
                "reads outside its inputs, no writes outside its output directory, no new programs")
        else:
            if mode == "require":
                pol.close()
                raise Unavailable(f"--sandbox require: {pol.reason}")
            log(f"sandbox: NOT ACTIVE ({pol.reason}). The submission's Lean runs with the checker's privileges; "
                "use --sandbox require for official runs")
    _POLICY = pol
    return pol


class Completed(subprocess.CompletedProcess):
    """A `subprocess.CompletedProcess` plus what the supervisor measured."""
    elapsed = None
    verdict = None


def _run_group(cmd, env, cwd, timeout, input_text):
    """`subprocess.run(cmd, capture_output=True, text=True, ...)`, except that a timeout kills the command's whole
    process group. `subprocess.run` kills only the direct child, so a `yosys` timeout left its `yosys-abc` running."""
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         stdin=None if input_text is None else subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(input=input_text, timeout=timeout)
    except BaseException:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        p.communicate()
        raise
    return subprocess.CompletedProcess(cmd, p.returncode, out, err)


def run(cmd, spec, *, env=None, cwd=None, timeout=None, kind="tool", label=None, input_text=None):
    """`subprocess.run(cmd, capture_output=True, text=True, timeout=..., env=...)` for a process that touches
    submitted text. Without an active sandbox that is exactly what it is, with the scrubbed environment.
    With one the command runs under `spec` and under the supervisor (wall, memory, output, file-size limits);
    a timeout raises `subprocess.TimeoutExpired` as before, and a memory or output kill is an ordinary failure
    (returncode 125 or 126, the reason on stderr)."""
    pol = policy()
    if not pol.active:
        return _run_group(cmd, env if env is not None else scrubbed_env(), cwd, timeout, input_text)
    child_env = env if env is not None else scrubbed_env()
    argv = pol.command(spec, cmd, child_env, cwd, label)
    lim = limits(timeout, kind)
    sup = [sys.executable, "-S", "-B", SUPERVISOR, str(lim["wall_s"] or 0), "--rss-mb", str(lim["rss_mb"]),
           "--out-mb", str(lim["out_mb"]), "--fsize-mb", str(lim["fsize_mb"]), "--cpu-s", str(lim["cpu_s"])]
    if cwd:
        sup += ["--cwd", cwd]
    sup += ["--"] + argv
    p = subprocess.run(sup, capture_output=True, text=True, errors="replace", env=scrubbed_env(),
                       stdin=subprocess.DEVNULL if input_text is None else None, input=input_text)
    if p.returncode == 124 and "SVGOLF_TIMEOUT" in p.stderr:
        raise subprocess.TimeoutExpired(cmd, timeout or 0, output=p.stdout, stderr=p.stderr)
    # the supervisor's closing line is not the tool's output (the LAST such line is the genuine one)
    lines = [m for m in ELAPSED.finditer(p.stderr)]
    stderr = ELAPSED.sub("", p.stderr)
    out = Completed(cmd, p.returncode, p.stdout, stderr)
    if lines:
        out.elapsed = float(lines[-1].group(1))
        peak = re.search(r"peak_rss_mb=(\d+)", lines[-1].group(2))
        if peak:
            pol.note["peak_rss_mb"] = max(pol.note.get("peak_rss_mb", 0), int(peak.group(1)))
    return out
