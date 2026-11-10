"""Specs and environments for the TOOLS that read submitted text: Yosys, Verilator and its make/C++ build,
the compiled model, `svgolf-eval`, the pinned extractor (Python + pyslang).

Each helper returns a `Spec` (spec.py). Call sites in score.py, banlist.py, fourstate.py, envelope.py and
postsynth.py are one line: `sandbox.run(cmd, sandbox.tool_spec(...), env=sandbox.tool_env(work), ...)`.
"""

import json
import os
import subprocess
import sys

from .envscrub import scrubbed_env
from .spec import Spec, real, tool_trees


def venv_configs(path=None):
    """The `pyvenv.cfg` of every virtual environment whose `bin` directory is on `path` (default: the
    scrubbed environment's PATH). A Python started from a venv reads that file before its first line
    (site.py), so where the sandbox denies it every Python a tool starts from PATH (the extractor's
    interpreter; `python3` in Verilator's generated makefile) dies with `init_import_site`. The file
    names the base interpreter and nothing else; the venv's other files stay unreadable."""
    if path is None:
        path = scrubbed_env().get("PATH", "")
    out = []
    for d in path.split(os.pathsep):
        cfg = os.path.join(os.path.dirname(d.rstrip(os.sep)), "pyvenv.cfg") if os.path.isabs(d) else None
        if cfg and os.path.isfile(cfg) and real(cfg) not in out:
            out.append(real(cfg))
    return out


def tool_spec(exes, read=(), write=(), label="tool", fork=True):
    """A build tool or a synthesis tool: it may execute inside the system and package trees (its own
    helpers: yosys-abc, perl, make, the C++ compiler, a `python3` from PATH), read those, `read` and the
    `pyvenv.cfg` of a venv on PATH (`venv_configs`), and write `write` only."""
    trees = tool_trees(*exes)
    return Spec(exec_subpaths=trees, read=trees + list(read) + venv_configs(), write=list(write), fork=fork,
                system="tools", label=label)


def exec_spec(exe, read=(), write=(), label="exec"):
    """ONE program that starts nothing (the compiled model, `svgolf-eval`): it may execute itself, read
    `read`, write `write`."""
    exe = real(exe)
    # (Seatbelt derives the executable's own directory for dyld from exec_paths; on Linux only the file is
    # mounted, so nothing else in its directory can run)
    return Spec(exec_paths=[exe], read=list(read), write=list(write), fork=False, system="libs", label=label)


def tool_env(work=None, extra=None):
    """The environment of a sandboxed tool: the allowlist, HOME and TMPDIR pointing into the work directory
    (Yosys's abc, Verilator's perl and the compilers write temporary files there), plus `extra`."""
    env = scrubbed_env()
    if work:
        tmp = os.path.join(work, "tmp")
        os.makedirs(tmp, exist_ok=True)
        env["HOME"] = work
        env["TMPDIR"] = tmp
    else:
        env["HOME"] = "/var/empty"
    env.update(extra or {})
    return env


_PY = {}


def python_probe(python):
    """(sys.base_prefix, [stdlib dirs], pyslang's site directory or None, [sys.prefix, sys.base_prefix,
    sys.exec_prefix]) of an interpreter, asked of the interpreter itself once. Trusted code, no submission in
    reach."""
    if python not in _PY:
        code = ("import json,sys,sysconfig,os\n"
                "try:\n import pyslang; site=os.path.dirname(os.path.dirname(pyslang.__file__))\n"
                "except Exception: site=None\n"
                "print(json.dumps([sys.base_prefix,[sysconfig.get_path('stdlib'),sysconfig.get_path('platstdlib')],site,"
                "[sys.prefix,sys.base_prefix,sys.exec_prefix]]))")
        out = subprocess.run([python, "-B", "-c", code], capture_output=True, text=True, timeout=60,
                             env=scrubbed_env()).stdout.strip().splitlines()
        _PY[python] = json.loads(out[-1]) if out else [sys.base_prefix, [], None, []]
    return _PY[python]


def python_spec(python, script_dir, read=(), write=(), label="python"):
    """(Spec, extra environment) for `python -s -B script ...`: the interpreter, its standard library and
    the directory pyslang lives in (reached through PYTHONPATH, so the user site of a HOME the sandbox
    does not give is not needed). The interpreter may READ its own prefixes, `sys.prefix`, `sys.base_prefix`
    and `sys.exec_prefix` (a venv's `pyvenv.cfg` is in its `sys.prefix`, which may be anywhere: a venv under
    a temporary directory failed at startup, "init_import_site", 2026-11-08), but not the root or `/usr` as a
    whole; it may EXECUTE only inside its base prefix, as before."""
    exe = real(subprocess.run(["which", python], capture_output=True, text=True,
                              env=scrubbed_env()).stdout.strip() or python)
    prefix, libs, site, prefixes = python_probe(python)
    prefix = real(prefix)
    private = prefix not in (os.sep, "/usr")
    reads = list(read) + [real(l) for l in libs if l] + [real(script_dir)] + ([prefix] if private else [])
    reads += [p for p in dict.fromkeys(real(x) for x in prefixes if x) if p not in (os.sep, "/usr") and p not in reads]
    if site:
        reads.append(real(site))
    # a venv interpreter (reached through PATH, or named by path in SVGOLF_PYTHON) reads its pyvenv.cfg
    reads += venv_configs() + (venv_configs(os.path.dirname(os.path.abspath(python))) if os.sep in python else [])
    if sys.platform == "darwin":       # Homebrew's libraries behind the interpreter's optional extension modules
        reads += [p for p in ("/opt/homebrew", "/usr/local/lib", "/usr/local/Cellar") if os.path.isdir(p)]
    spec = Spec(exec_paths=[exe], exec_subpaths=[prefix] if private else [], read=reads, write=list(write),
                fork=False, system="libs", label=label)
    return spec, ({"PYTHONPATH": site} if site else {})
