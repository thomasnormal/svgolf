"""The environment of every process that touches submitted text (WP-S, gate 1).

The checker's own environment holds secrets the submission must never see: the
competition salt `SVGOLF_POSTSYNTH_SALT` (the seed of the post-synthesis random
vectors: with it a player precomputes the exact vectors and special-cases a design
that passes them), tokens, credentials, an ssh-agent socket path. A Lean file reads
all of it (`IO.getEnv`, `Std.Internal.UV.System.osEnviron`); measured 2026-10-31
(WP-S gate 0): the unscrubbed `#eval` returned the salt.

So a child process gets an ALLOWLIST, never `os.environ`: `scrubbed_env()`. The
list is what the tools need to run (PATH and the toolchain locations, the locale,
Python's import variables for the extractor) and nothing else; every `SVGOLF_*`
variable is checker configuration, read in-process, and no child needs one.
"""

import fnmatch
import os

# exact names
ALLOW_EXACT = frozenset({
    "PATH", "HOME", "USER", "LOGNAME", "SHELL", "TERM", "TZ", "LANG", "TMPDIR",
    # Python (the extractor): where to find pyslang; never PYTHONSTARTUP
    "PYTHONPATH", "PYTHONHOME", "PYTHONUSERBASE", "PYTHONNOUSERSITE", "PYTHONUTF8",
    "PYTHONIOENCODING", "PYTHONDONTWRITEBYTECODE", "VIRTUAL_ENV",
    # C/C++ toolchains (Verilator's make): macOS finds the SDK and the developer dir through these
    "SDKROOT", "DEVELOPER_DIR", "CXX", "CC",
    # Verilator's runtime
    "VERILATOR_ROOT",
})
# name prefixes: the locale; elan/Lake/Lean's own settings (LEAN_PATH, LEAN_SYSROOT,
# LEAN_NUM_THREADS ... ; the slot wrapper sets LEAN_NUM_THREADS)
ALLOW_PREFIX = ("LC_", "LEAN_", "LAKE_", "ELAN_")
# never, whatever a prefix says
DENY_GLOB = ("*TOKEN*", "*SECRET*", "*PASSWORD*", "*CREDENTIAL*", "*SALT*", "*_KEY", "*APIKEY*",
             "SVGOLF_*", "SSH_*", "AWS_*", "GITHUB_*", "GH_*", "ANTHROPIC_*", "CLAUDE*")


def _allowed(name):
    if any(fnmatch.fnmatchcase(name.upper(), g) for g in DENY_GLOB):
        return False
    return name in ALLOW_EXACT or name.startswith(ALLOW_PREFIX)


def scrubbed_env(extra=None, base=None, **overrides):
    """A fresh environment dict: the allowlisted variables of `base` (default
    `os.environ`), then `extra` (a dict, applied as given: the caller's own, trusted
    additions such as LEAN_PATH), then `overrides` as keywords. Values of `extra`
    that are None remove the variable."""
    src = os.environ if base is None else base
    env = {k: v for k, v in src.items() if _allowed(k)}
    for k, v in list((extra or {}).items()) + list(overrides.items()):
        if v is None:
            env.pop(k, None)
        else:
            env[k] = v
    return env
