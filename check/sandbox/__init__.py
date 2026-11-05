"""svGolf checker sandbox (WP-S): everything that runs submitted text runs through here.

    envscrub     `scrubbed_env()`: the allowlisted environment of every child process
    spec         `Spec`: what one process may read, write and execute (nothing by default)
    seatbelt     macOS: a Seatbelt profile generated from a Spec
    bwrap        Linux: a bubblewrap argument vector generated from a Spec
    selftest     the canary that decides whether the mechanism works on this machine
    tools        the Specs and environments of Yosys, Verilator and make, the model, svgolf-eval, the extractor
    supervisor   wall-clock, memory and output limits, enforced from outside the sandbox
    policy       `configure(mode)`, `policy()`, `run(...)`

README.md, "Checker v0 limits" (the sandbox row) and "Sandbox".
"""

import os

from . import supervisor  # noqa: F401
from .envscrub import scrubbed_env  # noqa: F401
from .core import (MODES, Completed, Policy, Unavailable, configure, limits, policy, run,  # noqa: F401
                     SUPERVISOR)
from .spec import Spec, real, tool_trees  # noqa: F401
from .tools import exec_spec, python_spec, tool_env, tool_spec  # noqa: F401

HERE = os.path.dirname(os.path.abspath(__file__))


def trusted_files():
    """Every file of this package (code and generated-text templates), for check.py's integrity
    tripwire: the sandbox is part of the trusted base, fingerprinted by content like postsynth.py."""
    return sorted(os.path.join(HERE, f) for f in os.listdir(HERE)
                  if f.endswith((".py", ".in", ".sb", ".json")))
