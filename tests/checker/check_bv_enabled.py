#!/usr/bin/env python3.12
"""check.py with the DORMANT bv_decide support switched on, for the groundwork tests only (WP-BV, G3).

    python3.12 tests/checker/check_bv_enabled.py TASK_DIR DESIGN.sv SOLUTION.lean [check.py options]

bv_decide is not supported by the checker (decided 2026-11-01): `check.py`'s `BV_DECIDE_SUPPORTED` is False, and
nothing outside that file turns it on: no environment variable, option or task key reads it. This wrapper loads
`check.py` as a module, sets the constant in ITS OWN PROCESS and runs `main()`, so the code that the constant
guards (the comparator's re-verification of the generated axiom, the sandbox grant of `cadical`, `fork` and a
private TMPDIR) can still be exercised end to end: `tests/run.py`'s `bv_decide_groundwork_*` attack rows and the
`host_cadical` / `host_spawn_bomb` groundwork rows of its `sandbox` step. A contestant runs `check.py`, never this.
"""

import importlib.util
import os
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
CHECK = os.path.join(SVGOLF, "check.py")


def load():
    spec = importlib.util.spec_from_file_location("svgolf_check_bv_enabled", CHECK)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


if __name__ == "__main__":
    check = load()
    assert check.BV_DECIDE_SUPPORTED is False        # the shipped value: this wrapper is the only thing that changes it
    check.BV_DECIDE_SUPPORTED = True
    sys.argv[0] = CHECK
    sys.exit(check.main())
