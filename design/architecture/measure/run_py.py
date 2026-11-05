#!/usr/bin/env python3.12
"""Run a repository Python script in isolated mode with pyslang available.

    python3.12 -I run_py.py SCRIPT.py [args...]

`-I` keeps PYTHONPATH, the current directory and the user site off sys.path, which is what parsing untrusted
SystemVerilog requires. This wrapper adds back exactly two directories: the user site (where pyslang is installed,
slang_env.pyslang) and SCRIPT's own directory (its sibling modules), then runs SCRIPT as `__main__`.
"""
import os
import runpy
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402

slang_env.pyslang()
if len(sys.argv) < 2:
    sys.exit(__doc__)
script = os.path.abspath(sys.argv[1])
sys.path.insert(0, os.path.dirname(script))
sys.argv = [script] + sys.argv[2:]
runpy.run_path(script, run_name="__main__")
