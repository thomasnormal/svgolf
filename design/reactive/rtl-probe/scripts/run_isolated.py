"""Run a trusted tool script (the svGolf gate, the ls-sv extractor, ppa.py) under `python3.12 -I`.

-I keeps the current directory and the user site out of sys.path; this shim puts back exactly the
tool's own directory (the tools import their siblings) and nothing else, then runs the tool as
__main__. Downloaded RTL is only ever an ARGUMENT (data), never on sys.path or the cwd.

usage: python3.12 -I run_isolated.py TOOL.py [tool args...]
"""
import os
import runpy
import sys

tool = os.path.abspath(sys.argv[1])
# pyslang 11 lives in the user site, which -I drops: put back that one directory (trusted install)
USER_SITE = os.path.expanduser("~/Library/Python/3.12/lib/python/site-packages")
sys.path.append(USER_SITE)
sys.path.insert(0, os.path.dirname(tool))
sys.argv = [tool] + sys.argv[2:]
runpy.run_path(tool, run_name="__main__")
