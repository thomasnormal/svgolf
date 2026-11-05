#!/usr/bin/env python3.12
"""Run the repository's SV extractor (extractors/sv/extract.py) in isolated mode.

    python3.12 -I run_extract.py --repo REPO_ROOT -- <extract.py arguments>

`python3.12 -I` drops PYTHONPATH, the user site and the script directory from sys.path, which is what reading
untrusted sources requires; it also hides pyslang (a user-site install) and the extractor's sibling modules. This
wrapper puts back exactly those two directories, then runs extract.py's `__main__` with the given arguments. Nothing
from the source tree being extracted is ever put on sys.path.
"""
import os
import runpy
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import slang_env  # noqa: E402

slang_env.pyslang()
argv = sys.argv[1:]
if argv[:1] != ["--repo"] or "--" not in argv:
    sys.exit(__doc__)
repo = argv[1]
rest = argv[argv.index("--") + 1:]
ext = os.path.join(os.path.abspath(repo), "extractors", "sv")
sys.path.insert(0, ext)
sys.argv = [os.path.join(ext, "extract.py")] + rest
runpy.run_path(os.path.join(ext, "extract.py"), run_name="__main__")
