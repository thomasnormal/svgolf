#!/usr/bin/env python3
"""check/layout.py and its users in both of svGolf's layouts, on synthetic trees (no Lean, no Yosys).

    python3.12 tests/checker/test_layout.py

  * inside: svgolf/ in a lean-surfaces checkout: lean-surfaces is the parent, the packages and
    the manifest are the parent's;
  * standalone: svGolf as its own repository with lean-surfaces as the Lake dependency
    `lean-models`: lean-surfaces is `.lake/packages/lean-models`, the packages and the manifest
    are svGolf's own;
  * SVGOLF_LS_ROOT and SVGOLF_PACKAGES override, and inside, the packages follow an overridden
    lean-surfaces root (as before the layouts existed);
  * this checkout's own layout is what the directory says;
  * the site generator (site/build.py) reads `svgolf/...` repository paths from svGolf's tree
    and the rest from lean-surfaces', links them by layout, and shows the right clone commands.
"""
import html
import importlib.util
import os
import re
import shutil
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


layout = load("svgolf_layout_t", os.path.join(SVGOLF, "check", "layout.py"))
sys.path.insert(0, os.path.join(SVGOLF, "site"))
build = load("svgolf_site_build_t", os.path.join(SVGOLF, "site", "build.py"))


def touch(path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").close()


def lean_surfaces_tree(root):
    """The two things that make a directory a lean-surfaces checkout."""
    os.makedirs(os.path.join(root, "LeanModels", "Sv"), exist_ok=True)
    touch(os.path.join(root, "extractors", "sv", "extract.py"))


class Detect(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp(prefix="svgolf-layout-")
        self.addCleanup(shutil.rmtree, self.tmp)

    def test_inside(self):
        ls = os.path.join(self.tmp, "ls")
        lean_surfaces_tree(ls)
        sg = os.path.join(ls, "svgolf")
        os.makedirs(sg)
        got = layout.detect(sg, environ={})
        self.assertEqual(got, {"layout": "inside", "ls_root": ls,
                               "packages": os.path.join(ls, ".lake", "packages"),
                               "manifest": os.path.join(ls, "lake-manifest.json")})

    def test_standalone(self):
        sg = os.path.join(self.tmp, "svgolf")
        dep = os.path.join(sg, ".lake", "packages", "lean-models")
        lean_surfaces_tree(dep)
        got = layout.detect(sg, environ={})
        self.assertEqual(got, {"layout": "standalone", "ls_root": dep,
                               "packages": os.path.join(sg, ".lake", "packages"),
                               "manifest": os.path.join(sg, "lake-manifest.json")})

    def test_standalone_before_the_dependency_is_fetched(self):
        # the layout is a property of the parent directory, not of `.lake/` (which may not exist yet)
        sg = os.path.join(self.tmp, "svgolf")
        os.makedirs(sg)
        self.assertEqual(layout.detect(sg, environ={})["layout"], "standalone")

    def test_a_parent_without_ls_sv_is_not_lean_surfaces(self):
        sg = os.path.join(self.tmp, "parent", "svgolf")
        os.makedirs(os.path.join(self.tmp, "parent", "LeanModels"))   # no Sv/, no extractor
        os.makedirs(sg)
        self.assertEqual(layout.detect(sg, environ={})["layout"], "standalone")

    def test_overrides(self):
        ls = os.path.join(self.tmp, "ls")
        lean_surfaces_tree(ls)
        sg = os.path.join(ls, "svgolf")
        os.makedirs(sg)
        other = os.path.join(self.tmp, "other")
        got = layout.detect(sg, environ={"SVGOLF_LS_ROOT": other})
        # inside, the packages and the manifest follow the overridden root
        self.assertEqual((got["layout"], got["ls_root"], got["packages"], got["manifest"]),
                         ("inside", other, os.path.join(other, ".lake", "packages"),
                          os.path.join(other, "lake-manifest.json")))
        got = layout.detect(sg, environ={"SVGOLF_PACKAGES": os.path.join(self.tmp, "pk")})
        self.assertEqual((got["ls_root"], got["packages"]), (ls, os.path.join(self.tmp, "pk")))
        alone = os.path.join(self.tmp, "alone")
        os.makedirs(alone)
        got = layout.detect(alone, environ={"SVGOLF_LS_ROOT": other})
        self.assertEqual((got["layout"], got["ls_root"], got["packages"]),
                         ("standalone", other, os.path.join(alone, ".lake", "packages")))

    def test_this_checkout(self):
        want = "inside" if layout.is_lean_surfaces(os.path.dirname(SVGOLF)) else "standalone"
        self.assertEqual(layout.LAYOUT, want)
        self.assertEqual(layout.SVGOLF, SVGOLF)
        if not os.environ.get("SVGOLF_LS_ROOT"):
            self.assertTrue(layout.is_lean_surfaces(layout.LS_ROOT) or want == "standalone",
                            layout.LS_ROOT)


class Site(unittest.TestCase):
    """site/build.py's two roots, its links and its clone commands, in both layouts."""

    def test_repo_file(self):
        with mock.patch.object(build, "SVGOLF", "/sg"), mock.patch.object(build, "LS_ROOT", "/ls"):
            self.assertEqual(build.repo_file("svgolf/README.md"), "/sg/README.md")
            self.assertEqual(build.repo_file("svgolf/tasks/add/Spec.lean"), "/sg/tasks/add/Spec.lean")
            self.assertEqual(build.repo_file("docs/sv-refusals.json"), "/ls/docs/sv-refusals.json")
            self.assertEqual(build.repo_file("LeanModels/Sv/Ast.lean"), "/ls/LeanModels/Sv/Ast.lean")
            self.assertEqual(build.repo_file("svgolfx/a"), "/ls/svgolfx/a")     # a prefix, not a path

    def test_repo_link(self):
        url = "https://example.org/o/svgolf"
        with mock.patch.object(build, "LAYOUT", "inside"):
            self.assertEqual(build.repo_link(url, "svgolf/README.md"), url + "/svgolf/README.md")
            self.assertIsNone(build.repo_link(None, "svgolf/README.md"))
        with mock.patch.object(build, "LAYOUT", "standalone"):
            self.assertEqual(build.repo_link(url, "svgolf/score/PPA.md"), url + "/blob/HEAD/score/PPA.md")
            self.assertIsNone(build.repo_link(url, "docs/sv-refusals.json"))
            self.assertIsNone(build.repo_link(None, "svgolf/README.md"))

    def test_clone_commands(self):
        t = build.Task.__new__(build.Task)
        t.name = "add"
        url = "https://example.org/o/svgolf"
        text = lambda h: html.unescape(re.sub(r"<[^>]+>", "", h))     # noqa: E731  (the highlighted code as text)
        with mock.patch.object(build, "LAYOUT", "inside"):
            self.assertIn("cd svgolf/svgolf\n", text(build.submit_html(t, url)))
        with mock.patch.object(build, "LAYOUT", "standalone"):
            out = text(build.submit_html(t, url))
            self.assertIn("git clone " + url, out)
            self.assertNotIn("cd svgolf/svgolf", out)
            self.assertIn("cd svgolf\n", out)


if __name__ == "__main__":
    unittest.main()
