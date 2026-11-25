"""The build ratings use (decided 2026-11-05; since 2026-11-24 the WebAssembly Yosys, score/yosys_wasm.py):
score/reference_build.json is the data, the README's "Scoring" states it, and the site reads it (the rules page's
section, every task's score card, Step 0's check). No site build: the README, the data files and site/build.py's
functions.

    python3 -m unittest discover -s svgolf/tests/site      (from the lean-surfaces root)
"""

import hashlib
import importlib.util
import json
import os
import re
import sys
import types
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")


def load_build():
    sys.path.insert(0, SITE)
    spec = importlib.util.spec_from_file_location("svgolf_site_build_rating", os.path.join(SITE, "build.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def text(rel):
    with open(os.path.join(SVGOLF, *rel.split("/")), encoding="utf-8") as fh:
        return fh.read()


def sha256(rel):
    with open(os.path.join(SVGOLF, *rel.split("/")), "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def section(doc, title):
    """The `## title` section of a Markdown document."""
    m = re.search(r"^## " + re.escape(title) + r"\n(.*?)(?=^## |\Z)", doc, re.S | re.M)
    return m.group(1) if m else ""


def flat(s):
    return " ".join(s.split())


class RatingBuild(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rb = json.loads(text("score/reference_build.json"))
        cls.pins = json.loads(text("score/ppa_pins.json"))
        cls.flow = json.loads(text("tests/expected.json"))["flow"]
        cls.scoring = flat(section(text("README.md"), "Scoring"))
        sys.path.insert(0, os.path.join(SVGOLF, "score"))
        import yosys_wasm
        cls.launcher = yosys_wasm

    def test_the_data_is_the_pinned_flow_and_the_launchers_pin(self):
        """The rating build's Yosys is the version the flow pins, and the data names the module the launcher checks,
        with the package versions it requires and requirements.txt installs."""
        y, w = self.rb["yosys"], self.launcher.PIN
        self.assertEqual(y["version_line"], self.flow["yosys_version"])
        self.assertEqual(y["version_line"], w["version_line"])
        self.assertTrue(y["git_sha1"].startswith(w["version_line"].split("git sha1 ")[1].split(",")[0]))
        self.assertTrue(y["version_line"].startswith(f"Yosys {y['version']} "))
        self.assertEqual(y["sha256"], w["wasm_sha256"])
        self.assertEqual(self.rb["abc"]["sha256"], w["wasm_sha256"])      # ABC is linked into the same module
        self.assertEqual(y["package"], w["package"])
        self.assertEqual(sorted(y["runtime"] + [y["package"]]), sorted(f"{k}=={v}" for k, v in w["packages"].items()))
        req = text("requirements.txt")
        for k, v in w["packages"].items():
            self.assertIn(f"\n{k}=={v}\n", req)
        self.assertEqual(y["launcher"], "score/yosys_wasm.py")
        self.assertEqual(y["self_check"], "python3.12 score/yosys_wasm.py --self-check")
        # the module's memory ceiling, as leaderboard/sizes.py names it when a size stops there
        sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
        import sizes
        self.assertEqual(y["memory_ceiling_gib"], sizes.WASM_MEMORY_GIB)

    def test_the_readme_states_the_build_and_every_hash(self):
        y, d, prev = self.rb["yosys"], self.rb["determinism"], self.rb["previous"]
        o = d["other_build"]
        want = [y["git_sha1"], y["sha256"], flat(y["version_line"]), y["package"], *y["runtime"], y["self_check"],
                self.pins["liberty"]["sha256"], sha256("score/ppa.py"), sha256("score/ppa_pins.json"),
                self.flow["canon_script_sha256"], self.flow["script_sha256"], "score/reference_build.json",
                f"{o['designs_differing']} of them", f"{o['max_score_change_pct']:g}%",
                flat(prev["version_line"]), prev["sha256"], prev["abc_sha256"], "tests/checker/test_yosys_wasm.py",
                f"at most {y['memory_ceiling_gib']} GiB of memory"]
        for w in want:
            self.assertIn(w, self.scoring.replace("`", ""), w)

    def test_the_site_reads_the_data(self):
        build = load_build()
        b = build.rating_build()
        self.assertEqual(dict(b["files"])["score/ppa.py"], sha256("score/ppa.py"))
        section_html = build.rating_build_html()
        y = self.rb["yosys"]
        for w in (y["sha256"], y["git_sha1"], y["package"], *y["runtime"], self.pins["liberty"]["sha256"],
                  sha256("score/ppa.py"), sha256("score/ppa_pins.json"), self.flow["canon_script_sha256"],
                  self.flow["script_sha256"], f'id="{build.RATING_BUILD_ANCHOR}"', y["launcher"], y["self_check"],
                  self.rb["previous"]["version_line"]):
            self.assertIn(w, section_html)
        for w in ("Yosys 0.53", "byte for byte", f"{self.rb['determinism']['designs']} designs", "pip install -r "
                  "requirements.txt", "macOS and on Linux alike", f"at most {y['memory_ceiling_gib']} GiB of memory"):
            self.assertIn(w, section_html)
        # since 2026-11-11 the score card's line names the version and links the section, which holds the rest
        line = build.score_line(types.SimpleNamespace(page="tasks/add/index.html", pdk="sky130"))
        self.assertIn("Rated with " + build.page.link("../../rules.html#" + build.RATING_BUILD_ANCHOR,
                                                      "Yosys " + y["version"]), line)
        line = build.score_line(types.SimpleNamespace(page="tasks/add/index.html", pdk=build.COURSE2))
        self.assertNotIn("Rated with", line)
        self.assertIn(build.page.link("../../rules.html#" + build.ASAP7PNR_ANCHOR, "How the routed course is scored"),
                      line)

    def test_step0_checks_the_build_and_builds_none(self):
        """Decided 2026-11-24: Step 0 gives no recipe to build Yosys any more (pip installs the rating build); its fold is
        the launcher's self-check with the module's sha256 and version line, copyable."""
        recipe = load_build().yosys_recipe(None)
        y = self.rb["yosys"]
        self.assertIn(y["self_check"], recipe)
        self.assertIn(y["sha256"], recipe)
        self.assertIn(y["version_line"], recipe)
        self.assertNotIn("yosys.tar.gz", recipe)
        export = os.path.join(SVGOLF, "tools", "export_public.py")
        workflow = os.path.join(SVGOLF, ".github", "workflows", "records.yml")
        for path in (export, workflow):
            if os.path.isfile(path):
                body = text(os.path.relpath(path, SVGOLF).replace(os.sep, "/"))
                self.assertNotIn("yosys.tar.gz", body)
                self.assertIn("score/yosys_wasm.py --self-check", body)


if __name__ == "__main__":
    unittest.main()
