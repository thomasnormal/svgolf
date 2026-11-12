"""The build ratings use (decided 2026-11-05): score/reference_build.json is the data, the README's "Scoring" states it,
and the site reads it (the rules page's section, every task's score card). No site build: the README, the data files
and site/build.py's functions.

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

    def test_the_data_is_the_pinned_flow(self):
        """The rating build's Yosys is the version the expected scores were measured with."""
        y = self.rb["yosys"]
        self.assertEqual(y["version_line"], self.flow["yosys_version"])
        self.assertIn(y["git_sha1"], y["version_line"])
        self.assertTrue(y["version_line"].startswith(f"Yosys {y['version']} "))
        for k in ("yosys", "abc"):
            self.assertRegex(self.rb[k]["sha256"], r"^[0-9a-f]{64}$")

    def test_the_readme_states_the_build_and_every_hash(self):
        y, a, d = self.rb["yosys"], self.rb["abc"], self.rb["determinism"]
        want = [y["git_sha1"], y["sha256"], flat(y["version_line"]), a["sha256"], flat(a["version_line"]),
                "Homebrew build for macOS arm64", "clang++ 17 with -O3", "ABC 1.01 of 6 May 2025",
                self.pins["liberty"]["sha256"], sha256("score/ppa.py"), sha256("score/ppa_pins.json"),
                self.flow["canon_script_sha256"], self.flow["script_sha256"],
                f"{d['designs']} designs, {d['runs']} runs", f"{d['other_build']['max_delay_change_pct']:g}% in delay",
                "score/reference_build.json"]
        for w in want:
            self.assertIn(w, self.scoring.replace("`", ""), w)

    def test_the_site_reads_the_data(self):
        build = load_build()
        b = build.rating_build()
        self.assertEqual(dict(b["files"])["score/ppa.py"], sha256("score/ppa.py"))
        section_html = build.rating_build_html()
        for w in (self.rb["yosys"]["sha256"], self.rb["abc"]["sha256"], self.pins["liberty"]["sha256"],
                  sha256("score/ppa.py"), sha256("score/ppa_pins.json"), self.flow["canon_script_sha256"],
                  self.flow["script_sha256"], f'id="{build.RATING_BUILD_ANCHOR}"'):
            self.assertIn(w, section_html)
        # since 2026-11-11 the score card's line names the version and links the section, which holds the rest
        for w in ("Yosys 0.53", self.rb["yosys"]["git_sha1"][:8], "ABC 1.01 of 6 May 2025", "deterministic",
                  f"{self.rb['determinism']['designs']} designs", f'id="{build.RATING_BUILD_ANCHOR}"'):
            self.assertIn(w, section_html)
        for pdk in ("sky130", "asap7"):            # score_line reads the page's path and the view's library
            line = build.score_line(types.SimpleNamespace(page="tasks/add/index.html", pdk=pdk))
            self.assertIn("Rated with " + build.page.link("../../rules.html#" + build.RATING_BUILD_ANCHOR,
                                                          "Yosys " + self.rb["yosys"]["version"]), line)
            self.assertIn("Yosys 0.53", line)


if __name__ == "__main__":
    unittest.main()
