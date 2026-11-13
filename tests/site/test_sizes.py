"""The charts' per-size data path (prepared 2026-11-13 for the owner's UI feedback item 11; the data is another
round's): site/build.py `load_sizes` reads leaderboard/sizes/<task>.json, which no task has yet, and `size_series`
gives the area-time plot one series per size. Without the file nothing changes: one series, the scoring point's.

    python3.12 svgolf/tests/site/test_sizes.py
"""

import importlib.util
import os
import sys
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
SITE = os.path.join(SVGOLF, "site")
sys.path.insert(0, SITE)

spec = importlib.util.spec_from_file_location("svgolf_site_build_sizes", os.path.join(SITE, "build.py"))
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


class FakeTask:
    def __init__(self, name, pdk="sky130", point=None):
        self.name, self.pdk, self.point = name, pdk, point or {"N": 16}


DESIGNS = [{"id": "a", "sha": "1" * 64, "m": {"area_um2": 10.0, "time_ps": 100}},
           {"id": "b", "sha": "2" * 64, "m": {"area_um2": 20.0, "time_ps": 50}}]


class SizesTest(unittest.TestCase):
    def test_no_task_has_a_sizes_file_yet_and_nothing_changes(self):
        self.assertFalse(os.path.isdir(os.path.join(SVGOLF, "leaderboard", "sizes")))
        for name in os.listdir(os.path.join(SVGOLF, "tasks")):
            if os.path.isfile(os.path.join(SVGOLF, "tasks", name, "task.json")):
                self.assertIsNone(build.load_sizes(FakeTask(name)), name)
        self.assertEqual(build.size_series(FakeTask("mul"), DESIGNS), [(None, None, DESIGNS)])

    def test_a_sizes_file_gives_one_series_per_size(self):
        data = {"task": "mul", "points": [{"key": "N=16", "params": {"N": 16}}, {"key": "N=8", "params": {"N": 8},
                                                                                  "label": "N = 8"}],
                "courses": {"sky130": {"1" * 64: {"N=8": {"area_um2": 3.0, "time_ps": 40}}},
                            "asap7pnr": {}}}
        with mock.patch.object(build, "load_sizes", return_value=data):
            series = build.size_series(FakeTask("mul"), DESIGNS)
            self.assertEqual([k for k, _, _ in series], [None, "N=8"])
            key, label, at = series[1]
            self.assertEqual(label, "N = 8")
            self.assertEqual([d["id"] for d in at], ["a"])          # b has no N = 8 numbers: left out there
            self.assertEqual(at[0]["m"], {"area_um2": 3.0, "time_ps": 40})
            self.assertEqual(DESIGNS[0]["m"], {"area_um2": 10.0, "time_ps": 100})       # the page's own untouched
            self.assertEqual(build.size_series(FakeTask("mul", pdk="asap7pnr"), DESIGNS), [(None, None, DESIGNS)])


if __name__ == "__main__":
    unittest.main()
