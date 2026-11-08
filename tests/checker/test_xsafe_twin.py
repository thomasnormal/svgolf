#!/usr/bin/env python3.12
"""Rule 3's Python twin (check/clocked_rules.py, `xsafe_findings`) against the Lean rule (`xsafeB`,
SvGolf/TaskSeq.lean), REAL Lean, on two suites: every fixture of tests/seq_counter/xsafe/ (the `.sv` files
of the txtask-v2 acceptance table, tests/seq_counter/negative/Table.lean, and of the attacks on revisions 2
and 3 and the review of revision 3, all on the counter's interface) at every probe point of
tests/seq_counter (N = 1, 2, 3, 8); and every design of the reactive task `arbiter` (its reference, the
attacks of tests/arbiter/attacks/ and the negatives of tests/arbiter/negative/; rule 3 is part of the
ReactTask statement since 2026-11-06) at its probe points (N = 1, 2, 3, 5, 8), with the hand-built twins
of tests/arbiter/negative/Refute.lean. For each:

  * the twin, on the pinned extractor's envelope (check/envelope.py, as check.py runs it);
  * `xsafeB (d.sem N)` of the design `load_sv` loads from the same file (one generated Lean file,
    `lake env lean`, behind $SVGOLF_LEAN_WRAP when it is set), and `xsafeB` of the table's hand-built
    twins (`Table.lean`; MEASURED equal to the loaded designs there).

The twin must be SOUND (it refuses only where `xsafeB` is false: a refusal before the proof of a design
the proof could accept would be wrong), and agree with `xsafeB` at every point except where the loaded
design has an `Unsupported` node (`hasUnsupported`: its lowering refused a construct the envelope
carries, which the twin does not re-derive), which the `design` stage refuses before any proof (the
`U` rows). A fixture the source gate refuses has no envelope and no loaded design: both columns are
`gate`; one `load_sv` refuses (the loader's own refusal, `load_design_sv2`: the `design` stage) has
the twin's verdict and `loader`. Prints the table.

    python3.12 tests/checker/test_xsafe_twin.py
"""
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import clocked_rules  # noqa: E402
import envelope  # noqa: E402

COUNTER = os.path.join(SVGOLF, "tests", "seq_counter")
FIXTURES = os.path.join(COUNTER, "xsafe")
POINTS = [1, 2, 3, 8]
ARBITER = os.path.join(SVGOLF, "tasks", "arbiter")
ARBITER_TESTS = os.path.join(SVGOLF, "tests", "arbiter")
# Table.lean's hand-built twins: (fixture file stem, Lean term, N)
TABLE_TWINS = [("f0_xpess", "f0", 1), ("f1_tover", "f1", 1), ("f2_w1", "f2", 1), ("f3_w2", "f3", 1),
               ("f4_divc", "f4", 1), ("f5_guard", "f5", 1), ("f6_w3", "f6", 1), ("f7_bit", "f7", 1),
               ("f8_case", "f8", 1), ("f9_eqx", "f9", 1), ("f10_oob", "f10a", 1), ("f10_pow2", "f10b", 1),
               ("f11_w4", "u4", 1), ("f12_sidx_read", "f12", 1), ("f13_sidx_write", "f13", 1),
               ("f14_oob_write", "f14", 1), ("f15_cast_idx", "f15", 1), ("f16_ctx_width", "f16", 2),
               ("h1_xopt", "SvGolf.Tests.SeqCounter.Negative.h1x 1", 1),
               ("h1_rare", "SvGolf.Tests.SeqCounter.Negative.h1r 1", 1),
               ("f1_mealy", "SvGolf.Tests.SeqCounter.Negative.f1m 1", 1)]
# Refute.lean's hand-built twins of the arbiter's designs (MEASURED equal to the loaded designs there, `#guard`)
ARBITER_TWINS = [("a16_xopt", "SvGolf.Tasks.Arbiter.Refute.a16D 2", 2),
                 ("bit_ring", "SvGolf.Tasks.Arbiter.Refute.ringD 2", 2),
                 ("reset_edge", "SvGolf.Tasks.Arbiter.Refute.edgeD 2", 2)]
# (the task directory load_sv and the twin read, the probe points, the module the twins live in, the twins)
SUITES = {
    "counter": (COUNTER, POINTS, "tests.seq_counter.negative.Table", "SvGolf.Tests.SeqCounter.Table", TABLE_TWINS),
    "arbiter": (ARBITER, [1, 2, 3, 5, 8], "tests.arbiter.negative.Refute", "SvGolf.Tasks.Arbiter.Refute",
                ARBITER_TWINS),
}


def arbiter_fixtures():
    """The arbiter's designs: its reference, its attacks and its negatives."""
    out = [os.path.join(ARBITER, "reference", "rr_mask.sv")]
    for sub in ("attacks", "negative"):
        d = os.path.join(ARBITER_TESTS, sub)
        out += sorted(os.path.join(d, f) for f in os.listdir(d) if f.endswith(".sv"))
    return out


def twin_verdicts(sv, work, tdir=COUNTER):
    """{N: [findings]} for the fixture, or None when the source gate or the extractor refuses it."""
    task = envelope.load_task(tdir)
    try:
        env = envelope.extract(sv, task["top"], envelope.probe_points(task),
                               os.path.join(work, os.path.basename(sv)[:-3]))["envelope"]
    except envelope.Refused:
        return None
    out = {}
    for pt, mod in clocked_rules.modules_at_points(env):
        out[int(pt.split("=")[1])] = clocked_rules.xsafe_findings(mod)
    return out


def lean_text(fixtures, at=None, suite="counter"):
    """The probe; `at` (a dict) gets each fixture's stem -> the line of its `load_sv`."""
    tdir, points, mod, ns, twins = SUITES[suite]
    lines = ["import SvGolf.LoadSv", f"import {mod}", "",
             f"open LeanModels.Sv SvGolf {ns}", "", "set_option maxRecDepth 100000", "",
             "namespace XSafeTwinProbe"]
    for k, sv in enumerate(fixtures):
        lines.append(f'load_sv d{k} from "{sv}" (task := "{os.path.relpath(tdir, SVGOLF)}")')
        stem = os.path.basename(sv)[:-3]
        if at is not None:
            at[stem] = len(lines)
        cells = " ".join(f"N={n}:{{xsafeB (d{k}.sem {n})}}/{{(d{k}.sem {n}).hasUnsupported}}" for n in points)
        lines.append(f'#eval IO.println s!"XS {stem} {cells}"')
    for stem, term, n in twins:
        lines.append(f'#eval IO.println s!"TW {stem} N={n}:{{xsafeB ({term})}}"')
    lines.append("end XSafeTwinProbe")
    return "\n".join(lines) + "\n"


def run_lean(fixtures, work, suite="counter"):
    path = os.path.join(work, "XSafeTwinProbe.lean")
    at = {}
    with open(path, "w") as fh:
        fh.write(lean_text(fixtures, at, suite))
    wrap = shlex.split(os.environ.get("SVGOLF_LEAN_WRAP", ""))
    # the probe's imports first (it reads their built modules), then the probe
    b = subprocess.run(wrap + ["lake", "build", "SvGolf.LoadSv", SUITES[suite][2]], cwd=SVGOLF,
                       capture_output=True, text=True)
    if b.returncode != 0:
        raise AssertionError(f"lake build of the probe's imports failed:\n{(b.stdout + b.stderr)[-3000:]}")
    p = subprocess.run(wrap + ["lake", "env", "lean", path], cwd=SVGOLF, capture_output=True, text=True)
    loaded, twins, errors = {}, {}, {}
    for m in re.finditer(r"XSafeTwinProbe\.lean:(\d+):\d+: error: (.*)", p.stdout):
        errors.setdefault(int(m.group(1)), m.group(2))
    refused = {stem: errors[line] for stem, line in at.items() if line in errors}
    for ln in p.stdout.splitlines():
        m = re.match(r"XS (\S+) (.*)$", ln)
        if m:
            cells = re.findall(r"N=(\d+):(\w+)/(\w+)", m.group(2))
            loaded[m.group(1)] = ({int(n): v == "true" for n, v, _ in cells},
                                  {int(n): u == "true" for n, _, u in cells})
        m = re.match(r"TW (\S+) N=(\d+):(\w+)$", ln)
        if m:
            twins[m.group(1)] = (int(m.group(2)), m.group(3) == "true")
    return loaded, twins, refused, p


class XSafeTwin(unittest.TestCase):
    def test_the_twin_agrees_with_xsafeB(self):
        self.agrees(sorted(os.path.join(FIXTURES, f) for f in os.listdir(FIXTURES) if f.endswith(".sv")), "counter")

    def test_the_twin_agrees_with_xsafeB_on_the_arbiter(self):
        self.agrees(arbiter_fixtures(), "arbiter")

    def agrees(self, fixtures, suite):
        tdir, POINTS, _, _, _ = SUITES[suite]
        self.assertGreater(len(fixtures), 0)
        work = tempfile.mkdtemp(prefix="svgolf-xsafe-twin-")
        t0 = time.time()
        twin = {os.path.basename(sv)[:-3]: twin_verdicts(sv, work, tdir) for sv in fixtures}
        t_twin = time.time() - t0
        loadable = [sv for sv in fixtures if twin[os.path.basename(sv)[:-3]] is not None]
        t0 = time.time()
        loaded, twins, refused, proc = run_lean(loadable, work, suite)
        t_lean = time.time() - t0
        rows, unsound, disagree = [], [], []
        for sv in fixtures:
            stem = os.path.basename(sv)[:-3]
            tv = twin[stem]
            tw = twins.get(stem)
            tw_s = f"{'true' if tw[1] else 'false'} (N={tw[0]})" if tw else ""
            if tv is None:
                rows.append((stem, "gate", "gate", tw_s, ""))
                continue
            fmt = lambda d: " ".join("T" if d[n] else "F" for n in POINTS)  # noqa: E731
            t_ok = {n: not tv[n] for n in POINTS}
            if stem in refused and stem not in loaded:
                rows.append((stem, fmt(t_ok), "loader", tw_s, "load_sv: " + refused[stem][:80]))
                continue
            self.assertIn(stem, loaded, f"no Lean result for {stem}:\n{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}")
            lv, unsup = loaded[stem]
            for n in POINTS:
                if not t_ok[n] and lv[n]:
                    unsound.append(f"{stem} N={n}: the twin refuses, xsafeB is true: {tv[n]}")
                elif t_ok[n] != lv[n] and not unsup[n]:
                    disagree.append(f"{stem} N={n}: twin {'admits' if t_ok[n] else 'refuses'}, xsafeB {lv[n]}")
            why = "; ".join(sorted({(f.split("`: ")[0] + "`" if "`: " in f else f[:60]) for n in POINTS
                                    for f in tv[n]}))
            rows.append((stem, fmt(t_ok), fmt(lv) + (" U" if any(unsup.values()) else ""), tw_s, why))
        print(f"\nrule 3 ({suite}): twin vs xsafeB, N = {POINTS} (T = admitted), {len(fixtures)} fixtures "
              f"[twin {t_twin:.1f} s, Lean {t_lean:.1f} s]")
        print(f"{'fixture':24s} {'twin':9s} {'xsafeB':11s} {'Table twin':12s} twin's first reason")
        for r in rows:
            print(f"{r[0]:24s} {r[1]:9s} {r[2]:11s} {r[3]:12s} {r[4]}")
        self.assertEqual(unsound, [])
        self.assertEqual(disagree, [])
        for stem, (n, v) in twins.items():
            if twin.get(stem) is not None and stem in loaded:
                self.assertEqual(v, loaded[stem][0][n], f"Table twin of {stem} vs the loaded design at N={n}")


if __name__ == "__main__":
    unittest.main(verbosity=1)
