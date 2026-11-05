#!/usr/bin/env python3.12
"""Post-synthesis check of the `add` designs: the SCORED netlist computes the adder.

    python3.12 tests/add/validate/postsynth.py [--widths 16,32,64] [--vectors 5000]   (from svgolf/)

For each design, at each width: the source gate's canonical text is scored
by exactly the pinned flow (`score/score.py`: `score/canon.ys`, then
`score/svgolf.ys`, whose last line writes the scored gate netlist), and
Verilator simulates THAT netlist (with Yosys's `simcells.v`, through the
checker's own harness `check/postsynth.py`: one C++ model per netlist, every
vector in, one row per vector out) on the all-ones corner cases plus
fixed-seed random vectors, against `a + b + cin` computed in Python. The
checker's `postsynth` stage compares the netlist with ls-sv's reading; this
script compares it with the task's FUNCTION, for designs that have no proof
(the baselines) as well. Exit status 0 iff no mismatch.
"""

import argparse
import os
import random
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "score"))
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import postsynth  # noqa: E402  (check/postsynth.py: the Verilator build + harness)
import score  # noqa: E402
import srcgate  # noqa: E402

# Paths relative to svgolf/.
DESIGNS = ["tasks/add/reference/add_n.sv", "tests/add/baselines/add_n_sklansky.sv",
           "tests/add/baselines/add_n_kogge_stone.sv", "tests/add/negative/plus.sv",
           "tests/add/baselines/cmp_carry.sv"]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--widths", default="16,32,64")
    ap.add_argument("--vectors", type=int, default=5000)
    args = ap.parse_args()
    widths = [int(w) for w in args.widths.split(",")]
    work = tempfile.mkdtemp(prefix="svgolf-add-postsynth-")
    rng = random.Random(20261028)
    failures = 0
    try:
        for rel in DESIGNS:
            canon_text, findings = srcgate.gate_file(os.path.join(SVGOLF, rel), name=rel)
            if findings:
                print(f"[FAIL] {rel}: source gate: {findings[:2]}")
                failures += 1
                continue
            canon = os.path.join(work, os.path.basename(rel))
            with open(canon, "w") as fh:
                fh.write(canon_text)
            for n in widths:
                tag = f"{os.path.basename(rel)[:-3]}_{n}"
                net = os.path.join(work, tag + ".net.v")
                score.score([canon], "add_n", {"N": n}, gate=False, netlist_out=net)
                m = (1 << n) - 1
                vs = [(m, m, 1), (m, 0, 1), (m, 1, 0), (0, 0, 0), (0, m, 1)]
                vs += [(rng.getrandbits(n), rng.getrandbits(n), rng.getrandbits(1))
                       for _ in range(args.vectors)]
                ins, outs = [("a", n), ("b", n), ("cin", 1)], [("s", n), ("cout", 1)]
                exe, _, err = postsynth.vl_build([net, postsynth.simcells()], "add_n", {}, ins,
                                                 outs, work, tag, 900)
                rows = None
                if exe is not None:
                    rows, _, err = postsynth.vl_run(
                        exe, ins, outs, [{"a": a, "b": b, "cin": c} for a, b, c in vs], work, tag,
                        900)
                if rows is None:
                    print(f"[FAIL] {rel} N={n}: {err}", flush=True)
                    failures += 1
                    continue
                bad = sum([format((a + b + c) & m, f"0{n}b"), str((a + b + c) >> n)]
                          != [r["s"], r["cout"]] for (a, b, c), r in zip(vs, rows))
                failures += bad != 0
                print(f"[{'ok' if bad == 0 else 'FAIL'}] {rel} N={n}: netlist of the pinned flow, "
                      f"{len(vs)} vectors, {bad} mismatches", flush=True)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    print("postsynth:", "PASS" if not failures else "FAIL")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
