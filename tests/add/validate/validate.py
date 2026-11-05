#!/usr/bin/env python3.12
"""Simulation validation of the `add` task's designs: Verilator vs ls-sv `run2` vs arithmetic.

    python3.12 tests/add/validate/validate.py [--quick] [--out DIR] [--lean-wrap CMD]   (from svgolf/)
    python3.12 tests/add/validate/validate.py --verilator-only --widths 9,10,24 --samples 2000

For every design below, at every width N of the plan:

  * the pinned lean-surfaces extractor writes the design's sv-0.2 envelope
    (from the source gate's canonical text, through svGolf's one extraction
    path `check/envelope.py`, as the checker does);
  * Verilator simulates the design on every vector (one C++ model per width,
    built by `check/postsynth.py`'s harness: all vectors in, one row per
    vector out; Verilator is 2-state, so an `x` output cannot be seen here --
    the checker's static rules and its `postsynth` stage are the x/z defence);
  * ls-sv's `run2` runs one cycle per vector on `PDesign.instantiateGD2 [N]`
    (exactly `name.sem N`), under both schedules `σ_src` and `σ_rev`
    (`Run.lean`);
  * the expected outputs are `s = (a + b + cin) mod 2^N`,
    `cout = (a + b + cin) div 2^N`, in Python integers.

Vectors: EVERY input combination (2^(2N+1)) for N = 1..5, and for the larger
widths a fixed-seed random sample plus corner cases (all zeros, all ones,
a full carry ripple, alternating bits, single bits, the top bit).

Verdicts:
  correct designs (the reference, the baselines and Yosys's own `+`):
      Verilator, run2/σ_src and run2/σ_rev all equal the expected outputs on
      every vector;
  functional negatives: Verilator and run2 both DISAGREE with the expected
      outputs on at least one vector (the mutant is caught), and Verilator and
      run2 agree with EACH OTHER on every vector (ls-sv reads the wrong design
      the way a simulator does).
With --verilator-only, ls-sv is skipped (no Lean): Verilator alone against the
arithmetic, for random samples at other widths (--widths, --samples; the bulk
and exhaustive runs are verilator.py's).
Exit status 0 iff every verdict holds.
"""

import argparse
import os
import random
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
RUNNER = os.path.relpath(os.path.join(HERE, "Run.lean"), SVGOLF)
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(SVGOLF, "check"))
import envelope  # noqa: E402  (check/envelope.py: svGolf's one extraction path)
import postsynth  # noqa: E402  (check/postsynth.py: the Verilator build + harness)

TOP = "add_n"
# (label, path relative to svgolf/, kind)
DESIGNS = [
    ("reference ripple", "tasks/add/reference/add_n.sv", "correct"),
    ("baseline sklansky", "tests/add/baselines/add_n_sklansky.sv", "correct"),
    ("baseline kogge-stone", "tests/add/baselines/add_n_kogge_stone.sv", "correct"),
    ("baseline cmp_carry", "tests/add/baselines/cmp_carry.sv", "correct"),
    ("baseline yosys +", "tests/add/negative/plus.sv", "correct"),
    ("reference ripple, always_comb carry cell", "tasks/add/reference/add_proc.sv", "correct"),
    ("reference ripple, one always_comb body for carry and sum", "tasks/add/reference/add_proc_m.sv", "correct"),
    ("reference ripple, conditional expression carry", "tasks/add/reference/add_mux.sv", "correct"),
    ("negative no_cin", "tests/add/negative/no_cin.sv", "wrong"),
    ("negative cout_off", "tests/add/negative/cout_off.sv", "wrong"),
    ("negative carry_bug", "tests/add/negative/carry_bug.sv", "wrong"),
    ("negative only_n16", "tests/add/negative/only_n16.sv", "wrong"),
]
EXHAUSTIVE = [1, 2, 3, 4, 5]
RANDOM = [6, 7, 8, 13, 16, 31, 32, 33, 64]
SAMPLES = 300

FAILURES = []


def log(*a):
    print(*a, flush=True)


def vectors(n, samples, rng):
    if n in EXHAUSTIVE:
        return [(a, b, c) for c in (0, 1) for b in range(1 << n) for a in range(1 << n)]
    m = (1 << n) - 1
    alt = int("10" * n, 2) & m
    vs = [(0, 0, 0), (0, 0, 1), (m, 0, 1), (0, m, 1), (m, m, 0), (m, m, 1), (m, 1, 0),
          (alt, alt, 1), (alt, m ^ alt, 1), (1 << (n - 1), 1 << (n - 1), 0),
          (1 << (n - 1), 1 << (n - 1), 1)]
    vs += [(1 << k, m, 0) for k in range(n)]
    vs += [(rng.getrandbits(n), rng.getrandbits(n), rng.getrandbits(1)) for _ in range(samples)]
    return vs


def expected(n, a, b, c):
    t = a + b + c
    return format(t % (1 << n), f"0{n}b"), str(t >> n)


def verilator(sv, n, vs, work):
    """Verilator on the RTL at width `n`: per vector [s, cout] as binary
    strings (the shape `expected` gives). Raises RuntimeError when the model
    does not build or run."""
    ins, outs = [("a", n), ("b", n), ("cin", 1)], [("s", n), ("cout", 1)]
    exe, _, err = postsynth.vl_build([sv], TOP, {"N": n}, ins, outs, work, f"n{n}", 900, rtl=True)
    if exe is None:
        raise RuntimeError(f"Verilator N={n}: {err}")
    rows, _, err = postsynth.vl_run(exe, ins, outs, [{"a": a, "b": b, "cin": c} for a, b, c in vs],
                                    work, f"n{n}", 900)
    if rows is None:
        raise RuntimeError(f"Verilator N={n}: {err}")
    return [[r["s"], r["cout"]] for r in rows]


def validate(label, rel, kind, work, wrap, plan, verilator_only=False):
    src = os.path.join(SVGOLF, rel)
    d = os.path.join(work, label.replace(" ", "_"))
    try:
        ex = envelope.extract(src, TOP, [], d, name="design.sv")
    except envelope.Refused as e:
        FAILURES.append(f"{label}: {e.stage}: {e.msg[:600]}")
        return
    sv, env = ex["canonical"], ex["envelope"]
    jobs, per_n = [], {}
    for n, vs in plan:
        vdec = os.path.join(d, f"v{n}.dec")
        with open(vdec, "w") as fh:
            fh.writelines(f"{a} {b} {c}\n" for a, b, c in vs)
        out = os.path.join(d, f"r{n}.txt")
        jobs.append(f"{n} {vdec} {out}")
        per_n[n] = (vs, out)
    jf = os.path.join(d, "jobs.txt")
    with open(jf, "w") as fh:
        fh.write("\n".join(jobs) + "\n")
    if not verilator_only:
        proc = subprocess.run(wrap + ["lake", "env", "lean", "--run", RUNNER, env, jf],
                              cwd=SVGOLF, capture_output=True, text=True)
        if proc.returncode != 0:
            FAILURES.append(f"{label}: run2 runner failed: {(proc.stderr + proc.stdout)[-800:]}")
            return
    total = {"vectors": 0, "vl_bad": 0, "src_bad": 0, "rev_bad": 0, "vl_vs_run2": 0}
    if verilator_only:
        total = {"vectors": 0, "vl_bad": 0}
    for n, (vs, out) in per_n.items():
        try:
            ic = verilator(sv, n, vs, d)
        except RuntimeError as e:
            FAILURES.append(f"{label}: N={n}: {str(e)[:600]}")
            continue
        if verilator_only:
            for (a, b, c), icr in zip(vs, ic):
                exp = list(expected(n, a, b, c))
                total["vectors"] += 1
                total["vl_bad"] += icr != exp
                if kind == "correct" and icr != exp and total["vl_bad"] <= 3:
                    FAILURES.append(f"{label}: N={n} a={a} b={b} cin={c}: expected {exp}, "
                                    f"Verilator {icr}")
            continue
        with open(out) as fh:
            r2 = [ln.split() for ln in fh.read().splitlines() if ln]
        if len(ic) != len(vs) or len(r2) != len(vs):
            FAILURES.append(f"{label}: N={n}: {len(vs)} vectors, {len(ic)} Verilator rows, "
                            f"{len(r2)} run2 rows")
            continue
        bad_shown = 0
        for (a, b, c), icr, rr in zip(vs, ic, r2):
            exp = list(expected(n, a, b, c))
            total["vectors"] += 1
            ib, sb, rb = icr != exp, rr[0:2] != exp, rr[2:4] != exp
            total["vl_bad"] += ib
            total["src_bad"] += sb
            total["rev_bad"] += rb
            total["vl_vs_run2"] += (icr != rr[0:2]) or (icr != rr[2:4])
            if kind == "correct" and (ib or sb or rb) and bad_shown < 3:
                bad_shown += 1
                FAILURES.append(f"{label}: N={n} a={a} b={b} cin={c}: expected {exp}, "
                                f"Verilator {icr}, run2 src {rr[0:2]}, rev {rr[2:4]}")
            if kind == "wrong" and (icr != rr[0:2] or icr != rr[2:4]) and bad_shown < 3:
                bad_shown += 1
                FAILURES.append(f"{label}: N={n} a={a} b={b} cin={c}: Verilator {icr} but run2 "
                                f"src {rr[0:2]}, rev {rr[2:4]} (ls-sv/Verilator disagreement)")
    if kind == "wrong" and any(v == 0 for k, v in total.items() if k.endswith("_bad")):
        FAILURES.append(f"{label}: the mutant was NOT caught: {total}")
    ok = not any(f.startswith(label + ":") for f in FAILURES)
    log(f"[{'ok' if ok else 'FAIL'}] {label} ({kind}): {total}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--quick", action="store_true", help="N = 1..3 exhaustive, 16 and 64 sampled")
    ap.add_argument("--out", help="work directory (default: a fresh temporary directory)")
    ap.add_argument("--lean-wrap", default=os.environ.get("SVGOLF_LEAN_WRAP", ""))
    ap.add_argument("--seed", type=int, default=20261028)
    ap.add_argument("--verilator-only", action="store_true",
                    help="skip ls-sv (no Lean): Verilator against the arithmetic only")
    ap.add_argument("--widths", help="comma-separated widths instead of the plan "
                    "(N <= 5 exhaustive, larger ones sampled)")
    ap.add_argument("--samples", type=int, help="random vectors per sampled width")
    args = ap.parse_args()
    rng = random.Random(args.seed)
    ns = ([1, 2, 3, 16, 64] if args.quick else EXHAUSTIVE + RANDOM)
    if args.widths:
        ns = [int(w) for w in args.widths.split(",")]
    samples = args.samples or (50 if args.quick else SAMPLES)
    plan = [(n, vectors(n, samples, rng)) for n in ns]
    log("plan: " + ", ".join(f"N={n}: {len(vs)}" for n, vs in plan)
        + f" vectors (seed {args.seed}); "
        + postsynth.verilator_info()[1])
    if not args.verilator_only:
        # `lake env lean --run` builds nothing: bring Run.lean's imports up to date first.
        proc = subprocess.run(args.lean_wrap.split() + ["lake", "build", "LeanModels.Sv.Ingest2"],
                              cwd=SVGOLF, capture_output=True, text=True)
        if proc.returncode != 0:
            log("FAIL: `lake build LeanModels.Sv.Ingest2` failed:\n"
                + (proc.stdout + proc.stderr)[-2000:])
            return 1
    work = args.out or tempfile.mkdtemp(prefix="svgolf-add-validate-")
    os.makedirs(work, exist_ok=True)
    try:
        for label, rel, kind in DESIGNS:
            validate(label, rel, kind, work, args.lean_wrap.split(), plan, args.verilator_only)
    finally:
        if not args.out:
            shutil.rmtree(work, ignore_errors=True)
    for f in FAILURES:
        log("FAIL:", f)
    log("validate:", "PASS" if not FAILURES else "FAIL")
    return 0 if not FAILURES else 1


if __name__ == "__main__":
    sys.exit(main())
