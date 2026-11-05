#!/usr/bin/env python3.12
"""Cross-checks of task `clmul`'s function (README.md of the task, REVIEW.md): everything quick.

    python3.12 tests/clmul/validate/validate.py [--lean-wrap "CMD"] [--no-lean]

Steps (each prints one line; exit status 0 iff all pass):

  oracle   `tasks/clmul/oracle.py` (shift-and-XOR) equals an independent implementation by KRONECKER
           SUBSTITUTION (spread the bits k = bit_length(N) + 1 apart, multiply as Python integers, read the
           parity of each group) on every pair at N = 1 .. 6 and on random pairs at N in {7, 8, 16, 31,
           32, 33, 64, 100};
  anchors  the published products: the polynomial identities `(x+1)^2 = x^2+1`, `(x^2+1)(x+1) =
           x^3+x^2+x+1`, `(1+...+x^15)^2 = 1+x^2+...+x^30` and FIPS 197 Section 4.2: the unreduced
           products `0x57 (x) 0x83 = 0x2b79` and `0x57 (x) 0x13 = 0x0589` reduce modulo `0x11b` to
           `{c1}` (2001 edition) and `{fe}` (2023 edition, Eq. (4.7));
  lean     the TRUSTED Lean spec (`SvGolf.Tasks.Clmul.task.fn`, run through Lean's interpreter by
           `Dump.lean`) equals the oracle on every pair at N = 1 .. 7 and on the sample pairs at larger N
           (skipped with --no-lean; the Lean job goes through --lean-wrap, the slot wrapper).
"""
import argparse
import os
import random
import shlex
import subprocess
import sys

sys.dont_write_bytecode = True       # the oracle is imported from tasks/clmul/, which holds no build output
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(SVGOLF, "tasks", "clmul"))
from oracle import oracle  # noqa: E402


def clmul_oracle(n, a, b):
    return oracle({"N": n}, {"a": a, "b": b})["p"]


def clmul_kronecker(n, a, b):
    """The independent implementation: integer multiplication of the bit-spread operands."""
    k = n.bit_length() + 1                 # a group sums at most n ones: n < 2^k, so no carry leaves a group
    def spread(x):
        return sum(((x >> i) & 1) << (k * i) for i in range(n))
    prod = spread(a) * spread(b)
    return sum(((prod >> (k * j)) & 1) << j for j in range(2 * n - 1))


def reduce_mod(p, mod):
    """Polynomial remainder of p modulo `mod` over GF(2)."""
    while p.bit_length() >= mod.bit_length():
        p ^= mod << (p.bit_length() - mod.bit_length())
    return p


def step_oracle():
    rng = random.Random(20261101)
    count = 0
    for n in range(1, 7):
        for a in range(1 << n):
            for b in range(1 << n):
                assert clmul_oracle(n, a, b) == clmul_kronecker(n, a, b), (n, a, b)
                count += 1
    for n in (7, 8, 16, 31, 32, 33, 64, 100):
        corners = [0, 1, (1 << n) - 1, 1 << (n - 1), ((1 << n) - 1) // 3]
        pairs = [(a, b) for a in corners for b in corners] + [
            (rng.getrandbits(n), rng.getrandbits(n)) for _ in range(300)]
        for a, b in pairs:
            assert clmul_oracle(n, a, b) == clmul_kronecker(n, a, b), (n, a, b)
            count += 1
    print(f"oracle   shift-and-XOR = Kronecker substitution on {count} pairs (every pair at N <= 6)")


def step_anchors():
    assert clmul_oracle(2, 0b11, 0b11) == 0b101
    assert clmul_oracle(3, 0b101, 0b011) == 0b01111
    assert clmul_oracle(16, 0xffff, 0xffff) == 0x55555555
    assert clmul_oracle(8, 0x57, 0x83) == 0x2b79
    assert clmul_oracle(8, 0x57, 0x13) == 0x0589
    assert reduce_mod(0x2b79, 0x11b) == 0xc1      # FIPS 197 (2001) Section 4.2: {57} * {83} = {c1}
    assert reduce_mod(0x0589, 0x11b) == 0xfe      # FIPS 197 (2023) Eq. (4.7): {57} * {13} = {fe}
    # the product is a ring homomorphism's worth of structure: commutative, distributive, x-shift
    rng = random.Random(7)
    for _ in range(500):
        n = rng.randrange(1, 40)
        a, b, c = (rng.getrandbits(n) for _ in range(3))
        assert clmul_oracle(n, a, b) == clmul_oracle(n, b, a)
        assert clmul_oracle(n, a ^ b, c) == clmul_oracle(n, a, c) ^ clmul_oracle(n, b, c)
        assert clmul_oracle(n + 1, a << 1, b) == clmul_oracle(n, a, b) << 1
    print("anchors  (x+1)^2, (x^2+1)(x+1), (1+...+x^15)^2, FIPS 197 {57}*{83}={c1} and {57}*{13}={fe}; "
          "commutative, distributive, shifts")


def step_lean(wrap):
    cmd = shlex.split(wrap) if wrap else []
    cmd += ["lake", "env", "lean", "--run", "tests/clmul/validate/Dump.lean"]
    proc = subprocess.run(cmd, cwd=SVGOLF, capture_output=True, text=True)
    if proc.returncode != 0:
        print("lean     FAILED to run Dump.lean:", (proc.stderr or proc.stdout)[-600:])
        return False
    rows = [ln.split() for ln in proc.stdout.splitlines() if ln.strip()]
    bad = [r for r in rows if clmul_oracle(int(r[0]), int(r[1]), int(r[2])) != int(r[3])]
    exhaustive = sum(1 for r in rows if int(r[0]) <= 7)
    expect_exh = sum(4 ** n for n in range(1, 8))
    if bad or exhaustive != expect_exh:
        print(f"lean     FAILED: {len(bad)} mismatches (first {bad[:3]}), {exhaustive} of {expect_exh} exhaustive rows")
        return False
    print(f"lean     the Lean spec equals the oracle on {len(rows)} pairs ({exhaustive} exhaustive at N <= 7)")
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--lean-wrap", default="")
    ap.add_argument("--no-lean", action="store_true")
    args = ap.parse_args()
    step_oracle()
    step_anchors()
    ok = True if args.no_lean else step_lean(args.lean_wrap)
    print("validate:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
