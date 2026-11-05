#!/usr/bin/env python3
"""Differential validation of svgolf/tasks/fdivp/IEEE754.lean (Python 3 standard library only).

Implementations compared, vector by vector, on bit patterns:
  spec  -- SvGolf.IEEE754.divide, evaluated by Run.lean (`lean --run`)
  core  -- Lean core's logical float model Float.Model.UnpackedFloat.div (roundTiesToEven),
           an independent implementation that ships with the toolchain
  A     -- oracle.div_exact: exact Fraction arithmetic, any format, all five modes
  B     -- oracle.div_hw16 / div_hw32: CPU binary64 division + CPython's struct rounding

Usage (from anywhere; Lean runs in the svgolf Lake project):
  python3 svgolf/tasks/fdivp/spec_validate/validate.py [--quick] [--out DIR] [--lean-wrap CMD] [--only G,..]

  --out DIR        working directory for vector files
                   (default: $FPSPEC_OUT, else <tmpdir>/fpspec_out)
  --lean-wrap CMD  prefix for every lean invocation (e.g. a slot-limiting wrapper script)
  --quick          a sample of every set (smoke test, a few minutes)
  --only GROUPS    comma-separated subset of: oracle,toy,b16,b16modes,b32,mutants

Groups:
  oracle    oracle self-checks: decode/encode against CPython's struct 'e' and 'f'
  toy       every pair of bit patterns of 12 small formats, all five modes: spec = A (= core)
  b16       binary16 roundTiesToEven, sets S1-S5: spec = core = B on every vector, = A on samples
  b16modes  binary16, all five modes: spec = A on S1-S5 samples and every constructed tie
  b32       binary32: spec = core = B (roundTiesToEven), spec = A on samples for all modes
  mutants   mutation self-test: ten classic divider bugs must each disagree with the spec
Exit status 0 iff every comparison has zero mismatches and every mutant is caught.
"""

import argparse
import os
import random
import struct
import subprocess
import sys
import tempfile
import time
from array import array
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True   # keep the source tree clean
sys.path.insert(0, HERE)
import oracle  # noqa: E402
from oracle import Fmt, MODES, div_exact, div_hw16, div_hw32  # noqa: E402

SVGOLF = os.path.abspath(os.path.join(HERE, "..", "..", ".."))   # the svgolf Lake project
RUNNER = "tasks/fdivp/spec_validate/Run.lean"
CHUNK = 4_000_000
FAILURES = []
SUMMARY = []


def log(*a):
    print(*a, flush=True)


def typecode(F):
    return {1: "B", 2: "H", 4: "I"}[(F.k + 7) // 8] if F.k <= 32 else None


# ---------------------------------------------------------------------------------------
# Lean plumbing
# ---------------------------------------------------------------------------------------

class Lean:
    def __init__(self, out, wrap):
        self.out = os.path.abspath(out)
        self.wrap = wrap.split() if wrap else []
        self.evals = 0

    def build(self):
        """Build the spec module (`tasks.fdivp.IEEE754`) in the svgolf Lake project for Run.lean."""
        cmd = self.wrap + ["lake", "build", "tasks.fdivp.IEEE754"]
        log("$", " ".join(cmd))
        subprocess.run(cmd, cwd=SVGOLF, check=True)

    def run(self, impl, F, mode, pairs_path, out_path):
        cmd = self.wrap + ["lake", "env", "lean", "--run", RUNNER, impl, str(F.w), str(F.p),
                           mode, pairs_path, out_path]
        subprocess.run(cmd, cwd=SVGOLF, check=True, stdout=subprocess.DEVNULL)

    def eval(self, impl, F, mode, A, B, tag):
        """Results of `impl` (spec|core) on the pairs (A[i], B[i]), as an array."""
        tc = typecode(F)
        res = array(tc)
        for ci in range(0, len(A), CHUNK):
            a, b = A[ci:ci + CHUNK], B[ci:ci + CHUNK]
            inter = array(tc, bytes(2 * len(a) * array(tc).itemsize))
            inter[0::2] = a
            inter[1::2] = b
            pin = os.path.join(self.out, f"{tag}.pairs")
            pout = os.path.join(self.out, f"{tag}.{impl}.{mode}.out")
            with open(pin, "wb") as fh:
                fh.write(inter.tobytes())
            self.run(impl, F, mode, pin, pout)
            got = array(tc)
            with open(pout, "rb") as fh:
                got.frombytes(fh.read())
            assert len(got) == len(a), (len(got), len(a))
            res += got
        if impl == "spec":
            self.evals += len(A)
        return res


# ---------------------------------------------------------------------------------------
# reporting
# ---------------------------------------------------------------------------------------

def describe(F, x):
    d = F.decode(x)
    h = f"{x:#0{(F.k + 3) // 4 + 2}x}"
    if d[0] == "nan":
        return h + ("(sNaN)" if d[1] else "(qNaN)")
    if d[0] == "inf":
        return h + ("(-inf)" if d[1] else "(+inf)")
    return h + f"({'-' if d[1] else '+'}{float(d[2])!r})"


def compare(name, F, mode, A, B, lhs_name, lhs, rhs_name, rhs, show=10):
    bad = [i for i in range(len(A)) if lhs[i] != rhs[i]]
    SUMMARY.append((name, f"{lhs_name} = {rhs_name}", mode, len(A), len(bad)))
    log(f"  [{'ok' if not bad else 'MISMATCH'}] {name:<34} {mode} {lhs_name} = {rhs_name:<4} "
        f"{len(A):>9} vectors, {len(bad)} mismatches")
    for i in bad[:show]:
        log(f"      {describe(F, A[i])} / {describe(F, B[i])}: {lhs_name}={describe(F, lhs[i])} "
            f"{rhs_name}={describe(F, rhs[i])}")
    if bad:
        FAILURES.append((name, mode, lhs_name, rhs_name, len(bad)))


def oracle_A(F, mode, A, B, idx=None):
    idx = range(len(A)) if idx is None else idx
    return array(typecode(F), (div_exact(F, A[i], B[i], mode) for i in idx))


def subsample(n, k, rng):
    return sorted(rng.sample(range(n), k)) if n > k else list(range(n))


# ---------------------------------------------------------------------------------------
# test sets: each is a function returning two parallel arrays (A, B) of operand patterns
# ---------------------------------------------------------------------------------------

def specials(F):
    """Special and boundary operands of format F, both signs: every datum class."""
    t, w = F.t, F.w
    ones = 2 ** w - 1
    pos = {0, ones << t,                                   # +0, +inf
           (ones << t) | (1 << (t - 1)),                   # canonical qNaN
           (ones << t) | (2 ** t - 1)}                     # qNaN with all payload bits
    if t >= 2:
        pos |= {(ones << t) | 1, (ones << t) | (2 ** (t - 1) - 1)}   # sNaNs
    for T in (1, 2, 3, 2 ** (t - 1), 2 ** t - 2, 2 ** t - 1):        # subnormals
        if 0 < T < 2 ** t:
            pos.add(T)
    pos |= {1 << i for i in range(t)}                      # subnormal powers of two
    pos |= {E << t for E in range(1, ones)}                # normal powers of two
    for E in (1, F.bias - 1, F.bias, F.bias + 1, ones - 1):  # extremes, 1 +- ulp
        for T in (1, 2 ** t - 1, 2 ** (t - 1), 2 ** t - 2):
            if 0 <= T < 2 ** t and 1 <= E < ones:
                pos.add((E << t) | T)
    if F.k >= 16:                                          # non-dyadic significands
        for E in (F.bias, F.bias + 1):
            for num, den in ((1, 3), (2, 3), (1, 5), (1, 7), (5, 7)):
                pos.add((E << t) | (num * 2 ** t // den))
    sign = 1 << (F.k - 1)
    return sorted(pos | {x | sign for x in pos})


def cross(F, xs, ys):
    tc = typecode(F)
    A = array(tc, (x for x in xs for _ in ys))
    B = array(tc, (y for _ in xs for y in ys))
    return A, B


def with_signs(F, rng, gen):
    """Pairs from `gen` (magnitude patterns) with independent random sign bits."""
    tc = typecode(F)
    A, B = array(tc), array(tc)
    s = F.k - 1
    for a, b in gen:
        r = rng.getrandbits(2)
        A.append(a | (r & 1) << s)
        B.append(b | (r >> 1) << s)
    return A, B


def exp_block(F, rng, Ea, Eb):
    """All trailing-significand pairs with biased exponents Ea, Eb (E = 0: subnormals)."""
    t = F.t
    ta = range(1, 2 ** t) if Ea == 0 else range(2 ** t)
    tb = range(1, 2 ** t) if Eb == 0 else range(2 ** t)
    return with_signs(F, rng, ((Ea << t | x, Eb << t | y) for x in ta for y in tb))


def ties(F, rng, limit=None):
    """Pairs whose exact quotient is o2 * 2^(qmin - s), o2 odd: for s = 1 an exact rounding
    tie between two adjacent subnormals, s = 2, 3 quarter/eighth points, s = 0 exact.
    (For division, exact ties can only occur in the subnormal range.)"""
    out = []
    qmin = F.emin - F.t
    odd = range(1, 2 ** F.p, 2)
    for o1 in odd:
        for o2 in odd:
            if o1 * o2 >= 2 ** F.p:
                break
            for eb in (qmin, qmin + 3, -F.t, -F.t + 5, F.emax - F.t - 2):
                bmag = Fraction(o1) * Fraction(2) ** eb
                for s in (0, 1, 2, 3):
                    amag = Fraction(o2) * Fraction(2) ** (qmin - s) * bmag
                    try:
                        out.append((F.encode(0, amag), F.encode(0, bmag)))
                    except (KeyError, AssertionError):
                        pass
    if limit is not None and len(out) > limit:
        out = rng.sample(out, limit)
    return with_signs(F, rng, out)


def uniform(F, rng, n):
    tc = typecode(F)
    return array(tc, (rng.getrandbits(F.k) for _ in range(n))), \
        array(tc, (rng.getrandbits(F.k) for _ in range(n)))


B16_EXP_PAIRS = [(30, 14), (30, 15), (15, 15), (1, 14), (1, 15), (1, 16), (5, 25), (1, 25),
                 (1, 26)]


def b16_sets(quick):
    """[(name, thunk)] for binary16. Full: about 33 million vectors."""
    F = oracle.BINARY16
    rng = random.Random(20261027)
    sp = specials(F)
    allp = range(2 ** 16)
    sets = [("S0 special / special", lambda: cross(F, sp, sp)),
            ("S1 every x / special", lambda: cross(F, allp, sp)),
            ("S1 special / every y", lambda: cross(F, sp, allp))]
    for Ea, Eb in B16_EXP_PAIRS:
        sets.append((f"S2 all T, E=({Ea},{Eb})", lambda Ea=Ea, Eb=Eb: exp_block(F, rng, Ea, Eb)))
    for Ea, Eb in [(0, 1), (0, 14), (0, 15), (0, 16), (0, 25), (0, 30),
                   (1, 0), (15, 0), (16, 0), (29, 0), (30, 0), (0, 0)]:
        sets.append((f"S3 all T, E=({Ea},{Eb})", lambda Ea=Ea, Eb=Eb: exp_block(F, rng, Ea, Eb)))
    sets.append(("S4 constructed ties", lambda: ties(F, rng)))
    sets.append(("S5 uniform random", lambda: uniform(F, rng, 5_000_000)))
    if quick:
        keep = {"S0 special / special", "S1 every x / special", "S2 all T, E=(30,15)",
                "S3 all T, E=(0,15)", "S4 constructed ties"}
        sets = [s for s in sets if s[0] in keep]
        sets.append(("S5 uniform random", lambda: uniform(F, rng, 200_000)))
    return F, sets


# ---------------------------------------------------------------------------------------
# groups
# ---------------------------------------------------------------------------------------

def group_oracle(lean, quick):
    """Oracle A's decoder/encoder against CPython's struct on binary16 and binary32."""
    import math

    def check(F, fmt, xs, label):
        bad = 0
        for x in xs:
            hw = struct.unpack(fmt, x.to_bytes(F.k // 8, "little"))[0]
            d = F.decode(x)
            if d[0] == "nan":
                ok = math.isnan(hw)
            elif d[0] == "inf":
                ok = math.isinf(hw) and (hw < 0) == bool(d[1])
            else:
                ok = abs(hw) == float(d[2]) and math.copysign(1, hw) == (-1 if d[1] else 1) \
                    and F.encode(d[1], d[2]) == x
            bad += not ok
        SUMMARY.append((label, "A = struct", "-", len(xs), bad))
        log(f"  [{'ok' if not bad else 'MISMATCH'}] {label}: {len(xs)} patterns, {bad} mismatches")
        if bad:
            FAILURES.append((label, "-", "A", "struct", bad))

    check(oracle.BINARY16, "<e", range(2 ** 16), "binary16 decode/encode vs struct 'e'")
    rng = random.Random(32)
    xs = specials(oracle.BINARY32) + [rng.getrandbits(32) for _ in range(200_000)]
    check(oracle.BINARY32, "<f", xs, "binary32 decode/encode vs struct 'f'")


TOY_FORMATS = [(2, 2), (2, 3), (3, 2), (2, 4), (3, 3), (4, 2), (3, 4), (4, 3), (2, 6),
               (4, 4), (3, 5), (5, 3)]


def group_toy(lean, quick):
    """Every pair of bit patterns of small formats, all five modes: spec = A; RNE: = core."""
    for w, p in (TOY_FORMATS[:5] if quick else TOY_FORMATS):
        F = Fmt(w, p)
        A, B = cross(F, range(2 ** F.k), range(2 ** F.k))
        name = f"toy w={w} p={p} all pairs"
        for mode in MODES:
            got = lean.eval("spec", F, mode, A, B, "toy")
            compare(name, F, mode, A, B, "spec", got, "A", oracle_A(F, mode, A, B))
            if mode == "rne":
                compare(name, F, mode, A, B, "spec", got, "core",
                        lean.eval("core", F, mode, A, B, "toy"))


def group_b16(lean, quick):
    F, sets = b16_sets(quick)
    rng = random.Random(7)
    total = 0
    for name, thunk in sets:
        A, B = thunk()
        total += len(A)
        got = lean.eval("spec", F, "rne", A, B, "b16")
        compare("b16 " + name, F, "rne", A, B, "spec", got, "core",
                lean.eval("core", F, "rne", A, B, "b16"))
        compare("b16 " + name, F, "rne", A, B, "spec", got, "B",
                array("H", (div_hw16(a, b) for a, b in zip(A, B))))
        idx = subsample(len(A), 4_000 if quick else 40_000, rng)
        compare("b16 " + name + " [sample]", F, "rne", array("H", (A[i] for i in idx)),
                array("H", (B[i] for i in idx)), "spec", array("H", (got[i] for i in idx)),
                "A", oracle_A(F, "rne", A, B, idx))
    log(f"  binary16 roundTiesToEven: {total} vectors, each checked against core and B")


def group_b16modes(lean, quick):
    """All five modes on samples of every binary16 set (all constructed ties): spec = A."""
    F, sets = b16_sets(quick)
    rng = random.Random(11)
    A, B = array("H"), array("H")
    for name, thunk in sets:
        a, b = thunk()
        idx = range(len(a)) if name[:2] in ("S0", "S4") else \
            subsample(len(a), 2_000 if quick else 40_000, rng)
        A += array("H", (a[i] for i in idx))
        B += array("H", (b[i] for i in idx))
    for mode in MODES:
        got = lean.eval("spec", F, mode, A, B, "b16m")
        compare("b16 S1-S5 samples + all ties", F, mode, A, B, "spec", got, "A",
                oracle_A(F, mode, A, B))
    tA, tB = ties(F, random.Random(5))
    rne = lean.eval("spec", F, "rne", tA, tB, "b16t")
    rna = lean.eval("spec", F, "rna", tA, tB, "b16t")
    log(f"  S4: {sum(x != y for x, y in zip(rne, rna))} of {len(tA)} constructed vectors round "
        f"differently under roundTiesToEven and roundTiesToAway (exact ties are exercised)")


def b32_ties(F, rng, n):
    """Random exact subnormal ties and near-ties for binary32."""
    out = []
    qmin = F.emin - F.t
    while len(out) < n:
        o1 = rng.randrange(1, 2 ** 12, 2)
        o2 = rng.randrange(1, max(2, 2 ** F.p // o1), 2)
        eb = rng.choice((qmin, qmin + 7, -F.t, 0, F.emax - F.t - 1))
        s = rng.choice((0, 1, 1, 2, 3))
        bmag = Fraction(o1) * Fraction(2) ** eb
        amag = Fraction(o2) * Fraction(2) ** (qmin - s) * bmag
        try:
            out.append((F.encode(0, amag), F.encode(0, bmag)))
        except AssertionError:
            pass
    return with_signs(F, rng, out)


def group_b32(lean, quick):
    F = oracle.BINARY32
    rng = random.Random(3232)
    sp = specials(F)
    n = 2_000 if quick else 60_000

    def boundary():
        def gen():
            for Ea, Eb in ((254, 126), (254, 127), (127, 127), (1, 126), (1, 127), (1, 128),
                           (10, 150), (1, 149), (1, 150), (0, 127), (0, 100), (200, 0), (0, 0)):
                for _ in range(n):
                    yield (Ea << 23 | rng.getrandbits(23), Eb << 23 | rng.getrandbits(23))
        return with_signs(F, rng, gen())

    sets = [("specials x specials", lambda: cross(F, sp, sp)),
            ("uniform random", lambda: uniform(F, rng, 20_000 if quick else 1_000_000)),
            ("boundary exponents", boundary),
            ("constructed ties", lambda: b32_ties(F, rng, 3_000 if quick else 100_000))]
    for name, thunk in sets:
        A, B = thunk()
        got = lean.eval("spec", F, "rne", A, B, "b32")
        compare("b32 " + name, F, "rne", A, B, "spec", got, "core",
                lean.eval("core", F, "rne", A, B, "b32"))
        compare("b32 " + name, F, "rne", A, B, "spec", got, "B",
                array("I", (div_hw32(a, b) for a, b in zip(A, B))))
        idx = subsample(len(A), 3_000 if quick else 40_000, rng)
        sA, sB = array("I", (A[i] for i in idx)), array("I", (B[i] for i in idx))
        for mode in MODES:
            g = got if mode == "rne" else lean.eval("spec", F, mode, sA, sB, "b32")
            g = array("I", (g[i] for i in idx)) if mode == "rne" else g
            compare("b32 " + name + " [sample]", F, mode, sA, sB, "spec", g, "A",
                    oracle_A(F, mode, sA, sB))


# ---- mutation self-test -----------------------------------------------------------------

def mutants(F):
    """Deliberately wrong division functions, each a classic divider bug."""
    sbit = F.k - 1

    def finite_nonzero(d):
        return d[0] == "num" and d[2] != 0

    def ftz(a, b, mode):                     # flush subnormal results to zero
        r = div_exact(F, a, b, mode)
        S, E, T = F.fields(r)
        return S << sbit if E == 0 else r

    def ties_away(a, b, mode):               # ties away from zero instead of to even
        return div_exact(F, a, b, "rna" if mode == "rne" else mode)

    def zero_by_zero_inf(a, b, mode):        # 0/0 -> inf (x/0 tested before 0/0)
        A, B = F.decode(a), F.decode(b)
        if A[0] == B[0] == "num" and A[2] == 0 and B[2] == 0:
            return F.encode(A[1] ^ B[1], "inf")
        return div_exact(F, a, b, mode)

    def inf_by_zero_nan(a, b, mode):         # inf/0 treated as invalid
        A, B = F.decode(a), F.decode(b)
        if A[0] == "inf" and B[0] == "num" and B[2] == 0:
            return F.canonical_nan
        return div_exact(F, a, b, mode)

    def nan_sign(a, b, mode):                # NaN result carries the XOR of operand signs
        r = div_exact(F, a, b, mode)
        return r | ((a ^ b) >> sbit & 1) << sbit if r == F.canonical_nan else r

    def nan_payload(a, b, mode):             # propagate the first NaN operand, quietened
        for x in (a, b):
            if F.decode(x)[0] == "nan":
                return x | 1 << (F.t - 1)
        return div_exact(F, a, b, mode)

    def overflow_maxfinite(a, b, mode):      # RNE overflow delivers the largest finite number
        r = div_exact(F, a, b, mode)
        A, B = F.decode(a), F.decode(b)
        if finite_nonzero(A) and finite_nonzero(B) and F.decode(r)[0] == "inf":
            return F.encode(F.decode(r)[1], F.max_finite)
        return r

    def zero_sign_plus(a, b, mode):          # zero results always +0
        r = div_exact(F, a, b, mode)
        return 0 if r == 1 << sbit else r

    def no_sticky(a, b, mode):               # round from the guard bit only (sticky dropped)
        A, B = F.decode(a), F.decode(b)
        if not (finite_nonzero(A) and finite_nonzero(B)):
            return div_exact(F, a, b, mode)
        q = A[2] / B[2]
        half = Fraction(2) ** (max(oracle._floor_log2(q), F.emin) - F.p)
        n = q / half
        q2 = (n.numerator // n.denominator) * half
        r = oracle.round_exact(F, A[1] ^ B[1], q2, mode) if q2 > 0 else Fraction(0)
        return F.encode(A[1] ^ B[1], r)

    def emin_off_by_one(a, b, mode):         # gradual underflow starts one binade too high
        G = Fmt(F.w, F.p)
        G.emin = F.emin + 1
        A, B = F.decode(a), F.decode(b)
        if not (finite_nonzero(A) and finite_nonzero(B)):
            return div_exact(F, a, b, mode)
        try:
            return F.encode(A[1] ^ B[1], oracle.round_exact(G, A[1] ^ B[1], A[2] / B[2], mode))
        except KeyError:
            return -1

    return {"flush-to-zero": ftz, "ties away instead of even": ties_away,
            "0/0 -> inf": zero_by_zero_inf, "inf/0 -> NaN": inf_by_zero_nan,
            "NaN sign = XOR": nan_sign, "NaN payload propagated": nan_payload,
            "RNE overflow -> max finite": overflow_maxfinite, "zero result always +0": zero_sign_plus,
            "no sticky bit": no_sticky, "subnormal threshold off by one": emin_off_by_one}


def group_mutants(lean, quick):
    """Each mutant must disagree with the spec somewhere on (samples of) the binary16 sets."""
    F, sets = b16_sets(True)
    rng = random.Random(99)
    A, B = array("H"), array("H")
    for name, thunk in sets:
        a, b = thunk()
        idx = range(len(a)) if name[:2] in ("S0", "S4") else subsample(len(a), 10_000, rng)
        A += array("H", (a[i] for i in idx))
        B += array("H", (b[i] for i in idx))
    got = lean.eval("spec", F, "rne", A, B, "mut")
    for mname, fn in mutants(F).items():
        diff = sum(fn(a, b, "rne") != g for a, b, g in zip(A, B, got))
        SUMMARY.append((f"mutant: {mname}", "caught", "rne", len(A), 0 if diff else "MISSED"))
        log(f"  [{'ok' if diff else 'MISSED'}] mutant {mname!r}: differs from the spec on "
            f"{diff} of {len(A)} vectors")
        if not diff:
            FAILURES.append(("mutant " + mname, "rne", "mutant", "spec", 0))


GROUPS = ["oracle", "toy", "b16", "b16modes", "b32", "mutants"]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", default=os.environ.get(
        "FPSPEC_OUT", os.path.join(tempfile.gettempdir(), "fpspec_out")))
    ap.add_argument("--lean-wrap", default=os.environ.get("LEAN_WRAP", ""))
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--only", default=",".join(GROUPS))
    ap.add_argument("--no-build", action="store_true")
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    log(f"python {sys.version.split()[0]}  out={args.out}  quick={args.quick}")
    lean = Lean(args.out, args.lean_wrap)
    if not args.no_build:
        lean.build()
    t0 = time.time()
    for g in args.only.split(","):
        log(f"== {g}")
        t = time.time()
        globals()["group_" + g](lean, args.quick)
        log(f"   ({time.time() - t:.0f}s)")
    log(f"== summary ({time.time() - t0:.0f}s)")
    for name, what, mode, n, bad in SUMMARY:
        log(f"  {name:<44} {what:<14} {mode:<4} {n:>9}  {bad}")
    log(f"  spec evaluations: {lean.evals}")
    if FAILURES:
        log(f"FAILED: {len(FAILURES)} comparisons with mismatches or missed mutants")
        return 1
    log("ALL OK: 0 mismatches, every mutant caught")
    return 0


if __name__ == "__main__":
    sys.exit(main())
