#!/usr/bin/env python3.12
"""Bit-exact Python model of the radix-4 SRT core of tests/fdivp/baselines/fdivp_srt.sv, and an exact check of its
selection table (the records of gate S0 in srt_S0.md were produced with it; no dependencies, python3.12).

  table   : the Wally fdivsqrtuslc4cmp thresholds, checked over every (divisor interval, residual estimate) cell with
            exact rationals: the selected digit keeps the next residual in [-8/3 d, 8/3 d] for every residual the
            estimate can stand for (carry-save truncation error in [0, 3/16)), and the estimate never wraps.
  core    : the unrolled core at precision P, bit for bit as the SV writes it (vectors of RW = P + 6 bits, mod 2^RW),
            against qq = floor(2^(P+1) ma / mb), rnz = (2^(P+1) ma mod mb != 0).

usage: srt_model.py table | perturb | exh PMAX | rand PMAX N SEED | worst PMAX N SEED
"""
import sys, random
from fractions import Fraction as Fr

M2 = [12, 14, 16, 17, 18, 20, 22, 23]
M1 = [4, 4, 6, 6, 6, 8, 8, 8]
M0 = [-4, -4, -6, -6, -6, -8, -8, -8]
MM1 = [-13, -14, -16, -17, -18, -20, -22, -23]


def select(y, a):
    """Wally fdivsqrtuslc4cmp: y = the Q4.3 estimate (signed int, units 1/8), a = 3 divisor bits."""
    if y >= M2[a]: return 2
    if y >= M1[a]: return 1
    if y >= M0[a]: return 0
    if y >= MM1[a]: return -1
    return -2


def check_table():
    """Exact check. For divisor interval a (d in [1 + a/8, 1 + (a+1)/8)) and estimate y (w in [y/8, y/8 + 3/16)),
    with |w| <= 8/3 d: the digit q = select(y, a) must give |w - q d| <= 2/3 d. The feasible set is a convex polygon
    (closure taken; the check at the closure is sufficient), so the two linear conditions are checked at its vertices."""
    bad = 0; cells = 0
    for a in range(8):
        dlo, dhi = 1 + Fr(a, 8), 1 + Fr(a + 1, 8)
        for y in range(-64, 64):
            wlo, whi = Fr(y, 8), Fr(y, 8) + Fr(3, 16)
            # half-planes: d >= dlo, d <= dhi, w >= wlo, w <= whi, w <= 8/3 d, w >= -8/3 d
            lines = [(0, 1, dlo), (0, 1, dhi), (1, 0, wlo), (1, 0, whi), (1, Fr(-8, 3), 0), (1, Fr(8, 3), 0)]
            # each line: cw * w + cd * d = c
            def inside(w, d):
                return (dlo <= d <= dhi and wlo <= w <= whi and -Fr(8, 3) * d <= w <= Fr(8, 3) * d)
            verts = set()
            for i in range(len(lines)):
                for j in range(i + 1, len(lines)):
                    a1, b1, c1 = lines[i]; a2, b2, c2 = lines[j]
                    det = a1 * b2 - a2 * b1
                    if det == 0: continue
                    w = (c1 * b2 - c2 * b1) / det; d = (a1 * c2 - a2 * c1) / det
                    if inside(w, d): verts.add((w, d))
            if not verts: continue
            cells += 1
            q = select(y, a)
            for (w, d) in verts:
                if not (-Fr(2, 3) * d <= w - q * d <= Fr(2, 3) * d):
                    bad += 1
                    print(f"BAD a={a} y={y} q={q} vertex w={w} d={d} w-qd={w - q * d} bound {Fr(2, 3) * d}")
                    break
            # no wrap: the 8-bit sum is a Q4.4 two's-complement value in [-8, 8)
            if any(not (-8 <= w - Fr(3, 16) and w < 8) for (w, d) in verts):
                bad += 1; print(f"WRAP a={a} y={y}")
    print(f"table: {cells} feasible cells, {bad} bad")
    return bad


def core(P, ma, mb):
    """The SV core, bit for bit. Returns (qq, rnz)."""
    H = (P + 2) // 2; E = 2 * H - P - 1; N = H + 1
    RW = P + 6; MASK = (1 << RW) - 1; QW = P + 2; QMASK = (1 << QW) - 1
    dv = (mb << 3) & MASK                       # {3'b000, mb, 3'b000}
    d2 = (mb << 4) & MASK                       # {2'b00, mb, 4'b0000}
    nd1 = (((~mb) & ((1 << P) - 1)) << 3) | (0b111 << (P + 3))      # {3'b111, ~mb, 3'b000}
    nd2 = (((~mb) & ((1 << P) - 1)) << 4) | (0b11 << (P + 4)) | 0b1000  # {2'b11, ~mb, 4'b1000}
    a = (dv >> (P - 1)) & 7                     # dv[P+1:P-1]
    ws = ((ma << 3) >> E) & MASK                # {3'b000, ma, 3'b000} >> E
    wc = 0
    Q, QM = 0, QMASK
    for k in range(N):
        est = (((ws >> (P - 2)) & 0xFF) + ((wc >> (P - 2)) & 0xFF)) & 0xFF   # top 8 bits [P+5:P-2], summed mod 256
        y7 = est >> 1                                                       # Q4.3, 7 bits two's complement
        y = y7 - 128 if y7 >= 64 else y7
        q = select(y, a)
        mm = {2: nd2, 1: nd1, 0: 0, -1: dv, -2: d2}[q]
        cin = 1 if q > 0 else 0
        sm = ws ^ wc ^ mm
        cy = (ws & wc) | (ws & mm) | (wc & mm)
        ws = (sm << 2) & MASK
        wc = ((((cy >> 3) & ((1 << (RW - 6)) - 1)) << 6) | (cin << 5)) & MASK  # {cy[RW-4:3], cin, 5'b00000}
        if q >= 0:
            Qn = ((Q << 2) | q) & QMASK
            QMn = ((Q << 2) | (q - 1)) & QMASK if q > 0 else ((QM << 2) | 3) & QMASK
        else:
            Qn = ((QM << 2) | (4 + q)) & QMASK
            QMn = ((QM << 2) | (3 + q)) & QMASK
        Q, QM = Qn, QMn
    rsum = (ws + wc) & MASK
    neg = rsum >> (RW - 1)
    qq = QM if neg else Q
    return qq, int(rsum != 0)


def ref(P, ma, mb):
    n = ma << (P + 1)
    return n // mb, int(n % mb != 0)


def exh(pmax):
    tot = bad = 0
    for P in range(2, pmax + 1):
        b = 0
        for ma in range(1 << (P - 1), 1 << P):
            for mb in range(1 << (P - 1), 1 << P):
                if core(P, ma, mb) != ref(P, ma, mb):
                    b += 1
                    if b <= 3: print(f"MISMATCH P={P} ma={ma} mb={mb} core={core(P, ma, mb)} ref={ref(P, ma, mb)}")
        tot += 1 << (2 * P - 2); bad += b
        print(f"P={P}: {1 << (2 * P - 2)} pairs, {b} mismatches", flush=True)
    print(f"exh P<={pmax}: {tot} pairs, {bad} mismatches")
    return bad


def rnd(pmax, n, seed, worst=False):
    rg = random.Random(seed); bad = 0
    for P in range(2, pmax + 1):
        b = 0
        for _ in range(n):
            if worst:
                # near-boundary pairs: mb near the divisor-interval edges, ma near multiples making the residual extreme
                a = rg.randrange(8)
                lo = (8 + a) << (P - 1) >> 3 if P >= 4 else 1 << (P - 1)
                mb = min(max(lo + rg.choice([0, 1, 2, -1, -2]) + rg.choice([0, (1 << max(P - 4, 0)) - 1]), 1 << (P - 1)), (1 << P) - 1)
                ma = rg.choice([mb, (1 << P) - 1, 1 << (P - 1), (2 * mb) // 3, (4 * mb) // 3, mb - 1, mb + 1, rg.randrange(1 << (P - 1), 1 << P)])
                ma = min(max(ma, 1 << (P - 1)), (1 << P) - 1)
            else:
                ma = rg.randrange(1 << (P - 1), 1 << P); mb = rg.randrange(1 << (P - 1), 1 << P)
            if core(P, ma, mb) != ref(P, ma, mb):
                b += 1
                if b <= 3: print(f"MISMATCH P={P} ma={ma} mb={mb}")
        bad += b
    print(f"{'worst' if worst else 'rand'} P<={pmax}, {n} per P, seed {seed}: {bad} mismatches")
    return bad


def perturb():
    """The table check is not vacuous: each listed one-constant change is flagged (bad cells > 0), except mks1[5] = 6,
    which Wally's own comment asks about and which is also a valid table."""
    import io, contextlib
    for name, i, v in [("M2", 0, 11), ("M2", 7, 25), ("M1", 0, 2), ("M0", 3, -3), ("MM1", 0, -12), ("MM1", 7, -26),
                       ("M1", 5, 6)]:
        arr = globals()[name]; old = arr[i]; arr[i] = v
        with contextlib.redirect_stdout(io.StringIO()):
            b = check_table()
        arr[i] = old
        print(f"perturb {name}[{i}] {old} -> {v}: {b} bad cells")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "table": sys.exit(1 if check_table() else 0)
    if cmd == "perturb": perturb(); sys.exit(0)
    if cmd == "exh": sys.exit(1 if exh(int(sys.argv[2])) else 0)
    if cmd == "rand": sys.exit(1 if rnd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])) else 0)
    if cmd == "worst": sys.exit(1 if rnd(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), worst=True) else 0)
