#!/usr/bin/env python3
"""Python model of the t0 datapath + checks of the intermediate invariants used by the G1 decomposition (M3a..M3f)."""
import random, sys
from fractions import Fraction

def fields(a): return (a >> 15) & 1, (a >> 10) & 31, a & 1023
def sig_q(a):
    s, e, f = fields(a)
    return (f if e == 0 else 1024 + f), (1 if e == 0 else e) - 25

def norm(m):
    za8 = (m >> 3) == 0; n1 = (m << 8) % 2048 if za8 else m
    za4 = (n1 >> 7) == 0; n2 = (n1 << 4) % 2048 if za4 else n1
    za2 = (n2 >> 9) == 0; n3 = (n2 << 2) % 2048 if za2 else n2
    za1 = (n3 >> 10) == 0; n4 = (n3 << 1) % 2048 if za1 else n3
    return n4, 8*za8 + 4*za4 + 2*za2 + za1

def datapath(a, b):
    sa, ea, fa = fields(a); sb, eb, fb = fields(b)
    ma = (1024 if ea else 0) + fa; mb = (1024 if eb else 0) + fb
    xa = ea if ea else 1; xb = eb if eb else 1
    na, lza = norm(ma); nb, lzb = norm(mb)
    # restoring divider, 13 steps
    rem = na; qq = 0
    for i in range(13):
        bit = 1 if rem >= nb else 0
        qq |= bit << (12 - i)
        rem = ((rem - nb) << 1) if bit else (rem << 1)
    adj = 0 if (qq >> 12) & 1 else 1
    qm = (qq >> 1) if (qq >> 12) & 1 else (qq & 0xFFF)
    st0 = 1 if (((qq >> 12) & 1) and (qq & 1)) or rem != 0 else 0
    eoff = (xa + lzb + 47 - xb - lza - adj)
    assert 0 <= eoff < 128
    ovf = eoff >= 63; nrm = eoff >= 33
    dsh = 33 - eoff if not nrm else 0
    sh = 0 if nrm else (12 if dsh >= 12 else dsh)
    qs = qm >> sh
    st1 = st0 | (((qs << sh) & 0xFFF) != qm)
    rb = qs & 1; inc = rb & (st1 | ((qs >> 1) & 1))
    ef = (eoff & 31) if nrm else 0
    mag = ((ef << 10) | ((qs >> 1) & 1023)) + inc
    s = sa ^ sb
    return dict(s=s, ma=ma, mb=mb, xa=xa, xb=xb, na=na, nb=nb, lza=lza, lzb=lzb, qq=qq, rem13=rem, adj=adj, qm=qm,
                st0=st0, eoff=eoff, ovf=ovf, nrm=nrm, sh=sh, dsh=dsh, qs=qs, st1=st1, inc=inc, mag=mag)

def F(a, b):
    sa, ea, fa = fields(a); sb, eb, fb = fields(b)
    s = sa ^ sb
    a_nan = ea == 31 and fa; b_nan = eb == 31 and fb
    a_inf = ea == 31 and not fa; b_inf = eb == 31 and not fb
    a_zero = ea == 0 and not fa; b_zero = eb == 0 and not fb
    if a_nan or b_nan or (a_inf and b_inf) or (a_zero and b_zero): return 0x7E00
    if a_inf or b_zero: return (s << 15) | 0x7C00
    if b_inf or a_zero: return s << 15
    d = datapath(a, b)
    if d['ovf']: return (s << 15) | 0x7C00
    return (s << 15) | d['mag']

def cert16(a, b, c):
    """Spec's cert16 (SpecFacts.lean) in Python."""
    ma, qa = sig_q(a); mb, qb = sig_q(b)
    e = qa - qb + 24
    N = ma * 2 ** max(e, 0); D = mb * 2 ** max(-e, 0)
    sc, E, T = fields(c)
    thr = D * 4095 * 2 ** 28
    j = E - 1
    u = T if E == 0 else (1024 + T) * 2 ** j
    up = 2 ** j if E >= 1 else 2 ** (-1) if False else (2 ** j if j >= 0 else 1)
    # Lean: j := E - 1 on Nat (truncated subtraction): E=0 -> 0
    jj = max(E - 1, 0)
    u = T if E == 0 else (1024 + T) * 2 ** jj
    up = 2 ** jj
    dn = 2 ** (jj - 1) if (E >= 2 and T == 0) else 2 ** jj
    even = T % 2 == 0
    if sc != (fields(a)[0] ^ fields(b)[0]): return False
    if E == 31: return T == 0 and thr <= N
    if not (N < thr): return False
    lo = (u == 0) or ((D * (2*u - dn) <= 2*N) if even else (D * (2*u - dn) < 2*N))
    hi = (2*N <= D * (2*u + up)) if even else (2*N < D * (2*u + up))
    return lo and hi

def finite_nonzero(x):
    s, e, f = fields(x)
    return e != 31 and not (e == 0 and f == 0)

def check(a, b):
    assert finite_nonzero(a) and finite_nonzero(b)
    d = datapath(a, b)
    # M3a
    assert d['na'] == d['ma'] * 2 ** d['lza'] and 1024 <= d['na'] < 2048 and d['lza'] <= 10
    assert d['nb'] == d['mb'] * 2 ** d['lzb'] and 1024 <= d['nb'] < 2048 and d['lzb'] <= 10
    # M3b
    assert d['qq'] == (2**12 * d['na']) // d['nb'] and d['rem13'] == 2 * ((2**12 * d['na']) % d['nb'])
    assert (d['qq'] >= 4096) == (d['na'] >= d['nb'])
    # M3c
    assert d['eoff'] + d['xb'] + d['lza'] + d['adj'] == d['xa'] + d['lzb'] + 47
    # M3d inputs
    assert 2048 <= d['qm'] <= 4095
    assert d['qm'] == (2 ** (11 + d['adj']) * d['na']) // d['nb']
    exact = (2 ** (11 + d['adj']) * d['na']) % d['nb'] == 0
    assert d['st0'] == (0 if exact else 1)
    # value R = N/D = (qm+f) * 2^(eoff-34)
    ma, qa = sig_q(a); mb, qb = sig_q(b); e = qa - qb + 24
    R = Fraction(ma * 2 ** max(e, 0), mb * 2 ** max(-e, 0))
    Rm = Fraction(2 ** (11 + d['adj']) * d['na'], d['nb']) * Fraction(2) ** (d['eoff'] - 34)
    assert R == Rm
    c = F(a, b)
    assert cert16(a, b, c), (hex(a), hex(b), hex(c))
    return d

random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
n = 0
specials = [0x0001, 0x0002, 0x03FF, 0x0400, 0x0401, 0x3BFF, 0x3C00, 0x3C01, 0x4000, 0x7BFF, 0x7BFE, 0x0200, 0x0100, 0x3555]
vals = [v | s for v in specials for s in (0, 0x8000)]
for a in vals:
    for b in vals:
        check(a, b); n += 1
for _ in range(300000):
    a = random.getrandbits(16); b = random.getrandbits(16)
    if finite_nonzero(a) and finite_nonzero(b):
        check(a, b); n += 1
# exponent-stratified: every pair of exponent fields with random fractions
for ea in range(0, 31):
    for eb in range(0, 31):
        for _ in range(8):
            a = (ea << 10) | random.getrandbits(10); b = (eb << 10) | random.getrandbits(10)
            if finite_nonzero(a) and finite_nonzero(b):
                check(a, b); n += 1
print("checked", n, "finite pairs: all invariants and cert16 hold")
