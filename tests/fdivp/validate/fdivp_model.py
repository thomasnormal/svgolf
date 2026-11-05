#!/usr/bin/env python3
"""Bit-accurate Python model of the parametric divider tests/fdivp/baselines/fdivp_d1.sv (D1; `model3` is the reference's netlist, tasks/fdivp/reference/fdivp.sv), and two oracles.

model(W, P, a, b): the netlist of fdivp.sv, step for step (normalizer stages, P+2 restoring steps, exponent sum
with an offset, shifter with a sticky bit, increment).  oracle_int: exact integer RNE (independent of the
datapath: rounds the exact quotient in units of the least subnormal).  oracle_frac: tasks/fdivp/spec_validate/oracle.py's
Fraction oracle (the one validated against the Lean spec).
"""
import sys, os

HERE = os.path.dirname(os.path.abspath(__file__))


def clog2(n):
    return 0 if n <= 1 else (n - 1).bit_length()


def consts(W, P):
    emax = (1 << (W - 1)) - 1
    # OFF: a multiple of 2^W with OFF >= 2^(W-1) + P - 2 (E_res = xa - xb + lzb - lza + emax - adj >= -2^(W-1) - P + 2)
    offm = ((1 << (W - 1)) + P - 2 + (1 << W) - 1) // (1 << W)
    offm = max(offm, 1)
    OFF = offm << W
    emax_eoff = (1 << W) - 3 + (P - 1) + emax + OFF           # largest eoff
    EW = clog2(emax_eoff + 1)
    NS = clog2(P)                                              # normalizer stages
    SW = clog2(P + 2)                                          # shifter stages (sh in 0..P+1)
    return dict(emax=emax, OFF=OFF, EW=EW, NS=NS, SW=SW, K=W + P, T=P - 1)


def model(W, P, a, b):
    c = consts(W, P)
    K, T, OFF, EW, NS, SW, emax = c['K'], c['T'], c['OFF'], c['EW'], c['NS'], c['SW'], c['emax']
    mW = (1 << W) - 1

    def unpack(x):
        s = (x >> (K - 1)) & 1
        e = (x >> T) & mW
        f = x & ((1 << T) - 1)
        return s, e, f

    sa, ea, fa = unpack(a)
    sb, eb, fb = unpack(b)
    s = sa ^ sb
    a_nan = ea == mW and fa != 0
    b_nan = eb == mW and fb != 0
    a_inf = ea == mW and fa == 0
    b_inf = eb == mW and fb == 0
    a_zero = ea == 0 and fa == 0
    b_zero = eb == 0 and fb == 0
    nza, nzb = ea != 0, eb != 0
    ma = (int(nza) << T) | fa
    mb = (int(nzb) << T) | fb
    xa = ea if nza else 1
    xb = eb if nzb else 1

    def normalize(m):
        v, lz = m, 0
        for j in range(NS - 1, -1, -1):
            w = 1 << j
            top = (v >> (P - w)) & ((1 << w) - 1)          # the top 2^j bits
            z = top == 0
            if z:
                v = (v << w) & ((1 << P) - 1)
                lz |= w
        return v, lz

    na, lza = normalize(ma)
    nb, lzb = normalize(mb)
    # P+2 restoring steps
    nbx = nb                                                  # {1'b0, nb}, P+1 bits
    r = na
    qq = 0
    for k in range(P + 2):
        q = 1 if r >= nbx else 0
        d = (r - nbx) & ((1 << (P + 1)) - 1)
        qq |= q << (P + 1 - k)
        r = ((d if q else r) << 1) & ((1 << (P + 1)) - 1)
    rnz = r != 0
    adj = 1 - ((qq >> (P + 1)) & 1)
    qm = (qq >> 1) if (qq >> (P + 1)) & 1 else qq & ((1 << (P + 1)) - 1)
    st0 = (((qq >> (P + 1)) & 1) & (qq & 1)) | int(rnz)
    mEW = (1 << EW) - 1
    eoff = (xa + lzb + (emax + OFF) - xb - lza - adj) & mEW
    ovf = eoff >= OFF + (1 << W) - 1
    nrm = eoff >= OFF + 1
    dsh = ((OFF + 1) - eoff) & mEW
    big = dsh >= P + 1
    sh = 0 if nrm else ((P + 1) if big else dsh & ((1 << SW) - 1))
    # shifter with sticky
    qv, t = qm, 0
    for j in range(SW):
        if (sh >> j) & 1:
            lowmask = (1 << (1 << j)) - 1
            t |= int((qv & lowmask) != 0)
            qv >>= (1 << j)
    qs = qv
    st1 = st0 | t
    rb = qs & 1
    inc = rb & (st1 | ((qs >> 1) & 1))
    ef = (eoff & mW) if nrm else 0
    efq = (ef << (P - 1)) | ((qs >> 1) & ((1 << (P - 1)) - 1))
    mag = (efq + inc) & ((1 << (K - 1)) - 1)
    c_nan = a_nan or b_nan or (a_inf and b_inf) or (a_zero and b_zero)
    c_inf = a_inf or b_zero
    c_zero = b_inf or a_zero
    NAN = (mW << T) | (1 << (T - 1))
    w_inf = (s << (K - 1)) | (mW << T)
    w_zero = s << (K - 1)
    w_fin = (s << (K - 1)) | mag
    if c_nan:
        return NAN
    if c_inf:
        return w_inf
    if c_zero:
        return w_zero
    if ovf:
        return w_inf
    return w_fin


def oracle_int(W, P, a, b):
    """Exact RNE quotient, integer arithmetic only: round the quotient in units of the least subnormal."""
    K, T = W + P, P - 1
    emax = (1 << (W - 1)) - 1
    mW = (1 << W) - 1

    def unpack(x):
        return (x >> (K - 1)) & 1, (x >> T) & mW, x & ((1 << T) - 1)

    sa, ea, fa = unpack(a)
    sb, eb, fb = unpack(b)
    NAN = (mW << T) | (1 << (T - 1))
    a_nan, b_nan = ea == mW and fa != 0, eb == mW and fb != 0
    a_inf, b_inf = ea == mW and fa == 0, eb == mW and fb == 0
    a_zero, b_zero = ea == 0 and fa == 0, eb == 0 and fb == 0
    s = sa ^ sb
    if a_nan or b_nan or (a_inf and b_inf) or (a_zero and b_zero):
        return NAN
    INF = (s << (K - 1)) | (mW << T)
    ZERO = s << (K - 1)
    if a_inf or b_zero:
        return INF
    if b_inf or a_zero:
        return ZERO
    siga = fa if ea == 0 else (1 << T) + fa
    sigb = fb if eb == 0 else (1 << T) + fb
    qa = max(ea, 1) - emax - T
    qb = max(eb, 1) - emax - T
    qmin = 1 - emax - T
    e = qa - qb - qmin                                         # quotient in units: siga * 2^e / sigb
    N = siga << max(e, 0)
    D = sigb << max(-e, 0)
    # floor(log2(N/D))
    l = N.bit_length() - D.bit_length()
    while (N << max(-l, 0)) < (D << max(l, 0)):
        l -= 1
    while (N << max(-(l + 1), 0)) >= (D << max(l + 1, 0)):
        l += 1
    # spacing in units: 1 below 2^T units, else 2^(l - T)
    sp = 0 if l < T else l - T                                 # log2 of the spacing
    # M = round(N / (D * 2^sp)) ties to even
    Dn = D << sp
    M, rem = divmod(N, Dn)
    if 2 * rem > Dn or (2 * rem == Dn and (M & 1)):
        M += 1
    # M units (rounded with the exponent range of the binade of the quotient; a carry may move to the next binade, fine)
    M = M << sp
    maxU = ((1 << P) - 1) << ((1 << W) - 3)
    if M > maxU:
        return INF
    if M < (1 << T):
        return (s << (K - 1)) | M
    bl = M.bit_length()
    E = bl - T
    return (s << (K - 1)) | (E << T) | ((M >> (E - 1)) - (1 << T))


_FMTS = {}


_SPEC_ORACLE = []


def spec_oracle():
    """tasks/fdivp/spec_validate/oracle.py, loaded by PATH under its own module name: the task directory also has an
    `oracle.py` (the task's advisory oracle), so `import oracle` through sys.path could load either."""
    if not _SPEC_ORACLE:
        import importlib.util
        path = os.path.normpath(os.path.join(HERE, '..', '..', '..', 'tasks', 'fdivp', 'spec_validate', 'oracle.py'))
        sp = importlib.util.spec_from_file_location("fdivp_spec_validate_oracle", path)
        mod = importlib.util.module_from_spec(sp)
        sys.modules[sp.name] = mod
        sp.loader.exec_module(mod)
        _SPEC_ORACLE.append(mod)
    return _SPEC_ORACLE[0]


def oracle_frac(W, P, a, b):
    O = spec_oracle()
    F = _FMTS.get((W, P))
    if F is None:                      # a Fmt is slow to construct: once per format
        F = _FMTS[(W, P)] = O.Fmt(W, P)
    return O.div_exact(F, a, b, "rne")


def model3(W, P, a, b):
    """Bit-accurate model of fdivp3.sv (D3): linear normalizer, P+2 restoring steps, two's complement exponent
    E = ya - yb + emax - adj (EW = W+P+1 bits), nrm = E >= 1, ovf = E >= 2^W - 1, qs = qm >> dsh (any amount),
    sticky by (qs << dsh) != qm, output by fields."""
    K, T = W + P, P - 1
    EW = W + P + 1
    mEW = (1 << EW) - 1
    mW = (1 << W) - 1
    emax = (1 << (W - 1)) - 1

    def parts(x):
        return (x >> (K - 1)) & 1, (x >> T) & mW, x & ((1 << T) - 1)

    sa, ea, fa = parts(a)
    sb, eb, fb = parts(b)
    s = sa ^ sb
    ea_nz, eb_nz = int(ea != 0), int(eb != 0)
    fa_nz, fb_nz = int(fa != 0), int(fb != 0)
    ea_all, eb_all = int(ea == mW), int(eb == mW)
    c_nan = (ea_all & fa_nz) | (eb_all & fb_nz) | (ea_all & (1 - fa_nz) & eb_all & (1 - fb_nz)) | \
            ((1 - ea_nz) & (1 - fa_nz) & (1 - eb_nz) & (1 - fb_nz))
    c_inf = (ea_all & (1 - fa_nz)) | ((1 - eb_nz) & (1 - fb_nz))
    c_zero = (eb_all & (1 - fb_nz)) | ((1 - ea_nz) & (1 - fa_nz))
    mP = (1 << P) - 1

    def norm(m, x0):
        n, y = m, x0
        for _ in range(P - 1):
            if not (n >> (P - 1)) & 1:
                n = (n << 1) & mP
                y = (y - 1) & mEW
        return n, y

    na, ya = norm((ea_nz << T) | fa, ea if ea_nz else 1)
    nb, yb = norm((eb_nz << T) | fb, eb if eb_nz else 1)
    mP1 = (1 << (P + 1)) - 1
    r, qq = na, 0
    for k in range(P + 2):
        g = int(r >= nb)
        d = (r - nb) & mP1
        qq |= g << (P + 1 - k)
        r = ((d if g else r) << 1) & mP1
    adj = 1 - ((qq >> (P + 1)) & 1)
    qm = (qq >> 1) if (qq >> (P + 1)) & 1 else qq & mP1
    st0 = (((qq >> (P + 1)) & 1) & (qq & 1)) | int(r != 0)
    em = emax
    E = (ya - yb + em - adj) & mEW
    sgn = (E >> (EW - 1)) & 1
    nrm = int((not sgn) and E != 0)
    ovf = int((not sgn) and ((E >> W) & ((1 << (EW - 1 - W)) - 1) != 0 or (E & mW) == mW))
    dsh = 0 if nrm else ((1 - E) & mEW)
    qs = 0 if dsh > P + 1 else qm >> dsh
    st = int(((qs << dsh) & mP1) != qm) if dsh <= P + 1 else int(qm != 0)
    inc = (qs & 1) & (st0 | st | ((qs >> 1) & 1))
    ef = (E & mW) if nrm else 0
    mag = (((ef << (P - 1)) | ((qs >> 1) & ((1 << (P - 1)) - 1))) + inc) & ((1 << (K - 1)) - 1)
    fin = 1 - (c_nan | c_inf | c_zero | ovf)
    hi = mW if (c_nan or c_inf or ((not c_zero) and ovf)) else (0 if c_zero else (mag >> T) & mW)
    top = (c_nan | (fin & ((mag >> (T - 1)) & 1)))
    lo = (mag & ((1 << (T - 1)) - 1)) if fin else 0
    return (((1 - c_nan) & s) << (K - 1)) | (hi << T) | (top << (T - 1)) | lo
