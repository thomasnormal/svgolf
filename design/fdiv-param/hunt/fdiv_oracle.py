"""Exact IEEE-754-style division for ANY format (w = exponent bits >= 2, p = precision incl. the implicit bit >= 2).
Independent of the repository's oracle (exact rationals; no floating point): round to nearest, ties to even,
full subnormals, overflow to infinity, every NaN result is the canonical quiet NaN (sign 0, exponent all ones,
fraction MSB set, rest 0), as the svGolf `fdiv` task specifies.  Operands are the w+p-bit patterns."""
from fractions import Fraction


def fmt(w, p):
    t = p - 1
    bias = (1 << (w - 1)) - 1
    return dict(w=w, p=p, t=t, bias=bias, emax=bias, emin=1 - bias, k=w + p)


def decode(F, x):
    w, t = F["w"], F["t"]
    s = (x >> (w + t)) & 1
    e = (x >> t) & ((1 << w) - 1)
    f = x & ((1 << t) - 1)
    return s, e, f


def classify(F, x):
    s, e, f = decode(F, x)
    emaxfield = (1 << F["w"]) - 1
    if e == emaxfield:
        return "nan" if f else "inf"
    if e == 0:
        return "zero" if f == 0 else "sub"
    return "norm"


def value(F, x):
    """exact rational value of a finite pattern (sign included)"""
    s, e, f = decode(F, x)
    t, bias = F["t"], F["bias"]
    if e == 0:
        v = Fraction(f, 1 << t) * Fraction(2) ** F["emin"]
    else:
        v = (1 + Fraction(f, 1 << t)) * Fraction(2) ** (e - bias)
    return -v if s else v


def qnan(F):
    return ((1 << F["w"]) - 1) << F["t"] | (1 << (F["t"] - 1))


def pack_inf(F, s):
    return (s << (F["w"] + F["t"])) | (((1 << F["w"]) - 1) << F["t"])


def round_rne(F, q):
    """round the positive rational q > 0 to the nearest representable magnitude, ties to even; returns the
    pattern WITHOUT the sign bit (overflow gives the infinity pattern)."""
    t, p, emin, emax = F["t"], F["p"], F["emin"], F["emax"]
    # find e with 2^e <= q < 2^(e+1)
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    elif Fraction(2) ** (e + 1) <= q:
        e += 1
    e = max(e, emin)                 # subnormal range shares the exponent emin
    ulp = Fraction(2) ** (e - t)     # spacing at this exponent
    m = q / ulp                      # rational number of ulps
    n = m.numerator // m.denominator
    r = m - n
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and n % 2 == 1):
        n += 1
    # n ulps at exponent e; renormalize if it carried
    if n >= (1 << p):                # n == 2^p: carry into the next binade
        n >>= 1
        e += 1
    if e > emax:
        return ((1 << F["w"]) - 1) << t
    if n < (1 << t):                 # subnormal or zero (e == emin and no implicit bit)
        return n
    return ((e + F["bias"]) << t) | (n - (1 << t))


def fdiv(w, p, a, b):
    F = fmt(w, p)
    ca, cb = classify(F, a), classify(F, b)
    sa, _, _ = decode(F, a)
    sb, _, _ = decode(F, b)
    s = sa ^ sb
    if ca == "nan" or cb == "nan":
        return qnan(F)
    if ca == "inf":
        return qnan(F) if cb == "inf" else pack_inf(F, s)
    if cb == "inf":
        return s << (w + F["t"])
    if cb == "zero":
        return qnan(F) if ca == "zero" else pack_inf(F, s)
    if ca == "zero":
        return s << (w + F["t"])
    q = abs(value(F, a)) / abs(value(F, b))
    mag = round_rne(F, q)
    return (s << (w + F["t"])) | mag


if __name__ == "__main__":
    import random, sys, importlib.util, os
    REPO = os.path.join(os.environ["LEAN_SURFACES"], "svgolf")
    sp = importlib.util.spec_from_file_location("o", REPO + "/spec/validate/oracle.py")
    o = importlib.util.module_from_spec(sp); sp.loader.exec_module(o)
    rnd = random.Random(7)
    bad = 0
    for _ in range(200000):
        a = rnd.getrandbits(16); b = rnd.getrandbits(16)
        if rnd.random() < 0.3:   # bias toward specials and subnormals
            a = rnd.choice([0, 0x8000, 0x7C00, 0xFC00, 0x7E00, 1, 0x3FF, 0x400, 0x7BFF]) ^ (rnd.getrandbits(3) if rnd.random() < .5 else 0)
        if fdiv(5, 11, a, b) != o.div_hw16(a, b):
            bad += 1
            if bad < 5: print("MISMATCH", hex(a), hex(b), hex(fdiv(5, 11, a, b)), hex(o.div_hw16(a, b)))
    print("binary16 vs the repository oracle on 200000 random/special pairs: mismatches =", bad)
