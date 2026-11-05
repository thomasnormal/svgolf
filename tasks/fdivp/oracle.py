"""Advisory oracle of task `fdivp`: q = a / b in the IEEE 754 binary format with `W` exponent bits and precision `P`
(`W + P`-bit patterns), round to nearest even, every NaN result the canonical quiet NaN, full subnormals
(README.md, task.json `oracle`).

NOT part of the trusted statement (`Spec.lean`, `IEEE754.lean` are): a convenience that lets `check.py` tell a
contestant, before any proof, that their design computes something else. It is an INDEPENDENT implementation of the
spec in exact rational arithmetic (`fractions.Fraction`, no floating point and no code from `spec_validate/`), for ANY
format: `fdiv(w, p, a, b)`. It was compared with the repository's `div_hw16` (binary16) and with the C transliteration
of the Lean spec (`tests/fdivp/validate/`: every pair of every format with `W + P <= 14`, and the pairs of the two
32-bit formats `(5, 11)` x 2 and `(8, 8)`; see README.md, "Validation").

`params` is the point the checker evaluates at (`{"W": 5, "P": 11}`), `inputs` maps the input ports to ints; the result
maps the output ports to ints already masked to their widths.
"""

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


def oracle(params, inputs):
    w, p = params["W"], params["P"]
    return {"q": fdiv(w, p, inputs["a"], inputs["b"]) & ((1 << (w + p)) - 1)}
