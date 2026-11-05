"""Independent IEEE 754-2019 binary division oracles (Python 3 standard library only).

Two oracles, written without reference to the Lean spec's algorithm:

* Oracle A (`div_exact`) -- exact rational arithmetic with `fractions.Fraction`, any binary
  format, all five rounding-direction attributes. Operands are decoded with the §3.4 formulas
  into real values; the quotient is formed exactly; the result is the representable number
  chosen by searching the binade of the quotient and comparing exact distances to its two
  neighbours; overflow is decided on the value rounded with unbounded exponent range (§7.4)
  and cross-checked against the §4.3.1 threshold sentence. Results are encoded through a
  value -> bit-pattern table built by decoding every pattern (k <= 16), or arithmetically for
  wider formats.

* Oracle B (`div_hw16`, `div_hw32`) -- the machine: CPython's binary64 division (the CPU's
  IEEE divider, roundTiesToEven), then CPython's own binary64 -> binary16 conversion
  (`struct` format 'e', `_PyFloat_Pack2`, round-half-even with gradual underflow) or the C
  cast to float (`struct` format 'f'). roundTiesToEven only.
  Double rounding is innocuous here: a binary64 quotient of two binary16 (resp. binary32)
  operands is correctly rounded to 53 bits, and 53 >= 2*11 + 2 (resp. 2*24 + 2), which is
  the classical bound under which rounding the binary64 quotient again to the narrower
  format equals rounding the exact quotient directly (also for subnormal results: the
  binary64 quotient is never subnormal or overflowing for these operand ranges).

NaN policy, as in the spec: every NaN result is the canonical quiet NaN
(sign 0, exponent all ones, trailing significand 10...0).
"""

import math
import struct
from fractions import Fraction

MODES = ("rne", "rna", "rtp", "rtn", "rtz")


class Fmt:
    """A binary interchange format with exponent-field width w and precision p (IEEE §3.3)."""

    def __init__(self, w, p):
        assert w >= 2 and p >= 2
        self.w, self.p = w, p
        self.t = p - 1                       # trailing significand field width
        self.k = 1 + w + self.t              # storage width
        self.bias = 2 ** (w - 1) - 1
        self.emax = self.bias
        self.emin = 1 - self.emax
        # largest finite magnitude b^emax * (b - b^(1-p))  (§3.3)
        self.max_finite = Fraction(2) ** self.emax * (2 - Fraction(1, 2 ** (p - 1)))
        # overflow threshold of roundTiesToEven: b^emax * (b - 1/2 b^(1-p))  (§4.3.1)
        self.rne_threshold = Fraction(2) ** self.emax * (2 - Fraction(1, 2 ** p))
        self.exp_all_ones = 2 ** w - 1
        self.canonical_nan = (self.exp_all_ones << self.t) | (1 << (self.t - 1))
        self._table = None

    def __repr__(self):
        return f"Fmt(w={self.w}, p={self.p})"

    # ---- decoding (§3.4) ------------------------------------------------------------
    def fields(self, x):
        S = x >> (self.w + self.t)
        E = (x >> self.t) & (2 ** self.w - 1)
        T = x & (2 ** self.t - 1)
        return S, E, T

    def decode(self, x):
        """('nan', signaling) | ('inf', sign) | ('num', sign, Fraction magnitude)."""
        S, E, T = self.fields(x)
        if E == self.exp_all_ones:
            if T != 0:
                return ("nan", (T >> (self.t - 1)) == 0)
            return ("inf", S)
        if E == 0:   # §3.4 (d)/(e): 2^emin * (0 + 2^(1-p) * T)
            mag = Fraction(2) ** self.emin * Fraction(T, 2 ** self.t)
        else:        # §3.4 (c): 2^(E-bias) * (1 + 2^(1-p) * T)
            mag = Fraction(2) ** (E - self.bias) * (1 + Fraction(T, 2 ** self.t))
        return ("num", S, mag)

    # ---- encoding ---------------------------------------------------------------------
    def table(self):
        """{(sign, magnitude): pattern} for every non-NaN pattern (inverts `decode`)."""
        if self._table is None:
            assert self.k <= 16, "table encoding only for k <= 16"
            tab = {}
            for x in range(2 ** self.k):
                d = self.decode(x)
                if d[0] == "num":
                    tab[(d[1], d[2])] = x
                elif d[0] == "inf":
                    tab[(d[1], "inf")] = x
            self._table = tab
        return self._table

    def encode(self, sign, mag):
        """Bit pattern of (-1)^sign * mag, mag a representable Fraction or 'inf'."""
        if self.k <= 16:
            return self.table()[(sign, mag)]
        if mag == "inf":
            return (sign << (self.k - 1)) | (self.exp_all_ones << self.t)
        if mag == 0:
            return sign << (self.k - 1)
        e = _floor_log2(mag)
        if e < self.emin:   # subnormal: mag = T * 2^(emin - t)
            T = mag / Fraction(2) ** (self.emin - self.t)
            assert T.denominator == 1 and 0 < T < 2 ** self.t
            E, T = 0, int(T)
        else:
            c = mag / Fraction(2) ** (e - self.t)
            assert c.denominator == 1 and 2 ** self.t <= c < 2 ** self.p
            E, T = e + self.bias, int(c) - 2 ** self.t
            assert 1 <= E <= self.exp_all_ones - 1
        return (sign << (self.k - 1)) | (E << self.t) | T


def _floor_log2(q):
    """The integer e with 2^e <= q < 2^(e+1), for a positive Fraction q."""
    e = q.numerator.bit_length() - q.denominator.bit_length()
    while Fraction(2) ** e > q:
        e -= 1
    while Fraction(2) ** (e + 1) <= q:
        e += 1
    return e


def round_exact(F, sign, q, mode):
    """Round the exact positive Fraction q (result sign `sign`) to format F.

    Returns (magnitude or 'inf')."""
    assert q > 0
    e = max(_floor_log2(q), F.emin)              # exponent of the result's binade (§3.3)
    quantum = Fraction(2) ** (e - (F.p - 1))     # spacing of representable numbers there
    n = q / quantum
    lo = (n.numerator // n.denominator) * quantum
    hi = lo + quantum
    if lo == q:
        r = q
    else:
        dlo, dhi = q - lo, hi - q
        if mode == "rne":
            if dlo != dhi:
                r = lo if dlo < dhi else hi
            else:
                r = lo if (lo / quantum) % 2 == 0 else hi
        elif mode == "rna":
            r = lo if dlo < dhi else hi
        elif mode == "rtz":
            r = lo
        elif mode == "rtp":
            r = lo if sign else hi
        elif mode == "rtn":
            r = hi if sign else lo
        else:
            raise ValueError(mode)
    if r > F.max_finite:   # §7.4: overflow, judged after rounding with unbounded exponent
        if mode == "rne":
            assert q >= F.rne_threshold
        to_inf = {"rne": True, "rna": True, "rtz": False,
                  "rtp": not sign, "rtn": bool(sign)}[mode]
        return "inf" if to_inf else F.max_finite
    if mode == "rne":
        assert q < F.rne_threshold
    return r


def div_exact(F, a, b, mode="rne"):
    """Oracle A: IEEE 754-2019 division(a, b) on bit patterns of format F."""
    A, B = F.decode(a), F.decode(b)
    if A[0] == "nan" or B[0] == "nan":
        return F.canonical_nan
    sign = A[1] ^ B[1]
    a_inf, b_inf = A[0] == "inf", B[0] == "inf"
    a_zero = (not a_inf) and A[2] == 0
    b_zero = (not b_inf) and B[2] == 0
    if a_inf and b_inf:
        return F.canonical_nan                 # invalid: division(inf, inf)
    if a_zero and b_zero:
        return F.canonical_nan                 # invalid: division(0, 0)
    if a_inf:
        return F.encode(sign, "inf")           # exact infinity (divisor finite)
    if b_inf:
        return F.encode(sign, Fraction(0))     # exact zero
    if b_zero:
        return F.encode(sign, "inf")           # divideByZero
    if a_zero:
        return F.encode(sign, Fraction(0))
    return F.encode(sign, round_exact(F, sign, A[2] / B[2], mode))


# ---- Oracle B: the hardware -----------------------------------------------------------

def _hw(a, b, fmt, nbits, nan_bits):
    x = struct.unpack(fmt, a.to_bytes(nbits // 8, "little"))[0]
    y = struct.unpack(fmt, b.to_bytes(nbits // 8, "little"))[0]
    if math.isnan(x) or math.isnan(y):
        return nan_bits
    if y == 0:   # Python raises ZeroDivisionError; IEEE gives NaN (0/0) or infinity
        if x == 0:
            return nan_bits
        q = math.copysign(math.inf, math.copysign(1, x) * math.copysign(1, y))
    else:
        q = x / y   # binary64 IEEE division in hardware
    if math.isnan(q):
        return nan_bits
    try:
        return int.from_bytes(struct.pack(fmt, q), "little")
    except OverflowError:   # CPython refuses to round to infinity; IEEE RNE overflows to inf
        return int.from_bytes(struct.pack(fmt, math.copysign(math.inf, q)), "little")


def div_hw16(a, b):
    """Oracle B for binary16, roundTiesToEven."""
    return _hw(a, b, "<e", 16, 0x7E00)


def div_hw32(a, b):
    """Oracle B for binary32, roundTiesToEven."""
    return _hw(a, b, "<f", 32, 0x7FC00000)


BINARY16 = Fmt(5, 11)
BINARY32 = Fmt(8, 24)
