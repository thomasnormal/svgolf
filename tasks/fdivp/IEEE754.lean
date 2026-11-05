/-!
# IEEE 754-2019 binary floating-point division — trusted svGolf specification

This file is **trusted challenge material**. It defines, on raw bit patterns,

    divide (f : Format) (mode : RoundingMode) : BitVec f.k → BitVec f.k → BitVec f.k

the IEEE 754-2019 `division` operation (§5.4.1) of a binary interchange format `f`
(§3.3, §3.4), and the binary16 and binary32 instances `divBinary16`/`divBinary32` (under
roundTiesToEven, the default rounding-direction attribute of §4.3.3).

Reading guide (each definition's docstring cites its clause):

* `Format`        — the format parameters `w`, `p` and the derived `t`, `k`, `emax`, `emin` (§3.3).
* `decode`        — bit pattern → `Datum` (NaN / ±∞ / ±0 / finite (sign, q, c)), clause by clause
                    from §3.4 (a)–(e). `Datum.value?` is the exact rational value (§3.3).
* `round`         — the correctly rounded result (§4.3, §5.1: computed as if with unbounded
                    range and precision, then rounded) of an exact positive fraction `n/d`, including
                    gradual underflow to subnormals (§3.3, §7.5 — no flush-to-zero) and the
                    overflow results of §4.3.1/§7.4.
* `divide`        — the special-case table (§6.1, §6.2, §6.3, §7.2, §7.3), then `round` of the
                    exact quotient `|x| / |y|` with sign `sign x XOR sign y` (§6.3).
* `DivideIsNearestTiesToEven`, `DivideOverflowsAtThreshold`, `DivideOfNumbersIsNotNaN`,
  `DivideSignIsXor` — §4.3.1, §6.3 and §7.2 restated for `divide` with bit patterns, `decode`
                    and integer inequalities only, independently of `round`;
  `DivideIsUniquelyCharacterized` — those four properties single out one bit pattern, so they
                    are a complete specification of the binary16 and binary32 instances
                    `divBinary16`/`divBinary32` on operands that are
                    numbers with a nonzero divisor. All five are proved for every format in
                    `IEEE754Proofs.lean` (untrusted, kernel-checked).

**NaN policy** (§6.2.3 says a NaN result *should* — not *shall* — carry an input payload):
every NaN result is the single *canonical quiet NaN*: sign 0, exponent field all ones,
trailing significand `10…0` (only the quiet bit set, §6.2.1) — `0x7E00` in binary16 and
`0x7FC00000` in binary32. This is the RISC-V F/Zfh policy and SMT-LIB's single NaN; it makes
the result a *function* of the operand bits. Signaling NaN operands also produce it.

Scope: all five rounding-direction attributes of §4.3 are a parameter; exception *flags*
(§7) are not modelled — the result bits do not depend on them (see README.md).

Arithmetic convention: all computation is on `Nat`, with `BitVec.toNat`/`BitVec.ofNat` at the
boundary; no floating-point type, no `Rat`, no external code. Everything is executable
(`#eval`, `#guard`, kernel `decide`).
-/

namespace SvGolf.IEEE754

/-! ## Formats (§3.3, §3.4, Table 3.5) -/

/-- A **binary interchange format** (IEEE 754-2019 §3.3, §3.4 and Table 3.5), given by
* `w` — the width in bits of the biased-exponent field `E`, and
* `p` — the precision: the number of significand digits, *including* the implicit leading bit.

binary16 is `w = 5, p = 11`; binary32 is `w = 8, p = 24`; binary64 is `w = 11, p = 53`.
The side conditions `2 ≤ w`, `2 ≤ p` exclude degenerate parameter choices (Table 3.5's
formats all satisfy them); they are discharged automatically for literals. -/
structure Format where
  /-- Width of the biased-exponent field `E` (§3.4). -/
  w : Nat
  /-- Precision `p`: significand digits including the implicit bit (§3.3). -/
  p : Nat
  hw : 2 ≤ w := by decide
  hp : 2 ≤ p := by decide

namespace Format

variable (f : Format)

/-- `t = p − 1`: width of the trailing significand field `T` (§3.4). -/
abbrev t : Nat := f.p - 1

/-- `k = 1 + w + t`: the storage width in bits (§3.4, Table 3.5). -/
abbrev k : Nat := 1 + f.w + f.t

/-- `emax = 2^(w−1) − 1`, which is also the exponent `bias` (§3.3, §3.4, Table 3.5). -/
def emax : Nat := 2 ^ (f.w - 1) - 1

/-- `emin = 1 − emax` (§3.3). -/
def emin : Int := 1 - (f.emax : Int)

/-- `qmin = emin − (p − 1)`: the least *quantum exponent* (§3.3: a finite number is
`(−1)^s × 2^q × c` with `emin ≤ q + p − 1 ≤ emax`). `2^qmin` is the least positive subnormal
magnitude, and every finite number of the format is an integer multiple of it. -/
def qmin : Int := f.emin - f.t

/-- `scale = −qmin = emax + p − 2` as a natural number: one *unit* `2^qmin = 2^(−scale)` is the
least positive subnormal magnitude (binary16: 24, binary32: 149). Rounding (`round`) works on
magnitudes measured in units, where every finite number of the format is a natural number. -/
def scale : Nat := f.emax + f.t - 1

/-- The largest finite magnitude `(2 − 2^(1−p)) × 2^emax` (§3.3), in units:
`(2^p − 1) × 2^(emax − emin)`. (binary16: `2047 × 2^29` units `= 65504`.) -/
def maxUnits : Nat := (2 ^ f.p - 1) * 2 ^ (2 * f.emax - 1)

end Format

/-- binary16 (§3.6 Table 3.5: k = 16, p = 11, emax = 15). -/
abbrev binary16 : Format := { w := 5, p := 11 }
/-- binary32 (§3.6 Table 3.5: k = 32, p = 24, emax = 127). -/
abbrev binary32 : Format := { w := 8, p := 24 }
/-- binary64 (§3.6 Table 3.5: k = 64, p = 53, emax = 1023). -/
abbrev binary64 : Format := { w := 11, p := 53 }

/-! ## Decoding bit patterns (§3.4) -/

/-- The datum a bit pattern represents (§3.2 levels 2–3, §3.4 (a)–(e)).

* `nan signaling` — a NaN; `signaling` iff the first trailing-significand bit is 0 (§6.2.1).
  The payload is not recorded: this specification never propagates payloads.
* `inf neg` — `+∞` or `−∞` (`neg = true` means sign bit 1).
* `zero neg` — `+0` or `−0`.
* `finite neg q c` — the nonzero number `(−1)^neg × 2^q × c` in the integral-significand
  notation of §3.3, with `0 < c < 2^p` and `qmin ≤ q`. -/
inductive Datum where
  | nan (signaling : Bool)
  | inf (neg : Bool)
  | zero (neg : Bool)
  | finite (neg : Bool) (q : Int) (c : Nat)
  deriving DecidableEq, Repr

/-- **Decoding** (§3.4, Figure 3.1). The `k`-bit string is `S ‖ E ‖ T`: the sign bit `S`, the
`w`-bit biased exponent `E` and the `t`-bit trailing significand `T`, most significant first.
The five cases are §3.4 (a)–(e), with the significand written as an integer
(`1.T = (2^t + T) × 2^(−t)`, `0.T = T × 2^(−t)`):

* (a) `E = 2^w − 1`, `T ≠ 0`: NaN (quiet iff `T`'s leading bit `d₁` is 1, §6.2.1);
* (b) `E = 2^w − 1`, `T = 0`: `(−1)^S × ∞`;
* (c) `1 ≤ E ≤ 2^w − 2`: `(−1)^S × 2^(E − bias) × (1 + 2^(1−p) × T)
       = (−1)^S × 2^(E − bias − t) × (2^t + T)` — normal;
* (d) `E = 0`, `T ≠ 0`: `(−1)^S × 2^emin × (0 + 2^(1−p) × T) = (−1)^S × 2^(emin − t) × T`
       — subnormal;
* (e) `E = 0`, `T = 0`: `(−1)^S × 0`. -/
def decode (f : Format) (x : BitVec f.k) : Datum :=
  let S := x.toNat / 2 ^ (f.w + f.t)
  let E := x.toNat / 2 ^ f.t % 2 ^ f.w
  let T := x.toNat % 2 ^ f.t
  let neg := S == 1
  if E = 2 ^ f.w - 1 then
    if T = 0 then .inf neg                                   -- (b)
    else .nan (T < 2 ^ (f.t - 1))                            -- (a): signaling iff d₁ = 0
  else if E = 0 then
    if T = 0 then .zero neg                                  -- (e)
    else .finite neg (f.emin - f.t) T                        -- (d) subnormal
  else .finite neg ((E : Int) - f.emax - f.t) (2 ^ f.t + T)  -- (c) normal, bias = emax

/-- The **exact value** of a datum as a fraction `num / den` of an integer and a positive
natural number (§3.3: the finite number `(−1)^neg × 2^q × c`; zeros have value 0). NaNs and
infinities have no real value (`none`). The fraction is not reduced; `den` is a power of 2. -/
def Datum.value? : Datum → Option (Int × Nat)
  | .zero _ => some (0, 1)
  | .finite neg q c =>
    let num : Int := c * 2 ^ q.toNat
    some (if neg then -num else num, 2 ^ (-q).toNat)
  | .nan _ | .inf _ => none

/-! ## Encoding (§3.4) -/

/-- The `k`-bit string `S ‖ E ‖ T` (§3.4, Figure 3.1) for sign `neg`, biased exponent `E < 2^w`
and trailing significand `T < 2^t`. -/
def fields (f : Format) (neg : Bool) (E T : Nat) : BitVec f.k :=
  BitVec.ofNat f.k ((if neg then 1 else 0) * 2 ^ (f.w + f.t) + E * 2 ^ f.t + T)

/-- `(−1)^neg × ∞`: `E = 2^w − 1`, `T = 0` (§3.4 (b)). -/
def infinity (f : Format) (neg : Bool) : BitVec f.k := fields f neg (2 ^ f.w - 1) 0

/-- `(−1)^neg × 0`, a signed zero: `E = 0`, `T = 0` (§3.4 (e)). -/
def zero (f : Format) (neg : Bool) : BitVec f.k := fields f neg 0 0

/-- **The canonical NaN** (this specification's NaN policy, §6.2.1, §6.2.3): sign 0,
`E = 2^w − 1`, `T = 2^(t−1)` — a quiet NaN (`d₁ = 1`) with all other payload bits 0.
binary16: `0x7E00`; binary32: `0x7FC00000`. -/
def canonicalNaN (f : Format) : BitVec f.k := fields f false (2 ^ f.w - 1) (2 ^ (f.t - 1))

/-- `(−1)^neg × u × 2^qmin`, i.e. the finite magnitude of `u` units, encoded (§3.4 (c)–(e)).
Precondition: `u` is a representable magnitude — `u = c × 2^j` with `c < 2^p` — and
`u ≤ maxUnits`; `round` only produces such `u`.

* `u < 2^t`: a subnormal or zero, `E = 0`, `T = u` (§3.4 (d), (e)).
* otherwise `u = c × 2^j` with `2^t ≤ c < 2^p`, `j = ⌊log₂ u⌋ − t`; this is the normal number
  `2^(qmin + j) × c` with biased exponent `E = j + 1` and `T = c − 2^t` (§3.4 (c)). -/
def finite (f : Format) (neg : Bool) (u : Nat) : BitVec f.k :=
  if u < 2 ^ f.t then fields f neg 0 u
  else
    let j := Nat.log2 u - f.t
    fields f neg (j + 1) (u / 2 ^ j - 2 ^ f.t)

/-! ## Rounding (§4.3, §5.4.1, §7.4) -/

/-- The rounding-direction attributes (§4.3.1, §4.3.2). `roundTiesToEven` is the default
(§4.3.3) and the only one used by svGolf (the task `fdivp`, and the binary16 and binary32
instances `divBinary16`/`divBinary32`). -/
inductive RoundingMode where
  | roundTiesToEven
  | roundTiesToAway
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero
  deriving DecidableEq, Repr

/-- The spacing exponent of representable magnitudes near a magnitude of `n` units: in the
binade `[2^(p−1+j), 2^(p+j))` units (`j ≥ 1`), the representable magnitudes are exactly the
multiples of `2^j` units (§3.3: `2^q × c` with `q = qmin + j`, `2^(p−1) ≤ c < 2^p`); below
`2^p` units (subnormals and the lowest normal binade) they are the multiples of 1 unit.
Computed as `max(0, ⌊log₂ n⌋ + 1 − p)` (`Nat` subtraction truncates at 0; `log2 0 = 0`).
There is no upper limit on `j`: this is the *unbounded exponent range* of §4.3 and §7.4. -/
def ulpExp (f : Format) (n : Nat) : Nat := (Nat.log2 n + 1) - f.p

/-- **Rounding with unbounded exponent range** (§4.3, and §7.4's "rounded … were the exponent
range unbounded") of the exact magnitude `N / D` units (`D > 0`), with `neg` the sign of the
exact result (it matters only for the directed attributes).

`N / D` lies in the binade of `⌊N/D⌋` (binade boundaries are integers), where representable
magnitudes are the multiples of `2^j` units, `j = ulpExp ⌊N/D⌋`. Write `M = D × 2^j` and
`N = c × M + r` with `0 ≤ r < M`; then `N/D = (c + r/M) × 2^j`, so `c × 2^j` and `(c + 1) × 2^j`
are the two representable magnitudes bracketing `N/D` (`(c+1) × 2^j` may be `2^p × 2^j`, which
is `2^(p−1) × 2^(j+1)`), and `2r` versus `M` compares the distance to them:

* roundTiesToEven (§4.3.1): the nearer; on a tie (`2r = M`) the one with even significand
  — `c × 2^j` iff `c` is even;
* roundTiesToAway (§4.3.1): the nearer; on a tie the larger magnitude;
* roundTowardPositive / roundTowardNegative / roundTowardZero (§4.3.2): the one in that direction
  (for a magnitude: up iff inexact and the direction points away from zero).

The result is a magnitude in units. -/
def roundUnits (f : Format) (mode : RoundingMode) (neg : Bool) (N D : Nat) : Nat :=
  let j := ulpExp f (N / D)
  let M := D * 2 ^ j
  let c := N / M
  let r := N % M
  let up : Bool :=
    match mode with
    | .roundTiesToEven => 2 * r > M || (2 * r == M && c % 2 == 1)
    | .roundTiesToAway => 2 * r ≥ M
    | .roundTowardPositive => r != 0 && !neg
    | .roundTowardNegative => r != 0 && neg
    | .roundTowardZero => false
  (if up then c + 1 else c) * 2 ^ j

/-- Whether an overflow delivers `∞` (rather than the largest finite magnitude) — §7.4:
roundTiesToEven and roundTiesToAway carry all overflows to `∞`; roundTowardZero carries all
overflows to the largest finite number; roundTowardPositive carries negative overflows to the
most negative finite number and positive overflows to `+∞`; roundTowardNegative the mirror. -/
def overflowToInfinity : RoundingMode → (neg : Bool) → Bool
  | .roundTiesToEven, _ => true
  | .roundTiesToAway, _ => true
  | .roundTowardZero, _ => false
  | .roundTowardPositive, neg => !neg
  | .roundTowardNegative, neg => neg

/-- **The correctly rounded result** (§4.3, §5.4.1, §7.4, §7.5) of the exact nonzero value
`(−1)^neg × n / d` (`n, d > 0`), as a bit pattern of format `f`:

1. measure the magnitude in units of `2^qmin`: `n / d = (n × 2^scale / d) × 2^qmin`;
2. round it with unbounded exponent range (`roundUnits`); results below the normal range are
   subnormals or zero — gradual underflow, no flush-to-zero (§3.3, §7.5);
3. if the rounded magnitude exceeds the largest finite magnitude, the operation overflows
   (§7.4) and delivers `±∞` or `±maxFinite` per `overflowToInfinity`; otherwise it is encoded
   with sign `neg` — a zero result keeps the sign `neg` (§6.3). -/
def round (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) : BitVec f.k :=
  let u := roundUnits f mode neg (n * 2 ^ f.scale) d
  if u ≤ f.maxUnits then finite f neg u
  else if overflowToInfinity mode neg then infinity f neg
  else finite f neg f.maxUnits

/-! ## Division (§5.4.1) -/

/-- **IEEE 754-2019 division** `division(x, y)` (§5.4.1) of format `f` under rounding-direction
attribute `mode`, on bit patterns.

The special cases, in order:
* any NaN operand (quiet or signaling) → the canonical NaN (§6.2, NaN policy above);
* `division(∞, ∞)` and `division(0, 0)` are invalid operations (§7.2) → the canonical NaN;
* `division(∞, y)` for finite `y`, zero included → `∞`, exact (§6.1);
* `division(x, ∞)` for finite `x`, zero included → `0`, exact (§6.1);
* `division(x, 0)` for finite nonzero `x` → `∞`, the divideByZero exception (§7.3);
* `division(0, y)` for finite nonzero `y` → `0`, exact.
In all non-NaN cases the sign of the result is the exclusive OR of the operands' signs (§6.3).

Otherwise `x = (−1)^sx × 2^qx × cx` and `y = (−1)^sy × 2^qy × cy` are finite nonzero, and the
result is the exact quotient rounded (§4.3, §5.1: as if computed with unbounded range and
precision, then rounded): `|x| / |y| = (nx / dx) / (ny / dy) = (nx × dy) / (dx × ny)`
where `nx / dx` is `|x|` as a fraction (`Datum.value?`). -/
def divide (f : Format) (mode : RoundingMode) (a b : BitVec f.k) : BitVec f.k :=
  match decode f a, decode f b with
  | .nan _, _ | _, .nan _ => canonicalNaN f
  | .inf _, .inf _ => canonicalNaN f
  | .zero _, .zero _ => canonicalNaN f
  | .inf sx, .zero sy | .inf sx, .finite sy _ _ => infinity f (sx ^^ sy)
  | .zero sx, .inf sy | .finite sx _ _, .inf sy => zero f (sx ^^ sy)
  | .finite sx _ _, .zero sy => infinity f (sx ^^ sy)
  | .zero sx, .finite sy _ _ => zero f (sx ^^ sy)
  | .finite sx qx cx, .finite sy qy cy =>
    -- |x| = nx / dx and |y| = ny / dy exactly (Datum.value? without the sign)
    let nx := cx * 2 ^ qx.toNat
    let dx := 2 ^ (-qx).toNat
    let ny := cy * 2 ^ qy.toNat
    let dy := 2 ^ (-qy).toNat
    round f mode (sx ^^ sy) (nx * dy) (dx * ny)

/-- The binary16 instance: binary16 division, roundTiesToEven (the task `fdivp` at
`(W, P) = (5, 11)`). -/
def divBinary16 (a b : BitVec 16) : BitVec 16 := divide binary16 .roundTiesToEven a b

/-- The binary32 instance: binary32 division, roundTiesToEven (the task `fdivp` at
`(W, P) = (8, 24)`). -/
def divBinary32 (a b : BitVec 32) : BitVec 32 := divide binary32 .roundTiesToEven a b

/-! ## Characterization (statements; proofs in `IEEE754Proofs.lean`)

The first four propositions below restate what IEEE 754-2019 requires of `division` directly
in terms of bit patterns, `decode`, exact fractions and integer inequalities, independently of
how `round` computes; the fifth says that those four leave only one possible result.
`IEEE754Proofs.lean` proves all five for every format `f`. Fractions are pairs
`(num, den) : Int × Nat` with `den > 0`, as in `Datum.value?`.

* `DivideIsNearestTiesToEven` — a quotient that has a value is a nearest number, ties to even;
* `DivideOverflowsAtThreshold` — a quotient is an infinity exactly at the overflow threshold;
* `DivideOfNumbersIsNotNaN` — a quotient of two numbers (nonzero divisor) is never a NaN, so
  it is always covered by one of the two statements above;
* `DivideSignIsXor` — every non-NaN quotient has the XOR sign, zeros and infinities included;
* `DivideIsUniquelyCharacterized` — any bit pattern with the four properties above is the
  roundTiesToEven quotient.

How they fit together is spelled out before the last one. -/

/-- `NoFarther a b x`: the fraction `a = a.1 / a.2` is at least as close to `x` as `b` is,
`|a − x| ≤ |b − x|`, stated by cross-multiplication (all denominators positive):
`|a.1·x.2 − x.1·a.2| / (a.2·x.2) ≤ |b.1·x.2 − x.1·b.2| / (b.2·x.2)`. -/
def NoFarther (a b x : Int × Nat) : Prop :=
  (a.1 * x.2 - x.1 * a.2).natAbs * b.2 ≤ (b.1 * x.2 - x.1 * b.2).natAbs * a.2

/-- The exact quotient `x / y` of two fractions with `y ≠ 0`, with a positive denominator:
`(x.1/x.2) / (y.1/y.2) = (x.1·y.2) / (x.2·y.1)`, the sign moved to the numerator. -/
def fracDiv (x y : Int × Nat) : Int × Nat :=
  (if y.1 < 0 then -(x.1 * y.2) else x.1 * y.2, x.2 * y.1.natAbs)

/-- **`divide` under roundTiesToEven delivers the nearest number, ties to even** (§4.3.1,
§5.4.1). Let `a`, `b` be bit patterns whose exact values `x`, `y` exist (zero or finite
operands) with `y ≠ 0`, and suppose their quotient `divide f .roundTiesToEven a b` is zero or
finite with exact value `r`. (Read alone, this hypothesis excludes NaN results as well as
infinities, so it would leave a NaN result unconstrained; `DivideOfNumbersIsNotNaN` shows there
is none. With `DivideOverflowsAtThreshold`, the hypothesis therefore holds exactly for the
quotients below the overflow threshold.) Then:

1. *nearest* — every finite number (or zero) `v` of the format is at least as far from the
   exact quotient `x / y` as `r` is;
2. *ties to even* — if a finite number `v` with a different value is no farther from `x / y`
   than `r` (so the two are equally near), then the delivered bit pattern has least
   significant bit 0: its significand's last digit is even. -/
def DivideIsNearestTiesToEven (f : Format) : Prop :=
  ∀ (a b : BitVec f.k) (x y r : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    (decode f (divide f .roundTiesToEven a b)).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) →
          (divide f .roundTiesToEven a b).toNat % 2 = 0)

/-- **Overflow happens exactly at the §4.3.1 threshold** ("an infinitely precise result with
magnitude at least `b^emax × (b − ½ b^(1−p))` shall round to `∞` with no change in sign"; §7.4).
For bit patterns `a`, `b` whose exact values `x`, `y` exist with `y ≠ 0`, the roundTiesToEven
quotient is an infinity iff `|x / y| ≥ 2^emax × (2 − 2^(−p))`; writing `x / y = n / d`
(`fracDiv`) this is the integer inequality `d × 2^emax × (2^(p+1) − 1) ≤ |n| × 2^p`.
On its own this says nothing about a quotient below the threshold beyond "not an infinity";
`DivideOfNumbersIsNotNaN` adds that such a quotient has a value, so that
`DivideIsNearestTiesToEven` applies to it. -/
def DivideOverflowsAtThreshold (f : Format) : Prop :=
  ∀ (a b : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    ((∃ s, decode f (divide f .roundTiesToEven a b) = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p)

/-- **A quotient of two numbers is never a NaN** (§7.2: the invalid divisions are
`division(0, 0)` and `division(∞, ∞)`, and neither has two numbers with a nonzero divisor). For
bit patterns `a`, `b` whose exact values `x`, `y` exist (zero or finite operands) with `y ≠ 0`,
the quotient under **every** rounding-direction attribute is an infinity or has an exact value
(a zero or a finite number).

The conclusion is exactly the union of the cases the other statements speak about: infinities
(`DivideOverflowsAtThreshold`) and results with a value (`DivideIsNearestTiesToEven`). Without
it, those two would also be satisfied by a divider that returned a NaN for every quotient below
the overflow threshold. -/
def DivideOfNumbersIsNotNaN (f : Format) : Prop :=
  ∀ (mode : RoundingMode) (a b : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    (∃ s, decode f (divide f mode a b) = .inf s) ∨
      ∃ r, (decode f (divide f mode a b)).value? = some r

/-- **The sign of a quotient is the exclusive OR of the operands' signs** (§6.3: "When neither
the inputs nor result are NaN, the sign of a product or quotient is the exclusive OR of the
operands' signs"), for **every** pair of bit patterns and every rounding-direction attribute,
zero, infinite and overflowed results included. `BitVec.msb` is the most significant bit of
the `k`-bit string: the sign bit `S` (§3.4). The hypothesis is only that the *result* is not a
NaN; NaN operands always give a NaN result here, so this is the clause's condition. -/
def DivideSignIsXor (f : Format) : Prop :=
  ∀ (mode : RoundingMode) (a b : BitVec f.k),
    (∀ s, decode f (divide f mode a b) ≠ .nan s) →
      (divide f mode a b).msb = (a.msb ^^ b.msb)

/-! ### How the statements fit together

Take bit patterns `a`, `b` with exact values `x`, `y` and `y ≠ 0`, and let
`R = divide f .roundTiesToEven a b`. Then:

1. `R` is not a NaN: it is an infinity or has a value (`DivideOfNumbersIsNotNaN`);
2. its sign bit is `a.msb ^^ b.msb` (`DivideSignIsXor`);
3. it is an infinity exactly when `|x / y|` reaches the threshold (`DivideOverflowsAtThreshold`);
4. otherwise its value is a nearest number of the format to `x / y`, and on a tie its last bit
   is 0 (`DivideIsNearestTiesToEven`).

These four properties leave exactly one possible bit pattern, and that is proved too:
`DivideIsUniquelyCharacterized` below states that any pattern `R` with properties 1–4 is
`divide f .roundTiesToEven a b`. So for these operands a reader can take properties 1–4 as the
specification and need not read `round` at all. (Informally: above the threshold the result is
the infinity with the XOR sign. Below it, two different patterns with the same sign bit cannot
both qualify. Their values would be distinct and equally near `x / y`, so they would be adjacent
numbers of the format, both ending in bit 0. But adjacent numbers of one sign have consecutive
encodings, so their last bits differ.)

All other operand pairs, namely a NaN or infinite operand or a zero divisor, are the
special-case table in `divide` itself, which is meant to be read directly. The signs of its
non-NaN results are also covered by `DivideSignIsXor`. -/

/-- **Properties 1–4 determine the roundTiesToEven quotient.** For bit patterns `a`, `b` whose
exact values `x`, `y` exist with `y ≠ 0`, any bit pattern `R` that has the four properties that
`DivideOfNumbersIsNotNaN`, `DivideSignIsXor`, `DivideOverflowsAtThreshold` and
`DivideIsNearestTiesToEven` state of `divide f .roundTiesToEven a b` (copied here verbatim with
`R` in its place) is equal to `divide f .roundTiesToEven a b`. -/
def DivideIsUniquelyCharacterized (f : Format) : Prop :=
  ∀ (a b R : BitVec f.k) (x y : Int × Nat),
    (decode f a).value? = some x → (decode f b).value? = some y → y.1 ≠ 0 →
    -- 1. not a NaN
    ((∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r) →
    -- 2. the XOR sign
    ((∀ s, decode f R ≠ .nan s) → R.msb = (a.msb ^^ b.msb)) →
    -- 3. an infinity exactly at the threshold
    ((∃ s, decode f R = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p) →
    -- 4. otherwise nearest, ties to even
    (∀ r, (decode f R).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) → R.toNat % 2 = 0)) →
    R = divide f .roundTiesToEven a b

/-! ## Golden vectors (binary16 / binary32, roundTiesToEven; hand-derived)

Evaluated by `#guard` (compiled evaluation) and, for a few, by kernel reduction (`decide`). -/

-- §5.4.1 ordinary quotients: 1/3 = 0x3555 (1.0101010101|01… rounds down), 3/3 = 1, 1/2
#guard divBinary16 0x3C00#16 0x4200#16 = 0x3555#16
#guard divBinary16 0x4200#16 0x4200#16 = 0x3C00#16
#guard divBinary16 0xBC00#16 0x4000#16 = 0xB800#16
-- §6.3 signs: the sign of a quotient is the XOR of the operand signs, zeros included
#guard divBinary16 0x0000#16 0xBC00#16 = 0x8000#16
#guard divBinary16 0x8000#16 0xBC00#16 = 0x0000#16
-- §6.1 exact infinity arithmetic: ∞/finite = ∞, finite/∞ = 0, ∞/0 = ∞ (no divideByZero)
#guard divBinary16 0x7C00#16 0xC000#16 = 0xFC00#16
#guard divBinary16 0x3C00#16 0x7C00#16 = 0x0000#16
#guard divBinary16 0xBC00#16 0x7C00#16 = 0x8000#16
#guard divBinary16 0xFC00#16 0x0000#16 = 0xFC00#16
#guard divBinary16 0x7C00#16 0x8000#16 = 0xFC00#16
-- §7.3 divideByZero: finite nonzero / 0 = ∞ with XOR sign
#guard divBinary16 0x3C00#16 0x0000#16 = 0x7C00#16
#guard divBinary16 0xBC00#16 0x0000#16 = 0xFC00#16
#guard divBinary16 0x3C00#16 0x8000#16 = 0xFC00#16
-- §7.2 invalid: 0/0 and ∞/∞ give the canonical NaN (0/0 is NOT ∞)
#guard divBinary16 0x0000#16 0x0000#16 = 0x7E00#16
#guard divBinary16 0x8000#16 0x0000#16 = 0x7E00#16
#guard divBinary16 0x7C00#16 0xFC00#16 = 0x7E00#16
-- §6.2 NaN operands (quiet, signaling, negative, with payload) give the canonical NaN
#guard divBinary16 0x7E00#16 0x3C00#16 = 0x7E00#16
#guard divBinary16 0xFE00#16 0x3C00#16 = 0x7E00#16
#guard divBinary16 0x7C01#16 0x3C00#16 = 0x7E00#16
#guard divBinary16 0x3C00#16 0xFFFF#16 = 0x7E00#16
#guard divBinary16 0x0000#16 0x7D00#16 = 0x7E00#16
-- §7.4 overflow: 65504 / 0.5 = 131008 ≥ 65520 rounds to ∞; 65504 / 1 = 65504 does not
#guard divBinary16 0x7BFF#16 0x3800#16 = 0x7C00#16
#guard divBinary16 0xFBFF#16 0x3800#16 = 0xFC00#16
#guard divBinary16 0x7BFF#16 0x3C00#16 = 0x7BFF#16
-- 65504 / (1 − 2^−11) = 65536 exactly ≥ 65520: overflow
#guard divBinary16 0x7BFF#16 0x3BFF#16 = 0x7C00#16
-- §3.3, §7.5 gradual underflow (no flush-to-zero): min normal / 2 = 2^−15 = 0x0200
#guard divBinary16 0x0400#16 0x4000#16 = 0x0200#16
#guard divBinary16 0x0001#16 0x3C00#16 = 0x0001#16
-- 1023·2^−24 / (1023/1024) = 2^−14: a subnormal dividend, a normal (min normal) result
#guard divBinary16 0x03FF#16 0x3BFE#16 = 0x0400#16
-- §4.3.1 ties to even in the subnormal range (the only place division can tie):
-- 2^−24 / 2 = ½ unit, ties to 0 (even); 3·2^−24 / 2 = 1½ units, ties to 2 (even);
-- 5·2^−24 / 2 = 2½ units, ties to 2 (even)
#guard divBinary16 0x0001#16 0x4000#16 = 0x0000#16
#guard divBinary16 0x0003#16 0x4000#16 = 0x0002#16
#guard divBinary16 0x0005#16 0x4000#16 = 0x0002#16
-- just above a tie: 2^−24 / (2 − 2^−10) is a little over ½ unit, rounds up to 1 unit
#guard divBinary16 0x0001#16 0x3FFF#16 = 0x0001#16
-- underflow to zero keeps the sign: −2^−24 / 4 = −¼ unit → −0
#guard divBinary16 0x8001#16 0x4400#16 = 0x8000#16
-- binary32: 1/3, 0/0, 1/0, least subnormal / 2 ties to +0, 3·2^−149 / 2 ties to 2·2^−149
#guard divBinary32 0x3F800000#32 0x40400000#32 = 0x3EAAAAAB#32
#guard divBinary32 0x00000000#32 0x00000000#32 = 0x7FC00000#32
#guard divBinary32 0x3F800000#32 0x00000000#32 = 0x7F800000#32
#guard divBinary32 0x00000001#32 0x40000000#32 = 0x00000000#32
#guard divBinary32 0x00000003#32 0x40000000#32 = 0x00000002#32
#guard divBinary32 0x7F7FFFFF#32 0x3F000000#32 = 0x7F800000#32
-- the canonical NaN of both challenge formats; the named encodings of ±0 and ±∞
#guard canonicalNaN binary16 = 0x7E00#16
#guard canonicalNaN binary32 = 0x7FC00000#32
#guard zero binary16 false = 0x0000#16 && zero binary16 true = 0x8000#16
#guard infinity binary16 false = 0x7C00#16 && infinity binary16 true = 0xFC00#16
-- kernel reduction (no compiled code involved)
example : divBinary16 0x3C00#16 0x4200#16 = 0x3555#16 := by decide
example : divBinary16 0x0003#16 0x4000#16 = 0x0002#16 := by decide
example : divBinary16 0x0000#16 0x0000#16 = 0x7E00#16 := by decide
example : divBinary32 0x3F800000#32 0x40400000#32 = 0x3EAAAAAB#32 := by decide

end SvGolf.IEEE754
