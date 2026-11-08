# Task `fdivp`: IEEE 754 division, parametric in the format (`fdiv #(W, P)`, for EVERY `W >= 2`, `P >= 2`)

IEEE 754 division for all binary formats at once: a combinational divider **generic in the exponent width `W` and
the precision `P`**, **round to nearest, ties to even**, every NaN result the **canonical quiet NaN**, and **full
subnormals** (no flush to zero), proved correct against the trusted IEEE 754 spec **for every format**. The task is
**ready** (`task.json` `"status": "ready"`): the statement, a validated reference circuit (`reference/fdivp.sv`, a
word-level netlist of 34 sites with two generate families) and its **proof for every `W`, `P` and every pair of operands**
(`reference/fdivp.lean`, accepted by `check.py` through every stage, axioms `propext`, `Classical.choice`, `Quot.sound`
only). A second proved reference, a Newton-Raphson divider (`reference/fdivp_newton.sv`, `reference/fdivp_newton.lean`),
computes the same function by another algorithm (section "The Newton reference"), and a third, a radix-4 SRT divider
adapted from CORE-V Wally (`reference/fdivp_srt.sv`, `reference/fdivp_srt.lean`), by a third (section "The SRT
reference"). `REVIEW.md` is the review of the trusted statement for the maintainers.

**binary16 is the instance `(W, P) = (5, 11)`**, the scoring point. The former fixed-size 16-bit task (binary16 alone) was
folded into this one on 2026-11-03: its function is this task's at `(5, 11)`, its flat reference
is a baseline here (`tests/fdivp/baselines/flat_binary16.sv`), and its tests were ported to `(5, 11)`.

The task directory holds: `Spec.lean` and `IEEE754.lean` (TRUSTED: the statement and the IEEE 754 spec it uses),
`task.json`, `README.md`, `REVIEW.md` (the review of the trusted files), `oracle.py` (the advisory oracle),
`spec_validate/` (the spec's differential validation, untrusted tooling) and `reference/` (`fdivp.sv` and `fdivp.lean`,
D3; `fdivp_newton.sv` and `fdivp_newton.lean`, the Newton divider; `fdivp_srt.sv` and `fdivp_srt.lean`, the SRT
divider, with `LICENSES/`, the licence texts its Apache-2.0 WITH SHL-2.1 part needs). There is no proof library: each
reference proof is one self-contained file over the general ls-sv library `LeanModels.Sv.Lib` (the Newton and SRT proofs
copy the sections they share with D3's verbatim, and `tests/fdivp/shared_sections.py` checks that they stay
byte-identical).

## Start a new design

A new divider is your own `solution.sv` (the header below; `/ % **` are banned at run time, `+ - *` and the
comparisons are allowed) and a `Solution.lean` that proves it for every format, `W ≥ 2` and `P ≥ 2`. Find
the design without Lean, then check it once without a proof:

```bash
python3.12 score/ppa.py solution.sv --task tasks/fdivp --no-mapped   # area and delay at (5, 11), seconds
python3.12 check.py tasks/fdivp solution.sv --unproved --tactics --stage-dir stage
```

The second command runs every stage that needs no proof, the task's oracle included (a wrong divider is
named there, not deep in a proof), says whether the proof tactics read the design (`tactics.in_fragment`)
and leaves it staged in `stage/` for probe files ([PROVING.md, section 0](../../PROVING.md#0-the-loop)).

**The route: the `sv_comb` tactics, then a model of your datapath** ([PROVING.md, section
1](../../PROVING.md#1-the-shape-of-a-proof); three complete proofs, the largest of the course: the restoring
`reference/fdivp.lean`, 4034 code lines, Newton-Raphson 4693, SRT 4951; "The reference" below says how they are
built):

1. `sv_structure (rank := …)` over both parameters: one driver per bit and no combinational loop
   (`CombDesign ∧ Acyclic ∧ SharedObl design.pdesign [W, P]`); the restoring reference ranks its module-level
   assigns by depth and its two loops, `norm` and `div`, by stage, with `rippleRank`.
2. `sv_interface`, after `unfold SvGolf.Tasks.FdivP.task` (the tactic does not read the task as an
   application).
3. `sv_equations`: each assign as an equation over `Bool` and every driven bit known; the cover obligations of
   a generate family can be conjunctions, closed by `refine ⟨?_, ?_⟩ <;> sv_cover`.
4. The arithmetic: a model of your datapath on `Nat` that the printed equations imply (the reference's glue,
   `Glue.chain`: the equations in, the output's value out), then that model against the task's function
   (`OutN_fdivBits`). The facts about IEEE 754 rounding do not depend on the datapath: the rounding certificate
   `certF_bridge` (section `CertF`), for every format, is where a proof of any other divider starts.

**Lay the design out so the tactics take it** (what they refuse, with the messages: [PROVING.md, section
4](../../PROVING.md#4-what-the-tactics-accept-and-what-they-refuse)):

* continuous `assign`s in at most two nested `generate for` loops, every index and loop bound affine in `W`, `P`
  and the genvars; word-level `+ - *`, the comparisons and the run-time shifts `<<` and `>>` are in the fragment
  (PROVING.md, sections 14 and 17);
* the stages of a loop as the rows of 2-D arrays (the restoring reference's normalizer rows `na_r`, `ya_r` and
  its remainder rows `rr`);
* derived sizes as `localparam integer` (`K = W + P`; `+`, `-`, `*` by a literal, `/` and `%` by a literal,
  `$clog2`; not a 2-state `int`). The natural form D1 (`tests/fdivp/baselines/fdivp_d1.sv`: `$clog2`, `2**`,
  replication, a logarithmic normalizer and shifter) is validated but ls-sv cannot load it; D2 (`fdivp_d2.sv`)
  is the same divider written for the fragment;
* every declared bit driven at `(5, 11)`.

**The skeleton** (`reference/fdivp.lean` is it, filled in for the restoring divider):

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

set_option maxHeartbeats 300000 in
theorem my_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
  sv_structure (rank := myRank W P)           -- your rank, a `def` above
  all_goals (intros; omega)

theorem my_interface (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (design.sem W P)) :
    (SvGolf.Tasks.FdivP.task W P).Interface 0 (design.sem W P) := by
  unfold SvGolf.Tasks.FdivP.task
  sv_interface

-- your arithmetic: the printed equations in, the value of `q` out (fdivp.lean's `Glue.chain`, `OutN_fdivBits`)

set_option maxHeartbeats 500000 in
theorem solution : Goal := by
  intro W P hWP
  obtain ⟨hW, hP, -⟩ := hWP
  obtain ⟨hc, ha, hso⟩ := my_struct W P hW hP
  refine CombTask.satisfiedAt_of_comb (my_interface W P hW hP hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨a, b, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.FdivP.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hav, hbv⟩ := hv
  sv_equations
  · -- the main goal: your chain of equations to the value of `q` (fdivp.lean)
  case inputsKnown_1 => exact inKnown_ofBitVec hav (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hbv (by omega)
  all_goals first | (intros; omega) | sv_cover | (intros; refine ⟨?_, ?_⟩ <;> sv_cover)

end Submission
```

**Library lemmas that exist today** (the tables: [PROVING.md, section 6](../../PROVING.md#6-tips-the-library)):

* `LeanModels.Sv.Lib`: `Restoring` (`restRem`, `restQuo`, `restore_spec`: `n + 1` restoring steps give the
  quotient and the remainder; `val_restQuo`: the value of a row of quotient bits), `XFVal` (the `Nat` value of
  windows, concatenations, extensions, constants, shifts, `addBits` / `subBits`, multiplexers, reductions),
  `NatArith` (scaled comparisons, products of powers, modular subtraction, the bands of a remainder),
  `BitVecArith`, `RowMajor`;
* the IEEE 754 facts and the rounding certificate are in the references (a task ships no library: copy them):
  `reference/fdivp.lean`'s sections `IEEE754Proofs`, `ScaleInvariance`, `RneInterval`, `RoundingBounds` and
  `CertF` hold for every divider; `DpN` .. `DpU` and `DpG1` .. `DpG5` are the restoring datapath's;
* the port bridges `SvState.lookup_eq_ofBitVec_bv`, `SvState.boolAt_ofBitVec`, `inKnown_ofBitVec`; `sv_bridge`.

## The circuit

Write a module with exactly this header (parameter and port names, directions, widths and order matter; the module must
be called `fdiv`, and the parameters `W`, `P` must be overridable, in this order):

```systemverilog
module fdiv #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
```

`W` is the width of the biased exponent field and `P` the precision (significand digits including the implicit bit), so a
pattern is `1 + W + (P - 1) = W + P` bits: binary16 is `(5, 11)`, bfloat16 `(8, 8)`, binary32 `(8, 24)`, binary64
`(11, 53)`, the smallest format `(2, 2)`. It must compute, combinationally, `q = a / b` exactly as the trusted function
`SvGolf.IEEE754.divide <W, P> .roundTiesToEven` (`IEEE754.lean`, `fdivBits W P a b` in `Spec.lean`), for
every `W >= 2` and `P >= 2` (no upper bound):

| operands | `q` |
|---|---|
| any NaN operand (quiet or signaling, any sign or payload) | the canonical quiet NaN `{0, all-ones exponent, fraction MSB set, rest 0}` |
| `inf / inf`, `0 / 0` | the canonical quiet NaN |
| `inf / y` (finite `y`, zero included), `x / 0` (finite nonzero `x`) | `±inf` = `{s, all-ones exponent, zero fraction}` |
| `x / inf` (finite `x`, zero included), `0 / y` (finite nonzero `y`) | `±0` = `{s, W + P - 1 zeros}` |
| finite nonzero / finite nonzero | `|a| / |b|` rounded to nearest even, sign `s`, gradual underflow to subnormals and zero, overflow to `±inf` |

where `s = a[W+P-1] ^ b[W+P-1]`; the rows are tested top to bottom (so `0 / 0` is NaN, not `inf`). The canonical NaN of
binary16 is `0x7E00`, of binary32 `0x7FC00000`; at `P = 2` the fraction has ONE bit, the quiet bit.

## The statement (`Spec.lean`, trusted)

```lean
def task (W P : Nat) : CombTask where
  inRange K := K = 0
  inputs _ := [("a", W + P), ("b", W + P)]
  outputs _ := [("q", W + P)]
  fn _ := fun (a, b, ()) => (fdivBits W P a b, ())

def inRange (W P : Nat) : Prop := 2 ≤ W ∧ 2 ≤ P ∧ W + P + 1 < 2 ^ 31

abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) : Prop :=
  ∀ W P, inRange W P → (task W P).StatementFixed (sem W P)
```

A submission proves `SvGolf.Tasks.FdivP.Statement Submission.design.sem`, where `Submission.design.sem : Nat → Nat →
Design2` is the two-parameter design that `load_design_sv2` builds from the checker's own extraction of the `.sv`. For
each `(W, P)` this is a fixed-size statement (`CombTask.StatementFixed`): the design's inputs are exactly `a`, `b` (`W + P` bits) and
its output exactly `q`; there is no combinational loop; every run terminates under every schedule and stimulus; no process is clocked; and every cycle
whose stimulus drives `a` and `b` with known values ends with `q = fdivBits W P a b`. At `(5, 11)` that is IEEE binary16
division and at `(8, 24)` binary32. The choices of the statement (range, NaN, rounding, one fixed-size task per
format) are listed in `REVIEW.md`.

The range requires `W + P + 1 < 2^31` (decided 2026-11-06): the port widths are `int` expressions of the
parameters (`[W+P-1:0]`), a design computes its exponent in `W + P + 1` bits (`localparam integer EW = W + P + 1`
in the references), and an `int` holds no value of `2^31` or more, so beyond that bound the elaborated widths wrap.
Every task's range keeps every width it implies below `2^31`.

## The trusted spec (`IEEE754.lean`)

`IEEE754.lean` is the **trusted challenge material** of the task, beside `Spec.lean` (it was `svgolf/spec/IEEE754.lean`
until 2026-11-03; moved with its content unchanged). It defines IEEE 754-2019 `division` as a function on bit patterns,
generic over the binary format:

```lean
SvGolf.IEEE754.divide (f : Format) (mode : RoundingMode) : BitVec f.k → BitVec f.k → BitVec f.k
SvGolf.IEEE754.divBinary16 (a b : BitVec 16) : BitVec 16   -- binary16, roundTiesToEven
SvGolf.IEEE754.divBinary32 (a b : BitVec 32) : BitVec 32   -- binary32, roundTiesToEven
```

`Spec.lean`'s `fdivBits W P` is `divide ⟨W, P⟩ .roundTiesToEven`: at `(5, 11)` that is IEEE binary16 division, at `(8, 24)`
binary32.

The spec uses core Lean only: no Mathlib, no `Float`, no `Rat`, no `extern` or
`implemented_by`, no `sorry`/`native_decide`/axioms. It computes with `Nat` arithmetic and
`BitVec.toNat`/`BitVec.ofNat`, and everything is executable (`#eval`, `#guard`, kernel
`decide`). The operation takes about 300 lines and the characterization statements about
140 more; every docstring cites its IEEE 754-2019 clause. It was validated differentially
against three independent implementations (`spec_validate/`, its README has the evidence and
the commands to re-run it).

### What the spec says

Reading order in `IEEE754.lean`:

1. **`Format`** (§3.3, §3.4, Table 3.5) is given by `w` (exponent-field width) and `p` (precision,
   including the hidden bit), with `2 ≤ w` and `2 ≤ p`. The derived quantities are
   `t = p − 1`, `k = 1 + w + t`, `emax = bias = 2^(w−1) − 1`, `emin = 1 − emax`, and
   `qmin = emin − t`. binary16 is `⟨5, 11⟩` and binary32 is `⟨8, 24⟩`.
2. **`decode`** (§3.4 (a)–(e)) maps a bit pattern to a `Datum`: `nan signaling`, `inf neg`,
   `zero neg`, or `finite neg q c`, meaning `(−1)^neg × 2^q × c` in §3.3's integral-significand
   notation. **`Datum.value?`** is the exact value as a fraction `(num : Int, den : Nat)`.
3. **`round`** (§4.3, §5.4.1, §7.4, §7.5) correctly rounds an exact positive fraction
   `n / d`. It measures the fraction in *units* of the least subnormal `2^qmin`, so every
   representable magnitude is a natural number. It then rounds with unbounded exponent range
   (`roundUnits`) and encodes the result (`finite`). If the rounded magnitude exceeds the
   largest finite one, the result is the §7.4 overflow value. Subnormal results are produced
   (gradual underflow), with no flush-to-zero.
4. **`divide`** first applies the special-case table, then `round`s the exact quotient
   `|x| / |y|` with sign `sign(x) XOR sign(y)`:

   | operands | result | clause |
   |---|---|---|
   | any NaN (quiet or signaling) | canonical NaN | §6.2 |
   | ∞ / ∞, 0 / 0 | canonical NaN (invalid) | §7.2 |
   | ∞ / finite (zero included) | ±∞, exact | §6.1 |
   | finite (zero included) / ∞ | ±0, exact | §6.1 |
   | finite nonzero / 0 | ±∞ (divideByZero) | §7.3 |
   | 0 / finite nonzero | ±0 | §6.3 |
   | finite nonzero / finite nonzero | `round(|x|/|y|)`, sign XOR | §5.4.1, §4.3, §6.3, §7.4 |

   0/0 is listed before x/0. Mathlib's deprecated `Data.FP` checks them in the opposite order
   and gets ∞ for 0/0. A golden vector and a mutant in the test suite pin this ordering.

#### NaN policy

Every NaN result is the single **canonical quiet NaN**: sign 0, exponent field all ones,
trailing significand `10…0` (only the quiet bit set). That is **`0x7E00`** in binary16 and
**`0x7FC00000`** in binary32. NaN operands of either sign, signaling NaNs, and NaNs with
payloads all produce it. IEEE §6.2.3 says a quiet-NaN result *should*, not *shall*, carry an
input payload, so this choice conforms. RISC-V F/Zfh and SMT-LIB (one NaN per sort) use the
same policy, and Lean core's float model produces the same pattern. The policy makes the
result a function of the operand bits, which a circuit spec needs.

#### Rounding modes and flags

All five rounding-direction attributes of §4.3 are a parameter (`RoundingMode`). The
binary16 and binary32 instances `divBinary16`/`divBinary32`, like the task, fix `roundTiesToEven`, the default (§4.3.3). The
proofs cover roundTiesToEven only; the other modes are covered by differential testing
(below).

Exception flags (§7) are **not modelled**. The reasons:

* Under default exception handling (§7.1) the delivered result bits do not depend on the flags.
* The challenge scores a circuit on its result bits. Flags would add five outputs that players
  could trade area against.
* §7.5 leaves the tininess convention (before or after rounding) to the implementation for
  binary formats, so a flags spec would have to pin one convention arbitrarily.

A flags variant (`invalid`, `divideByZero`, `overflow`, `underflow` with a `Tininess`
parameter, `inexact`) would be a natural "hard mode" later.

#### Out of scope

* Exception flags, traps, and alternate exception handling (§7, §8).
* NaN payload propagation (by policy, see above).
* Decimal formats.
* Other operations: `round` is generic and could be reused for `×`, `+` and `√`, but only
  division is specified and validated.

### What is proved (`reference/fdivp.lean`, section `IEEE754Proofs`)

Five statements are defined as `Prop`s in the trusted file and proved **for every format**
in the reference proof (`reference/fdivp.lean`, section `IEEE754Proofs`; until 2026-11-03 the module
`spec/IEEE754Proofs.lean`, which the docstrings of `IEEE754.lean` still name). They are stated with bit patterns, `decode`, `Datum.value?`, `BitVec.msb`
and integer inequalities only. None of them mentions `round`.

In `DivideIsNearestTiesToEven`, `DivideOverflowsAtThreshold` and `DivideOfNumbersIsNotNaN`,
`a` and `b` are bit patterns with exact values `x` and `y` (zero or finite operands) and
`y ≠ 0`. `DivideSignIsXor` covers all bit patterns.

* **`DivideIsNearestTiesToEven f`**. Suppose the roundTiesToEven quotient has an exact value
  `r` (it is zero or finite). Then:
  * no finite number `v` of the format is strictly closer to `x / y` than `r`:
    `NoFarther r v (fracDiv x y)`, i.e. `|r − x/y| ≤ |v − x/y|` by cross-multiplication;
  * if some `v ≠ r` is equally close, the delivered pattern's last bit is 0 (ties to even).
* **`DivideOverflowsAtThreshold f`**. The roundTiesToEven quotient is an infinity exactly when
  `|x/y| ≥ 2^emax × (2 − 2^(−p))`, the §4.3.1 threshold. As integers:
  `d · 2^emax · (2^(p+1) − 1) ≤ |n| · 2^p` for `x/y = n/d`.
* **`DivideOfNumbersIsNotNaN f`**. Under every rounding mode, the quotient is an infinity or
  has an exact value; it is never a NaN (§7.2). This closes a gap the first two leave open on
  their own: the first applies only to results with a value and the second only says "not an
  infinity" below the threshold, so a divider that returned a NaN for every quotient below the
  threshold would satisfy both. This statement rules that divider out.
* **`DivideSignIsXor f`**. For **all** bit patterns and every rounding mode, a non-NaN result
  has sign bit `a.msb ^^ b.msb` (§6.3). This includes zeros, infinities, overflowed results
  and the special-case table.
* **`DivideIsUniquelyCharacterized f`**. Any bit pattern `R` with the four properties above
  (stated for `R`, at roundTiesToEven) equals `divide f .roundTiesToEven a b`.

So, for operands that are numbers with a nonzero divisor, the four properties are a complete
specification of the binary16 and binary32 instances `divBinary16`/`divBinary32`. A reader who trusts the statements need not read `round`.
The remaining operand pairs are a NaN or infinite operand, or a zero divisor. Their results are
the explicit special-case table in `divide`, meant to be read directly. The signs of its
non-NaN results are also covered by `DivideSignIsXor`; its NaN results are the canonical NaN
by inspection and by the golden vectors. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Proof outline: in units of `2^qmin`, `roundUnits` writes `N = c·(D·2^j) + r`. A gap lemma
shows that no magnitude `c'·2^i` with `c' < 2^p` lies strictly between `c·2^j` and
`(c+1)·2^j`, which gives the nearest and tie properties. The overflow threshold follows from
them: the threshold is the midpoint between `maxFinite`, whose significand `2^p − 1` is odd,
and `2^(emax+1)`. Bit-field lemmas show that the encoder round-trips, that every finite
pattern's value is a representable number of units, and that `round` writes the sign it is
given and never an all-ones exponent with a nonzero trailing field. For uniqueness, every
pattern with a value is the encoding of its own units. A nearest magnitude is one of the two
neighbours `c·2^j`, `(c+1)·2^j`, and those two never both have even significands.

## Rules for this task

* **Banned run-time operators: `/ % **`**: division is the task. Constant arithmetic (parameter
  expressions, `$clog2`, genvar indices) stays allowed; `+ - *`, shifts and comparisons are free (the ban on run-time
  ordering comparisons, decided 2026-11-05, is for the tasks that ban `+` or `-`, and this one bans neither). The checker enforces it
  twice (`score/banlist.py`: a pyslang front check and a Yosys backstop). `tests/fdivp/negative/div_op.sv` is a correct
  divider (the reference with its division rewritten as `/` and `%`) that is rejected for it.
* **The design must be generic.** The statement is for ALL formats, so a design with a width cap, or one that is right only
  at `(5, 11)`, has no proof. The advisory oracle and the post-synthesis check see only the SCORING POINT `(5, 11)`; the
  extractor's multi-point cross-check loads the design at the probe points `(2, 2)`, `(2, 3)`, `(3, 2)`, `(3, 4)`, `(4, 5)`,
  `(5, 11)`, `(8, 8)`, `(8, 24)`.
* **Write in the ls-sv subset** (the `design` stage must load it at those points). The reference uses continuous assigns
  over vectors (`+ - << >>`, `?:`, comparisons, reductions, part selects), two `generate for` families over packed
  two-dimensional arrays, and nothing else; the Newton reference adds the run-time `*` and a `$clog2` localparam, the SRT
  reference nothing (its selection tables are `?:` trees over constants, its stage count affine in `P`). If the
  design is to be proved with the `sv_comb` tactics, read `PROVING.md` and the findings below: part selects with
  parameter-affine bounds, one-bit comparison signals, a `$clog2` only in an `integer` localparam (its value is an
  opaque atom in the obligations), no `**`.
* **The proof is symbolic and for all formats.** No enumeration of operands, no `bv_decide` (the checker supports no
  external solver: `allow_bv_decide: false`), no `native_decide`, no `sorry`. Axioms `propext`, `Classical.choice`,
  `Quot.sound`.
* **Proof time limit: `time_limit_s = 300`** (CPU seconds), the one limit of every task (a ceiling, not a rule that a slow reference can
  raise). In CPU seconds, what the limit counts (2026-11-06, three cold `check.py` runs each, `score/time_limits.json`):
  `fdivp` 82.2, 79.1 and 80.4, `fdivp_newton` 120.7, 108.3 and 108.4, and `fdivp_srt` 181.8, 160.5 and 160.2 CPU s,
  `fdivp_srt` over the 150 CPU s target. Before, in wall-clock seconds: cold `solution` stage of the reference, three
  `check.py` runs (2026-11-03, a shared machine at load average
  9.5, 6.0 and 6.8): 70.3, 64.5 and 71.6 s, above the target of 60 s: the self-contained proof compiles the facts about
  the spec, the certificate, the math layer and the glue in the solution stage (they were a prebuilt library until
  2026-11-03: 31.0, 26.0 and 24.8 s). Heartbeats: `sv_structure` 239 thousand, the whole `solution` 388 thousand. The
  Newton reference, measured the same way (2026-11-04, load average 4 to 6): 44.6, 45.8 and 45.3 s; heartbeats 315 and
  536 thousand. The SRT reference (2026-11-05, each run started at a load average below 8): 78.6, 73.2 and 69.9 s, the
  slowest of the three; heartbeats 672 and 700 thousand. Its margin under the ceiling depends on the machine's load:
  before it took the shared obligations (959 thousand heartbeats for `solution`), runs at load 10 to 17 took 92 to
  121 s (`tests/fdivp/results/srt_S0.md`).
* **Scoring** at the scoring point `W = 5, P = 11` (binary16), no depth budget. The one ranked number is area x
  time on sky130 A0' (A0' decided 11/03, the product 11/05; svGolf `README.md`, "Scoring"): the cell area in um^2
  times the critical-path delay of the scored netlist of the pinned two-stage Yosys + ABC flow, weighed by
  `score/ppa.py` (`sky130_a0_v3`). Par, the proved SRT divider `fdivp_srt`, is 12356.8512 um^2 x 27592 ps =
  340 950.2 um2*ns (the restoring reference: 9675.5296 um^2 at 37984 ps, `score/tests/ppa/expected_ppa.json`). The
  Pareto frontier of area and time, area in NAND2 gate equivalents and depth in gates are extra columns, for
  exploring; `python3.12 score/ppa.py solution.sv --task tasks/fdivp --no-mapped [--path]` measures a design in
  seconds, with no Lean. The score is deterministic, the same file always scoring the same on the reference
  build: names, comments, blank lines, whitespace and the file name never change it, while operand order, how
  a chain of gates is grouped, gate forms and **the order of the statements** do (a few percent here), and
  trying them is golf: a golfer runs the pinned flow on candidate orders and submits the best (svGolf
  `README.md`, "Scoring"). This task is where another build of the same Yosys version was measured to differ
  (2026-11-05: three of 52 designs, all of this task, up to 2.9% in delay; score/PPA.md, "Determinism
  (measured)"). Every number can be
  reproduced bit for bit with the reference build: score/PPA.md, "Reproduce a score".
* Post-synthesis check (`task.json` `postsynth`): ls-sv's reading and the scored netlist must agree on the fixed corners,
  the 18 x 18 special operand pairs listed there (binary16: signed zeros, extreme subnormals and normals, ±1,
  ±max, ±inf, NaNs), the harvested comparison constants and 4000 seeded random pairs (4443 vectors on the reference;
  ls-sv about 12 ms per vector, 54 s in the whole stage). The advisory oracle (`oracle.py`) agrees on all of them.
* No x or z value may arise (the source gate and the `fourstate` stage), as for every task.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

`check.py` accepting `solution.sv` + `Solution.lean`:

```bash
python3.12 check.py tasks/fdivp solution.sv Solution.lean
```

All stages pass: the source gate, the pinned extractor (the top module has exactly the parameters `W`, `P`), the banlist,
`fourstate`, ls-sv loading the design at the scoring point and the probe points, the proof of `Submission.Goal` compiling
within the time limit, the comparator and `leanchecker`, scoring and the post-synthesis check.

## The reference (`reference/`)

`reference/fdivp.sv` (design "D3" of `design/fdiv-param/`, 34 sites) is the flat binary16 divider of the former
16-bit task made generic and word-level. The datapath:

1. unpack and classify the operands (NaN, inf, 0) with reductions over parameter-sized windows;
2. significands with the hidden bit, effective exponents (a subnormal has exponent 1);
3. a **linear normalizer** of `P - 1` one-bit stages (`generate for`, a 2-D array of rows; the `EW`-bit exponent register
   counts the shifts down), instead of the flat binary16 divider's 8/4/2/1 shifter;
4. `P + 2` **restoring-division steps** (`generate for`, one quotient bit per step) with the last remainder as the sticky bit;
5. quotient normalization to `P` significand bits plus a round bit (`adj`, `qm`);
6. the exponent `E = ya - yb + emax - adj` in `EW = W + P + 1` bits, two's complement, no offset; `nrm` (`E >= 1`) and `ovf`
   (`E >= 2^W - 1`) are read from its sign bit and two reductions;
7. a run-time shifter `qs = qm >> dsh` with `dsh = 1 - E` for a subnormal result (any amount; a shift of `P + 1` or more
   empties `qm`) and the sticky test `(qs << dsh) != qm`;
8. round to nearest even by adding the increment to the packed `{exponent, fraction}` word (the carry moves a subnormal to
   the least normal and the largest finite to `inf` for free);
9. the output by fields (sign, exponent field, top fraction bit, a generate family for the low fraction bits).

**Score** in the extra GE columns (`score.py`; in `tests/expected.json`, re-measured by `tests/run.py`; the ranked A0' numbers are under "Scoring" above): **2166.076 GE, depth 289** at `(5, 11)`
(1515 gates); 8826.016 GE, depth 1261 at `(8, 24)`; 1369.84 GE, depth 184 at `(8, 8)`; 102.985 GE, depth 18 at `(2, 2)`.
The baselines (`tests/fdivp/baselines/`) are: D1, the natural parametric form (`$clog2`, `2**`, replication,
logarithmic normalizer and shifter; validated, outside today's tactic fragment, ls-sv cannot load it): **1911.446 GE,
depth 300** at `(5, 11)` and 7450.536 at `(8, 24)`; D2, the fragment-friendly form (about 90 plain sites): 2314.058 GE,
depth 295 and 9813.601 at `(8, 24)`; and the flat binary16 divider (the former 16-bit task's reference) under the parametric header (right at
`(5, 11)` only): 1944.775 GE, depth 303. So the proved reference is 13 % larger than D1 and 12 % larger than the
hand-flattened binary16 divider (1929.778 in the former 16-bit task): the price of a proof for every format. Golf targets: the linear normalizer and the
linear denormalizer are where the logarithmic forms of D1 save area; the serial `P + 2` restoring steps dominate the depth.

**The proof** (`reference/fdivp.lean`, `check.py` accepts it, the `solution` stage takes about 70 s): `sv_structure` (with a
rank certificate: the plain sites by depth, the families `norm` and `div` by stage; `maxHeartbeats 300000`) and
`sv_interface` (after unfolding `task W P`, which the tactic does not read as an application), `sv_equations` (`maxHeartbeats
500000` for the whole theorem), then ONE theorem, `SvGolf.FdivParam.Glue.chain` (section `DpG5`): the 34 printed
equations in, the value `XF.val q (W + P) = OutN f a b` out; and `OutN_fdivBits` (section `DpU`) identifies `OutN` with
the task function for every format. The five `cover` obligations of the generate families are conjunctions: `refine ⟨?_, ?_⟩ <;>
sv_cover` closes them. The limits assume the `sv_comb` tactics with the grouped obligations of WP-LIN (without it the
structure costs 895 thousand heartbeats and the whole solution 2.38 million).

The file is self-contained: it imports the generated design, the framework, the `sv_comb` tactics and the general ls-sv
proof library `LeanModels.Sv.Lib` (`Nat` arithmetic, the `Nat` values of the word-level bit helpers `XF.*`, row-major
offsets, restoring division; task-independent, Mathlib-free, prebuilt in the checker's trusted stage), and proves the rest
in sections: `IEEE754Proofs` (facts about the spec, its five characterization theorems included), `ScaleInvariance`,
`RneInterval`, `RoundingBounds` and `CertF` (the rounding certificate `certF_bridge`, for every format: a proof for ANY
other divider starts here), `DpN` .. `DpU` (the arithmetic of THIS datapath on `Nat`, the model `OutN` and
`OutN_fdivBits`), `DpG1` .. `DpG5` (the glue: one lemma per shape of equation of THIS netlist, and `chain`). So: **copy
the reference's netlist and you inherit the proof**; **change a signal of the netlist and the corresponding hypothesis of
`chain` no longer matches** (a type mismatch at the `chain` application, which is how the attacks fail); a different
netlist needs its own chain, a different datapath its own `OutN`.

## The Newton reference (`reference/fdivp_newton.sv`)

The second proved reference is a Newton-Raphson divider: D3 with its `P + 2` restoring steps replaced by a reciprocal,
a quotient estimate and an exact correction (46 sites: 37 plain, and 4, 4 and 1 in the generate families `norm`,
`newton` and `lo`). Unpacking, classification, the normalizers, the exponent, the denormalizer, the rounding and the
output stage are D3's, so the core has the contract of D3's quotient `qq` and sticky bit. It is not competitive and is
not meant to be: it is a reference for a second algorithm, with a step count logarithmic in `P`, and for the run-time
`*` of the tactic fragment. The core, in fixed point with `F = P + 4` fraction bits:

1. the initial reciprocal `r0 = 45/32 - 15/32·d` of the divisor's significand `d` in `[1, 2)` (relative error at most
   1/16, no table and no multiplier: `15·mb = 16·mb - mb`);
2. `NI = $clog2((P + 9) / 8) + 1` Newton steps `r ← r·(2 - d·r)` (a generate family, two products per step, every product
   truncated): 1 step for `P <= 6`, 2 for `P <= 14` (binary16, bfloat16), 3 for binary32, 4 for binary64;
3. the estimate `qf = (ma·r) >> (F - 2)`, at most 2 below the quotient `qq = floor(ma·2^(P+1) / mb)`;
4. the exact correction: the remainder `rm = ma·2^(P+1) - qf·mb` modulo `2^(P+2)`, `qq = qf + [rm >= mb] + [rm >= 2·mb]`,
   and the sticky bit is zero iff `rm` is 0, `mb` or `2·mb`.

One change is for the pinned scoring flow: the estimate is perturbed when an exponent field is all ones (`qe = qf - a[0] - b[0]`
there, an infinite or NaN operand, where the output stage never reads the core). The facts that only the Newton error
bound proves (`ge2 = 0`, `rm < 2·mb`) are then false over ALL inputs; with them true, ABC's `&fraig -x` in the pinned flow
spends a SAT problem on each such near-constant node and does not finish at `(5, 11)` in 1800 s. With `qe` it finishes
in about 60 s. The proof needs one mux lemma for it (`qe = qf` for finite operands).

**Score** (`tests/expected.json`): **7892.452 GE, depth 252** at `(5, 11)` (5691 gates; D3: 2166.076, 289), 4286.665 GE,
depth 211 at `(8, 8)`, 115.318 GE, depth 21 at `(2, 2)`. It is not scored at `(8, 24)`: the pinned flow takes more than
30 min there. So it is 3.6 times D3's area at `(5, 11)` and 13 % shallower in gates; in the ranked sky130 columns (A0',
`sky130_a0_v3`, buffering only: one `buf_1` on one net; inputs driven by the default `buf_8`; every load pin read per
edge) it is 33825 µm² and 40031 ps against D3's 9676 µm² and 37984 ps (before the per-edge loads 39692 and 37872; v2,
inputs driven by `buf_1`: 39689 and 37872). The "large but shallow"
premise does not hold at these widths:
the multipliers of each Newton step are about as deep as the restoring chain they replace.

**Validation** (records in `tests/fdivp/results/newton_*`): Verilator against `oracle.h` on every pair of the 66 formats
with `W + P <= 14`, on all 2^32 pairs at `(5, 11)`, `(8, 8)` and `(2, 14)`, and 200,000 corner-rich vectors at 14
formats up to `(11, 53)` and `(2, 62)`: 0 mismatches.

**The proof** (`reference/fdivp_newton.lean`, 5,801 lines, `check.py` accepts it, the cold `solution` stage takes about
50 s; 45 s while the core's mathematics was prebuilt in the library). The sections `IEEE754Proofs` .. `DpG4` are D3's, copied verbatim (`tests/fdivp/shared_sections.py`). Section
`NwG1` is the glue of the core: `newton_rows` (the family, an induction over the steps on the value lemma of `*`,
`XF.val_mulBits`), one lemma per core site, and `core`: for `N >= 1` steps with `P + 2 <= 2^(N+2)`, the printed equations
of the core give restoring division's quotient and sticky bit. The mathematics of the core is section `NwCore`: the
error of the reciprocal after each step, `T·E <= S + 4·A·T` with `T = 2^(2^(k+2))`, the estimate and the correction,
`newton_rest`, and `nwNI_spec` for the step count. It models this core and nothing else, so it is compiled in the
solution stage like a player's own proof of their own core (it was the prebuilt library module
`LeanModels/Sv/Lib/Newton.lean` until 2026-11-04; decided 11/04: the shared library holds only results any proof of a
class of designs would use). Section `NwG2`
has this netlist's `Glue.chain` over its 46 printed equations, and the `Submission` section the rank certificate (every
site after the core above every Newton step, which needs `clog2_le`), `sv_interface` and the solution. Heartbeats:
`sv_structure` 315 thousand, the whole `solution` 536 thousand.

## The SRT reference (`reference/fdivp_srt.sv`)

The third proved reference is a radix-4 SRT divider adapted from CORE-V Wally (`src/fpu/fdivsqrt/`, Apache-2.0 WITH
SHL-2.1: the provenance header lists the source files, the authors and the ten changes, each with its reason, and
`reference/LICENSES/` holds the licence texts): D3 with its `P + 2` restoring steps replaced by `N = (P + 2) / 2 + 1`
unrolled radix-4 stages (69 sites: 45 plain, 4 in the generate family `norm`, 19 in `srt` and 1 in `lo`).
Unpacking, classification, the normalizers, the exponent, the denormalizer, the rounding and the output stage are D3's,
so the core has the contract of D3's quotient `qq` and sticky bit, the interface the Newton core plugs into as well.
A stage:

1. estimates the carry-save remainder `ws + wc` from its 8 top bits and selects a digit `q` in `{-2, ..., 2}` by
   comparing the estimate with four constants chosen by the 3 divisor bits after the leading one (Wally's constants, as
   four 3-level `?:` trees, a thermometer code `g2 <= g1 <= g0 <= gm`);
2. forms `4·(R - q·dv)` by one carry-save row (the multiple `-q·dv` from the divisor and its precomputed shifts and
   complements);
3. appends the digit to `U` (the quotient so far) and `UM = U - 1` by on-the-fly conversion.

After the last stage `qq = rs < 0 ? UM : U` and the sticky bit is `rs != 0`, with `rs = ws + wc` the one adder of the core.

**Score** (`tests/expected.json`): **2787.652 GE, depth 189** at `(5, 11)` (2012 gates; D3: 2166.076, 289), 1907.436 GE,
depth 141 at `(8, 8)`, 96.652 GE, depth 19 at `(2, 2)`, 10139.803 GE, depth 387 at `(8, 24)`. It is the shallowest of the
three: 1.29 times D3's area for 65 % of its depth at `(5, 11)`. In the ranked sky130 columns (A0', `sky130_a0_v3`) it
is 12356.9 µm² and 27592 ps against D3's 9675.5 µm² and 37984 ps (`score/tests/ppa/expected_ppa.json`): a point of the
frontier with the lowest delay of every scored fdivp design (references and baselines).

**Validation** (records in `tests/fdivp/results/srt_*`, `srt_S0.md` section 4): Verilator against `oracle.h` on every
pair of the 66 formats with `W + P <= 14`, on all 2^32 pairs at `(5, 11)`, `(8, 8)` and `(2, 14)`, and on 200,000
corner-rich vectors and 432,400 sampled pairs at 14 formats up to `(11, 53)` and `(2, 62)`: 0 mismatches. The selection
table is checked exactly over every one of its cells (section 4.1 there, and in the proof).

**The proof** (`reference/fdivp_srt.lean`, 6,090 lines, `check.py` accepts it, the cold `solution` stage takes 160 to 182 CPU s, 64 to 78 s of wall clock (2026-11-06, `score/time_limits.json`; 70 to 79 s of wall clock at a load average below 8 on 2026-11-05). The sections `IEEE754Proofs` ..
`DpG4` are D3's, copied verbatim (`tests/fdivp/shared_sections.py`). Section `SrCore` is the mathematics of the core:
the selection table checked cell by cell by one kernel `decide` (`srt_tbl`: the constants are a thermometer, and in every
cell of estimate and divisor bits the selected digit keeps `|3R| <= 8·dv`), the estimate, containment, the carry-save
row, on-the-fly conversion, the invariant over the stages (`SrtInv`, `srt_step`, `srt_core`) and `srt_rest`: after `N`
stages the corrected quotient and the sticky are those of `P + 2` restoring steps. It models this core and nothing
else, so it is compiled in the solution stage (it was the library module `LeanModels/Sv/Lib/Srt.lean` until 2026-11-05,
moved by the rule of 11/04); the two bit-level facts it needed, the value of a carry-save adder row (`XF.val_csa`) and
of an XOR with the top-bit constant (`XF.val_xor_top`), are general and stay in `LeanModels.Sv.Lib`. Section `SrG1` is
the glue of the core, one lemma per printed shape (the family `srt` row by row) and `core`, one application of
`srt_rest`; section `SrG2` has `g_inc_rnz` (the rounding increment with a one-bit sticky), `fin_ops` and this netlist's
`Glue.chain` over its 69 printed equations; the `Submission` section has the rank certificate (19 ranks per stage),
`sv_interface` and the solution. Heartbeats: `sv_structure` 672 thousand (with the shared obligations), the whole
`solution` 700 thousand.

## Validation (`tests/fdivp/validate/`, records in `tests/fdivp/results/`)

The reference is simulated with Verilator against a C++ oracle (`oracle.h`, 128-bit integers, the quotient rounded at the
spacing of its binade) that is itself tied to three other implementations (`oracle.py` in exact `Fraction` arithmetic,
`fdivp_model.oracle_int`, and `spec_validate/oracle.py`, the one validated against the Lean spec): step `oracles`. Results
(2026-11-02, `tests/fdivp/results/`):

| step | what | pairs | mismatches |
|---|---|---|---|
| exhaustive, `K = W + P <= 14` | all **66 formats** `(W, P)` with `2 <= W`, `2 <= P`, `W + P <= 14` | 3.82 x 10^9 | 0 |
| exhaustive, 2^32 pairs | `(5, 11)` (binary16) and `(8, 8)` (bfloat16-like) | 2 x 4,294,967,296 | 0 |
| corner-rich vectors | 200,000 per format at 12 larger formats up to `(11, 53)`, `(2, 62)`, `(3, 60)`, `(20, 12)` | 2.4 x 10^6 | 0 |
| Python model | `fdivp_model.model3` (the reference's netlist in Python) = the exact-integer oracle | the vectors above | 0 |

Because the reference is PROVED equal to the Lean spec for every format, each simulated pair is also a test of `divide`
itself at that format (`REVIEW.md`). The attacks and negatives below are simulated too (`tests/run.py`, step `validate`).

## Negative designs and attacks

`tests/fdivp/negative/` (all rejected, each with the first reference's proof, at the stage in `tests/expected.json`):

| design | what it tries | how it fails |
|---|---|---|
| `div_op.sv` | the reference with the division written as `/` and `%` (right at every format) | banned run-time operators (`banlist`) |
| `rm_pin.sv` | the reference plus an unread input `rtz` | the interface conjunct (`solution`) |
| `status_flag.sv` | the reference plus an `inexact` output | the interface conjunct (`solution`) |
| `wide_q.sv` | the reference with a `W + P + 1`-bit `q` (top bit 0) | the interface conjunct (`solution`) |
| `const_nan.sv` | `q` = the canonical NaN always | wrong on almost every pair (`solution`) |

`tests/fdivp/attacks/`: eight correct-looking netlists, each the reference D3 with ONE change that is wrong on some format
(exhaustive Verilator counts at small formats in `tests/fdivp/results/`). Each passes every check up to the proof and
must FAIL the reference's proof at the `solution` stage:

| design | the change | wrong on |
|---|---|---|
| `inc_tie_odd.sv` | `inc` rounds exact ties to the ODD neighbour (`~qs[1]`) | every format, ties only (subnormal range) |
| `dsh_wrap64.sv` | the denormalizing shift amount modulo 64 | `W >= 7` (right at `(5, 11)`, binary16) |
| `ew_narrow.sv` | the exponent register `W + 2` bits wide | `P` large against `W`, e.g. `(2, 8)`, `(2, 30)` (right at `(5, 11)`, `(8, 24)`, `(11, 53)`) |
| `zero_by_zero_inf.sv` | `0 / 0` gives `inf` | exactly 4 pairs per format |
| `rr_sticky_dropped.sv` | the division's sticky bit ignores the last remainder | a large share of the pairs, every format |
| `ftz.sv` | flush to zero: a result below the normal range is `±0` | every format (subnormal results) |
| `ovf_late.sv` | the overflow test one too late (`E >= 2^W`) | every format (results with the all-ones exponent) |
| `dsh_sticky_short.sv` | the denormalizer's sticky test does not see the two lowest bits of `qm` | subnormal results, e.g. `(3, 4)`, `(4, 6)`, `(2, 8)`, `(8, 2)` |

And seven of the Newton reference, each its netlist with ONE change in the core (the mutants of the design's own
validation), submitted with the Newton proof, which they must FAIL at the `solution` stage (`tests/fdivp/attacks/README.md`
has the counts):

| design | the change | wrong on |
|---|---|---|
| `newton_f_minus2.sv` | working precision `F = P + 2` instead of `P + 4` | every format |
| `newton_ge1_const.sv` | the correction always adds 1 | every format |
| `newton_ni_minus1.sv` | one Newton step fewer | from `P = 3` on |
| `newton_no_ge2.sv` | the correction stops at `qf + 1` | only where the estimate is 2 below: over `W = 2`, `P = 2..12` only at `P = 6`; right on all 2^32 pairs of `(5, 11)` |
| `newton_r0_off.sv` | the initial reciprocal's constant 47/32 instead of 45/32 | some `P` (6, 11, 12 among `W = 2`, `P = 2..12`) |
| `newton_rnz_no2mb.sv` | the sticky bit forgets the remainder `2·mb` | as `newton_no_ge2`: `P = 6` among the small formats, right at `(5, 11)` |
| `newton_rnz_nomb.sv` | the sticky bit forgets the remainder `mb` | every format, exact quotients only |

And ten of the SRT reference, each its netlist with ONE change in the core (S0's ten mutants of the design's validation,
re-applied to the committed file), submitted with the SRT proof, which they must FAIL at the `solution` stage
(`tests/fdivp/attacks/README.md` has the counts):

| design | the change | wrong on |
|---|---|---|
| `srt_qds_t2_d0.sv` | a selection constant: `t2` at `da = 0` is 75, not 76 | from `P = 5` on (the bad cell is not reached below) |
| `srt_qds_t1_d0.sv` | a selection constant: `t1` at `da = 0` is 66, not 68 | from `P = 5` on |
| `srt_qds_tm_d7.sv` | a selection constant: `tm` at `da = 7` is 38, not 41 | from `P = 5` on |
| `srt_no_corr.sv` | no final correction (`qq = u[N]`) | from `P = 3` on |
| `srt_drop_carry.sv` | one carry of the carry-save row dropped | every format |
| `srt_no_cin.sv` | the `+1` of the negated multiple dropped | every format |
| `srt_sticky_sign.sv` | the sticky bit reads the residual's sign | from `P = 3` on |
| `srt_stages_m1.sv` | one stage fewer (`N = H`) | every format |
| `srt_otfc_um.sv` | on-the-fly conversion: `UM'` for `q = 0` taken from `U` | from `P = 3` on |
| `srt_otfc_digit.sv` | on-the-fly conversion: the pair appended for `q = -1` is `10`, not `11` | every format |

## Findings

* **The ladder of designs.** D1 (natural, 165 lines) is smallest but outside the tactic fragment in six independent ways and
  refused at load; D2 (fragment-friendly, about 90 plain sites) is inside but costs `n^2` in the tactics; D3 (the
  reference) has 34 sites by folding the bit-level structure into vector sites and generate families. With the grouped
  obligations of WP-LIN the tactics cost 239 thousand (`sv_structure`) and 320 thousand (`sv_equations`) heartbeats on D3.
* **`sv_interface` and a two-parameter task.** The statement is `(task W P).StatementFixed (sem W P)`; the tactic unfolds the
  task only when it is a constant. `unfold SvGolf.Tasks.FdivP.task` before `sv_interface` fixes it.
* **`check.py --tactics`** (advisory) now states `example (W : Nat) (P : Nat) : CombDesign (design.sem W P)` for a task with
  several parameters (it returned no probe for more than one); `tests/checker/test_advisories.py` covers it.
* **Statement order moves the score of a netlist** (first found on the flat binary16 divider, WP-H2): decided to stay.
  Every reordering of the reference, D1 and D2 moves their scores at `(5, 11)` (`tests/expected.json`,
  `canonical_layout`), which is why no divider is in the `canon` step's list.
