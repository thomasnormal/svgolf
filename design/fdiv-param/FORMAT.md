# The format boundary of the parametric `fdiv` task

Hard gate 4 of `PLAN2.md`: the well-formedness predicate, written down. The compiled facts are in
[FormatFacts.lean](FormatFacts.lean) (every `Format`, symbolic, standard axioms, no `sorry`).

## What a "format" is

The trusted spec (`svgolf/spec/IEEE754.lean`, IEEE 754-2019 §3.3 and §3.4) takes `Format { w, p }` with the side
conditions `2 ≤ w` and `2 ≤ p` built into the structure (`Format.hw`, `Format.hp`). The task's range is exactly that and
nothing more:

    FormatOK w p  :=  2 ≤ w ∧ 2 ≤ p          -- no upper bound on either

* `w` — width of the biased exponent field; `p` — precision including the implicit bit; `t = p - 1` trailing bits;
* storage width `k = 1 + w + t = w + p` (the module's ports are `[W+P-1:0]`; `k_eq`);
* `emax = 2^(w-1) - 1`, which is also the bias, and `emin = 1 - emax`; `emax ≥ 1` (`emax_pos'`);
* `scale = emax + p - 2` units per least subnormal, `scale ≥ 1` (`scale_pos`); `t ≥ 1` (`t_pos`).

The smallest legal format is `(2, 2)`: a 4-bit pattern with exponent bias 1. Table 3.5's formats (binary16 `(5, 11)`,
binary32 `(8, 24)`, binary64 `(11, 53)`) and the bfloat16-like `(8, 8)` are inside the range.

## What the statement fixes (so the design may rely on it)

* **Rounding:** roundTiesToEven only (`divide f .roundTiesToEven`). The other four modes exist in the spec but are not
  part of this task.
* **Special values:** the spec's table, unchanged for every format: NaN operands, `0/0`, `inf/inf` give the canonical
  quiet NaN `sign 0, exponent all ones, trailing 10…0`; `x/0` is a signed infinity; `0/y` a signed zero; infinite
  numerators/denominators as in IEEE §6.1 to §6.3 and §7.2. Signalling NaNs give the canonical NaN.
* **Subnormals:** gradual underflow, no flush to zero (§3.3, §7.5): every finite magnitude is a natural multiple of one
  unit `2^qmin`; the least positive subnormal is one unit.
* **Overflow:** the §4.3.1 threshold, result infinity (roundTiesToEven).
* **Operands:** every pair of `k`-bit patterns; there is no precondition besides `FormatOK`.

## What the proof may use, and what is still to be proved

* The rounding certificate for every format is DONE: `certF_bridge`, `fdivF_cert`, `divide_iff_certAllF` (`CertF.lean`).
* The restoring-division recurrence is already format-agnostic in `SpecFacts.lean` (`restore_spec`: after `n + 1` steps
  `restQuo d x (n+1) = 2^n * x / d` and `restRem d x (n+1) = 2 * (2^n * x % d)`, for all `d`, `x`, `n`). Gate 3 of WP-H1
  (not started) instantiates it at the step count the rounding decision needs. The step count is fixed by that lemma, not
  assumed here; the usual figure is `p + 2` quotient bits for operands whose significand ratio lies in `(1/2, 2)`
  (`p` bits, a guard bit, and the sticky bit from the remainder).
* Normalization of subnormal operands (one bit per stage is acceptable), the exponent arithmetic on `Int` and the result
  packing (overflow, gradual underflow) are also Gate 3 lemmas.

## What is validation, not proof

Exhaustive simulation of the small formats (`w ∈ 2..4`, `p ∈ 2..5`, at most 2^18 operand pairs per format) and sampling
at binary16/32/(8,8) find bugs in a design and in the contract; they do NOT support the symbolic theorem, which is for
every `FormatOK` pair.
