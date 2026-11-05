import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib

/-!
# Reference solution for task `fdivp`, the Newton-Raphson divider: IEEE 754 division for every `W >= 2`, `P >= 2`

A submission like any player's `Solution.lean`, and the task's second proved reference (the first is `fdivp.lean`, D3,
a restoring divider). It proves `theorem Submission.solution : Submission.Goal` for the design `reference/fdivp_newton.sv`:
D3's datapath with its `P + 2` restoring steps replaced by a Newton-Raphson core, an initial reciprocal
`r0 = 45/32 - 15/32·d`, `NI = $clog2((P + 9) / 8) + 1` Newton steps `r ← r·(2 - d·r)` (word-level `*`, a generate family
`newton`), a quotient estimate `qf` at most 2 below the quotient, and an exact correction by the remainder `rm` modulo
`2^(P+2)`. Unpacking, classification, the normalizers, the exponent, the denormalizer, the rounding and the output stage
are D3's. It is not competitive (at `(5, 11)`: 7892 GE and depth 252, against D3's 2166 GE and depth 289); it is a
reference for a second algorithm, with a logarithmic step count, and for the word-level `*` of the tactic fragment.

The file is self-contained like `fdivp.lean`: besides the generated design module and the framework, it imports only
the general ls-sv proof library `LeanModels.Sv.Lib` (restoring division, `Nat` and `XF.val` facts). The mathematics of
the core is this file's own section `NwCore`. Sections:

1. `IEEE754Proofs` .. `DpG4`: copied VERBATIM from `fdivp.lean` (`tests/fdivp/shared_sections.py` checks that they stay
   byte-identical): the facts about the spec, the certificate `certF_bridge`, the math layer with the model `OutN`
   (whose quotient and sticky are those of `P + 2` restoring steps, `qqN` and `rrN`), and the glue of the sites the two
   designs share. D3's `div_rows` (`DpG1`), `g_ext` (`DpG2`) and `g_inc` (`DpG3`) come along unused.
2. `NwCore`: Newton-Raphson division as the core computes it: the error of the reciprocal after each step, the
   estimate and the correction, `newton_rest` (the core's quotient and sticky are restoring division's) and `nwNI_spec`
   (the step count qualifies). It was the library module `LeanModels/Sv/Lib/Newton.lean` until 2026-11-04.
3. `NwG1`: the glue of the Newton core. `newton_rows` is the family (an induction over the steps, on the value lemma of
   `*`); `core`: for normalized significands and `N ≥ 1` steps with `P + 2 ≤ 2^(N+2)`, the printed equations of the
   core give the quotient `qq` and the sticky `rnz` of restoring division.
4. `NwG2`: `g_inc_rnz` (the rounding increment with the one-bit sticky `rnz`) and `Glue.chain`, `DpG5`'s chain for this
   netlist.
5. `Submission`: the proof.

## Route

1. `fdiv_struct` / `fdiv_interface`: `sv_structure` with the rank of the design (the plain sites by depth, the families
   `norm` and `newton` by their stage, the sites after the core above every Newton step: the step count is at most
   `(P + 9) / 8 + 1` by `clog2_le`, which is also the generate-fuel bound of the family) and `sv_interface`.
2. `solution`: `CombTask.satisfiedAt_of_comb` reduces to one settled-state lemma; `sv_equations` hands over the 46
   equations of the netlist; the whole arithmetic is `SvGolf.FdivParam.Glue.chain` (section `NwG2`), with the vectors of
   the constants `6'd45` and `4'd0` of `r[0]` checked by `decide`, and `SvGolf.FdivParam.OutN_fdivBits` (section `DpU`)
   identifies its value with the task function. The residual obligations are closed by `omega`, `split`, `sv_cover`, and
   `simp [LVec.width]` (the widths of the two constants).
3. The side conditions of the chain are proved by `omega` in small contexts (`fin_ops` is a lemma of its own, and no fact
   with a `toNat` or a `natAbs` stays in the chain's context): `omega` reads every arithmetic fact of its context and
   splits on each `toNat`, `natAbs` and disjunction there, and in the chain's full context seven of its calls took
   35 s, against 2 s now.
4. Heartbeats (measured, 2026-11-04): 315 thousand for `fdiv_struct` and 536 thousand for the whole `solution` (D3: 239
   and 388); the limits set are 400 and 700 thousand. Every other option is scoped to its section or to one declaration.
   Elaborated single-threaded, the whole file takes 1,677,866 thousand heartbeats, section `NwCore` 49,233 thousand of
   them (1,627,676 thousand while `NwCore` was the prebuilt `Lib/Newton.lean`).
   Cold `solution` stage, three `check.py` runs (fresh `--stage-dir` each, one at a time, LEAN_NUM_THREADS=2, nice 19):
   49.9, 48.6, 52.7 s (2026-11-04, load average 6.1, 9.9, 6.6 at the start). With `NwCore` prebuilt in the library:
   44.6, 45.8, 45.3 s (load 5 to 6) and 46.9 s (load 9.5).
-/

/-! # Section `IEEE754Proofs`: Facts about the trusted spec: the five characterization theorems (was `spec/IEEE754Proofs.lean`) -/

section IEEE754Proofs

/-!
# Proofs of the characterization theorems for `SvGolf.IEEE754.divide` (untrusted)

This file is *not* trusted material: everything in it is checked by Lean's kernel. It proves,
for **every** binary format `f` (`2 ≤ w`, `2 ≤ p`), the five propositions stated in the trusted
spec `IEEE754.lean`:

* `divide_isNearestTiesToEven f : DivideIsNearestTiesToEven f` — a roundTiesToEven quotient
  that has a value is a number of the format nearest to the exact quotient `x / y`, and on a
  tie its last significand bit is 0 (§4.3.1);
* `divide_overflowsAtThreshold f : DivideOverflowsAtThreshold f` — the quotient is an
  infinity exactly when `|x / y| ≥ 2^emax × (2 − 2^(−p))` (§4.3.1, §7.4);
* `divide_ofNumbersIsNotNaN f : DivideOfNumbersIsNotNaN f` — under every rounding-direction
  attribute, a quotient of two numbers with a nonzero divisor is an infinity or has a value,
  never a NaN (§7.2), so the first two theorems together cover every such quotient;
* `divide_signIsXor f : DivideSignIsXor f` — every non-NaN quotient, for all bit patterns and
  every attribute, has the XOR of the operands' sign bits (§6.3);
* `divide_isUniquelyCharacterized f : DivideIsUniquelyCharacterized f` — any bit pattern with
  the four properties above (at roundTiesToEven) *is* the quotient, so the four properties are
  a complete specification on operands that are numbers with a nonzero divisor.

The statements mention only bit patterns, `decode`, `Datum.value?`, `BitVec.msb` and integer
inequalities, so they check `divide` against the standard independently of how `round`
computes.

Proof outline. Magnitudes are measured in *units* of the least subnormal `2^qmin`
(`IsUnits`). `roundUnits` splits `N = c·(D·2^j) + r`; `gap` shows no magnitude `c'·2^i`
(`c' < 2^p`, any `i`) lies strictly between `c·2^j` and `(c+1)·2^j`, which gives
`rne_nearest` and `rne_tie_even` (`EvenSig`: the significand at its own spacing is even).
`decode_encode` shows the encoder `finite` round-trips representable magnitudes;
`value_decode` shows every finite pattern's value is a representable number of units;
`noFarther_iff_units` converts `NoFarther` on fractions into distances in units.
`rne_overflow_iff` derives the overflow threshold from nearest + ties-to-even (the threshold
is the midpoint between `maxUnits`, whose significand `2^p − 1` is odd, and `2^(p+J)`).
The not-NaN and sign theorems follow from the encoders' bit fields (`finite_fields`,
`fields_msb`). Uniqueness goes through `canonQuot`; its section header has the outline.

Checking: this section is part of the reference proof of the task `fdivp` (formerly the module
`spec.IEEE754Proofs`), checked by `check.py` like any submission. Core Lean only; axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace SvGolf.IEEE754

open LeanModels.Sv.Lib (log2_mul_two_pow)

/-- `|u·D − N|` in `Nat` (one of the two truncated differences is 0). -/
def udist (N D u : Nat) : Nat := (N - u * D) + (u * D - N)

/-- `u` units is a magnitude representable with `p` significand bits and an unbounded
exponent range: `u = c × 2^j` with `c < 2^p`. -/
def RepU (f : Format) (u : Nat) : Prop := ∃ c j, c < 2 ^ f.p ∧ u = c * 2 ^ j

theorem two_pow_pred (f : Format) : 2 ^ f.p = 2 ^ (f.p - 1) * 2 := by
  have := f.hp
  rw [← Nat.pow_succ]; congr 1; omega

/-- The truncated significand `c = ⌊N / (D·2^j)⌋` has at most `p` bits, and exactly `p` bits
when `j > 0`. -/
theorem trunc_bounds (f : Format) (N D : Nat) :
    N / (D * 2 ^ ulpExp f (N / D)) < 2 ^ f.p ∧
    (0 < ulpExp f (N / D) → 2 ^ (f.p - 1) ≤ N / (D * 2 ^ ulpExp f (N / D))) := by
  have hp := f.hp
  rw [← Nat.div_div_eq_div_mul]
  generalize N / D = n
  unfold ulpExp
  constructor
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by omega) (by omega))
  · intro hj
    have hn : n ≠ 0 := by
      rintro rfl
      simp [Nat.log2_zero] at hj
      omega
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le hn)

/-- No representable magnitude lies strictly between `c·2^j` and `(c+1)·2^j`, when `c` has
`p` bits or `j = 0`. -/
theorem gap (f : Format) (c j w : Nat) (hc : 0 < j → 2 ^ (f.p - 1) ≤ c) (hw : RepU f w) :
    w ≤ c * 2 ^ j ∨ (c + 1) * 2 ^ j ≤ w := by
  obtain ⟨c', i, hc', rfl⟩ := hw
  by_cases hij : j ≤ i
  · have e : c' * 2 ^ i = c' * 2 ^ (i - j) * 2 ^ j := by
      rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
    rw [e]
    by_cases h : c' * 2 ^ (i - j) ≤ c
    · exact .inl (Nat.mul_le_mul_right _ h)
    · exact .inr (Nat.mul_le_mul_right _ (by omega))
  · left
    have hj : 0 < j := by omega
    have h1 := hc hj
    have h2 : 2 ^ i * 2 ≤ 2 ^ j := by
      rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    calc c' * 2 ^ i ≤ 2 ^ f.p * 2 ^ i := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (f.p - 1) * (2 ^ i * 2) := by rw [two_pow_pred]; ac_rfl
      _ ≤ c * 2 ^ j := Nat.mul_le_mul h1 h2

/-- `v`'s significand at its own spacing (`v / 2^ulpExp v`, the integral significand `c` of
§3.3, or the subnormal `T`) is even. -/
def EvenSig (f : Format) (v : Nat) : Prop := v / 2 ^ ulpExp f v % 2 = 0

theorem evenSig_of (f : Format) (e j : Nat) (he : e % 2 = 0) (hle : e ≤ 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ e) : EvenSig f (e * 2 ^ j) := by
  have hp := f.hp
  unfold EvenSig ulpExp
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · simp
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · rw [log2_mul_two_pow j (by omega)]
    have hl : e.log2 < f.p := (Nat.log2_lt (by omega)).2 hlt
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have : e.log2 + 0 + 1 - f.p = 0 := by omega
      simp [this, he]
    · have hl2 : f.p - 1 ≤ e.log2 := (Nat.le_log2 (by omega)).2 (hn hj)
      have : e.log2 + j + 1 - f.p = j := by omega
      rw [this, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]; exact he
  · rw [← Nat.pow_add, Nat.log2_two_pow]
    have : f.p + j + 1 - f.p = j + 1 := by omega
    rw [this, Nat.pow_div (by omega) (by omega)]
    have : f.p + j - (j + 1) = (f.p - 2) + 1 := by omega
    rw [this, Nat.pow_succ]; simp

/-- The pieces of `roundUnits`: `N = M·c + r` with `M = D·2^j`, `r < M`. -/
theorem rne_unfold (f : Format) (neg : Bool) (N D : Nat) :
    roundUnits f .roundTiesToEven neg N D =
      (if 2 * (N % (D * 2 ^ ulpExp f (N / D))) > D * 2 ^ ulpExp f (N / D) ∨
          (2 * (N % (D * 2 ^ ulpExp f (N / D))) = D * 2 ^ ulpExp f (N / D) ∧
           N / (D * 2 ^ ulpExp f (N / D)) % 2 = 1)
        then N / (D * 2 ^ ulpExp f (N / D)) + 1 else N / (D * 2 ^ ulpExp f (N / D)))
        * 2 ^ ulpExp f (N / D) := by
  simp only [roundUnits]
  congr 1
  split <;> split <;> simp_all

/-- **roundTiesToEven delivers a nearest representable magnitude** (§4.3.1): no magnitude
`w = c·2^j` with `c < 2^p` is strictly closer to `N / D` (all exponents allowed). -/
theorem rne_nearest (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) :
    udist N D (roundUnits f .roundTiesToEven neg N D) ≤ udist N D w := by
  obtain ⟨-, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold]
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  have hg' : w * D ≤ D * 2 ^ j * c ∨ D * 2 ^ j * c + D * 2 ^ j ≤ w * D := by
    rcases hg with h | h
    · exact .inl (e1 ▸ Nat.mul_le_mul_right D h)
    · exact .inr (e2 ▸ Nat.mul_le_mul_right D h)
  unfold udist
  generalize D * 2 ^ j * c = X at *
  generalize D * 2 ^ j = M at *
  split <;> omega

/-- **Ties go to even** (§4.3.1): if a different representable magnitude is as close to
`N / D` as the roundTiesToEven result, the result's significand is even. -/
theorem rne_tie_even (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) (hne : w ≠ roundUnits f .roundTiesToEven neg N D)
    (hle : udist N D w ≤ udist N D (roundUnits f .roundTiesToEven neg N D)) :
    EvenSig f (roundUnits f .roundTiesToEven neg N D) := by
  obtain ⟨hc1, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at *
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  -- w is one of the two neighbours c·2^j, (c+1)·2^j
  have hw2 : w = c * 2 ^ j ∨ w = (c + 1) * 2 ^ j := by
    rcases hg with h | h
    · rcases Nat.lt_or_eq_of_le h with h | h
      · exfalso
        have := e1 ▸ Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul] at this
        unfold udist at hle
        generalize D * 2 ^ j * c = X at *
        generalize D * 2 ^ j = M at *
        split at hle <;> omega
      · exact .inl h
    · rcases Nat.lt_or_eq_of_le h with h | h
      · exfalso
        have := Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
        rw [Nat.succ_mul, e2] at this
        unfold udist at hle
        generalize D * 2 ^ j * c = X at *
        generalize D * 2 ^ j = M at *
        split at hle <;> omega
      · exact .inr h.symm
  have hcp : c + 1 ≤ 2 ^ f.p := hc1
  split
  · next hup =>
    rcases hw2 with rfl | rfl
    · apply evenSig_of f (c + 1) j _ hcp (fun hj => Nat.le_succ_of_le (hc2 hj))
      have := hle
      rw [if_pos hup] at this
      unfold udist at this
      rw [e1, e2] at this
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      omega
    · exact absurd rfl (by rwa [if_pos hup] at hne)
  · next hup =>
    rcases hw2 with rfl | rfl
    · exact absurd rfl (by rwa [if_neg hup] at hne)
    · apply evenSig_of f c j _ (by omega) hc2
      have := hle
      rw [if_neg hup] at this
      unfold udist at this
      rw [e1, e2] at this
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      omega

/-! ## Bit fields -/

theorem fields_toNat (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) :
    (fields f neg E T).toNat = (if neg then 1 else 0) * 2 ^ (f.w + f.t) + (E * 2 ^ f.t + T) := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  unfold fields
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc]
  have : 2 ^ f.k = 2 * 2 ^ (f.w + f.t) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.k]; omega
  rw [this]; cases neg <;> simp <;> omega

theorem decode_fields (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) :
    decode f (fields f neg E T) =
      if E = 2 ^ f.w - 1 then (if T = 0 then .inf neg else .nan (T < 2 ^ (f.t - 1)))
      else if E = 0 then (if T = 0 then .zero neg else .finite neg (f.emin - f.t) T)
      else .finite neg ((E : Int) - f.emax - f.t) (2 ^ f.t + T) := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  have ht := Nat.two_pow_pos f.t
  have h1 : (fields f neg E T).toNat / 2 ^ (f.w + f.t) = if neg then 1 else 0 := by
    rw [fields_toNat f neg E T hE hT, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlow, Nat.zero_add]
  have h2 : (fields f neg E T).toNat / 2 ^ f.t % 2 ^ f.w = E := by
    rw [fields_toNat f neg E T hE hT, Nat.pow_add, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ ht, Nat.add_comm (E * _), Nat.add_mul_div_right _ _ ht,
      Nat.div_eq_of_lt hT, Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hE]
  have h3 : (fields f neg E T).toNat % 2 ^ f.t = T := by
    rw [fields_toNat f neg E T hE hT, Nat.pow_add, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_mod_self_right, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]
  unfold decode
  simp only [h1, h2, h3]
  have : ((if neg = true then 1 else 0) == 1) = neg := by cases neg <;> rfl
  rw [this]

/-! ## Exact values in units -/

theorem emax_pos (f : Format) : 1 ≤ f.emax := by
  have := f.hw
  unfold Format.emax
  have : 2 ≤ 2 ^ (f.w - 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (f.w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem scale_eq (f : Format) : (f.scale : Int) = -f.qmin := by
  have := emax_pos f
  unfold Format.scale Format.qmin Format.emin
  omega

/-- `v` is the exact value `(−1)^neg × u × 2^qmin = ±u / 2^scale` as a fraction. -/
def IsUnits (f : Format) (v : Int × Nat) (neg : Bool) (u : Nat) : Prop :=
  0 < v.2 ∧ v.1 * 2 ^ f.scale = (if neg then -(u : Int) else u) * v.2

/-- `n` with sign `neg`: `(−1)^neg × n`. -/
def sgn (neg : Bool) (n : Nat) : Int := if neg then -(n : Int) else n

theorem value_finite (f : Format) (neg : Bool) (q : Int) (c : Nat) (hq : f.qmin ≤ q) :
    ∃ v, (Datum.finite neg q c).value? = some v ∧
      IsUnits f v neg (c * 2 ^ (q - f.qmin).toNat) := by
  refine ⟨_, rfl, Nat.two_pow_pos _, ?_⟩
  have hS := scale_eq f
  have e : q.toNat + f.scale = (q - f.qmin).toNat + (-q).toNat := by omega
  have e2 : (2 : Int) ^ q.toNat * 2 ^ f.scale = 2 ^ (q - f.qmin).toNat * 2 ^ (-q).toNat := by
    rw [← Int.pow_add, ← Int.pow_add, e]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natCast_mul, Int.natCast_pow,
    Int.cast_ofNat_Int, Int.neg_mul, Int.mul_assoc, e2]

theorem value_zero (f : Format) (neg : Bool) :
    ∃ v, (Datum.zero neg).value? = some v ∧ IsUnits f v neg 0 :=
  ⟨_, rfl, by decide, by simp⟩

/-- Every finite datum decoded from a bit pattern has `0 < c < 2^p` and `qmin ≤ q`. -/
theorem decode_finite_bounds (f : Format) (z : BitVec f.k) (neg : Bool) (q : Int) (c : Nat)
    (h : decode f z = .finite neg q c) : c < 2 ^ f.p ∧ f.qmin ≤ q := by
  have hp := f.hp
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hT := Nat.mod_lt z.toNat (Nat.two_pow_pos f.t)
  unfold decode at h
  simp only at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨by omega, Int.le_refl _⟩
    · cases h
      refine ⟨by omega, ?_⟩
      unfold Format.qmin Format.emin; omega

/-- Every zero or finite pattern's value is `±u` units for a representable `u`. -/
theorem value_decode (f : Format) (z : BitVec f.k) (v : Int × Nat)
    (h : (decode f z).value? = some v) : ∃ neg u, RepU f u ∧ IsUnits f v neg u := by
  cases hd : decode f z with
  | nan _ => rw [hd] at h; cases h
  | inf _ => rw [hd] at h; cases h
  | zero neg =>
    rw [hd] at h; cases h
    exact ⟨neg, 0, ⟨0, 0, Nat.two_pow_pos _, rfl⟩, by decide, by simp⟩
  | finite neg q c =>
    obtain ⟨hc, hq⟩ := decode_finite_bounds f z neg q c hd
    obtain ⟨v', hv', hu⟩ := value_finite f neg q c hq
    rw [hd, hv'] at h; cases h
    exact ⟨neg, _, ⟨c, _, hc, rfl⟩, hu⟩

/-! ## The encoder `finite` round-trips representable magnitudes -/

theorem two_emax (f : Format) : 2 * f.emax + 2 = 2 ^ f.w := by
  have := f.hw
  have h2 : 2 * 2 ^ (f.w - 1) = 2 ^ f.w := by
    rw [← Nat.pow_succ']; congr 1; omega
  have := emax_pos f
  unfold Format.emax at *; omega

theorem rep_dvd (f : Format) (u : Nat) (hu : RepU f u) (hu0 : u ≠ 0) :
    2 ^ (Nat.log2 u - f.t) ∣ u := by
  obtain ⟨c, i, hc, rfl⟩ := hu
  have hc0 : c ≠ 0 := by rintro rfl; simp at hu0
  rw [log2_mul_two_pow i hc0]
  have : c.log2 < f.p := (Nat.log2_lt hc0).2 hc
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by simp only [Format.t]; omega))
    (Nat.dvd_mul_left _ _)

/-- For `2^t ≤ u ≤ maxUnits`, with `j = ⌊log₂ u⌋ − t`: the significand `u / 2^j` has exactly
`p` bits and the biased exponent `j + 1` is that of a finite number. -/
theorem normal_bounds (f : Format) (u : Nat) (hmax : u ≤ f.maxUnits) (hge : 2 ^ f.t ≤ u) :
    2 ^ f.t ≤ u / 2 ^ (u.log2 - f.t) ∧ u / 2 ^ (u.log2 - f.t) - 2 ^ f.t < 2 ^ f.t ∧
    u.log2 - f.t + 1 < 2 ^ f.w - 1 := by
  have hp := f.hp
  have hw2 := two_emax f
  have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
  have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 hge
  have hlo : 2 ^ f.t ≤ u / 2 ^ (u.log2 - f.t) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le hu0)
  have hhi : u / 2 ^ (u.log2 - f.t) < 2 ^ f.p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le Nat.lt_log2_self
      (Nat.pow_le_pow_right (by omega) (by simp only [Format.t] at *; omega))
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  refine ⟨hlo, by omega, ?_⟩
  have hm : f.maxUnits < 2 ^ (f.p + (2 * f.emax - 1)) := by
    unfold Format.maxUnits
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (by have := Nat.two_pow_pos f.p; omega)
      (Nat.two_pow_pos _)
  have := (Nat.log2_lt hu0).2 (Nat.lt_of_le_of_lt hmax hm)
  have := emax_pos f
  simp only [Format.t]; omega

theorem decode_encode (f : Format) (neg : Bool) (u : Nat) (hu : RepU f u)
    (hmax : u ≤ f.maxUnits) :
    ∃ v, (decode f (finite f neg u)).value? = some v ∧ IsUnits f v neg u := by
  have hp := f.hp
  have hw2 := two_emax f
  have h4 : 4 ≤ 2 ^ f.w := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f.w := Nat.pow_le_pow_right (by omega) f.hw
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt, decode_fields f neg 0 u (Nat.two_pow_pos _) hlt,
      if_neg (by omega), if_pos rfl]
    by_cases h0 : u = 0
    · subst h0; exact ⟨_, rfl, by decide, by simp⟩
    · rw [if_neg h0]
      obtain ⟨v, hv, hU⟩ := value_finite f neg (f.emin - f.t) u (Int.le_refl _)
      refine ⟨v, hv, ?_⟩
      have : (f.emin - f.t - f.qmin).toNat = 0 := by unfold Format.qmin; omega
      rwa [this, Nat.pow_zero, Nat.mul_one] at hU
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize hj : Nat.log2 u - f.t = j at hlo hT hj2
    rw [decode_fields f neg (j + 1) (u / 2 ^ j - 2 ^ f.t) (by omega) hT,
      if_neg (by omega), if_neg (by omega)]
    have hq : f.qmin ≤ ((j + 1 : Nat) : Int) - f.emax - f.t := by
      unfold Format.qmin Format.emin; omega
    obtain ⟨v, hv, hU⟩ := value_finite f neg _ (2 ^ f.t + (u / 2 ^ j - 2 ^ f.t)) hq
    refine ⟨v, hv, ?_⟩
    have e1 : (((j + 1 : Nat) : Int) - f.emax - f.t - f.qmin).toNat = j := by
      unfold Format.qmin Format.emin; omega
    have e2 : (2 ^ f.t + (u / 2 ^ j - 2 ^ f.t)) * 2 ^ j = u := by
      rw [Nat.add_sub_cancel' hlo, Nat.div_mul_cancel (hj ▸ rep_dvd f u hu hu0)]
    rwa [e1, e2] at hU

/-! ## Fractions and units -/

theorem isUnits_sgn (f : Format) (v : Int × Nat) (neg : Bool) (u : Nat) :
    IsUnits f v neg u ↔ 0 < v.2 ∧ v.1 * 2 ^ f.scale = sgn neg u * v.2 := Iff.rfl

theorem sgn_mul (s : Bool) (a b : Nat) : sgn s a * (b : Int) = sgn s (a * b) := by
  cases s <;> simp [sgn, Int.neg_mul]

theorem natAbs_sgn_same (s : Bool) (a b : Nat) :
    (sgn s a - sgn s b).natAbs = (b - a) + (a - b) := by
  cases s <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem natAbs_sgn_opp (s : Bool) (a b : Nat) :
    (sgn (!s) a - sgn s b).natAbs = a + b := by
  cases s <;> simp only [sgn, Bool.false_eq_true, Bool.not_true, Bool.not_false, ↓reduceIte] <;>
    omega

theorem value_finite_eq (neg : Bool) (q : Int) (c : Nat) :
    (Datum.finite neg q c).value? = some (sgn neg (c * 2 ^ q.toNat), 2 ^ (-q).toNat) := by
  cases neg <;> simp [Datum.value?, sgn]

theorem fracDiv_sgn (sa sb : Bool) (nx dx ny dy : Nat) (hny : ny ≠ 0) :
    fracDiv (sgn sa nx, dx) (sgn sb ny, dy) = (sgn (sa ^^ sb) (nx * dy), dx * ny) := by
  have h1 : ¬ ((ny : Int) < 0) := by omega
  have h2 : -(ny : Int) < 0 := by omega
  cases sa <;> cases sb <;>
    simp only [fracDiv, sgn, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.xor_true,
      Bool.not_true, Bool.not_false, h1, h2, Int.neg_mul, Int.neg_neg, Int.natAbs_neg,
      Int.natAbs_natCast, Int.natCast_mul]

/-- Two fractions with the same signed units are equal fractions. -/
theorem eqv_of_units (f : Format) (v r : Int × Nat) (sv sr : Bool) (uv ur : Nat)
    (hv : IsUnits f v sv uv) (hr : IsUnits f r sr ur) (h : sgn sv uv = sgn sr ur) :
    v.1 * r.2 = r.1 * v.2 := by
  rw [isUnits_sgn] at hv hr
  have hP : (2 : Int) ^ f.scale ≠ 0 := Int.ne_of_gt (Int.pow_pos (by decide))
  apply Int.eq_of_mul_eq_mul_right hP
  calc v.1 * r.2 * 2 ^ f.scale = v.1 * 2 ^ f.scale * r.2 := by ac_rfl
    _ = r.1 * 2 ^ f.scale * v.2 := by rw [hv.2, hr.2, h]; ac_rfl
    _ = r.1 * v.2 * 2 ^ f.scale := by ac_rfl

/-- Comparing distances to `±Nq / Dq` of two fractions given in units: `NoFarther` is the
comparison of `|±u·Dq − ±Nq·2^scale|`. -/
theorem noFarther_iff_units (f : Format) (r v : Int × Nat) (σr σv σ : Bool) (u u' Nq Dq : Nat)
    (hr : IsUnits f r σr u) (hv : IsUnits f v σv u') :
    NoFarther r v (sgn σ Nq, Dq) ↔
      (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs ≤
      (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale).natAbs := by
  rw [isUnits_sgn] at hr hv
  obtain ⟨hr2, hr⟩ := hr
  obtain ⟨hv2, hv⟩ := hv
  unfold NoFarther
  simp only
  have kA : (r.1 * Dq - sgn σ Nq * r.2) * 2 ^ f.scale =
      r.2 * (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale) := by grind
  have kB : (v.1 * Dq - sgn σ Nq * v.2) * 2 ^ f.scale =
      v.2 * (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale) := by grind
  have nA := congrArg Int.natAbs kA
  have nB := congrArg Int.natAbs kB
  simp only [Int.natAbs_mul, Int.natAbs_pow, show Int.natAbs 2 = 2 from rfl, Int.natAbs_natCast] at nA nB
  generalize (r.1 * Dq - sgn σ Nq * r.2).natAbs = A at *
  generalize (v.1 * Dq - sgn σ Nq * v.2).natAbs = B at *
  generalize (sgn σr u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = α at *
  generalize (sgn σv u' * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = β at *
  have hP := Nat.two_pow_pos f.scale
  constructor
  · intro h
    have : r.2 * v.2 * α ≤ r.2 * v.2 * β := by
      have := Nat.mul_le_mul_right (2 ^ f.scale) h
      calc r.2 * v.2 * α = v.2 * (r.2 * α) := by ac_rfl
        _ = A * v.2 * 2 ^ f.scale := by rw [← nA]; ac_rfl
        _ ≤ B * r.2 * 2 ^ f.scale := this
        _ = r.2 * (v.2 * β) := by rw [← nB]; ac_rfl
        _ = r.2 * v.2 * β := by ac_rfl
    exact Nat.le_of_mul_le_mul_left this (Nat.mul_pos hr2 hv2)
  · intro h
    apply Nat.le_of_mul_le_mul_right _ hP
    calc A * v.2 * 2 ^ f.scale = v.2 * (r.2 * α) := by rw [Nat.mul_right_comm, nA]; ac_rfl
      _ ≤ v.2 * (r.2 * β) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
      _ = B * r.2 * 2 ^ f.scale := by rw [Nat.mul_right_comm, nB]; ac_rfl

/-! ## Assembling the bit-level theorem -/

theorem rne_rep (f : Format) (neg : Bool) (N D : Nat) :
    RepU f (roundUnits f .roundTiesToEven neg N D) := by
  obtain ⟨hc1, -⟩ := trunc_bounds f N D
  rw [rne_unfold]
  generalize ulpExp f (N / D) = j at *
  generalize N / (D * 2 ^ j) = c at *
  split
  · by_cases h : c + 1 < 2 ^ f.p
    · exact ⟨c + 1, j, h, rfl⟩
    · refine ⟨2 ^ (f.p - 1), j + 1, ?_, ?_⟩
      · have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega
      · have : c + 1 = 2 ^ f.p := by omega
        rw [this, two_pow_pred, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
  · exact ⟨c, j, hc1, rfl⟩

theorem decode_infinity (f : Format) (neg : Bool) : decode f (infinity f neg) = .inf neg := by
  unfold infinity
  have := Nat.two_pow_pos f.w
  rw [decode_fields f neg (2 ^ f.w - 1) 0 (by omega) (Nat.two_pow_pos _), if_pos rfl, if_pos rfl]

theorem zero_rep (f : Format) : RepU f 0 := ⟨0, 0, Nat.two_pow_pos _, rfl⟩

/-- An encoded magnitude with even significand has least significant bit 0. -/
theorem finite_lsb (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) (he : EvenSig f u) : (finite f neg u).toNat % 2 = 0 := by
  have hp := f.hp
  have hw2 := two_emax f
  have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hwt : 2 ^ (f.w + f.t) = 2 * 2 ^ (f.w + f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have parity : ∀ E T, E < 2 ^ f.w → T < 2 ^ f.t → T % 2 = 0 →
      (fields f neg E T).toNat % 2 = 0 := by
    intro E T hE hT h
    rw [fields_toNat f neg E T hE hT, hwt, ht2]
    have : E * (2 * 2 ^ (f.t - 1)) = 2 * (E * 2 ^ (f.t - 1)) := by ac_rfl
    rw [this]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  unfold EvenSig ulpExp at he
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt]
    apply parity 0 u (Nat.two_pow_pos _) hlt
    by_cases h0 : u = 0
    · simp [h0]
    · have : u.log2 < f.t := (Nat.log2_lt h0).2 hlt
      have : u.log2 + 1 - f.p = 0 := by simp only [Format.t] at this; omega
      rwa [this, Nat.pow_zero, Nat.div_one] at he
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 (by omega)
    have hj : u.log2 + 1 - f.p = u.log2 - f.t := by simp only [Format.t]; omega
    rw [hj] at he
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize u.log2 - f.t = j at *
    exact parity (j + 1) _ (by omega) hT (by omega)

theorem natAbs_units_same (f : Format) (σ : Bool) (u Nq Dq : Nat) :
    (sgn σ u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = udist (Nq * 2 ^ f.scale) Dq u := by
  have : (2 : Int) ^ f.scale = ((2 ^ f.scale : Nat) : Int) := by simp
  rw [this, sgn_mul, sgn_mul, natAbs_sgn_same]; rfl

theorem natAbs_units_opp (f : Format) (σ : Bool) (u Nq Dq : Nat) :
    (sgn (!σ) u * Dq - sgn σ Nq * 2 ^ f.scale).natAbs = u * Dq + Nq * 2 ^ f.scale := by
  have : (2 : Int) ^ f.scale = ((2 ^ f.scale : Nat) : Int) := by simp
  rw [this, sgn_mul, sgn_mul, natAbs_sgn_opp]

/-- The shared core of both cases: a result `finite f σ u` whose units `u` are nearest to
`Nq·2^scale / Dq` (ties to even) satisfies both clauses of `DivideIsNearestTiesToEven`. -/
theorem nearest_core (f : Format) (σ : Bool) (Nq Dq u : Nat) (hD : 0 < Dq) (hu : RepU f u)
    (hmax : u ≤ f.maxUnits)
    (hnear : ∀ w, RepU f w → udist (Nq * 2 ^ f.scale) Dq u ≤ udist (Nq * 2 ^ f.scale) Dq w)
    (htie : ∀ w, RepU f w → w ≠ u →
      udist (Nq * 2 ^ f.scale) Dq w ≤ udist (Nq * 2 ^ f.scale) Dq u → EvenSig f u)
    (r : Int × Nat) (hr : (decode f (finite f σ u)).value? = some r) :
    (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        NoFarther r v (sgn σ Nq, Dq)) ∧
    (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (sgn σ Nq, Dq) →
        (finite f σ u).toNat % 2 = 0) := by
  obtain ⟨r', hr', hrU⟩ := decode_encode f σ u hu hmax
  rw [hr'] at hr; cases hr
  have h0 := hnear 0 (zero_rep f)
  have hd0 : udist (Nq * 2 ^ f.scale) Dq 0 = Nq * 2 ^ f.scale := by simp [udist]
  constructor
  · intro z v hv
    obtain ⟨σv, u', hu', hvU⟩ := value_decode f z v hv
    apply (noFarther_iff_units f r v σ σv σ u u' Nq Dq hrU hvU).mpr
    rw [natAbs_units_same]
    cases hσ : σv == σ
    · have : σv = !σ := by cases σv <;> cases σ <;> simp_all
      subst this
      rw [natAbs_units_opp]; omega
    · have : σv = σ := by simpa using hσ
      subst this
      rw [natAbs_units_same]; exact hnear u' hu'
  · intro z v hv hne hle
    obtain ⟨σv, u', hu', hvU⟩ := value_decode f z v hv
    have hle := (noFarther_iff_units f v r σv σ σ u' u Nq Dq hvU hrU).mp hle
    rw [natAbs_units_same] at hle
    apply finite_lsb f σ u hmax
    cases hσ : σv == σ
    · have : σv = !σ := by cases σv <;> cases σ <;> simp_all
      subst this
      rw [natAbs_units_opp] at hle
      have hu'0 : u' = 0 := by
        rcases Nat.eq_zero_or_pos u' with h | h
        · exact h
        · have := Nat.mul_pos h hD; omega
      subst hu'0
      by_cases hu0 : u = 0
      · subst hu0
        exact absurd (eqv_of_units f v r _ σ 0 0 hvU hrU (by cases σ <;> rfl)) hne
      · exact htie 0 (zero_rep f) (Ne.symm hu0) (by omega)
    · have : σv = σ := by simpa using hσ
      subst this
      rw [natAbs_units_same] at hle
      by_cases heq : u' = u
      · subst heq; exact absurd (eqv_of_units f v r σv σv u' u' hvU hrU rfl) hne
      · exact htie u' hu' heq hle

/-- The named signed zero is the encoder `finite` at 0 units. -/
theorem zero_eq_finite (f : Format) (neg : Bool) : zero f neg = finite f neg 0 := by
  unfold zero finite
  rw [if_pos (Nat.two_pow_pos _)]

theorem divide_zero_finite (f : Format) (m : RoundingMode) (a b : BitVec f.k) (sa sb : Bool)
    (qb : Int) (cb : Nat) (ha : decode f a = .zero sa) (hb : decode f b = .finite sb qb cb) :
    divide f m a b = finite f (sa ^^ sb) 0 := by
  simp only [divide, ha, hb, zero_eq_finite]

theorem divide_finite_finite (f : Format) (m : RoundingMode) (a b : BitVec f.k) (sa sb : Bool)
    (qa qb : Int) (ca cb : Nat) (ha : decode f a = .finite sa qa ca)
    (hb : decode f b = .finite sb qb cb) :
    divide f m a b = round f m (sa ^^ sb) (ca * 2 ^ qa.toNat * 2 ^ (-qb).toNat)
      (2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat)) := by
  simp only [divide, ha, hb]

/-- **Main theorem**: `divide` under roundTiesToEven returns the nearest finite number, ties to
even, for every format (the statement is `DivideIsNearestTiesToEven` in `IEEE754.lean`). -/
theorem divide_isNearestTiesToEven (f : Format) : DivideIsNearestTiesToEven f := by
  intro a b x y r hx hy hy0 hr
  -- the divisor is finite and nonzero
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  rw [hb, value_finite_eq] at hy
  cases hy
  have hny : cb * 2 ^ qb.toNat ≠ 0 := by
    intro h; apply hy0; simp only [h, sgn]; cases sb <;> rfl
  have hdq : 0 < 2 ^ (-qb).toNat := Nat.two_pow_pos _
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [ha] at hx; cases hx
    have hx0 : ((0 : Int), (1 : Nat)) = (sgn sa 0, 1) := by cases sa <;> rfl
    rw [hx0, fracDiv_sgn sa sb 0 1 _ _ hny]
    rw [divide_zero_finite f _ a b sa sb qb cb ha hb] at hr ⊢
    refine nearest_core f _ _ _ 0 (by omega) (zero_rep f) (Nat.zero_le _) ?_ ?_ r hr
    · intro w _; simp [udist]
    · intro w _ hw0 hle
      unfold udist at hle
      have := Nat.mul_pos (Nat.pos_of_ne_zero hw0)
        (show 0 < 1 * (cb * 2 ^ qb.toNat) by omega)
      omega
  | finite sa qa ca =>
    rw [ha, value_finite_eq] at hx; cases hx
    rw [fracDiv_sgn sa sb _ _ _ _ hny]
    rw [divide_finite_finite f _ a b sa sb qa qb ca cb ha hb] at hr ⊢
    have hD : 0 < 2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat) :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.pos_of_ne_zero hny)
    unfold round at hr ⊢
    simp only at hr ⊢
    split
    · next hmax =>
      rw [if_pos hmax] at hr
      exact nearest_core f _ _ _ _ hD (rne_rep f _ _ _) hmax
        (rne_nearest f _ _ _ hD) (fun w hw hne hle => rne_tie_even f _ _ _ hD w hw hne hle) r hr
    · next hmax =>
      rw [if_neg hmax] at hr
      simp [overflowToInfinity, decode_infinity, Datum.value?] at hr

/-! ## Overflow happens exactly at the §4.3.1 threshold -/

theorem maxUnits_eq (f : Format) :
    f.maxUnits = (2 ^ f.p - 1) * 2 ^ (2 * f.emax - 1) := rfl

theorem maxUnits_rep (f : Format) : RepU f f.maxUnits :=
  ⟨2 ^ f.p - 1, _, by have := Nat.two_pow_pos f.p; omega, rfl⟩

/-- The next representable magnitude above `maxUnits` (unbounded exponent) is `2^(p+J)`. -/
theorem rep_above_max (f : Format) (w : Nat) (hw : RepU f w) (h : f.maxUnits < w) :
    2 ^ (f.p + (2 * f.emax - 1)) ≤ w := by
  obtain ⟨c, i, hc, rfl⟩ := hw
  rw [maxUnits_eq] at h
  generalize 2 * f.emax - 1 = J at *
  have hp := f.hp
  by_cases hi : i ≤ J
  · exfalso
    have : c * 2 ^ i ≤ (2 ^ f.p - 1) * 2 ^ J :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hi)
    omega
  · have e : c * 2 ^ i = c * 2 ^ (i - (J + 1)) * 2 ^ J * 2 := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_add]; congr 2; omega
    rw [e] at h ⊢
    generalize c * 2 ^ (i - (J + 1)) = m at *
    have h2 : (2 ^ f.p - 1) * 2 ^ J < m * 2 * 2 ^ J := by
      rw [Nat.mul_right_comm]; exact h
    have h3 := Nat.lt_of_mul_lt_mul_right h2
    have hp2 := two_pow_pred f
    have hm : 2 ^ (f.p - 1) ≤ m := by omega
    calc 2 ^ (f.p + J) = 2 ^ (f.p - 1) * 2 ^ J * 2 := by
          rw [Nat.mul_right_comm, ← two_pow_pred, ← Nat.pow_add]
      _ ≤ m * 2 ^ J * 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm)

theorem not_evenSig_max (f : Format) : ¬ EvenSig f f.maxUnits := by
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  have hodd : (2 ^ f.p - 1) % 2 = 1 := by omega
  have h0 : 2 ^ f.p - 1 ≠ 0 := by omega
  have hl : (2 ^ f.p - 1).log2 = f.p - 1 := by
    rw [Nat.log2_eq_iff h0, show f.p - 1 + 1 = f.p by omega]
    omega
  unfold EvenSig ulpExp
  rw [maxUnits_eq, log2_mul_two_pow _ h0, hl,
    show f.p - 1 + (2 * f.emax - 1) + 1 - f.p = 2 * f.emax - 1 by omega,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), hodd]
  decide

/-- **Overflow threshold, in units** (§4.3.1, §7.4): the roundTiesToEven result with unbounded
exponent exceeds `maxUnits` iff `N / D ≥ maxUnits + 2^(J−1)`, where `J = 2·emax − 1` and
`2^J` is the spacing of the top binade. -/
theorem rne_overflow_iff (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) :
    f.maxUnits < roundUnits f .roundTiesToEven neg N D ↔
      D * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * N := by
  have hp := f.hp
  have he := emax_pos f
  have hvrep := rne_rep f neg N D
  have hnear := rne_nearest f neg N D hD
  have htie := rne_tie_even f neg N D hD
  generalize roundUnits f .roundTiesToEven neg N D = v at *
  have hmaxeq := maxUnits_eq f
  have habove := rep_above_max f
  have hJ1 : 1 ≤ 2 * f.emax - 1 := by omega
  generalize 2 * f.emax - 1 = J at *
  have hwrep : RepU f (2 ^ (f.p + J)) :=
    ⟨2 ^ (f.p - 1), J + 1, by have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega,
      by rw [← Nat.pow_add]; congr 1; omega⟩
  -- 2^(p+J) = maxUnits + 2^J and 2^J = 2·2^(J−1)
  have hmax : f.maxUnits + 2 ^ J = 2 ^ (f.p + J) := by
    rw [hmaxeq, Nat.pow_add, Nat.sub_mul, Nat.one_mul]
    have := Nat.le_mul_of_pos_left (2 ^ J) (Nat.two_pow_pos f.p); omega
  have hJh : 2 ^ J = 2 * 2 ^ (J - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have e1 : 2 ^ (f.p + J) * D = f.maxUnits * D + 2 * (2 ^ (J - 1) * D) := by
    rw [← hmax, Nat.add_mul, hJh, Nat.mul_assoc]
  have e2 : D * (2 * f.maxUnits + 2 ^ J) = 2 * (f.maxUnits * D) + 2 * (2 ^ (J - 1) * D) := by
    rw [hJh]; simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  rw [e2]
  have hmD := hnear _ (maxUnits_rep f)
  have hwD := hnear _ hwrep
  unfold udist at hmD hwD
  rw [e1] at hwD
  constructor
  · intro hgt
    have hvD := Nat.mul_le_mul_right D (habove v hvrep hgt)
    rw [e1] at hvD
    have hlt : f.maxUnits * D < v * D := Nat.mul_lt_mul_of_pos_right hgt hD
    generalize f.maxUnits * D = B at *
    generalize v * D = V at *
    generalize 2 ^ (J - 1) * D = A at *
    omega
  · intro hge
    apply Classical.byContradiction
    intro hle
    have hle : v ≤ f.maxUnits := by omega
    have hvD := Nat.mul_le_mul_right D hle
    by_cases hvm : v = f.maxUnits
    · -- v = maxUnits: then N/D is exactly the midpoint (else 2^(p+J) would be closer), a tie
      -- that ties-to-even must break towards the even 2^(p+J), not the odd maxUnits
      subst hvm
      apply not_evenSig_max f
      have h2J := Nat.two_pow_pos J
      apply htie (2 ^ (f.p + J)) hwrep (by rw [← hmax]; omega)
      unfold udist
      rw [e1]
      generalize f.maxUnits * D = B at *
      generalize 2 ^ (J - 1) * D = A at *
      omega
    · have hlt : v * D < f.maxUnits * D := Nat.mul_lt_mul_of_pos_right (by omega) hD
      generalize f.maxUnits * D = B at *
      generalize v * D = V at *
      generalize 2 ^ (J - 1) * D = A at *
      omega

theorem natAbs_sgn (s : Bool) (n : Nat) : (sgn s n).natAbs = n := by
  cases s <;> simp [sgn]

/-- The units form of the threshold is the fraction form times `2^(emax−1)`. -/
theorem threshold_units_iff (f : Format) (Nq Dq : Nat) :
    Dq * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * (Nq * 2 ^ f.scale) ↔
      Dq * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ Nq * 2 ^ f.p := by
  have hp := f.hp
  have he := emax_pos f
  have hK := Nat.two_pow_pos (f.emax - 1)
  have hJ : 2 ^ (2 * f.emax - 1) = 2 ^ f.emax * 2 ^ (f.emax - 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have eL : Dq * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) =
      Dq * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) * 2 ^ (f.emax - 1) := by
    rw [maxUnits_eq, hJ, Nat.pow_succ,
      show Dq * 2 ^ f.emax * (2 ^ f.p * 2 - 1) * 2 ^ (f.emax - 1) =
        Dq * ((2 ^ f.p * 2 - 1) * (2 ^ f.emax * 2 ^ (f.emax - 1))) by ac_rfl]
    congr 1
    generalize 2 ^ f.emax * 2 ^ (f.emax - 1) = Y
    have hX := Nat.two_pow_pos f.p
    generalize 2 ^ f.p = X at *
    rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul, Nat.mul_right_comm X 2 Y]
    have := Nat.le_mul_of_pos_left Y hX
    omega
  have eR : 2 * (Nq * 2 ^ f.scale) = Nq * 2 ^ f.p * 2 ^ (f.emax - 1) := by
    rw [Nat.mul_assoc, ← Nat.pow_add, Nat.mul_left_comm, ← Nat.pow_succ']
    congr 2; unfold Format.scale; simp only [Format.t]; omega
  rw [eL, eR]
  exact ⟨fun h => Nat.le_of_mul_le_mul_right h hK, fun h => Nat.mul_le_mul_right _ h⟩

/-- **Second theorem**: overflow happens exactly at the §4.3.1 threshold (the statement is
`DivideOverflowsAtThreshold` in `IEEE754.lean`). -/
theorem divide_overflowsAtThreshold (f : Format) : DivideOverflowsAtThreshold f := by
  intro a b x y hx hy hy0
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  rw [hb, value_finite_eq] at hy
  cases hy
  have hny : cb * 2 ^ qb.toNat ≠ 0 := by
    intro h; apply hy0; simp only [h, sgn]; cases sb <;> rfl
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [ha] at hx; cases hx
    have hx0 : ((0 : Int), (1 : Nat)) = (sgn sa 0, 1) := by cases sa <;> rfl
    rw [hx0, fracDiv_sgn sa sb 0 1 _ _ hny, divide_zero_finite f _ a b sa sb qb cb ha hb]
    obtain ⟨r', hr', -⟩ := decode_encode f (sa ^^ sb) 0 (zero_rep f) (Nat.zero_le _)
    simp only [natAbs_sgn, Nat.zero_mul]
    constructor
    · rintro ⟨s, hs⟩; rw [hs] at hr'; cases hr'
    · intro h
      have h1 : 0 < 1 * (cb * 2 ^ qb.toNat) := by omega
      have h2 : 0 < 2 ^ (f.p + 1) - 1 := by
        have := Nat.one_lt_two_pow (n := f.p + 1) (by omega); omega
      have := Nat.mul_pos (Nat.mul_pos h1 (Nat.two_pow_pos f.emax)) h2
      omega
  | finite sa qa ca =>
    rw [ha, value_finite_eq] at hx; cases hx
    rw [fracDiv_sgn sa sb _ _ _ _ hny, divide_finite_finite f _ a b sa sb qa qb ca cb ha hb]
    have hD : 0 < 2 ^ (-qa).toNat * (cb * 2 ^ qb.toNat) :=
      Nat.mul_pos (Nat.two_pow_pos _) (Nat.pos_of_ne_zero hny)
    simp only [natAbs_sgn]
    rw [← threshold_units_iff, ← rne_overflow_iff f (sa ^^ sb) _ _ hD]
    unfold round
    simp only
    split
    · next hmax =>
      obtain ⟨r', hr', -⟩ := decode_encode f (sa ^^ sb) _ (rne_rep f _ _ _) hmax
      constructor
      · rintro ⟨s, hs⟩; rw [hs] at hr'; cases hr'
      · intro h; omega
    · next hmax =>
      simp only [overflowToInfinity, ↓reduceIte, decode_infinity]
      exact ⟨fun _ => by omega, fun _ => ⟨_, rfl⟩⟩

/-! ## A quotient of numbers is never a NaN, and the sign is the XOR -/

theorem two_pow_k (f : Format) : 2 ^ f.k = 2 * 2 ^ (f.w + f.t) := by
  rw [← Nat.pow_succ']; congr 1; simp only [Format.k]; omega

/-- `BitVec.msb` is `decode`'s sign `S = 1` (`S` is the top bit of the `k = 1 + w + t` bits). -/
theorem msb_eq_S (f : Format) (a : BitVec f.k) :
    a.msb = (a.toNat / 2 ^ (f.w + f.t) == 1) := by
  have hlt : a.toNat < 2 * 2 ^ (f.w + f.t) := two_pow_k f ▸ a.isLt
  have hk : f.k - 1 = f.w + f.t := by simp only [Format.k]; omega
  have hP := Nat.two_pow_pos (f.w + f.t)
  rw [BitVec.msb_eq_decide, hk]
  by_cases h : 2 ^ (f.w + f.t) ≤ a.toNat
  · have : a.toNat / 2 ^ (f.w + f.t) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, this]
  · have : a.toNat / 2 ^ (f.w + f.t) = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, this]

/-- Every non-NaN datum `decode` returns carries the pattern's most significant bit as sign. -/
theorem decode_sign (f : Format) (a : BitVec f.k) :
    (∃ sg, decode f a = .nan sg) ∨ decode f a = .inf a.msb ∨ decode f a = .zero a.msb ∨
      ∃ q c, decode f a = .finite a.msb q c := by
  rw [msb_eq_S]
  unfold decode
  simp only
  split
  · split
    · exact .inr (.inl rfl)
    · exact .inl ⟨_, rfl⟩
  · split
    · split
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr ⟨_, _, rfl⟩))
    · exact .inr (.inr (.inr ⟨_, _, rfl⟩))

theorem fields_msb (f : Format) (neg : Bool) (E T : Nat) (hE : E < 2 ^ f.w)
    (hT : T < 2 ^ f.t) : (fields f neg E T).msb = neg := by
  have hlow : E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  rw [msb_eq_S, fields_toNat f neg E T hE hT, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, Nat.zero_add]
  cases neg <;> rfl

/-- Within the finite range, the encoder `finite` writes a biased exponent below `2^w − 1`. -/
theorem finite_fields (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    ∃ E T, E < 2 ^ f.w - 1 ∧ T < 2 ^ f.t ∧ finite f neg u = fields f neg E T := by
  have hw2 := two_emax f
  unfold finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt]; exact ⟨0, u, by omega, hlt, rfl⟩
  · rw [if_neg hlt]
    obtain ⟨-, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    exact ⟨_, _, hj2, hT, rfl⟩

theorem finite_msb (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    (finite f neg u).msb = neg := by
  obtain ⟨E, T, hE, hT, h⟩ := finite_fields f neg u hmax
  rw [h, fields_msb f neg E T (by omega) hT]

/-- Within the finite range, the encoder `finite` produces a zero or finite number. -/
theorem finite_hasValue (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    ∃ r, (decode f (finite f neg u)).value? = some r := by
  obtain ⟨E, T, hE, hT, h⟩ := finite_fields f neg u hmax
  rw [h, decode_fields f neg E T (by omega) hT, if_neg (by omega)]
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem infinity_msb (f : Format) (neg : Bool) : (infinity f neg).msb = neg := by
  unfold infinity
  exact fields_msb f neg _ _ (by have := Nat.two_pow_pos f.w; omega) (Nat.two_pow_pos _)

theorem zero_msb (f : Format) (neg : Bool) : (zero f neg).msb = neg := by
  unfold zero
  exact fields_msb f neg 0 0 (Nat.two_pow_pos _) (Nat.two_pow_pos _)

theorem decode_canonicalNaN (f : Format) : decode f (canonicalNaN f) = .nan false := by
  have hp := f.hp
  have ht : 2 ^ (f.t - 1) < 2 ^ f.t :=
    Nat.pow_lt_pow_right (by omega) (by simp only [Format.t]; omega)
  unfold canonicalNaN
  rw [decode_fields f false _ _ (by have := Nat.two_pow_pos f.w; omega) ht, if_pos rfl,
    if_neg (Nat.ne_of_gt (Nat.two_pow_pos _))]
  simp

/-- `round` always delivers the sign it is given (§6.3), overflow results included. -/
theorem round_msb (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) :
    (round f mode neg n d).msb = neg := by
  unfold round
  simp only
  split
  · next hmax => exact finite_msb f neg _ hmax
  · split
    · exact infinity_msb f neg
    · exact finite_msb f neg _ (Nat.le_refl _)

/-- `round` never delivers a NaN: an infinity, or a zero or finite number. -/
theorem round_notNaN (f : Format) (mode : RoundingMode) (neg : Bool) (n d : Nat) :
    (∃ s, decode f (round f mode neg n d) = .inf s) ∨
      ∃ r, (decode f (round f mode neg n d)).value? = some r := by
  unfold round
  simp only
  split
  · next hmax => exact .inr (finite_hasValue f neg _ hmax)
  · split
    · exact .inl ⟨_, decode_infinity f neg⟩
    · exact .inr (finite_hasValue f neg _ (Nat.le_refl _))

/-- **Third theorem**: a quotient of two numbers with a nonzero divisor is never a NaN, under
every rounding-direction attribute (the statement is `DivideOfNumbersIsNotNaN` in
`IEEE754.lean`). -/
theorem divide_ofNumbersIsNotNaN (f : Format) : DivideOfNumbersIsNotNaN f := by
  intro mode a b x y hx hy hy0
  obtain ⟨sb, qb, cb, hb⟩ : ∃ sb qb cb, decode f b = .finite sb qb cb := by
    cases hb : decode f b with
    | finite sb qb cb => exact ⟨sb, qb, cb, rfl⟩
    | zero sb => rw [hb] at hy; cases hy; exact absurd rfl hy0
    | nan _ => rw [hb] at hy; cases hy
    | inf _ => rw [hb] at hy; cases hy
  cases ha : decode f a with
  | nan _ => rw [ha] at hx; cases hx
  | inf _ => rw [ha] at hx; cases hx
  | zero sa =>
    rw [divide_zero_finite f mode a b sa sb qb cb ha hb]
    exact .inr (finite_hasValue f _ 0 (Nat.zero_le _))
  | finite sa qa ca =>
    rw [divide_finite_finite f mode a b sa sb qa qb ca cb ha hb]
    exact round_notNaN f mode _ _ _

/-- **Fourth theorem**: every non-NaN quotient has the XOR of the operands' sign bits, for all
bit patterns and every rounding-direction attribute (the statement is `DivideSignIsXor` in
`IEEE754.lean`). -/
theorem divide_signIsXor (f : Format) : DivideSignIsXor f := by
  intro mode a b hnan
  have hN := decode_canonicalNaN f
  rcases decode_sign f a with ⟨sa, ha⟩ | ha | ha | ⟨qa, ca, ha⟩ <;>
  rcases decode_sign f b with ⟨sb, hb⟩ | hb | hb | ⟨qb, cb, hb⟩ <;>
  simp only [divide, ha, hb] at hnan ⊢ <;>
  -- `rw` matches the encoders syntactically, so a wrong alternative fails at once
  first
    | rw [infinity_msb]
    | rw [zero_msb]
    | rw [round_msb]
    | exact absurd hN (hnan false)

/-! ## The four properties determine the result

`divide_isUniquelyCharacterized`: any bit pattern with the four properties is the
roundTiesToEven quotient. The route: such a pattern is `canonQuot` (the infinity with the XOR
sign above the threshold, else the encoding of the roundTiesToEven magnitude), and so is
`divide` (it has the four properties by the theorems above). Below the threshold, a pattern
with a value is `finite f σ u` for its own units `u` (`decode_value_pattern`); `u` is a nearest
magnitude, hence one of the two neighbours `c·2^j`, `(c+1)·2^j` of the exact quotient
(`rne_near_two`); if it were not the roundTiesToEven choice, both neighbours would have even
significands (`rne_two_even`), which `not_both_even` rules out. -/

/-- Every pattern is its fields `S ‖ E ‖ T`, with `S = msb`. -/
theorem eq_fields (f : Format) (R : BitVec f.k) :
    R = fields f R.msb (R.toNat / 2 ^ f.t % 2 ^ f.w) (R.toNat % 2 ^ f.t) := by
  have hE := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hT := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  apply BitVec.eq_of_toNat_eq
  rw [fields_toNat f _ _ _ hE hT, msb_eq_S]
  have hlt : R.toNat < 2 * 2 ^ (f.w + f.t) := two_pow_k f ▸ R.isLt
  have h1 := Nat.div_add_mod R.toNat (2 ^ (f.w + f.t))
  have e : 2 ^ (f.w + f.t) = 2 ^ f.t * 2 ^ f.w := by rw [Nat.pow_add, Nat.mul_comm]
  have h2 : R.toNat % 2 ^ (f.w + f.t) =
      R.toNat / 2 ^ f.t % 2 ^ f.w * 2 ^ f.t + R.toNat % 2 ^ f.t := by
    rw [e, Nat.mod_mul, Nat.add_comm, Nat.mul_comm]
  have hS : R.toNat / 2 ^ (f.w + f.t) < 2 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
  rw [h2] at h1
  generalize R.toNat / 2 ^ (f.w + f.t) = S at *
  have : S = 0 ∨ S = 1 := by omega
  rcases this with rfl | rfl <;> simp <;> omega

/-- An infinity pattern is `infinity f s`. -/
theorem decode_inf_eq (f : Format) (R : BitVec f.k) (s : Bool) (h : decode f R = .inf s) :
    R = infinity f s := by
  have hR := eq_fields f R
  have hEl := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hTl := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  generalize R.toNat / 2 ^ f.t % 2 ^ f.w = E at hR hEl
  generalize R.toNat % 2 ^ f.t = T at hR hTl
  generalize R.msb = σ at hR
  rw [hR, decode_fields f σ E T hEl hTl] at h
  rw [hR]
  split at h
  · next hE =>
    split at h
    · next hT => cases h; subst hE; subst hT; rfl
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

/-- A pattern with a value is the encoding (`finite`) of its magnitude `u` in units, with its
own sign bit; `u` is representable and at most `maxUnits`. -/
theorem decode_value_pattern (f : Format) (R : BitVec f.k) (r : Int × Nat)
    (h : (decode f R).value? = some r) :
    ∃ u, u ≤ f.maxUnits ∧ RepU f u ∧ IsUnits f r R.msb u ∧ R = finite f R.msb u := by
  have hp := f.hp
  have hw2 := two_emax f
  have he := emax_pos f
  have hR := eq_fields f R
  have hEl := Nat.mod_lt (R.toNat / 2 ^ f.t) (Nat.two_pow_pos f.w)
  have hTl := Nat.mod_lt R.toNat (Nat.two_pow_pos f.t)
  generalize R.toNat / 2 ^ f.t % 2 ^ f.w = E at hR hEl
  generalize R.toNat % 2 ^ f.t = T at hR hTl
  generalize R.msb = σ at hR ⊢
  rw [hR, decode_fields f σ E T hEl hTl] at h
  rw [hR]
  have ht : 2 ^ f.t + 2 ^ f.t = 2 ^ f.p := by
    rw [← Nat.two_mul, ← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hmaxp : 2 ^ f.p - 1 ≤ f.maxUnits := by
    unfold Format.maxUnits
    exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  split at h
  · split at h <;> simp [Datum.value?] at h
  · split at h
    · next hE0 =>
      subst hE0
      split at h
      · next hT0 =>
        subst hT0
        simp only [Datum.value?, Option.some.injEq] at h
        subst h
        exact ⟨0, Nat.zero_le _, zero_rep f, ⟨by decide, by simp⟩, zero_eq_finite f σ⟩
      · obtain ⟨v, hv, hU⟩ := value_finite f σ (f.emin - f.t) T (Int.le_refl _)
        rw [hv] at h; cases h
        have e : (f.emin - f.t - f.qmin).toNat = 0 := by unfold Format.qmin; omega
        rw [e, Nat.pow_zero, Nat.mul_one] at hU
        refine ⟨T, by omega, ⟨T, 0, by omega, by simp⟩, hU, ?_⟩
        unfold finite; rw [if_pos hTl]
    · next hEm hE0 =>
      have hq : f.qmin ≤ (E : Int) - f.emax - f.t := by
        unfold Format.qmin Format.emin; omega
      obtain ⟨v, hv, hU⟩ := value_finite f σ ((E : Int) - f.emax - f.t) (2 ^ f.t + T) hq
      rw [hv] at h; cases h
      have e : ((E : Int) - f.emax - f.t - f.qmin).toNat = E - 1 := by
        unfold Format.qmin Format.emin; omega
      rw [e] at hU
      refine ⟨(2 ^ f.t + T) * 2 ^ (E - 1), ?_, ⟨2 ^ f.t + T, E - 1, by omega, rfl⟩, hU, ?_⟩
      · unfold Format.maxUnits
        exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
      · have hc0 : 2 ^ f.t + T ≠ 0 := by omega
        have hlog : (2 ^ f.t + T).log2 = f.t := by
          rw [Nat.log2_eq_iff hc0, Nat.pow_succ]; omega
        have hge : ¬ (2 ^ f.t + T) * 2 ^ (E - 1) < 2 ^ f.t := by
          have := Nat.le_mul_of_pos_right (2 ^ f.t + T) (Nat.two_pow_pos (E - 1)); omega
        unfold finite
        rw [if_neg hge]
        simp only []
        rw [log2_mul_two_pow _ hc0, hlog, show f.t + (E - 1) - f.t = E - 1 by omega,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _), show E - 1 + 1 = E by omega,
          show 2 ^ f.t + T - 2 ^ f.t = T by omega]

/-- The last bit of an encoded magnitude is the last bit of its significand at its own
spacing (the subnormal `T`, or the integral significand `c`). -/
theorem finite_mod_two (f : Format) (neg : Bool) (u : Nat) (hmax : u ≤ f.maxUnits) :
    (finite f neg u).toNat % 2 = u / 2 ^ ulpExp f u % 2 := by
  have hp := f.hp
  have hw2 := two_emax f
  have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have hwt : 2 ^ (f.w + f.t) = 2 * 2 ^ (f.w + f.t - 1) := by
    rw [← Nat.pow_succ']; congr 1; simp only [Format.t]; omega
  have parity : ∀ E T, E < 2 ^ f.w → T < 2 ^ f.t → (fields f neg E T).toNat % 2 = T % 2 := by
    intro E T hE hT
    rw [fields_toNat f neg E T hE hT, hwt, ht2]
    have : E * (2 * 2 ^ (f.t - 1)) = 2 * (E * 2 ^ (f.t - 1)) := by ac_rfl
    rw [this]
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  unfold ulpExp finite
  by_cases hlt : u < 2 ^ f.t
  · rw [if_pos hlt, parity 0 u (Nat.two_pow_pos _) hlt]
    by_cases h0 : u = 0
    · simp [h0]
    · have : u.log2 < f.t := (Nat.log2_lt h0).2 hlt
      have : u.log2 + 1 - f.p = 0 := by simp only [Format.t] at this; omega
      rw [this, Nat.pow_zero, Nat.div_one]
  · rw [if_neg hlt]
    simp only []
    have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    have hl : f.t ≤ u.log2 := (Nat.le_log2 hu0).2 (by omega)
    have hj : u.log2 + 1 - f.p = u.log2 - f.t := by simp only [Format.t]; omega
    rw [hj]
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    generalize u.log2 - f.t = j at *
    rw [parity (j + 1) _ (by omega) hT]
    omega

theorem ulpExp_mul (f : Format) (c j : Nat) (h0 : 0 < c) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) : ulpExp f (c * 2 ^ j) = j := by
  have hp := f.hp
  unfold ulpExp
  rw [log2_mul_two_pow j (by omega)]
  have hl : c.log2 < f.p := (Nat.log2_lt (by omega)).2 hc
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · omega
  · have hl2 : f.p - 1 ≤ c.log2 := (Nat.le_log2 (by omega)).2 (hn hj)
    omega

theorem evenSig_iff (f : Format) (c j : Nat) (h0 : 0 < c) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) : EvenSig f (c * 2 ^ j) ↔ c % 2 = 0 := by
  unfold EvenSig
  rw [ulpExp_mul f c j h0 hc hn, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The two neighbours `c·2^j` and `(c+1)·2^j` never both have even significands. -/
theorem not_both_even (f : Format) (c j : Nat) (hc : c < 2 ^ f.p)
    (hn : 0 < j → 2 ^ (f.p - 1) ≤ c) (h1 : EvenSig f (c * 2 ^ j))
    (h2 : EvenSig f ((c + 1) * 2 ^ j)) : False := by
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  rcases Nat.eq_zero_or_pos c with rfl | h0
  · -- then j = 0, and the upper neighbour is 1 unit, whose significand 1 is odd
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · have := hn h; omega
    subst hj
    rw [evenSig_iff f (0 + 1) 0 (by omega) (by omega) (by omega)] at h2
    omega
  · rw [evenSig_iff f c j h0 hc hn] at h1
    by_cases hc1 : c + 1 < 2 ^ f.p
    · rw [evenSig_iff f (c + 1) j (by omega) hc1 (fun hj => by have := hn hj; omega)] at h2
      omega
    · -- c = 2^p − 1 is odd
      omega

/-- The only representable magnitudes at most as far from `N / D` as the roundTiesToEven
result are its two neighbours `c·2^j` and `(c+1)·2^j`. -/
theorem rne_near_two (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w)
    (hle : udist N D w ≤ udist N D (roundUnits f .roundTiesToEven neg N D)) :
    w = N / (D * 2 ^ ulpExp f (N / D)) * 2 ^ ulpExp f (N / D) ∨
      w = (N / (D * 2 ^ ulpExp f (N / D)) + 1) * 2 ^ ulpExp f (N / D) := by
  obtain ⟨-, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at hle
  generalize ulpExp f (N / D) = j at *
  have hM : 0 < D * 2 ^ j := Nat.mul_pos hD (Nat.two_pow_pos _)
  have hdm := Nat.div_add_mod N (D * 2 ^ j)
  have hr := Nat.mod_lt N hM
  generalize N / (D * 2 ^ j) = c at *
  generalize N % (D * 2 ^ j) = r at *
  have hg := gap f c j w hc2 hw
  have e1 : c * 2 ^ j * D = D * 2 ^ j * c := by ac_rfl
  have e2 : (c + 1) * 2 ^ j * D = D * 2 ^ j * c + D * 2 ^ j := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; ac_rfl
  rcases hg with h | h
  · rcases Nat.lt_or_eq_of_le h with h | h
    · exfalso
      have := e1 ▸ Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at this
      unfold udist at hle
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      split at hle <;> omega
    · exact .inl h
  · rcases Nat.lt_or_eq_of_le h with h | h
    · exfalso
      have := Nat.mul_le_mul_right D (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul, e2] at this
      unfold udist at hle
      generalize D * 2 ^ j * c = X at *
      generalize D * 2 ^ j = M at *
      split at hle <;> omega
    · exact .inr h.symm

/-- No representable magnitude other than the roundTiesToEven result is as near to `N / D`
and has an even significand. -/
theorem rne_two_even (f : Format) (neg : Bool) (N D : Nat) (hD : 0 < D) (w : Nat)
    (hw : RepU f w) (hne : w ≠ roundUnits f .roundTiesToEven neg N D)
    (hle : udist N D w ≤ udist N D (roundUnits f .roundTiesToEven neg N D))
    (hev : EvenSig f w) : False := by
  have hstar := rne_tie_even f neg N D hD w hw hne hle
  have h2 := rne_near_two f neg N D hD w hw hle
  obtain ⟨hc1, hc2⟩ := trunc_bounds f N D
  rw [rne_unfold] at hne hstar
  generalize ulpExp f (N / D) = j at *
  generalize N / (D * 2 ^ j) = c at *
  split at hstar
  · next hup =>
    rw [if_pos hup] at hne
    rcases h2 with rfl | h
    · exact not_both_even f c j hc1 hc2 hev hstar
    · exact hne h
  · next hup =>
    rw [if_neg hup] at hne
    rcases h2 with h | rfl
    · exact hne h
    · exact not_both_even f c j hc1 hc2 hstar hev

/-- A value read off a pattern is `±n / d` with the pattern's sign bit, `d > 0`. -/
theorem value_sgn (f : Format) (a : BitVec f.k) (x : Int × Nat)
    (h : (decode f a).value? = some x) : ∃ n d, 0 < d ∧ x = (sgn a.msb n, d) := by
  rcases decode_sign f a with ⟨_, h'⟩ | h' | h' | ⟨q, c, h'⟩ <;> rw [h'] at h
  · simp [Datum.value?] at h
  · simp [Datum.value?] at h
  · simp only [Datum.value?, Option.some.injEq] at h
    subst h
    refine ⟨0, 1, by decide, ?_⟩
    generalize a.msb = s
    cases s <;> rfl
  · rw [value_finite_eq] at h
    cases h
    exact ⟨_, _, Nat.two_pow_pos _, rfl⟩

/-- The exact quotient of two values read off patterns, with the XOR sign. -/
theorem quotient_sgn (f : Format) (a b : BitVec f.k) (x y : Int × Nat)
    (hx : (decode f a).value? = some x) (hy : (decode f b).value? = some y) (hy0 : y.1 ≠ 0) :
    ∃ N D, 0 < D ∧ fracDiv x y = (sgn (a.msb ^^ b.msb) N, D) := by
  obtain ⟨nx, dx, hdx, rfl⟩ := value_sgn f a x hx
  obtain ⟨ny, dy, hdy, rfl⟩ := value_sgn f b y hy
  have hny : ny ≠ 0 := by
    rintro rfl
    apply hy0
    generalize b.msb = s
    cases s <;> rfl
  exact ⟨_, _, Nat.mul_pos hdx (Nat.pos_of_ne_zero hny), fracDiv_sgn _ _ _ _ _ _ hny⟩

/-- Distinct magnitudes of one sign are distinct fractions. -/
theorem units_ne (f : Format) (r v : Int × Nat) (σ : Bool) (u1 u2 : Nat)
    (hr : IsUnits f r σ u1) (hv : IsUnits f v σ u2) (hne : u1 ≠ u2) :
    v.1 * r.2 ≠ r.1 * v.2 := by
  intro h
  apply hne
  rw [isUnits_sgn] at hr hv
  have hpos : (0 : Int) < (r.2 : Int) * v.2 := by
    have := hr.1; have := hv.1
    exact Int.mul_pos (by omega) (by omega)
  have key : sgn σ u1 * ((r.2 : Int) * v.2) = sgn σ u2 * ((r.2 : Int) * v.2) := by
    calc sgn σ u1 * ((r.2 : Int) * v.2) = r.1 * 2 ^ f.scale * v.2 := by rw [hr.2]; ac_rfl
      _ = r.1 * v.2 * 2 ^ f.scale := by ac_rfl
      _ = v.1 * r.2 * 2 ^ f.scale := by rw [h]
      _ = v.1 * 2 ^ f.scale * r.2 := by ac_rfl
      _ = sgn σ u2 * ((r.2 : Int) * v.2) := by rw [hv.2]; ac_rfl
  have := Int.eq_of_mul_eq_mul_right (Int.ne_of_gt hpos) key
  cases σ <;> simp only [sgn, Bool.false_eq_true, ↓reduceIte] at this <;> omega

theorem noFarther_iff_udist (f : Format) (r v : Int × Nat) (σ : Bool) (u u' N D : Nat)
    (hr : IsUnits f r σ u) (hv : IsUnits f v σ u') :
    NoFarther r v (sgn σ N, D) ↔
      udist (N * 2 ^ f.scale) D u ≤ udist (N * 2 ^ f.scale) D u' := by
  rw [noFarther_iff_units f r v σ σ σ u u' N D hr hv, natAbs_units_same, natAbs_units_same]

/-- A magnitude `u` of sign `σ` (the value `r`) that is nearest to `±N / D` among the patterns
of the format, and has an even significand whenever another pattern is equally near, is the
roundTiesToEven magnitude, provided that one is finite. -/
theorem units_eq_rne (f : Format) (σ : Bool) (N D u : Nat) (hD : 0 < D) (r : Int × Nat)
    (hu : RepU f u) (hR : IsUnits f r σ u)
    (hstar : roundUnits f .roundTiesToEven σ (N * 2 ^ f.scale) D ≤ f.maxUnits)
    (hnear : ∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        NoFarther r v (sgn σ N, D))
    (htie : ∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
        v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (sgn σ N, D) → EvenSig f u) :
    u = roundUnits f .roundTiesToEven σ (N * 2 ^ f.scale) D := by
  obtain ⟨p, hp, hpU⟩ := decode_encode f σ _ (rne_rep f _ _ _) hstar
  have hle := (noFarther_iff_udist f r p σ u _ N D hR hpU).mp (hnear _ p hp)
  apply Classical.byContradiction
  intro hne
  have hsle := rne_nearest f σ (N * 2 ^ f.scale) D hD u hu
  have hev : EvenSig f u := htie _ p hp (units_ne f r p σ u _ hR hpU hne)
    ((noFarther_iff_udist f p r σ _ u N D hpU hR).mpr hsle)
  exact rne_two_even f σ _ D hD u hu hne hle hev

/-- The pattern singled out by the four properties, for sign `σ` and exact quotient `q`. -/
def canonQuot (f : Format) (σ : Bool) (q : Int × Nat) : BitVec f.k :=
  if q.2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ q.1.natAbs * 2 ^ f.p then infinity f σ
  else finite f σ (roundUnits f .roundTiesToEven σ (q.1.natAbs * 2 ^ f.scale) q.2)

/-- Any pattern with the four properties is `canonQuot`. -/
theorem eq_canonQuot (f : Format) (a b R : BitVec f.k) (x y : Int × Nat)
    (hx : (decode f a).value? = some x) (hy : (decode f b).value? = some y) (hy0 : y.1 ≠ 0)
    (h1 : (∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r)
    (h2 : R.msb = (a.msb ^^ b.msb))
    (h3 : (∃ s, decode f R = .inf s) ↔
      (fracDiv x y).2 * 2 ^ f.emax * (2 ^ (f.p + 1) - 1) ≤ (fracDiv x y).1.natAbs * 2 ^ f.p)
    (h4 : ∀ r, (decode f R).value? = some r →
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          NoFarther r v (fracDiv x y)) ∧
      (∀ (z : BitVec f.k) (v : Int × Nat), (decode f z).value? = some v →
          v.1 * r.2 ≠ r.1 * v.2 → NoFarther v r (fracDiv x y) → R.toNat % 2 = 0)) :
    R = canonQuot f (a.msb ^^ b.msb) (fracDiv x y) := by
  obtain ⟨N, D, hD, hxy⟩ := quotient_sgn f a b x y hx hy hy0
  rw [hxy] at h3 h4 ⊢
  generalize (a.msb ^^ b.msb) = σ at h2 h4 ⊢
  unfold canonQuot
  simp only [natAbs_sgn] at h3 ⊢
  split
  · next hT =>
    obtain ⟨s, hs⟩ := h3.mpr hT
    have hRs := decode_inf_eq f R s hs
    rw [hRs, infinity_msb] at h2
    rw [hRs, h2]
  · next hT =>
    obtain ⟨r, hr⟩ := h1.resolve_left (fun h => hT (h3.mp h))
    obtain ⟨u, hmax, hu, hU, hReq⟩ := decode_value_pattern f R r hr
    rw [h2] at hU hReq
    have hstar : roundUnits f .roundTiesToEven σ (N * 2 ^ f.scale) D ≤ f.maxUnits :=
      Nat.le_of_not_lt fun h =>
        hT ((threshold_units_iff f N D).mp ((rne_overflow_iff f σ _ D hD).mp h))
    rw [hReq, units_eq_rne f σ N D u hD r hu hU hstar (h4 r hr).1 fun z v hv hne hle => by
      have := (h4 r hr).2 z v hv hne hle
      rw [hReq, finite_mod_two f σ u hmax] at this
      exact this]

/-- An infinity or a pattern with a value is not a NaN. -/
theorem not_nan_of (f : Format) (R : BitVec f.k)
    (h : (∃ s, decode f R = .inf s) ∨ ∃ r, (decode f R).value? = some r) :
    ∀ s, decode f R ≠ .nan s := by
  intro s hs
  rcases h with ⟨s', hs'⟩ | ⟨r, hr⟩
  · rw [hs] at hs'; cases hs'
  · rw [hs] at hr; simp [Datum.value?] at hr

/-- **Fifth theorem**: the four properties determine the roundTiesToEven quotient (the
statement is `DivideIsUniquelyCharacterized` in `IEEE754.lean`). -/
theorem divide_isUniquelyCharacterized (f : Format) : DivideIsUniquelyCharacterized f := by
  intro a b R x y hx hy hy0 h1 h2 h3 h4
  have g1 := divide_ofNumbersIsNotNaN f .roundTiesToEven a b x y hx hy hy0
  have g2 := divide_signIsXor f .roundTiesToEven a b (not_nan_of f _ g1)
  rw [eq_canonQuot f a b R x y hx hy hy0 h1 (h2 (not_nan_of f R h1)) h3 h4,
    eq_canonQuot f a b _ x y hx hy hy0 g1 g2 (divide_overflowsAtThreshold f a b x y hx hy hy0)
      (fun r hr => divide_isNearestTiesToEven f a b x y r hx hy hy0 hr)]

end SvGolf.IEEE754

namespace SvGolf.IEEE754

/-- The challenge instances. -/
example : DivideIsNearestTiesToEven binary16 := divide_isNearestTiesToEven _
example : DivideOverflowsAtThreshold binary16 := divide_overflowsAtThreshold _
example : DivideOfNumbersIsNotNaN binary16 := divide_ofNumbersIsNotNaN _
example : DivideSignIsXor binary16 := divide_signIsXor _
example : DivideIsUniquelyCharacterized binary16 := divide_isUniquelyCharacterized _
example : DivideIsNearestTiesToEven binary32 := divide_isNearestTiesToEven _
example : DivideOverflowsAtThreshold binary32 := divide_overflowsAtThreshold _
example : DivideOfNumbersIsNotNaN binary32 := divide_ofNumbersIsNotNaN _
example : DivideSignIsXor binary32 := divide_signIsXor _
example : DivideIsUniquelyCharacterized binary32 := divide_isUniquelyCharacterized _

end SvGolf.IEEE754

end IEEE754Proofs

/-! # Section `ScaleInvariance`: `roundUnits` only sees the ratio `N / D` (was in the former 16-bit task's `SpecFacts.lean`) -/

section ScaleInvariance

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

/-- **`roundUnits` only sees the ratio**: scaling the exact quotient's numerator
and denominator by the same power of two does not change the rounded
magnitude, in every rounding mode. (It uses only `N / D`, `N / M`, `N % M`
and comparisons of `2·(N % M)` with `M`, all of which scale together.) This
removes the operands' exponents from a rounding certificate. -/
theorem roundUnits_scale (f : Format) (mode : RoundingMode) (neg : Bool) (N D k : Nat) :
    roundUnits f mode neg (N * 2 ^ k) (D * 2 ^ k) = roundUnits f mode neg N D := by
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  simp only [roundUnits, Nat.mul_div_mul_right N D hk]
  generalize ulpExp f (N / D) = j
  rw [Nat.mul_right_comm D (2 ^ k) (2 ^ j), Nat.mul_div_mul_right N _ hk,
    Nat.mul_mod_mul_right]
  generalize D * 2 ^ j = M
  generalize N / M = c
  generalize N % M = r
  have hlt : (M * 2 ^ k < 2 * (r * 2 ^ k)) = (M < 2 * r) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_lt_mul_right hk)
  have hle : (M * 2 ^ k ≤ 2 * (r * 2 ^ k)) = (M ≤ 2 * r) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_le_mul_right_iff hk)
  have heq : (2 * (r * 2 ^ k) = M * 2 ^ k) = (2 * r = M) := by
    rw [← Nat.mul_assoc]; exact propext (Nat.mul_left_inj (Nat.pos_iff_ne_zero.mp hk))
  have hz : (r * 2 ^ k = 0) = (r = 0) :=
    propext ⟨fun h => (Nat.mul_eq_zero.mp h).resolve_right (Nat.pos_iff_ne_zero.mp hk),
      fun h => by rw [h, Nat.zero_mul]⟩
  cases mode <;> simp [hlt, hle, heq, hz]

-- the certificate on spec values (kernel evaluation): 1/3, an overflow, a
-- subnormal tie, and a rejected neighbour of 1/3
-- the reference's 13 steps on 1.0 / 1.0 (na4 = nb4 = 1024): qq = 2^12, rem[13] = 0
-- and on 1.0 / 1.5 (nb4 = 1536): qq = 2730 = 0b0101010101010, remainder 2 * 1024
end SvGolf.FdivParam

end ScaleInvariance

/-! # Section `RneInterval`: The interval characterization of the roundTiesToEven magnitude, for every format (was in
the former 16-bit task's `Cert16.lean`)

`rne_eq_iff` (the heart): a representable magnitude `u` with an upper neighbour at distance `up` and a lower neighbour at
distance `dn` (no representable magnitude strictly between) is the roundTiesToEven magnitude of `N / D` iff `N / D` lies
within half a spacing of `u` on each side, a boundary allowed only if `u`'s significand is even (`→`: `rne_nearest` and
`rne_tie_even` at the two neighbours; `←`: `rne_nearest` plus `rne_two_even` at `u`). `rne_eq_iff_canon` instantiates
it at `u = c·2^j` (`gap` supplies the neighbours; the lower one is `2^(j-1)` below a binade bottom). `leB` is the
certificate's "equality only for an even significand". -/

section RneInterval

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

/-- `x ≤ y`, strict unless `par` (the certificate's "equality only for an even significand"). -/
def leB (par : Bool) (x y : Nat) : Prop := if par = true then x ≤ y else x < y

theorem leB_of_eq {par : Bool} (hp : par = true) (x y : Nat) : leB par x y = (x ≤ y) := by
  simp [leB, hp]

theorem leB_of_ne {par : Bool} (hp : ¬ par = true) (x y : Nat) : leB par x y = (x < y) := by
  simp [leB, hp]

/-- **The certificate interval characterizes the roundTiesToEven result.** `u` is a
representable magnitude with an upper neighbour at distance `up` and a lower neighbour at
distance `dn` (nothing representable strictly between), and `par` says that `u`'s significand
is even. Then `u` is the roundTiesToEven magnitude of `N / D` iff `N / D` lies within half a
spacing of `u` on each side, a boundary allowed only if `par`. -/
theorem rne_eq_iff (f : Format) (s : Bool) (N D u up dn : Nat) (par : Bool) (hD : 0 < D)
    (hup0 : 0 < up) (hdn0 : 0 < dn)
    (hu : RepU f u) (hup : RepU f (u + up))
    (hdn : u ≠ 0 → dn ≤ u ∧ RepU f (u - dn))
    (nhi : ∀ w, RepU f w → w ≤ u ∨ u + up ≤ w)
    (nlo : u ≠ 0 → ∀ w, RepU f w → w ≤ u - dn ∨ u ≤ w)
    (hev : EvenSig f u ↔ par = true) :
    (u = roundUnits f .roundTiesToEven s N D) ↔
      ((u = 0 ∨ leB par (D * (2 * u - dn)) (2 * N)) ∧ leB par (2 * N) (D * (2 * u + up))) := by
  have hnear := rne_nearest f s N D hD
  have htie := rne_tie_even f s N D hD
  have hrep := rne_rep f s N D
  have htwo := rne_two_even f s N D hD
  generalize roundUnits f .roundTiesToEven s N D = v at *
  have hDup : 0 < up * D := Nat.mul_pos hup0 hD
  have hDdn : 0 < dn * D := Nat.mul_pos hdn0 hD
  have eU : D * (2 * u + up) = 2 * (u * D) + up * D := by
    rw [Nat.mul_add]; ac_rfl
  have eUp : (u + up) * D = u * D + up * D := Nat.add_mul _ _ _
  have eL : u ≠ 0 → D * (2 * u - dn) = (u - dn) * D + u * D ∧ (u - dn) * D + dn * D = u * D := by
    intro h0
    obtain ⟨h1, -⟩ := hdn h0
    constructor
    · rw [show 2 * u - dn = (u - dn) + u by omega, Nat.mul_add]; ac_rfl
    · rw [← Nat.add_mul, Nat.sub_add_cancel h1]
  constructor
  · intro h
    subst h
    have hhi : leB par (2 * N) (D * (2 * u + up)) := by
      have h1 := hnear (u + up) hup
      unfold udist at h1
      rw [eUp] at h1
      rw [eU]
      by_cases hp : par = true
      · rw [leB_of_eq hp]; omega
      · rw [leB_of_ne hp]
        refine Classical.byContradiction fun hge => ?_
        apply hp
        apply hev.mp
        apply htie (u + up) hup (by omega)
        unfold udist
        rw [eUp]
        omega
    refine ⟨?_, hhi⟩
    by_cases hu0 : u = 0
    · exact .inl hu0
    · right
      obtain ⟨hdle, hrepd⟩ := hdn hu0
      obtain ⟨e1, e2⟩ := eL hu0
      have h1 := hnear (u - dn) hrepd
      unfold udist at h1
      rw [e1]
      by_cases hp : par = true
      · rw [leB_of_eq hp]; omega
      · rw [leB_of_ne hp]
        refine Classical.byContradiction fun hge => ?_
        apply hp
        apply hev.mp
        apply htie (u - dn) hrepd (by omega)
        unfold udist
        omega
  · rintro ⟨hlo, hhi⟩
    refine Classical.byContradiction fun hne => ?_
    have hn1 := hnear u hu
    unfold udist at hn1
    rcases nhi v hrep with hv | hv
    · have hu0 : u ≠ 0 := by omega
      obtain ⟨hdle, hrepd⟩ := hdn hu0
      have hvlo : v ≤ u - dn := by
        rcases nlo hu0 v hrep with h | h
        · exact h
        · omega
      have hVD : v * D ≤ (u - dn) * D := Nat.mul_le_mul_right D hvlo
      obtain ⟨e1, e2⟩ := eL hu0
      have hlo' := hlo.resolve_left hu0
      rw [e1] at hlo'
      by_cases hp : par = true
      · rw [leB_of_eq hp] at hlo'
        have hle : udist N D u ≤ udist N D v := by unfold udist; omega
        exact htwo u hu hne hle (hev.mpr hp)
      · rw [leB_of_ne hp] at hlo'
        omega
    · have hVD : (u + up) * D ≤ v * D := Nat.mul_le_mul_right D hv
      rw [eUp] at hVD
      rw [eU] at hhi
      by_cases hp : par = true
      · rw [leB_of_eq hp] at hhi
        have hle : udist N D u ≤ udist N D v := by unfold udist; omega
        exact htwo u hu hne hle (hev.mpr hp)
      · rw [leB_of_ne hp] at hhi
        omega

theorem rep_succ (f : Format) (c j : Nat) (hc : c < 2 ^ f.p) :
    RepU f (c * 2 ^ j + 2 ^ j) := by
  have e : c * 2 ^ j + 2 ^ j = (c + 1) * 2 ^ j := by rw [Nat.succ_mul]
  rw [e]
  by_cases h : c + 1 < 2 ^ f.p
  · exact ⟨c + 1, j, h, rfl⟩
  · refine ⟨2 ^ (f.p - 1), j + 1, ?_, ?_⟩
    · have := two_pow_pred f; have := Nat.two_pow_pos (f.p - 1); omega
    · have : c + 1 = 2 ^ f.p := by omega
      rw [this, two_pow_pred, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]

/-- The canonical instance of `rne_eq_iff`: `u = c·2^j` with `c` a `p`-bit significand (or
`j = 0`), upper neighbour at `2^j`, lower neighbour at `2^j`, or `2^(j-1)` at the bottom of a
binade (`c = 2^(p-1)`, `j > 0`). -/
theorem rne_eq_iff_canon (f : Format) (s : Bool) (N D c j u up dn : Nat) (par : Bool)
    (hD : 0 < D) (hc : c < 2 ^ f.p) (hc0 : 0 < c) (hj : 0 < j → 2 ^ (f.p - 1) ≤ c)
    (hu : u = c * 2 ^ j) (hup : up = 2 ^ j)
    (hdn : dn = if c = 2 ^ (f.p - 1) ∧ 0 < j then 2 ^ (j - 1) else 2 ^ j)
    (hev : c % 2 = 0 ↔ par = true) :
    (u = roundUnits f .roundTiesToEven s N D) ↔
      ((u = 0 ∨ leB par (D * (2 * u - dn)) (2 * N)) ∧ leB par (2 * N) (D * (2 * u + up))) := by
  subst hu hup hdn
  have hp := f.hp
  have hp2 := two_pow_pred f
  have hpos := Nat.two_pow_pos (f.p - 1)
  have hj0 := Nat.two_pow_pos j
  have hdn0 : 0 < (if c = 2 ^ (f.p - 1) ∧ 0 < j then 2 ^ (j - 1) else 2 ^ j) := by
    split <;> exact Nat.two_pow_pos _
  refine rne_eq_iff f s N D _ _ _ par hD hj0 hdn0 ⟨c, j, hc, rfl⟩ (rep_succ f c j hc) ?_ ?_ ?_
    ((evenSig_iff f c j hc0 hc hj).trans hev)
  · intro _
    by_cases hb : c = 2 ^ (f.p - 1) ∧ 0 < j
    · rw [if_pos hb]
      obtain ⟨hc', hj'⟩ := hb
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i + 1 - 1 = i := by omega
      have e1 : (2 ^ f.p - 1) * 2 ^ i + 2 ^ i = c * 2 ^ (i + 1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_two_pow), hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
      have e2 : 2 ^ i ≤ c * 2 ^ (i + 1) := by omega
      rw [hi]
      exact ⟨e2, ⟨2 ^ f.p - 1, i, by omega, by omega⟩⟩
    · rw [if_neg hb]
      have e1 : c * 2 ^ j - 2 ^ j = (c - 1) * 2 ^ j := by
        rw [Nat.sub_mul, Nat.one_mul]
      exact ⟨Nat.le_mul_of_pos_left _ hc0, ⟨c - 1, j, by omega, e1⟩⟩
  · intro w hw
    rcases gap f c j w hj hw with h | h
    · exact .inl h
    · exact .inr (by rw [Nat.succ_mul] at h; exact h)
  · intro _ w hw
    by_cases hb : c = 2 ^ (f.p - 1) ∧ 0 < j
    · rw [if_pos hb]
      obtain ⟨hc', hj'⟩ := hb
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hi : i + 1 - 1 = i := by omega
      have e1 : (2 ^ f.p - 1) * 2 ^ i + 2 ^ i = c * 2 ^ (i + 1) := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_two_pow), hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
      rw [hi]
      rcases gap f (2 ^ f.p - 1) i w (fun _ => by omega) hw with h | h
      · exact .inl (by omega)
      · have e3 : 2 ^ f.p * 2 ^ i = c * 2 ^ (i + 1) := by
          rw [hc', hp2, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
        exact .inr (by rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h; omega)
    · rw [if_neg hb]
      rcases gap f (c - 1) j w (fun hj' => by omega) hw with h | h
      · exact .inl (by rw [Nat.sub_mul, Nat.one_mul] at h; exact h)
      · exact .inr (by rw [Nat.sub_add_cancel hc0] at h; exact h)

/-! ## The certificate on a pattern's fields -/

theorem ite_decide_leB (q : Prop) [Decidable q] (x y : Nat) :
    ((if q then decide (x ≤ y) else decide (x < y)) = true) ↔ leB (decide q) x y := by
  by_cases h : q <;> simp [leB, h]

end SvGolf.FdivParam

end RneInterval

/-! # Section `RoundingBounds`: The certificate's two interval bounds from the rounding core's inequalities (was in
the former 16-bit task's `DpRound.lean`): `low_*`, `up_*`, with `S = nb·M`, `u = z·P`, `T = P·M0`. -/

section RoundingBounds

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

/-! ## The certificate's interval bounds from the rounding core

`S = nb·M`, `u = z·P`, `T = P·M0` (so that `T / S = M0·P / (nb·M)` is the exact quotient); `qm` is the quotient of
`M0` by `nb`, so `nb·qm ≤ M0 < nb·qm + nb`. -/

theorem two_zP_sub (z P y : Nat) (hy : y + 1 = 2 * z) : 2 * (z * P) - P = y * P := by
  have h : 2 * (z * P) = y * P + P := by
    calc 2 * (z * P) = (2 * z) * P := by rw [Nat.mul_assoc]
      _ = (y + 1) * P := by rw [hy]
      _ = y * P + P := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem two_zP_add (z P y : Nat) (hy : y = 2 * z + 1) : 2 * (z * P) + P = y * P := by
  subst hy
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]

/-- Lower bound, distance `P` below `u`. -/
theorem low_std (nb M P y z qm M0 : Nat) (hy : y + 1 = 2 * z) (hX : y * M ≤ 2 * qm) (hq : nb * qm ≤ M0) :
    (nb * M) * (2 * (z * P) - P) ≤ 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ ≤ P * (nb * (2 * qm)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ ≤ P * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (P * M0) := by ac_rfl

/-- ... strict, from a strict `qm`-side bound. -/
theorem low_std_lt_a (nb M P y z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y + 1 = 2 * z)
    (hX : y * M < 2 * qm) (hq : nb * qm ≤ M0) : (nb * M) * (2 * (z * P) - P) < 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ < P * (nb * (2 * qm)) := Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hX hnb) hP
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ ≤ P * (2 * M0) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (P * M0) := by ac_rfl

/-- ... strict, from a strict `M0`-side bound (the sticky bit is set). -/
theorem low_std_lt_b (nb M P y z qm M0 : Nat) (hP : 0 < P) (hy : y + 1 = 2 * z)
    (hX : y * M ≤ 2 * qm) (hq : nb * qm < M0) : (nb * M) * (2 * (z * P) - P) < 2 * (P * M0) := by
  rw [two_zP_sub z P y hy]
  calc (nb * M) * (y * P) = P * (nb * (y * M)) := by ac_rfl
    _ ≤ P * (nb * (2 * qm)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = P * (2 * (nb * qm)) := by ac_rfl
    _ < P * (2 * M0) := Nat.mul_lt_mul_of_pos_left (by omega) hP
    _ = 2 * (P * M0) := by ac_rfl

/-- Lower bound at a binade bottom, where the result is the floor (`z·M ≤ qm`): any distance below. -/
theorem low_floor (nb M P z qm M0 dn : Nat) (hX : z * M ≤ qm) (hq : nb * qm ≤ M0) :
    (nb * M) * (2 * (z * P) - dn) ≤ 2 * (P * M0) := by
  calc (nb * M) * (2 * (z * P) - dn) ≤ (nb * M) * (2 * (z * P)) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 2 * (P * (nb * (z * M))) := by ac_rfl
    _ ≤ 2 * (P * (nb * qm)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P (Nat.mul_le_mul_left nb hX))
    _ ≤ 2 * (P * M0) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)

/-- Upper bound (non-strict): `2·M0 ≤ nb·(y'·M)` from `2·qm ≤ y'·M` and `M0 ≤ nb·qm`. -/
theorem up_le (nb M P y' z qm M0 : Nat) (hy : y' = 2 * z + 1) (hX : 2 * qm ≤ y' * M) (hq : M0 ≤ nb * qm) :
    2 * (P * M0) ≤ (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  calc 2 * (P * M0) ≤ 2 * (P * (nb * qm)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)
    _ = P * (nb * (2 * qm)) := by ac_rfl
    _ ≤ P * (nb * (y' * M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = (nb * M) * (y' * P) := by ac_rfl

/-- ... strict from the core's strict inequality. -/
theorem up_lt_a (nb M P y' z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y' = 2 * z + 1)
    (hX : 2 * qm < y' * M) (hq : M0 ≤ nb * qm) : 2 * (P * M0) < (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  calc 2 * (P * M0) ≤ 2 * (P * (nb * qm)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left P hq)
    _ = P * (nb * (2 * qm)) := by ac_rfl
    _ < P * (nb * (y' * M)) := Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hX hnb) hP
    _ = (nb * M) * (y' * P) := by ac_rfl

/-- ... strict from the sticky bit: `M0 < nb·qm + nb` and `2·qm + 2 ≤ y'·M`. -/
theorem up_lt_b (nb M P y' z qm M0 : Nat) (hnb : 0 < nb) (hP : 0 < P) (hy : y' = 2 * z + 1)
    (hX : 2 * qm + 2 ≤ y' * M) (hq : M0 < nb * qm + nb) :
    2 * (P * M0) < (nb * M) * (2 * (z * P) + P) := by
  rw [two_zP_add z P y' hy]
  have e1 : nb * (2 * qm) = 2 * (nb * qm) := by ac_rfl
  have h1 : 2 * M0 < nb * (2 * qm + 2) := by
    calc 2 * M0 < 2 * (nb * qm + nb) := by omega
      _ = nb * (2 * qm + 2) := by rw [Nat.mul_add nb (2 * qm) 2, e1, Nat.mul_add 2 (nb * qm) nb]; omega
  calc 2 * (P * M0) = P * (2 * M0) := by ac_rfl
    _ < P * (nb * (2 * qm + 2)) := Nat.mul_lt_mul_of_pos_left h1 hP
    _ ≤ P * (nb * (y' * M)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    _ = (nb * M) * (y' * P) := by ac_rfl

end SvGolf.FdivParam

end RoundingBounds

/-! # Section `CertF`: The parametric rounding certificate (was `tasks/fdivp/CertF.lean`) -/

section CertF

/-!
# The parametric rounding certificate, for EVERY format (untrusted, kernel-checked)

The proof of the former 16-bit task (removed: binary16 is this task's instance `(5, 11)`) proved,
for binary16 only, that the roundTiesToEven quotient of two finite nonzero operands is the one
pattern a multiplication-and-comparison certificate accepts (`cert16_bridge` of its `Cert16.lean`).
This part proves the same theorem for an arbitrary
`f : Format` (`2 ≤ w`, `2 ≤ p`, the spec's own well-formedness; nothing else is assumed):

    theorem certF_bridge (f : Format) (a b c : BitVec f.k) (hb : ¬ isZeroF f b) :
        finQuotF f .roundTiesToEven a b = c ↔ certF f a b c = true

No enumeration, no `bv_decide`, no `native_decide`: the proof is symbolic in `w` and `p`
(and in the three bit patterns). It is `cert16_bridge` with every binary16 numeral replaced
by the format constant it came from, and the proof is the same proof:

| binary16 numeral | format constant                              |
|------------------|----------------------------------------------|
| 16               | `f.k = 1 + w + (p - 1)`                      |
| 31               | `2 ^ f.w - 1` (the all-ones exponent field)  |
| 1024, 10         | `2 ^ f.t`, `f.t = p - 1`                     |
| 15, 25 (`E - 25`)| `f.emax`, `f.emax + f.t`                     |
| 24               | `f.scale = emax + t - 1` (units are `2^-scale`) |
| 4095 · 2^28      | `(2^(p+1) - 1) · 2^(2·emax - 2)`             |

What is reused unchanged: `rne_eq_iff`, `rne_eq_iff_canon` (the interval characterization of
the roundTiesToEven magnitude, stated for every `Format`: section `RneInterval`),
`roundUnits_scale` (section `ScaleInvariance`), and from section `IEEE754Proofs`: `rne_overflow_iff`,
`normal_bounds`, `rep_dvd`, `fields_toNat`, `eq_fields`, `msb_eq_S`, `maxUnits_eq`, `emax_pos`.
What is new: the field accessors and the certificate with the format constants
(`expF`, `fracF`, `signF`, `sigF`, `qexpF`, `uF`, `dnF`, `certNF`, `certF`), the
format-general `claimF`, `fields_injF`, `finite_uF`, `uF_of_rep`, `certNF_iff`,
`roundUnits_reduceF`, and the special-case table `divide_table` (the former 16-bit task's binary16 table, for
every format and every rounding mode), whose finite/finite arm is `finQuotF`.

## Statement of the certificate

With `e = qexp a - qexp b + scale` the exact quotient in units of the least subnormal is
`N / D`, `N = sig a · 2^max(e,0)`, `D = sig b · 2^max(-e,0)`. The pattern `c` (sign `S`,
exponent field `E`, trailing field `T`) is accepted iff it has the XOR sign and

* `E = 2^w - 1` (the infinity pattern, `T = 0`) and `N ≥ D · (2^(p+1) - 1) · 2^(2·emax - 2)`
  (the overflow threshold `maxUnits + half the top spacing`, in units), or
* `E < 2^w - 1`, `N` below the threshold, and `N / D` within half a spacing of the magnitude
  `u = uF E T` of `c` on each side (the lower neighbour at distance `dn`, the upper at
  `2^(E-1)`), a boundary allowed only if `c`'s last bit `T % 2` is 0 (ties to even).

Both sides use only `+ - *`, comparisons, `2^_` and fixed constants: no division, no `log2`.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib
/-! ## Numeric facts about a format -/

theorem two_pow_t (f : Format) : 2 ^ f.p = 2 * 2 ^ f.t := by
  have := two_pow_pred f
  simp only [Format.t]; omega

theorem four_le_two_pow_w (f : Format) : 4 ≤ 2 ^ f.w := by
  have := f.hw
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ f.w := Nat.pow_le_pow_right (by omega) this

theorem two_pow_t_even (f : Format) : 2 ^ f.t % 2 = 0 := by
  have h1 : f.t = (f.t - 1) + 1 := by have := f.hp; simp only [Format.t]; omega
  rw [h1, Nat.pow_succ]; omega

/-! ## Fields of a pattern, with the format's constants -/

/-- The biased exponent field `E` (§3.4): the `w` bits above the trailing field. -/
def expF (f : Format) (x : BitVec f.k) : Nat := x.toNat / 2 ^ f.t % 2 ^ f.w

/-- The trailing significand field `T`: the low `t = p - 1` bits. -/
def fracF (f : Format) (x : BitVec f.k) : Nat := x.toNat % 2 ^ f.t

/-- The sign bit `S`: the bit above `E ‖ T`. -/
def signF (f : Format) (x : BitVec f.k) : Bool := x.toNat / 2 ^ (f.w + f.t) == 1

/-- `x` is a NaN: `E = 2^w - 1`, `T ≠ 0`. -/
def isNaNF (f : Format) (x : BitVec f.k) : Prop := expF f x = 2 ^ f.w - 1 ∧ fracF f x ≠ 0

/-- `x` is an infinity: `E = 2^w - 1`, `T = 0`. -/
def isInfF (f : Format) (x : BitVec f.k) : Prop := expF f x = 2 ^ f.w - 1 ∧ fracF f x = 0

/-- `x` is a zero: `E = 0`, `T = 0`. -/
def isZeroF (f : Format) (x : BitVec f.k) : Prop := expF f x = 0 ∧ fracF f x = 0

instance (f : Format) (x : BitVec f.k) : Decidable (isNaNF f x) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (x : BitVec f.k) : Decidable (isInfF f x) := inferInstanceAs (Decidable (_ ∧ _))
instance (f : Format) (x : BitVec f.k) : Decidable (isZeroF f x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The integral significand `c` of a finite pattern (§3.3, §3.4 (c), (d)): hidden bit `E ≠ 0`
above `T`. -/
def sigF (f : Format) (x : BitVec f.k) : Nat :=
  if expF f x = 0 then fracF f x else 2 ^ f.t + fracF f x

/-- The quantum exponent `q` of a finite pattern (§3.3): `E - emax - t` for a normal number,
`emin - t = 1 - emax - t` for a subnormal, i.e. `max(E, 1) - emax - t`. -/
def qexpF (f : Format) (x : BitVec f.k) : Int :=
  (if expF f x = 0 then (1 : Int) else (expF f x : Int)) - f.emax - f.t

/-- **The finite/finite case**: the `mode`-rounded quotient of two finite nonzero operands,
`|a| / |b| = (sig a · 2^qa) / (sig b · 2^qb)` as the fraction `(nx · dy) / (dx · ny)` with the
XOR sign (the last arm of `divide`, written over the fields). -/
def finQuotF (f : Format) (mode : RoundingMode) (a b : BitVec f.k) : BitVec f.k :=
  let nx := sigF f a * 2 ^ (qexpF f a).toNat
  let dx := 2 ^ (-qexpF f a).toNat
  let ny := sigF f b * 2 ^ (qexpF f b).toNat
  let dy := 2 ^ (-qexpF f b).toNat
  round f mode (signF f a ^^ signF f b) (nx * dy) (dx * ny)

/-! ## Decoding by fields, and the special-case table -/

/-- `decode` in terms of the fields (it is literally this; `rfl`). -/
theorem decodeF_eq (f : Format) (x : BitVec f.k) :
    decode f x =
      if expF f x = 2 ^ f.w - 1 then
        (if fracF f x = 0 then .inf (signF f x) else .nan (fracF f x < 2 ^ (f.t - 1)))
      else if expF f x = 0 then
        (if fracF f x = 0 then .zero (signF f x)
         else .finite (signF f x) (f.emin - f.t) (fracF f x))
      else .finite (signF f x) ((expF f x : Int) - f.emax - f.t) (2 ^ f.t + fracF f x) := rfl

/-- **`divide f mode` is the special-case table of a divider over the operands' fields**, with
the finite/finite case `finQuotF`, for every format, rounding mode and pair of patterns:

* a NaN operand, `∞ / ∞` or `0 / 0`: the canonical NaN;
* otherwise `∞ / y` or `x / 0`: the infinity with the XOR sign;
* otherwise `x / ∞` or `0 / y`: the zero with the XOR sign;
* otherwise both are finite and nonzero: `finQuotF`.

(The conditions are tested in this order, as in `divide` itself and in the reference
design's `always_comb`.) -/
theorem divide_table (f : Format) (mode : RoundingMode) (a b : BitVec f.k) :
    divide f mode a b =
      if isNaNF f a ∨ isNaNF f b ∨ (isInfF f a ∧ isInfF f b) ∨ (isZeroF f a ∧ isZeroF f b) then
        canonicalNaN f
      else if isInfF f a ∨ isZeroF f b then infinity f (signF f a ^^ signF f b)
      else if isInfF f b ∨ isZeroF f a then zero f (signF f a ^^ signF f b)
      else finQuotF f mode a b := by
  have hm : 2 ^ f.w - 1 ≠ 0 := by have := four_le_two_pow_w f; omega
  unfold divide
  rw [decodeF_eq f a, decodeF_eq f b]
  simp only [isNaNF, isInfF, isZeroF, finQuotF, sigF, qexpF, Format.emin]
  by_cases ha31 : expF f a = 2 ^ f.w - 1 <;> by_cases hb31 : expF f b = 2 ^ f.w - 1 <;>
    by_cases ha0 : expF f a = 0 <;> by_cases hb0 : expF f b = 0 <;>
    by_cases ta : fracF f a = 0 <;> by_cases tb : fracF f b = 0 <;>
    simp_all

/-! ## Fields as `BitVec` slices (what a circuit computes) -/

theorem signF_eq (f : Format) (x : BitVec f.k) : signF f x = x.msb := (msb_eq_S f x).symm

theorem eq_fieldsF (f : Format) (c : BitVec f.k) :
    c = fields f (signF f c) (expF f c) (fracF f c) := by
  have h := eq_fields f c
  rw [signF_eq]
  exact h

theorem expF_lt (f : Format) (x : BitVec f.k) : expF f x < 2 ^ f.w :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fracF_lt (f : Format) (x : BitVec f.k) : fracF f x < 2 ^ f.t :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-! ## Field injectivity -/

theorem fields_injF (f : Format) (s s' : Bool) (E E' T T' : Nat) (hE : E < 2 ^ f.w)
    (hE' : E' < 2 ^ f.w) (hT : T < 2 ^ f.t) (hT' : T' < 2 ^ f.t)
    (h : fields f s E T = fields f s' E' T') : s = s' ∧ E = E' ∧ T = T' := by
  have h1 := congrArg BitVec.toNat h
  rw [fields_toNat f s E T hE hT, fields_toNat f s' E' T' hE' hT'] at h1
  have hB := Nat.two_pow_pos f.t
  have hlow : ∀ E T : Nat, E < 2 ^ f.w → T < 2 ^ f.t → E * 2 ^ f.t + T < 2 ^ (f.w + f.t) := by
    intro E T hE hT
    rw [Nat.pow_add]
    have : (E + 1) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ hE
    rw [Nat.succ_mul] at this; omega
  have hX := hlow E T hE hT
  have hX' := hlow E' T' hE' hT'
  have key : E * 2 ^ f.t + T = E' * 2 ^ f.t + T' → E = E' ∧ T = T' := by
    intro hh
    have a1 : (T + E * 2 ^ f.t) % 2 ^ f.t = T := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT]
    have a2 : (T' + E' * 2 ^ f.t) % 2 ^ f.t = T' := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hT']
    have b1 : (T + E * 2 ^ f.t) / 2 ^ f.t = E := by
      rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT, Nat.zero_add]
    have b2 : (T' + E' * 2 ^ f.t) / 2 ^ f.t = E' := by
      rw [Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hT', Nat.zero_add]
    have hh' : T + E * 2 ^ f.t = T' + E' * 2 ^ f.t := by omega
    refine ⟨?_, ?_⟩
    · rw [← b1, ← b2, hh']
    · rw [← a1, ← a2, hh']
  generalize 2 ^ (f.w + f.t) = C at *
  cases s <;> cases s' <;> simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
  · have := key (by omega); exact ⟨trivial, this⟩
  · omega
  · omega
  · have := key (by omega); exact ⟨trivial, this⟩

/-! ## The magnitude a pattern denotes, in units -/

/-- The magnitude, in units of `2^-scale`, of a pattern with fields `E < 2^w - 1`, `T`:
`T` (subnormal) or `(2^t + T)·2^(E-1)`. -/
def uF (f : Format) (E T : Nat) : Nat := if E = 0 then T else (2 ^ f.t + T) * 2 ^ (E - 1)

/-- The distance (in units) from `uF E T` down to the previous representable magnitude. -/
def dnF (E T : Nat) : Nat := if 2 ≤ E ∧ T = 0 then 2 ^ (E - 1 - 1) else 2 ^ (E - 1)

theorem finite_uF (f : Format) (s : Bool) (E T : Nat) (hE : E < 2 ^ f.w - 1) (hT : T < 2 ^ f.t) :
    finite f s (uF f E T) = fields f s E T := by
  have ht : f.t = f.p - 1 := rfl
  have hB := Nat.two_pow_pos f.t
  unfold finite
  by_cases hE0 : E = 0
  · subst hE0
    have : uF f 0 T = T := by simp [uF]
    rw [this, if_pos hT]
  · have hu : uF f E T = (2 ^ f.t + T) * 2 ^ (E - 1) := by simp [uF, hE0]
    rw [hu]
    have hc0 : 2 ^ f.t + T ≠ 0 := by omega
    have hlog : (2 ^ f.t + T).log2 = f.t := by
      rw [Nat.log2_eq_iff hc0, Nat.pow_succ]; omega
    have hge : ¬ (2 ^ f.t + T) * 2 ^ (E - 1) < 2 ^ f.t := by
      have := Nat.le_mul_of_pos_right (2 ^ f.t + T) (Nat.two_pow_pos (E - 1)); omega
    rw [if_neg hge]
    simp only []
    rw [log2_mul_two_pow _ hc0, hlog, show f.t + (E - 1) - f.t = E - 1 by omega,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _), show E - 1 + 1 = E by omega,
      show 2 ^ f.t + T - 2 ^ f.t = T by omega]

/-- Every representable magnitude in the finite range is `uF E T` for a finite pattern. -/
theorem uF_of_rep (f : Format) (u : Nat) (hmax : u ≤ f.maxUnits) (hu : RepU f u) :
    ∃ E T, E < 2 ^ f.w - 1 ∧ T < 2 ^ f.t ∧ u = uF f E T := by
  have hw4 := four_le_two_pow_w f
  by_cases hlt : u < 2 ^ f.t
  · exact ⟨0, u, by omega, hlt, by simp [uF]⟩
  · have hu0 : u ≠ 0 := by have := Nat.two_pow_pos f.t; omega
    obtain ⟨hlo, hT, hj2⟩ := normal_bounds f u hmax (by omega)
    have hdvd := rep_dvd f u hu hu0
    generalize hj : Nat.log2 u - f.t = j at hlo hT hj2 hdvd
    refine ⟨j + 1, u / 2 ^ j - 2 ^ f.t, by omega, by omega, ?_⟩
    simp only [uF, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [show 2 ^ f.t + (u / 2 ^ j - 2 ^ f.t) = u / 2 ^ j by omega, Nat.div_mul_cancel hdvd]

/-! ## The interval characterization at a pattern's magnitude -/

/-- **The interval characterizes the roundTiesToEven magnitude, for every pattern magnitude**
`uF f E T` (`T < 2^t`; no threshold, no sign), in every format. -/
theorem claimF (f : Format) (s : Bool) (N D E T : Nat) (hD : 0 < D) (hT : T < 2 ^ f.t) :
    (uF f E T = roundUnits f .roundTiesToEven s N D) ↔
      ((uF f E T = 0 ∨ leB (decide (T % 2 = 0)) (D * (2 * uF f E T - dnF E T)) (2 * N)) ∧
        leB (decide (T % 2 = 0)) (2 * N) (D * (2 * uF f E T + 2 ^ (E - 1)))) := by
  have hp1 : 2 ^ (f.p - 1) = 2 ^ f.t := rfl
  have hp2 := two_pow_t f
  have hB := Nat.two_pow_pos f.t
  by_cases hE0 : E = 0
  · subst hE0
    by_cases hT0 : T = 0
    · subst hT0
      have hu : uF f 0 0 = 0 := rfl
      have hd : dnF 0 0 = 1 := rfl
      have h1 : (2 : Nat) ^ (0 - 1) = 1 := rfl
      have h2 : decide ((0 : Nat) % 2 = 0) = true := rfl
      rw [hu, hd, h1, h2]
      exact rne_eq_iff f s N D 0 1 1 true hD Nat.one_pos Nat.one_pos (zero_rep _)
        ⟨1, 0, by omega, rfl⟩ (fun h => absurd rfl h) (fun w _ => by omega)
        (fun h => absurd rfl h)
        ⟨fun _ => rfl, fun _ => by simp [EvenSig]⟩
    · have hu : uF f 0 T = T * 2 ^ 0 := by simp [uF]
      have hd : dnF 0 T = if T = 2 ^ (f.p - 1) ∧ 0 < 0 then 2 ^ (0 - 1) else 2 ^ 0 := by
        simp [dnF]
      exact rne_eq_iff_canon f s N D T 0 (uF f 0 T) (2 ^ (0 - 1)) (dnF 0 T)
        (decide (T % 2 = 0)) hD (by omega) (by omega) (fun h => absurd h (Nat.lt_irrefl 0)) hu
        rfl hd (by simp)
  · have hu : uF f E T = (2 ^ f.t + T) * 2 ^ (E - 1) := by simp [uF, hE0]
    have hd : dnF E T = if 2 ^ f.t + T = 2 ^ (f.p - 1) ∧ 0 < E - 1 then 2 ^ (E - 1 - 1)
        else 2 ^ (E - 1) := by
      rw [hp1]
      unfold dnF
      by_cases hb : 2 ≤ E ∧ T = 0
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb, if_neg (by omega)]
    exact rne_eq_iff_canon f s N D (2 ^ f.t + T) (E - 1) (uF f E T) (2 ^ (E - 1)) (dnF E T)
      (decide (T % 2 = 0)) hD (by omega) (by omega) (fun _ => by omega) hu rfl hd
      (by have := two_pow_t_even f; simp only [decide_eq_true_eq]; omega)

/-! ## The certificate -/

/-- `cert16 a b c` with the exact quotient `N / D` (in units) and the XOR sign `s` abstracted.
`(2^(p+1) - 1) · 2^(2·emax - 2)` is the overflow threshold in units (binary16: `4095 · 2^28`). -/
def certNF (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k) : Bool :=
  (signF f c == s) &&
    (if expF f c = 2 ^ f.w - 1 then
      fracF f c == 0 && decide (D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N)
     else decide (N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) &&
      (uF f (expF f c) (fracF f c) == 0 ||
        (if fracF f c % 2 == 0
          then decide (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) ≤ 2 * N)
          else decide (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) < 2 * N))) &&
      (if fracF f c % 2 == 0
        then decide (2 * N ≤ D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))
        else decide (2 * N < D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))))

/-- **The rounding certificate** of a finite nonzero quotient, in every format: `c` is the
roundTiesToEven quotient `a / b` iff `certF f a b c` (`certF_bridge`). With
`e = qexp a - qexp b + scale`, the exact quotient in units of the least subnormal is
`N / D`, `N = sig a · 2^max(e,0)`, `D = sig b · 2^max(-e,0)`. -/
def certF (f : Format) (a b c : BitVec f.k) : Bool :=
  let e : Int := qexpF f a - qexpF f b + f.scale
  certNF f (sigF f a * 2 ^ e.toNat) (sigF f b * 2 ^ (-e).toNat) (signF f a ^^ signF f b) c

/-- The certificate for `E = 2^w - 1`: the infinity pattern, at or above the threshold. -/
theorem certNF_inf (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k)
    (hE : expF f c = 2 ^ f.w - 1) :
    certNF f N D s c = true ↔
      (signF f c = s ∧ fracF f c = 0 ∧
        D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N) := by
  unfold certNF
  rw [if_pos hE]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- The certificate for `E ≠ 2^w - 1`: below the threshold and inside the pattern's interval. -/
theorem certNF_fin (f : Format) (N D : Nat) (s : Bool) (c : BitVec f.k)
    (hE : expF f c ≠ 2 ^ f.w - 1) :
    certNF f N D s c = true ↔
      (signF f c = s ∧ N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ∧
        (uF f (expF f c) (fracF f c) = 0 ∨
          leB (decide (fracF f c % 2 = 0))
            (D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c))) (2 * N)) ∧
        leB (decide (fracF f c % 2 = 0)) (2 * N)
          (D * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)))) := by
  unfold certNF
  rw [if_neg hE]
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, ite_decide_leB, decide_eq_true_eq,
    and_assoc]

/-! ## The bridge, in units -/

/-- The roundTiesToEven result of an exact positive quotient `N / D`, measured in units of
`2^-scale`, with sign `s`: the encoder applied to `roundUnits`, or the infinity on overflow.
This is `round f .roundTiesToEven s` after the unit scaling. -/
def unitsResultF (f : Format) (s : Bool) (N D : Nat) : BitVec f.k :=
  if roundUnits f .roundTiesToEven s N D ≤ f.maxUnits
  then finite f s (roundUnits f .roundTiesToEven s N D) else infinity f s

/-- The overflow threshold of the spec in units, in the certificate's form. -/
theorem thr_iff (f : Format) (N D : Nat) :
    D * (2 * f.maxUnits + 2 ^ (2 * f.emax - 1)) ≤ 2 * N ↔
      D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N := by
  have he := emax_pos f
  have hP := Nat.two_pow_pos f.p
  obtain ⟨J, hJ⟩ : ∃ J, 2 * f.emax - 2 = J := ⟨_, rfl⟩
  have e1 : 2 * f.emax - 1 = J + 1 := by omega
  obtain ⟨Q, hQ⟩ : ∃ Q, 2 ^ f.p = Q + 1 := ⟨2 ^ f.p - 1, by omega⟩
  have e2 : 2 ^ (f.p + 1) - 1 = 2 * Q + 1 := by rw [Nat.pow_succ]; omega
  have e3 : 2 ^ f.p - 1 = Q := by omega
  rw [maxUnits_eq, e1, hJ, e2, e3, Nat.pow_succ]
  have h : D * (2 * (Q * (2 ^ J * 2)) + 2 ^ J * 2) = 2 * (D * (2 * Q + 1) * 2 ^ J) := by grind
  rw [h]; omega

/-- **The certificate characterizes the rounded quotient**, for any exact quotient `N / D`,
in every format. -/
theorem certNF_iff (f : Format) (N D : Nat) (hD : 0 < D) (s : Bool) (c : BitVec f.k) :
    unitsResultF f s N D = c ↔ certNF f N D s c = true := by
  have hEl : expF f c < 2 ^ f.w := expF_lt f c
  have hTl : fracF f c < 2 ^ f.t := fracF_lt f c
  have hw4 := four_le_two_pow_w f
  have hc := eq_fieldsF f c
  have key : ∀ (s' : Bool) (E' T' : Nat), E' < 2 ^ f.w → T' < 2 ^ f.t →
      (fields f s' E' T' = c ↔
        s' = signF f c ∧ E' = expF f c ∧ T' = fracF f c) := by
    intro s' E' T' hE' hT'
    constructor
    · intro h
      exact fields_injF f s' (signF f c) E' (expF f c) T' (fracF f c) hE' hEl hT' hTl (h.trans hc)
    · rintro ⟨h1, h2, h3⟩
      rw [h1, h2, h3]
      exact hc.symm
  have hovf := rne_overflow_iff f s N D hD
  have hthr : f.maxUnits < roundUnits f .roundTiesToEven s N D ↔
      D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N := by
    rw [hovf]; exact thr_iff f N D
  have hrep := rne_rep f s N D
  unfold unitsResultF
  by_cases hth : D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) ≤ N
  · -- overflow: the result is the infinity
    have hgt := hthr.mpr hth
    rw [if_neg (Nat.not_le.mpr hgt)]
    have hinf : infinity f s = fields f s (2 ^ f.w - 1) 0 := rfl
    rw [hinf, key s (2 ^ f.w - 1) 0 (by omega) (Nat.two_pow_pos _)]
    by_cases hE31 : expF f c = 2 ^ f.w - 1
    · rw [certNF_inf f N D s c hE31]
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1.symm, h3.symm, hth⟩
      · rintro ⟨h1, h2, -⟩
        exact ⟨h1.symm, hE31.symm, h2.symm⟩
    · constructor
      · rintro ⟨-, h2, -⟩
        exact absurd h2.symm hE31
      · intro h
        have := ((certNF_fin f N D s c hE31).mp h).2.1
        omega
  · -- below the threshold: the result is the encoding of `roundUnits`
    have hle : roundUnits f .roundTiesToEven s N D ≤ f.maxUnits :=
      Nat.not_lt.mp fun h => hth (hthr.mp h)
    rw [if_pos hle]
    obtain ⟨E0, T0, hE0, hT0, hu0⟩ := uF_of_rep f _ hle hrep
    have hf : finite f s (roundUnits f .roundTiesToEven s N D) = fields f s E0 T0 := by
      rw [hu0]; exact finite_uF f s E0 T0 hE0 hT0
    rw [hf, key s E0 T0 (by omega) hT0]
    by_cases hE31 : expF f c = 2 ^ f.w - 1
    · constructor
      · rintro ⟨-, h2, -⟩
        omega
      · intro h
        exact absurd ((certNF_inf f N D s c hE31).mp h).2.2 hth
    · rw [certNF_fin f N D s c hE31]
      have hD' := claimF f s N D (expF f c) (fracF f c) hD hTl
      constructor
      · rintro ⟨h1, h2, h3⟩
        have hu : uF f (expF f c) (fracF f c) =
            roundUnits f .roundTiesToEven s N D := by
          rw [← h2, ← h3, ← hu0]
        exact ⟨h1.symm, by omega, hD'.mp hu⟩
      · rintro ⟨h1, -, h3⟩
        have hu := hD'.mpr h3
        have hfe : fields f s (expF f c) (fracF f c) = fields f s E0 T0 := by
          rw [← finite_uF f s (expF f c) (fracF f c) (by omega) hTl, hu, hf]
        obtain ⟨-, h2, h3'⟩ := fields_injF f s s _ _ _ _ hEl (by omega) hTl hT0 hfe
        exact ⟨h1.symm, h2.symm, h3'.symm⟩

/-! ## From operands to the exact quotient in units -/

/-- The operands' exponents cancel: `roundUnits` of `n·2^scale / d` is that of `N / D`, with
`N = sa · 2^max(e,0)`, `D = sb · 2^max(-e,0)`, `e = qa − qb + scale` (by `roundUnits_scale`). -/
theorem roundUnits_reduceF (f : Format) (mode : RoundingMode) (s : Bool) (sa sb : Nat)
    (qa qb : Int) :
    roundUnits f mode s
        ((sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale)
        (2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat)) =
      roundUnits f mode s (sa * 2 ^ (qa - qb + f.scale).toNat)
        (sb * 2 ^ (-(qa - qb + f.scale)).toNat) := by
  by_cases he : 0 ≤ qa - qb + f.scale
  · have h0 : (-(qa - qb + f.scale)).toNat = 0 := by omega
    rw [h0]
    have := roundUnits_scale f mode s (sa * 2 ^ (qa - qb + f.scale).toNat)
      (sb * 2 ^ 0) ((-qa).toNat + qb.toNat)
    have hN : (sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale =
        sa * 2 ^ (qa - qb + f.scale).toNat * 2 ^ ((-qa).toNat + qb.toNat) := by
      rw [mul_pow_mul_pow_mul_pow, mul_pow_mul_pow]; congr 2; omega
    have hD : 2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat) = sb * 2 ^ 0 * 2 ^ ((-qa).toNat + qb.toNat) := by
      rw [Nat.pow_zero, Nat.mul_one, Nat.pow_add]; ac_rfl
    rw [hN, hD]
    exact this
  · have h0 : (qa - qb + f.scale).toNat = 0 := by omega
    rw [h0]
    have := roundUnits_scale f mode s (sa * 2 ^ 0)
      (sb * 2 ^ (-(qa - qb + f.scale)).toNat) (qa.toNat + (-qb).toNat + f.scale)
    have hN : (sa * 2 ^ qa.toNat * 2 ^ (-qb).toNat) * 2 ^ f.scale =
        sa * 2 ^ 0 * 2 ^ (qa.toNat + (-qb).toNat + f.scale) := by
      rw [mul_pow_mul_pow_mul_pow, Nat.pow_zero, Nat.mul_one]
    have hD : 2 ^ (-qa).toNat * (sb * 2 ^ qb.toNat) =
        sb * 2 ^ (-(qa - qb + f.scale)).toNat * 2 ^ (qa.toNat + (-qb).toNat + f.scale) := by
      rw [mul_pow_mul_pow]
      have e : (-(qa - qb + f.scale)).toNat + (qa.toNat + (-qb).toNat + f.scale) =
          (-qa).toNat + qb.toNat := by
        omega
      rw [e, Nat.pow_add]; ac_rfl
    rw [hN, hD]
    exact this

/-- `finQuotF` under roundTiesToEven is the rounded quotient of the exact quotient in units. -/
theorem finQuotF_eq (f : Format) (a b : BitVec f.k) :
    finQuotF f .roundTiesToEven a b =
      unitsResultF f (signF f a ^^ signF f b)
        (sigF f a * 2 ^ (qexpF f a - qexpF f b + f.scale).toNat)
        (sigF f b * 2 ^ (-(qexpF f a - qexpF f b + f.scale)).toNat) := by
  unfold finQuotF SvGolf.IEEE754.round unitsResultF
  simp only []
  rw [roundUnits_reduceF]
  simp [overflowToInfinity]

/-- `sigF` is positive on a nonzero pattern. -/
theorem sigF_pos (f : Format) (b : BitVec f.k) (hb0 : ¬ isZeroF f b) : 0 < sigF f b := by
  have hB := Nat.two_pow_pos f.t
  unfold sigF
  unfold isZeroF at hb0
  by_cases h : expF f b = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **The certificate bridge, for every format** (`cert16_bridge` for all `Format`s): for
finite nonzero operands, `finQuotF a b` (hence, by `divide_table`, `divide f .roundTiesToEven a b`)
is exactly the pattern the certificate `certF` accepts. Only `b ≠ 0` is used (`D > 0`). -/
theorem certF_bridge (f : Format) (a b c : BitVec f.k) (hb0 : ¬ isZeroF f b) :
    finQuotF f .roundTiesToEven a b = c ↔ certF f a b c = true := by
  have hD : 0 < sigF f b * 2 ^ (-(qexpF f a - qexpF f b + f.scale)).toNat :=
    Nat.mul_pos (sigF_pos f b hb0) (Nat.two_pow_pos _)
  rw [finQuotF_eq]
  exact certNF_iff f _ _ hD _ c

end SvGolf.FdivParam

end CertF

/-! # Section `DpN`: Format-independent arithmetic of the datapath (was `tasks/fdivp/DpN.lean`) -/

section DpN

/-!
# Task `fdivp`: format-independent arithmetic of the parametric divider datapath (untrusted, kernel-checked)

WP-H3. Plain `Nat`/`Int` lemmas with NO format in sight (the format is instantiated in `DpM.lean`):

* `normIter_spec`: the linear one-bit normalizer (`P - 1` stages, each shifting left while the top bit is clear and
  counting the shifts down modulo `Z = 2^EW`) yields `m * 2^l` in `[2^T, 2^(T+1))`, by induction on the stage count
  (the former 16-bit task's proof enumerated the 2047 significands in the kernel);
* `core_t`, `core_f`: the guard/round/sticky decision `inc = rb & (st1 | qs[1])` of `qs = qm >> sh` is round to
  nearest even of `qm / 2^(sh+1)`, for EVERY shift amount (the former 16-bit task's proof split on the 13 shifts `sh <= 12`).
-/

namespace SvGolf.FdivParam

open LeanModels.Sv.Lib

/-! ## The one-bit normalizer -/

/-- One stage: while the top bit (weight `2^T`) is clear, shift left (`m` has `T + 1` bits) and decrement the exponent
register modulo `Z`. -/
def normStep (T Z : Nat) (s : Nat × Nat) : Nat × Nat :=
  if 2 ^ T ≤ s.1 then s else ((2 * s.1) % 2 ^ (T + 1), (s.2 + (Z - 1)) % Z)

/-- `k` stages. -/
def normIter (T Z : Nat) : Nat → Nat × Nat → Nat × Nat
  | 0, s => s
  | k + 1, s => normIter T Z k (normStep T Z s)

theorem normIter_fix (T Z n y : Nat) (h : 2 ^ T ≤ n) : ∀ k, normIter T Z k (n, y) = (n, y)
  | 0 => rfl
  | k + 1 => by
    have : normStep T Z (n, y) = (n, y) := by simp [normStep, h]
    simp only [normIter, this]
    exact normIter_fix T Z n y h k

/-- **The normalizer.** `0 < n < 2^(T+1)` and `k` stages with `2^T <= n * 2^k` (and `k < Z`): the result is `n * 2^l` for
some `l <= k`, normalized, with the register decremented `l` times modulo `Z` (`y' + l = y` or `y' + l = y + Z`). -/
theorem normIter_spec (T Z : Nat) : ∀ (k n y : Nat), 0 < n → n < 2 ^ (T + 1) → 2 ^ T ≤ n * 2 ^ k → y < Z →
    k < Z →
    ∃ l y', l ≤ k ∧ normIter T Z k (n, y) = (n * 2 ^ l, y') ∧ y' < Z ∧ (y' + l = y ∨ y' + l = y + Z) ∧
      2 ^ T ≤ n * 2 ^ l ∧ n * 2 ^ l < 2 ^ (T + 1)
  | 0, n, y, _, hn1, hk, hy, _ => by
    refine ⟨0, y, Nat.le_refl _, ?_, hy, Or.inl (by omega), by simpa using hk, by simpa using hn1⟩
    simp [normIter]
  | k + 1, n, y, hn0, hn1, hk, hy, hkZ => by
    by_cases h : 2 ^ T ≤ n
    · refine ⟨0, y, Nat.zero_le _, ?_, hy, Or.inl (by omega), by simpa using h, by simpa using hn1⟩
      rw [normIter_fix T Z n y h (k + 1)]
      simp
    · have hlt : n < 2 ^ T := Nat.lt_of_not_ge h
      have h2 : 2 * n < 2 ^ (T + 1) := by rw [Nat.pow_succ]; omega
      have hZ : 0 < Z := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
      have hy' : (y + (Z - 1)) % Z < Z := Nat.mod_lt _ hZ
      have hk' : 2 ^ T ≤ (2 * n) * 2 ^ k := by
        have e : 2 * n * 2 ^ k = n * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
        omega
      obtain ⟨l, y', hl, hr, hy1, hyl, h3, h4⟩ :=
        normIter_spec T Z k (2 * n) ((y + (Z - 1)) % Z) (by omega) h2 hk' hy' (by omega)
      have hd := add_sub_one_mod_of_lt Z y hy
      refine ⟨l + 1, y', by omega, ?_, hy1, ?_, ?_, ?_⟩
      · have e1 : normIter T Z (k + 1) (n, y) = normIter T Z k (2 * n, (y + (Z - 1)) % Z) := by
          simp only [normIter, normStep, if_neg h]
          rw [Nat.mod_eq_of_lt h2]
        have e2 : n * 2 ^ (l + 1) = 2 * n * 2 ^ l := by rw [Nat.pow_succ]; ac_rfl
        rw [e1, hr, e2]
      · by_cases h0 : y = 0
        · rw [if_pos h0] at hd; rw [hd] at hyl; omega
        · rw [if_neg h0] at hd; rw [hd] at hyl; omega
      · have e2 : n * 2 ^ (l + 1) = 2 * n * 2 ^ l := by rw [Nat.pow_succ]; ac_rfl
        rw [e2]; exact h3
      · have e2 : n * 2 ^ (l + 1) = 2 * n * 2 ^ l := by rw [Nat.pow_succ]; ac_rfl
        rw [e2]; exact h4

/-! ## The rounding core, for every shift amount -/

theorem mul2_le (S u v c : Nat) (h : c ≤ u) : c * (S * 2) ≤ 2 * (S * u + v) := by
  have h1 : c * (S * 2) ≤ u * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : u * (S * 2) = 2 * (S * u) := by ac_rfl
  omega

theorem mul2_lt (S u v c : Nat) (h : c < u ∨ (c = u ∧ 0 < v)) (hS : 0 < S) :
    c * (S * 2) < 2 * (S * u + v) := by
  rcases h with h | ⟨rfl, hv⟩
  · have h1 : (c + 1) * (S * 2) ≤ u * (S * 2) := Nat.mul_le_mul_right _ h
    have h2 : u * (S * 2) = 2 * (S * u) := by ac_rfl
    have h3 : (c + 1) * (S * 2) = c * (S * 2) + S * 2 := by rw [Nat.add_mul, Nat.one_mul]
    omega
  · have h2 : c * (S * 2) = 2 * (S * c) := by ac_rfl
    omega

theorem lt_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c) : 2 * (S * u + v) < c * (S * 2) := by
  have h1 : (u + 1) * (S * 2) ≤ c * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : (u + 1) * (S * 2) = 2 * (S * u) + S * 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    have : u * (S * 2) = 2 * (S * u) := by ac_rfl
    omega
  omega

theorem lt2_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c) : 2 * (S * u + v) + 2 ≤ c * (S * 2) := by
  have h1 : (u + 1) * (S * 2) ≤ c * (S * 2) := Nat.mul_le_mul_right _ h
  have h2 : (u + 1) * (S * 2) = 2 * (S * u) + S * 2 := by
    rw [Nat.add_mul, Nat.one_mul]
    have : u * (S * 2) = 2 * (S * u) := by ac_rfl
    omega
  omega

theorem le_mul2 (S u v c : Nat) (hv : v < S) (h : u + 1 ≤ c ∨ (c = u ∧ v = 0)) :
    2 * (S * u + v) ≤ c * (S * 2) := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact Nat.le_of_lt (lt_mul2 S u v c hv h)
  · have h2 : c * (S * 2) = 2 * (S * c) := by ac_rfl
    omega

/-- `st0 = true`: `inc = rb`, so `z = (qs + 1) / 2`; `z` is within half a spacing on both sides, strictly above
(the true value is strictly above `qm / 2^sh`). `M = 2^(sh+1)`. -/
theorem core_t (qm sh z : Nat) (hz : z = (qm / 2 ^ sh + 1) / 2) :
    (z = 0 ∨ (2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * 2 ^ (sh + 1) := by
  have hS : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hd := Nat.div_add_mod qm (2 ^ sh)
  have hv := Nat.mod_lt qm hS
  rw [Nat.pow_succ]
  generalize 2 ^ sh = S at *
  generalize qm / S = u at *
  generalize qm % S = v at *
  subst hd
  constructor
  · by_cases h0 : z = 0
    · exact Or.inl h0
    · exact Or.inr (mul2_le S u v (2 * z - 1) (by omega))
  · exact lt2_mul2 S u v (2 * z + 1) hv (by omega)

/-- `st0 = false`: `inc = rb ∧ (dropped bits nonzero ∨ qs[1])`; ties (the true value exactly half) round to even. -/
theorem core_f (qm sh z : Nat)
    (hz : ((qm / 2 ^ sh % 2 = 1 ∧ (qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2 + 1) ∨
          (¬ (qm / 2 ^ sh % 2 = 1 ∧ (qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)) ∧
            z = qm / 2 ^ sh / 2)) :
    (z = 0 ∨ ((2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm ∧ (z % 2 = 1 → (2 * z - 1) * 2 ^ (sh + 1) < 2 * qm))) ∧
    2 * qm ≤ (2 * z + 1) * 2 ^ (sh + 1) ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * 2 ^ (sh + 1)) := by
  have hS : 0 < 2 ^ sh := Nat.two_pow_pos sh
  have hd := Nat.div_add_mod qm (2 ^ sh)
  have hv := Nat.mod_lt qm hS
  rw [Nat.pow_succ]
  generalize 2 ^ sh = S at *
  generalize qm / S = u at *
  generalize qm % S = v at *
  subst hd
  have hz' : (u % 2 = 1 ∧ (v ≠ 0 ∨ u / 2 % 2 = 1) ∧ z = u / 2 + 1) ∨
      (¬ (u % 2 = 1 ∧ (v ≠ 0 ∨ u / 2 % 2 = 1)) ∧ z = u / 2) := by
    rcases hz with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · by_cases h0 : z = 0
    · exact Or.inl h0
    · refine Or.inr ⟨mul2_le S u v (2 * z - 1) ?_, fun hodd => mul2_lt S u v (2 * z - 1) ?_ hS⟩
      · omega
      · omega
  · apply le_mul2 S u v (2 * z + 1) hv
    omega
  · intro hodd
    exact lt_mul2 S u v (2 * z + 1) hv (by omega)

end SvGolf.FdivParam

end DpN

/-! # Section `DpM`: The certificate on the datapath's result (was `tasks/fdivp/DpM.lean`) -/

section DpM

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the certificate on the datapath's result, for every format (untrusted, kernel-checked)

WP-H3. `cert_fin_grid` / `cert_inf_grid` are the former 16-bit task's lemmas (its `DpCert.lean`) with the binary16 numerals
(`1024`, `2048`, `30`, `31`, `4095 * 2^28`) replaced by the format constants (`2^t`, `2 * 2^t`, `2^w - 2`, `2^w - 1`,
`(2^(p+1) - 1) * 2^(2 * emax - 2)`), stated against `certNF` of `CertF.lean`. `fin_cert_abs` and `ovf_cert_abs` assemble them
from the abstract quantities of a datapath (`qm`, `st0`, the shift `sh`, the grid exponent `j`, the grid mantissa `z`,
the packed magnitude `mag`): no design, no format-specific number, one rounding-core lemma for every shift.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib
/-! ## The exponent identity -/

/-- `N·S = D·T` for the datapath, `S = nb·2^(sh+1)`, `T = 2^j·M0`, `M0 = 2^(p+adj)·(ma·2^lza)`, `nb = mb·2^lzb`,
`e = xa - xb + scale` and `E = xa - lza - xb + lzb + emax - adj` the true result exponent; `j + 1 = E + sh`. -/
theorem scale_id' (ma mb lza lzb xa xb adj j sh emax T : Nat) (e E : Int)
    (he : e = (xa : Int) - xb + (emax + T - 1))
    (hE : E = (xa : Int) - lza - xb + lzb + emax - adj)
    (hjs : (j : Int) + 1 = E + sh) :
    (ma * 2 ^ e.toNat) * (mb * 2 ^ lzb * 2 ^ (sh + 1)) =
      (mb * 2 ^ (-e).toNat) * (2 ^ j * (2 ^ (T + 1 + adj) * (ma * 2 ^ lza))) := by
  have hp : e.toNat + lzb + (sh + 1) = (-e).toNat + j + (T + 1 + adj) + lza := by omega
  have l : (ma * 2 ^ e.toNat) * (mb * 2 ^ lzb * 2 ^ (sh + 1)) =
      ma * mb * 2 ^ (e.toNat + lzb + (sh + 1)) := by
    simp only [Nat.pow_add]
    generalize 2 ^ e.toNat = A; generalize 2 ^ lzb = B; generalize 2 ^ sh = C; generalize 2 ^ 1 = D
    ac_rfl
  have r : (mb * 2 ^ (-e).toNat) * (2 ^ j * (2 ^ (T + 1 + adj) * (ma * 2 ^ lza))) =
      ma * mb * 2 ^ ((-e).toNat + j + (T + 1 + adj) + lza) := by
    simp only [Nat.pow_add]
    generalize 2 ^ (-e).toNat = A; generalize 2 ^ j = B; generalize 2 ^ T = C; generalize 2 ^ 1 = D
    generalize 2 ^ adj = E'; generalize 2 ^ lza = F
    ac_rfl
  rw [l, r, hp]

/-! ## The fields of the packed result as a point of the grid -/

theorem fields_gridF (f : Format) (j z Ec Tc : Nat)
    (h : (Ec = 0 ∧ j = 0 ∧ z = Tc ∧ Tc < 2 ^ f.t) ∨
         (1 ≤ Ec ∧ j + 1 = Ec ∧ z = 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t) ∨
         (1 ≤ Ec ∧ j + 2 = Ec ∧ z = 2 * 2 ^ f.t ∧ Tc = 0)) :
    uF f Ec Tc = z * 2 ^ j ∧
    (dnF Ec Tc = 2 ^ j ∨ (dnF Ec Tc * 2 = 2 ^ j ∧ z = 2 ^ f.t ∧ 1 ≤ j)) ∧
    (2 ^ (Ec - 1) = 2 ^ j ∨ (2 ^ (Ec - 1) = 2 * 2 ^ j ∧ z = 2 * 2 ^ f.t)) ∧
    (Tc % 2 = 0 ↔ z % 2 = 0) := by
  have hev := two_pow_t_even f
  rcases h with ⟨hE, hj, hz, hT⟩ | ⟨hE1, hj, hz, hT⟩ | ⟨hE1, hj, hz, hT⟩
  · subst hE hj hz
    refine ⟨?_, Or.inl ?_, Or.inl ?_, Iff.rfl⟩
    · simp [uF]
    · simp [dnF]
    · simp
  · have hj' : j = Ec - 1 := by omega
    subst hj'
    have hu : uF f Ec Tc = z * 2 ^ (Ec - 1) := by
      unfold uF
      rw [if_neg (show ¬ (Ec = 0) by omega), hz]
    refine ⟨hu, ?_, Or.inl rfl, by omega⟩
    by_cases hd : 2 ≤ Ec ∧ Tc = 0
    · right
      unfold dnF
      rw [if_pos hd]
      obtain ⟨k, hk⟩ : ∃ k, Ec - 1 = k + 1 := ⟨Ec - 2, by omega⟩
      have : Ec - 1 - 1 = k := by omega
      rw [this, hk, Nat.pow_succ]
      exact ⟨rfl, by omega, by omega⟩
    · left
      unfold dnF
      rw [if_neg hd]
  · have hj' : Ec = j + 2 := by omega
    subst hj' hT hz
    have h1 : j + 2 - 1 = j + 1 := by omega
    refine ⟨?_, Or.inl ?_, Or.inr ⟨?_, rfl⟩, by omega⟩
    · unfold uF
      rw [if_neg (show ¬ (j + 2 = 0) by omega), h1, Nat.pow_succ]
      rw [Nat.add_zero, Nat.mul_comm (2 ^ j) 2, ← Nat.mul_assoc, Nat.mul_comm (2 ^ f.t) 2]
    · unfold dnF
      rw [if_pos (show 2 ≤ j + 2 ∧ (0 : Nat) = 0 by omega)]
      have : j + 2 - 1 - 1 = j := by omega
      rw [this]
    · rw [h1, Nat.pow_succ, Nat.mul_comm]

/-! ## Thresholds and the grid certificate -/

theorem c0_of (nb M P qm M0 Th : Nat) (hnb : 0 < nb) (hP : 0 < P) (hq : M0 < nb * qm + nb)
    (hb : P * (qm + 1) ≤ M * Th) : P * M0 < (nb * M) * Th := by
  have h1 : M0 < nb * (qm + 1) := by rw [Nat.mul_add]; omega
  calc P * M0 < P * (nb * (qm + 1)) := Nat.mul_lt_mul_of_pos_left h1 hP
    _ = nb * (P * (qm + 1)) := by ac_rfl
    _ ≤ nb * (M * Th) := Nat.mul_le_mul_left _ hb
    _ = (nb * M) * Th := by ac_rfl

/-- **The certificate for a finite pattern on the grid.** `c` has fields `(Ec, Tc)` in one of three shapes (subnormal,
normal, normal after the carry), `u = z·2^j`; `N·(nb·M) = D·(2^j·M0)`; `qm` is the quotient of `M0` by `nb`, `st0` its
inexactness; the rounding core relates `z`, `qm`, `M`. -/
theorem cert_fin_grid (f : Format) (N D nb M qm M0 z j : Nat) (st0 : Prop) (c : BitVec f.k) (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb) (hM : 0 < M)
    (hrel : N * (nb * M) = D * (2 ^ j * M0))
    (hq1 : nb * qm ≤ M0) (hq2 : M0 < nb * qm + nb)
    (hst1 : st0 → nb * qm < M0) (hst2 : ¬ st0 → M0 = nb * qm)
    (hcT : st0 → ((z = 0 ∨ (2 * z - 1) * M ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * M))
    (hcF : ¬ st0 → ((z = 0 ∨ ((2 * z - 1) * M ≤ 2 * qm ∧ (z % 2 = 1 → (2 * z - 1) * M < 2 * qm))) ∧
                    2 * qm ≤ (2 * z + 1) * M ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * M)))
    (hfloor : z = 2 ^ f.t → 1 ≤ j → z * M ≤ qm)
    (hsign : signF f c = s) (hE : expF f c ≠ 2 ^ f.w - 1)
    (hshape : (expF f c = 0 ∧ j = 0 ∧ z = fracF f c ∧ fracF f c < 2 ^ f.t) ∨
         (1 ≤ expF f c ∧ j + 1 = expF f c ∧ z = 2 ^ f.t + fracF f c ∧ fracF f c < 2 ^ f.t) ∨
         (1 ≤ expF f c ∧ j + 2 = expF f c ∧ z = 2 * 2 ^ f.t ∧ fracF f c = 0))
    (hC0 : N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) :
    certNF f N D s c = true := by
  have hPpos : 0 < 2 ^ j := Nat.two_pow_pos _
  have hSpos : 0 < nb * M := Nat.mul_pos hnb hM
  obtain ⟨hu, hdn, hup, hpar⟩ := fields_gridF f j z (expF f c) (fracF f c) hshape
  have hrel2 : (2 * N) * (nb * M) = D * (2 * (2 ^ j * M0)) := by
    calc (2 * N) * (nb * M) = 2 * (N * (nb * M)) := by ac_rfl
      _ = 2 * (D * (2 ^ j * M0)) := by rw [hrel]
      _ = D * (2 * (2 ^ j * M0)) := by ac_rfl
  rw [certNF_fin f N D s c hE]
  refine ⟨hsign, hC0, ?_, ?_⟩
  · -- the lower bound
    by_cases hz0 : z = 0
    · left; rw [hu, hz0]; simp
    · right
      have hy : (2 * z - 1) + 1 = 2 * z := by omega
      have hle : D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) ≤ 2 * N := by
        rw [scale_le D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2, hu]
        rcases hdn with hdn | ⟨hdn, hz1024, hj1⟩
        · rw [hdn]
          by_cases hs : st0
          · exact low_std nb M (2 ^ j) (2 * z - 1) z qm M0 hy ((hcT hs).1.resolve_left hz0) hq1
          · exact low_std nb M (2 ^ j) (2 * z - 1) z qm M0 hy (((hcF hs).1.resolve_left hz0).1) hq1
        · exact low_floor nb M (2 ^ j) z qm M0 _ (hfloor hz1024 hj1) hq1
      have hlt : z % 2 = 1 →
          D * (2 * uF f (expF f c) (fracF f c) - dnF (expF f c) (fracF f c)) < 2 * N := by
        intro hodd
        rw [scale_lt D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2, hu]
        have hdn' : dnF (expF f c) (fracF f c) = 2 ^ j := by
          rcases hdn with hdn | ⟨-, hz1024, -⟩
          · exact hdn
          · have := two_pow_t_even f
            omega
        rw [hdn']
        by_cases hs : st0
        · exact low_std_lt_b nb M (2 ^ j) (2 * z - 1) z qm M0 hPpos hy ((hcT hs).1.resolve_left hz0) (hst1 hs)
        · exact low_std_lt_a nb M (2 ^ j) (2 * z - 1) z qm M0 hnb hPpos hy
            (((hcF hs).1.resolve_left hz0).2 hodd) hq1
      by_cases hev : fracF f c % 2 = 0
      · rw [leB_of_eq (decide_eq_true hev)]; exact hle
      · rw [leB_of_ne (fun h => hev (of_decide_eq_true h))]
        exact hlt (by omega)
  · -- the upper bound
    have mono : ∀ upv : Nat, (upv = 2 ^ j ∨ upv = 2 * 2 ^ j) →
        (nb * M) * (2 * (z * 2 ^ j) + 2 ^ j) ≤ (nb * M) * (2 * (z * 2 ^ j) + upv) := by
      intro upv h
      apply Nat.mul_le_mul_left
      rcases h with h | h <;> omega
    have hupv : 2 ^ (expF f c - 1) = 2 ^ j ∨ 2 ^ (expF f c - 1) = 2 * 2 ^ j := by
      rcases hup with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    have hle : 2 * (2 ^ j * M0) ≤
        (nb * M) * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)) := by
      rw [hu]
      have hbase : 2 * (2 ^ j * M0) ≤ (nb * M) * (2 * (z * 2 ^ j) + 2 ^ j) := by
        by_cases hs : st0
        · exact Nat.le_of_lt (up_lt_b nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl (hcT hs).2 hq2)
        · exact up_le nb M (2 ^ j) (2 * z + 1) z qm M0 rfl (hcF hs).2.1 (Nat.le_of_eq (hst2 hs))
      exact Nat.le_trans hbase (mono _ hupv)
    have hlt : z % 2 = 1 → 2 * (2 ^ j * M0) <
        (nb * M) * (2 * uF f (expF f c) (fracF f c) + 2 ^ (expF f c - 1)) := by
      intro hodd
      rw [hu]
      have hup1 : 2 ^ (expF f c - 1) = 2 ^ j := by
        rcases hup with h | ⟨-, hz2048⟩
        · exact h
        · have := two_pow_t_even f
          omega
      rw [hup1]
      by_cases hs : st0
      · exact up_lt_b nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl (hcT hs).2 hq2
      · exact up_lt_a nb M (2 ^ j) (2 * z + 1) z qm M0 hnb hPpos rfl ((hcF hs).2.2 hodd)
          (Nat.le_of_eq (hst2 hs))
    by_cases hev : fracF f c % 2 = 0
    · rw [leB_of_eq (decide_eq_true hev),
        scale_ge D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2]
      exact hle
    · rw [leB_of_ne (fun h => hev (of_decide_eq_true h)),
        scale_gt D (nb * M) (2 * N) (2 * (2 ^ j * M0)) _ hD hSpos hrel2]
      exact hlt (by omega)

/-- **The certificate for the infinity pattern**, at or above the threshold. -/
theorem cert_inf_grid (f : Format) (N D nb M M0 j : Nat) (c : BitVec f.k) (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb) (hM : 0 < M)
    (hrel : N * (nb * M) = D * (2 ^ j * M0))
    (hE : expF f c = 2 ^ f.w - 1) (hT : fracF f c = 0) (hsign : signF f c = s)
    (hge : nb * M * ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) ≤ 2 ^ j * M0) :
    certNF f N D s c = true := by
  rw [certNF_inf f N D s c hE]
  refine ⟨hsign, hT, ?_⟩
  have h := (scale_le D (nb * M) N (2 ^ j * M0) ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) hD
    (Nat.mul_pos hnb hM) hrel).2 hge
  calc D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)
      = D * ((2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2)) := Nat.mul_assoc _ _ _
    _ ≤ N := h

/-! ## The fields of a packed pattern -/

theorem fields_fields (f : Format) (s : Bool) (E T : Nat) (hE : E < 2 ^ f.w) (hT : T < 2 ^ f.t) :
    signF f (fields f s E T) = s ∧ expF f (fields f s E T) = E ∧ fracF f (fields f s E T) = T := by
  have h := fields_injF f s (signF f (fields f s E T)) E (expF f (fields f s E T)) T
    (fracF f (fields f s E T)) hE (expF_lt f _) hT (fracF_lt f _)
    (eq_fieldsF f (fields f s E T))
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-! ## Format constants -/

theorem two_pow_w_emax (f : Format) : 2 ^ f.w = 2 * f.emax + 2 := by
  have hw := f.hw
  obtain ⟨k, hk⟩ : ∃ k, f.w = k + 1 := ⟨f.w - 1, by omega⟩
  have e1 : f.w - 1 = k := by omega
  have h2 : 2 ^ (f.w - 1) = 2 ^ k := by rw [e1]
  have hpos := Nat.two_pow_pos k
  have : f.emax = 2 ^ k - 1 := by simp only [Format.emax, e1]
  rw [hk, Nat.pow_succ, this]
  omega

theorem two_pow_p1 (f : Format) : 2 ^ (f.p + 1) = 4 * 2 ^ f.t := by
  have hp := f.hp
  have e : f.p + 1 = f.t + 2 := by simp only [Format.t]; omega
  rw [e, Nat.pow_add]
  omega

/-! ## The datapath's result is accepted by the certificate -/

/-- The below-threshold inequality `P·(qm+1) ≤ M·Th` with `Th = (A-1)·Q` in the three regimes of the datapath. -/
theorem thr_bound (A Q P qm M : Nat) (hQ : 0 < Q) (hA : 8 ≤ A)
    (h : (M = 2 ∧ P ≤ Q ∧ qm + 1 ≤ A) ∨ (M = 2 ∧ P = 2 * Q ∧ qm + 1 ≤ A - 1) ∨
      (4 ≤ M ∧ P = 1 ∧ qm + 1 ≤ A)) :
    P * (qm + 1) ≤ M * ((A - 1) * Q) := by
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, rfl, h2⟩ | ⟨h1, rfl, h2⟩
  · calc P * (qm + 1) ≤ Q * A := Nat.mul_le_mul h1 h2
      _ = A * Q := Nat.mul_comm _ _
      _ ≤ (2 * (A - 1)) * Q := Nat.mul_le_mul_right Q (by omega)
      _ = 2 * ((A - 1) * Q) := Nat.mul_assoc _ _ _
  · calc 2 * Q * (qm + 1) ≤ 2 * Q * (A - 1) := Nat.mul_le_mul_left _ h2
      _ = 2 * ((A - 1) * Q) := by ac_rfl
  · have h3 : A - 1 ≤ (A - 1) * Q := Nat.le_mul_of_pos_right _ hQ
    have h4 : 4 * ((A - 1) * Q) ≤ M * ((A - 1) * Q) := Nat.mul_le_mul_right _ h1
    omega

/-- **The finite, not overflowing case.** Abstract datapath: `qm ∈ [2^p, 2^(p+1))` is the quotient of `M0` by `nb` with
sticky `st0`; the shift is `sh`, `qs = qm / 2^sh`, `inc` the round-to-nearest-even increment, `z = qs / 2 + inc`; the
packed magnitude is `mag = j · 2^t + z`, with `j` the grid exponent: in the normal regime (`sh = 0`) `z ∈ [2^t, 2^(t+1)]`,
`j + 3 ≤ 2^w`, and a carry (`z = 2^(t+1)`) happens exactly for `qm = 2^(p+1) - 1`; in the subnormal regime `j = 0`,
`sh ≥ 1`, `z ≤ 2^t`. -/
theorem fin_cert_abs (f : Format) (N D nb M0 qm sh j z mag : Nat) (st0 inc : Prop) [Decidable inc] (s : Bool)
    (hD : 0 < D) (hnb : 0 < nb)
    (hrel : N * (nb * 2 ^ (sh + 1)) = D * (2 ^ j * M0))
    (hq1 : nb * qm ≤ M0) (hq2 : M0 < nb * qm + nb)
    (hst1 : st0 → nb * qm < M0) (hst2 : ¬ st0 → M0 = nb * qm)
    (hqm1 : 2 * 2 ^ f.t ≤ qm) (hqm2 : qm < 4 * 2 ^ f.t)
    (hinc : inc ↔ (qm / 2 ^ sh % 2 = 1 ∧ (st0 ∨ qm % 2 ^ sh ≠ 0 ∨ qm / 2 ^ sh / 2 % 2 = 1)))
    (hz : z = qm / 2 ^ sh / 2 + (if inc then 1 else 0))
    (hmag : mag = j * 2 ^ f.t + z)
    (hreg : (sh = 0 ∧ 2 ^ f.t ≤ z ∧ z ≤ 2 * 2 ^ f.t ∧ j + 3 ≤ 2 ^ f.w ∧
              (z = 2 * 2 ^ f.t ↔ qm = 4 * 2 ^ f.t - 1)) ∨
            (j = 0 ∧ 1 ≤ sh ∧ z ≤ 2 ^ f.t)) :
    certNF f N D s (fields f s (mag / 2 ^ f.t) (mag % 2 ^ f.t)) = true := by
  have hMt : 0 < 2 ^ f.t := Nat.two_pow_pos _
  have hev := two_pow_t_even f
  have hw2 := two_pow_w_emax f
  have hw4 := four_le_two_pow_w f
  have hp1 := two_pow_p1 f
  have hemax := emax_pos f
  have hMpos : 0 < 2 ^ (sh + 1) := Nat.two_pow_pos _
  have hMt2 : 2 ≤ 2 ^ f.t := by omega
  -- the field bounds
  have hmag_lt : mag < 2 ^ f.w * 2 ^ f.t := by
    rcases hreg with ⟨-, h1, h2, h3, -⟩ | ⟨h0, -, h2⟩
    · have : (j + 3) * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ h3
      rw [Nat.add_mul] at this
      omega
    · subst h0
      have : 2 * 2 ^ f.t ≤ 2 ^ f.w * 2 ^ f.t := Nat.mul_le_mul_right _ (by omega)
      omega
  -- the fields (Ec, Tc) of mag
  obtain ⟨Ec, Tc, hmagE, hTc, hshape'⟩ : ∃ Ec Tc : Nat, mag = Ec * 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t ∧
      ((Ec = 0 ∧ j = 0 ∧ z = Tc ∧ Tc < 2 ^ f.t) ∨
       (1 ≤ Ec ∧ j + 1 = Ec ∧ z = 2 ^ f.t + Tc ∧ Tc < 2 ^ f.t) ∨
       (1 ≤ Ec ∧ j + 2 = Ec ∧ z = 2 * 2 ^ f.t ∧ Tc = 0)) := by
    rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
    · by_cases hz2 : z = 2 * 2 ^ f.t
      · refine ⟨j + 2, 0, ?_, hMt, Or.inr (Or.inr ⟨by omega, rfl, hz2, rfl⟩)⟩
        rw [hmag, hz2, Nat.add_mul]; omega
      · refine ⟨j + 1, z - 2 ^ f.t, ?_, by omega, Or.inr (Or.inl ⟨by omega, rfl, by omega, by omega⟩)⟩
        rw [hmag, Nat.add_mul, Nat.one_mul]; omega
    · by_cases hzM : z = 2 ^ f.t
      · refine ⟨1, 0, ?_, hMt, Or.inr (Or.inl ⟨Nat.le_refl _, by omega, by omega, hMt⟩)⟩
        rw [hmag, h0, hzM]; omega
      · refine ⟨0, z, ?_, by omega, Or.inl ⟨rfl, h0, rfl, by omega⟩⟩
        rw [hmag, h0]
  have hEc : Ec < 2 ^ f.w := by
    have h1 : Ec * 2 ^ f.t < 2 ^ f.w * 2 ^ f.t := by omega
    exact Nat.lt_of_mul_lt_mul_right h1
  obtain ⟨hd1, hd2⟩ := (Nat.div_mod_unique (a := mag) (d := Ec) hMt).mpr
    ⟨by rw [hmagE, Nat.mul_comm Ec, Nat.add_comm Tc], hTc⟩
  rw [hd1, hd2]
  obtain ⟨hsg, hex, hfr⟩ := fields_fields f s Ec Tc hEc hTc
  -- the rounding core
  have hcT : st0 → ((z = 0 ∨ (2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm) ∧ 2 * qm + 2 ≤ (2 * z + 1) * 2 ^ (sh + 1)) := by
    intro hs
    apply core_t qm sh z
    rw [hz]
    by_cases hi : inc
    · have h1 := (hinc.1 hi).1
      rw [if_pos hi]; omega
    · rw [if_neg hi]
      have : ¬ (qm / 2 ^ sh % 2 = 1) := fun h1 => hi (hinc.2 ⟨h1, Or.inl hs⟩)
      omega
  have hcF : ¬ st0 → ((z = 0 ∨ ((2 * z - 1) * 2 ^ (sh + 1) ≤ 2 * qm ∧
        (z % 2 = 1 → (2 * z - 1) * 2 ^ (sh + 1) < 2 * qm))) ∧
      2 * qm ≤ (2 * z + 1) * 2 ^ (sh + 1) ∧ (z % 2 = 1 → 2 * qm < (2 * z + 1) * 2 ^ (sh + 1))) := by
    intro hs
    apply core_f qm sh z
    by_cases hi : inc
    · left
      refine ⟨?_, by rw [hz, if_pos hi]⟩
      have := hinc.1 hi
      refine ⟨this.1, ?_⟩
      rcases this.2 with h | h
      · exact absurd h hs
      · exact h
    · right
      refine ⟨fun h => hi (hinc.2 ?_), by rw [hz, if_neg hi, Nat.add_zero]⟩
      rcases h with ⟨h1, h2⟩
      exact ⟨h1, Or.inr h2⟩
  have hQ : 0 < 2 ^ (2 * f.emax - 2) := Nat.two_pow_pos _
  by_cases hcarry : j + 3 = 2 ^ f.w ∧ z = 2 * 2 ^ f.t ∧ sh = 0
  · -- the carry out of the largest finite number: infinity
    obtain ⟨hj, hz2, hsh0⟩ := hcarry
    have hqm : qm = 4 * 2 ^ f.t - 1 := by
      rcases hreg with ⟨-, -, -, -, h5⟩ | ⟨-, h1, -⟩
      · exact h5.1 hz2
      · omega
    have hE31 : Ec = 2 ^ f.w - 1 ∧ Tc = 0 := by
      rcases hshape' with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩ <;> omega
    refine cert_inf_grid f N D nb (2 ^ (sh + 1)) M0 j _ s hD hnb hMpos hrel
      (by rw [hex]; exact hE31.1) (by rw [hfr]; exact hE31.2) hsg ?_
    have hjE : j = (2 * f.emax - 2) + 1 := by omega
    have h2j : 2 ^ j = 2 * 2 ^ (2 * f.emax - 2) := by rw [hjE, Nat.pow_succ]; ac_rfl
    rw [hsh0, h2j, hp1]
    simp only [Nat.zero_add, Nat.pow_one]
    rw [hqm] at hq1
    have := Nat.mul_le_mul_left (2 * 2 ^ (2 * f.emax - 2)) hq1
    calc nb * 2 * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2))
        = 2 * 2 ^ (2 * f.emax - 2) * (nb * (4 * 2 ^ f.t - 1)) := by ac_rfl
      _ ≤ 2 * 2 ^ (2 * f.emax - 2) * M0 := this
  · -- a finite pattern on the grid
    have hE : Ec ≠ 2 ^ f.w - 1 := by
      rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩ <;>
      rcases hshape' with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ <;> omega
    have hC0 : N < D * (2 ^ (f.p + 1) - 1) * 2 ^ (2 * f.emax - 2) := by
      have hb : 2 ^ j * (qm + 1) ≤ 2 ^ (sh + 1) * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) := by
        apply thr_bound (4 * 2 ^ f.t) (2 ^ (2 * f.emax - 2)) (2 ^ j) qm (2 ^ (sh + 1)) hQ (by omega)
        rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
        · subst hsh
          by_cases hjl : j ≤ 2 * f.emax - 2
          · left
            exact ⟨by simp, Nat.pow_le_pow_right (by omega) hjl, by omega⟩
          · right; left
            have hjE : j = (2 * f.emax - 2) + 1 := by omega
            have hz2 : z ≠ 2 * 2 ^ f.t := fun hz2 => hcarry ⟨by omega, hz2, rfl⟩
            have hq3 : qm ≠ 4 * 2 ^ f.t - 1 := fun hq => hz2 (h5.2 hq)
            refine ⟨by simp, ?_, by omega⟩
            rw [hjE, Nat.pow_succ]; ac_rfl
        · right; right
          subst h0
          refine ⟨?_, by simp, by omega⟩
          have : 2 ^ 2 ≤ 2 ^ (sh + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
      have hc0 := c0_of nb (2 ^ (sh + 1)) (2 ^ j) qm M0 ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) hnb
        (Nat.two_pow_pos _) hq2 hb
      have := (scale_gt D (nb * 2 ^ (sh + 1)) N (2 ^ j * M0)
        ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) hD (Nat.mul_pos hnb hMpos) hrel).2 hc0
      rw [hp1]
      calc N < D * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2)) := this
        _ = D * (4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2) := (Nat.mul_assoc _ _ _).symm
    have hfloor : z = 2 ^ f.t → 1 ≤ j → z * 2 ^ (sh + 1) ≤ qm := by
      intro hzM hj1
      rcases hreg with ⟨hsh, h1, h2, h3, h5⟩ | ⟨h0, hs1, h2⟩
      · subst hsh
        rw [hzM]
        simp only [Nat.zero_add, Nat.pow_one]
        omega
      · omega
    exact cert_fin_grid f N D nb (2 ^ (sh + 1)) qm M0 z j st0 _ s hD hnb hMpos hrel hq1 hq2 hst1 hst2 hcT hcF
      hfloor hsg (by rw [hex]; exact hE) (by rw [hex, hfr]; exact hshape') hC0

/-- **Overflow**: `E >= 2^w - 1` (so `sh = 0`, `j = E - 1 >= 2^w - 2`): the infinity pattern is at or above the threshold. -/
theorem ovf_cert_abs (f : Format) (N D nb M0 qm j : Nat) (s : Bool) (hD : 0 < D) (hnb : 0 < nb)
    (hrel : N * (nb * 2 ^ (0 + 1)) = D * (2 ^ j * M0)) (hq1 : nb * qm ≤ M0)
    (hqm1 : 2 * 2 ^ f.t ≤ qm) (hj : 2 ^ f.w ≤ j + 2) :
    certNF f N D s (infinity f s) = true := by
  have hw2 := two_pow_w_emax f
  have hw4 := four_le_two_pow_w f
  have hp1 := two_pow_p1 f
  have hemax := emax_pos f
  have hMt := Nat.two_pow_pos f.t
  obtain ⟨hsg, hex, hfr⟩ := fields_fields f s (2 ^ f.w - 1) 0 (by omega) hMt
  refine cert_inf_grid f N D nb (2 ^ (0 + 1)) M0 j (infinity f s) s hD hnb (Nat.two_pow_pos _) hrel hex hfr hsg ?_
  have h4 : 2 ^ (2 * f.emax) = 4 * 2 ^ (2 * f.emax - 2) := by
    have e : 2 * f.emax = (2 * f.emax - 2) + 2 := by omega
    have h4' : 2 ^ ((2 * f.emax - 2) + 2) = 4 * 2 ^ (2 * f.emax - 2) := by
      rw [Nat.pow_add]; omega
    rw [← e] at h4'
    exact h4'
  have h2j : 4 * 2 ^ (2 * f.emax - 2) ≤ 2 ^ j := by
    rw [← h4]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hM0 : nb * (2 * 2 ^ f.t) ≤ M0 := Nat.le_trans (Nat.mul_le_mul_left nb hqm1) hq1
  have h5 := Nat.mul_le_mul h2j hM0
  rw [hp1]
  simp only [Nat.zero_add, Nat.pow_one]
  calc nb * 2 * ((4 * 2 ^ f.t - 1) * 2 ^ (2 * f.emax - 2))
      ≤ nb * 2 * ((4 * 2 ^ f.t) * 2 ^ (2 * f.emax - 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    _ = 4 * 2 ^ (2 * f.emax - 2) * (nb * (2 * 2 ^ f.t)) := by ac_rfl
    _ ≤ 2 ^ j * M0 := h5

end SvGolf.FdivParam

end DpM

/-! # Section `DpQ`: The datapath as a `Nat` model (was `tasks/fdivp/DpQ.lean`) -/

section DpQ

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the parametric datapath as a `Nat` model, and the facts about it (untrusted, kernel-checked)

WP-H3. The reference datapath `fdivp3.sv` (D3: linear one-bit normalizer, `P + 2` restoring steps, a two's complement
exponent `E`, `qs = qm >> dsh` for any shift, round to nearest even into the exponent field) on `Nat`, signal by
signal, for ANY format `f`. `a`, `b` are the operands as numbers (`BitVec.toNat`). The facts: the normalizer, the
quotient/sticky, the exponent decode (sign, `nrm`, `ovf`, `dsh`), the packed magnitude.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib
/-! ## The model -/

def eF (f : Format) (x : Nat) : Nat := x / 2 ^ f.t % 2 ^ f.w
def fF (f : Format) (x : Nat) : Nat := x % 2 ^ f.t
def sF (f : Format) (x : Nat) : Nat := x / 2 ^ (f.w + f.t) % 2
/-- the effective exponent `xa = nza ? ea : 1` -/
def xeN (f : Format) (x : Nat) : Nat := if eF f x = 0 then 1 else eF f x
/-- the significand `{nza, fa}` -/
def sigN (f : Format) (x : Nat) : Nat := if eF f x = 0 then fF f x else 2 ^ f.t + fF f x
/-- `Z = 2^EW`, `EW = W + P + 1` -/
def ZN (f : Format) : Nat := 2 ^ (f.w + f.p + 1)

/-- the normalizer row `P - 1` of an operand: normalized significand and exponent register -/
def nyN (f : Format) (x : Nat) : Nat × Nat := normIter f.t (ZN f) f.t (sigN f x, xeN f x)
def naN (f : Format) (x : Nat) : Nat := (nyN f x).1
def yaN (f : Format) (x : Nat) : Nat := (nyN f x).2

/-- the quotient `qq` and the last remainder `rr[P+2]` of the `P + 2` restoring steps -/
def qqN (f : Format) (a b : Nat) : Nat := restQuo (naN f b) (naN f a) (f.p + 2)
def rrN (f : Format) (a b : Nat) : Nat := restRem (naN f b) (naN f a) (f.p + 2)
def adjN (f : Format) (a b : Nat) : Nat := if 2 ^ (f.p + 1) ≤ qqN f a b then 0 else 1
def qmN (f : Format) (a b : Nat) : Nat := if 2 ^ (f.p + 1) ≤ qqN f a b then qqN f a b / 2 else qqN f a b
def st0N (f : Format) (a b : Nat) : Prop := (2 ^ (f.p + 1) ≤ qqN f a b ∧ qqN f a b % 2 = 1) ∨ rrN f a b ≠ 0

/-- `E = ya - yb + emax - adj` in `EW` bits -/
def EN (f : Format) (a b : Nat) : Nat :=
  (((yaN f a + (ZN f - yaN f b)) % ZN f + f.emax) % ZN f + (ZN f - adjN f a b)) % ZN f

/-- `nrm = ~E[EW-1] & (|E)`: `E >= 1` -/
def nrmE (f : Format) (E : Nat) : Prop := E / 2 ^ (f.w + f.p) % 2 = 0 ∧ E ≠ 0
/-- `ovf = ~E[EW-1] & ((|E[EW-2:W]) | (&E[W-1:0]))`: `E >= 2^W - 1` -/
def ovfE (f : Format) (E : Nat) : Prop :=
  E / 2 ^ (f.w + f.p) % 2 = 0 ∧ (E / 2 ^ f.w % 2 ^ f.p ≠ 0 ∨ E % 2 ^ f.w = 2 ^ f.w - 1)
instance (f : Format) (E : Nat) : Decidable (nrmE f E) := by unfold nrmE; infer_instance
instance (f : Format) (E : Nat) : Decidable (ovfE f E) := by unfold ovfE; infer_instance

/-- `dsh = nrm ? 0 : (1 - E)` in `EW` bits -/
def dshE (f : Format) (E : Nat) : Nat := if nrmE f E then 0 else (1 + (ZN f - E)) % ZN f

instance (f : Format) (a b : Nat) : Decidable (st0N f a b) := by unfold st0N; infer_instance

def qsN (f : Format) (a b : Nat) : Nat := qmN f a b / 2 ^ dshE f (EN f a b)
/-- `inc = qs[0] & (st0 | ((qs << dsh) != qm) | qs[1])` -/
def incN (f : Format) (a b : Nat) : Prop :=
  qsN f a b % 2 = 1 ∧ (st0N f a b ∨ qmN f a b % 2 ^ dshE f (EN f a b) ≠ 0 ∨ qsN f a b / 2 % 2 = 1)
instance (f : Format) (a b : Nat) : Decidable (incN f a b) := by unfold incN; infer_instance
def efN (f : Format) (a b : Nat) : Nat := if nrmE f (EN f a b) then EN f a b % 2 ^ f.w else 0
/-- `mag = {ef, qs[P-1:1]} + inc` in `K - 1` bits -/
def magN (f : Format) (a b : Nat) : Nat :=
  (efN f a b * 2 ^ f.t + qsN f a b / 2 % 2 ^ f.t + (if incN f a b then 1 else 0)) % 2 ^ (f.w + f.t)

/-! ## Operand classification and the result word -/

def nanN (f : Format) (x : Nat) : Prop := eF f x = 2 ^ f.w - 1 ∧ fF f x ≠ 0
def infN (f : Format) (x : Nat) : Prop := eF f x = 2 ^ f.w - 1 ∧ fF f x = 0
def zeroN (f : Format) (x : Nat) : Prop := eF f x = 0 ∧ fF f x = 0
def cNanN (f : Format) (a b : Nat) : Prop := nanN f a ∨ nanN f b ∨ (infN f a ∧ infN f b) ∨ (zeroN f a ∧ zeroN f b)
def cInfN (f : Format) (a b : Nat) : Prop := infN f a ∨ zeroN f b
def cZeroN (f : Format) (a b : Nat) : Prop := infN f b ∨ zeroN f a
def ovfN (f : Format) (a b : Nat) : Prop := ovfE f (EN f a b)
def finN (f : Format) (a b : Nat) : Prop := ¬ (cNanN f a b ∨ cInfN f a b ∨ cZeroN f a b ∨ ovfN f a b)

instance (f : Format) (x : Nat) : Decidable (nanN f x) := by unfold nanN; infer_instance
instance (f : Format) (x : Nat) : Decidable (infN f x) := by unfold infN; infer_instance
instance (f : Format) (x : Nat) : Decidable (zeroN f x) := by unfold zeroN; infer_instance
instance (f : Format) (a b : Nat) : Decidable (cNanN f a b) := by unfold cNanN; infer_instance
instance (f : Format) (a b : Nat) : Decidable (cInfN f a b) := by unfold cInfN; infer_instance
instance (f : Format) (a b : Nat) : Decidable (cZeroN f a b) := by unfold cZeroN; infer_instance
instance (f : Format) (a b : Nat) : Decidable (ovfN f a b) := by unfold ovfN; infer_instance
instance (f : Format) (a b : Nat) : Decidable (finN f a b) := by unfold finN; infer_instance

/-- The value of the output `q`, by fields: sign, exponent field, top fraction bit, low fraction bits. -/
def OutN (f : Format) (a b : Nat) : Nat :=
  (if cNanN f a b then 0 else (sF f a + sF f b) % 2) * 2 ^ (f.w + f.t) +
  (if cNanN f a b ∨ cInfN f a b ∨ (¬ cZeroN f a b ∧ ovfN f a b) then 2 ^ f.w - 1
   else if cZeroN f a b then 0 else magN f a b / 2 ^ f.t) * 2 ^ f.t +
  (if cNanN f a b ∨ (finN f a b ∧ magN f a b / 2 ^ (f.t - 1) % 2 = 1) then 1 else 0) * 2 ^ (f.t - 1) +
  (if finN f a b then magN f a b % 2 ^ (f.t - 1) else 0)

/-! ## Residues -/

theorem ovf_bits (E A B : Nat) (hA : 0 < A) (hB : 0 < B) (hE : E < A * B) :
    (E / A % B ≠ 0 ∨ E % A = A - 1) ↔ A - 1 ≤ E := by
  have hq : E / A < B := (Nat.div_lt_iff_lt_mul hA).2 (by rw [Nat.mul_comm] at hE; exact hE)
  have hd := Nat.div_add_mod E A
  have hr := Nat.mod_lt E hA
  rw [Nat.mod_eq_of_lt hq]
  generalize E / A = q at *
  generalize E % A = r at *
  rcases Nat.eq_zero_or_pos q with h0 | hpos
  · subst h0
    simp only [Nat.mul_zero, Nat.zero_add] at hd
    omega
  · have : A ≤ A * q := Nat.le_mul_of_pos_right _ hpos
    omega

theorem two_pow_wp (f : Format) : 2 ^ (f.w + f.p) = 2 ^ f.w * 2 ^ f.p := Nat.pow_add _ _ _

theorem ZN_eq (f : Format) : ZN f = 2 * 2 ^ (f.w + f.p) := by
  unfold ZN; rw [Nat.pow_succ]; omega

theorem Z_big (f : Format) : 4 * 2 ^ f.w + 2 * f.t + 8 ≤ ZN f := by
  have hA := four_le_two_pow_w f
  have hp := f.hp
  have hC : 4 ≤ 2 ^ f.p := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ f.p := Nat.pow_le_pow_right (by omega) hp
  have ht : f.t < 2 ^ f.p := by
    have h1 : f.t < 2 ^ f.t := Nat.lt_two_pow_self
    have h2 : 2 ^ f.t ≤ 2 ^ f.p := Nat.pow_le_pow_right (by omega) (by simp only [Format.t]; omega)
    omega
  have h1 : 4 * 2 ^ f.p ≤ 2 ^ f.w * 2 ^ f.p := Nat.mul_le_mul_right _ hA
  have h2 : 2 ^ f.w * 4 ≤ 2 ^ f.w * 2 ^ f.p := Nat.mul_le_mul_left _ hC
  rw [ZN_eq, two_pow_wp]
  omega

/-! ## The exponent decode -/

theorem exp_facts (Z A emax t xa xb la lb ya yb adj : Nat)
    (hZ : 4 * A + 2 * t + 8 ≤ Z) (hA : 4 ≤ A) (hem : 2 * emax + 2 = A)
    (hxa1 : 1 ≤ xa) (hxa2 : xa + 2 ≤ A) (hxb1 : 1 ≤ xb) (hxb2 : xb + 2 ≤ A)
    (hla : la ≤ t) (hlb : lb ≤ t) (hadj : adj ≤ 1)
    (hya : ya < Z) (hya' : ya + la = xa ∨ ya + la = xa + Z)
    (hyb : yb < Z) (hyb' : yb + lb = xb ∨ yb + lb = xb + Z) :
    ((0 : Int) ≤ (xa : Int) - la - xb + lb + emax - adj ∧
        (((((ya + (Z - yb)) % Z + emax) % Z + (Z - adj)) % Z : Nat) : Int) =
          (xa : Int) - la - xb + lb + emax - adj) ∨
    ((xa : Int) - la - xb + lb + emax - adj < 0 ∧
        (((((ya + (Z - yb)) % Z + emax) % Z + (Z - adj)) % Z : Nat) : Int) =
          (xa : Int) - la - xb + lb + emax - adj + Z) := by
  have hZ0 : 0 < Z := by omega
  have h1 := mod_cases_of_lt_three_mul (ya + (Z - yb)) Z (by omega)
  have hm1 := Nat.mod_lt (ya + (Z - yb)) hZ0
  generalize (ya + (Z - yb)) % Z = E1 at *
  have h2 := mod_cases_of_lt_three_mul (E1 + emax) Z (by omega)
  have hm2 := Nat.mod_lt (E1 + emax) hZ0
  generalize (E1 + emax) % Z = E2 at *
  have h3 := mod_cases_of_lt_three_mul (E2 + (Z - adj)) Z (by omega)
  have hm3 := Nat.mod_lt (E2 + (Z - adj)) hZ0
  generalize (E2 + (Z - adj)) % Z = E3 at *
  omega

theorem nrm_ovf_dsh (f : Format) (E : Nat) (Ei : Int)
    (hE : (0 ≤ Ei ∧ (E : Int) = Ei) ∨ (Ei < 0 ∧ (E : Int) = Ei + ZN f))
    (h1 : -(ZN f : Int) < 2 * Ei) (h2 : 2 * Ei < ZN f) (hE2 : E < ZN f) :
    (nrmE f E ↔ 1 ≤ Ei) ∧ (ovfE f E ↔ ((2 ^ f.w : Nat) : Int) - 1 ≤ Ei) ∧
    (¬ nrmE f E → ((dshE f E : Nat) : Int) = 1 - Ei) := by
  have hZH := ZN_eq f
  have hA4 := four_le_two_pow_w f
  have hbt := div_mod_two_eq_zero_iff_lt E (2 ^ (f.w + f.p)) (by omega)
  have hsgn : E / 2 ^ (f.w + f.p) % 2 = 0 ↔ 0 ≤ Ei := by
    rw [hbt]; omega
  have hnrm : nrmE f E ↔ 1 ≤ Ei := by
    unfold nrmE; rw [hsgn]; omega
  refine ⟨hnrm, ?_, ?_⟩
  · unfold ovfE
    rw [hsgn]
    by_cases hs : 0 ≤ Ei
    · have hEH : E < 2 ^ (f.w + f.p) := hbt.1 (hsgn.2 hs)
      have hEE : E < 2 ^ f.w * 2 ^ f.p := by rw [← two_pow_wp]; exact hEH
      have hob := ovf_bits E (2 ^ f.w) (2 ^ f.p) (Nat.two_pow_pos _) (Nat.two_pow_pos _) hEE
      constructor
      · rintro ⟨-, h⟩
        have := hob.1 h
        omega
      · intro h
        refine ⟨hs, hob.2 ?_⟩
        omega
    · constructor
      · rintro ⟨h, -⟩; exact absurd h hs
      · intro h; omega
  · intro hn
    have hn' : ¬ (1 ≤ Ei) := fun h => hn (hnrm.2 h)
    unfold dshE
    rw [if_neg hn]
    have h3 := mod_cases_of_lt_three_mul (1 + (ZN f - E)) (ZN f) (by omega)
    omega

/-! ## The quotient and the sticky bit -/

theorem mul_sq (X n : Nat) : 2 * X * (2 * n) = 4 * X * n := by
  have h : 2 * X * (2 * n) = 2 * (2 * (X * n)) := by ac_rfl
  have h2 : 4 * X * n = 4 * (X * n) := Nat.mul_assoc _ _ _
  omega

/-- The `P + 2` restoring steps with `P = T + 1`, on `na, nb ∈ [2^T, 2^(T+1))`. -/
theorem qm_st0 (T na nb : Nat) (h1 : 2 ^ T ≤ na) (h2 : na < 2 ^ (T + 1)) (h3 : 2 ^ T ≤ nb)
    (h4 : nb < 2 ^ (T + 1)) :
    (2 ^ (T + 2) ≤ restQuo nb na (T + 3) ↔ nb ≤ na) ∧
    (2 ^ (T + 2) ≤ restQuo nb na (T + 3) →
      restQuo nb na (T + 3) / 2 = 2 ^ (T + 1) * na / nb ∧
      ((restQuo nb na (T + 3) % 2 = 1 ∨ restRem nb na (T + 3) ≠ 0) ↔ 2 ^ (T + 1) * na % nb ≠ 0)) ∧
    (restQuo nb na (T + 3) = 2 ^ (T + 2) * na / nb) ∧
    (restRem nb na (T + 3) = 2 * (2 ^ (T + 2) * na % nb)) := by
  have hT := Nat.two_pow_pos T
  have hd : 0 < nb := by omega
  have hx : na < 2 * nb := by rw [Nat.pow_succ] at h2; omega
  have e1 := restore_spec nb na (T + 1) hd hx
  have e2 := restore_spec nb na (T + 2) hd hx
  have s1 : restQuo nb na (T + 3) = 2 * restQuo nb na (T + 2) + (if nb ≤ restRem nb na (T + 2) then 1 else 0) := by
    first | rfl | simp [restQuo]
  have s2 : restRem nb na (T + 3) =
      if nb ≤ restRem nb na (T + 2) then 2 * (restRem nb na (T + 2) - nb) else 2 * restRem nb na (T + 2) := by
    first | rfl | simp [restRem]
  obtain ⟨q1, r1⟩ := e1
  obtain ⟨q2, r2⟩ := e2
  have hpos : 0 < 2 ^ (T + 2) := Nat.two_pow_pos _
  have key : 2 ^ (T + 2) ≤ 2 ^ (T + 2) * na / nb ↔ nb ≤ na := by
    rw [Nat.le_div_iff_mul_le hd]
    constructor
    · intro h
      exact Nat.le_of_mul_le_mul_left h hpos
    · intro h
      exact Nat.mul_le_mul_left _ h
  rw [q2] at s1
  rw [q1, r1] at s1
  rw [r2, r1] at s2
  rw [q2, r2]
  refine ⟨key, fun _ => ?_, rfl, rfl⟩
  generalize 2 ^ (T + 2) * na / nb = Q at *
  generalize 2 ^ (T + 2) * na % nb = R at *
  generalize 2 ^ (T + 1) * na / nb = q at *
  generalize 2 ^ (T + 1) * na % nb = r at *
  split at s1 <;> split at s2 <;> omega

/-- `qm = ⌊M0 / nb⌋ ∈ [2^p, 2^(p+1))` and `st0 ↔ M0 mod nb ≠ 0`, `M0 = 2^(p+adj) · na`, for the quotient `Q` and the
last remainder `R` of the `P + 2` restoring steps. -/
theorem quot_abs (T na nb Q R : Nat) (hQ : Q = restQuo nb na (T + 3)) (hR : R = restRem nb na (T + 3))
    (h1 : 2 ^ T ≤ na) (h2 : na < 2 ^ (T + 1)) (h3 : 2 ^ T ≤ nb) (h4 : nb < 2 ^ (T + 1)) :
    ∃ adj qm M0 : Nat, adj ≤ 1 ∧ (if 2 ^ (T + 2) ≤ Q then 0 else 1) = adj ∧
      (if 2 ^ (T + 2) ≤ Q then Q / 2 else Q) = qm ∧ M0 = 2 ^ (T + 1 + adj) * na ∧ qm = M0 / nb ∧
      (((2 ^ (T + 2) ≤ Q ∧ Q % 2 = 1) ∨ R ≠ 0) ↔ M0 % nb ≠ 0) ∧
      2 * 2 ^ T ≤ qm ∧ qm < 4 * 2 ^ T ∧ (adj = 0 ↔ nb ≤ na) := by
  subst hQ hR
  obtain ⟨hk, hs, hQe, hRe⟩ := qm_st0 T na nb h1 h2 h3 h4
  have hMt := Nat.two_pow_pos T
  have hnb : 0 < nb := by omega
  have hP1 : 2 ^ (T + 1) = 2 * 2 ^ T := by rw [Nat.pow_succ]; omega
  have hP2 : 2 ^ (T + 2) = 4 * 2 ^ T := by rw [Nat.pow_add]; omega
  generalize restQuo nb na (T + 3) = Q at *
  generalize restRem nb na (T + 3) = R at *
  by_cases hc : nb ≤ na
  · have hq1 : 2 ^ (T + 2) ≤ Q := hk.2 hc
    obtain ⟨e1, e2⟩ := hs hq1
    refine ⟨0, Q / 2, 2 ^ (T + 1 + 0) * na, by omega, if_pos hq1, if_pos hq1, rfl, e1, ?_, ?_, ?_,
      ⟨fun _ => hc, fun _ => rfl⟩⟩
    · exact ⟨fun h => e2.1 (h.elim (fun h => Or.inl h.2) Or.inr),
        fun h => (e2.2 h).elim (fun h => Or.inl ⟨hq1, h⟩) Or.inr⟩
    · rw [e1, hP1]
      apply (Nat.le_div_iff_mul_le hnb).2
      exact Nat.mul_le_mul_left _ hc
    · rw [e1, hP1]
      apply (Nat.div_lt_iff_lt_mul hnb).2
      have h5 : na < 2 * nb := by omega
      calc 2 * 2 ^ T * na < 2 * 2 ^ T * (2 * nb) := Nat.mul_lt_mul_of_pos_left h5 (by omega)
        _ = 4 * 2 ^ T * nb := mul_sq _ _
  · have hq1 : ¬ 2 ^ (T + 2) ≤ Q := fun h => hc (hk.1 h)
    refine ⟨1, Q, 2 ^ (T + 1 + 1) * na, by omega, if_neg hq1, if_neg hq1, rfl, hQe, ?_, ?_, ?_,
      ⟨fun h => by omega, fun h => absurd h hc⟩⟩
    · have hX : 2 ^ (T + 1 + 1) * na % nb = 2 ^ (T + 2) * na % nb := rfl
      rw [hX]
      constructor
      · rintro (⟨h, -⟩ | h)
        · exact absurd h hq1
        · rw [hRe] at h; omega
      · intro h
        right
        rw [hRe]; omega
    · rw [hQe, hP2]
      apply (Nat.le_div_iff_mul_le hnb).2
      have h5 : nb ≤ 2 * na := by omega
      calc 2 * 2 ^ T * nb ≤ 2 * 2 ^ T * (2 * na) := Nat.mul_le_mul_left _ h5
        _ = 4 * 2 ^ T * na := mul_sq _ _
    · rw [hP2] at hq1; omega

end SvGolf.FdivParam

end DpQ

/-! # Section `DpR`: Bridges, operands and the packed magnitude (was `tasks/fdivp/DpR.lean`) -/

section DpR

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the datapath model computes the certified result, for every format (untrusted, kernel-checked)

WP-H3. Bridges between the model (`Nat`) and the spec's `BitVec` fields, the facts about a finite nonzero operand, and the
packed magnitude in the two regimes; then `fin_cert_model` (the result of the datapath on finite nonzero operands is
accepted by the rounding certificate, with `ovf` giving infinity) and `OutN_eq` (the whole output equals the spec's
`divide`).
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib
/-! ## Bridges -/

theorem hp_eq (f : Format) : f.p = f.t + 1 := by have := f.hp; simp only [Format.t]; omega

theorem qexpF_eq' (f : Format) (a : BitVec f.k) :
    qexpF f a = (xeN f a.toNat : Int) - f.emax - f.t := by
  unfold qexpF xeN
  by_cases h : expF f a = 0
  · have h' : eF f a.toNat = 0 := h
    rw [if_pos h, if_pos h']
    first | rfl | simp
  · have h' : ¬ eF f a.toNat = 0 := h
    rw [if_neg h, if_neg h']
    first | rfl | simp

theorem sign_nat (f : Format) (a : BitVec f.k) : (if signF f a = true then 1 else 0) = sF f a.toNat := by
  have hlt : a.toNat < 2 * 2 ^ (f.w + f.t) := two_pow_k f ▸ a.isLt
  have hq : a.toNat / 2 ^ (f.w + f.t) < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by omega)
  unfold signF sF
  generalize a.toNat / 2 ^ (f.w + f.t) = q at *
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> simp

theorem sign_xor_nat (f : Format) (a b : BitVec f.k) :
    (if (signF f a ^^ signF f b) = true then 1 else 0) = (sF f a.toNat + sF f b.toNat) % 2 := by
  have h1 := sign_nat f a
  have h2 := sign_nat f b
  generalize signF f a = p at h1 ⊢
  generalize signF f b = q at h2 ⊢
  cases p <;> cases q <;> simp at h1 h2 ⊢ <;> omega

/-! ## A finite nonzero operand -/

theorem fin_op (f : Format) (x : BitVec f.k) (hn : ¬ isNaNF f x) (hi : ¬ isInfF f x) (hz : ¬ isZeroF f x) :
    eF f x.toNat ≠ 2 ^ f.w - 1 ∧ ¬ (eF f x.toNat = 0 ∧ fF f x.toNat = 0) := by
  unfold isNaNF at hn
  unfold isInfF at hi
  unfold isZeroF at hz
  refine ⟨fun h => ?_, hz⟩
  by_cases hf : fF f x.toNat = 0
  · exact hi ⟨h, hf⟩
  · exact hn ⟨h, hf⟩

theorem sig_facts (f : Format) (x : Nat) (hz : ¬ (eF f x = 0 ∧ fF f x = 0)) :
    0 < sigN f x ∧ sigN f x < 2 ^ f.p := by
  have hp1 : 2 ^ f.p = 2 * 2 ^ f.t := two_pow_t f
  have hf : fF f x < 2 ^ f.t := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hMt := Nat.two_pow_pos f.t
  unfold sigN
  by_cases h : eF f x = 0
  · rw [if_pos h]
    have : fF f x ≠ 0 := fun h' => hz ⟨h, h'⟩
    omega
  · rw [if_neg h]
    omega

theorem xe_facts (f : Format) (x : Nat) (hfin : eF f x ≠ 2 ^ f.w - 1) :
    1 ≤ xeN f x ∧ xeN f x + 2 ≤ 2 ^ f.w := by
  have he : eF f x < 2 ^ f.w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hA := four_le_two_pow_w f
  unfold xeN
  by_cases h : eF f x = 0
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem norm_facts (f : Format) (x : Nat) (hz : ¬ (eF f x = 0 ∧ fF f x = 0)) (hfin : eF f x ≠ 2 ^ f.w - 1) :
    ∃ l, l ≤ f.t ∧ naN f x = sigN f x * 2 ^ l ∧ yaN f x < ZN f ∧
      (yaN f x + l = xeN f x ∨ yaN f x + l = xeN f x + ZN f) ∧ 2 ^ f.t ≤ naN f x ∧ naN f x < 2 ^ f.p := by
  obtain ⟨hs0, hs1⟩ := sig_facts f x hz
  obtain ⟨hx1, hx2⟩ := xe_facts f x hfin
  have hZ := Z_big f
  have hp : f.p = f.t + 1 := hp_eq f
  have hs1' : sigN f x < 2 ^ (f.t + 1) := by rw [← hp]; exact hs1
  have hk : 2 ^ f.t ≤ sigN f x * 2 ^ f.t := Nat.le_mul_of_pos_left _ hs0
  obtain ⟨l, y', hl, hr, hy', hyl, h3, h4⟩ :=
    normIter_spec f.t (ZN f) f.t (sigN f x) (xeN f x) hs0 hs1' hk (by omega) (by omega)
  refine ⟨l, hl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold naN nyN; rw [hr]
  · unfold yaN nyN; rw [hr]; exact hy'
  · unfold yaN nyN; rw [hr]; exact hyl
  · unfold naN nyN; rw [hr]; exact h3
  · unfold naN nyN; rw [hr]; rw [hp]; exact h4

/-! ## The packed magnitude -/

/-- Normal regime: `qs = qm`, `ef = E`. -/
theorem mag_norm (Mt A Ep qm inc : Nat) (hMt : 0 < Mt) (hEp1 : 1 ≤ Ep) (hEp2 : Ep + 2 ≤ A)
    (hq1 : 2 * Mt ≤ qm) (hq2 : qm < 4 * Mt) (hinc : inc ≤ 1) :
    (Ep % A * Mt + qm / 2 % Mt + inc) % (A * Mt) = (Ep - 1) * Mt + (qm / 2 + inc) := by
  have e1 : Ep % A = Ep := Nat.mod_eq_of_lt (by omega)
  have e2 : qm / 2 % Mt = qm / 2 - Mt := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨j, hj⟩ : ∃ j, Ep = j + 1 := ⟨Ep - 1, by omega⟩
  have e3 : (j + 1) * Mt = j * Mt + Mt := by rw [Nat.add_mul, Nat.one_mul]
  have e4 : (Ep + 1) * Mt ≤ (A - 1) * Mt := Nat.mul_le_mul_right _ (by omega)
  have e5 : (A - 1) * Mt + Mt = A * Mt := by
    have hA1 : A = (A - 1) + 1 := by omega
    calc (A - 1) * Mt + Mt = (A - 1) * Mt + 1 * Mt := by rw [Nat.one_mul]
      _ = ((A - 1) + 1) * Mt := (Nat.add_mul _ _ _).symm
      _ = A * Mt := by rw [← hA1]
  have e6 : (Ep + 1) * Mt = j * Mt + 2 * Mt := by
    rw [hj, show j + 1 + 1 = j + 2 by rfl, Nat.add_mul]
  rw [e1, e2]
  have e7 : Ep * Mt = j * Mt + Mt := by rw [hj, e3]
  have : Ep - 1 = j := by omega
  rw [this, Nat.mod_eq_of_lt]
  · rw [e7]; omega
  · omega

/-- Subnormal regime: `ef = 0`, `qs / 2 < 2^t`. -/
theorem mag_sub (Mt A qs inc : Nat) (hMt : 0 < Mt) (hA : 2 ≤ A) (hqs : qs < 2 * Mt) (hinc : inc ≤ 1) :
    (0 * Mt + qs / 2 % Mt + inc) % (A * Mt) = qs / 2 + inc := by
  have e2 : qs / 2 % Mt = qs / 2 := Nat.mod_eq_of_lt (by omega)
  have e3 : 2 * Mt ≤ A * Mt := Nat.mul_le_mul_right _ hA
  rw [e2, Nat.mod_eq_of_lt]
  · omega
  · omega

end SvGolf.FdivParam

end DpR

/-! # Section `DpS`: The model computes `divide`: the finite arm (was `tasks/fdivp/DpS.lean`) -/

section DpS

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the model computes `divide`, for every format (untrusted, kernel-checked)

WP-H3. `fin_cert_model`: for finite nonzero operands the datapath's result (`infinity` on `ovf`, otherwise the pattern
with fields `(mag / 2^t, mag % 2^t)`) is accepted by the rounding certificate `certF` of `CertF.lean`, hence (by
`certF_bridge`) is `finQuotF = divide`. `OutN_eq`: the value of the output `q` of the design (`OutN`, by fields) is
`(divide f .roundTiesToEven a b).toNat`, in every case of the special-value table.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

theorem fin_cert_model (f : Format) (a b : BitVec f.k)
    (ha : ¬ isNaNF f a) (ha' : ¬ isInfF f a) (ha0 : ¬ isZeroF f a)
    (hb : ¬ isNaNF f b) (hb' : ¬ isInfF f b) (hb0 : ¬ isZeroF f b) :
    (ovfN f a.toNat b.toNat → certF f a b (infinity f (signF f a ^^ signF f b)) = true) ∧
    (¬ ovfN f a.toNat b.toNat → magN f a.toNat b.toNat < 2 ^ (f.w + f.t) ∧
       certF f a b (fields f (signF f a ^^ signF f b) (magN f a.toNat b.toNat / 2 ^ f.t)
         (magN f a.toNat b.toNat % 2 ^ f.t)) = true) := by
  have hp := hp_eq f
  have hMt := Nat.two_pow_pos f.t
  have hev := two_pow_t_even f
  have hw2 := two_pow_w_emax f
  have hw4 := four_le_two_pow_w f
  have hemax := emax_pos f
  have hp1 : 2 ^ f.p = 2 * 2 ^ f.t := two_pow_t f
  have hZ := Z_big f
  obtain ⟨hea, hza⟩ := fin_op f a ha ha' ha0
  obtain ⟨heb, hzb⟩ := fin_op f b hb hb' hb0
  obtain ⟨hxa1, hxa2⟩ := xe_facts f a.toNat hea
  obtain ⟨hxb1, hxb2⟩ := xe_facts f b.toNat heb
  obtain ⟨la, hla, hna_eq, hya, hya', hna1, hna2⟩ := norm_facts f a.toNat hza hea
  obtain ⟨lb, hlb, hnb_eq, hyb, hyb', hnb1, hnb2⟩ := norm_facts f b.toNat hzb heb
  have hna2' : naN f a.toNat < 2 ^ (f.t + 1) := by rw [← hp]; exact hna2
  have hnb2' : naN f b.toNat < 2 ^ (f.t + 1) := by rw [← hp]; exact hnb2
  have hp3 : f.p + 2 = f.t + 3 := by omega
  obtain ⟨adj, qm, M0, hadj, hadj_def, hqm_def, hM0, hqmM, hst, hq_lo, hq_hi, hadj0⟩ :=
    quot_abs f.t (naN f a.toNat) (naN f b.toNat) (qqN f a.toNat b.toNat) (rrN f a.toNat b.toNat)
      (by unfold qqN; rw [hp3]) (by unfold rrN; rw [hp3]) hna1 hna2' hnb1 hnb2'
  have hadjN : adjN f a.toNat b.toNat = adj := by
    unfold adjN; rw [hp]; exact hadj_def
  have hqmN : qmN f a.toNat b.toNat = qm := by
    unfold qmN; rw [hp]; exact hqm_def
  have hstN : st0N f a.toNat b.toNat ↔ M0 % naN f b.toNat ≠ 0 := by
    unfold st0N; rw [hp]; exact hst
  subst hqmN
  have hnb : 0 < naN f b.toNat := by omega
  -- the exponent
  obtain ⟨Ei, hEi⟩ : ∃ Ei : Int, Ei = (xeN f a.toNat : Int) - la - xeN f b.toNat + lb + f.emax - adj := ⟨_, rfl⟩
  have hEdec := exp_facts (ZN f) (2 ^ f.w) f.emax f.t (xeN f a.toNat) (xeN f b.toNat) la lb
    (yaN f a.toNat) (yaN f b.toNat) adj hZ hw4 hw2.symm hxa1 hxa2 hxb1 hxb2 hla hlb hadj hya hya' hyb hyb'
  have hE : (0 ≤ Ei ∧ (EN f a.toNat b.toNat : Int) = Ei) ∨ (Ei < 0 ∧ (EN f a.toNat b.toNat : Int) = Ei + ZN f) := by
    have h : EN f a.toNat b.toNat =
        (((yaN f a.toNat + (ZN f - yaN f b.toNat)) % ZN f + f.emax) % ZN f + (ZN f - adj)) % ZN f := by
      unfold EN; rw [hadjN]
    rw [h, hEi]; exact hEdec
  have hE2 : EN f a.toNat b.toNat < ZN f := by
    unfold EN; exact Nat.mod_lt _ (by omega)
  have hEi1 : -(ZN f : Int) < 2 * Ei := by omega
  have hEi2 : 2 * Ei < ZN f := by omega
  obtain ⟨hnrm_iff, hovf_iff, hdsh⟩ := nrm_ovf_dsh f (EN f a.toNat b.toNat) Ei hE hEi1 hEi2 hE2
  -- the exact quotient
  have hD : 0 < sigF f b * 2 ^ (-(qexpF f a - qexpF f b + (f.scale : Int))).toNat :=
    Nat.mul_pos (sigF_pos f b hb0) (Nat.two_pow_pos _)
  have hq1 : naN f b.toNat * qmN f a.toNat b.toNat ≤ M0 := by
    rw [hqmM]; exact Nat.mul_div_le M0 _
  have hdm := Nat.div_add_mod M0 (naN f b.toNat)
  have hmd := Nat.mod_lt M0 hnb
  have hq2 : M0 < naN f b.toNat * qmN f a.toNat b.toNat + naN f b.toNat := by
    rw [hqmM]; omega
  have hst1 : st0N f a.toNat b.toNat → naN f b.toNat * qmN f a.toNat b.toNat < M0 := by
    intro h
    have := hstN.1 h
    rw [hqmM]; omega
  have hst2 : ¬ st0N f a.toNat b.toNat → M0 = naN f b.toNat * qmN f a.toNat b.toNat := by
    intro h
    have : ¬ (M0 % naN f b.toNat ≠ 0) := fun h' => h (hstN.2 h')
    rw [hqmM]; omega
  have hrel_gen : ∀ j sh : Nat, (j : Int) + 1 = Ei + sh →
      sigF f a * 2 ^ (qexpF f a - qexpF f b + (f.scale : Int)).toNat * (naN f b.toNat * 2 ^ (sh + 1)) =
      sigF f b * 2 ^ (-(qexpF f a - qexpF f b + (f.scale : Int))).toNat * (2 ^ j * M0) := by
    intro j sh hjs
    have he : qexpF f a - qexpF f b + (f.scale : Int) =
        (xeN f a.toNat : Int) - xeN f b.toNat + ((f.emax : Int) + f.t - 1) := by
      rw [qexpF_eq', qexpF_eq']
      have : (f.scale : Int) = (f.emax : Int) + f.t - 1 := by simp only [Format.scale]; omega
      rw [this]; omega
    rw [he, hnb_eq, hM0, hna_eq]
    exact scale_id' (sigN f a.toNat) (sigN f b.toNat) la lb (xeN f a.toNat) (xeN f b.toNat) adj j sh
      f.emax f.t _ Ei rfl hEi hjs
  have hinc01 : (if incN f a.toNat b.toNat then 1 else 0) ≤ 1 := by
    by_cases h : incN f a.toNat b.toNat <;> simp [h]
  refine ⟨fun hov => ?_, fun hnov => ⟨?_, ?_⟩⟩
  · -- overflow
    have hEi_big : ((2 ^ f.w : Nat) : Int) - 1 ≤ Ei := hovf_iff.1 hov
    obtain ⟨Ep, hEp⟩ : ∃ Ep : Nat, Ei = Ep := ⟨Ei.toNat, by omega⟩
    have hjs : ((Ep - 1 : Nat) : Int) + 1 = Ei + ((0 : Nat) : Int) := by omega
    have hrel := hrel_gen (Ep - 1) 0 hjs
    have hj : 2 ^ f.w ≤ (Ep - 1) + 2 := by omega
    show certNF f (sigF f a * 2 ^ (qexpF f a - qexpF f b + (f.scale : Int)).toNat)
      (sigF f b * 2 ^ (-(qexpF f a - qexpF f b + (f.scale : Int))).toNat) (signF f a ^^ signF f b)
      (infinity f (signF f a ^^ signF f b)) = true
    exact ovf_cert_abs f _ _ (naN f b.toNat) M0 (qmN f a.toNat b.toNat) (Ep - 1) _ hD hnb hrel hq1 hq_lo hj
  · -- the magnitude is a (K-1)-bit number
    unfold magN; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · -- finite pattern
    have hnov' : ¬ ovfE f (EN f a.toNat b.toNat) := hnov
    have hEi_small : Ei < ((2 ^ f.w : Nat) : Int) - 1 := by
      by_cases h : ((2 ^ f.w : Nat) : Int) - 1 ≤ Ei
      · exact absurd (hovf_iff.2 h) hnov'
      · omega
    have hmag_lt : magN f a.toNat b.toNat < 2 ^ (f.w + f.t) := by
      unfold magN; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    show certNF f (sigF f a * 2 ^ (qexpF f a - qexpF f b + (f.scale : Int)).toNat)
      (sigF f b * 2 ^ (-(qexpF f a - qexpF f b + (f.scale : Int))).toNat) (signF f a ^^ signF f b)
      (fields f (signF f a ^^ signF f b) (magN f a.toNat b.toNat / 2 ^ f.t)
        (magN f a.toNat b.toNat % 2 ^ f.t)) = true
    by_cases hn : nrmE f (EN f a.toNat b.toNat)
    · -- the normal regime: sh = 0
      have hn1 : 1 ≤ Ei := hnrm_iff.1 hn
      obtain ⟨Ep, hEp⟩ : ∃ Ep : Nat, Ei = Ep := ⟨Ei.toNat, by omega⟩
      have hEN : EN f a.toNat b.toNat = Ep := by omega
      have hd0 : dshE f (EN f a.toNat b.toNat) = 0 := by unfold dshE; rw [if_pos hn]
      have hqs : qsN f a.toNat b.toNat = qmN f a.toNat b.toNat := by
        unfold qsN; rw [hd0, Nat.pow_zero, Nat.div_one]
      have hmag : magN f a.toNat b.toNat =
          (Ep - 1) * 2 ^ f.t + (qmN f a.toNat b.toNat / 2 + (if incN f a.toNat b.toNat then 1 else 0)) := by
        have := mag_norm (2 ^ f.t) (2 ^ f.w) Ep (qmN f a.toNat b.toNat) (if incN f a.toNat b.toNat then 1 else 0)
          hMt (by omega) (by omega) hq_lo (by omega) hinc01
        unfold magN efN
        rw [if_pos hn, hEN, hqs, Nat.pow_add]
        exact this
      have hinc_def : incN f a.toNat b.toNat ↔
          (qmN f a.toNat b.toNat % 2 = 1 ∧ (st0N f a.toNat b.toNat ∨ qmN f a.toNat b.toNat / 2 % 2 = 1)) := by
        unfold incN
        rw [hqs, hd0, Nat.pow_zero, Nat.mod_one]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases h2 with h | h | h
          · exact Or.inl h
          · exact absurd rfl h
          · exact Or.inr h
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases h2 with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
      have hjs : ((Ep - 1 : Nat) : Int) + 1 = Ei + ((0 : Nat) : Int) := by omega
      have hrel := hrel_gen (Ep - 1) 0 hjs
      refine fin_cert_abs f _ _ (naN f b.toNat) M0 (qmN f a.toNat b.toNat) 0 (Ep - 1)
        (qmN f a.toNat b.toNat / 2 ^ 0 / 2 + (if incN f a.toNat b.toNat then 1 else 0))
        (magN f a.toNat b.toNat) (st0N f a.toNat b.toNat) (incN f a.toNat b.toNat) _ hD hnb hrel hq1 hq2 hst1 hst2
        hq_lo hq_hi ?_ rfl ?_ ?_
      · unfold incN qsN
        rw [hd0]
      · rw [hmag]; simp
      · left
        refine ⟨rfl, ?_, ?_, ?_, ?_⟩
        · simp only [Nat.pow_zero, Nat.div_one]
          omega
        · simp only [Nat.pow_zero, Nat.div_one]
          omega
        · omega
        · simp only [Nat.pow_zero, Nat.div_one]
          constructor
          · intro hz
            have hic : incN f a.toNat b.toNat := by
              by_cases hic : incN f a.toNat b.toNat
              · exact hic
              · rw [if_neg hic] at hz; omega
            have := (hinc_def.1 hic).1
            rw [if_pos hic] at hz
            omega
          · intro hq
            have hic : incN f a.toNat b.toNat := by
              apply hinc_def.2
              refine ⟨by omega, Or.inr (by omega)⟩
            rw [if_pos hic]
            omega
    · -- the subnormal regime: sh = 1 - E >= 1
      have hn1 : ¬ (1 ≤ Ei) := fun h => hn (hnrm_iff.2 h)
      have hd := hdsh hn
      have hd1 : 1 ≤ dshE f (EN f a.toNat b.toNat) := by omega
      have hqs_lt : qsN f a.toNat b.toNat < 2 * 2 ^ f.t := by
        unfold qsN
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
        have h2 : 2 ^ 1 ≤ 2 ^ dshE f (EN f a.toNat b.toNat) := Nat.pow_le_pow_right (by omega) hd1
        have := Nat.mul_le_mul_left (2 * 2 ^ f.t) h2
        simp only [Nat.pow_one] at h2
        omega
      have hmag : magN f a.toNat b.toNat =
          qmN f a.toNat b.toNat / 2 ^ dshE f (EN f a.toNat b.toNat) / 2 +
            (if incN f a.toNat b.toNat then 1 else 0) := by
        have := mag_sub (2 ^ f.t) (2 ^ f.w) (qsN f a.toNat b.toNat) (if incN f a.toNat b.toNat then 1 else 0)
          hMt (by omega) hqs_lt hinc01
        unfold magN efN
        rw [if_neg hn, Nat.pow_add]
        exact this
      have hjs : ((0 : Nat) : Int) + 1 = Ei + ((dshE f (EN f a.toNat b.toNat) : Nat) : Int) := by omega
      have hrel := hrel_gen 0 (dshE f (EN f a.toNat b.toNat)) hjs
      refine fin_cert_abs f _ _ (naN f b.toNat) M0 (qmN f a.toNat b.toNat) (dshE f (EN f a.toNat b.toNat)) 0
        (qmN f a.toNat b.toNat / 2 ^ dshE f (EN f a.toNat b.toNat) / 2 + (if incN f a.toNat b.toNat then 1 else 0))
        (magN f a.toNat b.toNat) (st0N f a.toNat b.toNat) (incN f a.toNat b.toNat) _ hD hnb hrel hq1 hq2 hst1 hst2
        hq_lo hq_hi ?_ rfl ?_ ?_
      · unfold incN qsN
        exact Iff.rfl
      · rw [hmag]; simp
      · right
        refine ⟨rfl, hd1, ?_⟩
        have : qsN f a.toNat b.toNat / 2 < 2 ^ f.t := by omega
        have h2 : qsN f a.toNat b.toNat = qmN f a.toNat b.toNat / 2 ^ dshE f (EN f a.toNat b.toNat) := rfl
        rw [← h2]
        omega

end SvGolf.FdivParam

end DpS

/-! # Section `DpT`: The whole output is `divide` (was `tasks/fdivp/DpT.lean`) -/

section DpT

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the whole output of the parametric divider is `divide`, for every format (untrusted, kernel-checked)

WP-H3, the end of the math layer. `OutN_eq`: for EVERY format `f` (`2 ≤ w`, `2 ≤ p`) and every pair of patterns, the value
`OutN f a b` of the output of `fdivp3.sv` (sign, exponent field, top fraction bit, low fraction bits, each by case of the
special-value table) is the value of `divide f .roundTiesToEven a b`, the trusted spec. `OutN_fdivBits` restates it with the
task's own function `fdivBits W P`.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

theorem OutN_eq (f : Format) (a b : BitVec f.k) :
    OutN f a.toNat b.toNat = (divide f .roundTiesToEven a b).toNat := by
  have hMt := Nat.two_pow_pos f.t
  have hA := four_le_two_pow_w f
  have hpf := f.hp
  have ht1 : 1 ≤ f.t := by simp only [Format.t]; omega
  have hE : 2 ^ f.w - 1 < 2 ^ f.w := by omega
  have hs := sign_xor_nat f a b
  rw [divide_table f .roundTiesToEven a b]
  by_cases hN : isNaNF f a ∨ isNaNF f b ∨ (isInfF f a ∧ isInfF f b) ∨ (isZeroF f a ∧ isZeroF f b)
  · rw [if_pos hN]
    have hN' : cNanN f a.toNat b.toNat := hN
    have hT : 2 ^ (f.t - 1) < 2 ^ f.t := Nat.pow_lt_pow_right (by omega) (by omega)
    unfold canonicalNaN
    rw [fields_toNat f false _ _ hE hT]
    unfold OutN
    have hfin : ¬ finN f a.toNat b.toNat := fun h => h (Or.inl hN')
    have c1 : cNanN f a.toNat b.toNat ∨ cInfN f a.toNat b.toNat ∨ (¬ cZeroN f a.toNat b.toNat ∧ ovfN f a.toNat b.toNat) :=
      Or.inl hN'
    have c2 : cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1) :=
      Or.inl hN'
    rw [if_pos hN', if_pos c1, if_pos c2, if_neg hfin]
    simp
  · rw [if_neg hN]
    have hN' : ¬ cNanN f a.toNat b.toNat := hN
    by_cases hI : isInfF f a ∨ isZeroF f b
    · rw [if_pos hI]
      have hI' : cInfN f a.toNat b.toNat := hI
      unfold infinity
      rw [fields_toNat f _ _ _ hE hMt]
      unfold OutN
      have hfin : ¬ finN f a.toNat b.toNat := fun h => h (Or.inr (Or.inl hI'))
      have c1 : cNanN f a.toNat b.toNat ∨ cInfN f a.toNat b.toNat ∨ (¬ cZeroN f a.toNat b.toNat ∧ ovfN f a.toNat b.toNat) :=
        Or.inr (Or.inl hI')
      have c2 : ¬ (cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1)) :=
        fun h => h.elim hN' (fun h2 => hfin h2.1)
      rw [if_neg hN', if_pos c1, if_neg c2, if_neg hfin, hs]
      simp
    · rw [if_neg hI]
      have hI' : ¬ cInfN f a.toNat b.toNat := hI
      by_cases hZ : isInfF f b ∨ isZeroF f a
      · rw [if_pos hZ]
        have hZ' : cZeroN f a.toNat b.toNat := hZ
        unfold zero
        rw [fields_toNat f _ 0 0 (by omega) hMt]
        unfold OutN
        have hfin : ¬ finN f a.toNat b.toNat := fun h => h (Or.inr (Or.inr (Or.inl hZ')))
        have c1 : ¬ (cNanN f a.toNat b.toNat ∨ cInfN f a.toNat b.toNat ∨
            (¬ cZeroN f a.toNat b.toNat ∧ ovfN f a.toNat b.toNat)) :=
          fun h => h.elim hN' (fun h2 => h2.elim hI' (fun h3 => h3.1 hZ'))
        have c2 : ¬ (cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1)) :=
          fun h => h.elim hN' (fun h2 => hfin h2.1)
        rw [if_neg hN', if_neg c1, if_pos hZ', if_neg c2, if_neg hfin, hs]
        simp
      · rw [if_neg hZ]
        have hZ' : ¬ cZeroN f a.toNat b.toNat := hZ
        have ha : ¬ isNaNF f a := fun h => hN (Or.inl h)
        have hb : ¬ isNaNF f b := fun h => hN (Or.inr (Or.inl h))
        have ha' : ¬ isInfF f a := fun h => hI (Or.inl h)
        have hb0 : ¬ isZeroF f b := fun h => hI (Or.inr h)
        have hb' : ¬ isInfF f b := fun h => hZ (Or.inl h)
        have ha0 : ¬ isZeroF f a := fun h => hZ (Or.inr h)
        obtain ⟨hov, hnov⟩ := fin_cert_model f a b ha ha' ha0 hb hb' hb0
        by_cases hv : ovfN f a.toNat b.toNat
        · have hc := hov hv
          rw [(certF_bridge f a b _ hb0).2 hc]
          unfold infinity
          rw [fields_toNat f _ _ _ hE hMt]
          unfold OutN
          have hfin : ¬ finN f a.toNat b.toNat := fun h => h (Or.inr (Or.inr (Or.inr hv)))
          have c1 : cNanN f a.toNat b.toNat ∨ cInfN f a.toNat b.toNat ∨ (¬ cZeroN f a.toNat b.toNat ∧ ovfN f a.toNat b.toNat) :=
            Or.inr (Or.inr ⟨hZ', hv⟩)
          have c2 : ¬ (cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1)) :=
            fun h => h.elim hN' (fun h2 => hfin h2.1)
          rw [if_neg hN', if_pos c1, if_neg c2, if_neg hfin, hs]
          simp
        · obtain ⟨hmlt, hc⟩ := hnov hv
          rw [(certF_bridge f a b _ hb0).2 hc]
          have hE2 : magN f a.toNat b.toNat / 2 ^ f.t < 2 ^ f.w := by
            apply (Nat.div_lt_iff_lt_mul hMt).2
            rw [Nat.pow_add] at hmlt
            exact hmlt
          have hT2 : magN f a.toNat b.toNat % 2 ^ f.t < 2 ^ f.t := Nat.mod_lt _ hMt
          rw [fields_toNat f _ _ _ hE2 hT2]
          unfold OutN
          have hfin : finN f a.toNat b.toNat := fun h =>
            h.elim hN' (fun h2 => h2.elim hI' (fun h3 => h3.elim hZ' hv))
          obtain ⟨t', ht'⟩ : ∃ t', f.t = t' + 1 := ⟨f.t - 1, by omega⟩
          have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
            have : f.t - 1 = t' := by omega
            rw [this, ht', Nat.pow_succ]; omega
          have fs := Nat.mod_mul (x := magN f a.toNat b.toNat) (a := 2 ^ (f.t - 1)) (b := 2)
          rw [show 2 ^ (f.t - 1) * 2 = 2 ^ f.t by omega] at fs
          have c1 : ¬ (cNanN f a.toNat b.toNat ∨ cInfN f a.toNat b.toNat ∨
              (¬ cZeroN f a.toNat b.toNat ∧ ovfN f a.toNat b.toNat)) :=
            fun h => h.elim hN' (fun h2 => h2.elim hI' (fun h3 => hv h3.2))
          rw [if_neg hN', if_neg c1, if_neg hZ', if_pos hfin, hs]
          by_cases ht : magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1
          · have c2 : cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1) :=
              Or.inr ⟨hfin, ht⟩
            rw [if_pos c2]
            rw [ht] at fs
            omega
          · have c2 : ¬ (cNanN f a.toNat b.toNat ∨ (finN f a.toNat b.toNat ∧ magN f a.toNat b.toNat / 2 ^ (f.t - 1) % 2 = 1)) :=
              fun h => h.elim hN' (fun h2 => ht h2.2)
            rw [if_neg c2]
            rw [Nat.mod_two_ne_one.mp ht] at fs
            omega

end SvGolf.FdivParam

end DpT

/-! # Section `DpU`: The math layer in the task's terms (was `tasks/fdivp/DpU.lean`) -/

section DpU

/-!
# Task `fdivp`: the math layer in the task's own terms (untrusted, kernel-checked)

WP-H3. `OutN_fdivBits`: for every `W, P ≥ 2` and every pair of `(W + P)`-bit patterns, the value of the datapath output
`OutN ⟨W, P⟩` is the value of the trusted task function `fdivBits W P` (`Spec.lean`). This is the theorem a design with
the datapath of `fdivp3.sv` instantiates: its `design.sem W P` outputs `q` equal `OutN ⟨W, P⟩ a b` at every state of
the netlist (the equations of `sv_equations`), hence `q = fdivBits W P a b`.
-/

namespace SvGolf.FdivParam

open SvGolf.IEEE754
open LeanModels.Sv.Lib

theorem OutN_fdivBits (W P : Nat) (h : 2 ≤ W ∧ 2 ≤ P) (a b : BitVec (W + P)) :
    OutN ⟨W, P, h.1, h.2⟩ a.toNat b.toNat = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat := by
  have hk : (⟨W, P, h.1, h.2⟩ : Format).k = W + P := SvGolf.Tasks.FdivP.k_eq W P (by omega)
  have key := OutN_eq ⟨W, P, h.1, h.2⟩ (a.cast hk.symm) (b.cast hk.symm)
  simp only [BitVec.toNat_cast] at key
  rw [SvGolf.Tasks.FdivP.fdivBits_toNat W P h a b]
  exact key

/-- The format instances: binary16, bfloat16-like, binary32. -/
example (a b : BitVec 16) : OutN ⟨5, 11, by decide, by decide⟩ a.toNat b.toNat = (SvGolf.IEEE754.divBinary16 a b).toNat :=
  OutN_fdivBits 5 11 ⟨by decide, by decide⟩ a b

end SvGolf.FdivParam

end DpU

/-! # Section `DpG1`: Glue: the two generate families (was `tasks/fdivp/DpG1.lean`) -/

section DpG1

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Task `fdivp`: the glue for the two generate families (untrusted, kernel-checked)

WP-H3 design layer. `norm_rows` and `div_rows` turn the printed equations of the families `norm` and `div` of
`fdivp3.sv` (as `sv_equations` states them: `rmN`-indexed rows of two-dimensional arrays, context-width conditionals for
the unsized constant `1`) into the `Nat` recurrences of the model: the rows of the normalizer are `normIter` of row 0
(`DpN.lean`), the rows of the divider are `restRem` and the quotient bits are `restQuo` (`SpecFacts.lean`).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four)

theorem normIter_succ' (T Z : Nat) : ∀ (k : Nat) (s : Nat × Nat),
    normIter T Z (k + 1) s = normStep T Z (normIter T Z k s)
  | 0, s => rfl
  | k + 1, s => by
    have h := normIter_succ' T Z k (normStep T Z s)
    show normIter T Z (k + 1) (normStep T Z s) = normStep T Z (normIter T Z (k + 1) s)
    rw [h]
    try rfl

/-- **The normalizer family.** After `i` stages the rows are `normIter` of row 0. -/
theorem norm_rows (P w : Nat) (wI : Int) (hwI : wI = (w : Int)) (hP : 2 ≤ P) (hw : 1 ≤ w)
    (fn fy : Nat → Bool) (n0 y0 : Nat)
    (hn0 : XF.val (fun x => fn x) P = n0) (hy0 : XF.val (fun x => fy x) w = y0)
    (hn : ∀ i : Nat, (i : Int) < (P : Int) + -1 → ∀ k, k < P →
        fn (rmN (P : Int) ((i : Int) + 1) 0 + k) =
          if fn (rmN (P : Int) (i : Int) ((P : Int) + -1)) = true then fn (rmN (P : Int) (i : Int) 0 + k)
          else XF.shlBits (XF.zext P fun x => fn (rmN (P : Int) (i : Int) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (hy : ∀ i : Nat, (i : Int) < (P : Int) + -1 → ∀ k, k < w →
        fy (rmN wI ((i : Int) + 1) 0 + k) =
          if max w (max w 32) < w then
            if fn (rmN (P : Int) (i : Int) ((P : Int) + -1)) = true then
              XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) k
            else
              XF.subBits w (fun x => XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x) w
                (fun x => XF.constBit 1 w x) k
          else
            XF.zext (max w (max w 32))
              (fun x =>
                if fn (rmN (P : Int) (i : Int) ((P : Int) + -1)) = true then
                  XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x
                else
                  XF.subBits (max w (max w 32)) (fun x => XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x)
                    (max w (max w 32)) (fun x => XF.constBit 1 (max w (max w 32)) x) x) k) :
    ∀ i, i ≤ P - 1 → (XF.val (fun x => fn (i * P + x)) P, XF.val (fun x => fy (i * w + x)) w) =
      normIter (P - 1) (2 ^ w) i (n0, y0) := by
  subst hwI
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.zero_add, normIter]
    exact Prod.ext hn0 hy0
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    rw [normIter_succ', ← ih']
    have hlt : (i : Int) < (P : Int) + -1 := by omega
    have hnrow := hn i hlt
    have hyrow := hy i hlt
    simp only [rmN_succ0, rmN_row0, rmN_last_col P i (by omega)] at hnrow hyrow
    -- the current rows
    obtain ⟨rn, hrn⟩ : ∃ rn, XF.val (fun x => fn (i * P + x)) P = rn := ⟨_, rfl⟩
    obtain ⟨ry, hry⟩ : ∃ ry, XF.val (fun x => fy (i * w + x)) w = ry := ⟨_, rfl⟩
    have hrnlt : rn < 2 ^ P := hrn ▸ XF.val_lt _ P
    have hrylt : ry < 2 ^ w := hry ▸ XF.val_lt _ w
    have hc : fn (i * P + (P - 1)) = true ↔ 2 ^ (P - 1) ≤ rn :=
      top_bit_iff (fun x => fn (i * P + x)) P rn (by omega) hrn
    rw [hrn, hry]
    show (XF.val _ P, XF.val _ w) = normStep (P - 1) (2 ^ w) (rn, ry)
    have hPe : P - 1 + 1 = P := by omega
    have hn' : XF.val (fun x => fn ((i + 1) * P + x)) P =
        if fn (i * P + (P - 1)) = true then rn else (rn * 2) % 2 ^ P := by
      rw [XF.val_congr_lt (g := fun k => if fn (i * P + (P - 1)) = true then fn (i * P + k)
        else XF.shlBits (XF.zext P fun x => fn (i * P + x)) 32 (fun x => XF.constBit 1 32 x) k)
        (fun j hj => hnrow j hj)]
      rw [val_ite, val_shlBits_one _ _ 32 (by omega), hrn]
    have hM : ¬ (max w (max w 32) < w) := by omega
    have hy' : XF.val (fun x => fy ((i + 1) * w + x)) w =
        if fn (i * P + (P - 1)) = true then ry else (ry + (2 ^ w - 1)) % 2 ^ w := by
      rw [XF.val_congr_lt (g := fun k => if fn (i * P + (P - 1)) = true then
            XF.zext w (fun k => fy (i * w + k)) k
          else XF.subBits (max w (max w 32)) (fun x => XF.zext w (fun k => fy (i * w + k)) x)
            (max w (max w 32)) (fun x => XF.constBit 1 (max w (max w 32)) x) k)
        (fun j hj => by
          rw [hyrow j hj, if_neg hM]
          have hjM : j < max w (max w 32) := by omega
          simp [XF.zext, hjM, hj])]
      rw [val_ite]
      have h1 : XF.val (fun k => XF.zext w (fun k => fy (i * w + k)) k) w = ry := by
        rw [XF.val_zext w _ w (Nat.le_refl w)]; exact hry
      have h2 : XF.val (fun k => XF.subBits (max w (max w 32)) (fun x => XF.zext w (fun k => fy (i * w + k)) x)
            (max w (max w 32)) (fun x => XF.constBit 1 (max w (max w 32)) x) k) w =
          (ry + (2 ^ w - 1)) % 2 ^ w := by
        rw [val_subBits]
        have hwM : w ≤ max w (max w 32) := by omega
        have hz : XF.val (fun x => XF.zext w (fun k => fy (i * w + k)) x) (max w (max w 32)) = ry := by
          rw [XF.val_zext w _ _ hwM]; exact hry
        have hc1 : XF.val (fun x => XF.constBit 1 (max w (max w 32)) x) (max w (max w 32)) = 1 :=
          val_constBit_one (max w (max w 32)) (max w (max w 32)) (by omega) (Nat.le_refl _)
        rw [hz, hc1, Nat.max_self]
        exact add_two_pow_sub_mod_two_pow ry 1 w _ (by have := Nat.two_pow_pos w; omega) hwM
      rw [h1, h2]
    rw [hn', hy']
    unfold normStep
    by_cases hb : fn (i * P + (P - 1)) = true
    · have h2T : 2 ^ (P - 1) ≤ rn := hc.1 hb
      simp [hb, h2T]
    · have h2T : ¬ 2 ^ (P - 1) ≤ rn := fun h => hb (hc.2 h)
      simp only [hb, h2T, Bool.false_eq_true, if_false]
      have e2 : 2 ^ (P - 1 + 1) = 2 ^ P := by rw [hPe]
      rw [e2, Nat.mul_comm 2 rn]

/-! ## The restoring divider -/

/-- **The divider family.** The rows of `rr` are `restRem` and the bits of `qq` are the digits (`restQuo`). -/
theorem div_rows (P : Nat) (rr dd qq nbx : Nat → Bool) (na nb : Nat) (hP : 2 ≤ P)
    (hnb0 : 0 < nb) (hnbP : nb < 2 ^ P) (hna : na < 2 * nb)
    (hnbv : XF.val (fun x => nbx x) (P + 1) = nb)
    (hr0 : XF.val (fun x => rr x) (P + 1) = na)
    (hqq : ∀ i : Nat, (i : Int) < (P : Int) + 2 →
        qq ((P : Int) + -1 * (i : Int) + 1).toNat =
          decide (XF.val (fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) (P + 1) ≥
            XF.val (fun x => nbx x) (P + 1)))
    (hdd : ∀ i : Nat, (i : Int) < (P : Int) + 2 → ∀ k, k < P + 1 →
        dd (rmN ((P : Int) + 1) (i : Int) 0 + k) =
          XF.subBits (P + 1) (fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) (P + 1) (fun x => nbx x) k)
    (hrr : ∀ i : Nat, (i : Int) < (P : Int) + 2 → ∀ k, k < P + 1 →
        rr (rmN ((P : Int) + 1) ((i : Int) + 1) 0 + k) =
          if qq ((P : Int) + -1 * (i : Int) + 1).toNat = true then
            XF.shlBits (XF.zext (P + 1) fun x => dd (rmN ((P : Int) + 1) (i : Int) 0 + x)) 32
              (fun x => XF.constBit 1 32 x) k
          else
            XF.shlBits (XF.zext (P + 1) fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) 32
              (fun x => XF.constBit 1 32 x) k) :
    (∀ i, i ≤ P + 2 → XF.val (fun x => rr (i * (P + 1) + x)) (P + 1) = restRem nb na i) ∧
    XF.val (fun k => qq k) (P + 2) = restQuo nb na (P + 2) := by
  have hP1 : ((P : Int) + 1).toNat = P + 1 := by omega
  have hrow0 : ∀ (i : Nat), rmN ((P : Int) + 1) (i : Int) 0 = i * (P + 1) := by
    intro i
    have h1 : (i : Int).toNat = i := by omega
    unfold rmN; rw [h1, hP1]; rfl
  have hrow1 : ∀ (i : Nat), rmN ((P : Int) + 1) ((i : Int) + 1) 0 = (i + 1) * (P + 1) := by
    intro i
    have h1 : ((i : Int) + 1).toNat = i + 1 := by omega
    unfold rmN; rw [h1, hP1]; rfl
  have hZ : 2 ^ (P + 1) = 2 * 2 ^ P := by rw [Nat.pow_succ]; omega
  have hinv := restore_inv nb na hna
  have hrows : ∀ i, i ≤ P + 2 → XF.val (fun x => rr (i * (P + 1) + x)) (P + 1) = restRem nb na i := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [Nat.zero_mul, Nat.zero_add, restRem]
      exact hr0
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hlt : (i : Int) < (P : Int) + 2 := by omega
      have hqrow := hqq i hlt
      have hdrow := hdd i hlt
      have hrrow := hrr i hlt
      simp only [hrow0, hrow1, hnbv] at hqrow hdrow hrrow
      have hidx : ((P : Int) + -1 * (i : Int) + 1).toNat = P + 1 - i := by omega
      rw [hidx, ih'] at hqrow
      rw [hidx] at hrrow
      have hr := (hinv i).1
      have hnbZ : nb < 2 ^ (P + 1) := by omega
      -- the row of dd
      have hdv : XF.val (fun x => dd (i * (P + 1) + x)) (P + 1) = (restRem nb na i + (2 ^ (P + 1) - nb)) % 2 ^ (P + 1) := by
        rw [XF.val_congr_lt (fun j hj => hdrow j hj), val_subBits, Nat.max_self, ih', hnbv]
      have hqb : qq (P + 1 - i) = decide (nb ≤ restRem nb na i) := by
        rw [hqrow]
      rw [XF.val_congr_lt (fun j hj => hrrow j hj)]
      simp only [restRem]
      by_cases hge : nb ≤ restRem nb na i
      · have hq : qq (P + 1 - i) = true := by rw [hqb]; simpa using hge
        simp only [hq, if_true, if_pos hge]
        rw [val_shlBits_one _ _ 32 (by omega), hdv]
        have e : restRem nb na i + (2 ^ (P + 1) - nb) = (restRem nb na i - nb) + 2 ^ (P + 1) := by omega
        rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : restRem nb na i - nb < 2 ^ (P + 1)),
          Nat.mod_eq_of_lt (by omega : (restRem nb na i - nb) * 2 < 2 ^ (P + 1))]
        omega
      · have hq : qq (P + 1 - i) = false := by rw [hqb]; simpa using hge
        simp only [hq, Bool.false_eq_true, if_false, if_neg hge]
        rw [val_shlBits_one _ _ 32 (by omega), ih']
        rw [Nat.mod_eq_of_lt (by omega : restRem nb na i * 2 < 2 ^ (P + 1))]
        omega
  refine ⟨hrows, ?_⟩
  rw [← val_restQuo nb na (P + 2)]
  apply XF.val_congr_lt
  intro k hk
  have hq := hqq (P + 1 - k) (by omega)
  have hidx : ((P : Int) + -1 * ((P + 1 - k : Nat) : Int) + 1).toNat = k := by omega
  rw [hidx] at hq
  simp only [hrow0, hnbv] at hq
  rw [hrows (P + 1 - k) (by omega)] at hq
  rw [hq]
  have e : P + 2 - 1 - k = P + 1 - k := by omega
  rw [e]

end Glue
end SvGolf.FdivParam

end DpG1

/-! # Section `DpG2`: Glue: unpacking, classification, row 0, extensions (was `tasks/fdivp/DpG2.lean`) -/

section DpG2

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Task `fdivp`: the glue for the unpacking and classification sites, the row-0 sites and the extension sites

WP-H3 design layer. One lemma per SHAPE of the printed equations of `fdivp3.sv` (`sv_equations`): the equation is the
hypothesis `h`, in its printed form with the Int-typed widths and offsets abstracted to `Nat` variables (`n`, `m`, ...)
whose values are side conditions (`omega` at the use site, after the unifier has read them off the equation); the
conclusion is the value of the signal in the terms of the `Nat` model of `DpQ.lean`.
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four)
open SvGolf.IEEE754

/-! ## Unpack and classify -/

theorem g_s (f : Format) (av bv j : Nat) (fs fa fb : Nat → Bool) (hj : j + 1 = f.w + f.p)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hb : ∀ k, k < f.w + f.p → fb k = bv.testBit k)
    (h : fs 0 = (fa j ^^ fb j)) :
    fs 0 = decide ((sF f av + sF f bv) % 2 = 1) := by
  have hfp := f.hp
  have ht : f.t = f.p - 1 := rfl
  have e : f.w + f.t = j := by omega
  unfold sF
  rw [e, h, ha j (by omega), hb j (by omega), Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have h1 : av / 2 ^ j % 2 = 0 ∨ av / 2 ^ j % 2 = 1 := by omega
  have h2 : bv / 2 ^ j % 2 = 0 ∨ bv / 2 ^ j % 2 = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

theorem g_nz (f : Format) (av n m : Nat) (fe fa : Nat → Bool) (hn : n = f.w) (hm : m = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k)
    (h : fe 0 = XF.any n fun x => fa (m + x)) :
    fe 0 = decide (eF f av ≠ 0) := by
  have hfp := f.hp
  subst hn hm
  rw [h, any_eq_decide_val, val_window_of_testBit fa av (f.p - 1) f.w (fun j hj => ha j (by omega))]
  try rfl

theorem g_all (f : Format) (av n m : Nat) (fa : Nat → Bool) (hn : n = f.w) (hm : m = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) :
    (XF.all n fun x => fa (m + x)) = decide (eF f av = 2 ^ f.w - 1) := by
  have hfp := f.hp
  subst hn hm
  rw [all_eq_decide_val, val_window_of_testBit fa av (f.p - 1) f.w (fun j hj => ha j (by omega))]
  try rfl

theorem g_any0 (f : Format) (av n : Nat) (fa : Nat → Bool) (hn : n = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) :
    (XF.any n fun x => fa x) = decide (fF f av ≠ 0) := by
  have hfp := f.hp
  subst hn
  rw [any_eq_decide_val, val_of_testBit (w := f.p - 1) (fun j hj => ha j (by omega))]
  try rfl

theorem g_cnan (f : Format) (av bv n1 m1 n2 : Nat) (fcn fea feb fa fb : Nat → Bool)
    (hn1 : n1 = f.w) (hm1 : m1 = f.p - 1) (hn2 : n2 = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hb : ∀ k, k < f.w + f.p → fb k = bv.testBit k)
    (hea : fea 0 = decide (eF f av ≠ 0)) (heb : feb 0 = decide (eF f bv ≠ 0))
    (h : fcn 0 =
      (((((XF.all n1 fun x => fa (m1 + x)) && XF.any n2 fun x => fa x) ||
            (XF.all n1 fun x => fb (m1 + x)) && XF.any n2 fun x => fb x) ||
          (((XF.all n1 fun x => fa (m1 + x)) && !XF.any n2 fun x => fa x) && XF.all n1 fun x => fb (m1 + x)) &&
            !XF.any n2 fun x => fb x) ||
        (!fea 0 && !XF.any n2 fun x => fa x) && !feb 0 && !XF.any n2 fun x => fb x)) :
    fcn 0 = decide (cNanN f av bv) := by
  have ga_all := g_all f av n1 m1 fa hn1 hm1 ha
  have gb_all := g_all f bv n1 m1 fb hn1 hm1 hb
  have ga_any := g_any0 f av n2 fa hn2 ha
  have gb_any := g_any0 f bv n2 fb hn2 hb
  rw [h, ga_all, gb_all, ga_any, gb_any, hea, heb, Bool.eq_iff_iff]
  simp [cNanN, nanN, infN, zeroN] <;> first | omega | grind

theorem g_cinf (f : Format) (av bv n1 m1 n2 : Nat) (fci fea feb fa fb : Nat → Bool)
    (hn1 : n1 = f.w) (hm1 : m1 = f.p - 1) (hn2 : n2 = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hb : ∀ k, k < f.w + f.p → fb k = bv.testBit k)
    (heb : feb 0 = decide (eF f bv ≠ 0))
    (h : fci 0 =
      (((XF.all n1 fun x => fa (m1 + x)) && !XF.any n2 fun x => fa x) || !feb 0 && !XF.any n2 fun x => fb x)) :
    fci 0 = decide (cInfN f av bv) := by
  have ga_all := g_all f av n1 m1 fa hn1 hm1 ha
  have ga_any := g_any0 f av n2 fa hn2 ha
  have gb_any := g_any0 f bv n2 fb hn2 hb
  rw [h, ga_all, ga_any, gb_any, heb, Bool.eq_iff_iff]
  simp [cInfN, infN, zeroN] <;> first | omega | grind

theorem g_czero (f : Format) (av bv n1 m1 n2 : Nat) (fcz fea feb fa fb : Nat → Bool)
    (hn1 : n1 = f.w) (hm1 : m1 = f.p - 1) (hn2 : n2 = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hb : ∀ k, k < f.w + f.p → fb k = bv.testBit k)
    (hea : fea 0 = decide (eF f av ≠ 0))
    (h : fcz 0 =
      (((XF.all n1 fun x => fb (m1 + x)) && !XF.any n2 fun x => fb x) || !fea 0 && !XF.any n2 fun x => fa x)) :
    fcz 0 = decide (cZeroN f av bv) := by
  have gb_all := g_all f bv n1 m1 fb hn1 hm1 hb
  have ga_any := g_any0 f av n2 fa hn2 ha
  have gb_any := g_any0 f bv n2 fb hn2 hb
  rw [h, gb_all, ga_any, gb_any, hea, Bool.eq_iff_iff]
  simp [cZeroN, infN, zeroN] <;> first | omega | grind

/-! ## Row 0 of the normalizer -/

theorem g_n0 (f : Format) (av m : Nat) (hm : m = f.p - 1) (fn fa fe : Nat → Bool)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hea : fe 0 = decide (eF f av ≠ 0))
    (h : ∀ k, k < f.p → fn k = if k < m then fa k else fe (k - m)) :
    XF.val (fun x => fn x) f.p = sigN f av := by
  have hfp := f.hp
  have hP1 : f.p = m + 1 := by omega
  have ht : f.t = m := by simp only [Format.t]; omega
  have hlow := val_of_testBit (w := m) (fun j hj => ha j (by omega))
  have h1 : XF.val fe 1 = (fe 0).toNat := val_one fe
  rw [XF.val_congr_lt (fun j hj => h j hj), hP1, val_cat fa fe m 1, hlow, h1, hea]
  unfold sigN fF
  rw [ht]
  by_cases hz : eF f av = 0
  · simp [hz]
  · simp [hz] <;> omega

theorem g_y0 (f : Format) (av n m w : Nat) (hn : n = f.w) (hm : m = f.p - 1) (hw : w = f.w + f.p + 1)
    (fy fa fe : Nat → Bool) (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k)
    (hea : fe 0 = decide (eF f av ≠ 0))
    (h : ∀ k, k < w → fy k =
      if max n 32 < w then
        (if fe 0 = true then XF.zext n (fun x => fa (m + x)) k else XF.constBit 1 w k)
      else
        XF.zext (max n 32) (fun x =>
          if fe 0 = true then XF.zext n (fun x => fa (m + x)) x else XF.constBit 1 (max n 32) x) k) :
    XF.val (fun x => fy x) w = xeN f av := by
  have hfp := f.hp
  have hfw := f.hw
  subst hn hm hw
  have ht : f.t = f.p - 1 := rfl
  have hwin : XF.val (fun x => fa (f.p - 1 + x)) f.w = eF f av := by
    rw [val_window_of_testBit fa av (f.p - 1) f.w (fun j hj => ha j (by omega))]
    rfl
  have key : ∀ W', f.w + f.p + 1 ≤ W' →
      XF.val (fun x => if fe 0 = true then XF.zext f.w (fun x => fa (f.p - 1 + x)) x else XF.constBit 1 W' x)
        (f.w + f.p + 1) = if fe 0 = true then eF f av else 1 := by
    intro W' h1
    rw [val_ite]
    have e1 := XF.val_zext f.w (fun x => fa (f.p - 1 + x)) (f.w + f.p + 1) (by omega)
    have e2 := val_constBit_one W' (f.w + f.p + 1) (by omega) h1
    rw [e1, e2, hwin]
  have fin : (if fe 0 = true then eF f av else 1) = xeN f av := by
    unfold xeN
    rw [hea]
    by_cases hz : eF f av = 0
    · simp [hz]
    · simp [hz]
  by_cases hc : max f.w 32 < f.w + f.p + 1
  · rw [XF.val_congr_lt (fun j hj => (h j hj).trans (if_pos hc))]
    rw [key (f.w + f.p + 1) (by omega)]
    exact fin
  · rw [XF.val_congr_lt (fun j hj => (h j hj).trans (if_neg hc))]
    rw [val_zext_trunc (max f.w 32) (f.w + f.p + 1) _ (by omega)]
    rw [key (max f.w 32) (by omega)]
    exact fin

/-! ## The extension sites `{1'b0, x}` -/

theorem g_ext (P r nbv : Nat) (fx fn : Nat → Bool)
    (hv : XF.val (fun x => fn (r + x)) P = nbv)
    (h : ∀ k, k < P + 1 → fx k = if k < P then fn (r + k) else false) :
    XF.val (fun x => fx x) (P + 1) = nbv := by
  have htop : (if P < P then fn (r + P) else false) = false := if_neg (Nat.lt_irrefl P)
  rw [XF.val_congr_lt (fun j hj => h j hj), val_succ, htop, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, ← hv]
  exact XF.val_congr_lt (fun j hj => by simp [hj])

end Glue
end SvGolf.FdivParam

end DpG2

/-! # Section `DpG3`: Glue: quotient, exponent, shifter, rounding, output sites (was `tasks/fdivp/DpG3.lean`) -/

section DpG3

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Task `fdivp`: the glue for the quotient, exponent, shifter, rounding and output sites

WP-H3 design layer, continued (`DpG2.lean`): the value lemmas of the sites `adj`, `qm`, `onesW`, `emw`, `E`, `ovf`,
`dsh`, `qs`, `inc`, `ef`, `mag` and the four output sites, in the same style (the printed equation is the hypothesis `h`).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four)
open SvGolf.IEEE754

/-! ## Quotient normalization -/

theorem g_adj (P qqv : Nat) (fadj fqq : Nat → Bool)
    (hq : XF.val fqq (P + 2) = qqv)
    (h : fadj 0 = !fqq (P + 1)) :
    (fadj 0).toNat = if 2 ^ (P + 1) ≤ qqv then 0 else 1 := by
  have ht := top_bit_succ_iff fqq (P + 1) qqv hq
  by_cases hc : 2 ^ (P + 1) ≤ qqv
  · have hb : fqq (P + 1) = true := ht.2 hc
    rw [h, hb, if_pos hc]
    try rfl
  · have hb : fqq (P + 1) = false := by
      cases hh : fqq (P + 1)
      · rfl
      · exact absurd (ht.1 hh) hc
    rw [h, hb, if_neg hc]
    try rfl

theorem g_qm (P one qqv : Nat) (hone : one = 1) (fqm fqq : Nat → Bool)
    (hq : XF.val fqq (P + 2) = qqv)
    (h : ∀ k, k < P + 1 → fqm k = if fqq (P + 1) = true then fqq (one + k) else fqq k) :
    XF.val (fun x => fqm x) (P + 1) = if 2 ^ (P + 1) ≤ qqv then qqv / 2 else qqv := by
  subst hone
  have ht := top_bit_succ_iff fqq (P + 1) qqv hq
  have hlt : qqv < 2 ^ (P + 2) := by
    have hl := XF.val_lt fqq (P + 2)
    rw [hq] at hl
    exact hl
  have hP2 : 2 ^ (P + 2) = 2 * 2 ^ (P + 1) := Nat.pow_succ' (n := P + 1)
  rw [XF.val_congr_lt (fun j hj => h j hj), val_ite]
  by_cases hc : 2 ^ (P + 1) ≤ qqv
  · have hb : fqq (P + 1) = true := ht.2 hc
    rw [if_pos hb, if_pos hc]
    rw [val_window fqq 1 (P + 1) (P + 2) (by omega), hq, Nat.pow_one]
    exact Nat.mod_eq_of_lt (by omega)
  · have hb : ¬ fqq (P + 1) = true := fun hh => hc (ht.1 hh)
    rw [if_neg hb, if_neg hc]
    rw [val_prefix fqq (P + 2) (P + 1) (by omega), hq]
    exact Nat.mod_eq_of_lt (by omega)

/-! ## The exponent -/

theorem g_emw (f : Format) (n : Nat) (hn : n = f.w) (femw fones : Nat → Bool) (h1 : ∀ k, k < n → fones k = true)
    (h : ∀ k, k < n → femw k = XF.shrBits n (fun x => fones x) 32 (fun x => XF.constBit 1 32 x) k) :
    XF.val (fun x => femw x) n = f.emax := by
  have hfw := f.hw
  rw [XF.val_congr_lt (fun j hj => h j hj), val_shrBits, val_all_true (fun x => fones x) n h1, val_constBit_one 32 32 (by omega) (Nat.le_refl _)]
  unfold Format.emax
  obtain ⟨t, ht⟩ : ∃ t, f.w = t + 1 := ⟨f.w - 1, by omega⟩
  have hp : 2 ^ (t + 1) = 2 * 2 ^ t := Nat.pow_succ' (n := t)
  have hpos := Nat.two_pow_pos t
  have e : t + 1 - 1 = t := by omega
  rw [hn, ht, e, Nat.pow_one, hp]
  omega

theorem g_E (EW nw Z rA rB yav ybv emv adjv : Nat) (fE fya fyb femw fadj : Nat → Bool)
    (hZ : 2 ^ EW = Z) (hEW : 1 ≤ EW) (hnw : nw ≤ EW)
    (hya : XF.val (fun x => fya (rA + x)) EW = yav) (hyb : XF.val (fun x => fyb (rB + x)) EW = ybv)
    (hem : XF.val femw nw = emv) (hadj : (fadj 0).toNat = adjv)
    (h : ∀ k, k < EW → fE k =
      XF.subBits EW
        (fun x => XF.addBits EW
          (fun x => XF.subBits EW (fun x => fya (rA + x)) EW (fun x => fyb (rB + x)) x) EW
          (fun x => XF.zext nw (fun k => femw k) x) x)
        EW (fun x => XF.zext 1 (fun k => fadj k) x) k) :
    XF.val (fun x => fE x) EW = (((yav + (Z - ybv)) % Z + emv) % Z + (Z - adjv)) % Z := by
  subst hZ
  rw [XF.val_congr_lt (fun j hj => h j hj), val_subBits, Nat.max_self, val_addBits, val_subBits, Nat.max_self,
    hya, hyb, XF.val_zext nw (fun k => femw k) EW hnw, hem, XF.val_zext 1 (fun k => fadj k) EW hEW, val_one, hadj]

theorem flag_nrm (f : Format) (fE : Nat → Bool) (n Ev EW : Nat) (hn : n = f.w + f.p) (hEW : EW = f.w + f.p + 1)
    (hEv : XF.val fE EW = Ev) :
    (!fE n && XF.any EW fun x => fE x) = decide (nrmE f Ev) := by
  subst hn hEW
  have hbit : fE (f.w + f.p) = decide (Ev / 2 ^ (f.w + f.p) % 2 = 1) :=
    bit_eq_of_val fE (f.w + f.p + 1) Ev (f.w + f.p) hEv (by omega)
  rw [any_eq_decide_val, hEv, hbit, Bool.eq_iff_iff]
  simp [nrmE] <;> first | omega | grind

theorem g_ovf (f : Format) (Ev n m1 m2 : Nat) (fovf fE : Nat → Bool)
    (hn : n = f.w + f.p) (hm1 : m1 = f.p) (hm2 : m2 = f.w)
    (hEv : XF.val fE (f.w + f.p + 1) = Ev)
    (h : fovf 0 = (!fE n && ((XF.any m1 fun x => fE (f.w + x)) || XF.all m2 fun x => fE x))) :
    fovf 0 = decide (ovfE f Ev) := by
  subst hn hm1 hm2
  have hbit : fE (f.w + f.p) = decide (Ev / 2 ^ (f.w + f.p) % 2 = 1) :=
    bit_eq_of_val fE (f.w + f.p + 1) Ev (f.w + f.p) hEv (by omega)
  have hEt : ∀ j, j < f.w + f.p + 1 → fE j = Ev.testBit j := fun j hj => by
    rw [← hEv, XF.testBit_val fE _ j hj]
  have hany : (XF.any f.p fun x => fE (f.w + x)) = decide (Ev / 2 ^ f.w % 2 ^ f.p ≠ 0) := by
    rw [any_eq_decide_val, val_window_of_testBit fE Ev f.w f.p (fun j hj => hEt j (by omega))]
  have hall : (XF.all f.w fun x => fE x) = decide (Ev % 2 ^ f.w = 2 ^ f.w - 1) := by
    rw [all_eq_decide_val, val_of_testBit (w := f.w) (fun j hj => hEt j (by omega))]
  rw [h, hbit, hany, hall, Bool.eq_iff_iff]
  simp [ovfE] <;> first | omega | grind

theorem g_dsh (f : Format) (Ev n EW : Nat) (fdsh fE : Nat → Bool)
    (hn : n = f.w + f.p) (hEW : EW = f.w + f.p + 1)
    (hEv : XF.val fE EW = Ev)
    (h : ∀ k, k < EW → fdsh k =
      if max 32 (max 32 EW) < EW then
        (if (!fE n && XF.any EW fun x => fE x) = true then XF.constBit 0 EW k
         else XF.subBits EW (fun x => XF.constBit 1 EW x) EW (fun x => XF.zext EW (fun x => fE x) x) k)
      else
        XF.zext (max 32 (max 32 EW)) (fun x =>
          if (!fE n && XF.any EW fun x => fE x) = true then XF.constBit 0 (max 32 (max 32 EW)) x
          else XF.subBits (max 32 (max 32 EW)) (fun x => XF.constBit 1 (max 32 (max 32 EW)) x)
            (max 32 (max 32 EW)) (fun x => XF.zext EW (fun x => fE x) x) x) k) :
    XF.val (fun x => fdsh x) EW = dshE f Ev := by
  have hflag := flag_nrm f fE n Ev EW hn hEW hEv
  have hfw := f.hw
  have hEvlt : Ev < 2 ^ EW := by
    have hl := XF.val_lt fE EW
    rw [hEv] at hl
    exact hl
  obtain ⟨Mx, hMx⟩ : ∃ Mx, Mx = max 32 (max 32 EW) := ⟨_, rfl⟩
  rw [← hMx] at h
  have hc : ¬ (Mx < EW) := by omega
  have hM1 : EW ≤ Mx := by omega
  rw [XF.val_congr_lt (fun j hj => (h j hj).trans (if_neg hc))]
  rw [val_zext_trunc Mx EW _ hM1, val_ite, val_constBit_zero]
  have e2 : XF.val (fun k => XF.subBits Mx (fun x => XF.constBit 1 Mx x) Mx
      (fun x => XF.zext EW (fun x => fE x) x) k) EW = (1 + (2 ^ EW - Ev)) % 2 ^ EW := by
    rw [val_subBits, Nat.max_self, val_constBit_one Mx Mx (by omega) (Nat.le_refl _),
      XF.val_zext EW (fun x => fE x) Mx hM1, hEv]
    exact add_two_pow_sub_mod_two_pow 1 Ev EW Mx (Nat.le_of_lt hEvlt) hM1
  rw [e2, hflag]
  unfold dshE ZN
  rw [← hEW]
  by_cases hnr : nrmE f Ev <;> simp [hnr]

theorem g_qs (P EW qmv dv : Nat) (fqs fqm fdsh : Nat → Bool)
    (hqm : XF.val fqm (P + 1) = qmv) (hd : XF.val fdsh EW = dv)
    (h : ∀ k, k < P + 1 → fqs k = XF.shrBits (P + 1) (fun x => fqm x) EW (fun x => fdsh x) k) :
    XF.val (fun x => fqs x) (P + 1) = qmv / 2 ^ dv := by
  rw [XF.val_congr_lt (fun j hj => h j hj), val_shrBits, hqm, hd]

/-! ## Rounding -/

theorem g_eqv (P EW qsv qmv dv : Nat) (fqs fqm fdsh : Nat → Bool)
    (hqs : XF.val fqs (P + 1) = qsv) (hqm : XF.val fqm (P + 1) = qmv) (hd : XF.val fdsh EW = dv)
    (hqsd : qsv = qmv / 2 ^ dv) (hlt : qmv < 2 ^ (P + 1)) :
    XF.eqv (P + 1) (fun x => XF.shlBits (XF.zext (P + 1) fun x => fqs x) EW (fun x => fdsh x) x) (fun x => fqm x)
      = decide (qmv % 2 ^ dv = 0) := by
  rw [eqv_eq_decide_val, val_shlBits_zext, hqs, hd, hqm]
  subst hqsd
  have hdm := Nat.div_add_mod qmv (2 ^ dv)
  have hcomm : qmv / 2 ^ dv * 2 ^ dv = 2 ^ dv * (qmv / 2 ^ dv) := Nat.mul_comm _ _
  have hle : qmv / 2 ^ dv * 2 ^ dv ≤ qmv := Nat.div_mul_le_self qmv (2 ^ dv)
  have hlt' : qmv / 2 ^ dv * 2 ^ dv < 2 ^ (P + 1) := by omega
  rw [Nat.mod_eq_of_lt hlt', decide_eq_decide]
  constructor <;> intro h <;> omega

theorem g_inc (P EW rr0 qsv qmv qqv rrv dv one : Nat) (hone : one = 1) (hP : 1 ≤ P)
    (fqs fqm fdsh fqq frr finc : Nat → Bool)
    (hqs : XF.val fqs (P + 1) = qsv) (hqm : XF.val fqm (P + 1) = qmv) (hd : XF.val fdsh EW = dv)
    (hqq : XF.val fqq (P + 2) = qqv) (hrr : XF.val (fun x => frr (rr0 + x)) (P + 1) = rrv)
    (hqsd : qsv = qmv / 2 ^ dv) (hlt : qmv < 2 ^ (P + 1))
    (h : finc 0 = (fqs 0 && (((fqq (P + 1) && fqq 0 || XF.any (P + 1) fun x => frr (rr0 + x)) ||
          !XF.eqv (P + 1) (fun x => XF.shlBits (XF.zext (P + 1) fun x => fqs x) EW (fun x => fdsh x) x)
            fun x => fqm x) || fqs one))) :
    finc 0 = decide (qsv % 2 = 1 ∧ ((2 ^ (P + 1) ≤ qqv ∧ qqv % 2 = 1 ∨ rrv ≠ 0) ∨
      qmv % 2 ^ dv ≠ 0 ∨ qsv / 2 % 2 = 1)) := by
  subst hone
  have hq0 : fqs 0 = decide (qsv % 2 = 1) := by
    have := bit_eq_of_val fqs (P + 1) qsv 0 hqs (by omega)
    simpa using this
  have hq1 : fqs 1 = decide (qsv / 2 % 2 = 1) := by
    have := bit_eq_of_val fqs (P + 1) qsv 1 hqs (by omega)
    simpa using this
  have hqqtop : fqq (P + 1) = decide (2 ^ (P + 1) ≤ qqv) := by
    have := top_bit_succ_iff fqq (P + 1) qqv hqq
    by_cases hc : 2 ^ (P + 1) ≤ qqv
    · rw [this.2 hc]; simp [hc]
    · have hb : ¬ fqq (P + 1) = true := fun hh => hc (this.1 hh)
      simp at hb
      rw [hb]; simp [hc]
  have hqq0 : fqq 0 = decide (qqv % 2 = 1) := by
    have := bit_eq_of_val fqq (P + 2) qqv 0 hqq (by omega)
    simpa using this
  have hany : (XF.any (P + 1) fun x => frr (rr0 + x)) = decide (rrv ≠ 0) := by
    rw [any_eq_decide_val, hrr]
  have heqv := g_eqv P EW qsv qmv dv fqs fqm fdsh hqs hqm hd hqsd hlt
  rw [h, hq0, hq1, hqqtop, hqq0, hany, heqv, Bool.eq_iff_iff]
  simp <;> first | omega | grind

theorem g_ef (f : Format) (Ev n EW nw n1 : Nat) (fef fE : Nat → Bool)
    (hn : n = f.w + f.p) (hEW : EW = f.w + f.p + 1) (hnw : nw = f.w) (hn1 : n1 = f.w)
    (hEv : XF.val fE EW = Ev)
    (h : ∀ k, k < nw → fef k =
      if max n1 32 < nw then
        (if (!fE n && XF.any EW fun x => fE x) = true then XF.zext n1 (fun x => fE x) k else XF.constBit 0 nw k)
      else
        XF.zext (max n1 32) (fun x =>
          if (!fE n && XF.any EW fun x => fE x) = true then XF.zext n1 (fun x => fE x) x
          else XF.constBit 0 (max n1 32) x) k) :
    XF.val (fun x => fef x) f.w = if nrmE f Ev then Ev % 2 ^ f.w else 0 := by
  have hflag := flag_nrm f fE n Ev EW hn hEW hEv
  have hfw := f.hw
  have hwEW : f.w ≤ EW := by omega
  subst hnw hn1
  have hc : ¬ (max f.w 32 < f.w) := by omega
  rw [XF.val_congr_lt (fun j hj => (h j hj).trans (if_neg hc))]
  rw [val_zext_trunc (max f.w 32) f.w _ (by omega), val_ite, XF.val_zext f.w (fun x => fE x) f.w (Nat.le_refl _),
    val_constBit_zero, hflag]
  have hv : XF.val (fun x => fE x) f.w = Ev % 2 ^ f.w := by
    rw [val_prefix fE EW f.w hwEW, hEv]
  rw [hv]
  by_cases hnr : nrmE f Ev <;> simp [hnr]

theorem g_mag (t w M pm one P qsv efv incv : Nat) (hM : M = t + w) (hpm : pm = t) (hone : one = 1)
    (hP : t + 1 = P) (hw1 : 1 ≤ w) (fmag fqs fef finc : Nat → Bool)
    (hqs : XF.val fqs (P + 1) = qsv) (hef : XF.val fef w = efv) (hinc : (finc 0).toNat = incv)
    (h : ∀ k, k < M → fmag k =
      XF.addBits M (fun x => if x < pm then fqs (one + x) else fef (x - pm)) M
        (fun x => XF.zext 1 (fun k => finc k) x) k) :
    XF.val (fun x => fmag x) M = (efv * 2 ^ t + qsv / 2 % 2 ^ t + incv) % 2 ^ (w + t) := by
  subst hM hone
  rw [hpm] at h
  have e1 := val_cat (fun x => fqs (1 + x)) fef t w
  have e2 := val_window fqs 1 t (P + 1) (by omega)
  rw [XF.val_congr_lt (fun j hj => h j hj), val_addBits, e1, e2, hqs, Nat.pow_one, hef,
    XF.val_zext 1 (fun k => finc k) (t + w) (by omega), val_one, hinc, Nat.mul_comm (2 ^ t) efv, Nat.add_comm w t]
  congr 1
  omega

/-! ## The output -/

theorem g_qfield (nm n0 T w : Nat) (cn ci cz ov : Bool) (fq fones fmag : Nat → Bool)
    (hnm : nm = n0) (hnw : n0 = w) (hones : ∀ k, k < nm → fones k = true)
    (h : ∀ k, k < n0 → fq (T + k) =
      if max nm (max 32 n0) < n0 then
        (if (cn || ci || !cz && ov) = true then XF.zext nm (fun x => fones x) k
         else if cz = true then XF.constBit 0 n0 k else XF.zext n0 (fun k => fmag (T + k)) k)
      else
        XF.zext (max nm (max 32 n0)) (fun x =>
          if (cn || ci || !cz && ov) = true then XF.zext nm (fun x => fones x) x
          else if cz = true then XF.constBit 0 (max nm (max 32 n0)) x
          else XF.zext n0 (fun k => fmag (T + k)) x) k) :
    XF.val (fun x => fq (T + x)) w =
      if (cn || ci || !cz && ov) = true then 2 ^ w - 1
      else if cz = true then 0 else XF.val (fun k => fmag (T + k)) w := by
  rw [← hnw]
  have hM : n0 ≤ max nm (max 32 n0) := by omega
  have hc : ¬ (max nm (max 32 n0) < n0) := by omega
  generalize hF : (cn || ci || !cz && ov) = F at h ⊢
  by_cases hFt : F = true
  · have hbits : ∀ k, k < n0 → fq (T + k) = true := by
      intro k hk
      have hknm : k < nm := by omega
      have hkM : k < max nm (max 32 n0) := by omega
      rw [h k hk, if_neg hc]
      simp [XF.zext, hFt, hknm, hkM, hones k hknm]
    rw [if_pos hFt]
    exact val_all_true (fun x => fq (T + x)) n0 hbits
  · have hFf : F = false := by simpa using hFt
    by_cases hcz : cz = true
    · have hbits : ∀ k, k < n0 → fq (T + k) = false := by
        intro k hk
        have hkM : k < max nm (max 32 n0) := by omega
        rw [h k hk, if_neg hc]
        simp [XF.zext, hFf, hcz, constBit_zero]
      rw [if_neg hFt, if_pos hcz]
      exact val_all_false (fun x => fq (T + x)) n0 hbits
    · have hczf : cz = false := by simpa using hcz
      have hbits : ∀ k, k < n0 → fq (T + k) = fmag (T + k) := by
        intro k hk
        have hkM : k < max nm (max 32 n0) := by omega
        rw [h k hk, if_neg hc]
        simp [XF.zext, hFf, hczf, hk, hkM]
      rw [if_neg hFt, if_neg hcz]
      exact XF.val_congr_lt hbits

theorem g_out (a T w jK K : Nat) (hT : T = a + 1) (hjK : jK = a + 1 + w) (hK : K = a + 1 + w + 1)
    (A : Int) (hA : A = (a : Int)) (cn ci cz ov s mb : Bool) (fq fmag : Nat → Bool) (F : Nat)
    (hs : fq jK = (!cn && s))
    (hF : XF.val (fun x => fq (T + x)) w = F)
    (hb : fq a = (cn || !(cn || ci || cz || ov) && mb))
    (hlo : ∀ i : Nat, (i : Int) < A → fq i = (!(cn || ci || cz || ov) && fmag i)) :
    XF.val (fun x => fq x) K =
      (if (cn || ci || cz || ov) = true then 0 else XF.val (fun x => fmag x) a) +
        (cn || !(cn || ci || cz || ov) && mb).toNat * 2 ^ a + F * 2 ^ (a + 1) + (!cn && s).toNat * 2 ^ (a + 1 + w) := by
  subst hK
  rw [hT] at hF
  rw [hjK] at hs
  have hlow : XF.val fq a = if (cn || ci || cz || ov) = true then 0 else XF.val (fun x => fmag x) a := by
    by_cases hf : (cn || ci || cz || ov) = true
    · rw [if_pos hf]
      exact val_all_false fq a (fun k hk => by rw [hlo k (by omega), hf]; simp)
    · have hf' : (cn || ci || cz || ov) = false := by simpa using hf
      rw [if_neg hf]
      exact XF.val_congr_lt (fun k hk => by rw [hlo k (by omega), hf']; simp)
  rw [val_four fq a w, hF, hs, hb, hlow]

end Glue
end SvGolf.FdivParam

end DpG3

/-! # Section `DpG4`: Glue: the final assembly of the output value (was `tasks/fdivp/DpG4.lean`) -/

section DpG4

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Task `fdivp`: the final assembly of the output value

WP-H3 design layer, continued (`DpG3.lean`): `g_out` expresses the value of `q` through the Boolean flags `c_nan`, `c_inf`,
`c_zero`, `ovf` and the bits of `mag`; `g_final` shows that this is `OutN` (`DpQ.lean`). The flags are known exactly
(`decide` of the model's Propositions) for every pair; `ovf` and `mag` only for finite nonzero operands, and the output
does not depend on them otherwise (the four component lemmas `fin_c1..4` are a case analysis on the flags).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four)
open SvGolf.IEEE754

theorem fin_c1 (N : Prop) [Decidable N] (u : Nat) (cn s : Bool) (hcn : cn = decide N)
    (hs : s = decide (u % 2 = 1)) :
    (!cn && s).toNat = if N then 0 else u % 2 := by
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  by_cases hN : N <;> rcases hu with hu | hu <;> simp [hcn, hs, hN, hu]

theorem fin_c2 (N I Z O : Prop) [Decidable N] [Decidable I] [Decidable Z] [Decidable O]
    (cn ci cz ov : Bool) (MW M t w : Nat)
    (hcn : cn = decide N) (hci : ci = decide I) (hcz : cz = decide Z)
    (hov : ¬ (N ∨ I ∨ Z) → ov = decide O) (hmw : ¬ (N ∨ I ∨ Z) → MW = M / 2 ^ t) :
    (if (cn || ci || !cz && ov) = true then 2 ^ w - 1 else if cz = true then 0 else MW) =
      if N ∨ I ∨ (¬ Z ∧ O) then 2 ^ w - 1 else if Z then 0 else M / 2 ^ t := by
  by_cases hN : N
  · simp [hcn, hN]
  · by_cases hI : I
    · simp [hcn, hci, hN, hI]
    · by_cases hZ : Z
      · simp [hcn, hci, hcz, hN, hI, hZ]
      · have h0 : ¬ (N ∨ I ∨ Z) := fun h => h.elim hN (fun h' => h'.elim hI hZ)
        have h1 := hov h0
        have h2 := hmw h0
        by_cases hO : O <;> simp [hcn, hci, hcz, hN, hI, hZ, h1, h2, hO]

theorem fin_c3 (N I Z O MB FN : Prop) [Decidable N] [Decidable I] [Decidable Z] [Decidable O] [Decidable MB]
    [Decidable FN] (cn ci cz ov mb : Bool)
    (hcn : cn = decide N) (hci : ci = decide I) (hcz : cz = decide Z)
    (hov : ¬ (N ∨ I ∨ Z) → ov = decide O) (hmb : ¬ (N ∨ I ∨ Z) → mb = decide MB)
    (hFN : FN ↔ ¬ (N ∨ I ∨ Z ∨ O)) :
    (cn || !(cn || ci || cz || ov) && mb).toNat = if N ∨ (FN ∧ MB) then 1 else 0 := by
  by_cases hN : N
  · simp [hcn, hN]
  · by_cases hI : I
    · have hnFN : ¬ FN := fun h => hFN.1 h (Or.inr (Or.inl hI))
      simp [hcn, hci, hN, hI, hnFN]
    · by_cases hZ : Z
      · have hnFN : ¬ FN := fun h => hFN.1 h (Or.inr (Or.inr (Or.inl hZ)))
        simp [hcn, hci, hcz, hN, hI, hZ, hnFN]
      · have h0 : ¬ (N ∨ I ∨ Z) := fun h => h.elim hN (fun h' => h'.elim hI hZ)
        have h1 := hov h0
        have h2 := hmb h0
        by_cases hO : O <;> by_cases hM : MB <;> simp [hcn, hci, hcz, hN, hI, hZ, h1, h2, hO, hM, hFN]

theorem fin_c4 (N I Z O FN : Prop) [Decidable N] [Decidable I] [Decidable Z] [Decidable O] [Decidable FN]
    (cn ci cz ov : Bool) (ML M a : Nat)
    (hcn : cn = decide N) (hci : ci = decide I) (hcz : cz = decide Z)
    (hov : ¬ (N ∨ I ∨ Z) → ov = decide O) (hml : ¬ (N ∨ I ∨ Z) → ML = M % 2 ^ a)
    (hFN : FN ↔ ¬ (N ∨ I ∨ Z ∨ O)) :
    (if (cn || ci || cz || ov) = true then 0 else ML) = if FN then M % 2 ^ a else 0 := by
  by_cases hN : N
  · simp [hcn, hN, hFN]
  · by_cases hI : I
    · simp [hcn, hci, hN, hI, hFN]
    · by_cases hZ : Z
      · simp [hcn, hci, hcz, hN, hI, hZ, hFN]
      · have h0 : ¬ (N ∨ I ∨ Z) := fun h => h.elim hN (fun h' => h'.elim hI hZ)
        have h1 := hov h0
        have h2 := hml h0
        by_cases hO : O <;> simp [hcn, hci, hcz, hN, hI, hZ, h1, h2, hO, hFN]

theorem comb4 (a t w lo b F sb X1 X2 X3 X4 : Nat) (hta : t = a + 1)
    (hlo : lo = X4) (hb : b = X3) (hF : F = X2) (hsb : sb = X1) :
    lo + b * 2 ^ a + F * 2 ^ (a + 1) + sb * 2 ^ (a + 1 + w) =
      X1 * 2 ^ (w + t) + X2 * 2 ^ t + X3 * 2 ^ (t - 1) + X4 := by
  rw [hlo, hb, hF, hsb, hta]
  have e1 : w + (a + 1) = a + 1 + w := Nat.add_comm _ _
  have e2 : a + 1 - 1 = a := by omega
  rw [e1, e2]
  omega

theorem g_final (f : Format) (av bv : Nat) (cn ci cz ov s mb : Bool) (fmag : Nat → Bool) (a T Fv : Nat)
    (hT : T = a + 1) (hta : f.t = a + 1)
    (hcn : cn = decide (cNanN f av bv)) (hci : ci = decide (cInfN f av bv)) (hcz : cz = decide (cZeroN f av bv))
    (hs : s = decide ((sF f av + sF f bv) % 2 = 1))
    (hdp : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      ov = decide (ovfN f av bv) ∧ XF.val (fun x => fmag x) (f.w + f.t) = magN f av bv)
    (hmb : mb = fmag a)
    (hFv : Fv = if (cn || ci || !cz && ov) = true then 2 ^ f.w - 1
        else if cz = true then 0 else XF.val (fun k => fmag (T + k)) f.w) :
    (if (cn || ci || cz || ov) = true then 0 else XF.val (fun x => fmag x) a) +
        (cn || !(cn || ci || cz || ov) && mb).toNat * 2 ^ a + Fv * 2 ^ (a + 1) +
        (!cn && s).toNat * 2 ^ (a + 1 + f.w) = OutN f av bv := by
  have hfw := f.hw
  have hfp := f.hp
  have hov : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) → ov = decide (ovfN f av bv) :=
    fun h => (hdp h).1
  have hmagv : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      XF.val (fun x => fmag x) (f.w + f.t) = magN f av bv := fun h => (hdp h).2
  have hmlt : magN f av bv < 2 ^ (f.w + f.t) := by
    unfold magN
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hML : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      XF.val (fun x => fmag x) a = magN f av bv % 2 ^ (f.t - 1) := by
    intro hns
    rw [val_prefix fmag (f.w + f.t) a (by omega), hmagv hns]
    have e : f.t - 1 = a := by omega
    rw [e]
  have hMB : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      mb = decide (magN f av bv / 2 ^ (f.t - 1) % 2 = 1) := by
    intro hns
    have e : f.t - 1 = a := by omega
    rw [e, hmb]
    exact bit_eq_of_val fmag (f.w + f.t) (magN f av bv) a (hmagv hns) (by omega)
  have hMW : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      XF.val (fun k => fmag (T + k)) f.w = magN f av bv / 2 ^ f.t := by
    intro hns
    rw [val_window fmag T f.w (f.w + f.t) (by omega), hmagv hns]
    have e : T = f.t := by omega
    rw [e]
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [Nat.pow_add] at hmlt
    exact hmlt
  have hc1 := fin_c1 (cNanN f av bv) (sF f av + sF f bv) cn s hcn hs
  have hc2 := fin_c2 (cNanN f av bv) (cInfN f av bv) (cZeroN f av bv) (ovfN f av bv) cn ci cz ov
    (XF.val (fun k => fmag (T + k)) f.w) (magN f av bv) f.t f.w hcn hci hcz hov hMW
  have hc3 := fin_c3 (cNanN f av bv) (cInfN f av bv) (cZeroN f av bv) (ovfN f av bv)
    (magN f av bv / 2 ^ (f.t - 1) % 2 = 1) (finN f av bv) cn ci cz ov mb hcn hci hcz hov hMB Iff.rfl
  have hc4 := fin_c4 (cNanN f av bv) (cInfN f av bv) (cZeroN f av bv) (ovfN f av bv) (finN f av bv)
    cn ci cz ov (XF.val (fun x => fmag x) a) (magN f av bv) (f.t - 1) hcn hci hcz hov hML Iff.rfl
  unfold OutN
  exact comb4 a f.t f.w _ _ Fv _ _ _ _ _ hta hc4 hc3 (hFv.trans hc2) hc1

end Glue
end SvGolf.FdivParam

end DpG4

/-! # Section `NwCore`: The mathematics of the Newton core (was `LeanModels/Sv/Lib/Newton.lean`) -/

section NwCore

/-!
# Task `fdivp`, the Newton reference: the mathematics of the core (untrusted)

The core of `fdivp_newton.sv`, a Newton-Raphson divider of normalized significands `ma, mb ∈ [2^(P-1), 2^P)`, as the
`Nat` values the hardware computes (each product at its declared width, each part select a window), with `F = P + 4`
fraction bits for the reciprocal `r ≈ 2^F / d`, `d = mb / 2^(P-1) ∈ [1, 2)`:

* `nwR0`: the initial reciprocal `45/32 - 15/32·d`, that is `45·2^(P-1) - 15·mb`;
* `nwU`, `nwStep`: one step `r ← r·(2 - d·r)`: `u` is the one's complement of the top `F + 1` bits of `mb·r` (taken
  at `P + F` bits), and the product `r·u` (at `2F + 1` bits) is truncated to `F` fraction bits; `nwIter`: `k` steps;
* `nwQf`: the estimate `⌊ma·r / 2^(F-2)⌋` (`ma·r` at `P + F` bits); `nwRm`: the remainder `2^(P+1)·ma - qf·mb`
  modulo `2^(P+2)`; `nwQQ`, `nwRnz`: the quotient `qf + [rm ≥ mb] + [rm ≥ 2·mb]` and the sticky `rm ∉ {0, mb, 2·mb}`
  (`nwRnz` is decidable);
* `nwR0_hw`: `r[0]` as the hardware computes it (`45·2^(P-1) - 16·mb + mb`, each step at `P + 5` bits) is `nwR0`.

`newton_div`: after `K ≥ 1` steps with `P + 2 ≤ 2^(K+2)`, `nwQQ = ⌊2^(P+1)·ma / mb⌋` and `nwRnz ↔ 2^(P+1)·ma mod mb ≠ 0`
(only `ma < 2^P` is needed of `ma`).
`newton_rest` states it against restoring division (`restQuo`, `restRem` of `P + 2` steps, `LeanModels.Sv.Lib`), and
`nwNI_spec` shows that `K = $clog2((P + 9) / 8) + 1` qualifies (section `NwG1`'s `core` composes the two).

The error analysis is in units of `A = 2^(P-1)`: `S = 2^F·A = 32·A²` is `1` at the scale of `d·r`, so `E = S - mb·r` is
the error `1 - d·r` scaled by `S`, and `2^F = 32·A`, `2^(F+1) = 64·A`, `2^(P+F) = 2·S`, `2^(P+2) = 8·A`.

* `nw_step`: one step with `D = mb·r < 2·S` satisfies `S·(S - mb·r') = (S - D)² + D·(A - D mod A) + A·mb·t` (`t` the
  truncated low part of `r·u`), so the new error is nonnegative and at most `E²/S + (D + 2·S)·A/S`; `nwStep_spec`
  is the same bound for `nwStep` at `P` (no window of `nwU`/`nwStep` wraps).
* `nw_base`: `|E₀| ≤ S/16` (the linear approximation is within `1/16` on `[1, 2]`).
* `nw_iter_inv`: for `k ≥ 1`, `0 ≤ E_k` and `T·E_k ≤ S + 4·A·T` with `T = 2^(2^(k+2))`, i.e.
  `e_k ≤ 2^-(2^(k+2)) + 2^-(P+2)`; `T` is squared by a step and kept symbolic.
* `nw_quot`: with `E ≤ 8·A` (`e ≤ 2^-(P+1)`), `qf ≤ ⌊2^(P+1)·ma / mb⌋ ≤ qf + 2`; `correct_quot_of_rem_lt_three_mul` is
  the correction stage (`qq = qf + ge1 + ge2`, `rnz`).

Until 2026-11-04 this was the library module `LeanModels/Sv/Lib/Newton.lean`, and the correction lemma was in
`Lib/NatArith.lean`. Both model this one reference's core and nothing else uses them, so they are compiled here, in the
solution stage, like any golfer's own proof of their own core (decided 11/04: the shared library holds only results that
any proof of that class of designs would use). Plain Lean: `omega`, `grind` and core lemmas, on `LeanModels.Sv.Lib`'s
restoring division (`restQuo`, `restRem`, `restore_spec`), its `Nat` facts (`two_mul_le_mul_self_add_mul_self`,
`mod_add_sub_mod_of_eq_add`, `mod_cases_of_lt_three_mul`) and `LeanModels.Sv.clog2`.
-/

namespace SvGolf.FdivParam

open LeanModels.Sv (clog2)
open LeanModels.Sv.Lib

/-! ## The core, as the hardware computes it -/

/-- `r[0] = 45/32 - 15/32·d` at `F = P + 4` fraction bits. -/
def nwR0 (P mb : Nat) : Nat := 45 * 2 ^ (P - 1) - 15 * mb

/-- `u = ~dr[P+F-1:P-1]`, `dr = mb·r` at `P + F` bits: `2 - d·r` rounded down to `F` fraction bits. -/
def nwU (P mb r : Nat) : Nat := 2 ^ (P + 5) - 1 - mb * r % 2 ^ (2 * P + 4) / 2 ^ (P - 1) % 2 ^ (P + 5)

/-- `r' = ru[2F:F]`, `ru = r·u` at `2F + 1` bits. -/
def nwStep (P mb r : Nat) : Nat := r * nwU P mb r % 2 ^ (2 * P + 9) / 2 ^ (P + 4) % 2 ^ (P + 5)

/-- `r[k]`: `k` Newton steps from `r[0]`. -/
def nwIter (P mb : Nat) : Nat → Nat
  | 0 => nwR0 P mb
  | k + 1 => nwStep P mb (nwIter P mb k)

/-- `qf = qp[P+F-1:F-2]`, `qp = ma·r[K]` at `P + F` bits. -/
def nwQf (P K ma mb : Nat) : Nat := ma * nwIter P mb K % 2 ^ (2 * P + 4) / 2 ^ (P + 2) % 2 ^ (P + 2)

/-- `rm = {ma[0], 0^(P+1)} - qb`, `qb = qf·mb` at `P + 2` bits. -/
def nwRm (P K ma mb : Nat) : Nat :=
  (ma % 2 * 2 ^ (P + 1) + (2 ^ (P + 2) - nwQf P K ma mb * mb % 2 ^ (P + 2))) % 2 ^ (P + 2)

/-- `qq = qf + (rm >= mb) + (rm >= {mb, 1'b0})` at `P + 2` bits. -/
def nwQQ (P K ma mb : Nat) : Nat :=
  (nwQf P K ma mb + (if mb ≤ nwRm P K ma mb then 1 else 0) + (if 2 * mb ≤ nwRm P K ma mb then 1 else 0)) %
    2 ^ (P + 2)

/-- `rnz = (rm != mb) & (rm != {mb, 1'b0}) & (|rm)`. -/
def nwRnz (P K ma mb : Nat) : Prop := nwRm P K ma mb ≠ mb ∧ nwRm P K ma mb ≠ 2 * mb ∧ nwRm P K ma mb ≠ 0

/-- `nwRnz` (three disequalities of `Nat`s) is decidable, so a proof can split on it or `decide` it at a point. -/
instance (P K ma mb : Nat) : Decidable (nwRnz P K ma mb) := by unfold nwRnz; infer_instance

/-- `r[0]` as the hardware computes it, `45·2^(P-1) - 16·mb + mb` at the context width `F + 1 = P + 5`. -/
theorem nwR0_hw (P mb : Nat) (hP : 1 ≤ P) (hm1 : 2 ^ (P - 1) ≤ mb) (hm2 : mb < 2 ^ P) :
    ((2 ^ (P - 1) * 45 + (2 ^ (P + 5) - 16 * mb)) % 2 ^ (P + 5) + mb) % 2 ^ (P + 5) = nwR0 P mb := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hm1 ⊢
  have h5 : 2 ^ (n + 1 + 5) = 64 * 2 ^ n := by rw [show n + 1 + 5 = n + 6 by omega, Nat.pow_add]; omega
  have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
  rw [h1] at hm2
  unfold nwR0
  rw [Nat.add_sub_cancel, h5]
  have e1 : (2 ^ n * 45 + (64 * 2 ^ n - 16 * mb)) % (64 * 2 ^ n) = 45 * 2 ^ n - 16 * mb := by
    rw [show 2 ^ n * 45 + (64 * 2 ^ n - 16 * mb) = (45 * 2 ^ n - 16 * mb) + 64 * 2 ^ n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : 45 * 2 ^ n - 16 * mb < 64 * 2 ^ n)]
  rw [e1, Nat.mod_eq_of_lt (by omega : 45 * 2 ^ n - 16 * mb + mb < 64 * 2 ^ n)]
  omega

/-! ## Arithmetic -/

/-- The widths of the core in units of `A = 2^(P-1)`. -/
private theorem nw_pows (P : Nat) (hP : 1 ≤ P) :
    2 ^ P = 2 * 2 ^ (P - 1) ∧ 2 ^ (P + 1) = 4 * 2 ^ (P - 1) ∧ 2 ^ (P + 2) = 8 * 2 ^ (P - 1) ∧
      2 ^ (P + 4) = 32 * 2 ^ (P - 1) ∧ 2 ^ (P + 5) = 64 * 2 ^ (P - 1) ∧
      2 ^ (2 * P + 4) = 64 * (2 ^ (P - 1) * 2 ^ (P - 1)) ∧
      2 ^ (2 * P + 9) = 2048 * (2 ^ (P - 1) * 2 ^ (P - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 1 := ⟨P - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e : ∀ c, 2 ^ (n + c) = 2 ^ n * 2 ^ c := fun c => Nat.pow_add 2 n c
  have e2 : ∀ c, 2 ^ (n + n + c) = 2 ^ n * 2 ^ n * 2 ^ c := fun c => by rw [Nat.pow_add, Nat.pow_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 1]; omega
  · rw [show n + 1 + 1 = n + 2 by omega, e 2]; omega
  · rw [show n + 1 + 2 = n + 3 by omega, e 3]; omega
  · rw [show n + 1 + 4 = n + 5 by omega, e 5]; omega
  · rw [show n + 1 + 5 = n + 6 by omega, e 6]; omega
  · rw [show 2 * (n + 1) + 4 = n + n + 6 by omega, e2 6]; omega
  · rw [show 2 * (n + 1) + 9 = n + n + 11 by omega, e2 11]; omega

/-! ## One step -/

/-- **One Newton step**, in units of `A`: from `D = mb·r < 2·S`, the product `r·u` stays below `2^(2F)`, the new
reciprocal `r'` satisfies `mb·r' ≤ S` (the error is nonnegative), and the new error `S - mb·r'` is at most
`((S - D)² + A·D + 2·A·S) / S`, stated without subtraction. -/
theorem nw_step (A S mb R : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb) (hm2 : mb < 2 * A)
    (hD : mb * R < 2 * S) :
    R * (64 * A - 1 - mb * R / A) < 1024 * (A * A) ∧
      mb * (R * (64 * A - 1 - mb * R / A) / (32 * A)) ≤ S ∧
      S * (S - mb * (R * (64 * A - 1 - mb * R / A) / (32 * A))) + 2 * S * (mb * R) ≤
        S * S + mb * R * (mb * R) + A * (mb * R) + 2 * A * S := by
  have hq := Nat.div_add_mod (mb * R) A
  have hs := Nat.mod_lt (mb * R) hA
  have hqlt : mb * R / A < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul hA]
    have : 2 * S = 64 * A * A := by rw [hS]; grind
    omega
  generalize mb * R / A = q at *
  generalize mb * R % A = s at *
  generalize hu : 64 * A - 1 - q = u
  have hu' : u + q + 1 = 64 * A := by omega
  have hB : 0 < 32 * A := by omega
  have ht := Nat.div_add_mod (R * u) (32 * A)
  have htl := Nat.mod_lt (R * u) hB
  generalize R * u / (32 * A) = R' at *
  generalize R * u % (32 * A) = t at *
  generalize hD' : mb * R = D at *
  obtain ⟨a, ha⟩ : ∃ a, a + s = A := ⟨A - s, by omega⟩
  -- the error identity `S·(S - mb·r') = (S - D)² + D·(A - s) + A·mb·t`, without subtraction
  have hid : S * (mb * R') + D * D + D * a + A * mb * t = 2 * S * D := by
    clear hu hqlt hs htl hD hm1 hm2
    subst hS hD'
    grind
  have hsq := two_mul_le_mul_self_add_mul_self S D
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
  -- `r·u < 2^(2F)`: `A·mb·(r·u) = D·(A·u) ≤ D·(2·S - D - 1) ≤ S² - D`
  have hRu : R * u < 1024 * (A * A) := by
    refine Nat.lt_of_not_le fun hc => ?_
    have hAu : A * u + D + 1 ≤ 2 * S := by
      have : A * u + A * q + A = 64 * (A * A) := by
        clear hu hqlt
        grind
      omega
    have h1 : A * A * (1024 * (A * A)) ≤ A * mb * (R * u) := Nat.mul_le_mul (Nat.mul_le_mul_left A hm1) hc
    have h2 : D * (A * u + D + 1) ≤ D * (2 * S) := Nat.mul_le_mul_left D hAu
    have hD0 : D = 0 := by
      clear hid hu hqlt
      subst hS hD'
      have := Nat.zero_le (mb * R)
      grind
    rw [← hD'] at hD0
    rcases Nat.mul_eq_zero.1 hD0 with h | h
    · omega
    · subst h
      rw [Nat.zero_mul] at hc
      have : 0 < 1024 * (A * A) := Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
      omega
  have hle : mb * R' ≤ S := by
    have : S * (mb * R') ≤ S * S := by
      have := Nat.zero_le (D * a)
      have := Nat.zero_le (A * mb * t)
      clear hu hqlt hRu
      grind
    exact Nat.le_of_mul_le_mul_left this hSpos
  refine ⟨hRu, hle, ?_⟩
  obtain ⟨E', hE'⟩ : ∃ E', S = mb * R' + E' := ⟨S - mb * R', by omega⟩
  rw [show S - mb * R' = E' by omega]
  have h1 : D * a ≤ A * D := by rw [Nat.mul_comm A D]; exact Nat.mul_le_mul_left D (by omega)
  have h2 : A * (mb * t) ≤ A * (2 * S) := by
    apply Nat.mul_le_mul_left
    have : mb * t ≤ 2 * A * (32 * A) := Nat.mul_le_mul (by omega) (by omega)
    rw [hS]
    grind
  have h3 : S * S = S * (mb * R') + S * E' := by rw [← Nat.mul_add, ← hE']
  clear hu hqlt hRu hE' hsq
  grind

/-- `nwU` and `nwStep` at `P`: no window wraps when `D = mb·r < 2·S`, and the step is `nw_step`'s. -/
theorem nwStep_spec (P A S mb R : Nat) (hP : 1 ≤ P) (hA : A = 2 ^ (P - 1)) (hS : S = 32 * (A * A))
    (hm1 : A ≤ mb) (hm2 : mb < 2 * A) (hD : mb * R < 2 * S) :
    mb * nwStep P mb R ≤ S ∧
      S * (S - mb * nwStep P mb R) + 2 * S * (mb * R) ≤ S * S + mb * R * (mb * R) + A * (mb * R) + 2 * A * S := by
  obtain ⟨-, -, -, hp4, hp5, hpf, hp2f⟩ := nw_pows P hP
  rw [← hA] at hp4 hp5 hpf hp2f
  have hApos : 0 < A := by rw [hA]; exact Nat.two_pow_pos _
  obtain ⟨hRu, hle, hup⟩ := nw_step A S mb R hApos hS hm1 hm2 hD
  have hD2 : mb * R < 64 * (A * A) := by rw [hS] at hD; omega
  have hq : mb * R / A < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul hApos]
    have : 64 * (A * A) = 64 * A * A := by rw [Nat.mul_assoc]
    omega
  have hU : nwU P mb R = 64 * A - 1 - mb * R / A := by
    unfold nwU
    rw [← hA, hp5, hpf, Nat.mod_eq_of_lt hD2, Nat.mod_eq_of_lt hq]
  generalize 64 * A - 1 - mb * R / A = u at *
  have hRu' : R * u < 2048 * (A * A) := by omega
  have hRu2 : R * u / (32 * A) < 64 * A := by
    rw [Nat.div_lt_iff_lt_mul (show 0 < 32 * A by omega)]
    have : 64 * A * (32 * A) = 2048 * (A * A) := by grind
    omega
  have hStep : nwStep P mb R = R * u / (32 * A) := by
    unfold nwStep
    rw [hU, hp2f, hp4, hp5, Nat.mod_eq_of_lt hRu', Nat.mod_eq_of_lt hRu2]
  rw [hStep]
  exact ⟨hle, hup⟩

/-! ## The error bounds -/

/-- **The initial reciprocal**: `15·S ≤ 16·mb·r₀ ≤ 17·S`, i.e. `|E₀| ≤ S/16`. -/
theorem nw_base (A S mb : Nat) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb) (hm2 : mb < 2 * A) :
    15 * S ≤ 16 * (mb * (45 * A - 15 * mb)) ∧ 16 * (mb * (45 * A - 15 * mb)) ≤ 17 * S := by
  obtain ⟨R, hR⟩ : ∃ R, R + 15 * mb = 45 * A := ⟨45 * A - 15 * mb, by omega⟩
  rw [show 45 * A - 15 * mb = R by omega]
  have hmR : mb * R + 15 * (mb * mb) = 45 * (A * mb) := by grind
  subst hS
  constructor
  · -- `3·A·mb - 2·A² - mb² = c·(A - c)` with `mb = A + c`
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hm1
    have : c * c ≤ A * c := Nat.mul_le_mul_right c (by omega)
    grind
  · -- `60·(15·mb² - 45·A·mb + 34·A²) = (30·mb - 45·A)² + 15·A²`
    have := two_mul_le_mul_self_add_mul_self (30 * mb) (45 * A)
    have := Nat.zero_le (A * A)
    grind

/-- The new error from `nw_step`'s bound, with `e = |S - D|`. -/
private theorem nw_err_sq (A S D E' e : Nat) (he : S = D + e ∨ D = S + e)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : S * E' ≤ e * e + A * D + 2 * A * S := by
  rcases he with rfl | rfl <;> grind

/-- **The first step**: from `|E₀| ≤ S/16`, `256·E₁ ≤ S + 1024·A` (`e₁ ≤ 2^-8 + 2^-(P+2)`). -/
private theorem nw_first (A S D E' : Nat) (hSpos : 0 < S) (h15 : 15 * S ≤ 16 * D) (h17 : 16 * D ≤ 17 * S)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : 256 * E' ≤ S + 1024 * A := by
  have hA17 : A * (16 * D) ≤ A * (17 * S) := Nat.mul_le_mul_left A h17
  have key : ∃ e, (S = D + e ∨ D = S + e) ∧ 16 * e ≤ S := by
    rcases Nat.le_total D S with h | h
    · exact ⟨S - D, Or.inl (by omega), by omega⟩
    · exact ⟨D - S, Or.inr (by omega), by omega⟩
  obtain ⟨e, he, he16⟩ := key
  have h1 := nw_err_sq A S D E' e he hup
  have h2 : 16 * e * (16 * e) ≤ S * S := Nat.mul_le_mul he16 he16
  have h0 := Nat.zero_le (A * S)
  have : S * (256 * E') ≤ S * (S + 1024 * A) := by grind
  exact Nat.le_of_mul_le_mul_left this hSpos

/-- **A later step**: from `0 ≤ E` and `T·E ≤ S + 4·A·T` (`T ≥ 16`), `T²·E' ≤ S + 4·A·T²`. -/
private theorem nw_next (A S T D E' : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (hT : 16 ≤ T) (hD : D ≤ S)
    (hinv : T * (S - D) ≤ S + 4 * A * T)
    (hup : S * E' + 2 * S * D ≤ S * S + D * D + A * D + 2 * A * S) : T * T * E' ≤ S + 4 * A * (T * T) := by
  obtain ⟨e, he⟩ : ∃ e, S = D + e := ⟨S - D, by omega⟩
  have h1 := nw_err_sq A S D E' e (Or.inl he) hup
  rw [show S - D = e by omega] at hinv
  have hAD : A * D ≤ A * S := Nat.mul_le_mul_left A hD
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hA hA)
  have h2 : T * T * (S * E') ≤ T * T * (e * e + 3 * A * S) := Nat.mul_le_mul_left _ (by grind)
  have h3 : T * e * (T * e) ≤ (S + 4 * A * T) * (S + 4 * A * T) := Nat.mul_le_mul hinv hinv
  have h4 : 16 * (A * A * A * T) ≤ T * (A * A * A * T) := Nat.mul_le_mul_right _ hT
  have h5 : 1 * (A * A * T * T) ≤ A * (A * A * T * T) := Nat.mul_le_mul_right _ hA
  have : S * (T * T * E') ≤ S * (S + 4 * A * (T * T)) := by
    clear he h1 hinv hAD hup hD
    subst hS
    grind
  exact Nat.le_of_mul_le_mul_left this hSpos

/-- **The iteration**: for `k ≥ 1`, `mb·r_k ≤ S` and `T·(S - mb·r_k) ≤ S + 4·A·T`, `T = 2^(2^(k+2))`. -/
theorem nw_iter_inv (P A S mb : Nat) (hP : 1 ≤ P) (hA : A = 2 ^ (P - 1)) (hS : S = 32 * (A * A)) (hm1 : A ≤ mb)
    (hm2 : mb < 2 * A) :
    ∀ k, 1 ≤ k → mb * nwIter P mb k ≤ S ∧
      2 ^ 2 ^ (k + 2) * (S - mb * nwIter P mb k) ≤ S + 4 * A * 2 ^ 2 ^ (k + 2) := by
  have hApos : 0 < A := by rw [hA]; exact Nat.two_pow_pos _
  have hSpos : 0 < S := by rw [hS]; exact Nat.mul_pos (by omega) (Nat.mul_pos hApos hApos)
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    show mb * nwStep P mb (nwIter P mb k) ≤ S ∧
      2 ^ 2 ^ (k + 1 + 2) * (S - mb * nwStep P mb (nwIter P mb k)) ≤ S + 4 * A * 2 ^ 2 ^ (k + 1 + 2)
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- the first step, from `r₀`
      obtain ⟨h15, h17⟩ := nw_base A S mb hS hm1 hm2
      have hR0 : nwIter P mb 0 = 45 * A - 15 * mb := by rw [hA]; rfl
      rw [← hR0] at h15 h17
      obtain ⟨hle, hup⟩ := nwStep_spec P A S mb (nwIter P mb 0) hP hA hS hm1 hm2 (by omega)
      have h1 := nw_first A S _ _ hSpos h15 h17 hup
      have hT : 2 ^ 2 ^ (0 + 1 + 2) = 256 := by decide
      rw [hT]
      exact ⟨hle, by omega⟩
    · obtain ⟨hle0, hinv0⟩ := ih hk1
      obtain ⟨hle, hup⟩ := nwStep_spec P A S mb (nwIter P mb k) hP hA hS hm1 hm2 (by omega)
      have hT : 16 ≤ 2 ^ 2 ^ (k + 2) := by
        have : 4 ≤ 2 ^ (k + 2) := by
          rw [Nat.pow_add]
          have := Nat.two_pow_pos k
          omega
        calc 16 = 2 ^ 4 := by decide
          _ ≤ 2 ^ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) this
      have hTT : 2 ^ 2 ^ (k + 1 + 2) = 2 ^ 2 ^ (k + 2) * 2 ^ 2 ^ (k + 2) := by
        have e : 2 ^ (k + 1 + 2) = 2 ^ (k + 2) + 2 ^ (k + 2) := by
          rw [show k + 1 + 2 = (k + 2) + 1 by omega, Nat.pow_add 2 (k + 2) 1]
          omega
        rw [e, Nat.pow_add]
      have h1 := nw_next A S _ _ _ hApos hS hT hle0 hinv0 hup
      rw [hTT]
      exact ⟨hle, h1⟩

/-! ## The quotient and the correction -/

/-- **The estimate**: with `mb·r ≤ S` and `S - mb·r ≤ 8·A` (`0 ≤ e ≤ 2^-(P+1)`), `qf = ⌊ma·r / 2^(P+2)⌋` satisfies
`qf·mb ≤ 2^(P+1)·ma < (qf + 3)·mb`, and `ma·r` fits its `P + F` bits. -/
theorem nw_quot (A S ma mb R : Nat) (hA : 0 < A) (hS : S = 32 * (A * A)) (ha2 : ma < 2 * A) (hab : ma < 2 * mb)
    (hb1 : A ≤ mb) (hD : mb * R ≤ S) (hE : S - mb * R ≤ 8 * A) :
    ma * R < 64 * (A * A) ∧ ma * R / (8 * A) * mb ≤ 4 * A * ma ∧ 4 * A * ma < (ma * R / (8 * A) + 3) * mb := by
  have hR : R ≤ 32 * A := by
    have : A * R ≤ A * (32 * A) := by
      have := Nat.mul_le_mul_right R hb1
      grind
    exact Nat.le_of_mul_le_mul_left this hA
  have hX : ma * R < 64 * (A * A) := by
    have h1 : ma * R ≤ ma * (32 * A) := Nat.mul_le_mul_left ma hR
    have h2 : ma * (32 * A) < 2 * A * (32 * A) := Nat.mul_lt_mul_of_pos_right ha2 (by omega)
    grind
  refine ⟨hX, ?_, ?_⟩
  · have hx := Nat.div_add_mod (ma * R) (8 * A)
    generalize ma * R / (8 * A) = qf at *
    generalize ma * R % (8 * A) = x0 at *
    have h1 : ma * (mb * R) ≤ ma * S := Nat.mul_le_mul_left ma hD
    have h2 : mb * (ma * R) = mb * (8 * A * qf + x0) := by rw [hx]
    have h0 : 0 ≤ mb * x0 := Nat.zero_le _
    have : 8 * A * (qf * mb) ≤ 8 * A * (4 * A * ma) := by
      subst hS
      grind
    exact Nat.le_of_mul_le_mul_left this (by omega)
  · have hx := Nat.div_add_mod (ma * R) (8 * A)
    have hxl := Nat.mod_lt (ma * R) (show 0 < 8 * A by omega)
    generalize ma * R / (8 * A) = qf at *
    generalize ma * R % (8 * A) = x0 at *
    obtain ⟨E, hE'⟩ : ∃ E, S = mb * R + E := ⟨S - mb * R, by omega⟩
    have hE8 : E ≤ 8 * A := by omega
    have h1 : ma * S = ma * (mb * R + E) := by rw [← hE']
    have h2 : mb * (ma * R) = mb * (8 * A * qf + x0) := by rw [hx]
    have h3 : ma * E ≤ ma * (8 * A) := Nat.mul_le_mul_left ma hE8
    have h4 : (ma + 1) * (8 * A) ≤ 2 * mb * (8 * A) := Nat.mul_le_mul_right _ (by omega)
    have h5 : mb * (x0 + 1) ≤ mb * (8 * A) := Nat.mul_le_mul_left mb (by omega)
    have : 8 * A * (4 * A * ma) < 8 * A * ((qf + 3) * mb) := by
      subst hS
      grind
    exact Nat.lt_of_mul_lt_mul_left this

/-- **Correcting a quotient estimate low by at most two**: with `N = qf·mb + rm` and `rm < 3·mb`,
`qf + [rm ≥ mb] + [rm ≥ 2·mb]` is `⌊N / mb⌋` (modulo any `M` above it), and `N mod mb ≠ 0` exactly when
`rm ∉ {0, mb, 2·mb}`. -/
theorem correct_quot_of_rem_lt_three_mul (N mb qf rm M : Nat) (h : N = qf * mb + rm) (hrm : rm < 3 * mb)
    (hM : N / mb < M) :
    (qf + (if mb ≤ rm then 1 else 0) + (if 2 * mb ≤ rm then 1 else 0)) % M = N / mb ∧
      ((rm ≠ mb ∧ rm ≠ 2 * mb ∧ rm ≠ 0) ↔ N % mb ≠ 0) := by
  have hmb : 0 < mb := by omega
  have hl := Nat.mod_lt rm hmb
  rcases mod_cases_of_lt_three_mul rm mb hrm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · obtain ⟨hq, hr⟩ := (Nat.div_mod_unique (a := N) (d := qf) hmb).mpr ⟨by rw [h, Nat.mul_comm mb qf]; omega, hl⟩
    rw [hq] at hM ⊢
    have n1 : ¬ mb ≤ rm := by omega
    have n2 : ¬ 2 * mb ≤ rm := by omega
    rw [hr, h1, if_neg n1, if_neg n2, Nat.mod_eq_of_lt (by omega : qf + 0 + 0 < M)]
    exact ⟨rfl, fun hh => hh.2.2, fun hh => ⟨by omega, by omega, hh⟩⟩
  · obtain ⟨hq, hr⟩ := (Nat.div_mod_unique (a := N) (d := qf + 1) hmb).mpr
      ⟨by rw [h, Nat.mul_comm mb, Nat.add_mul]; omega, hl⟩
    rw [hq] at hM ⊢
    have n2 : ¬ 2 * mb ≤ rm := by omega
    rw [hr, if_pos h2, if_neg n2, Nat.mod_eq_of_lt (by omega : qf + 1 + 0 < M)]
    generalize rm % mb = r at *
    exact ⟨rfl, fun hh => by omega, fun hh => ⟨by omega, by omega, by omega⟩⟩
  · obtain ⟨hq, hr⟩ := (Nat.div_mod_unique (a := N) (d := qf + 2) hmb).mpr
      ⟨by rw [h, Nat.mul_comm mb, Nat.add_mul]; omega, hl⟩
    rw [hq] at hM ⊢
    have p1 : mb ≤ rm := by omega
    rw [hr, if_pos p1, if_pos h2, Nat.mod_eq_of_lt (by omega : qf + 1 + 1 < M)]
    generalize rm % mb = r at *
    exact ⟨rfl, fun hh => by omega, fun hh => ⟨by omega, by omega, by omega⟩⟩


/-! ## The divider -/

/-- **Newton-Raphson division.** For `mb ∈ [2^(P-1), 2^P)`, `ma < 2^P` and `K ≥ 1` steps with
`P + 2 ≤ 2^(K+2)`, the core's quotient is `⌊2^(P+1)·ma / mb⌋` and its sticky is the remainder test. -/
theorem newton_div (P K ma mb : Nat) (hP : 2 ≤ P) (ha : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) (hK : 1 ≤ K) (hKP : P + 2 ≤ 2 ^ (K + 2)) :
    nwQQ P K ma mb = 2 ^ (P + 1) * ma / mb ∧ (nwRnz P K ma mb ↔ 2 ^ (P + 1) * ma % mb ≠ 0) := by
  obtain ⟨hp0, hp1, hp2, -, -, hpf, -⟩ := nw_pows P (by omega)
  have hT : 2 ^ (P + 2) ≤ 2 ^ 2 ^ (K + 2) := Nat.pow_le_pow_right (by omega) hKP
  generalize hA : 2 ^ (P - 1) = A at *
  have hApos : 0 < A := by rw [← hA]; exact Nat.two_pow_pos _
  have hab : ma < 2 * mb := by omega
  obtain ⟨hle, hinv⟩ := nw_iter_inv P A (32 * (A * A)) mb (by omega) hA.symm rfl hb1 (by omega) K hK
  -- the final error: `T·E ≤ S + 4·A·T` with `S = 4·A·(8·A) ≤ 4·A·T` gives `E ≤ 8·A`
  have hE : 32 * (A * A) - mb * nwIter P mb K ≤ 8 * A := by
    generalize 2 ^ 2 ^ (K + 2) = T at *
    generalize 32 * (A * A) - mb * nwIter P mb K = E at *
    have h1 : 4 * A * (8 * A) ≤ 4 * A * T := Nat.mul_le_mul_left _ (by omega)
    have h2 : T * E ≤ T * (8 * A) := by grind
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  generalize hR : nwIter P mb K = R at *
  obtain ⟨hX, hlo, hhi⟩ := nw_quot A (32 * (A * A)) ma mb R hApos rfl (by omega) hab hb1 hle hE
  have hqf : nwQf P K ma mb = ma * R / (8 * A) := by
    unfold nwQf
    have hq8 : ma * R / (8 * A) < 8 * A := by
      rw [Nat.div_lt_iff_lt_mul (show 0 < 8 * A by omega)]
      have : 8 * A * (8 * A) = 64 * (A * A) := by grind
      omega
    rw [hR, hpf, hp2, Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hq8]
  generalize ma * R / (8 * A) = qf at *
  have hN8 : 4 * A * ma % (8 * A) = ma % 2 * (4 * A) := by
    rw [show 8 * A = 4 * A * 2 by omega, Nat.mul_mod_mul_left]
    exact Nat.mul_comm _ _
  have hhi' : 4 * A * ma < qf * mb + 3 * mb := by rw [Nat.add_mul] at hhi; exact hhi
  have hrm : nwRm P K ma mb = 4 * A * ma - qf * mb := by
    unfold nwRm
    rw [hqf, hp1, hp2, ← hN8]
    exact mod_add_sub_mod_of_eq_add (8 * A) (4 * A * ma) (qf * mb) _ (by omega) (by omega)
  have hQ : 4 * A * ma / mb < 8 * A := by
    rw [Nat.div_lt_iff_lt_mul (show 0 < mb by omega)]
    have : 4 * A * ma < 4 * A * (2 * mb) := Nat.mul_lt_mul_of_pos_left hab (by omega)
    grind
  obtain ⟨h1, h2⟩ := correct_quot_of_rem_lt_three_mul (4 * A * ma) mb qf (4 * A * ma - qf * mb) (8 * A) (by omega)
    (by omega) hQ
  unfold nwQQ nwRnz
  rw [hrm, hqf, hp2, hp1]
  exact ⟨h1, h2⟩

/-- `newton_div` against restoring division: the quotient and the sticky of `P + 2` restoring steps. -/
theorem newton_rest (P K ma mb : Nat) (hP : 2 ≤ P) (ha : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) (hK : 1 ≤ K) (hKP : P + 2 ≤ 2 ^ (K + 2)) :
    nwQQ P K ma mb = restQuo mb ma (P + 2) ∧ (nwRnz P K ma mb ↔ restRem mb ma (P + 2) ≠ 0) := by
  obtain ⟨hp0, -⟩ := nw_pows P (by omega)
  have := Nat.two_pow_pos (P - 1)
  obtain ⟨h1, h2⟩ := newton_div P K ma mb hP ha hb1 hb2 hK hKP
  obtain ⟨e1, e2⟩ := restore_spec mb ma (P + 1) (by omega) (by omega)
  rw [show P + 1 + 1 = P + 2 from rfl] at e1 e2
  rw [e1, e2, h1, h2]
  generalize 2 ^ (P + 1) * ma % mb = r
  exact ⟨rfl, fun h => by omega, fun h => by omega⟩

/-- **The step count** `NI = $clog2((P + 9) / 8) + 1`: `1 ≤ NI` and `P + 2 ≤ 2^(NI+2)`. -/
theorem nwNI_spec (P : Nat) : 1 ≤ clog2 ((P + 9) / 8) + 1 ∧ P + 2 ≤ 2 ^ (clog2 ((P + 9) / 8) + 1 + 2) := by
  refine ⟨by omega, ?_⟩
  unfold clog2
  split
  · show P + 2 ≤ 8
    omega
  · have hl := Nat.lt_log2_self (n := (P + 9) / 8 - 1)
    generalize ((P + 9) / 8 - 1).log2 = L at hl ⊢
    rw [show L + 1 + 1 + 2 = (L + 1) + 3 by omega, Nat.pow_add]
    generalize 2 ^ (L + 1) = M at hl ⊢
    show P + 2 ≤ M * 8
    omega

end SvGolf.FdivParam

end NwCore

/-! # Section `NwG1`: Glue: the Newton core (new in this reference) -/

section NwG1

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# Task `fdivp`, the Newton reference: the glue for the Newton core

The sites of the Newton core of `fdivp_newton.sv` (`r[0]`, the family `newton`, `qp`, `qf`, `qe`, `qb`, `rm`, `ge1`,
`ge2`, `qq`, `rnz`), in the style of `DpG2`/`DpG3`: one lemma per shape of the printed equations, the equation the
hypothesis `h`, the conclusion the `Nat` value of the site in the terms of section `NwCore` (`nwR0`, `nwIter`, `nwQf`,
`nwRm`, `nwQQ`, `nwRnz`). `newton_rows` is the family (an induction over the steps, on the value lemma of `*`);
`core` puts the sites together: for normalized significands `ma`, `mb` and `N ≥ 1` steps with `P + 2 ≤ 2^(N+2)`, the
quotient `qq` and the sticky `rnz` are those of `P + 2` restoring steps (`newton_rest`), which is what the model of
`DpQ` reads (`qqN`, `rrN`).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four
  val_not val_cons_false)
open SvGolf.IEEE754

/-! ## The Newton family -/

/-- **The Newton family.** After `i` steps the row `i` of `r` is `nwIter` of `r[0]`. -/
theorem newton_rows (P N : Nat) (NIi : Int) (hNI : NIi = (N : Int)) (hP : 2 ≤ P)
    (fr fdr fu fru fmb : Nat → Bool) (mb : Nat)
    (hmb : XF.val (fun k => fmb k) P = mb) (hr0 : XF.val (fun x => fr x) (P + 5) = nwR0 P mb)
    (hdr : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + ((P : Int) + 4)).toNat → fdr (rmN ((P : Int) + ((P : Int) + 4)) ((i : Int)) 0 + k) = XF.mulBits ((P : Int) + ((P : Int) + 4)).toNat (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => fmb k) x) ((P : Int) + ((P : Int) + 4)).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => fr (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (hu : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + 4 + 1).toNat → fu (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k) = !fdr (rmN ((P : Int) + ((P : Int) + 4)) ((i : Int)) ((P : Int) + -1) + k))
    (hru : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < (2 * ((P : Int) + 4) + 1).toNat → fru (rmN (2 * ((P : Int) + 4) + 1) ((i : Int)) 0 + k) = XF.mulBits (2 * ((P : Int) + 4) + 1).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => fr (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) (2 * ((P : Int) + 4) + 1).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => fu (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (hrr : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + 4 + 1).toNat → fr (rmN ((P : Int) + 4 + 1) ((i : Int) + 1) 0 + k) = fru (rmN (2 * ((P : Int) + 4) + 1) ((i : Int)) ((P : Int) + 4) + k)) :
    ∀ i, i ≤ N → XF.val (fun x => fr (i * (P + 5) + x)) (P + 5) = nwIter P mb i := by
  subst hNI
  have w1 : ((P : Int) + ((P : Int) + 4)).toNat = 2 * P + 4 := by omega
  have w2 : ((P : Int) + 4 + 1).toNat = P + 5 := by omega
  have w3 : (2 * ((P : Int) + 4) + 1).toNat = 2 * P + 9 := by omega
  have w4 : ((P : Int) + -1).natAbs + 1 = P := by omega
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.zero_add, nwIter]
    exact hr0
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hlt : (i : Int) < ((N : Nat) : Int) := by omega
    have hdrow := hdr i hlt
    have hurow := hu i hlt
    have hrurow := hru i hlt
    have hrrow := hrr i hlt
    have o1 : rmN ((P : Int) + ((P : Int) + 4)) (i : Int) 0 = i * (2 * P + 4) :=
      rmN_eq _ _ _ (2 * P + 4) i 0 (by omega) rfl rfl
    have o2 : rmN ((P : Int) + 4 + 1) (i : Int) 0 = i * (P + 5) :=
      rmN_eq _ _ _ (P + 5) i 0 (by omega) rfl rfl
    have o3 : rmN ((P : Int) + 4 + 1) ((i : Int) + 1) 0 = (i + 1) * (P + 5) :=
      rmN_eq _ _ _ (P + 5) (i + 1) 0 (by omega) (by omega) rfl
    have o4 : rmN ((P : Int) + ((P : Int) + 4)) (i : Int) ((P : Int) + -1) = i * (2 * P + 4) + (P - 1) :=
      rmN_eq _ _ _ (2 * P + 4) i (P - 1) (by omega) rfl (by omega)
    have o5 : rmN (2 * ((P : Int) + 4) + 1) (i : Int) 0 = i * (2 * P + 9) :=
      rmN_eq _ _ _ (2 * P + 9) i 0 (by omega) rfl rfl
    have o6 : rmN (2 * ((P : Int) + 4) + 1) (i : Int) ((P : Int) + 4) = i * (2 * P + 9) + (P + 4) :=
      rmN_eq _ _ _ (2 * P + 9) i (P + 4) (by omega) rfl (by omega)
    simp only [w1, w2, w3, w4, o1, o2, o3, o4, o5, o6] at hdrow hurow hrurow hrrow
    obtain ⟨R, hR⟩ : ∃ R, nwIter P mb i = R := ⟨_, rfl⟩
    rw [hR] at ih'
    -- `dr = mb·r`, `u = ~dr[P+F-1:P-1]`, `ru = r·u`
    have vdr : XF.val (fun x => fdr (i * (2 * P + 4) + x)) (2 * P + 4) = mb * R % 2 ^ (2 * P + 4) := by
      rw [XF.val_congr_lt (fun j hj => hdrow j hj), XF.val_mulBits, XF.val_zext P _ (2 * P + 4) (by omega),
        XF.val_zext (P + 5) _ (2 * P + 4) (by omega), hmb, ih']
    have vu : XF.val (fun x => fu (i * (P + 5) + x)) (P + 5) = nwU P mb R := by
      rw [XF.val_congr_lt (fun j hj => hurow j hj), val_not]
      have e : XF.val (fun x => fdr (i * (2 * P + 4) + (P - 1) + x)) (P + 5) =
          XF.val (fun x => fdr (i * (2 * P + 4) + (P - 1 + x))) (P + 5) :=
        XF.val_congr_lt (fun j _ => by rw [Nat.add_assoc])
      rw [e, val_window (fun x => fdr (i * (2 * P + 4) + x)) (P - 1) (P + 5) (2 * P + 4) (by omega), vdr]
      rfl
    have vru : XF.val (fun x => fru (i * (2 * P + 9) + x)) (2 * P + 9) = R * nwU P mb R % 2 ^ (2 * P + 9) := by
      rw [XF.val_congr_lt (fun j hj => hrurow j hj), XF.val_mulBits, XF.val_zext (P + 5) _ (2 * P + 9) (by omega),
        XF.val_zext (P + 5) _ (2 * P + 9) (by omega), ih', vu]
    -- `r[i+1] = ru[2F:F]`
    show XF.val (fun x => fr ((i + 1) * (P + 5) + x)) (P + 5) = nwStep P mb (nwIter P mb i)
    rw [hR, XF.val_congr_lt (fun j hj => hrrow j hj)]
    have e : XF.val (fun x => fru (i * (2 * P + 9) + (P + 4) + x)) (P + 5) =
        XF.val (fun x => fru (i * (2 * P + 9) + (P + 4 + x))) (P + 5) :=
      XF.val_congr_lt (fun j _ => by rw [Nat.add_assoc])
    rw [e, val_window (fun x => fru (i * (2 * P + 9) + x)) (P + 4) (P + 5) (2 * P + 9) (by omega), vru]
    rfl

/-! ## The sites of the core -/

/-- A copy of a row (`ma = na_r[P-1]`, `mb = nb_r[P-1]`). -/
theorem g_copy (P n r v : Nat) (hn : n = P) (fm fn : Nat → Bool) (hv : XF.val (fun x => fn (r + x)) P = v)
    (h : ∀ k, k < n → fm k = fn (r + k)) : XF.val (fun x => fm x) P = v := by
  subst n
  rw [XF.val_congr_lt (fun j hj => h j hj), hv]

/-- `r[0] = {6'd45, zr[P-2:0]} - {mb, 4'd0} + mb` (`nwR0_hw`). -/
theorem g_r0 (P n m w4 : Nat) (hn : n = P - 1) (hm : m = P + 5) (hw4 : w4 = P) (hP : 2 ≤ P)
    (fr fzr fmb : Nat → Bool) (c45 c0 : LVec) (mb : Nat)
    (hzr : ∀ k, k < P + 1 → fzr k = false)
    (h45 : XF.val (fun x => c45.boolAt x) 6 = 45) (hc0w : c0.width = 4) (hc0 : XF.val (fun x => c0.boolAt x) 4 = 0)
    (hmb : XF.val (fun k => fmb k) P = mb) (hm1 : 2 ^ (P - 1) ≤ mb) (hm2 : mb < 2 ^ P)
    (h : ∀ k, k < m → fr k =
      XF.addBits m (fun x => XF.subBits m (fun x => if x < n then fzr x else c45.boolAt (x - n)) m
          (fun x => XF.zext (w4 + c0.width) (fun x => if x < c0.width then c0.boolAt x else fmb (x - c0.width)) x) x)
        m (fun x => XF.zext w4 (fun k => fmb k) x) k) :
    XF.val (fun x => fr x) (P + 5) = nwR0 P mb := by
  subst n m w4
  rw [XF.val_congr_lt (fun j hj => h j hj), val_addBits, val_subBits, Nat.max_self]
  have e1 : XF.val (fun x => if x < P - 1 then fzr x else c45.boolAt (x - (P - 1))) (P + 5) = 2 ^ (P - 1) * 45 := by
    have hc := val_cat fzr (fun x => c45.boolAt x) (P - 1) 6
    rw [show P - 1 + 6 = P + 5 by omega] at hc
    rw [hc, h45, val_all_false fzr (P - 1) (fun k hk => hzr k (by omega)), Nat.zero_add]
  have e2 : XF.val (fun x => XF.zext (P + c0.width)
      (fun x => if x < c0.width then c0.boolAt x else fmb (x - c0.width)) x) (P + 5) = 16 * mb := by
    rw [XF.val_zext (P + c0.width) _ (P + 5) (by omega), hc0w]
    have hc := val_cat (fun x => c0.boolAt x) fmb 4 P
    rw [Nat.add_comm P 4, hc, hc0, hmb]
    show 0 + 16 * mb = 16 * mb
    omega
  have e3 : XF.val (fun x => XF.zext P (fun k => fmb k) x) (P + 5) = mb := by
    rw [XF.val_zext P _ (P + 5) (by omega), hmb]
  rw [e1, e2, e3]
  exact nwR0_hw P mb (by omega) hm1 hm2

/-- `qp = ma·r[N]`, `qf = qp[P+F-1:F-2]`: `nwQf`'s window. -/
theorem g_qf (P wq wa wr wf s rN : Nat) (hwq : wq = 2 * P + 4) (hwa : wa = P) (hwr : wr = P + 5) (hwf : wf = P + 2)
    (hs : s = P + 2) (hP : 1 ≤ P) (fqf fqp fma fr : Nat → Bool) (ma R : Nat)
    (hma : XF.val (fun k => fma k) P = ma) (hR : XF.val (fun x => fr (rN + x)) (P + 5) = R)
    (hqp : ∀ k, k < wq → fqp k = XF.mulBits wq (fun x => XF.zext wa (fun k => fma k) x) wq
        (fun x => XF.zext wr (fun k => fr (rN + k)) x) k)
    (hqf : ∀ k, k < wf → fqf k = fqp (s + k)) :
    XF.val (fun x => fqf x) (P + 2) = ma * R % 2 ^ (2 * P + 4) / 2 ^ (P + 2) % 2 ^ (P + 2) := by
  subst wq wa wr wf s
  rw [XF.val_congr_lt (fun j hj => hqf j hj), val_window fqp (P + 2) (P + 2) (2 * P + 4) (by omega),
    XF.val_congr_lt (fun j hj => hqp j hj), XF.val_mulBits, XF.val_zext P _ (2 * P + 4) (by omega),
    XF.val_zext (P + 5) _ (2 * P + 4) (by omega), hma, hR]

/-- `qe`: the estimate itself unless an exponent field is all ones. -/
theorem g_qe (f : Format) (av bv n m w : Nat) (fqe fqf fa fb : Nat → Bool) (hn : n = f.w) (hm : m = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k) (hb : ∀ k, k < f.w + f.p → fb k = bv.testBit k)
    (hfa : eF f av ≠ 2 ^ f.w - 1) (hfb : eF f bv ≠ 2 ^ f.w - 1)
    (h : ∀ k, k < w → fqe k =
      if ((XF.all n fun x => fa (m + x)) || XF.all n fun x => fb (m + x)) = true then
        XF.subBits w (fun x => XF.subBits w (fun x => fqf x) w (fun x => XF.zext 1 (fun x => fa x) x) x)
          w (fun x => XF.zext 1 (fun x => fb x) x) k
      else fqf k) :
    XF.val (fun x => fqe x) w = XF.val (fun x => fqf x) w := by
  have h1 := g_all f av n m fa hn hm ha
  have h2 := g_all f bv n m fb hn hm hb
  apply XF.val_congr_lt
  intro k hk
  rw [h k hk, h1, h2]
  simp [hfa, hfb]

/-- `qb = qe·mb` at `P + 2` bits. -/
theorem g_qb (P w wm : Nat) (hw : w = P + 2) (hwm : wm = P) (fqb fqe fmb : Nat → Bool) (qe mb : Nat)
    (hqe : XF.val (fun x => fqe x) (P + 2) = qe) (hmb : XF.val (fun k => fmb k) P = mb)
    (h : ∀ k, k < w → fqb k = XF.mulBits w (fun x => fqe x) w (fun x => XF.zext wm (fun k => fmb k) x) k) :
    XF.val (fun x => fqb x) (P + 2) = qe * mb % 2 ^ (P + 2) := by
  subst w wm
  rw [XF.val_congr_lt (fun j hj => h j hj), XF.val_mulBits, XF.val_zext P _ (P + 2) (by omega), hqe, hmb]

/-- `rm = {ma[0], zr} - qb` at `P + 2` bits. -/
theorem g_rm (P w : Nat) (hw : w = P + 2) (frm fzr fma fqb : Nat → Bool) (ma qb : Nat) (hP : 1 ≤ P)
    (hzr : ∀ k, k < P + 1 → fzr k = false) (hma : XF.val (fun k => fma k) P = ma)
    (hqb : XF.val (fun x => fqb x) (P + 2) = qb)
    (h : ∀ k, k < w → frm k =
      XF.subBits w (fun x => if x < P + 1 then fzr x else fma (x - (P + 1))) w (fun x => fqb x) k) :
    XF.val (fun x => frm x) (P + 2) = (ma % 2 * 2 ^ (P + 1) + (2 ^ (P + 2) - qb)) % 2 ^ (P + 2) := by
  subst w
  rw [XF.val_congr_lt (fun j hj => h j hj), val_subBits, Nat.max_self, hqb]
  have hc := val_cat fzr fma (P + 1) 1
  rw [show P + 1 + 1 = P + 2 by omega] at hc
  have h0 : (fma 0).toNat = ma % 2 := by
    have hb := bit_eq_of_val fma P ma 0 hma (by omega)
    rw [hb]
    have : ma % 2 = 0 ∨ ma % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]
  rw [hc, val_all_false fzr (P + 1) hzr, val_one, h0, Nat.zero_add, Nat.mul_comm (2 ^ (P + 1))]

/-- `ge1 = (rm >= mb)`. -/
theorem g_ge1 (P w wm : Nat) (hw : w = P + 2) (hwm : wm = P) (fge frm fmb : Nat → Bool) (rm mb : Nat)
    (hrm : XF.val (fun x => frm x) (P + 2) = rm) (hmb : XF.val (fun k => fmb k) P = mb)
    (h : fge 0 = decide (XF.val (fun x => frm x) (max w wm) ≥
      XF.val (fun x => XF.zext wm (fun k => fmb k) x) (max w wm))) :
    fge 0 = decide (mb ≤ rm) := by
  subst w wm
  rw [h, show max (P + 2) P = P + 2 by omega, hrm, XF.val_zext P _ (P + 2) (by omega), hmb]

/-- `ge2 = (rm >= {mb, 1'b0})`. -/
theorem g_ge2 (P w wm : Nat) (hw : w = P + 2) (hwm : wm = P) (fge frm fmb : Nat → Bool) (rm mb : Nat)
    (hrm : XF.val (fun x => frm x) (P + 2) = rm) (hmb : XF.val (fun k => fmb k) P = mb)
    (h : fge 0 = decide (XF.val (fun x => frm x) (max w (wm + 1)) ≥
      XF.val (fun x => XF.zext (wm + 1) (fun x => if x = 0 then false else fmb (x - 1)) x) (max w (wm + 1)))) :
    fge 0 = decide (2 * mb ≤ rm) := by
  subst w wm
  rw [h, show max (P + 2) (P + 1) = P + 2 by omega, hrm, XF.val_zext (P + 1) _ (P + 2) (by omega), val_cons_false, hmb]

/-- `qq = qe + ge1 + ge2` at `P + 2` bits. -/
theorem g_qq (P w : Nat) (hw : w = P + 2) (fqq fqe fg1 fg2 : Nat → Bool) (qe : Nat)
    (hqe : XF.val (fun x => fqe x) (P + 2) = qe)
    (h : ∀ k, k < w → fqq k =
      XF.addBits w (fun x => XF.addBits w (fun x => fqe x) w (fun x => XF.zext 1 (fun k => fg1 k) x) x)
        w (fun x => XF.zext 1 (fun k => fg2 k) x) k) :
    XF.val (fun x => fqq x) (P + 2) = (qe + (fg1 0).toNat + (fg2 0).toNat) % 2 ^ (P + 2) := by
  subst w
  rw [XF.val_congr_lt (fun j hj => h j hj), val_addBits, val_addBits, XF.val_zext 1 _ (P + 2) (by omega),
    XF.val_zext 1 _ (P + 2) (by omega), val_one, val_one, hqe, Nat.mod_add_mod]

/-- `rnz = (rm != mb) & (rm != {mb, 1'b0}) & (|rm)`. -/
theorem g_rnz (P w wm : Nat) (hw : w = P + 2) (hwm : wm = P) (frnz frm fmb : Nat → Bool) (rm mb : Nat)
    (hrm : XF.val (fun x => frm x) (P + 2) = rm) (hmb : XF.val (fun k => fmb k) P = mb)
    (h : frnz 0 = (((!XF.eqv (max w wm) (fun x => frm x) fun x => XF.zext wm (fun k => fmb k) x) &&
        !XF.eqv (max w (wm + 1)) (fun x => frm x) fun x =>
          XF.zext (wm + 1) (fun x => if x = 0 then false else fmb (x - 1)) x) &&
      XF.any w fun x => frm x)) :
    frnz 0 = decide (rm ≠ mb ∧ rm ≠ 2 * mb ∧ rm ≠ 0) := by
  subst w wm
  rw [h, eqv_eq_decide_val, eqv_eq_decide_val, any_eq_decide_val, show max (P + 2) P = P + 2 by omega, show max (P + 2) (P + 1) = P + 2 by omega,
    hrm, XF.val_zext P _ (P + 2) (by omega), XF.val_zext (P + 1) _ (P + 2) (by omega), val_cons_false, hmb]
  by_cases h1 : rm = mb <;> by_cases h2 : rm = 2 * mb <;> by_cases h3 : rm = 0 <;> simp [h1, h2, h3]

/-! ## The core -/

/-- **The Newton core.** For normalized significands (`ma < 2^P`, `2^(P-1) ≤ mb < 2^P`) and `N ≥ 1` steps with
`P + 2 ≤ 2^(N+2)`, the printed equations of the core give the quotient and the sticky of `P + 2` restoring steps. -/
theorem core (P N : Nat) (NIi : Int) (hNI : NIi = (N : Int)) (hP : 2 ≤ P) (hN1 : 1 ≤ N) (hNP : P + 2 ≤ 2 ^ (N + 2))
    (f_ma f_mb f_zr f_r f_dr f_u f_ru f_qp f_qf f_qe f_qb f_rm f_ge1 f_ge2 f_qq f_rnz : Nat → Bool)
    (c45 c0 : LVec) (h45 : XF.val (fun x => c45.boolAt x) 6 = 45) (hc0w : c0.width = 4)
    (hc0 : XF.val (fun x => c0.boolAt x) 4 = 0) (ma mb : Nat)
    (hma : XF.val (fun k => f_ma k) P = ma) (hmb : XF.val (fun k => f_mb k) P = mb)
    (ha : ma < 2 ^ P) (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P)
    (hqe : XF.val (fun x => f_qe x) (P + 2) = XF.val (fun x => f_qf x) (P + 2))
    (eq_zr_plain_12 : ∀ (k : Nat), k < P + 1 → f_zr k = false)
    (eq_r_plain_13 : ∀ (k : Nat), k < ((P : Int) + 4 + 1).toNat → f_r k = XF.addBits ((P : Int) + 4 + 1).toNat (fun x => XF.subBits ((P : Int) + 4 + 1).toNat (fun x => if x < ((P : Int) + -2 + 1).toNat then f_zr x else c45.boolAt (x - ((P : Int) + -2 + 1).toNat)) ((P : Int) + 4 + 1).toNat (fun x => XF.zext (((P : Int) + -1).natAbs + 1 + c0.width) (fun x => if x < c0.width then c0.boolAt x else f_mb (x - c0.width)) x) x) ((P : Int) + 4 + 1).toNat (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_mb k) x) k)
    (eq_qp_plain_14 : ∀ (k : Nat), k < ((P : Int) + ((P : Int) + 4) + -1).natAbs + 1 → f_qp k = XF.mulBits (((P : Int) + ((P : Int) + 4) + -1).natAbs + 1) (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_ma k) x) (((P : Int) + ((P : Int) + 4) + -1).natAbs + 1) (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => f_r (rmN ((P : Int) + 4 + 1) (NIi) 0 + k)) x) k)
    (eq_qf_plain_15 : ∀ (k : Nat), k < ((P : Int) + 1).natAbs + 1 → f_qf k = f_qp (((P : Int) + 4 + -2).toNat + k))
    (eq_qb_plain_17 : ∀ (k : Nat), k < ((P : Int) + 1).natAbs + 1 → f_qb k = XF.mulBits (((P : Int) + 1).natAbs + 1) (fun x => f_qe x) (((P : Int) + 1).natAbs + 1) (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_mb k) x) k)
    (eq_rm_plain_18 : ∀ (k : Nat), k < ((P : Int) + 1).natAbs + 1 → f_rm k = XF.subBits (((P : Int) + 1).natAbs + 1) (fun x => if x < P + 1 then f_zr x else f_ma (x - (P + 1))) (((P : Int) + 1).natAbs + 1) (fun x => f_qb x) k)
    (eq_ge1_plain_19 : f_ge1 0 = decide (XF.val (fun x => f_rm x) (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1)) ≥ XF.val (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_mb k) x) (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1))))
    (eq_ge2_plain_20 : f_ge2 0 = decide (XF.val (fun x => f_rm x) (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1 + 1)) ≥ XF.val (fun x => XF.zext (((P : Int) + -1).natAbs + 1 + 1) (fun x => if x = 0 then false else f_mb (x - 1)) x) (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1 + 1))))
    (eq_qq_plain_21 : ∀ (k : Nat), k < ((P : Int) + 1).natAbs + 1 → f_qq k = XF.addBits (((P : Int) + 1).natAbs + 1) (fun x => XF.addBits (((P : Int) + 1).natAbs + 1) (fun x => f_qe x) (((P : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_ge1 k) x) x) (((P : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_ge2 k) x) k)
    (eq_rnz_plain_22 : f_rnz 0 = (((!XF.eqv (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1)) (fun x => f_rm x) fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_mb k) x) && !XF.eqv (max (((P : Int) + 1).natAbs + 1) (((P : Int) + -1).natAbs + 1 + 1)) (fun x => f_rm x) fun x => XF.zext (((P : Int) + -1).natAbs + 1 + 1) (fun x => if x = 0 then false else f_mb (x - 1)) x) && XF.any (((P : Int) + 1).natAbs + 1) fun x => f_rm x))
    (eq_dr_newton_0 : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + ((P : Int) + 4)).toNat → f_dr (rmN ((P : Int) + ((P : Int) + 4)) ((i : Int)) 0 + k) = XF.mulBits ((P : Int) + ((P : Int) + 4)).toNat (fun x => XF.zext (((P : Int) + -1).natAbs + 1) (fun k => f_mb k) x) ((P : Int) + ((P : Int) + 4)).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => f_r (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (eq_u_newton_1 : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + 4 + 1).toNat → f_u (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k) = !f_dr (rmN ((P : Int) + ((P : Int) + 4)) ((i : Int)) ((P : Int) + -1) + k))
    (eq_ru_newton_2 : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < (2 * ((P : Int) + 4) + 1).toNat → f_ru (rmN (2 * ((P : Int) + 4) + 1) ((i : Int)) 0 + k) = XF.mulBits (2 * ((P : Int) + 4) + 1).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => f_r (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) (2 * ((P : Int) + 4) + 1).toNat (fun x => XF.zext ((P : Int) + 4 + 1).toNat (fun k => f_u (rmN ((P : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (eq_r_newton_3 : ∀ (i : Nat), (i : Int) < NIi → ∀ (k : Nat), k < ((P : Int) + 4 + 1).toNat → f_r (rmN ((P : Int) + 4 + 1) ((i : Int) + 1) 0 + k) = f_ru (rmN (2 * ((P : Int) + 4) + 1) ((i : Int)) ((P : Int) + 4) + k)) :
    XF.val (fun x => f_qq x) (P + 2) = restQuo mb ma (P + 2) ∧ f_rnz 0 = decide (restRem mb ma (P + 2) ≠ 0) := by
  have hr0 : XF.val (fun x => f_r x) (P + 5) = nwR0 P mb :=
    g_r0 P _ _ _ (by omega) (by omega) (by omega) hP f_r f_zr f_mb c45 c0 mb eq_zr_plain_12 h45 hc0w hc0 hmb hb1 hb2
      eq_r_plain_13
  have hrows := newton_rows P N NIi hNI hP f_r f_dr f_u f_ru f_mb mb hmb hr0
    eq_dr_newton_0 eq_u_newton_1 eq_ru_newton_2 eq_r_newton_3
  have hoff : rmN ((P : Int) + 4 + 1) NIi 0 = N * (P + 5) := rmN_eq _ _ _ (P + 5) N 0 (by omega) hNI rfl
  have hR : XF.val (fun x => f_r (rmN ((P : Int) + 4 + 1) NIi 0 + x)) (P + 5) = nwIter P mb N := by
    rw [hoff]; exact hrows N (Nat.le_refl _)
  have hqf : XF.val (fun x => f_qf x) (P + 2) = nwQf P N ma mb :=
    g_qf P _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) f_qf f_qp f_ma f_r ma _ hma hR
      eq_qp_plain_14 eq_qf_plain_15
  have hqe' : XF.val (fun x => f_qe x) (P + 2) = nwQf P N ma mb := hqe.trans hqf
  have hqb := g_qb P _ _ (by omega) (by omega) f_qb f_qe f_mb _ mb hqe' hmb eq_qb_plain_17
  have hrm : XF.val (fun x => f_rm x) (P + 2) = nwRm P N ma mb :=
    g_rm P _ (by omega) f_rm f_zr f_ma f_qb ma _ (by omega) eq_zr_plain_12 hma hqb eq_rm_plain_18
  have hge1 := g_ge1 P _ _ (by omega) (by omega) f_ge1 f_rm f_mb _ mb hrm hmb eq_ge1_plain_19
  have hge2 := g_ge2 P _ _ (by omega) (by omega) f_ge2 f_rm f_mb _ mb hrm hmb eq_ge2_plain_20
  have hqq := g_qq P _ (by omega) f_qq f_qe f_ge1 f_ge2 _ hqe' eq_qq_plain_21
  have hrnz := g_rnz P _ _ (by omega) (by omega) f_rnz f_rm f_mb _ mb hrm hmb eq_rnz_plain_22
  obtain ⟨hQ, hS⟩ := newton_rest P N ma mb hP ha hb1 hb2 hN1 hNP
  refine ⟨?_, ?_⟩
  · rw [hqq, ← hQ, hge1, hge2]
    unfold nwQQ
    by_cases c1 : mb ≤ nwRm P N ma mb <;> by_cases c2 : 2 * mb ≤ nwRm P N ma mb <;> simp [c1, c2]
  · rw [hrnz]
    exact decide_eq_decide.2 hS

end Glue
end SvGolf.FdivParam

end NwG1

/-! # Section `NwG2`: Glue: the sticky bit and the chain (new in this reference) -/

section NwG2

set_option maxRecDepth 100000

/-!
# Task `fdivp`, the Newton reference: the chain, from the printed equations of `sv_equations` to the value of `q`

`DpG5` of `fdivp.lean` for the netlist `fdivp_newton.sv`: `chain` takes its 46 equations exactly as `sv_equations`
states them and concludes `XF.val q (W + P) = OutN f a b`. Outside the core it is `DpG5`'s chain (the same lemmas of
`DpG1`..`DpG4`); the core (`NwG1`'s `core`) gives `qq` and `rnz` for finite nonzero operands, where `qe = qf`, after
`NI = $clog2((P + 9) / 8) + 1` steps (`nwNI_spec`), and `g_inc_rnz` reads the one-bit sticky `rnz` where D3 reads
`|rr[P+2]`. The two constants of `r[0]` (`6'd45` and `4'd0`) are the vectors `c45` and `c0`, whose values the solution
checks by `decide`.
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four
  val_not val_cons_false)
open SvGolf.IEEE754

/-- `inc`, with the core's one-bit sticky `rnz` (`g_inc` with `|rr[P+2]`). -/
theorem g_inc_rnz (P EW qsv qmv qqv rrv dv one : Nat) (hone : one = 1) (hP : 1 ≤ P)
    (fqs fqm fdsh fqq frnz finc : Nat → Bool)
    (hqs : XF.val fqs (P + 1) = qsv) (hqm : XF.val fqm (P + 1) = qmv) (hd : XF.val fdsh EW = dv)
    (hqq : XF.val fqq (P + 2) = qqv) (hrnz : frnz 0 = decide (rrv ≠ 0))
    (hqsd : qsv = qmv / 2 ^ dv) (hlt : qmv < 2 ^ (P + 1))
    (h : finc 0 = (fqs 0 && ((fqq (P + 1) && fqq 0 || frnz 0 || !XF.eqv (P + 1) (fun x => XF.shlBits
      (XF.zext (P + 1) fun x => fqs x) EW (fun x => fdsh x) x) fun x => fqm x) || fqs one))) :
    finc 0 = decide (qsv % 2 = 1 ∧ ((2 ^ (P + 1) ≤ qqv ∧ qqv % 2 = 1 ∨ rrv ≠ 0) ∨
      qmv % 2 ^ dv ≠ 0 ∨ qsv / 2 % 2 = 1)) := by
  subst hone
  have hq0 : fqs 0 = decide (qsv % 2 = 1) := by
    have := bit_eq_of_val fqs (P + 1) qsv 0 hqs (by omega)
    simpa using this
  have hq1 : fqs 1 = decide (qsv / 2 % 2 = 1) := by
    have := bit_eq_of_val fqs (P + 1) qsv 1 hqs (by omega)
    simpa using this
  have hqqtop : fqq (P + 1) = decide (2 ^ (P + 1) ≤ qqv) := by
    have := top_bit_succ_iff fqq (P + 1) qqv hqq
    by_cases hc : 2 ^ (P + 1) ≤ qqv
    · rw [this.2 hc]; simp [hc]
    · have hb : ¬ fqq (P + 1) = true := fun hh => hc (this.1 hh)
      simp at hb
      rw [hb]; simp [hc]
  have hqq0 : fqq 0 = decide (qqv % 2 = 1) := by
    have := bit_eq_of_val fqq (P + 2) qqv 0 hqq (by omega)
    simpa using this
  have heqv := g_eqv P EW qsv qmv dv fqs fqm fdsh hqs hqm hd hqsd hlt
  rw [h, hq0, hq1, hqqtop, hqq0, hrnz, heqv, Bool.eq_iff_iff]
  simp <;> first | omega | grind

/-- Finite nonzero operands: neither exponent field is all ones and neither operand is a zero. -/
theorem fin_ops (f : Format) (av bv : Nat) (hns : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv)) :
    (eF f av ≠ 2 ^ f.w - 1 ∧ ¬ (eF f av = 0 ∧ fF f av = 0)) ∧
      (eF f bv ≠ 2 ^ f.w - 1 ∧ ¬ (eF f bv = 0 ∧ fF f bv = 0)) := by
  unfold cNanN cInfN cZeroN nanN infN zeroN at hns
  omega

set_option maxHeartbeats 4000000 in
theorem chain (f : Format)
    (f_s f_ea_nz f_eb_nz f_c_nan f_c_inf f_c_zero f_na_r f_nb_r f_ya_r f_yb_r f_ma f_mb f_zr f_r f_qp f_qf f_qe f_qb
      f_rm f_ge1 f_ge2 f_qq f_rnz f_adj f_qm f_onesW f_emw f_E f_ovf f_dsh f_qs f_inc f_ef f_mag f_q f_dr f_u f_ru
      f_a f_b : Nat → Bool)
    (c45 c0 : LVec) (h45 : XF.val (fun x => c45.boolAt x) 6 = 45) (hc0w : c0.width = 4)
    (hc0 : XF.val (fun x => c0.boolAt x) 4 = 0)
    (av bv : Nat)
    (ha : ∀ k, k < f.w + f.p → f_a k = av.testBit k) (hb : ∀ k, k < f.w + f.p → f_b k = bv.testBit k)
    (eq_s_plain_0 : f_s 0 = (f_a ((f.w : Int) + (f.p : Int) + -1).toNat ^^ f_b ((f.w : Int) + (f.p : Int) + -1).toNat))
    (eq_ea_nz_plain_1 : f_ea_nz 0 = XF.any ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_a (((f.p : Int) - 1).toNat + x))
    (eq_eb_nz_plain_2 : f_eb_nz 0 = XF.any ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_b (((f.p : Int) - 1).toNat + x))
    (eq_c_nan_plain_3 : f_c_nan 0 = (((((XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_a (((f.p : Int) - 1).toNat + x)) && XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_a x) || (XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_b (((f.p : Int) - 1).toNat + x)) && XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_b x) || (((XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_a (((f.p : Int) - 1).toNat + x)) && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_a x) && XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_b (((f.p : Int) - 1).toNat + x)) && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_b x) || (!f_ea_nz 0 && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_a x) && !f_eb_nz 0 && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_b x))
    (eq_c_inf_plain_4 : f_c_inf 0 = (((XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_a (((f.p : Int) - 1).toNat + x)) && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_a x) || !f_eb_nz 0 && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_b x))
    (eq_c_zero_plain_5 : f_c_zero 0 = (((XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_b (((f.p : Int) - 1).toNat + x)) && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_b x) || !f_ea_nz 0 && !XF.any ((f.p : Int) - 1 + -1 + 1).toNat fun x => f_a x))
    (eq_na_r_plain_6 : ∀ (k : Nat), k < f.p → f_na_r k = if k < ((f.p : Int) - 1 + -1 + 1).toNat then f_a k else f_ea_nz (k - ((f.p : Int) - 1 + -1 + 1).toNat))
    (eq_nb_r_plain_7 : ∀ (k : Nat), k < f.p → f_nb_r k = if k < ((f.p : Int) - 1 + -1 + 1).toNat then f_b k else f_eb_nz (k - ((f.p : Int) - 1 + -1 + 1).toNat))
    (eq_ya_r_plain_8 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r k = if max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32 < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_ea_nz 0 = true then XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun x => f_a (((f.p : Int) - 1).toNat + x)) k else XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat k else XF.zext (max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32) (fun x => if f_ea_nz 0 = true then XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun x => f_a (((f.p : Int) - 1).toNat + x)) x else XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32) x) k)
    (eq_yb_r_plain_9 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r k = if max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32 < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_eb_nz 0 = true then XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun x => f_b (((f.p : Int) - 1).toNat + x)) k else XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat k else XF.zext (max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32) (fun x => if f_eb_nz 0 = true then XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun x => f_b (((f.p : Int) - 1).toNat + x)) x else XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat 32) x) k)
    (eq_ma_plain_10 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_ma k = f_na_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k))
    (eq_mb_plain_11 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_mb k = f_nb_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k))
    (eq_zr_plain_12 : ∀ (k : Nat), k < f.p + 1 → f_zr k = false)
    (eq_r_plain_13 : ∀ (k : Nat), k < ((f.p : Int) + 4 + 1).toNat → f_r k = XF.addBits ((f.p : Int) + 4 + 1).toNat (fun x => XF.subBits ((f.p : Int) + 4 + 1).toNat (fun x => if x < ((f.p : Int) + -2 + 1).toNat then f_zr x else c45.boolAt (x - ((f.p : Int) + -2 + 1).toNat)) ((f.p : Int) + 4 + 1).toNat (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1 + c0.width) (fun x => if x < c0.width then c0.boolAt x else f_mb (x - c0.width)) x) x) ((f.p : Int) + 4 + 1).toNat (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_mb k) x) k)
    (eq_qp_plain_14 : ∀ (k : Nat), k < ((f.p : Int) + ((f.p : Int) + 4) + -1).natAbs + 1 → f_qp k = XF.mulBits (((f.p : Int) + ((f.p : Int) + 4) + -1).natAbs + 1) (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_ma k) x) (((f.p : Int) + ((f.p : Int) + 4) + -1).natAbs + 1) (fun x => XF.zext ((f.p : Int) + 4 + 1).toNat (fun k => f_r (rmN ((f.p : Int) + 4 + 1) (((clog2 (((f.p : Int) + 9) / 8).toNat : Nat) : Int) + 1) 0 + k)) x) k)
    (eq_qf_plain_15 : ∀ (k : Nat), k < ((f.p : Int) + 1).natAbs + 1 → f_qf k = f_qp (((f.p : Int) + 4 + -2).toNat + k))
    (eq_qe_plain_16 : ∀ (k : Nat), k < ((f.p : Int) + 1).natAbs + 1 → f_qe k = if ((XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_a (((f.p : Int) - 1).toNat + x)) || XF.all ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat fun x => f_b (((f.p : Int) - 1).toNat + x)) = true then XF.subBits (((f.p : Int) + 1).natAbs + 1) (fun x => XF.subBits (((f.p : Int) + 1).natAbs + 1) (fun x => f_qf x) (((f.p : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun x => f_a x) x) x) (((f.p : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun x => f_b x) x) k else f_qf k)
    (eq_qb_plain_17 : ∀ (k : Nat), k < ((f.p : Int) + 1).natAbs + 1 → f_qb k = XF.mulBits (((f.p : Int) + 1).natAbs + 1) (fun x => f_qe x) (((f.p : Int) + 1).natAbs + 1) (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_mb k) x) k)
    (eq_rm_plain_18 : ∀ (k : Nat), k < ((f.p : Int) + 1).natAbs + 1 → f_rm k = XF.subBits (((f.p : Int) + 1).natAbs + 1) (fun x => if x < f.p + 1 then f_zr x else f_ma (x - (f.p + 1))) (((f.p : Int) + 1).natAbs + 1) (fun x => f_qb x) k)
    (eq_ge1_plain_19 : f_ge1 0 = decide (XF.val (fun x => f_rm x) (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1)) ≥ XF.val (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_mb k) x) (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1))))
    (eq_ge2_plain_20 : f_ge2 0 = decide (XF.val (fun x => f_rm x) (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1 + 1)) ≥ XF.val (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1 + 1) (fun x => if x = 0 then false else f_mb (x - 1)) x) (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1 + 1))))
    (eq_qq_plain_21 : ∀ (k : Nat), k < ((f.p : Int) + 1).natAbs + 1 → f_qq k = XF.addBits (((f.p : Int) + 1).natAbs + 1) (fun x => XF.addBits (((f.p : Int) + 1).natAbs + 1) (fun x => f_qe x) (((f.p : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_ge1 k) x) x) (((f.p : Int) + 1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_ge2 k) x) k)
    (eq_rnz_plain_22 : f_rnz 0 = (((!XF.eqv (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1)) (fun x => f_rm x) fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_mb k) x) && !XF.eqv (max (((f.p : Int) + 1).natAbs + 1) (((f.p : Int) + -1).natAbs + 1 + 1)) (fun x => f_rm x) fun x => XF.zext (((f.p : Int) + -1).natAbs + 1 + 1) (fun x => if x = 0 then false else f_mb (x - 1)) x) && XF.any (((f.p : Int) + 1).natAbs + 1) fun x => f_rm x))
    (eq_adj_plain_23 : f_adj 0 = !f_qq (f.p + 1))
    (eq_qm_plain_24 : ∀ (k : Nat), k < f.p + 1 → f_qm k = if f_qq (f.p + 1) = true then f_qq (Int.toNat 1 + k) else f_qq k)
    (eq_onesW_plain_25 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_onesW k = true)
    (eq_emw_plain_26 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_emw k = XF.shrBits (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_E_plain_27 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_E k = XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.addBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + -1).natAbs + 1) (fun k => f_emw k) x) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_adj k) x) k)
    (eq_ovf_plain_28 : f_ovf 0 = (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && ((XF.any ((f.w : Int) + (f.p : Int) + 1 + -2 - (f.w : Int) + 1).toNat fun x => f_E (f.w + x)) || XF.all ((f.w : Int) + -1 + 1).toNat fun x => f_E x)))
    (eq_dsh_plain_29 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_dsh k = if max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)) < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) k else XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.constBit 1 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) k else XF.zext (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x else XF.subBits (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.constBit 1 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x) (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) x) k)
    (eq_qs_plain_30 : ∀ (k : Nat), k < f.p + 1 → f_qs k = XF.shrBits (f.p + 1) (fun x => f_qm x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_dsh x) k)
    (eq_inc_plain_31 : f_inc 0 = (f_qs 0 && ((f_qq (f.p + 1) && f_qq 0 || f_rnz 0 || !XF.eqv (f.p + 1) (fun x => XF.shlBits (XF.zext (f.p + 1) fun x => f_qs x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_dsh x) x) fun x => f_qm x) || f_qs (Int.toNat 1))))
    (eq_ef_plain_32 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_ef k = if max ((f.w : Int) + -1 + 1).toNat 32 < ((f.w : Int) + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) k else XF.constBit 0 (((f.w : Int) + -1).natAbs + 1) k else XF.zext (max ((f.w : Int) + -1 + 1).toNat 32) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) x else XF.constBit 0 (max ((f.w : Int) + -1 + 1).toNat 32) x) k)
    (eq_mag_plain_33 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 → f_mag k = XF.addBits (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => if x < ((f.p : Int) + -1).toNat then f_qs (Int.toNat 1 + x) else f_ef (x - ((f.p : Int) + -1).toNat)) (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => XF.zext 1 (fun k => f_inc k) x) k)
    (eq_q_plain_34 : f_q ((f.w : Int) + (f.p : Int) + -1).toNat = (!f_c_nan 0 && f_s 0))
    (eq_q_plain_35 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat → f_q (((f.p : Int) - 1).toNat + k) = if max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat) < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat then if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) k else if f_c_zero 0 = true then XF.constBit 0 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat k else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) k else XF.zext (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) (fun x => if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) x else if f_c_zero 0 = true then XF.constBit 0 (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) x else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) x) k)
    (eq_q_plain_36 : f_q ((f.p : Int) - 1 + -1).toNat = (f_c_nan 0 || !(f_c_nan 0 || f_c_inf 0 || f_c_zero 0 || f_ovf 0) && f_mag ((f.p : Int) - 1 + -1).toNat))
    (eq_na_r_norm_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_na_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_nb_r_norm_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_nb_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_ya_r_norm_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_yb_r_norm_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_dr_newton_0 : ∀ (i : Nat), (i : Int) < ((clog2 (((f.p : Int) + 9) / 8).toNat : Nat) : Int) + 1 → ∀ (k : Nat), k < ((f.p : Int) + ((f.p : Int) + 4)).toNat → f_dr (rmN ((f.p : Int) + ((f.p : Int) + 4)) ((i : Int)) 0 + k) = XF.mulBits ((f.p : Int) + ((f.p : Int) + 4)).toNat (fun x => XF.zext (((f.p : Int) + -1).natAbs + 1) (fun k => f_mb k) x) ((f.p : Int) + ((f.p : Int) + 4)).toNat (fun x => XF.zext ((f.p : Int) + 4 + 1).toNat (fun k => f_r (rmN ((f.p : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (eq_u_newton_1 : ∀ (i : Nat), (i : Int) < ((clog2 (((f.p : Int) + 9) / 8).toNat : Nat) : Int) + 1 → ∀ (k : Nat), k < ((f.p : Int) + 4 + 1).toNat → f_u (rmN ((f.p : Int) + 4 + 1) ((i : Int)) 0 + k) = !f_dr (rmN ((f.p : Int) + ((f.p : Int) + 4)) ((i : Int)) ((f.p : Int) + -1) + k))
    (eq_ru_newton_2 : ∀ (i : Nat), (i : Int) < ((clog2 (((f.p : Int) + 9) / 8).toNat : Nat) : Int) + 1 → ∀ (k : Nat), k < (2 * ((f.p : Int) + 4) + 1).toNat → f_ru (rmN (2 * ((f.p : Int) + 4) + 1) ((i : Int)) 0 + k) = XF.mulBits (2 * ((f.p : Int) + 4) + 1).toNat (fun x => XF.zext ((f.p : Int) + 4 + 1).toNat (fun k => f_r (rmN ((f.p : Int) + 4 + 1) ((i : Int)) 0 + k)) x) (2 * ((f.p : Int) + 4) + 1).toNat (fun x => XF.zext ((f.p : Int) + 4 + 1).toNat (fun k => f_u (rmN ((f.p : Int) + 4 + 1) ((i : Int)) 0 + k)) x) k)
    (eq_r_newton_3 : ∀ (i : Nat), (i : Int) < ((clog2 (((f.p : Int) + 9) / 8).toNat : Nat) : Int) + 1 → ∀ (k : Nat), k < ((f.p : Int) + 4 + 1).toNat → f_r (rmN ((f.p : Int) + 4 + 1) ((i : Int) + 1) 0 + k) = f_ru (rmN (2 * ((f.p : Int) + 4) + 1) ((i : Int)) ((f.p : Int) + 4) + k))
    (eq_q_lo_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) - 1 + -1 → f_q i = (!(f_c_nan 0 || f_c_inf 0 || f_c_zero 0 || f_ovf 0) && f_mag i))
    : XF.val (fun x => f_q x) (f.w + f.p) = OutN f av bv := by
  have hfw := f.hw
  have hfp := f.hp
  have ht : f.t = f.p - 1 := rfl
  -- unpack and classify
  have b_s : f_s 0 = decide ((sF f av + sF f bv) % 2 = 1) :=
    g_s f av bv _ f_s f_a f_b (by omega) ha hb eq_s_plain_0
  have b_ea : f_ea_nz 0 = decide (eF f av ≠ 0) :=
    g_nz f av _ _ f_ea_nz f_a (by omega) (by omega) ha eq_ea_nz_plain_1
  have b_eb : f_eb_nz 0 = decide (eF f bv ≠ 0) :=
    g_nz f bv _ _ f_eb_nz f_b (by omega) (by omega) hb eq_eb_nz_plain_2
  have b_cn : f_c_nan 0 = decide (cNanN f av bv) :=
    g_cnan f av bv _ _ _ f_c_nan f_ea_nz f_eb_nz f_a f_b (by omega) (by omega) (by omega) ha hb b_ea b_eb
      eq_c_nan_plain_3
  have b_ci : f_c_inf 0 = decide (cInfN f av bv) :=
    g_cinf f av bv _ _ _ f_c_inf f_ea_nz f_eb_nz f_a f_b (by omega) (by omega) (by omega) ha hb b_eb
      eq_c_inf_plain_4
  have b_cz : f_c_zero 0 = decide (cZeroN f av bv) :=
    g_czero f av bv _ _ _ f_c_zero f_ea_nz f_eb_nz f_a f_b (by omega) (by omega) (by omega) ha hb b_ea
      eq_c_zero_plain_5
  -- row 0 of the normalizer
  have hn0a := g_n0 f av _ (by omega) f_na_r f_a f_ea_nz ha b_ea eq_na_r_plain_6
  have hn0b := g_n0 f bv _ (by omega) f_nb_r f_b f_eb_nz hb b_eb eq_nb_r_plain_7
  have hy0a := g_y0 f av _ _ _ (by omega) (by omega) (by omega) f_ya_r f_a f_ea_nz ha b_ea eq_ya_r_plain_8
  have hy0b := g_y0 f bv _ _ _ (by omega) (by omega) (by omega) f_yb_r f_b f_eb_nz hb b_eb eq_yb_r_plain_9
  -- the normalizer rows
  have hrows_a := norm_rows f.p _ _ (by omega) f.hp (by omega) f_na_r f_ya_r (sigN f av) (xeN f av) hn0a hy0a
    eq_na_r_norm_0 eq_ya_r_norm_2
  have hrows_b := norm_rows f.p _ _ (by omega) f.hp (by omega) f_nb_r f_yb_r (sigN f bv) (xeN f bv) hn0b hy0b
    eq_nb_r_norm_1 eq_yb_r_norm_3
  have hna_top := hrows_a (f.p - 1) (Nat.le_refl _)
  have hnb_top := hrows_b (f.p - 1) (Nat.le_refl _)
  have hwe : ((f.w : Int) + (f.p : Int) + 1).toNat = f.w + f.p + 1 := by omega
  rw [hwe] at hna_top hnb_top
  clear hwe
  have hna_val : XF.val (fun x => f_na_r ((f.p - 1) * f.p + x)) f.p = naN f av := congrArg Prod.fst hna_top
  have hnb_val : XF.val (fun x => f_nb_r ((f.p - 1) * f.p + x)) f.p = naN f bv := congrArg Prod.fst hnb_top
  have hya_val : XF.val (fun x => f_ya_r ((f.p - 1) * (f.w + f.p + 1) + x)) (f.w + f.p + 1) = yaN f av :=
    congrArg Prod.snd hna_top
  have hyb_val : XF.val (fun x => f_yb_r ((f.p - 1) * (f.w + f.p + 1) + x)) (f.w + f.p + 1) = yaN f bv :=
    congrArg Prod.snd hnb_top
  have hrtop : rmN ((f.p : Int)) ((f.p : Int) + -1) 0 = (f.p - 1) * f.p :=
    rmN_eq _ _ _ f.p (f.p - 1) 0 (by omega) (by omega) (by omega)
  have hrtopE : rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 = (f.p - 1) * (f.w + f.p + 1) :=
    rmN_eq _ _ _ (f.w + f.p + 1) (f.p - 1) 0 (by omega) (by omega) (by omega)
  -- the normalized significands
  have hma : XF.val (fun x => f_ma x) f.p = naN f av :=
    g_copy f.p _ _ _ (by omega) f_ma f_na_r (by rw [hrtop]; exact hna_val) eq_ma_plain_10
  have hmb : XF.val (fun x => f_mb x) f.p = naN f bv :=
    g_copy f.p _ _ _ (by omega) f_mb f_nb_r (by rw [hrtop]; exact hnb_val) eq_mb_plain_11
  -- the datapath, for finite nonzero operands
  have hdp : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      f_ovf 0 = decide (ovfN f av bv) ∧ XF.val (fun x => f_mag x) (f.w + f.t) = magN f av bv := by
    intro hns
    obtain ⟨hfa, hfb⟩ := fin_ops f av bv hns
    clear hns
    obtain ⟨_, -, -, -, -, -, hna_hi⟩ := norm_facts f av hfa.2 hfa.1
    obtain ⟨_, -, -, -, -, hnb_lo, hnb_hi⟩ := norm_facts f bv hfb.2 hfb.1
    -- the Newton core: `qe = qf` (no exponent field is all ones), then `NI` steps
    have hqe : XF.val (fun x => f_qe x) (f.p + 2) = XF.val (fun x => f_qf x) (f.p + 2) := by
      have h := g_qe f av bv _ _ _ f_qe f_qf f_a f_b (by omega) (by omega) ha hb hfa.1 hfb.1 eq_qe_plain_16
      rwa [show ((f.p : Int) + 1).natAbs + 1 = f.p + 2 by omega] at h
    have hNI := nwNI_spec f.p
    obtain ⟨hqqv, hrnzv⟩ := core f.p (clog2 ((f.p + 9) / 8) + 1) _
      (by rw [show (((f.p : Int) + 9) / 8).toNat = (f.p + 9) / 8 by omega]; omega) f.hp hNI.1 hNI.2
      f_ma f_mb f_zr f_r f_dr f_u f_ru f_qp f_qf f_qe f_qb f_rm f_ge1 f_ge2 f_qq f_rnz c45 c0 h45 hc0w hc0
      (naN f av) (naN f bv) hma hmb hna_hi hnb_lo hnb_hi hqe eq_zr_plain_12 eq_r_plain_13 eq_qp_plain_14
      eq_qf_plain_15 eq_qb_plain_17 eq_rm_plain_18 eq_ge1_plain_19 eq_ge2_plain_20 eq_qq_plain_21 eq_rnz_plain_22
      eq_dr_newton_0 eq_u_newton_1 eq_ru_newton_2 eq_r_newton_3
    have hqq : XF.val (fun x => f_qq x) (f.p + 2) = qqN f av bv := hqqv
    have hrnz : f_rnz 0 = decide (rrN f av bv ≠ 0) := hrnzv
    have hqq_lt : qqN f av bv < 2 ^ (f.p + 2) := by
      have hl := XF.val_lt f_qq (f.p + 2)
      rw [hqq] at hl
      exact hl
    have hp21 : 2 ^ (f.p + 2) = 2 * 2 ^ (f.p + 1) := Nat.pow_succ' (n := f.p + 1)
    have hqm_lt : qmN f av bv < 2 ^ (f.p + 1) := by
      unfold qmN
      split <;> omega
    -- quotient normalization
    have b_adj : (f_adj 0).toNat = adjN f av bv := g_adj f.p (qqN f av bv) f_adj f_qq hqq eq_adj_plain_23
    have b_qm : XF.val (fun x => f_qm x) (f.p + 1) = qmN f av bv :=
      g_qm f.p _ (qqN f av bv) (by omega) f_qm f_qq hqq eq_qm_plain_24
    -- the exponent
    have b_emw := g_emw f _ (by omega) f_emw f_onesW eq_onesW_plain_25 eq_emw_plain_26
    have hEWe : ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 = f.w + f.p + 1 := by omega
    have b_E := g_E _ _ (ZN f) _ _ (yaN f av) (yaN f bv) f.emax (adjN f av bv) f_E f_ya_r f_yb_r f_emw f_adj
      (by unfold ZN; congr 1 <;> omega) (by omega) (by omega)
      (by rw [hEWe, hrtopE]; exact hya_val) (by rw [hEWe, hrtopE]; exact hyb_val) b_emw b_adj eq_E_plain_27
    have hEVp : XF.val (fun x => f_E x) _ = EN f av bv := b_E
    have hEV : XF.val (fun x => f_E x) (f.w + f.p + 1) = EN f av bv := by
      rw [← hEWe]; exact b_E
    clear hEWe
    have b_ovf : f_ovf 0 = decide (ovfE f (EN f av bv)) :=
      g_ovf f (EN f av bv) _ _ _ f_ovf f_E (by omega) (by omega) (by omega) hEV eq_ovf_plain_28
    have b_dsh := g_dsh f (EN f av bv) _ _ f_dsh f_E (by omega) (by omega) hEVp eq_dsh_plain_29
    have b_qs : XF.val (fun x => f_qs x) (f.p + 1) = qsN f av bv :=
      g_qs f.p _ (qmN f av bv) (dshE f (EN f av bv)) f_qs f_qm f_dsh b_qm b_dsh eq_qs_plain_30
    have b_inc : f_inc 0 = decide (incN f av bv) := by
      have h := g_inc_rnz f.p _ (qsN f av bv) (qmN f av bv) (qqN f av bv) (rrN f av bv) (dshE f (EN f av bv)) _
        (by omega) (by omega) f_qs f_qm f_dsh f_qq f_rnz f_inc b_qs b_qm b_dsh hqq hrnz rfl hqm_lt eq_inc_plain_31
      rw [h]
      exact decide_eq_decide.2 Iff.rfl
    have b_ef : XF.val (fun x => f_ef x) f.w = efN f av bv :=
      g_ef f (EN f av bv) _ _ _ _ f_ef f_E (by omega) (by omega) (by omega) (by omega) hEVp eq_ef_plain_32
    have hinc : (f_inc 0).toNat = if incN f av bv then 1 else 0 := by
      rw [b_inc]
      by_cases h : incN f av bv <;> simp [h]
    have b_mag := g_mag f.t f.w _ _ _ f.p (qsN f av bv) (efN f av bv) (if incN f av bv then 1 else 0)
      (by omega) (by omega) (by omega) (by omega) (by omega) f_mag f_qs f_ef f_inc b_qs b_ef hinc
      eq_mag_plain_33
    rw [show ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 = f.w + f.t by omega] at b_mag
    refine ⟨?_, b_mag⟩
    rw [b_ovf]
    exact decide_eq_decide.2 Iff.rfl
  -- the output
  have hfield := g_qfield _ _ _ f.w (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) f_q f_onesW f_mag (by omega)
    (by omega) eq_onesW_plain_25 eq_q_plain_35
  have hout := g_out _ _ f.w _ (f.w + f.p) (by omega) (by omega) (by omega) _ (by omega)
    (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_q f_mag _ eq_q_plain_34 hfield eq_q_plain_36
    eq_q_lo_0
  rw [hout]
  exact g_final f av bv (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_mag _ _ _ (by omega)
    (by omega) b_cn b_ci b_cz b_s hdp rfl rfl

end Glue
end SvGolf.FdivParam

end NwG2

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

set_option maxHeartbeats 400000 in
theorem fdiv_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
  have hNI := clog2_le (((P : Int) + 9) / 8).toNat
  have hs : CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
    sv_structure (rank := rippleRank
        (fun p =>
          if p ≤ 2 then 0 else if p ≤ 9 then 1 else if p ≤ 11 then P + 1 else if p = 12 then 0
          else if p = 13 then P + 2 else if p ≤ 24 then 5 * P + 6 + p else if p = 25 then 0 else if p = 26 then 1
          else if p = 27 then 5 * P + 31 else if p ≤ 29 then 5 * P + 32 else if p = 30 then 5 * P + 33
          else if p = 31 then 5 * P + 34 else if p = 32 then 5 * P + 32 else if p = 33 then 5 * P + 35
          else if p = 34 then 2 else 5 * P + 36)
        (fun blk p i =>
          if blk = "norm" then 2 + i.toNat
          else if blk = "newton" then P + 3 + 4 * i.toNat + p
          else 5 * P + 36))
    all_goals (intros; sv_rowmajor; omega)
  exact hs

theorem fdiv_interface (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (design.sem W P)) :
    (SvGolf.Tasks.FdivP.task W P).Interface 0 (design.sem W P) := by
  unfold SvGolf.Tasks.FdivP.task
  sv_interface

set_option maxHeartbeats 700000 in
theorem solution : Goal := by
  intro W P hWP
  obtain ⟨hW, hP⟩ := hWP
  obtain ⟨hc, ha, hso⟩ := fdiv_struct W P hW hP
  refine CombTask.satisfiedAt_of_comb (fdiv_interface W P hW hP hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨a, b, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.FdivP.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hav, hbv⟩ := hv
  have hNI := clog2_le (((P : Int) + 9) / 8).toNat
  sv_equations
  · have ha' : ∀ k, k < W + P → st.boolAt "a" k = a.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hav hk]; rfl
    have hb' : ∀ k, k < W + P → st.boolAt "b" k = b.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hbv hk]; rfl
    have hch := SvGolf.FdivParam.Glue.chain ⟨W, P, hW, hP⟩ (st.boolAt "s") (st.boolAt "ea_nz") (st.boolAt "eb_nz")
      (st.boolAt "c_nan") (st.boolAt "c_inf") (st.boolAt "c_zero") (st.boolAt "na_r") (st.boolAt "nb_r")
      (st.boolAt "ya_r") (st.boolAt "yb_r") (st.boolAt "ma") (st.boolAt "mb") (st.boolAt "zr") (st.boolAt "r")
      (st.boolAt "qp") (st.boolAt "qf") (st.boolAt "qe") (st.boolAt "qb") (st.boolAt "rm") (st.boolAt "ge1")
      (st.boolAt "ge2") (st.boolAt "qq") (st.boolAt "rnz") (st.boolAt "adj") (st.boolAt "qm") (st.boolAt "onesW")
      (st.boolAt "emw") (st.boolAt "E") (st.boolAt "ovf") (st.boolAt "dsh") (st.boolAt "qs") (st.boolAt "inc")
      (st.boolAt "ef") (st.boolAt "mag") (st.boolAt "q") (st.boolAt "dr") (st.boolAt "u") (st.boolAt "ru")
      (st.boolAt "a") (st.boolAt "b") _ _ (by decide) rfl (by decide) a.toNat b.toNat ha' hb'
      eq_s_plain_0 eq_ea_nz_plain_1 eq_eb_nz_plain_2 eq_c_nan_plain_3 eq_c_inf_plain_4 eq_c_zero_plain_5
      eq_na_r_plain_6 eq_nb_r_plain_7 eq_ya_r_plain_8 eq_yb_r_plain_9 eq_ma_plain_10 eq_mb_plain_11
      eq_zr_plain_12 eq_r_plain_13 eq_qp_plain_14 eq_qf_plain_15 eq_qe_plain_16 eq_qb_plain_17 eq_rm_plain_18
      eq_ge1_plain_19 eq_ge2_plain_20 eq_qq_plain_21 eq_rnz_plain_22 eq_adj_plain_23 eq_qm_plain_24
      eq_onesW_plain_25 eq_emw_plain_26 eq_E_plain_27 eq_ovf_plain_28 eq_dsh_plain_29 eq_qs_plain_30
      eq_inc_plain_31 eq_ef_plain_32 eq_mag_plain_33 eq_q_plain_34 eq_q_plain_35 eq_q_plain_36
      eq_na_r_norm_0 eq_nb_r_norm_1 eq_ya_r_norm_2 eq_yb_r_norm_3
      eq_dr_newton_0 eq_u_newton_1 eq_ru_newton_2 eq_r_newton_3 eq_q_lo_0
    have hval : XF.val (st.boolAt "q") (W + P) = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat :=
      hch.trans (SvGolf.FdivParam.OutN_fdivBits W P ⟨hW, hP⟩ a b)
    have hkq : ∀ k, k < W + P → KnownBit st "q" k := by
      intro k hk
      by_cases h1 : k = W + P - 1
      · have := known_q_plain_34.2
        rwa [show ((W : Int) + (P : Int) + -1).toNat = k by omega] at this
      · by_cases h2 : P - 1 ≤ k
        · have := (known_q_plain_35 (k - (P - 1)) (by omega)).2
          rwa [show ((P : Int) - 1).toNat + (k - (P - 1)) = k by omega] at this
        · by_cases h3 : k = P - 2
          · have := known_q_plain_36.2
            rwa [show ((P : Int) - 1 + -1).toNat = k by omega] at this
          · exact (known_q_lo_0 k (by omega)).2
    obtain ⟨vs, hvs, hvsw⟩ := known_q_plain_34.1
    have hq := SvState.lookup_eq_ofBitVec_bv (W := W + P) hvs (by omega) hkq
    have hbq : XF.bv (W + P) (st.boolAt "q") = SvGolf.Tasks.FdivP.fdivBits W P a b := by
      apply BitVec.eq_of_toNat_eq
      rw [XF.toNat_bv, hval]
    rw [hvs, hq, hbq]
  case inputsKnown_1 => exact inKnown_ofBitVec hav (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hbv (by omega)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (intros; split <;> omega)
    | (intros; simp [LVec.width] <;> omega)
    | (intros; refine ⟨?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover))
    | (intros; refine ⟨?_, ?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover))
    | skip

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
