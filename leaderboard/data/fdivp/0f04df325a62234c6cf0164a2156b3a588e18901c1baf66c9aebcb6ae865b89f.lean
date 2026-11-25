import Submission.Design
import SvGolf.Comb
import LeanModels.SoftFloat.Binary
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib

/-!
# Reference solution for task `fdivp`, the radix-4 SRT divider: IEEE 754 division for every `W >= 2`, `P >= 2`

A submission like any player's `Solution.lean`, and the task's third proved reference (the first is `fdivp.lean`, D3,
a restoring divider; the second `fdivp_newton.lean`, a Newton-Raphson divider). It proves
`theorem Submission.solution : Submission.Goal` for the design `reference/fdivp_srt.sv`: D3's datapath with its `P + 2`
restoring steps replaced by an unrolled radix-4 SRT core adapted from CORE-V Wally (the design's provenance header):
`N = (P + 2) / 2 + 1` stages (a generate family `srt`), each selecting a digit in `{-2, ..., 2}` by comparing a 7-bit
estimate of the carry-save remainder with four constants chosen by 3 divisor bits (`?:` trees), one carry-save row
`4·(R - q·d)`, and on-the-fly conversion of the digits into the quotient `U` and `U - 1`; then the final correction by
the sign of the remainder and the sticky `rs != 0`. Unpacking, classification, the normalizers, the exponent, the
denormalizer, the rounding and the output stage are D3's.

The file is self-contained like `fdivp.lean`: besides the generated design module and the framework, it imports
the general ls-sv proof library `LeanModels.Sv.Lib` (restoring division, the `XF.val` facts, among them the carry-save
row `val_csa` and the top-bit XOR `val_xor_top`) and Proglib's IEEE 754 library
`LeanModels.SoftFloat.Binary` (the statement's own: the facts about division and the certificate `certF_bridge`). Sections:

1. `DpN` .. `DpG4`: copied VERBATIM from `fdivp.lean` (`tests/fdivp/shared_sections.py` checks that they stay
   byte-identical): the math layer with the model `OutN`
   (whose quotient and sticky are those of `P + 2` restoring steps, `qqN` and `rrN`), and the glue of the sites the
   designs share. D3's `div_rows` (`DpG1`), `g_ext` (`DpG2`) and `g_inc` (`DpG3`) come along unused.
2. `SrCore`: the mathematics of the core (until 2026-11-05 the library module `LeanModels/Sv/Lib/Srt.lean`): the
   selection table checked cell by cell by kernel `decide`, the estimate, containment, the carry-save row, on-the-fly
   conversion, the invariant over the stages and `srt_rest`, which identifies the corrected quotient and the sticky
   with those of restoring division.
3. `SrG1`: the glue of the SRT core, one lemma per printed shape (the concatenations of the divisor multiples, the
   selection tables, the family `srt` row by row, the correction and the sticky); `core`: for normalized significands,
   the printed equations of the core give the quotient `qq` and the sticky `rnz` of restoring division (one
   application of `srt_rest`).
4. `SrG2`: `g_inc_rnz` (the rounding increment with the one-bit sticky `rnz`), `fin_ops` and `Glue.chain`, `DpG5`'s
   chain for this netlist.
5. `Submission`: the proof.

## Route

1. `fdiv_struct` / `fdiv_interface`: `sv_structure` with the rank of the design (the plain sites by depth, the families
   `norm` and `srt` by their stage, 19 ranks per SRT stage, the sites after the core above every stage) and
   `sv_interface`; `fdiv_struct` also returns `sv_structure`'s shared obligations (`SharedObl`), which `sv_equations`
   takes instead of proving them again. The stage bound `(P + 2) / 2 + 1` reaches the side goals as a truncated division (`Int.tdiv`, SV's
   integer `/`), which `omega` reads once it is equated with `/` (`htd`).
2. `solution`: `CombTask.satisfiedAt_of_comb` reduces to one settled-state lemma; `sv_equations` hands over the 69
   equations of the netlist; the whole arithmetic is `SvGolf.FdivParam.Glue.chain` (section `SrG2`), and
   `SvGolf.FdivParam.OutN_fdivBits` (section `DpU`) identifies its value with the task function. The constants of the
   core (the zero pads of the multiples, the 32 table leaves, the sign flip `7'b1000000`) are the vectors the
   equations print; `core` checks their values by `decide`.
3. Heartbeats (measured 2026-11-05, `Elab.async false`): 672 thousand for `fdiv_struct` and 700 thousand for
   `solution`, which takes the shared obligations from `fdiv_struct` (959 thousand before, 749 of them `sv_equations`'s);
   `chain` 90 and `core` 38 (2026-11-04). The limits set are 900 thousand and 1.3 million; every other declaration is
   under the default.
-/

/-! # Section `DpN`: Format-independent arithmetic of the datapath (was `tasks/fdivp/DpN.lean`) -/

section DpN

/-!
# Task `fdivp`: format-independent arithmetic of the parametric divider datapath (untrusted, kernel-checked)

WP-H3. Plain `Nat`/`Int` lemmas with NO format in sight (the format is instantiated in `DpM.lean`):

* `normIter_spec`: the linear one-bit normalizer (`P - 1` stages, each shifting left while the top bit is clear and
  counting the shifts down modulo `Z = 2^EW`) yields `m * 2^l` in `[2^T, 2^(T+1))`, by induction on the stage count
  (the former 16-bit task's proof enumerated the 2047 significands in the kernel);
* the guard/round/sticky decision `inc = rb & (st1 | qs[1])` of `qs = qm >> sh` is round to nearest even of
  `qm / 2^(sh+1)` for every shift amount: `core_t`, `core_f` of Proglib's `LeanModels.SoftFloat.Binary`.
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

end SvGolf.FdivParam

end DpN

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

open LeanModels.SoftFloat.Binary
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

open LeanModels.SoftFloat.Binary
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
`(divide f .nearestTiesToEven a b).toNat`, in every case of the special-value table.
-/

namespace SvGolf.FdivParam

open LeanModels.SoftFloat.Binary
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
special-value table) is the value of `divide f .nearestTiesToEven a b`, the library's division, which the statement names. `OutN_fdivBits` restates it with the
task's own function `fdivBits W P`.
-/

namespace SvGolf.FdivParam

open LeanModels.SoftFloat.Binary
open LeanModels.Sv.Lib

theorem OutN_eq (f : Format) (a b : BitVec f.k) :
    OutN f a.toNat b.toNat = (divide f .nearestTiesToEven a b).toNat := by
  have hMt := Nat.two_pow_pos f.t
  have hA := four_le_two_pow_w f
  have hpf := f.hp
  have ht1 : 1 ≤ f.t := by simp only [Format.t]; omega
  have hE : 2 ^ f.w - 1 < 2 ^ f.w := by omega
  have hs := sign_xor_nat f a b
  rw [divide_table f .nearestTiesToEven a b]
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

open LeanModels.SoftFloat.Binary
open LeanModels.Sv.Lib

theorem OutN_fdivBits (W P : Nat) (h : 2 ≤ W ∧ 2 ≤ P) (a b : BitVec (W + P)) :
    OutN ⟨W, P, h.1, h.2⟩ a.toNat b.toNat = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat := by
  have hk : (⟨W, P, h.1, h.2⟩ : Format).k = W + P := SvGolf.Tasks.FdivP.k_eq W P (by omega)
  have key := OutN_eq ⟨W, P, h.1, h.2⟩ (a.cast hk.symm) (b.cast hk.symm)
  simp only [BitVec.toNat_cast] at key
  rw [SvGolf.Tasks.FdivP.fdivBits_toNat W P h a b]
  exact key

/-- The format instances: binary16, bfloat16-like, binary32. -/
example (a b : BitVec 16) : OutN ⟨5, 11, by decide, by decide⟩ a.toNat b.toNat = (LeanModels.SoftFloat.Binary.divBinary16 a b).toNat :=
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
open LeanModels.SoftFloat.Binary

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
open LeanModels.SoftFloat.Binary

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
open LeanModels.SoftFloat.Binary

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

/-! # Section `SrCore`: The mathematics of the SRT core (was `LeanModels/Sv/Lib/Srt.lean`) -/

section SrCore


/-!
# Task `fdivp`, the SRT reference: the mathematics of the core (untrusted)

The core of a radix-4 SRT divider of normalized significands `ma, mb ∈ [2^(P-1), 2^P)` (`P ≥ 2`), as the `Nat` values
its hardware computes: digits `q ∈ {-2, …, 2}`, a carry-save partial remainder `ws + wc` of `RW = P + 6` bits, the
selection of `q` from the 8 top bits of `ws + wc` and 3 divisor bits by comparison with table constants, and on-the-fly
conversion of the digits into `U` (the digits so far) and `UM = U - 1`, modulo `2^(P+2)`.

Units: `U = 2^(P-2)`, so `2^RW = 256·U`; the divisor `dv = 8·mb ∈ [16·U, 32·U)`, and its 3 bits after the leading one
are `da = (dv / 2U) mod 8`, so `(16 + 2·da)·U ≤ dv < (18 + 2·da)·U`. A stage reads the estimate
`es = (ws/U + wc/U) mod 256` and `yb = (es/2 + 64) mod 128` (its sign bit flipped); `g_j = [t_j(da) ≤ yb]`.

* `srtT2`/`srtT1`/`srtT0`/`srtTm`: the selection constants (+ 64); `srtDigit`, `srtQ`: the thermometer digit.
* `srt_tbl` (**the table, by one kernel `decide`**): the constants are a thermometer, and in every cell
  `[2y, 2y+3)·U × [16 + 2da, 18 + 2da)·U` of `(R, dv)` (`y = yb - 64`) the selected digit keeps
  `(3q - 2)·dv ≤ 3R ≤ (3q + 2)·dv` at both divisor endpoints (`srtCell`; the sides at `q = ±2` are the invariant).
* `srt_est`: the estimate brackets the residual: `2y·U ≤ R < (2y + 3)·U`.
* `srt_qds`: containment: `|3R| ≤ 8·dv` gives `|3·R'| ≤ 8·dv` for `R' = 4·(R - q·dv)`.
* `srt_mm`, `srt_csa`: the multiple and the carry-save row: `ws' + wc' ≡ 4·(R - q·dv) (mod 2^RW)`.
* `srt_otf`: on-the-fly conversion: `U' ≡ 4·Q + q`, `UM' ≡ 4·Q + q - 1`.
* `SrtInv`, `srt_step`, `srt_core`: the invariant of `k` stages and its induction.
* `srt_final`, `srt_rest`: after `N` stages with `2N = P + 3 + XS` and `ws[0] = 16·ma / 2^(1+XS)`, the corrected
  quotient `rs < 0 ? UM : U` and the sticky `rs ≠ 0` (`rs = ws + wc`) are those of `P + 2` restoring steps.

Until 2026-11-05 this was the library module `LeanModels/Sv/Lib/Srt.lean`. It models this one reference's core and
nothing else uses it, so it is compiled here, in the solution stage, like any golfer's own proof of their own core
(the rule of 11/04 that moved Newton's core into `fdivp_newton.lean`: the shared library holds only results that any
proof of that class of designs would use). Plain Lean: `omega`, `grind` and core lemmas, on `LeanModels.Sv.Lib`'s
restoring division (`restQuo`, `restRem`).
-/

namespace SvGolf.FdivParam

open LeanModels.Sv.Lib

/-! ## The selection table -/

/-- Wally's `mks2` constants + 64, by the 3 divisor bits `da`. -/
def srtT2 (da : Nat) : Nat := [76, 78, 80, 81, 82, 84, 86, 87].getD da 0
/-- Wally's `mks1` constants + 64. -/
def srtT1 (da : Nat) : Nat := [68, 68, 70, 70, 70, 72, 72, 72].getD da 0
/-- Wally's `mks0` constants + 64. -/
def srtT0 (da : Nat) : Nat := [60, 60, 58, 58, 58, 56, 56, 56].getD da 0
/-- Wally's `mksm1` constants + 64. -/
def srtTm (da : Nat) : Nat := [51, 50, 48, 47, 46, 44, 42, 41].getD da 0

/-- The digit of the thermometer code `g2 ≤ g1 ≤ g0 ≤ gm`: `q = g2 + g1 + g0 + gm - 2`. -/
def srtDigit (g2 g1 g0 gm : Bool) : Int := ((g2.toNat + g1.toNat + g0.toNat + gm.toNat : Nat) : Int) - 2

/-- The digit selected in cell `(da, yb)`. -/
def srtQ (da yb : Nat) : Int :=
  srtDigit (decide (srtT2 da ≤ yb)) (decide (srtT1 da ≤ yb)) (decide (srtT0 da ≤ yb)) (decide (srtTm da ≤ yb))

/-- Digit `q` is safe in cell `(da, yb)`: on the cell `[2y, 2y+3) × [16 + 2da, 18 + 2da)` (`y = yb - 64`, in units
of `U`), `(3q - 2)·d ≤ 3R` and `3R ≤ (3q + 2)·d`, checked at both divisor endpoints `d` (the conditions are linear in
`d`) and at the worst residual; the lower side at `q = -2` and the upper at `q = 2` are the invariant itself. -/
abbrev srtCell (da yb : Nat) (q : Int) : Prop :=
  (q = -2 ∨ ((3 * q - 2) * (16 + 2 * (da : Int)) ≤ 6 * ((yb : Int) - 64) ∧
      (3 * q - 2) * (18 + 2 * (da : Int)) ≤ 6 * ((yb : Int) - 64))) ∧
    (q = 2 ∨ (3 * (2 * ((yb : Int) - 64) + 3) ≤ (3 * q + 2) * (16 + 2 * (da : Int)) ∧
      3 * (2 * ((yb : Int) - 64) + 3) ≤ (3 * q + 2) * (18 + 2 * (da : Int))))

/-- **The selection table**, all 8 × 128 cells by one kernel `decide`: the constants are a thermometer, and every
cell is safe for the digit it selects. -/
theorem srt_tbl : ∀ da, da < 8 → (srtTm da ≤ srtT0 da ∧ srtT0 da ≤ srtT1 da ∧ srtT1 da ≤ srtT2 da) ∧
    ∀ yb, yb < 128 → srtCell da yb (srtQ da yb) := by
  decide +kernel

/-! ## The estimate and containment -/

/-- **The estimate.** For `ws, wc < 256·U` whose sum is the residual `R` modulo `256·U`, `|3R| < 256·U`: the
estimate `yb` read from the 8 top bits of `ws` and `wc` brackets `R`: `2·(yb - 64)·U ≤ R < (2·(yb - 64) + 3)·U`. -/
theorem srt_est (U ws wc es yb : Nat) (R : Int) (hU : 0 < U) (hws : ws < 256 * U) (hwc : wc < 256 * U)
    (hR : (256 * U : Int) ∣ (ws + wc : Int) - R) (hR1 : -(256 * U : Int) < 3 * R) (hR2 : 3 * R < 256 * U)
    (hes : es = (ws / U % 256 + wc / U % 256) % 256) (hyb : yb = (es / 2 % 128 + 64) % 128) :
    yb < 128 ∧ 2 * ((yb : Int) * U) - 128 * U ≤ R ∧ R < 2 * ((yb : Int) * U) - 125 * U := by
  have hA := Nat.div_add_mod ws U
  have hB := Nat.div_add_mod wc U
  have hA' := Nat.mod_lt ws hU
  have hB' := Nat.mod_lt wc hU
  have hA8 : ws / U < 256 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hws)
  have hB8 : wc / U < 256 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hwc)
  generalize ws / U = A at *
  generalize wc / U = B at *
  generalize ws % U = a at *
  generalize wc % U = b at *
  obtain ⟨t, ht⟩ := hR
  have hwsI : (ws : Int) = U * A + a := by exact_mod_cast hA.symm
  have hwcI : (wc : Int) = U * B + b := by exact_mod_cast hB.symm
  have ht' : (256 * U : Int) * t = 256 * (U * t) := Int.mul_assoc _ _ _
  have e1 : (U : Int) * ((A : Int) + B - 256 * t) = U * A + U * B - 256 * (U * t) := by
    rw [Int.mul_sub, Int.mul_add, Int.mul_left_comm (U : Int) 256 t]
  generalize hm : (A : Int) + B - 256 * t = m at e1
  have hU' : (0 : Int) < U := by exact_mod_cast hU
  have h1 : (U : Int) * m ≤ R := by omega
  have h2 : R < (U : Int) * m + 2 * U := by omega
  have hm1 : m < 86 := Int.lt_of_mul_lt_mul_left (a := (U : Int)) (by omega) (Int.le_of_lt hU')
  have hm2 : -88 < m := Int.lt_of_mul_lt_mul_left (a := (U : Int)) (by omega) (Int.le_of_lt hU')
  have hy : 2 * ((yb : Int) - 64) ≤ m ∧ m ≤ 2 * ((yb : Int) - 64) + 1 := by omega
  have hl := Int.mul_le_mul_of_nonneg_left hy.1 (Int.le_of_lt hU')
  have hh := Int.mul_le_mul_of_nonneg_left hy.2 (Int.le_of_lt hU')
  have e2 : (U : Int) * (2 * ((yb : Int) - 64)) = 2 * ((yb : Int) * U) - 128 * U := by
    rw [Int.mul_comm (U : Int), Int.mul_assoc, Int.sub_mul]; omega
  have e3 : (U : Int) * (2 * ((yb : Int) - 64) + 1) = 2 * ((yb : Int) * U) - 127 * U := by
    rw [Int.mul_add, e2]; omega
  refine ⟨by omega, by omega, by omega⟩

/-- A safe cell, scaled by `U`: the lower side. -/
theorem srt_scale_lo (U c d yb : Int) (hU : 0 ≤ U)
    (h : c * (16 + 2 * d) ≤ 6 * (yb - 64) ∧ c * (18 + 2 * d) ≤ 6 * (yb - 64)) :
    c * (16 * U) + c * (2 * (d * U)) ≤ 6 * (yb * U) - 384 * U ∧
      c * (18 * U) + c * (2 * (d * U)) ≤ 6 * (yb * U) - 384 * U := by
  have h1 := Int.mul_le_mul_of_nonneg_right h.1 hU
  have h2 := Int.mul_le_mul_of_nonneg_right h.2 hU
  simp only [Int.add_mul, Int.sub_mul, Int.mul_assoc, Int.mul_add, Int.mul_sub] at h1 h2
  omega

/-- A safe cell, scaled by `U`: the upper side. -/
theorem srt_scale_hi (U c d yb : Int) (hU : 0 ≤ U)
    (h : 3 * (2 * (yb - 64) + 3) ≤ c * (16 + 2 * d) ∧ 3 * (2 * (yb - 64) + 3) ≤ c * (18 + 2 * d)) :
    6 * (yb * U) - 375 * U ≤ c * (16 * U) + c * (2 * (d * U)) ∧
      6 * (yb * U) - 375 * U ≤ c * (18 * U) + c * (2 * (d * U)) := by
  have h1 := Int.mul_le_mul_of_nonneg_right h.1 hU
  have h2 := Int.mul_le_mul_of_nonneg_right h.2 hU
  simp only [Int.add_mul, Int.sub_mul, Int.mul_assoc, Int.mul_add, Int.mul_sub] at h1 h2
  omega

/-- The digit lies in `[-2, 2]`. -/
theorem srtDigit_range (g2 g1 g0 gm : Bool) : -2 ≤ srtDigit g2 g1 g0 gm ∧ srtDigit g2 g1 g0 gm ≤ 2 := by
  cases g2 <;> cases g1 <;> cases g0 <;> cases gm <;> decide

/-- **Containment.** With the divisor in its cell `(16 + 2·da)·U ≤ dv < (18 + 2·da)·U`, the estimate's bracket of
`R` (`srt_est`) and `|3R| ≤ 8·dv`, the selected digit keeps `|3·R'| ≤ 8·dv` for `R' = 4·(R - q·dv)`. -/
theorem srt_qds (U da yb : Nat) (dv R : Int) (hU : 0 < U) (hda : da < 8) (hyb : yb < 128)
    (hd1 : 16 * (U : Int) + 2 * ((da : Int) * U) ≤ dv) (hd2 : dv < 18 * (U : Int) + 2 * ((da : Int) * U))
    (he1 : 2 * ((yb : Int) * U) - 128 * U ≤ R) (he2 : R < 2 * ((yb : Int) * U) - 125 * U)
    (hR1 : -8 * dv ≤ 3 * R) (hR2 : 3 * R ≤ 8 * dv) :
    -8 * dv ≤ 3 * (4 * (R - srtQ da yb * dv)) ∧ 3 * (4 * (R - srtQ da yb * dv)) ≤ 8 * dv := by
  have hc := (srt_tbl da hda).2 yb hyb
  have hU0 : (0 : Int) ≤ U := by omega
  have hqr : -2 ≤ srtQ da yb ∧ srtQ da yb ≤ 2 := srtDigit_range _ _ _ _
  generalize srtQ da yb = q at hc hqr ⊢
  have hq : q = -2 ∨ q = -1 ∨ q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> obtain ⟨hl | hl, hh | hh⟩ := hc
  all_goals first
    | omega
    | (have h1 := srt_scale_lo U _ da yb hU0 hl; have h2 := srt_scale_hi U _ da yb hU0 hh; omega)
    | (have h1 := srt_scale_lo U _ da yb hU0 hl; omega)
    | (have h2 := srt_scale_hi U _ da yb hU0 hh; omega)

/-! ## The carry-save step -/

/-- **The multiple.** The priority chain `g2 ? nd2 : g1 ? nd1 : g0 ? 0 : gm ? dv : d2` with the `+8` that the
carry vector takes for `q > 0` is `-q·dv` modulo `256·U` (`dv = 8·mb`; `nd1 = -dv - 8`, `nd2 = -2·dv - 8`). -/
theorem srt_mm (U mb nd1 nd2 mm : Nat) (g2 g1 g0 gm : Bool)
    (h21 : g2 = true → g1 = true) (h10 : g1 = true → g0 = true) (h0m : g0 = true → gm = true)
    (hnd1 : nd1 + 8 * mb + 8 = 256 * U) (hnd2 : nd2 + 16 * mb + 8 = 256 * U)
    (hmm : mm = if g2 = true then nd2 else if g1 = true then nd1 else if g0 = true then 0
      else if gm = true then 8 * mb else 16 * mb) :
    (256 * U : Int) ∣ (mm + 8 * g1.toNat : Int) + srtDigit g2 g1 g0 gm * (8 * mb) := by
  cases g2 <;> cases g1 <;> cases g0 <;> cases gm <;> simp at hmm
  all_goals first
    | exact absurd (h21 rfl) (by decide)
    | exact absurd (h10 rfl) (by decide)
    | exact absurd (h0m rfl) (by decide)
    | exact ⟨0, by simp only [srtDigit, Bool.toNat_true, Bool.toNat_false]; omega⟩
    | exact ⟨1, by simp only [srtDigit, Bool.toNat_true, Bool.toNat_false]; omega⟩

/-- **The carry-save row.** `sm + 2·cy = ws + wc + mm` (a full-adder row) with `cy`'s 3 low bits zero; the next
remainder `ws' = 4·(sm mod 64U)`, `wc' = 8·(cy mod 32U) + 32·g` is `4·(ws + wc + mm + 8·g)` modulo `256·U`. -/
theorem srt_csa (U ws wc mm sm cy g ws' wc' : Nat)
    (hcsa : sm + 2 * cy = ws + wc + mm) (hcy : cy % 8 = 0)
    (hws' : ws' = 4 * (sm % (64 * U))) (hwc' : wc' = 64 * (cy / 8 % (4 * U)) + 32 * g) :
    (256 * U : Int) ∣ (ws' + wc' : Int) - 4 * (ws + wc + mm + 8 * g) := by
  have h1 := Nat.div_add_mod sm (64 * U)
  have h2 := Nat.div_add_mod (cy / 8) (4 * U)
  generalize sm / (64 * U) = s1 at h1
  generalize sm % (64 * U) = r1 at h1 hws'
  generalize cy / 8 / (4 * U) = s2 at h2
  generalize cy / 8 % (4 * U) = r2 at h2 hwc'
  rw [Nat.mul_assoc] at h1 h2
  have hN : ws' + wc' + 256 * (U * s1) + 256 * (U * s2) = 4 * (ws + wc + mm + 8 * g) := by omega
  refine ⟨-((s1 : Int) + s2), ?_⟩
  have e : (256 * U : Int) * -((s1 : Int) + s2) = -(256 * ((U : Int) * s1)) - 256 * ((U : Int) * s2) := by
    rw [Int.mul_neg, Int.mul_add, Int.mul_assoc, Int.mul_assoc]; omega
  rw [e]
  have hc1 := Int.natCast_mul U s1
  have hc2 := Int.natCast_mul U s2
  omega

/-! ## On-the-fly conversion -/

/-- `y mod n = x` from `y = x + n·t` with `0 ≤ x < n`. -/
theorem srt_emod (x y n t : Int) (h0 : 0 ≤ x) (h1 : x < n) (h : y = x + n * t) : y % n = x := by
  subst h; rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

/-- One append: `x ≡ v (mod 4K)` gives `4·(x mod K) + d ≡ 4·v + d (mod 4K)` for a 2-bit `d`. -/
theorem srt_append (K x d y : Nat) (v w : Int) (hK : 0 < K) (hd : d < 4) (hx : (x : Int) = v % (4 * K))
    (hy : y = 4 * (x % K) + d) (hw : w = 4 * v + d) : (y : Int) = w % (4 * K) := by
  have hK' : (0 : Int) < K := by exact_mod_cast hK
  have e1 : (x : Int) % K = v % K := by
    rw [hx, Int.emod_emod_of_dvd v (Int.dvd_mul_left 4 (K : Int))]
  have e2 := Int.mul_ediv_add_emod v K
  have e3 := Int.emod_nonneg v (by omega : (K : Int) ≠ 0)
  have e4 := Int.emod_lt_of_pos v hK'
  have h5 := Nat.mod_lt x hK
  subst hy hw
  symm
  apply srt_emod _ _ _ (v / K)
  · exact_mod_cast Nat.zero_le _
  · exact_mod_cast (show 4 * (x % K) + d < 4 * K by omega)
  · push_cast
    rw [e1, Int.mul_assoc]
    omega

/-- **On-the-fly conversion.** With `u ≡ Q` and `um ≡ Q - 1` modulo `4K`, the appends of the five thermometer cases
give `u' ≡ 4·Q + q` and `um' ≡ 4·Q + q - 1`. -/
theorem srt_otf (K u um u' um' : Nat) (Q : Int) (g2 g1 g0 gm : Bool) (hK : 0 < K)
    (h21 : g2 = true → g1 = true) (h10 : g1 = true → g0 = true) (h0m : g0 = true → gm = true)
    (hu : (u : Int) = Q % (4 * K)) (hum : (um : Int) = (Q - 1) % (4 * K))
    (hu' : u' = 4 * ((if g0 = true then u else um) % K) + 2 * (g2 || !g0).toNat + (g1 && !g2 || gm && !g0).toNat)
    (hum' : um' = 4 * ((if g1 = true then u else um) % K) + 2 * (!g1 && gm).toNat +
      (g2 || g0 && !g1 || !gm).toNat) :
    (u' : Int) = (4 * Q + srtDigit g2 g1 g0 gm) % (4 * K) ∧
      (um' : Int) = (4 * Q + srtDigit g2 g1 g0 gm - 1) % (4 * K) := by
  subst hu' hum'
  cases g2 <;> cases g1 <;> cases g0 <;> cases gm
  all_goals first
    | exact absurd (h21 rfl) (by decide)
    | exact absurd (h10 rfl) (by decide)
    | exact absurd (h0m rfl) (by decide)
    | skip
  · -- q = -2
    exact ⟨srt_append K um 2 _ (Q - 1) _ hK (by omega) hum (by simp) (by simp [srtDigit] <;> omega),
      srt_append K um 1 _ (Q - 1) _ hK (by omega) hum (by simp) (by simp [srtDigit] <;> omega)⟩
  · -- q = -1
    exact ⟨srt_append K um 3 _ (Q - 1) _ hK (by omega) hum (by simp) (by simp [srtDigit] <;> omega),
      srt_append K um 2 _ (Q - 1) _ hK (by omega) hum (by simp) (by simp [srtDigit] <;> omega)⟩
  · -- q = 0
    exact ⟨srt_append K u 0 _ Q _ hK (by omega) hu (by simp) (by simp [srtDigit] <;> omega),
      srt_append K um 3 _ (Q - 1) _ hK (by omega) hum (by simp) (by simp [srtDigit] <;> omega)⟩
  · -- q = 1
    exact ⟨srt_append K u 1 _ Q _ hK (by omega) hu (by simp) (by simp [srtDigit] <;> omega),
      srt_append K u 0 _ Q _ hK (by omega) hu (by simp) (by simp [srtDigit] <;> omega)⟩
  · -- q = 2
    exact ⟨srt_append K u 2 _ Q _ hK (by omega) hu (by simp) (by simp [srtDigit] <;> omega),
      srt_append K u 1 _ Q _ hK (by omega) hu (by simp) (by simp [srtDigit] <;> omega)⟩

/-! ## The invariant and the stages -/

/-- The invariant after `k` stages (`dv = 8·mb`, residual `R`, digits `Q`, start `r0`): `ws, wc < 256·U`,
`ws + wc ≡ R (mod 256·U)`, `|3R| ≤ 8·dv`, `4^k·r0 = R + 4·dv·Q`, `u ≡ Q`, `um ≡ Q - 1 (mod 16·U)`. -/
def SrtInv (U mb r0 k ws wc u um : Nat) : Prop :=
  ws < 256 * U ∧ wc < 256 * U ∧ ∃ R Q : Int, (256 * U : Int) ∣ (ws + wc : Int) - R ∧
    -64 * (mb : Int) ≤ 3 * R ∧ 3 * R ≤ 64 * mb ∧ (4 : Int) ^ k * r0 = R + 32 * mb * Q ∧
    (u : Int) = Q % (16 * U) ∧ (um : Int) = (Q - 1) % (16 * U)

/-- The start: `ws = r0`, `wc = 0`, `u = 0`, `um = 16·U - 1`, for `0 ≤ 3·r0 ≤ 8·dv`. -/
theorem srt_init (U mb r0 : Nat) (hU : 0 < U) (hr0 : 3 * r0 ≤ 64 * mb) (hr0w : r0 < 256 * U) :
    SrtInv U mb r0 0 r0 0 0 (16 * U - 1) := by
  refine ⟨hr0w, by omega, r0, 0, ⟨0, by omega⟩, by omega, by omega, by simp, by simp, ?_⟩
  symm
  apply srt_emod _ _ _ (-1) (by omega) (by omega)
  omega

/-- **One stage**: the invariant after `k` stages and the stage's equations give the invariant after `k + 1`, with
`R' = 4·(R - q·dv)` and `Q' = 4·Q + q`. -/
theorem srt_step (U mb da nd1 nd2 r0 k ws wc u um es yb mm sm cy ws' wc' u' um' : Nat) (g2 g1 g0 gm : Bool)
    (hU : 0 < U) (hb2 : mb < 4 * U) (hda : da < 8)
    (hd1 : 16 * U + 2 * (da * U) ≤ 8 * mb) (hd2 : 8 * mb < 18 * U + 2 * (da * U))
    (hnd1 : nd1 + 8 * mb + 8 = 256 * U) (hnd2 : nd2 + 16 * mb + 8 = 256 * U)
    (hinv : SrtInv U mb r0 k ws wc u um)
    (hes : es = (ws / U % 256 + wc / U % 256) % 256) (hyb : yb = (es / 2 % 128 + 64) % 128)
    (hg2 : g2 = decide (srtT2 da ≤ yb)) (hg1 : g1 = decide (srtT1 da ≤ yb))
    (hg0 : g0 = decide (srtT0 da ≤ yb)) (hgm : gm = decide (srtTm da ≤ yb))
    (hmm : mm = if g2 = true then nd2 else if g1 = true then nd1 else if g0 = true then 0
      else if gm = true then 8 * mb else 16 * mb)
    (hcsa : sm + 2 * cy = ws + wc + mm) (hcy : cy % 8 = 0)
    (hws' : ws' = 4 * (sm % (64 * U))) (hwc' : wc' = 64 * (cy / 8 % (4 * U)) + 32 * g1.toNat)
    (hu' : u' = 4 * ((if g0 = true then u else um) % (4 * U)) + 2 * (g2 || !g0).toNat +
      (g1 && !g2 || gm && !g0).toNat)
    (hum' : um' = 4 * ((if g1 = true then u else um) % (4 * U)) + 2 * (!g1 && gm).toNat +
      (g2 || g0 && !g1 || !gm).toNat) :
    SrtInv U mb r0 (k + 1) ws' wc' u' um' := by
  obtain ⟨hws, hwc, R, Q, hdvd, hR1, hR2, hrel, hu, hum⟩ := hinv
  obtain ⟨⟨hm0, hm1, hm2⟩, -⟩ := srt_tbl da hda
  have h21 : g2 = true → g1 = true := by subst hg2 hg1; simp only [decide_eq_true_eq]; omega
  have h10 : g1 = true → g0 = true := by subst hg1 hg0; simp only [decide_eq_true_eq]; omega
  have h0m : g0 = true → gm = true := by subst hg0 hgm; simp only [decide_eq_true_eq]; omega
  have hq : srtDigit g2 g1 g0 gm = srtQ da yb := by subst hg2 hg1 hg0 hgm; rfl
  -- the estimate and containment
  obtain ⟨hyb', he1, he2⟩ := srt_est U ws wc es yb R hU hws hwc hdvd (by omega) (by omega) hes hyb
  have hd1' : 16 * (U : Int) + 2 * ((da : Int) * U) ≤ 8 * (mb : Int) := by exact_mod_cast hd1
  have hd2' : 8 * (mb : Int) < 18 * (U : Int) + 2 * ((da : Int) * U) := by exact_mod_cast hd2
  obtain ⟨hc1, hc2⟩ := srt_qds U da yb (8 * mb) R hU hda hyb' hd1' hd2' he1 he2 (by omega) (by omega)
  rw [← hq] at hc1 hc2
  -- the carry-save row and the multiple
  have hcs := srt_csa U ws wc mm sm cy g1.toNat ws' wc' hcsa hcy hws' hwc'
  have hmf := srt_mm U mb nd1 nd2 mm g2 g1 g0 gm h21 h10 h0m hnd1 hnd2 hmm
  -- on-the-fly conversion
  have hu16 : (u : Int) = Q % (4 * ((4 * U : Nat) : Int)) := by rw [hu]; congr 1; push_cast; omega
  have hum16 : (um : Int) = (Q - 1) % (4 * ((4 * U : Nat) : Int)) := by rw [hum]; congr 1; push_cast; omega
  obtain ⟨ho1, ho2⟩ := srt_otf (4 * U) u um u' um' Q g2 g1 g0 gm (by omega) h21 h10 h0m hu16 hum16 hu' hum'
  generalize srtDigit g2 g1 g0 gm = q at hc1 hc2 hmf ho1 ho2
  refine ⟨?_, ?_, 4 * (R - q * (8 * mb)), 4 * Q + q, ?_, by omega, by omega, ?_, ?_, ?_⟩
  · have := Nat.mod_lt sm (show 0 < 64 * U by omega); omega
  · have := Nat.mod_lt (cy / 8) (show 0 < 4 * U by omega)
    cases g1 <;> simp only [Bool.toNat_true, Bool.toNat_false] at hwc' <;> omega
  · have e : (ws' + wc' : Int) - 4 * (R - q * (8 * mb)) =
        ((ws' + wc' : Int) - 4 * (ws + wc + mm + 8 * g1.toNat)) + 4 * ((ws + wc : Int) - R) +
          4 * ((mm + 8 * g1.toNat : Int) + q * (8 * mb)) := by omega
    rw [e]
    exact Int.dvd_add (Int.dvd_add hcs (Int.dvd_trans hdvd (Int.dvd_mul_left 4 _)))
      (Int.dvd_trans hmf (Int.dvd_mul_left 4 _))
  · rw [Int.pow_succ]; grind
  · rw [ho1]; congr 1; push_cast; omega
  · rw [ho2]; congr 1; push_cast; omega

/-- **The stages**: from the start, `N` stages keep the invariant (`srt_step` at each `k < N`). -/
theorem srt_core (U mb da nd1 nd2 r0 N : Nat) (hU : 0 < U) (hb2 : mb < 4 * U) (hda : da < 8)
    (hd1 : 16 * U + 2 * (da * U) ≤ 8 * mb) (hd2 : 8 * mb < 18 * U + 2 * (da * U))
    (hnd1 : nd1 + 8 * mb + 8 = 256 * U) (hnd2 : nd2 + 16 * mb + 8 = 256 * U)
    (hr0 : 3 * r0 ≤ 64 * mb) (hr0w : r0 < 256 * U)
    (ws wc u um es yb mm sm cy : Nat → Nat) (g2 g1 g0 gm : Nat → Bool)
    (hws0 : ws 0 = r0) (hwc0 : wc 0 = 0) (hu0 : u 0 = 0) (hum0 : um 0 = 16 * U - 1)
    (hes : ∀ k, k < N → es k = (ws k / U % 256 + wc k / U % 256) % 256)
    (hyb : ∀ k, k < N → yb k = (es k / 2 % 128 + 64) % 128)
    (hg2 : ∀ k, k < N → g2 k = decide (srtT2 da ≤ yb k)) (hg1 : ∀ k, k < N → g1 k = decide (srtT1 da ≤ yb k))
    (hg0 : ∀ k, k < N → g0 k = decide (srtT0 da ≤ yb k)) (hgm : ∀ k, k < N → gm k = decide (srtTm da ≤ yb k))
    (hmm : ∀ k, k < N → mm k = if g2 k = true then nd2 else if g1 k = true then nd1 else if g0 k = true then 0
      else if gm k = true then 8 * mb else 16 * mb)
    (hcsa : ∀ k, k < N → sm k + 2 * cy k = ws k + wc k + mm k) (hcy : ∀ k, k < N → cy k % 8 = 0)
    (hws : ∀ k, k < N → ws (k + 1) = 4 * (sm k % (64 * U)))
    (hwc : ∀ k, k < N → wc (k + 1) = 64 * (cy k / 8 % (4 * U)) + 32 * (g1 k).toNat)
    (hu : ∀ k, k < N → u (k + 1) = 4 * ((if g0 k = true then u k else um k) % (4 * U)) +
      2 * (g2 k || !g0 k).toNat + (g1 k && !g2 k || gm k && !g0 k).toNat)
    (hum : ∀ k, k < N → um (k + 1) = 4 * ((if g1 k = true then u k else um k) % (4 * U)) +
      2 * (!g1 k && gm k).toNat + (g2 k || g0 k && !g1 k || !gm k).toNat) :
    ∀ k, k ≤ N → SrtInv U mb r0 k (ws k) (wc k) (u k) (um k)
  | 0, _ => by rw [hws0, hwc0, hu0, hum0]; exact srt_init U mb r0 hU hr0 hr0w
  | k + 1, hk =>
    srt_step U mb da nd1 nd2 r0 k (ws k) (wc k) (u k) (um k) (es k) (yb k) (mm k) (sm k) (cy k) (ws (k + 1))
      (wc (k + 1)) (u (k + 1)) (um (k + 1)) (g2 k) (g1 k) (g0 k) (gm k) hU hb2 hda hd1 hd2 hnd1 hnd2
      (srt_core U mb da nd1 nd2 r0 N hU hb2 hda hd1 hd2 hnd1 hnd2 hr0 hr0w ws wc u um es yb mm sm cy g2 g1 g0
        gm hws0 hwc0 hu0 hum0 hes hyb hg2 hg1 hg0 hgm hmm hcsa hcy hws hwc hu hum k (by omega))
      (hes k (by omega)) (hyb k (by omega)) (hg2 k (by omega)) (hg1 k (by omega)) (hg0 k (by omega))
      (hgm k (by omega)) (hmm k (by omega)) (hcsa k (by omega)) (hcy k (by omega)) (hws k (by omega))
      (hwc k (by omega)) (hu k (by omega)) (hum k (by omega))

/-! ## The correction -/

/-- The widths of the core in units of `U = 2^(P-2)`. -/
theorem srt_pows (P : Nat) (hP : 2 ≤ P) :
    2 ^ (P - 1) = 2 * 2 ^ (P - 2) ∧ 2 ^ P = 4 * 2 ^ (P - 2) ∧ 2 ^ (P + 1) = 8 * 2 ^ (P - 2) ∧
      2 ^ (P + 2) = 16 * 2 ^ (P - 2) ∧ 2 ^ (P + 4) = 64 * 2 ^ (P - 2) ∧ 2 ^ (P + 5) = 128 * 2 ^ (P - 2) ∧
      2 ^ (P + 6) = 256 * 2 ^ (P - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, P = n + 2 := ⟨P - 2, by omega⟩
  rw [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]
  have e : ∀ c, 2 ^ (n + c) = 2 ^ n * 2 ^ c := fun c => Nat.pow_add 2 n c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e 1]; omega
  · rw [e 2]; omega
  · rw [show n + 2 + 1 = n + 3 by omega, e 3]; omega
  · rw [show n + 2 + 2 = n + 4 by omega, e 4]; omega
  · rw [show n + 2 + 4 = n + 6 by omega, e 6]; omega
  · rw [show n + 2 + 5 = n + 7 by omega, e 7]; omega
  · rw [show n + 2 + 6 = n + 8 by omega, e 8]; omega

/-- The divisor's cell: `da = dv[P+1:P-1]` for `dv = 8·mb` lies in `[0, 8)` with
`(16 + 2·da)·U ≤ dv < (18 + 2·da)·U`. -/
theorem srt_da (U mb da : Nat) (hU : 0 < U) (hb1 : 2 * U ≤ mb) (hb2 : mb < 4 * U)
    (hda : da = 8 * mb / (2 * U) % 8) :
    da < 8 ∧ 16 * U + 2 * (da * U) ≤ 8 * mb ∧ 8 * mb < 18 * U + 2 * (da * U) := by
  have h1 := Nat.div_add_mod (8 * mb) (2 * U)
  have h2 := Nat.mod_lt (8 * mb) (show 0 < 2 * U by omega)
  have h3 : 8 ≤ 8 * mb / (2 * U) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have h4 : 8 * mb / (2 * U) < 16 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
  generalize 8 * mb / (2 * U) = c at *
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 8 := ⟨c - 8, by omega⟩
  have e : 2 * U * (d + 8) = 2 * (U * d) + 16 * U := by
    rw [Nat.mul_add, Nat.mul_assoc 2 U d]; omega
  subst hda
  rw [show (d + 8) % 8 = d by omega, Nat.mul_comm d U]
  omega



/-! ## Pre-aligned correction and SRT theorem -/

/-- The pre-aligned dividend: `ws[0] = xw[RW+XS-1:XS]` with `xw = 32·r0` is `r0·2^(5-XS)`. -/
theorem srt_r0_pre (P r0 XS : Nat) (hXS1 : 1 ≤ XS) (hXS2 : XS ≤ 2) (hr0 : r0 < 2 ^ P) :
    32 * r0 / 2 ^ XS % 2 ^ (P + 6) = r0 * 2 ^ (5 - XS) := by
  have hp : 2 ^ (P + 6) = 2 ^ P * 64 := Nat.pow_add 2 P 6
  rcases (by omega : XS = 1 ∨ XS = 2) with rfl | rfl
  · show 32 * r0 / 2 % 2 ^ (P + 6) = r0 * 16
    rw [Nat.mod_eq_of_lt (show 32 * r0 / 2 < 2 ^ (P + 6) by omega)]; omega
  · show 32 * r0 / 4 % 2 ^ (P + 6) = r0 * 8
    rw [Nat.mod_eq_of_lt (show 32 * r0 / 4 < 2 ^ (P + 6) by omega)]; omega

/-- **Pre-aligned correction and sticky.** After `NS` stages with `4^NS · r0w = 128 · U · r0` (`r0 < mb`),
`rs = (ws + wc) mod 256·U` decodes in two's complement, `rs < 0 ? um % 4U : u % 4U = ⌊4·U·r0 / mb⌋`, and
`rs ≠ 0 ↔ 4·U·r0 mod mb ≠ 0`. -/
theorem srt_final_pre (U r0 mb r0w NS ws wc u um : Nat) (hU : 0 < U) (hr0 : r0 < mb) (hb1 : 2 * U ≤ mb)
    (hb2 : mb < 4 * U) (hinv : SrtInv U mb r0w NS ws wc u um) (hfin : (4 : Int) ^ NS * r0w = 128 * U * r0) :
    (if 128 * U ≤ (ws + wc) % (256 * U) then um % (4 * U) else u % (4 * U)) = 4 * U * r0 / mb ∧
      ((ws + wc) % (256 * U) ≠ 0 ↔ 4 * U * r0 % mb ≠ 0) := by
  obtain ⟨hws, hwc, R, Q, ⟨t, ht⟩, hR1, hR2, hrel, hu, hum⟩ := hinv
  have hU' : (0 : Int) < U := by exact_mod_cast hU
  have hmb : (0 : Int) < mb := by omega
  have hX : ((4 * U * r0 : Nat) : Int) = 4 * ((U : Int) * r0) := by push_cast; rw [Int.mul_assoc]
  have hrel' : R + 32 * ((mb : Int) * Q) = 128 * ((U : Int) * r0) := by
    rw [← Int.mul_assoc 32, ← Int.mul_assoc 128, ← hrel, hfin]
  have hUr0 : (U : Int) * r0 < (U : Int) * mb :=
    Int.mul_lt_mul_of_pos_left (show (r0 : Int) < mb by omega) hU'
  have hmbU : (mb : Int) * (4 * U) = 4 * ((U : Int) * mb) := by
    rw [Int.mul_left_comm (mb : Int) 4 (U : Int), Int.mul_comm (mb : Int) (U : Int)]
  have e256 : ((256 * U : Nat) : Int) = 256 * (U : Int) := Int.natCast_mul 256 U
  have hrs : (((ws + wc) % (256 * U) : Nat) : Int) = R % (256 * U) := by
    rw [Int.natCast_emod, e256, Int.natCast_add, show (ws : Int) + wc = R + 256 * U * t by omega,
      Int.add_mul_emod_self_left]
  generalize (ws + wc) % (256 * U) = rs at hrs ⊢
  generalize hXd : 4 * U * r0 = X at hX ⊢
  by_cases hR : 0 ≤ R
  · have hrsR : (rs : Int) = R := by rw [hrs]; exact Int.emod_eq_of_lt hR (by omega)
    have hQ0 : 0 ≤ Q := by
      have := Int.lt_of_mul_lt_mul_left (by omega : (mb : Int) * -1 < mb * Q) (Int.le_of_lt hmb)
      omega
    have hQ1 : Q < 4 * U :=
      Int.lt_of_mul_lt_mul_left (by rw [hmbU]; omega : (mb : Int) * Q < mb * (4 * U)) (Int.le_of_lt hmb)
    have hq := (Int.ediv_emod_unique hmb).2
      ⟨(by omega : (X : Int) - mb * Q + mb * Q = X), (by omega : (0 : Int) ≤ X - mb * Q), by omega⟩
    have huQ : (u : Int) = Q := by rw [hu]; exact Int.emod_eq_of_lt hQ0 (by omega)
    have hnt : ¬ 128 * U ≤ rs := by omega
    rw [if_neg hnt, Nat.mod_eq_of_lt (by omega : u < 4 * U)]
    refine ⟨?_, ?_⟩
    · have : ((X / mb : Nat) : Int) = Q := by push_cast; exact hq.1
      omega
    · have : ((X % mb : Nat) : Int) = X - mb * Q := by push_cast; exact hq.2
      constructor <;> intro h <;> omega
  · have hrsR : (rs : Int) = R + 256 * U := by
      rw [hrs]; exact srt_emod _ _ _ (-1) (by omega) (by omega) (by omega)
    have hQ0 : 1 ≤ Q := by
      have := Int.lt_of_mul_lt_mul_left (by omega : (mb : Int) * 0 < mb * Q) (Int.le_of_lt hmb)
      omega
    have hQ1 : Q - 1 < 4 * U :=
      Int.lt_of_mul_lt_mul_left (by rw [Int.mul_sub, hmbU]; omega : (mb : Int) * (Q - 1) < mb * (4 * U)) (Int.le_of_lt hmb)
    have hq := (Int.ediv_emod_unique hmb).2
      ⟨(by rw [Int.mul_sub]; omega : (X : Int) - mb * Q + mb + mb * (Q - 1) = X),
        (by omega : (0 : Int) ≤ X - mb * Q + mb), by omega⟩
    have humQ : (um : Int) = Q - 1 := by rw [hum]; exact Int.emod_eq_of_lt (by omega) (by omega)
    have ht' : 128 * U ≤ rs := by omega
    rw [if_pos ht', Nat.mod_eq_of_lt (by omega : um < 4 * U)]
    refine ⟨?_, ?_⟩
    · have : ((X / mb : Nat) : Int) = Q - 1 := by push_cast; exact hq.1
      omega
    · have : ((X % mb : Nat) : Int) = X - mb * Q + mb := by push_cast; exact hq.2
      constructor <;> intro h <;> omega

/-- **Pre-aligned radix-4 SRT division.** For `r0 < mb`, `2^(P-1) ≤ mb < 2^P`, `NS` stages with `2*NS = P + XS`
(`1 ≤ XS ≤ 2`), `ws[0] = 32·r0 / 2^XS` and `wc[0] = 0`, the corrected low quotient `ql` and sticky `rs ≠ 0` are
`⌊2^P · r0 / mb⌋` and `(2^P · r0) mod mb ≠ 0`. -/
theorem srt_pre (P NS XS r0 mb da nd1 nd2 : Nat) (hP : 2 ≤ P) (hr0 : r0 < mb) (hb1 : 2 ^ (P - 1) ≤ mb)
    (hb2 : mb < 2 ^ P) (hN : 2 * NS = P + XS) (hXS1 : 1 ≤ XS) (hXS2 : XS ≤ 2) (hda : da = 8 * mb / 2 ^ (P - 1) % 8)
    (hnd1 : nd1 + 8 * mb + 8 = 2 ^ (P + 6)) (hnd2 : nd2 + 16 * mb + 8 = 2 ^ (P + 6))
    (ws wc u um es yb mm sm cy : Nat → Nat) (g2 g1 g0 gm : Nat → Bool)
    (hws0 : ws 0 = 32 * r0 / 2 ^ XS % 2 ^ (P + 6)) (hwc0 : wc 0 = 0) (hu0 : u 0 = 0)
    (hum0 : um 0 = 2 ^ (P + 2) - 1)
    (hes : ∀ k, k < NS → es k = (ws k / 2 ^ (P - 2) % 256 + wc k / 2 ^ (P - 2) % 256) % 256)
    (hyb : ∀ k, k < NS → yb k = (es k / 2 % 128 + 64) % 128)
    (hg2 : ∀ k, k < NS → g2 k = decide (srtT2 da ≤ yb k)) (hg1 : ∀ k, k < NS → g1 k = decide (srtT1 da ≤ yb k))
    (hg0 : ∀ k, k < NS → g0 k = decide (srtT0 da ≤ yb k)) (hgm : ∀ k, k < NS → gm k = decide (srtTm da ≤ yb k))
    (hmm : ∀ k, k < NS → mm k = if g2 k = true then nd2 else if g1 k = true then nd1 else if g0 k = true then 0
      else if gm k = true then 8 * mb else 16 * mb)
    (hcsa : ∀ k, k < NS → sm k + 2 * cy k = ws k + wc k + mm k) (hcy : ∀ k, k < NS → cy k % 8 = 0)
    (hws : ∀ k, k < NS → ws (k + 1) = 4 * (sm k % 2 ^ (P + 4)))
    (hwc : ∀ k, k < NS → wc (k + 1) = 64 * (cy k / 8 % 2 ^ P) + 32 * (g1 k).toNat)
    (hu : ∀ k, k < NS → u (k + 1) = 4 * ((if g0 k = true then u k else um k) % 2 ^ P) +
      2 * (g2 k || !g0 k).toNat + (g1 k && !g2 k || gm k && !g0 k).toNat)
    (hum : ∀ k, k < NS → um (k + 1) = 4 * ((if g1 k = true then u k else um k) % 2 ^ P) +
      2 * (!g1 k && gm k).toNat + (g2 k || g0 k && !g1 k || !gm k).toNat) :
    (if 2 ^ (P + 5) ≤ (ws NS + wc NS) % 2 ^ (P + 6) then um NS % 2 ^ P else u NS % 2 ^ P) = 2 ^ P * r0 / mb ∧
      ((ws NS + wc NS) % 2 ^ (P + 6) ≠ 0 ↔ 2 ^ P * r0 % mb ≠ 0) := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := srt_pows P hP
  have hr0w := srt_r0_pre P r0 XS hXS1 hXS2 (by omega)
  have hU := Nat.two_pow_pos (P - 2)
  rw [p1] at hb1 hda
  rw [p2] at hb2 hu hum hwc ⊢
  rw [p4] at hum0
  rw [p5] at hws
  rw [p6]
  rw [p7] at hnd1 hnd2 hws0 hr0w ⊢
  have hfin : (4 : Nat) ^ NS * (r0 * 2 ^ (5 - XS)) = 128 * 2 ^ (P - 2) * r0 := by
    rw [← p6, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul, Nat.mul_left_comm, ← Nat.pow_add,
      show 2 * NS + (5 - XS) = P + 5 by omega, Nat.mul_comm]
  generalize 2 ^ (P - 2) = U at *
  obtain ⟨hda8, hd1, hd2⟩ := srt_da U mb da hU hb1 hb2 hda
  have hr3 : 3 * (r0 * 2 ^ (5 - XS)) ≤ 64 * mb := by
    rcases (by omega : XS = 1 ∨ XS = 2) with rfl | rfl <;> simp <;> omega
  have hinv := srt_core U mb da nd1 nd2 (r0 * 2 ^ (5 - XS)) NS hU hb2 hda8 hd1 hd2 hnd1 hnd2 hr3
    (by rw [← hr0w]; exact Nat.mod_lt _ (by omega)) ws wc u um es yb mm sm cy g2 g1 g0 gm (hws0.trans hr0w) hwc0 hu0
    hum0 hes hyb hg2 hg1 hg0 hgm hmm hcsa hcy hws hwc hu hum NS (Nat.le_refl _)
  have hfinI := congrArg (fun x : Nat => (x : Int)) hfin
  simp only [Int.natCast_mul, Int.natCast_pow] at hfinI
  exact srt_final_pre U r0 mb _ NS (ws NS) (wc NS) (u NS) (um NS) hU hr0 hb1 hb2 hinv hfinI

end SvGolf.FdivParam

end SrCore

section SrG1

set_option maxRecDepth 100000

/-!
# Task `fdivp`, the SRT reference: the glue for the SRT core

The sites of the SRT core of `fdivp_srt.sv` (the divisor multiples `mbn`, `dv`, `d2`, `nd1`, `nd2`, `zw`, the dividend
`xw`, the divisor bits `da`, the selection tables `t2`, `t1`, `t0`, `tm`, row 0 of the family, the family `srt`, and
`rs`, `qq`, `rnz`), in the style of `DpG2`/`DpG3`: one lemma per shape of the printed equations, the equation the
hypothesis `h`, the conclusion the `Nat` value of the site, a family lemma for every row `i < N` at once. `core` puts
them together into the hypotheses of `LeanModels.Sv.Lib.srt_rest` (the rows of the family as `Nat` sequences
`i ↦ XF.val (row i)`), whose conclusion is what the model of `DpQ` reads (`qqN`, `rrN`).
-/

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four
  val_not val_csa val_xor_top)

/-! ## Constants, concatenations, windows -/

/-- A copy of a row (`ma = na_r[P-1]`, `mb = nb_r[P-1]`). -/
theorem g_copy (P n r v : Nat) (hn : n = P) (fm fn : Nat → Bool) (hv : XF.val (fun x => fn (r + x)) P = v)
    (h : ∀ k, k < n → fm k = fn (r + k)) : XF.val (fun x => fm x) P = v := by
  subst n
  rw [XF.val_congr_lt (fun j hj => h j hj), hv]

/-- A concatenation `{hi, g, lo}` of a row `g` between two constants. -/
theorem g_cat3 (n m wl wh M N' vl vh v : Nat) (f g : Nat → Bool) (clo chi : LVec) (hwl : clo.width = wl)
    (hm : m = M) (hn : n = N') (hN' : N' = wl + M + wh)
    (hvl : XF.val (fun x => clo.boolAt x) wl = vl) (hvh : XF.val (fun x => chi.boolAt x) wh = vh)
    (hg : XF.val (fun x => g x) M = v)
    (h : ∀ k, k < n → f k = if k < m + clo.width then (if k < clo.width then clo.boolAt k else g (k - clo.width))
      else chi.boolAt (k - (m + clo.width))) :
    XF.val (fun x => f x) N' = vl + 2 ^ wl * (v + 2 ^ M * vh) := by
  subst hm hn hN'
  rw [hwl] at h
  rw [XF.val_congr_lt (fun j hj => h j hj)]
  have h1 := val_cat (fun k => if k < wl then clo.boolAt k else g (k - wl)) (fun x => chi.boolAt x) (m + wl) wh
  have h2 := val_cat (fun x => clo.boolAt x) g wl m
  rw [show wl + m + wh = m + wl + wh by omega, h1, show m + wl = wl + m by omega, h2, hvl, hvh, hg, Nat.pow_add,
    Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- A complement `~g`. -/
theorem g_not (n P v : Nat) (hn : n = P) (f g : Nat → Bool) (hg : XF.val (fun k => g k) P = v)
    (h : ∀ k, k < n → f k = !g k) : XF.val (fun x => f x) P = 2 ^ P - 1 - v := by
  subst hn
  rw [XF.val_congr_lt (fun j hj => h j hj), val_not, ← hg]

/-- A window `g[s + w - 1 : s]`. -/
theorem g_win (n s w o M v : Nat) (hn : n = w) (hs : s = o) (hle : o + w ≤ M) (f g : Nat → Bool)
    (hg : XF.val (fun x => g x) M = v) (h : ∀ k, k < n → f k = g (s + k)) :
    XF.val (fun x => f x) w = v / 2 ^ o % 2 ^ w := by
  subst hn hs
  rw [XF.val_congr_lt (fun j hj => h j hj), val_window g s n M hle, ← hg]

/-- A selection table: a 3-level `?:` tree over the three bits of `da`, its eight leaves the constants `T 0 .. T 7`. -/
theorem g_tbl (n i2 i1 : Nat) (hn : n = 7) (hi2 : i2 = 2) (hi1 : i1 = 1) (ft fda : Nat → Bool)
    (T : Nat → Nat) (c0 c1 c2 c3 c4 c5 c6 c7 : LVec)
    (h0 : XF.val (fun x => c0.boolAt x) 7 = T 0) (h1 : XF.val (fun x => c1.boolAt x) 7 = T 1)
    (h2 : XF.val (fun x => c2.boolAt x) 7 = T 2) (h3 : XF.val (fun x => c3.boolAt x) 7 = T 3)
    (h4 : XF.val (fun x => c4.boolAt x) 7 = T 4) (h5 : XF.val (fun x => c5.boolAt x) 7 = T 5)
    (h6 : XF.val (fun x => c6.boolAt x) 7 = T 6) (h7 : XF.val (fun x => c7.boolAt x) 7 = T 7)
    (h : ∀ k, k < n → ft k =
      if fda i2 = true then
        (if fda i1 = true then (if fda 0 = true then c7.boolAt k else c6.boolAt k)
         else (if fda 0 = true then c5.boolAt k else c4.boolAt k))
      else
        (if fda i1 = true then (if fda 0 = true then c3.boolAt k else c2.boolAt k)
         else (if fda 0 = true then c1.boolAt k else c0.boolAt k))) :
    XF.val (fun x => ft x) 7 = T (XF.val (fun x => fda x) 3) := by
  subst hn hi2 hi1
  rw [XF.val_congr_lt (fun j hj => h j hj)]
  have hv : XF.val (fun x => fda x) 3 = (fda 0).toNat + 2 * (fda 1).toNat + 4 * (fda 2).toNat := by
    simp only [XF.val]; omega
  rw [hv]
  cases fda 2 <;> cases fda 1 <;> cases fda 0 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true] <;> assumption

/-- The three low bits of a multiple of 8. -/
theorem low3_false (f : Nat → Bool) (n x : Nat) (hx : XF.val f n = x) (h8 : x % 8 = 0) (hn : 3 ≤ n) :
    ∀ j, j < 3 → f j = false := by
  intro j hj
  rw [bit_eq_of_val f n x j hx (by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp <;> omega

/-- A value whose three low bits are zero is a multiple of 8. -/
theorem low3_val (f : Nat → Bool) (n : Nat) (hn : 3 ≤ n) (h : ∀ j, j < 3 → f j = false) : XF.val f n % 8 = 0 := by
  have hs := val_split f 3 (n - 3)
  rw [show 3 + (n - 3) = n by omega, val_all_false f 3 h] at hs
  rw [hs]
  simp

/-! ## The family `srt`: one stage -/

/-- `es[k] = ws[k][P+5:P-2] + wc[k][P+5:P-2]`. -/
theorem g_es (P N w8 : Nat) (NI : Int) (hN : NI = (N : Int)) (hP : 2 ≤ P) (hw8 : w8 = 8) (fes fws fwc : Nat → Bool)
    (h : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w8 → fes (rmN 8 (i : Int) 0 + k) =
      XF.addBits w8 (fun x => fws (rmN ((P : Int) + 6) (i : Int) ((P : Int) + -2) + x)) w8
        (fun x => fwc (rmN ((P : Int) + 6) (i : Int) ((P : Int) + -2) + x)) k) :
    ∀ i, i < N → XF.val (fun x => fes (i * 8 + x)) 8 =
      (XF.val (fun x => fws (i * (P + 6) + x)) (P + 6) / 2 ^ (P - 2) % 256 +
        XF.val (fun x => fwc (i * (P + 6) + x)) (P + 6) / 2 ^ (P - 2) % 256) % 256 := by
  subst hN hw8
  intro i hi
  have hrow := h i (by omega)
  have o1 : rmN 8 (i : Int) 0 = i * 8 := rmN_eq _ _ _ 8 i 0 (by omega) rfl rfl
  have o2 : rmN ((P : Int) + 6) (i : Int) ((P : Int) + -2) = i * (P + 6) + (P - 2) :=
    rmN_eq _ _ _ (P + 6) i (P - 2) (by omega) rfl (by omega)
  rw [o1, o2] at hrow
  rw [XF.val_congr_lt (fun j hj => hrow j hj), val_addBits]
  have e : ∀ fw : Nat → Bool, XF.val (fun x => fw (i * (P + 6) + (P - 2) + x)) 8 =
      XF.val (fun x => fw (i * (P + 6) + x)) (P + 6) / 2 ^ (P - 2) % 256 := by
    intro fw
    have hw := val_window (fun x => fw (i * (P + 6) + x)) (P - 2) 8 (P + 6) (by omega)
    rw [show (2 : Nat) ^ 8 = 256 from rfl] at hw
    rw [← hw]
    exact XF.val_congr_lt (fun j _ => by rw [Nat.add_assoc])
  rw [e fws, e fwc]

/-- `yb[k] = es[k][7:1] ^ 7'b1000000`. -/
theorem g_yb (N w7 : Nat) (NI : Int) (hN : NI = (N : Int)) (hw7 : w7 = 7) (fyb fes : Nat → Bool) (c : LVec)
    (hc : XF.val (fun x => c.boolAt x) 7 = 64)
    (h : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w7 →
      fyb (rmN 7 (i : Int) 0 + k) = (fes (rmN 8 (i : Int) 1 + k) ^^ c.boolAt k)) :
    ∀ i, i < N → XF.val (fun x => fyb (i * 7 + x)) 7 = (XF.val (fun x => fes (i * 8 + x)) 8 / 2 % 128 + 64) % 128 := by
  subst hN hw7
  intro i hi
  have hrow := h i (by omega)
  have o1 : rmN 7 (i : Int) 0 = i * 7 := rmN_eq _ _ _ 7 i 0 (by omega) rfl rfl
  have o2 : rmN 8 (i : Int) 1 = i * 8 + 1 := rmN_eq _ _ _ 8 i 1 (by omega) rfl (by omega)
  rw [o1, o2] at hrow
  rw [XF.val_congr_lt (fun j hj => hrow j hj)]
  have hx := val_xor_top (fun x => fes (i * 8 + 1 + x)) (fun x => c.boolAt x) 6 hc
  have hw := val_window (fun x => fes (i * 8 + x)) 1 7 8 (by omega)
  have e : XF.val (fun x => fes (i * 8 + 1 + x)) 7 = XF.val (fun x => fes (i * 8 + (1 + x))) 7 :=
    XF.val_congr_lt (fun j _ => by rw [Nat.add_assoc])
  rw [hx, e, hw]

/-- `g[k] = (yb[k] >= t)`, the table value `T`. -/
theorem g_ge (N m : Nat) (NI : Int) (hN : NI = (N : Int)) (hm : m = 7) (fg fyb ft : Nat → Bool) (T : Nat)
    (ht : XF.val (fun x => ft x) 7 = T)
    (h : ∀ (i : Nat), (i : Int) < NI →
      fg i = decide (XF.val (fun x => fyb (rmN 7 (i : Int) 0 + x)) m ≥ XF.val (fun x => ft x) m)) :
    ∀ i, i < N → fg i = decide (T ≤ XF.val (fun x => fyb (i * 7 + x)) 7) := by
  subst hN hm
  intro i hi
  have o : rmN 7 (i : Int) 0 = i * 7 := rmN_eq _ _ _ 7 i 0 (by omega) rfl rfl
  rw [h i (by omega), ht, o]

/-- `mm[k]`: the priority chain on the comparisons over the five multiples. -/
theorem g_mm (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 6)
    (fmm fg2 fg1 fg0 fgm fnd2 fnd1 fzw fdv fd2 : Nat → Bool) (nd2 nd1 dv d2 : Nat)
    (hnd2 : XF.val (fun x => fnd2 x) (P + 6) = nd2) (hnd1 : XF.val (fun x => fnd1 x) (P + 6) = nd1)
    (hzw : XF.val (fun x => fzw x) (P + 6) = 0) (hdv : XF.val (fun x => fdv x) (P + 6) = dv)
    (hd2 : XF.val (fun x => fd2 x) (P + 6) = d2)
    (h : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fmm (rmN ((P : Int) + 6) (i : Int) 0 + k) =
      if fg2 i = true then fnd2 k else if fg1 i = true then fnd1 k else if fg0 i = true then fzw k
      else if fgm i = true then fdv k else fd2 k) :
    ∀ i, i < N → XF.val (fun x => fmm (i * (P + 6) + x)) (P + 6) =
      if fg2 i = true then nd2 else if fg1 i = true then nd1 else if fg0 i = true then 0
      else if fgm i = true then dv else d2 := by
  subst hN hw
  intro i hi
  have hrow := h i (by omega)
  have o : rmN ((P : Int) + 6) (i : Int) 0 = i * (P + 6) := rmN_eq _ _ _ (P + 6) i 0 (by omega) rfl rfl
  rw [o] at hrow
  rw [XF.val_congr_lt (fun j hj => hrow j hj)]
  cases fg2 i <;> cases fg1 i <;> cases fg0 i <;> cases fgm i <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption

/-- `sm[k] = ws ^ wc ^ mm`, `cy[k] = maj(ws, wc, mm)`: one full-adder row. -/
theorem g_csa (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 6) (fsm fcy fws fwc fmm : Nat → Bool)
    (hs : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fsm (rmN ((P : Int) + 6) (i : Int) 0 + k) =
      (fws (rmN ((P : Int) + 6) (i : Int) 0 + k) ^^ fwc (rmN ((P : Int) + 6) (i : Int) 0 + k) ^^
        fmm (rmN ((P : Int) + 6) (i : Int) 0 + k)))
    (hc : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fcy (rmN ((P : Int) + 6) (i : Int) 0 + k) =
      (fws (rmN ((P : Int) + 6) (i : Int) 0 + k) && fwc (rmN ((P : Int) + 6) (i : Int) 0 + k) ||
          fws (rmN ((P : Int) + 6) (i : Int) 0 + k) && fmm (rmN ((P : Int) + 6) (i : Int) 0 + k) ||
        fwc (rmN ((P : Int) + 6) (i : Int) 0 + k) && fmm (rmN ((P : Int) + 6) (i : Int) 0 + k))) :
    ∀ i, i < N → XF.val (fun x => fsm (i * (P + 6) + x)) (P + 6) + 2 * XF.val (fun x => fcy (i * (P + 6) + x)) (P + 6) =
      XF.val (fun x => fws (i * (P + 6) + x)) (P + 6) + XF.val (fun x => fwc (i * (P + 6) + x)) (P + 6) +
        XF.val (fun x => fmm (i * (P + 6) + x)) (P + 6) := by
  subst hN hw
  intro i hi
  have hs' := hs i (by omega)
  have hc' := hc i (by omega)
  have o : rmN ((P : Int) + 6) (i : Int) 0 = i * (P + 6) := rmN_eq _ _ _ (P + 6) i 0 (by omega) rfl rfl
  rw [o] at hs' hc'
  rw [XF.val_congr_lt (fun j hj => hs' j hj), XF.val_congr_lt (fun j hj => hc' j hj)]
  exact val_csa (fun x => fws (i * (P + 6) + x)) (fun x => fwc (i * (P + 6) + x)) (fun x => fmm (i * (P + 6) + x))
    (P + 6)

/-- The carry `cy[k]` has its three low bits zero when `wc[k]` and `mm[k]` have. -/
theorem g_cy (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 6) (fcy fws fwc fmm : Nat → Bool)
    (hc : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fcy (rmN ((P : Int) + 6) (i : Int) 0 + k) =
      (fws (rmN ((P : Int) + 6) (i : Int) 0 + k) && fwc (rmN ((P : Int) + 6) (i : Int) 0 + k) ||
          fws (rmN ((P : Int) + 6) (i : Int) 0 + k) && fmm (rmN ((P : Int) + 6) (i : Int) 0 + k) ||
        fwc (rmN ((P : Int) + 6) (i : Int) 0 + k) && fmm (rmN ((P : Int) + 6) (i : Int) 0 + k)))
    (hwc8 : ∀ i, i < N → XF.val (fun x => fwc (i * (P + 6) + x)) (P + 6) % 8 = 0)
    (hmm8 : ∀ i, i < N → XF.val (fun x => fmm (i * (P + 6) + x)) (P + 6) % 8 = 0) :
    ∀ i, i < N → XF.val (fun x => fcy (i * (P + 6) + x)) (P + 6) % 8 = 0 := by
  subst hN hw
  intro i hi
  have hc' := hc i (by omega)
  have o : rmN ((P : Int) + 6) (i : Int) 0 = i * (P + 6) := rmN_eq _ _ _ (P + 6) i 0 (by omega) rfl rfl
  rw [o] at hc'
  have bw := low3_false (fun x => fwc (i * (P + 6) + x)) (P + 6) _ rfl (hwc8 i hi) (by omega)
  have bm := low3_false (fun x => fmm (i * (P + 6) + x)) (P + 6) _ rfl (hmm8 i hi) (by omega)
  apply low3_val _ (P + 6) (by omega)
  intro j hj
  rw [hc' j (by omega), bw j hj, bm j hj]
  simp

/-- `ws[k+1] = {sm[k][RW-3:0], 2'b00}`. -/
theorem g_ws1 (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 6) (fws fsm : Nat → Bool) (c : LVec)
    (hcw : c.width = 2) (hc : XF.val (fun x => c.boolAt x) 2 = 0)
    (h : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fws (rmN ((P : Int) + 6) ((i : Int) + 1) 0 + k) =
      if k < c.width then c.boolAt k else fsm (rmN ((P : Int) + 6) (i : Int) 0 + (k - c.width))) :
    ∀ i, i < N → XF.val (fun x => fws ((i + 1) * (P + 6) + x)) (P + 6) =
      4 * (XF.val (fun x => fsm (i * (P + 6) + x)) (P + 6) % 2 ^ (P + 4)) := by
  subst hN hw
  intro i hi
  have hrow := h i (by omega)
  have o1 : rmN ((P : Int) + 6) ((i : Int) + 1) 0 = (i + 1) * (P + 6) :=
    rmN_eq _ _ _ (P + 6) (i + 1) 0 (by omega) (by omega) rfl
  have o : rmN ((P : Int) + 6) (i : Int) 0 = i * (P + 6) := rmN_eq _ _ _ (P + 6) i 0 (by omega) rfl rfl
  rw [o1, o, hcw] at hrow
  rw [XF.val_congr_lt (fun j hj => hrow j hj)]
  have h1 := val_cat (fun x => c.boolAt x) (fun x => fsm (i * (P + 6) + x)) 2 (P + 4)
  rw [show 2 + (P + 4) = P + 6 by omega] at h1
  rw [h1, hc, val_prefix (fun x => fsm (i * (P + 6) + x)) (P + 6) (P + 4) (by omega)]
  show 0 + 4 * _ = _
  omega

/-- `wc[k+1] = {cy[k][RW-4:3], g1[k], 5'b00000}`. -/
theorem g_wc1 (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 6) (fwc fcy fg1 : Nat → Bool) (c : LVec)
    (hcw : c.width = 5) (hc : XF.val (fun x => c.boolAt x) 5 = 0)
    (h : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fwc (rmN ((P : Int) + 6) ((i : Int) + 1) 0 + k) =
      if k < 1 + c.width then (if k < c.width then c.boolAt k else fg1 (i + (k - c.width)))
      else fcy (rmN ((P : Int) + 6) (i : Int) 3 + (k - (1 + c.width)))) :
    ∀ i, i < N → XF.val (fun x => fwc ((i + 1) * (P + 6) + x)) (P + 6) =
      64 * (XF.val (fun x => fcy (i * (P + 6) + x)) (P + 6) / 8 % 2 ^ P) + 32 * (fg1 i).toNat := by
  subst hN hw
  intro i hi
  have hrow := h i (by omega)
  have o1 : rmN ((P : Int) + 6) ((i : Int) + 1) 0 = (i + 1) * (P + 6) :=
    rmN_eq _ _ _ (P + 6) (i + 1) 0 (by omega) (by omega) rfl
  have o3 : rmN ((P : Int) + 6) (i : Int) 3 = i * (P + 6) + 3 := rmN_eq _ _ _ (P + 6) i 3 (by omega) rfl (by omega)
  rw [o1, o3, hcw] at hrow
  rw [XF.val_congr_lt (fun j hj => hrow j hj)]
  have h1 := val_cat (fun k => if k < 5 then c.boolAt k else fg1 (i + (k - 5))) (fun x => fcy (i * (P + 6) + 3 + x))
    (1 + 5) P
  have h2 := val_cat (fun x => c.boolAt x) (fun x => fg1 (i + x)) 5 1
  have hw := val_window (fun x => fcy (i * (P + 6) + x)) 3 P (P + 6) (by omega)
  have e : XF.val (fun x => fcy (i * (P + 6) + 3 + x)) P = XF.val (fun x => fcy (i * (P + 6) + (3 + x))) P :=
    XF.val_congr_lt (fun j _ => by rw [Nat.add_assoc])
  rw [show 1 + 5 + P = P + 6 by omega] at h1
  rw [h1, show (1 + 5 : Nat) = 5 + 1 from rfl, h2, hc, val_one, e, hw, Nat.add_zero]
  show 0 + 32 * _ + 64 * (_ / 8 % 2 ^ P) = _
  omega

/-- On-the-fly conversion: `u[k+1] = {us[k], d1, d0}` with `us[k] = sel ? u[k][P-1:0] : um[k][P-1:0]` (likewise
`um[k+1]`). -/
theorem g_otf (P N w : Nat) (NI : Int) (hN : NI = (N : Int)) (hw : w = P + 2) (fv fs f1 f0 fg fu fum : Nat → Bool)
    (hv : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < w → fv (rmN ((P : Int) + 2) ((i : Int) + 1) 0 + k) =
      if k < 2 then (if k = 0 then f0 (i + k) else f1 (i + (k - 1))) else fs (rmN (P : Int) (i : Int) 0 + (k - 2)))
    (hs : ∀ (i : Nat), (i : Int) < NI → ∀ (k : Nat), k < P → fs (rmN (P : Int) (i : Int) 0 + k) =
      if fg i = true then fu (rmN ((P : Int) + 2) (i : Int) 0 + k) else fum (rmN ((P : Int) + 2) (i : Int) 0 + k)) :
    ∀ i, i < N → XF.val (fun x => fv ((i + 1) * (P + 2) + x)) (P + 2) =
      4 * ((if fg i = true then XF.val (fun x => fu (i * (P + 2) + x)) (P + 2)
        else XF.val (fun x => fum (i * (P + 2) + x)) (P + 2)) % 2 ^ P) + 2 * (f1 i).toNat + (f0 i).toNat := by
  subst hN hw
  intro i hi
  have hv' := hv i (by omega)
  have hs' := hs i (by omega)
  have o1 : rmN ((P : Int) + 2) ((i : Int) + 1) 0 = (i + 1) * (P + 2) :=
    rmN_eq _ _ _ (P + 2) (i + 1) 0 (by omega) (by omega) rfl
  have o2 : rmN (P : Int) (i : Int) 0 = i * P := rmN_eq _ _ _ P i 0 (by omega) rfl rfl
  have o3 : rmN ((P : Int) + 2) (i : Int) 0 = i * (P + 2) := rmN_eq _ _ _ (P + 2) i 0 (by omega) rfl rfl
  rw [o1, o2] at hv'
  rw [o2, o3] at hs'
  rw [XF.val_congr_lt (fun j hj => hv' j hj)]
  have h1 := val_cat (fun k => if k = 0 then f0 (i + k) else f1 (i + (k - 1))) (fun x => fs (i * P + x)) 2 P
  rw [show 2 + P = P + 2 by omega] at h1
  have hlo : XF.val (fun k => if k = 0 then f0 (i + k) else f1 (i + (k - 1))) 2 = (f0 i).toNat + 2 * (f1 i).toNat := by
    simp [XF.val]
  rw [h1, hlo, XF.val_congr_lt (fun j hj => hs' j hj), val_ite]
  cases fg i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [val_prefix _ (P + 2) P (by omega)] <;> show _ + 4 * _ = _ <;> omega

/-! ## The final correction and the sticky -/

/-- `rs = ws[N] + wc[N]`. -/
theorem g_rs (P N n : Nat) (NI : Int) (hN : NI = (N : Int)) (hn : n = P + 6) (frs fws fwc : Nat → Bool)
    (h : ∀ k, k < n → frs k = XF.addBits n (fun x => fws (rmN ((P : Int) + 6) NI 0 + x)) n
      (fun x => fwc (rmN ((P : Int) + 6) NI 0 + x)) k) :
    XF.val (fun x => frs x) (P + 6) = (XF.val (fun x => fws (N * (P + 6) + x)) (P + 6) +
      XF.val (fun x => fwc (N * (P + 6) + x)) (P + 6)) % 2 ^ (P + 6) := by
  subst hn
  have o : rmN ((P : Int) + 6) NI 0 = N * (P + 6) := rmN_eq _ _ _ (P + 6) N 0 (by omega) hN rfl
  rw [o] at h
  rw [XF.val_congr_lt (fun j hj => h j hj), val_addBits]

/-- `rnz = |rs`. -/
theorem g_rnz (P n : Nat) (hn : n = P + 6) (frnz frs : Nat → Bool) (rs : Nat)
    (hrs : XF.val (fun x => frs x) (P + 6) = rs) (h : frnz 0 = XF.any n fun x => frs x) :
    frnz 0 = decide (rs ≠ 0) := by
  subst hn
  rw [h, any_eq_decide_val, hrs]



/-! ## Pre-alignment, low quotient and normalized quotient -/

/-- `d0 = {1'b0, ma} - {1'b0, mb}`. -/
theorem g_d0 (P nP ma mb : Nat) (hnP : nP = P) (fd0 fma fmb : Nat → Bool)
    (hma : XF.val (fun x => fma x) P = ma) (hmb : XF.val (fun x => fmb x) P = mb)
    (h : ∀ k, k < P + 1 → fd0 k = XF.subBits (P + 1) (fun x => if x < nP then fma x else false) (P + 1)
      (fun x => if x < nP then fmb x else false) k) :
    XF.val (fun x => fd0 x) (P + 1) = (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) := by
  subst nP
  have hz : ∀ (f : Nat → Bool) (v : Nat), XF.val (fun x => f x) P = v →
      XF.val (fun x => if x < P then f x else false) (P + 1) = v := by
    intro f v hv
    rw [val_succ, if_neg (Nat.lt_irrefl P), Bool.toNat_false, Nat.mul_zero, Nat.add_zero, ← hv]
    exact XF.val_congr_lt (fun j hj => by simp [hj])
  rw [XF.val_congr_lt (fun j hj => h j hj), val_subBits, Nat.max_self, hz fma ma hma, hz fmb mb hmb]

/-- `d1 = {ma, 1'b0} - {1'b0, mb}`. -/
theorem g_d1 (P nP ma mb : Nat) (hnP : nP = P) (fd1 fma fmb : Nat → Bool)
    (hma : XF.val (fun x => fma x) P = ma) (hmb : XF.val (fun x => fmb x) P = mb)
    (h : ∀ k, k < P + 1 → fd1 k = XF.subBits (P + 1) (fun x => if x = 0 then false else fma (x - 1)) (P + 1)
      (fun x => if x < nP then fmb x else false) k) :
    XF.val (fun x => fd1 x) (P + 1) = (2 * ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) := by
  subst nP
  have h1 : XF.val (fun x => if x = 0 then false else fma (x - 1)) (P + 1) = 2 * ma := by
    have hc := val_cat (fun _ => false) fma 1 P
    rw [show 1 + P = P + 1 by omega] at hc
    rw [XF.val_congr_lt (g := fun x => if x < 1 then false else fma (x - 1)) (fun j _ => by
      by_cases hj : j = 0 <;> simp [hj])]
    rw [hc, val_one, hma]
    simp
  have h2 : XF.val (fun x => if x < P then fmb x else false) (P + 1) = mb := by
    rw [val_succ, if_neg (Nat.lt_irrefl P), Bool.toNat_false, Nat.mul_zero, Nat.add_zero, ← hmb]
    exact XF.val_congr_lt (fun j hj => by simp [hj])
  rw [XF.val_congr_lt (fun j hj => h j hj), val_subBits, Nat.max_self, h1, h2]

/-- `adj = d0[P]`: `1` iff `ma < mb`. -/
theorem g_adj_pre (P ma mb : Nat) (hma : ma < 2 ^ P) (hmb : mb < 2 ^ P) (fadj fd0 : Nat → Bool)
    (hd0 : XF.val (fun x => fd0 x) (P + 1) = (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1))
    (h : fadj 0 = fd0 P) :
    fadj 0 = decide (¬ mb ≤ ma) ∧ (fadj 0).toNat = if mb ≤ ma then 0 else 1 := by
  have hp : 2 ^ (P + 1) = 2 * 2 ^ P := Nat.pow_succ'
  have ht := top_bit_succ_iff fd0 P _ hd0
  by_cases hc : mb ≤ ma
  · have hv : (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) = ma - mb := by
      rw [show ma + (2 ^ (P + 1) - mb) = (ma - mb) + 2 ^ (P + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have hlt : ¬ 2 ^ P ≤ (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) := by rw [hv]; omega
    have hb : fd0 P = false := by
      cases e : fd0 P
      · rfl
      · exact absurd (ht.1 e) hlt
    rw [h, hb, if_pos hc]
    simp [hc]
  · have hv : (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) = ma + (2 ^ (P + 1) - mb) :=
      Nat.mod_eq_of_lt (by omega)
    have hge : 2 ^ P ≤ (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1) := by rw [hv]; omega
    have hb : fd0 P = true := ht.2 hge
    rw [h, hb, if_neg hc]
    simp [hc]

/-- `r0 = adj ? d1[P-1:0] : d0[P-1:0]`: `ma - mb` if `mb ≤ ma`, else `2*ma - mb`. -/
theorem g_r0 (P nP ma mb : Nat) (hnP : nP = P) (hP : 2 ≤ P) (ha1 : 2 ^ (P - 1) ≤ ma) (ha2 : ma < 2 ^ P)
    (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P) (fr0 fadj fd0 fd1 : Nat → Bool)
    (hd0 : XF.val (fun x => fd0 x) (P + 1) = (ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1))
    (hd1 : XF.val (fun x => fd1 x) (P + 1) = (2 * ma + (2 ^ (P + 1) - mb)) % 2 ^ (P + 1))
    (hadj : fadj 0 = decide (¬ mb ≤ ma))
    (h : ∀ k, k < nP → fr0 k = if fadj 0 = true then fd1 k else fd0 k) :
    XF.val (fun x => fr0 x) P = if mb ≤ ma then ma - mb else 2 * ma - mb := by
  subst nP
  have hp : 2 ^ (P + 1) = 2 * 2 ^ P := Nat.pow_succ'
  have hp0 : 2 ^ P = 2 * 2 ^ (P - 1) := by
    obtain ⟨t, ht⟩ : ∃ t, P = t + 1 := ⟨P - 1, by omega⟩
    rw [ht, show t + 1 - 1 = t by omega]; exact Nat.pow_succ'
  rw [XF.val_congr_lt (fun j hj => h j hj), val_ite, val_prefix fd1 (P + 1) P (by omega),
    val_prefix fd0 (P + 1) P (by omega), hd1, hd0, hadj]
  by_cases hc : mb ≤ ma
  · simp only [hc, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [show ma + (2 ^ (P + 1) - mb) = (ma - mb) + 2 ^ (P + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show ma - mb < 2 ^ (P + 1) by omega),
      Nat.mod_eq_of_lt (show ma - mb < 2 ^ P by omega)]
  · simp only [hc, not_false_eq_true, decide_true, ↓reduceIte]
    rw [show 2 * ma + (2 ^ (P + 1) - mb) = (2 * ma - mb) + 2 ^ (P + 1) by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show 2 * ma - mb < 2 ^ (P + 1) by omega),
      Nat.mod_eq_of_lt (show 2 * ma - mb < 2 ^ P by omega)]

/-- `ql = rs[RW-1] ? um[NS][P-1:0] : u[NS][P-1:0]`. -/
theorem g_ql (P NS nP : Nat) (NI : Int) (hN : NI = (NS : Int)) (hn : nP = P) (fql frs fu fum : Nat → Bool) (rs : Nat)
    (hrs : XF.val (fun x => frs x) (P + 6) = rs)
    (h : ∀ k, k < nP → fql k = if frs ((P : Int) + 6 + -1).toNat = true then fum (rmN ((P : Int) + 2) NI 0 + k)
      else fu (rmN ((P : Int) + 2) NI 0 + k)) :
    XF.val (fun x => fql x) P = if 2 ^ (P + 5) ≤ rs then XF.val (fun x => fum (NS * (P + 2) + x)) (P + 2) % 2 ^ P
      else XF.val (fun x => fu (NS * (P + 2) + x)) (P + 2) % 2 ^ P := by
  subst nP
  have o : rmN ((P : Int) + 2) NI 0 = NS * (P + 2) := rmN_eq _ _ _ (P + 2) NS 0 (by omega) hN rfl
  rw [o, show ((P : Int) + 6 + -1).toNat = P + 5 by omega] at h
  rw [XF.val_congr_lt (fun j hj => h j hj), val_ite,
    val_prefix (fun x => fum (NS * (P + 2) + x)) (P + 2) P (by omega),
    val_prefix (fun x => fu (NS * (P + 2) + x)) (P + 2) P (by omega)]
  have ht := top_bit_succ_iff frs (P + 5) rs hrs
  by_cases hc : 2 ^ (P + 5) ≤ rs
  · rw [ht.2 hc, if_pos rfl, if_pos hc]
  · have hb : frs (P + 5) = false := by
      cases e : frs (P + 5)
      · rfl
      · exact absurd (ht.1 e) hc
    rw [hb, if_neg (by simp), if_neg hc]

/-- `qm = {1'b1, ql}`. -/
theorem g_qm_pre (P nP ql : Nat) (hnP : nP = P) (fqm fql : Nat → Bool) (c : LVec)
    (hc : XF.val (fun x => c.boolAt x) 1 = 1)
    (hql : XF.val (fun x => fql x) P = ql)
    (h : ∀ k, k < P + 1 → fqm k = if k < nP then fql k else c.boolAt (k - nP)) :
    XF.val (fun x => fqm x) (P + 1) = ql + 2 ^ P := by
  subst nP
  rw [XF.val_congr_lt (fun j hj => h j hj), val_cat fql (fun x => c.boolAt x) P 1, hql, hc, Nat.mul_one]

/-! ## The pre-aligned SRT core -/

/-- **The pre-aligned SRT core.** For normalized significands (`2^(P-1) ≤ ma, mb < 2^P`), the printed equations
of the pre-alignment and `NS = P / 2 + 1` radix-4 SRT stages give `adj`, `qm`, and `rnz` matching `M0 = 2^(P+adj)*ma`. -/
theorem core (P : Nat) (hP : 2 ≤ P)
    (f_ma f_mb f_mbn f_d0 f_d1 f_adj f_r0 f_dv f_d2 f_nd1 f_nd2 f_zw f_xw f_da f_t2 f_t1 f_t0 f_tm f_ws f_wc f_u f_um
      f_rs f_ql f_qm f_rnz f_es f_yb f_g2 f_g1 f_g0 f_gm f_mm f_sm f_cy f_uq1 f_uq0 f_um1 f_um0 f_us f_ums : Nat → Bool)
    (ma mb : Nat) (hma : XF.val (fun k => f_ma k) P = ma) (hmb : XF.val (fun k => f_mb k) P = mb)
    (ha1 : 2 ^ (P - 1) ≤ ma) (ha2 : ma < 2 ^ P) (hb1 : 2 ^ (P - 1) ≤ mb) (hb2 : mb < 2 ^ P)
    (eq_mbn_plain_12 : ∀ (k : Nat), k < ((P : Int) + -1).natAbs + 1 → f_mbn k = !f_mb k)
    (eq_d0_plain_13 : ∀ (k : Nat), k < P + 1 → f_d0 k = XF.subBits (P + 1) (fun x => if x < ((P : Int) + -1).natAbs + 1 then f_ma x else false) (P + 1) (fun x => if x < ((P : Int) + -1).natAbs + 1 then f_mb x else false) k)
    (eq_d1_plain_14 : ∀ (k : Nat), k < P + 1 → f_d1 k = XF.subBits (P + 1) (fun x => if x = 0 then false else f_ma (x - 1)) (P + 1) (fun x => if x < ((P : Int) + -1).natAbs + 1 then f_mb x else false) k)
    (eq_adj_plain_15 : f_adj 0 = f_d0 P)
    (eq_r0_plain_16 : ∀ (k : Nat), k < ((P : Int) + -1).natAbs + 1 → f_r0 k = if f_adj 0 = true then f_d1 k else f_d0 k)
    (eq_dv_plain_22 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_dv k = if k < ((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mb (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_d2_plain_23 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_d2 k = if k < ((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mb (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_nd1_plain_24 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_nd1 k = if k < ((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mbn (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l1, Logic.l1, Logic.l1] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_nd2_plain_25 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_nd2 k = if k < ((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else f_mbn (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width) else ({ bits := #[Logic.l1, Logic.l1] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width)))
    (eq_zw_plain_26 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_zw k = false)
    (eq_xw_plain_27 : ∀ (k : Nat), k < ((P : Int) + 6 + 1).natAbs + 1 → f_xw k = if k < ((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_r0 (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_da_plain_28 : ∀ (k : Nat), k < Int.natAbs 2 + 1 → f_da k = f_dv (((P : Int) + -1).toNat + k))
    (eq_t2_plain_29 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t2 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k)
    (eq_t1_plain_30 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t1 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k)
    (eq_t0_plain_31 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t0 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k)
    (eq_tm_plain_32 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_tm k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k)
    (eq_ws_plain_33 : ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_ws k = f_xw ((2 * ((P : Int) / 2 + 1) - (P : Int)).toNat + k))
    (eq_wc_plain_34 : ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_wc k = false)
    (eq_u_plain_35 : ∀ (k : Nat), k < ((P : Int) + 2).toNat → f_u k = false)
    (eq_um_plain_36 : ∀ (k : Nat), k < ((P : Int) + 2).toNat → f_um k = true)
    (eq_rs_plain_37 : ∀ (k : Nat), k < ((P : Int) + 6 + -1).natAbs + 1 → f_rs k = XF.addBits (((P : Int) + 6 + -1).natAbs + 1) (fun x => f_ws (rmN ((P : Int) + 6) ((P : Int) / 2 + 1) 0 + x)) (((P : Int) + 6 + -1).natAbs + 1) (fun x => f_wc (rmN ((P : Int) + 6) ((P : Int) / 2 + 1) 0 + x)) k)
    (eq_ql_plain_38 : ∀ (k : Nat), k < ((P : Int) + -1).natAbs + 1 → f_ql k = if f_rs ((P : Int) + 6 + -1).toNat = true then f_um (rmN ((P : Int) + 2) ((P : Int) / 2 + 1) 0 + k) else f_u (rmN ((P : Int) + 2) ((P : Int) / 2 + 1) 0 + k))
    (eq_qm_plain_39 : ∀ (k : Nat), k < P + 1 → f_qm k = if k < ((P : Int) + -1).natAbs + 1 then f_ql k else ({ bits := #[Logic.l1] } : LVec).boolAt (k - (((P : Int) + -1).natAbs + 1)))
    (eq_rnz_plain_40 : f_rnz 0 = XF.any (((P : Int) + 6 + -1).natAbs + 1) fun x => f_rs x)
    (eq_es_srt_0 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < 8 → f_es (rmN 8 ((i : Int)) 0 + k) = XF.addBits 8 (fun x => f_ws (rmN ((P : Int) + 6) ((i : Int)) ((P : Int) + -2) + x)) 8 (fun x => f_wc (rmN ((P : Int) + 6) ((i : Int)) ((P : Int) + -2) + x)) k)
    (eq_yb_srt_1 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < 7 → f_yb (rmN 7 ((i : Int)) 0 + k) = (f_es (rmN 8 ((i : Int)) 1 + k) ^^ ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k))
    (eq_g2_srt_2 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_g2 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t2 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_g1_srt_3 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_g1 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t1 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_g0_srt_4 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_g0 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t0 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_gm_srt_5 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_gm i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_tm x) (max 7 (Int.natAbs 6 + 1))))
    (eq_mm_srt_6 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_mm (rmN ((P : Int) + 6) ((i : Int)) 0 + k) = if f_g2 i = true then f_nd2 k else if f_g1 i = true then f_nd1 k else if f_g0 i = true then f_zw k else if f_gm i = true then f_dv k else f_d2 k)
    (eq_sm_srt_7 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_sm (rmN ((P : Int) + 6) ((i : Int)) 0 + k) = (f_ws (rmN ((P : Int) + 6) ((i : Int)) 0 + k) ^^ f_wc (rmN ((P : Int) + 6) ((i : Int)) 0 + k) ^^ f_mm (rmN ((P : Int) + 6) ((i : Int)) 0 + k)))
    (eq_cy_srt_8 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_cy (rmN ((P : Int) + 6) ((i : Int)) 0 + k) = (f_ws (rmN ((P : Int) + 6) ((i : Int)) 0 + k) && f_wc (rmN ((P : Int) + 6) ((i : Int)) 0 + k) || f_ws (rmN ((P : Int) + 6) ((i : Int)) 0 + k) && f_mm (rmN ((P : Int) + 6) ((i : Int)) 0 + k) || f_wc (rmN ((P : Int) + 6) ((i : Int)) 0 + k) && f_mm (rmN ((P : Int) + 6) ((i : Int)) 0 + k)))
    (eq_ws_srt_9 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_ws (rmN ((P : Int) + 6) ((i : Int) + 1) 0 + k) = if k < ({ bits := #[Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0] } : LVec).boolAt k else f_sm (rmN ((P : Int) + 6) ((i : Int)) 0 + (k - ({ bits := #[Logic.l0, Logic.l0] } : LVec).width)))
    (eq_wc_srt_10 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 6).toNat → f_wc (rmN ((P : Int) + 6) ((i : Int) + 1) 0 + k) = if k < 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_g1 (i + (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)) else f_cy (rmN ((P : Int) + 6) ((i : Int)) 3 + (k - (1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width))))
    (eq_uq1_srt_11 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_uq1 i = (f_g2 i || !f_g0 i))
    (eq_uq0_srt_12 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_uq0 i = (f_g1 i && !f_g2 i || f_gm i && !f_g0 i))
    (eq_um1_srt_13 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_um1 i = (!f_g1 i && f_gm i))
    (eq_um0_srt_14 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → f_um0 i = (f_g2 i || f_g0 i && !f_g1 i || !f_gm i))
    (eq_us_srt_15 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < P → f_us (rmN ((P : Int)) ((i : Int)) 0 + k) = if f_g0 i = true then f_u (rmN ((P : Int) + 2) ((i : Int)) 0 + k) else f_um (rmN ((P : Int) + 2) ((i : Int)) 0 + k))
    (eq_ums_srt_16 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < P → f_ums (rmN ((P : Int)) ((i : Int)) 0 + k) = if f_g1 i = true then f_u (rmN ((P : Int) + 2) ((i : Int)) 0 + k) else f_um (rmN ((P : Int) + 2) ((i : Int)) 0 + k))
    (eq_u_srt_17 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 2).toNat → f_u (rmN ((P : Int) + 2) ((i : Int) + 1) 0 + k) = if k < 2 then if k = 0 then f_uq0 (i + k) else f_uq1 (i + (k - 1)) else f_us (rmN ((P : Int)) ((i : Int)) 0 + (k - 2)))
    (eq_um_srt_18 : ∀ (i : Nat), (i : Int) < (P : Int) / 2 + 1 → ∀ (k : Nat), k < ((P : Int) + 2).toNat → f_um (rmN ((P : Int) + 2) ((i : Int) + 1) 0 + k) = if k < 2 then if k = 0 then f_um0 (i + k) else f_um1 (i + (k - 1)) else f_ums (rmN ((P : Int)) ((i : Int)) 0 + (k - 2))) :
    (f_adj 0).toNat = (if mb ≤ ma then 0 else 1) ∧
    XF.val (fun x => f_qm x) (P + 1) = 2 ^ P + 2 ^ P * (if mb ≤ ma then ma - mb else 2 * ma - mb) / mb ∧
    f_rnz 0 = decide (2 ^ P * (if mb ≤ ma then ma - mb else 2 * ma - mb) % mb ≠ 0) := by
  obtain ⟨NS, hNd⟩ : ∃ NS, NS = P / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨XS, hXSd⟩ : ∃ XS, XS = 2 * NS - P := ⟨_, rfl⟩
  have hNI : (P : Int) / 2 + 1 = (NS : Int) := by omega
  have hp6 : 2 ^ (P + 6) = 64 * 2 ^ P := by rw [Nat.pow_add, Nat.mul_comm]
  -- pre-alignment: d0, d1, adj, r0
  have hd0 := g_d0 P _ ma mb (by omega) f_d0 f_ma f_mb hma hmb eq_d0_plain_13
  have hd1 := g_d1 P _ ma mb (by omega) f_d1 f_ma f_mb hma hmb eq_d1_plain_14
  obtain ⟨hadj_b, hadj_n⟩ := g_adj_pre P ma mb ha2 hb2 f_adj f_d0 hd0 eq_adj_plain_15
  have hr0v := g_r0 P _ ma mb (by omega) hP ha1 ha2 hb1 hb2 f_r0 f_adj f_d0 f_d1 hd0 hd1 hadj_b eq_r0_plain_16
  obtain ⟨r0, hr0d⟩ : ∃ r0, r0 = if mb ≤ ma then ma - mb else 2 * ma - mb := ⟨_, rfl⟩
  rw [← hr0d] at hr0v
  have hr0_lt : r0 < mb := by
    rw [hr0d]
    have hp0 : 2 ^ P = 2 * 2 ^ (P - 1) := by
      obtain ⟨t, ht⟩ : ∃ t, P = t + 1 := ⟨P - 1, by omega⟩
      rw [ht, show t + 1 - 1 = t by omega]; exact Nat.pow_succ'
    split <;> omega
  -- divisor multiples and shifted r0
  have hmbn := g_not _ P mb (by omega) f_mbn f_mb hmb eq_mbn_plain_12
  have hdv : XF.val (fun x => f_dv x) (P + 6) = 8 * mb := by
    rw [g_cat3 _ _ 3 3 P (P + 6) 0 0 mb f_dv f_mb _ _ (by rfl) (by omega) (by omega) (by omega) (by decide) (by decide)
      hmb eq_dv_plain_22]
    simp
  have hd2 : XF.val (fun x => f_d2 x) (P + 6) = 16 * mb := by
    rw [g_cat3 _ _ 4 2 P (P + 6) 0 0 mb f_d2 f_mb _ _ (by rfl) (by omega) (by omega) (by omega) (by decide) (by decide)
      hmb eq_d2_plain_23]
    simp
  have hnd1 : XF.val (fun x => f_nd1 x) (P + 6) + 8 * mb + 8 = 2 ^ (P + 6) := by
    rw [g_cat3 _ _ 3 3 P (P + 6) 0 7 _ f_nd1 f_mbn _ _ (by rfl) (by omega) (by omega) (by omega) (by decide) (by decide)
      hmbn eq_nd1_plain_24, hp6]
    have := Nat.two_pow_pos P
    show 0 + 8 * (2 ^ P - 1 - mb + 2 ^ P * 7) + 8 * mb + 8 = 64 * 2 ^ P
    omega
  have hnd2 : XF.val (fun x => f_nd2 x) (P + 6) + 16 * mb + 8 = 2 ^ (P + 6) := by
    rw [g_cat3 _ _ 4 2 P (P + 6) 8 3 _ f_nd2 f_mbn _ _ (by rfl) (by omega) (by omega) (by omega) (by decide) (by decide)
      hmbn eq_nd2_plain_25, hp6]
    have := Nat.two_pow_pos P
    show 8 + 16 * (2 ^ P - 1 - mb + 2 ^ P * 3) + 16 * mb + 8 = 64 * 2 ^ P
    omega
  have hzw : XF.val (fun x => f_zw x) (P + 6) = 0 :=
    val_all_false _ _ (fun k hk => eq_zw_plain_26 k (by omega))
  have hxw : XF.val (fun x => f_xw x) (P + 8) = 32 * r0 := by
    rw [g_cat3 _ _ 5 3 P (P + 8) 0 0 r0 f_xw f_r0 _ _ (by rfl) (by omega) (by omega) (by omega) (by decide) (by decide)
      hr0v eq_xw_plain_27]
    simp
  have hda : XF.val (fun x => f_da x) 3 = 8 * mb / 2 ^ (P - 1) % 8 :=
    g_win _ _ 3 (P - 1) (P + 6) _ (by omega) (by omega) (by omega) f_da f_dv hdv eq_da_plain_28
  -- selection constants
  have ht2 : XF.val (fun x => f_t2 x) 7 = srtT2 (XF.val (fun x => f_da x) 3) :=
    g_tbl _ _ _ (by rfl) (by rfl) (by rfl) f_t2 f_da srtT2 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) eq_t2_plain_29
  have ht1 : XF.val (fun x => f_t1 x) 7 = srtT1 (XF.val (fun x => f_da x) 3) :=
    g_tbl _ _ _ (by rfl) (by rfl) (by rfl) f_t1 f_da srtT1 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) eq_t1_plain_30
  have ht0 : XF.val (fun x => f_t0 x) 7 = srtT0 (XF.val (fun x => f_da x) 3) :=
    g_tbl _ _ _ (by rfl) (by rfl) (by rfl) f_t0 f_da srtT0 _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) eq_t0_plain_31
  have htm : XF.val (fun x => f_tm x) 7 = srtTm (XF.val (fun x => f_da x) 3) :=
    g_tbl _ _ _ (by rfl) (by rfl) (by rfl) f_tm f_da srtTm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) eq_tm_plain_32
  -- row 0
  have hws0 : XF.val (fun x => f_ws (0 * (P + 6) + x)) (P + 6) = 32 * r0 / 2 ^ XS % 2 ^ (P + 6) := by
    simp only [Nat.zero_mul, Nat.zero_add]
    exact g_win _ _ (P + 6) XS (P + 8) _ (by omega) (by omega) (by omega) f_ws f_xw hxw eq_ws_plain_33
  have hwc0 : XF.val (fun x => f_wc (0 * (P + 6) + x)) (P + 6) = 0 := by
    simp only [Nat.zero_mul, Nat.zero_add]
    exact val_all_false _ _ (fun k hk => eq_wc_plain_34 k (by omega))
  have hu0 : XF.val (fun x => f_u (0 * (P + 2) + x)) (P + 2) = 0 := by
    simp only [Nat.zero_mul, Nat.zero_add]
    exact val_all_false _ _ (fun k hk => eq_u_plain_35 k (by omega))
  have hum0 : XF.val (fun x => f_um (0 * (P + 2) + x)) (P + 2) = 2 ^ (P + 2) - 1 := by
    simp only [Nat.zero_mul, Nat.zero_add]
    exact val_all_true _ _ (fun k hk => eq_um_plain_36 k (by omega))
  -- stages
  have hmm := g_mm P NS _ _ hNI (by omega) f_mm f_g2 f_g1 f_g0 f_gm f_nd2 f_nd1 f_zw f_dv f_d2 _ _ _ _ rfl rfl hzw
    hdv hd2 eq_mm_srt_6
  have hwc := g_wc1 P NS _ _ hNI (by omega) f_wc f_cy f_g1 _ (by rfl) (by decide) eq_wc_srt_10
  have hwc8 : ∀ i, i < NS → XF.val (fun x => f_wc (i * (P + 6) + x)) (P + 6) % 8 = 0 := by
    intro i hi
    cases i with
    | zero => rw [hwc0]
    | succ j => rw [hwc j (by omega)]; omega
  have hmm8 : ∀ i, i < NS → XF.val (fun x => f_mm (i * (P + 6) + x)) (P + 6) % 8 = 0 := by
    intro i hi
    rw [hmm i hi]
    split
    · omega
    · split
      · omega
      · split
        · rfl
        · split <;> omega
  have hcy := g_cy P NS _ _ hNI (by omega) f_cy f_ws f_wc f_mm eq_cy_srt_8 hwc8 hmm8
  have hu : ∀ i, i < NS → XF.val (fun x => f_u ((i + 1) * (P + 2) + x)) (P + 2) =
      4 * ((if f_g0 i = true then XF.val (fun x => f_u (i * (P + 2) + x)) (P + 2)
        else XF.val (fun x => f_um (i * (P + 2) + x)) (P + 2)) % 2 ^ P) + 2 * (f_g2 i || !f_g0 i).toNat +
        (f_g1 i && !f_g2 i || f_gm i && !f_g0 i).toNat := by
    intro i hi
    rw [g_otf P NS _ _ hNI (by omega) f_u f_us f_uq1 f_uq0 f_g0 f_u f_um eq_u_srt_17 eq_us_srt_15 i hi,
      eq_uq1_srt_11 i (by omega), eq_uq0_srt_12 i (by omega)]
  have hum : ∀ i, i < NS → XF.val (fun x => f_um ((i + 1) * (P + 2) + x)) (P + 2) =
      4 * ((if f_g1 i = true then XF.val (fun x => f_u (i * (P + 2) + x)) (P + 2)
        else XF.val (fun x => f_um (i * (P + 2) + x)) (P + 2)) % 2 ^ P) + 2 * (!f_g1 i && f_gm i).toNat +
        (f_g2 i || f_g0 i && !f_g1 i || !f_gm i).toNat := by
    intro i hi
    rw [g_otf P NS _ _ hNI (by omega) f_um f_ums f_um1 f_um0 f_g1 f_u f_um eq_um_srt_18 eq_ums_srt_16 i hi,
      eq_um1_srt_13 i (by omega), eq_um0_srt_14 i (by omega)]
  -- final correction and sticky
  have hrs := g_rs P NS _ _ hNI (by omega) f_rs f_ws f_wc eq_rs_plain_37
  have hql := g_ql P NS _ _ hNI (by omega) f_ql f_rs f_u f_um _ hrs eq_ql_plain_38
  have hqm := g_qm_pre P _ _ (by omega) f_qm f_ql _ (by decide) hql eq_qm_plain_39
  have hrnz := g_rnz P _ (by omega) f_rnz f_rs _ hrs eq_rnz_plain_40
  obtain ⟨hQ, hS⟩ := srt_pre P NS XS r0 mb (XF.val (fun x => f_da x) 3) (XF.val (fun x => f_nd1 x) (P + 6))
    (XF.val (fun x => f_nd2 x) (P + 6)) hP hr0_lt hb1 hb2 (by omega) (by omega) (by omega) hda hnd1 hnd2
    (fun i => XF.val (fun x => f_ws (i * (P + 6) + x)) (P + 6)) (fun i => XF.val (fun x => f_wc (i * (P + 6) + x)) (P + 6))
    (fun i => XF.val (fun x => f_u (i * (P + 2) + x)) (P + 2)) (fun i => XF.val (fun x => f_um (i * (P + 2) + x)) (P + 2))
    (fun i => XF.val (fun x => f_es (i * 8 + x)) 8) (fun i => XF.val (fun x => f_yb (i * 7 + x)) 7)
    (fun i => XF.val (fun x => f_mm (i * (P + 6) + x)) (P + 6)) (fun i => XF.val (fun x => f_sm (i * (P + 6) + x)) (P + 6))
    (fun i => XF.val (fun x => f_cy (i * (P + 6) + x)) (P + 6)) f_g2 f_g1 f_g0 f_gm hws0 hwc0 hu0 hum0
    (g_es P NS _ _ hNI hP (by rfl) f_es f_ws f_wc eq_es_srt_0)
    (g_yb NS _ _ hNI (by rfl) f_yb f_es _ (by decide) eq_yb_srt_1)
    (g_ge NS _ _ hNI (by rfl) f_g2 f_yb f_t2 _ ht2 eq_g2_srt_2)
    (g_ge NS _ _ hNI (by rfl) f_g1 f_yb f_t1 _ ht1 eq_g1_srt_3)
    (g_ge NS _ _ hNI (by rfl) f_g0 f_yb f_t0 _ ht0 eq_g0_srt_4)
    (g_ge NS _ _ hNI (by rfl) f_gm f_yb f_tm _ htm eq_gm_srt_5)
    hmm (g_csa P NS _ _ hNI (by omega) f_sm f_cy f_ws f_wc f_mm eq_sm_srt_7 eq_cy_srt_8) hcy
    (g_ws1 P NS _ _ hNI (by omega) f_ws f_sm _ (by rfl) (by decide) eq_ws_srt_9) hwc hu hum
  refine ⟨hadj_n, ?_, ?_⟩
  · rw [hqm, hQ, ← hr0d]; omega
  · rw [hrnz, ← hr0d]; exact decide_eq_decide.2 hS

end Glue
end SvGolf.FdivParam

end SrG1


/-! # Section `SrG2`: Glue: clamped denormalizer, rounding, and the chain -/

section SrG2

set_option maxRecDepth 100000

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four
  val_not)
open LeanModels.SoftFloat.Binary

/-- `dsh_big = (dsh >= P + 1)`. -/
theorem g_dsh_big (P EW nEW dv : Nat) (hnEW : nEW = EW) (hP32 : P + 1 < 2 ^ 32)
    (fdsh_big fdsh : Nat → Bool) (hdsh : XF.val (fun x => fdsh x) EW = dv)
    (h : fdsh_big 0 = decide (
      XF.val (fun x => XF.zext nEW (fun k => fdsh k) x) (max nEW 32) ≥
      XF.val (fun x => XF.addBits (max nEW 32) (fun x => XF.constBit (P : Int) 32 x)
        (max nEW 32) (fun x => XF.constBit 1 (max nEW 32) x) x) (max nEW 32))) :
    fdsh_big 0 = decide (P + 1 ≤ dv) := by
  subst nEW
  let M := max EW 32
  have hM32 : 32 ≤ M := Nat.le_max_right EW 32
  have hMEW : EW ≤ M := Nat.le_max_left EW 32
  have hpow : 2 ^ 32 ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) hM32
  have hlhs : XF.val (fun x => XF.zext EW (fun k => fdsh k) x) M = dv := by
    rw [XF.val_zext EW _ M hMEW, hdsh]
  have hPval : XF.val (fun x => XF.constBit (P : Int) 32 x) M = P := by
    unfold XF.constBit
    have he : ((P : Int).emod ((2 : Int) ^ (32 : Nat))) = (P : Int) :=
      Int.emod_eq_of_lt (by omega) (by exact_mod_cast (show P < 2 ^ 32 by omega))
    rw [he, XF.val_testBit, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]
  have h1val : XF.val (fun x => XF.constBit 1 M x) M = 1 :=
    val_constBit_one M M (by omega) (Nat.le_refl M)
  have hrhs : XF.val (fun x => XF.addBits M (fun x => XF.constBit (P : Int) 32 x) M
      (fun x => XF.constBit 1 M x) x) M = P + 1 := by
    rw [val_addBits, hPval, h1val, Nat.mod_eq_of_lt (by omega)]
  rw [h, hlhs, hrhs]

/-- `dsh_c = dsh_big ? (P + 1) : dsh[DL-1:0]`, when `dsh_big = false` (`dv < P + 1`). -/
theorem g_dsh_c_lt (P EW DL n1 n2 dv : Nat) (hDL : DL = clog2 (P + 2)) (hn1 : n1 = DL) (hn2 : n2 = DL)
    (hDLEW : DL ≤ EW) (hdv_lt : dv < P + 1)
    (fdsh_c fdsh_big fdsh : Nat → Bool)
    (hbig : fdsh_big 0 = false) (hdsh : XF.val (fun x => fdsh x) EW = dv)
    (h : ∀ k, k < n1 → fdsh_c k =
      if max 32 n2 < n1 then
        if fdsh_big 0 = true then
          XF.addBits n1 (fun x => XF.constBit (P : Int) 32 x) n1 (fun x => XF.constBit 1 n1 x) k
        else XF.zext n2 (fun k => fdsh k) k
      else
        XF.zext (max 32 n2) (fun x =>
          if fdsh_big 0 = true then
            XF.addBits (max 32 n2) (fun x => XF.constBit (P : Int) 32 x) (max 32 n2)
              (fun x => XF.constBit 1 (max 32 n2) x) x
          else XF.zext n2 (fun k => fdsh k) x) k) :
    XF.val (fun x => fdsh_c x) DL = dv := by
  subst n1 n2
  have hc : ¬ (max 32 DL < DL) := by omega
  have hbits : ∀ k, k < DL → fdsh_c k = fdsh k := by
    intro k hk
    rw [h k hk, if_neg hc]
    have hkM : k < max 32 DL := by omega
    simp [XF.zext, hkM, hk, hbig]
  rw [XF.val_congr_lt hbits, val_prefix fdsh EW DL hDLEW, hdsh]
  have h2DL : P + 2 ≤ 2 ^ DL := by rw [hDL]; exact le_two_pow_clog2 (P + 2)
  exact Nat.mod_eq_of_lt (by omega)

/-- `qs = dsh_big ? zw[P:0] : (qm >> dsh_c)`. -/
theorem g_qs_clamped (P DL nDL qmv dv : Nat) (hnDL : nDL = DL) (hqm_lt : qmv < 2 ^ (P + 1))
    (fqs fdsh_big fzw fqm fdsh_c : Nat → Bool)
    (hbig : fdsh_big 0 = decide (P + 1 ≤ dv))
    (hzw : ∀ k, k < P + 1 → fzw k = false)
    (hqm : XF.val (fun x => fqm x) (P + 1) = qmv)
    (hdc : dv < P + 1 → XF.val (fun x => fdsh_c x) DL = dv)
    (h : ∀ k, k < P + 1 → fqs k = if fdsh_big 0 = true then fzw k else XF.shrBits (P + 1) (fun x => fqm x) nDL (fun x => fdsh_c x) k) :
    XF.val (fun x => fqs x) (P + 1) = qmv / 2 ^ dv := by
  subst nDL
  by_cases hge : P + 1 ≤ dv
  · have hb : fdsh_big 0 = true := by rw [hbig]; simp [hge]
    have h0 : XF.val (fun x => fqs x) (P + 1) = 0 :=
      val_all_false _ _ (fun k hk => by rw [h k hk, hb, if_pos rfl, hzw k hk])
    have hpow : 2 ^ (P + 1) ≤ 2 ^ dv := Nat.pow_le_pow_right (by omega) hge
    rw [h0, Nat.div_eq_of_lt (by omega)]
  · have hb : fdsh_big 0 = false := by rw [hbig]; simp [hge]
    rw [XF.val_congr_lt (g := fun j => XF.shrBits (P + 1) (fun x => fqm x) DL (fun x => fdsh_c x) j)
      (fun j hj => by rw [h j hj, hb]; simp), val_shrBits, hqm, hdc (by omega)]

/-- `inc = qs[0] & (rnz | ((qs << dsh_c) != qm) | qs[1])`, with clamped `dsh_c` and pre-aligned `rnz = st0`. -/
theorem g_inc_clamped (P DL nDL qsv qmv dv : Nat) (ST0 : Prop) [Decidable ST0]
    (hnDL : nDL = DL) (hP : 1 ≤ P)
    (fqs fqm fdsh_c frnz finc : Nat → Bool)
    (hqs : XF.val (fun x => fqs x) (P + 1) = qsv)
    (hqm : XF.val (fun x => fqm x) (P + 1) = qmv)
    (hrnz : frnz 0 = decide ST0)
    (hqsd : qsv = qmv / 2 ^ dv) (hlt : qmv < 2 ^ (P + 1))
    (hdc : dv < P + 1 → XF.val (fun x => fdsh_c x) DL = dv)
    (h : finc 0 = (fqs 0 && ((frnz 0 || !XF.eqv (P + 1)
      (fun x => XF.shlBits (XF.zext (P + 1) fun x => fqs x) nDL (fun x => fdsh_c x) x) fun x => fqm x) || fqs 1))) :
    finc 0 = decide (qsv % 2 = 1 ∧ (ST0 ∨ qmv % 2 ^ dv ≠ 0 ∨ qsv / 2 % 2 = 1)) := by
  subst nDL
  have hq0 : fqs 0 = decide (qsv % 2 = 1) := by
    have := bit_eq_of_val fqs (P + 1) qsv 0 hqs (by omega)
    simpa using this
  by_cases hge : P + 1 ≤ dv
  · have hpow : 2 ^ (P + 1) ≤ 2 ^ dv := Nat.pow_le_pow_right (by omega) hge
    have hqsv0 : qsv = 0 := by rw [hqsd, Nat.div_eq_of_lt (by omega)]
    rw [h, hq0, hqsv0]
    simp
  · have hq1 : fqs 1 = decide (qsv / 2 % 2 = 1) := by
      have := bit_eq_of_val fqs (P + 1) qsv 1 hqs (by omega)
      simpa using this
    have heqv := g_eqv P DL qsv qmv dv fqs fqm fdsh_c hqs hqm (hdc (by omega)) hqsd hlt
    rw [h, hq0, hq1, hrnz, heqv, Bool.eq_iff_iff]
    simp <;> first | omega | grind

/-- Finite nonzero operands: neither exponent field is all ones and neither operand is a zero. -/
theorem fin_ops (f : Format) (av bv : Nat) (hns : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv)) :
    (eF f av ≠ 2 ^ f.w - 1 ∧ ¬ (eF f av = 0 ∧ fF f av = 0)) ∧
      (eF f bv ≠ 2 ^ f.w - 1 ∧ ¬ (eF f bv = 0 ∧ fF f bv = 0)) := by
  unfold cNanN cInfN cZeroN nanN infN zeroN at hns
  omega

theorem chain (f : Format) (hR : f.w + f.p < 2 ^ 20)
    (f_s f_ea_nz f_eb_nz f_c_nan f_c_inf f_c_zero f_na_r f_nb_r f_ya_r f_yb_r f_ma f_mb f_mbn
      f_d0 f_d1 f_adj f_r0 f_onesW f_emw f_E f_ovf f_dsh f_dv f_d2 f_nd1 f_nd2 f_zw f_xw f_da
      f_t2 f_t1 f_t0 f_tm f_ws f_wc f_u f_um f_rs f_ql f_qm f_rnz f_dsh_big f_dsh_c
      f_qs f_inc f_ef f_mag f_q f_es f_yb f_g2 f_g1 f_g0 f_gm f_mm f_sm f_cy f_uq1 f_uq0 f_um1 f_um0 f_us f_ums
      f_a f_b : Nat → Bool)
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
    (eq_mbn_plain_12 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_mbn k = !f_mb k)
    (eq_d0_plain_13 : ∀ (k : Nat), k < f.p + 1 → f_d0 k = XF.subBits (f.p + 1) (fun x => if x < ((f.p : Int) + -1).natAbs + 1 then f_ma x else false) (f.p + 1) (fun x => if x < ((f.p : Int) + -1).natAbs + 1 then f_mb x else false) k)
    (eq_d1_plain_14 : ∀ (k : Nat), k < f.p + 1 → f_d1 k = XF.subBits (f.p + 1) (fun x => if x = 0 then false else f_ma (x - 1)) (f.p + 1) (fun x => if x < ((f.p : Int) + -1).natAbs + 1 then f_mb x else false) k)
    (eq_adj_plain_15 : f_adj 0 = f_d0 f.p)
    (eq_r0_plain_16 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_r0 k = if f_adj 0 = true then f_d1 k else f_d0 k)
    (eq_onesW_plain_17 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_onesW k = true)
    (eq_emw_plain_18 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_emw k = XF.shrBits (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_E_plain_19 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_E k = XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.addBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + -1).natAbs + 1) (fun k => f_emw k) x) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_adj k) x) k)
    (eq_ovf_plain_20 : f_ovf 0 = (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && ((XF.any ((f.w : Int) + (f.p : Int) + 1 + -2 - (f.w : Int) + 1).toNat fun x => f_E (f.w + x)) || XF.all ((f.w : Int) + -1 + 1).toNat fun x => f_E x)))
    (eq_dsh_plain_21 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_dsh k = if max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)) < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) k else XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.constBit 1 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) k else XF.zext (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x else XF.subBits (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.constBit 1 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x) (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) x) k)
    (eq_dv_plain_22 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_dv k = if k < ((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mb (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_d2_plain_23 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_d2 k = if k < ((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mb (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_nd1_plain_24 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_nd1 k = if k < ((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_mbn (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l1, Logic.l1, Logic.l1] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_nd2_plain_25 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_nd2 k = if k < ((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else f_mbn (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width) else ({ bits := #[Logic.l1, Logic.l1] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).width)))
    (eq_zw_plain_26 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_zw k = false)
    (eq_xw_plain_27 : ∀ (k : Nat), k < ((f.p : Int) + 6 + 1).natAbs + 1 → f_xw k = if k < ((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_r0 (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width) else ({ bits := #[Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)))
    (eq_da_plain_28 : ∀ (k : Nat), k < Int.natAbs 2 + 1 → f_da k = f_dv (((f.p : Int) + -1).toNat + k))
    (eq_t2_plain_29 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t2 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k)
    (eq_t1_plain_30 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t1 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k)
    (eq_t0_plain_31 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_t0 k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k)
    (eq_tm_plain_32 : ∀ (k : Nat), k < Int.natAbs 6 + 1 → f_tm k = if f_da 2 = true then if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 1 = true then if f_da 0 = true then ({ bits := #[Logic.l1, Logic.l1, Logic.l1, Logic.l1, Logic.l0, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else if f_da 0 = true then ({ bits := #[Logic.l0, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k else ({ bits := #[Logic.l1, Logic.l1, Logic.l0, Logic.l0, Logic.l1, Logic.l1, Logic.l0] } : LVec).boolAt k)
    (eq_ws_plain_33 : ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_ws k = f_xw ((2 * ((f.p : Int) / 2 + 1) - (f.p : Int)).toNat + k))
    (eq_wc_plain_34 : ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_wc k = false)
    (eq_u_plain_35 : ∀ (k : Nat), k < ((f.p : Int) + 2).toNat → f_u k = false)
    (eq_um_plain_36 : ∀ (k : Nat), k < ((f.p : Int) + 2).toNat → f_um k = true)
    (eq_rs_plain_37 : ∀ (k : Nat), k < ((f.p : Int) + 6 + -1).natAbs + 1 → f_rs k = XF.addBits (((f.p : Int) + 6 + -1).natAbs + 1) (fun x => f_ws (rmN ((f.p : Int) + 6) ((f.p : Int) / 2 + 1) 0 + x)) (((f.p : Int) + 6 + -1).natAbs + 1) (fun x => f_wc (rmN ((f.p : Int) + 6) ((f.p : Int) / 2 + 1) 0 + x)) k)
    (eq_ql_plain_38 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_ql k = if f_rs ((f.p : Int) + 6 + -1).toNat = true then f_um (rmN ((f.p : Int) + 2) ((f.p : Int) / 2 + 1) 0 + k) else f_u (rmN ((f.p : Int) + 2) ((f.p : Int) / 2 + 1) 0 + k))
    (eq_qm_plain_39 : ∀ (k : Nat), k < f.p + 1 → f_qm k = if k < ((f.p : Int) + -1).natAbs + 1 then f_ql k else ({ bits := #[Logic.l1] } : LVec).boolAt (k - (((f.p : Int) + -1).natAbs + 1)))
    (eq_rnz_plain_40 : f_rnz 0 = XF.any (((f.p : Int) + 6 + -1).natAbs + 1) fun x => f_rs x)
    (eq_dsh_big_plain_41 : f_dsh_big 0 = decide (XF.val (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun k => f_dsh k) x) (max (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) 32) ≥ XF.val (fun x => XF.addBits (max (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) 32) (fun x => XF.constBit ((f.p : Int)) 32 x) (max (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) 32) (fun x => XF.constBit 1 (max (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) 32) x) x) (max (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) 32)))
    (eq_dsh_c_plain_42 : ∀ (k : Nat), k < ((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1 → f_dsh_c k = if max 32 ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat < ((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1 then if f_dsh_big 0 = true then XF.addBits (((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1) (fun x => XF.constBit ((f.p : Int)) 32 x) (((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1) (fun x => XF.constBit 1 (((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1) x) k else XF.zext ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat (fun k => f_dsh k) k else XF.zext (max 32 ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat) (fun x => if f_dsh_big 0 = true then XF.addBits (max 32 ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat) (fun x => XF.constBit ((f.p : Int)) 32 x) (max 32 ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat) (fun x => XF.constBit 1 (max 32 ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat) x) x else XF.zext ((clog2 ((f.p : Int) + 2).toNat : Int) + -1 + 1).toNat (fun k => f_dsh k) x) k)
    (eq_qs_plain_43 : ∀ (k : Nat), k < f.p + 1 → f_qs k = if f_dsh_big 0 = true then f_zw k else XF.shrBits (f.p + 1) (fun x => f_qm x) (((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1) (fun x => f_dsh_c x) k)
    (eq_inc_plain_44 : f_inc 0 = (f_qs 0 && ((f_rnz 0 || !XF.eqv (f.p + 1) (fun x => XF.shlBits (XF.zext (f.p + 1) fun x => f_qs x) (((clog2 ((f.p : Int) + 2).toNat : Int) + -1).natAbs + 1) (fun x => f_dsh_c x) x) fun x => f_qm x) || f_qs 1)))
    (eq_ef_plain_45 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_ef k = if max ((f.w : Int) + -1 + 1).toNat 32 < ((f.w : Int) + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) k else XF.constBit 0 (((f.w : Int) + -1).natAbs + 1) k else XF.zext (max ((f.w : Int) + -1 + 1).toNat 32) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) x else XF.constBit 0 (max ((f.w : Int) + -1 + 1).toNat 32) x) k)
    (eq_mag_plain_46 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 → f_mag k = XF.addBits (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => if x < ((f.p : Int) + -1).toNat then f_qs (1 + x) else f_ef (x - ((f.p : Int) + -1).toNat)) (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => XF.zext 1 (fun k => f_inc k) x) k)
    (eq_q_plain_47 : f_q ((f.w : Int) + (f.p : Int) + -1).toNat = (!f_c_nan 0 && f_s 0))
    (eq_q_plain_48 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat → f_q (((f.p : Int) - 1).toNat + k) = if max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat) < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat then if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) k else if f_c_zero 0 = true then XF.constBit 0 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat k else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) k else XF.zext (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) (fun x => if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) x else if f_c_zero 0 = true then XF.constBit 0 (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) x else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) x) k)
    (eq_q_plain_49 : f_q ((f.p : Int) - 1 + -1).toNat = (f_c_nan 0 || !(f_c_nan 0 || f_c_inf 0 || f_c_zero 0 || f_ovf 0) && f_mag ((f.p : Int) - 1 + -1).toNat))
    (eq_na_r_norm_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_na_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_nb_r_norm_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_nb_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_ya_r_norm_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_yb_r_norm_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_es_srt_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < 8 → f_es (rmN 8 ((i : Int)) 0 + k) = XF.addBits 8 (fun x => f_ws (rmN ((f.p : Int) + 6) ((i : Int)) ((f.p : Int) + -2) + x)) 8 (fun x => f_wc (rmN ((f.p : Int) + 6) ((i : Int)) ((f.p : Int) + -2) + x)) k)
    (eq_yb_srt_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < 7 → f_yb (rmN 7 ((i : Int)) 0 + k) = (f_es (rmN 8 ((i : Int)) 1 + k) ^^ ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l1] } : LVec).boolAt k))
    (eq_g2_srt_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_g2 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t2 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_g1_srt_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_g1 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t1 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_g0_srt_4 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_g0 i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_t0 x) (max 7 (Int.natAbs 6 + 1))))
    (eq_gm_srt_5 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_gm i = decide (XF.val (fun x => f_yb (rmN 7 ((i : Int)) 0 + x)) (max 7 (Int.natAbs 6 + 1)) ≥ XF.val (fun x => f_tm x) (max 7 (Int.natAbs 6 + 1))))
    (eq_mm_srt_6 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_mm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) = if f_g2 i = true then f_nd2 k else if f_g1 i = true then f_nd1 k else if f_g0 i = true then f_zw k else if f_gm i = true then f_dv k else f_d2 k)
    (eq_sm_srt_7 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_sm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) = (f_ws (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) ^^ f_wc (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) ^^ f_mm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k)))
    (eq_cy_srt_8 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_cy (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) = (f_ws (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) && f_wc (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) || f_ws (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) && f_mm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) || f_wc (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k) && f_mm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + k)))
    (eq_ws_srt_9 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_ws (rmN ((f.p : Int) + 6) ((i : Int) + 1) 0 + k) = if k < ({ bits := #[Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0] } : LVec).boolAt k else f_sm (rmN ((f.p : Int) + 6) ((i : Int)) 0 + (k - ({ bits := #[Logic.l0, Logic.l0] } : LVec).width)))
    (eq_wc_srt_10 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 6).toNat → f_wc (rmN ((f.p : Int) + 6) ((i : Int) + 1) 0 + k) = if k < 1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then if k < ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width then ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).boolAt k else f_g1 (i + (k - ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width)) else f_cy (rmN ((f.p : Int) + 6) ((i : Int)) 3 + (k - (1 + ({ bits := #[Logic.l0, Logic.l0, Logic.l0, Logic.l0, Logic.l0] } : LVec).width))))
    (eq_uq1_srt_11 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_uq1 i = (f_g2 i || !f_g0 i))
    (eq_uq0_srt_12 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_uq0 i = (f_g1 i && !f_g2 i || f_gm i && !f_g0 i))
    (eq_um1_srt_13 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_um1 i = (!f_g1 i && f_gm i))
    (eq_um0_srt_14 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → f_um0 i = (f_g2 i || f_g0 i && !f_g1 i || !f_gm i))
    (eq_us_srt_15 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < f.p → f_us (rmN ((f.p : Int)) ((i : Int)) 0 + k) = if f_g0 i = true then f_u (rmN ((f.p : Int) + 2) ((i : Int)) 0 + k) else f_um (rmN ((f.p : Int) + 2) ((i : Int)) 0 + k))
    (eq_ums_srt_16 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < f.p → f_ums (rmN ((f.p : Int)) ((i : Int)) 0 + k) = if f_g1 i = true then f_u (rmN ((f.p : Int) + 2) ((i : Int)) 0 + k) else f_um (rmN ((f.p : Int) + 2) ((i : Int)) 0 + k))
    (eq_u_srt_17 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 2).toNat → f_u (rmN ((f.p : Int) + 2) ((i : Int) + 1) 0 + k) = if k < 2 then if k = 0 then f_uq0 (i + k) else f_uq1 (i + (k - 1)) else f_us (rmN ((f.p : Int)) ((i : Int)) 0 + (k - 2)))
    (eq_um_srt_18 : ∀ (i : Nat), (i : Int) < (f.p : Int) / 2 + 1 → ∀ (k : Nat), k < ((f.p : Int) + 2).toNat → f_um (rmN ((f.p : Int) + 2) ((i : Int) + 1) 0 + k) = if k < 2 then if k = 0 then f_um0 (i + k) else f_um1 (i + (k - 1)) else f_ums (rmN ((f.p : Int)) ((i : Int)) 0 + (k - 2)))
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
  -- normalizer rows
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
  -- normalized significands
  have hma : XF.val (fun x => f_ma x) f.p = naN f av :=
    g_copy f.p _ _ _ (by omega) f_ma f_na_r (by rw [hrtop]; exact hna_val) eq_ma_plain_10
  have hmb : XF.val (fun x => f_mb x) f.p = naN f bv :=
    g_copy f.p _ _ _ (by omega) f_mb f_nb_r (by rw [hrtop]; exact hnb_val) eq_mb_plain_11
  -- datapath for finite nonzero operands
  have hdp : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      f_ovf 0 = decide (ovfN f av bv) ∧ XF.val (fun x => f_mag x) (f.w + f.t) = magN f av bv := by
    intro hns
    obtain ⟨hfa, hfb⟩ := fin_ops f av bv hns
    clear hns
    obtain ⟨_, -, -, -, -, hna_lo, hna_hi⟩ := norm_facts f av hfa.2 hfa.1
    obtain ⟨_, -, -, -, -, hnb_lo, hnb_hi⟩ := norm_facts f bv hfb.2 hfb.1
    -- pre-aligned SRT core
    obtain ⟨hadj_c, hqm_c, hrnz_c⟩ := core f.p f.hp f_ma f_mb f_mbn f_d0 f_d1 f_adj f_r0 f_dv f_d2 f_nd1 f_nd2 f_zw
      f_xw f_da f_t2 f_t1 f_t0 f_tm f_ws f_wc f_u f_um f_rs f_ql f_qm f_rnz f_es f_yb f_g2 f_g1 f_g0 f_gm f_mm f_sm
      f_cy f_uq1 f_uq0 f_um1 f_um0 f_us f_ums (naN f av) (naN f bv) hma hmb hna_lo hna_hi hnb_lo hnb_hi
      eq_mbn_plain_12 eq_d0_plain_13 eq_d1_plain_14 eq_adj_plain_15 eq_r0_plain_16
      eq_dv_plain_22 eq_d2_plain_23 eq_nd1_plain_24 eq_nd2_plain_25 eq_zw_plain_26 eq_xw_plain_27 eq_da_plain_28
      eq_t2_plain_29 eq_t1_plain_30 eq_t0_plain_31 eq_tm_plain_32 eq_ws_plain_33 eq_wc_plain_34 eq_u_plain_35
      eq_um_plain_36 eq_rs_plain_37 eq_ql_plain_38 eq_qm_plain_39 eq_rnz_plain_40
      eq_es_srt_0 eq_yb_srt_1 eq_g2_srt_2 eq_g1_srt_3 eq_g0_srt_4 eq_gm_srt_5 eq_mm_srt_6 eq_sm_srt_7 eq_cy_srt_8
      eq_ws_srt_9 eq_wc_srt_10 eq_uq1_srt_11 eq_uq0_srt_12 eq_um1_srt_13 eq_um0_srt_14 eq_us_srt_15 eq_ums_srt_16
      eq_u_srt_17 eq_um_srt_18
    -- connect pre-aligned (adj, qm, rnz) to model (adjN, qmN, st0N) via quot_abs
    have hp_eq' : f.p = f.t + 1 := hp_eq f
    have hna_hi' : naN f av < 2 ^ (f.t + 1) := by rw [← hp_eq']; exact hna_hi
    have hnb_hi' : naN f bv < 2 ^ (f.t + 1) := by rw [← hp_eq']; exact hnb_hi
    have hp3 : f.p + 2 = f.t + 3 := by omega
    obtain ⟨adj, qm, M0, hadj_le, hadj_def, hqm_def, hM0, hqmM, hst, hq_lo, hq_hi, hadj0⟩ :=
      quot_abs f.t (naN f av) (naN f bv) (qqN f av bv) (rrN f av bv)
        (by unfold qqN; rw [hp3]) (by unfold rrN; rw [hp3]) hna_lo hna_hi' hnb_lo hnb_hi'
    have hadjN : adjN f av bv = adj := by unfold adjN; rw [hp_eq']; exact hadj_def
    have hqmN : qmN f av bv = qm := by unfold qmN; rw [hp_eq']; exact hqm_def
    have hstN : st0N f av bv ↔ M0 % naN f bv ≠ 0 := by unfold st0N; rw [hp_eq']; exact hst
    have hnb_pos : 0 < naN f bv := by have := Nat.two_pow_pos f.t; omega
    have hadj_val : adj = if naN f bv ≤ naN f av then 0 else 1 := by
      by_cases hc : naN f bv ≤ naN f av
      · rw [if_pos hc]; exact hadj0.2 hc
      · rw [if_neg hc]
        have : adj ≠ 0 := fun h0 => hc (hadj0.1 h0)
        omega
    have hM0_eq : M0 = 2 ^ f.p * (if naN f bv ≤ naN f av then naN f av - naN f bv else 2 * naN f av - naN f bv) +
        2 ^ f.p * naN f bv := by
      rw [hM0, ← hp_eq', hadj_val]
      by_cases hc : naN f bv ≤ naN f av
      · rw [if_pos hc, if_pos hc, Nat.add_zero, ← Nat.mul_add, Nat.sub_add_cancel hc]
      · rw [if_neg hc, if_neg hc, Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add]
        have h2a : naN f bv ≤ naN f av * 2 := by
          have : 2 ^ f.p = 2 * 2 ^ f.t := two_pow_t f
          omega
        rw [Nat.mul_comm 2 (naN f av), Nat.sub_add_cancel h2a]
    have b_adj : (f_adj 0).toNat = adjN f av bv := by rw [hadj_c, ← hadj_val, hadjN]
    have b_qm : XF.val (fun x => f_qm x) (f.p + 1) = qmN f av bv := by
      rw [hqm_c, hqmN, hqmM, hM0_eq, Nat.add_mul_div_right _ _ hnb_pos, Nat.add_comm]
    have b_rnz : f_rnz 0 = decide (st0N f av bv) := by
      rw [hrnz_c, decide_eq_decide, hstN, hM0_eq, Nat.add_mul_mod_self_right]
    have hqm_lt : qmN f av bv < 2 ^ (f.p + 1) := by
      rw [hqmN]
      have : 2 ^ (f.p + 1) = 4 * 2 ^ f.t := by rw [hp_eq', show f.t + 1 + 1 = f.t + 2 by omega, Nat.pow_add]; omega
      omega
    -- exponent
    have b_emw := g_emw f _ (by omega) f_emw f_onesW eq_onesW_plain_17 eq_emw_plain_18
    have hEWe : ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 = f.w + f.p + 1 := by omega
    have b_E := g_E _ _ (ZN f) _ _ (yaN f av) (yaN f bv) f.emax (adjN f av bv) f_E f_ya_r f_yb_r f_emw f_adj
      (by unfold ZN; congr 1 <;> omega) (by omega) (by omega)
      (by rw [hEWe, hrtopE]; exact hya_val) (by rw [hEWe, hrtopE]; exact hyb_val) b_emw b_adj eq_E_plain_19
    have hEVp : XF.val (fun x => f_E x) _ = EN f av bv := b_E
    have hEV : XF.val (fun x => f_E x) (f.w + f.p + 1) = EN f av bv := by
      rw [← hEWe]; exact b_E
    have b_ovf : f_ovf 0 = decide (ovfE f (EN f av bv)) :=
      g_ovf f (EN f av bv) _ _ _ f_ovf f_E (by omega) (by omega) (by omega) hEV eq_ovf_plain_20
    have b_dsh := g_dsh f (EN f av bv) _ _ f_dsh f_E (by omega) (by omega) hEVp eq_dsh_plain_21
    have hDshV : XF.val (fun x => f_dsh x) (f.w + f.p + 1) = dshE f (EN f av bv) := by
      rw [← hEWe]; exact b_dsh
    -- clamped denormalizer + rounding
    have hcl_toNat : ((f.p : Int) + 2).toNat = f.p + 2 := by omega
    have hcl_lo : 1 ≤ clog2 (f.p + 2) := by
      have h := le_two_pow_clog2 (f.p + 2)
      cases hc : clog2 (f.p + 2) with
      | zero => rw [hc] at h; omega
      | succ _ => omega
    have hcl_hi : clog2 (f.p + 2) ≤ f.p + 2 := clog2_le (f.p + 2)
    have b_dsh_big : f_dsh_big 0 = decide (f.p + 1 ≤ dshE f (EN f av bv)) :=
      g_dsh_big f.p (f.w + f.p + 1) _ (dshE f (EN f av bv)) hEWe (by omega) f_dsh_big f_dsh hDshV eq_dsh_big_plain_41
    have b_dsh_c : dshE f (EN f av bv) < f.p + 1 →
        XF.val (fun x => f_dsh_c x) (clog2 (f.p + 2)) = dshE f (EN f av bv) := by
      intro hlt
      have hb : f_dsh_big 0 = false := by rw [b_dsh_big]; simp [show ¬ f.p + 1 ≤ dshE f (EN f av bv) by omega]
      exact g_dsh_c_lt f.p (f.w + f.p + 1) (clog2 (f.p + 2)) _ _ (dshE f (EN f av bv)) rfl
        (by rw [hcl_toNat]; omega) (by rw [hcl_toNat]; omega) (by omega) hlt f_dsh_c f_dsh_big f_dsh hb hDshV
        eq_dsh_c_plain_42
    have hzw_lo : ∀ k, k < f.p + 1 → f_zw k = false := fun k hk => eq_zw_plain_26 k (by omega)
    have b_qs : XF.val (fun x => f_qs x) (f.p + 1) = qsN f av bv :=
      g_qs_clamped f.p (clog2 (f.p + 2)) _ (qmN f av bv) (dshE f (EN f av bv)) (by rw [hcl_toNat]; omega) hqm_lt
        f_qs f_dsh_big f_zw f_qm f_dsh_c b_dsh_big hzw_lo b_qm b_dsh_c eq_qs_plain_43
    have b_inc : f_inc 0 = decide (incN f av bv) := by
      have h := g_inc_clamped f.p (clog2 (f.p + 2)) _ (qsN f av bv) (qmN f av bv) (dshE f (EN f av bv))
        (st0N f av bv) (by rw [hcl_toNat]; omega) (by omega) f_qs f_qm f_dsh_c f_rnz f_inc b_qs b_qm b_rnz
        rfl hqm_lt b_dsh_c eq_inc_plain_44
      rw [h]
      exact decide_eq_decide.2 Iff.rfl
    have b_ef : XF.val (fun x => f_ef x) f.w = efN f av bv :=
      g_ef f (EN f av bv) _ _ _ _ f_ef f_E (by omega) (by omega) (by omega) (by omega) hEVp eq_ef_plain_45
    have hinc : (f_inc 0).toNat = if incN f av bv then 1 else 0 := by
      rw [b_inc]
      by_cases h : incN f av bv <;> simp [h]
    have b_mag := g_mag f.t f.w _ _ _ f.p (qsN f av bv) (efN f av bv) (if incN f av bv then 1 else 0)
      (by omega) (by omega) (by omega) (by omega) (by omega) f_mag f_qs f_ef f_inc b_qs b_ef hinc
      eq_mag_plain_46
    rw [show ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 = f.w + f.t by omega] at b_mag
    refine ⟨?_, b_mag⟩
    rw [b_ovf]
    exact decide_eq_decide.2 Iff.rfl
  -- output
  have hfield := g_qfield _ _ _ f.w (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) f_q f_onesW f_mag (by omega)
    (by omega) eq_onesW_plain_17 eq_q_plain_48
  have hout := g_out _ _ f.w _ (f.w + f.p) (by omega) (by omega) (by omega) _ (by omega)
    (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_q f_mag _ eq_q_plain_47 hfield eq_q_plain_49
    eq_q_lo_0
  rw [hout]
  exact g_final f av bv (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_mag _ _ _ (by omega)
    (by omega) b_cn b_ci b_cz b_s hdp rfl rfl

end Glue
end SvGolf.FdivParam

end SrG2


namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

private theorem clog2_pos_of_two_le (n : Nat) (hn : 2 ≤ n) : 1 ≤ clog2 n := by
  have h := le_two_pow_clog2 n
  cases hc : clog2 n with
  | zero => rw [hc] at h; omega
  | succ _ => omega

set_option maxHeartbeats 1200000 in
theorem fdiv_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20) :
    CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
  have htd : (P : Int).tdiv 2 = (P : Int) / 2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hcl_lo : 1 ≤ clog2 ((P : Int) + 2).toNat := by
    rw [show ((P : Int) + 2).toNat = P + 2 by omega]; exact clog2_pos_of_two_le (P + 2) (by omega)
  have hcl_hi : clog2 ((P : Int) + 2).toNat ≤ P + 2 := by
    rw [show ((P : Int) + 2).toNat = P + 2 by omega]; exact clog2_le (P + 2)
  have hs : CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
    sv_structure (rank := rippleRank
        (fun p =>
          if p ≤ 2 then 0
          else if p ≤ 9 then 1
          else if p ≤ 11 then P + 1
          else if p ≤ 14 then P + 2
          else if p = 15 then P + 3
          else if p = 16 then P + 4
          else if p = 17 then 0
          else if p = 18 then 1
          else if p = 19 then P + 4
          else if p ≤ 21 then P + 5
          else if p ≤ 23 then P + 2
          else if p ≤ 25 then P + 3
          else if p = 26 then 0
          else if p = 27 then P + 5
          else if p = 28 then P + 3
          else if p ≤ 32 then P + 4
          else if p = 33 then P + 6
          else if p ≤ 36 then 0
          else if p = 37 then 11 * P + 50
          else if p = 38 then 11 * P + 51
          else if p ≤ 40 then 11 * P + 52
          else if p = 41 then P + 6
          else if p = 42 then P + 7
          else if p = 43 then 11 * P + 53
          else if p = 44 then 11 * P + 54
          else if p = 45 then P + 5
          else if p = 46 then 11 * P + 55
          else if p = 47 then 2
          else 11 * P + 56)
        (fun blk p i =>
          if blk = "norm" then 2 + i.toNat
          else if blk = "srt" then P + 7 + 19 * i.toNat + p
          else 11 * P + 56))
    all_goals (intros; sv_rowmajor; omega)
  exact hs

theorem fdiv_interface (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20)
    (hc : CombDesign (design.sem W P)) :
    (SvGolf.Tasks.FdivP.task W P).Interface 0 (design.sem W P) := by
  unfold SvGolf.Tasks.FdivP.task
  sv_interface

set_option maxHeartbeats 1500000 in
theorem solution : Goal := by
  intro W P hWP
  obtain ⟨hW, hP, hR⟩ := hWP
  obtain ⟨hc, ha, hso⟩ := fdiv_struct W P hW hP hR
  refine CombTask.satisfiedAt_of_comb (fdiv_interface W P hW hP hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨a, b, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.FdivP.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hav, hbv⟩ := hv
  have htd : (P : Int).tdiv 2 = (P : Int) / 2 := Int.tdiv_eq_ediv_of_nonneg (by omega)
  have hcl_lo : 1 ≤ clog2 ((P : Int) + 2).toNat := by
    rw [show ((P : Int) + 2).toNat = P + 2 by omega]; exact clog2_pos_of_two_le (P + 2) (by omega)
  have hcl_hi : clog2 ((P : Int) + 2).toNat ≤ P + 2 := by
    rw [show ((P : Int) + 2).toNat = P + 2 by omega]; exact clog2_le (P + 2)
  sv_equations
  · have ha' : ∀ k, k < W + P → st.boolAt "a" k = a.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hav hk]; rfl
    have hb' : ∀ k, k < W + P → st.boolAt "b" k = b.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hbv hk]; rfl
    have hch := SvGolf.FdivParam.Glue.chain ⟨W, P, hW, hP⟩ hR (st.boolAt "s") (st.boolAt "ea_nz") (st.boolAt "eb_nz")
      (st.boolAt "c_nan") (st.boolAt "c_inf") (st.boolAt "c_zero") (st.boolAt "na_r") (st.boolAt "nb_r")
      (st.boolAt "ya_r") (st.boolAt "yb_r") (st.boolAt "ma") (st.boolAt "mb") (st.boolAt "mbn")
      (st.boolAt "d0") (st.boolAt "d1") (st.boolAt "adj") (st.boolAt "r0") (st.boolAt "onesW") (st.boolAt "emw")
      (st.boolAt "E") (st.boolAt "ovf") (st.boolAt "dsh") (st.boolAt "dv") (st.boolAt "d2") (st.boolAt "nd1")
      (st.boolAt "nd2") (st.boolAt "zw") (st.boolAt "xw") (st.boolAt "da") (st.boolAt "t2") (st.boolAt "t1")
      (st.boolAt "t0") (st.boolAt "tm") (st.boolAt "ws") (st.boolAt "wc") (st.boolAt "u") (st.boolAt "um")
      (st.boolAt "rs") (st.boolAt "ql") (st.boolAt "qm") (st.boolAt "rnz") (st.boolAt "dsh_big") (st.boolAt "dsh_c")
      (st.boolAt "qs") (st.boolAt "inc") (st.boolAt "ef") (st.boolAt "mag") (st.boolAt "q") (st.boolAt "es")
      (st.boolAt "yb") (st.boolAt "g2") (st.boolAt "g1") (st.boolAt "g0") (st.boolAt "gm") (st.boolAt "mm")
      (st.boolAt "sm") (st.boolAt "cy") (st.boolAt "uq1") (st.boolAt "uq0") (st.boolAt "um1") (st.boolAt "um0")
      (st.boolAt "us") (st.boolAt "ums") (st.boolAt "a") (st.boolAt "b") a.toNat b.toNat ha' hb' eq_s_plain_0 eq_ea_nz_plain_1 eq_eb_nz_plain_2 eq_c_nan_plain_3 eq_c_inf_plain_4 eq_c_zero_plain_5 eq_na_r_plain_6 eq_nb_r_plain_7 eq_ya_r_plain_8 eq_yb_r_plain_9 eq_ma_plain_10 eq_mb_plain_11 eq_mbn_plain_12 eq_d0_plain_13 eq_d1_plain_14 eq_adj_plain_15 eq_r0_plain_16 eq_onesW_plain_17 eq_emw_plain_18 eq_E_plain_19 eq_ovf_plain_20 eq_dsh_plain_21 eq_dv_plain_22 eq_d2_plain_23 eq_nd1_plain_24 eq_nd2_plain_25 eq_zw_plain_26 eq_xw_plain_27 eq_da_plain_28 eq_t2_plain_29 eq_t1_plain_30 eq_t0_plain_31 eq_tm_plain_32 eq_ws_plain_33 eq_wc_plain_34 eq_u_plain_35 eq_um_plain_36 eq_rs_plain_37 eq_ql_plain_38 eq_qm_plain_39 eq_rnz_plain_40 eq_dsh_big_plain_41 eq_dsh_c_plain_42 eq_qs_plain_43 eq_inc_plain_44 eq_ef_plain_45 eq_mag_plain_46 eq_q_plain_47 eq_q_plain_48 eq_q_plain_49 eq_na_r_norm_0 eq_nb_r_norm_1 eq_ya_r_norm_2 eq_yb_r_norm_3 eq_es_srt_0 eq_yb_srt_1 eq_g2_srt_2 eq_g1_srt_3 eq_g0_srt_4 eq_gm_srt_5 eq_mm_srt_6 eq_sm_srt_7 eq_cy_srt_8 eq_ws_srt_9 eq_wc_srt_10 eq_uq1_srt_11 eq_uq0_srt_12 eq_um1_srt_13 eq_um0_srt_14 eq_us_srt_15 eq_ums_srt_16 eq_u_srt_17 eq_um_srt_18 eq_q_lo_0
    have hval : XF.val (st.boolAt "q") (W + P) = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat :=
      hch.trans (SvGolf.FdivParam.OutN_fdivBits W P ⟨hW, hP⟩ a b)
    have hkq : ∀ k, k < W + P → KnownBit st "q" k := by
      intro k hk
      by_cases h1 : k = W + P - 1
      · have := known_q_plain_47.2
        rwa [show ((W : Int) + (P : Int) + -1).toNat = k by omega] at this
      · by_cases h2 : P - 1 ≤ k
        · have := (known_q_plain_48 (k - (P - 1)) (by omega)).2
          rwa [show ((P : Int) - 1).toNat + (k - (P - 1)) = k by omega] at this
        · by_cases h3 : k = P - 2
          · have := known_q_plain_49.2
            rwa [show ((P : Int) - 1 + -1).toNat = k by omega] at this
          · exact (known_q_lo_0 k (by omega)).2
    obtain ⟨vs, hvs, hvsw⟩ := known_q_plain_47.1
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
    | (intros; refine ⟨?_, ?_, ?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover))
    | skip

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
