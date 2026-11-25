import Submission.Design
import SvGolf.Comb
import LeanModels.SoftFloat.Binary
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib

/-!
# Reference solution for task `fdivp`: IEEE 754 division, PARAMETRIC in the format, for every `W >= 2`, `P >= 2`

A submission like any player's `Solution.lean`: the checker generates `Submission.Design` (`Submission.design`,
`Submission.Goal`) and this file proves `theorem Submission.solution : Submission.Goal`, i.e. for every `W, P >= 2` the
design `fdiv #(W, P)` has the ports `a`, `b`, `q` (`W + P` bits) and `q = fdivBits W P a b` for every pair of operands
(`LeanModels.SoftFloat.Binary.divide ⟨W, P⟩ .nearestTiesToEven`: IEEE 754 division as Proglib's library defines it). The design is `reference/fdivp.sv` (D3: a word-level
netlist of 34 sites, a linear one-bit normalizer, `P + 2` restoring steps as generate families, a two's complement
exponent, a run-time shifter with a sticky bit, round to nearest even by an increment into `{exponent, fraction}`).
binary16 is the instance `(W, P) = (5, 11)` (the task's scoring point).

Besides the generated design module and the framework, it imports the general ls-sv proof library `LeanModels.Sv.Lib`
(`Nat` arithmetic, the `Nat` values of the word-level bit helpers, row-major offsets, restoring division) and
Proglib's IEEE 754 binary-format library `LeanModels.SoftFloat.Binary`, which the statement is written in (rounding, the
multiplication-and-comparison certificate `certF_bridge`, the rounding stage `fin_cert_abs`, for every format). This datapath is proved here, in sections:

1. `DpN` .. `DpU`: the math layer, the datapath as a `Nat` model and `OutN_fdivBits` (its output is the task function,
   for every format).
2. `DpG1` .. `DpG5`: the glue, from the printed equations of `sv_equations` to the model (`Glue.chain`).
3. `Submission`: the proof.

Each section was a module of the task before the proof was folded into this file (its heading says which); the section
docs keep the module names (`DpN.lean` is the section `DpN`, and so on).

## Route

1. `fdiv_struct` / `fdiv_interface`: `sv_structure` (with the rank of the design: the 24 plain sites by depth, the
   families `norm` and `div` by their stage) and `sv_interface` (the task is unfolded first: `task W P` is an application,
   which the tactic's own unfolding of a constant task does not read).
2. `solution`: `CombTask.satisfiedAt_of_comb` reduces to one settled-state lemma; `sv_equations` hands over the 34
   equations of the netlist as `eq_<signal>_<kind>_<k>`; the whole arithmetic is `SvGolf.FdivParam.Glue.chain`
   (section `DpG5`): the equations, as printed, with the two operands as numbers, give `XF.val q (W + P) = OutN f a b`, and
   `SvGolf.FdivParam.OutN_fdivBits` (section `DpU`, the math layer, proved for every format) identifies that with the task
   function. The residual obligations of the tactic (`inRange`, `width`, `bitRead`, `cover`) are closed by `omega`,
   `split`, and `sv_cover` (the five family covers of the `norm` and `div` rows are conjunctions: split first).
3. The heartbeat limits are those of the WP-LIN tactics (`ac01d4df`, grouped obligations): 239 thousand for
   `sv_structure` and 388 thousand for the whole `solution` (measured, `design/fdiv-param/H3-G2-NOTE.md`); without WP-LIN the
   same two cost 895 thousand and 2.38 million. Every other option is scoped to its section or to one
   declaration (`set_option … in`).
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
open LeanModels.SoftFloat.Binary

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

/-! # Section `DpG5`: Glue: the chain (was `tasks/fdivp/DpG5.lean`) -/

section DpG5

set_option maxRecDepth 100000

/-!
# Task `fdivp`: the chain, from the printed equations of `sv_equations` to the value of `q`

WP-H3 design layer, continued (`DpG4.lean`). `chain` takes the 34 equations of the netlist `fdivp3.sv` exactly as
`sv_equations` states them (the signal `x` is the bit function `f_x`, `st.boolAt "x"` in the solution) and the two
operands as numbers, and concludes `XF.val q (W + P) = OutN f a b`, the value of the model of `DpQ.lean`, which
`OutN_fdivBits` identifies with the task function. Widths are `f.w`, `f.p` of a format `f`, which at the use site is
`⟨W, P, hW, hP⟩` (the projections reduce).
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

set_option maxHeartbeats 4000000 in
theorem chain (f : Format)
    (f_s f_ea_nz f_eb_nz f_c_nan f_c_inf f_c_zero f_na_r f_nb_r f_ya_r f_yb_r f_nbx f_rr f_adj f_qm f_onesW f_emw
      f_E f_ovf f_dsh f_qs f_inc f_ef f_mag f_q f_qq f_dd f_a f_b : Nat → Bool)
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
    (eq_nbx_plain_10 : ∀ (k : Nat), k < f.p + 1 → f_nbx k = if k < f.p then f_nb_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k) else false)
    (eq_rr_plain_11 : ∀ (k : Nat), k < f.p + 1 → f_rr k = if k < f.p then f_na_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k) else false)
    (eq_adj_plain_12 : f_adj 0 = !f_qq (f.p + 1))
    (eq_qm_plain_13 : ∀ (k : Nat), k < f.p + 1 → f_qm k = if f_qq (f.p + 1) = true then f_qq (Int.toNat 1 + k) else f_qq k)
    (eq_onesW_plain_14 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_onesW k = true)
    (eq_emw_plain_15 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_emw k = XF.shrBits (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_E_plain_16 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_E k = XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.addBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + x)) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + -1).natAbs + 1) (fun k => f_emw k) x) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_adj k) x) k)
    (eq_ovf_plain_17 : f_ovf 0 = (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && ((XF.any ((f.w : Int) + (f.p : Int) + 1 + -2 - (f.w : Int) + 1).toNat fun x => f_E (f.w + x)) || XF.all ((f.w : Int) + -1 + 1).toNat fun x => f_E x)))
    (eq_dsh_plain_18 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_dsh k = if max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)) < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) k else XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.constBit 1 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) k else XF.zext (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.constBit 0 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x else XF.subBits (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.constBit 1 (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) x) (max 32 (max 32 (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))) (fun x => XF.zext (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_E x) x) x) k)
    (eq_qs_plain_19 : ∀ (k : Nat), k < f.p + 1 → f_qs k = XF.shrBits (f.p + 1) (fun x => f_qm x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_dsh x) k)
    (eq_inc_plain_20 : f_inc 0 = (f_qs 0 && (((f_qq (f.p + 1) && f_qq 0 || XF.any (f.p + 1) fun x => f_rr (rmN ((f.p : Int) + 1) ((f.p : Int) + 2) 0 + x)) || !XF.eqv (f.p + 1) (fun x => XF.shlBits (XF.zext (f.p + 1) fun x => f_qs x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_dsh x) x) fun x => f_qm x) || f_qs (Int.toNat 1))))
    (eq_ef_plain_21 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_ef k = if max ((f.w : Int) + -1 + 1).toNat 32 < ((f.w : Int) + -1).natAbs + 1 then if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) k else XF.constBit 0 (((f.w : Int) + -1).natAbs + 1) k else XF.zext (max ((f.w : Int) + -1 + 1).toNat 32) (fun x => if (!f_E ((f.w : Int) + (f.p : Int) + 1 + -1).toNat && XF.any (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) fun x => f_E x) = true then XF.zext ((f.w : Int) + -1 + 1).toNat (fun x => f_E x) x else XF.constBit 0 (max ((f.w : Int) + -1 + 1).toNat 32) x) k)
    (eq_mag_plain_22 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 → f_mag k = XF.addBits (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => if x < ((f.p : Int) + -1).toNat then f_qs (Int.toNat 1 + x) else f_ef (x - ((f.p : Int) + -1).toNat)) (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => XF.zext 1 (fun k => f_inc k) x) k)
    (eq_q_plain_23 : f_q ((f.w : Int) + (f.p : Int) + -1).toNat = (!f_c_nan 0 && f_s 0))
    (eq_q_plain_24 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat → f_q (((f.p : Int) - 1).toNat + k) = if max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat) < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat then if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) k else if f_c_zero 0 = true then XF.constBit 0 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat k else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) k else XF.zext (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) (fun x => if (f_c_nan 0 || f_c_inf 0 || !f_c_zero 0 && f_ovf 0) = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_onesW x) x else if f_c_zero 0 = true then XF.constBit 0 (max (((f.w : Int) + -1).natAbs + 1) (max 32 ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat)) x else XF.zext ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat (fun k => f_mag (((f.p : Int) - 1).toNat + k)) x) k)
    (eq_q_plain_25 : f_q ((f.p : Int) - 1 + -1).toNat = (f_c_nan 0 || !(f_c_nan 0 || f_c_inf 0 || f_c_zero 0 || f_ovf 0) && f_mag ((f.p : Int) - 1 + -1).toNat))
    (eq_na_r_norm_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_na_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_nb_r_norm_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_nb_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + k) else XF.shlBits (XF.zext f.p fun x => f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_ya_r_norm_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_yb_r_norm_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => if f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)) = true then XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x else XF.subBits (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) (fun x => XF.constBit 1 (max ((f.w : Int) + (f.p : Int) + 1).toNat (max ((f.w : Int) + (f.p : Int) + 1).toNat 32)) x) x) k)
    (eq_qq_div_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → f_qq ((f.p : Int) + -1 * (i : Int) + 1).toNat = decide (XF.val (fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) (f.p + 1) ≥ XF.val (fun x => f_nbx x) (f.p + 1)))
    (eq_dd_div_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → ∀ (k : Nat), k < f.p + 1 → f_dd (rmN ((f.p : Int) + 1) ((i : Int)) 0 + k) = XF.subBits (f.p + 1) (fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) (f.p + 1) (fun x => f_nbx x) k)
    (eq_rr_div_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → ∀ (k : Nat), k < f.p + 1 → f_rr (rmN ((f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if f_qq ((f.p : Int) + -1 * (i : Int) + 1).toNat = true then XF.shlBits (XF.zext (f.p + 1) fun x => f_dd (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k else XF.shlBits (XF.zext (f.p + 1) fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_q_lo_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) - 1 + -1 → f_q i = (!(f_c_nan 0 || f_c_inf 0 || f_c_zero 0 || f_ovf 0) && f_mag i))
    : XF.val (fun x => f_q x) (f.w + f.p) = OutN f av bv := by
  have hfw := f.hw
  have hfp := f.hp
  -- the operand classes, while the context is still small (PROVING.md §11, the omega rule)
  have hfin : ∀ x, ¬ (nanN f x ∨ infN f x ∨ zeroN f x) → eF f x ≠ 2 ^ f.w - 1 ∧ ¬ (eF f x = 0 ∧ fF f x = 0) := by
    intro x hx
    unfold nanN infN zeroN at hx
    omega
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
  have hrtop2 : rmN ((f.p : Int) + 1) ((f.p : Int) + 2) 0 = (f.p + 2) * (f.p + 1) :=
    rmN_eq _ _ _ (f.p + 1) (f.p + 2) 0 (by omega) (by omega) (by omega)
  -- the extensions of the normalized operands
  have hnbx : XF.val (fun x => f_nbx x) (f.p + 1) = naN f bv :=
    g_ext f.p _ _ f_nbx f_nb_r (by rw [hrtop]; exact hnb_val) eq_nbx_plain_10
  have hr0 : XF.val (fun x => f_rr x) (f.p + 1) = naN f av :=
    g_ext f.p _ _ f_rr f_na_r (by rw [hrtop]; exact hna_val) eq_rr_plain_11
  -- the datapath, for finite nonzero operands
  have hdp : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      f_ovf 0 = decide (ovfN f av bv) ∧ XF.val (fun x => f_mag x) (f.w + f.t) = magN f av bv := by
    intro hns
    have hfa := hfin av fun h => hns (by
      rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hfb := hfin bv fun h => hns (by
      rcases h with h | h | h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h)))
    obtain ⟨la, hla, hna_def, hya_lt, hya_l, hna_lo, hna_hi⟩ := norm_facts f av hfa.2 hfa.1
    obtain ⟨lb, hlb, hnb_def, hyb_lt, hyb_l, hnb_lo, hnb_hi⟩ := norm_facts f bv hfb.2 hfb.1
    -- the case-split facts are consumed: every `omega` below would split on them (PROVING.md §11, the omega rule)
    clear hns hfa hfb hya_l hyb_l
    have hp2 : 2 ^ f.p = 2 * 2 ^ f.t := two_pow_t f
    have hnb0 : 0 < naN f bv := by have := Nat.two_pow_pos f.t; omega
    have hnalt : naN f av < 2 * naN f bv := by omega
    have hdiv := div_rows f.p f_rr f_dd f_qq f_nbx (naN f av) (naN f bv) f.hp hnb0 hnb_hi hnalt hnbx hr0
      eq_qq_div_0 eq_dd_div_1 eq_rr_div_2
    obtain ⟨hrowsd, hqqval⟩ := hdiv
    have hqq : XF.val (fun x => f_qq x) (f.p + 2) = qqN f av bv := hqqval
    have hrr_top := hrowsd (f.p + 2) (Nat.le_refl _)
    have hqq_lt : qqN f av bv < 2 ^ (f.p + 2) := by
      have hl := XF.val_lt f_qq (f.p + 2)
      rw [hqq] at hl
      exact hl
    have hp21 : 2 ^ (f.p + 2) = 2 * 2 ^ (f.p + 1) := Nat.pow_succ' (n := f.p + 1)
    have hqm_lt : qmN f av bv < 2 ^ (f.p + 1) := by
      unfold qmN
      split <;> omega
    -- quotient normalization
    have b_adj : (f_adj 0).toNat = adjN f av bv := g_adj f.p (qqN f av bv) f_adj f_qq hqq eq_adj_plain_12
    have b_qm : XF.val (fun x => f_qm x) (f.p + 1) = qmN f av bv :=
      g_qm f.p _ (qqN f av bv) (by omega) f_qm f_qq hqq eq_qm_plain_13
    -- the exponent
    have b_emw := g_emw f _ (by omega) f_emw f_onesW eq_onesW_plain_14 eq_emw_plain_15
    have hEWe : ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 = f.w + f.p + 1 := by omega
    have b_E := g_E _ _ (ZN f) _ _ (yaN f av) (yaN f bv) f.emax (adjN f av bv) f_E f_ya_r f_yb_r f_emw f_adj
      (by unfold ZN; congr 1 <;> omega) (by omega) (by omega)
      (by rw [hEWe, hrtopE]; exact hya_val) (by rw [hEWe, hrtopE]; exact hyb_val) b_emw b_adj eq_E_plain_16
    have hEVp : XF.val (fun x => f_E x) _ = EN f av bv := b_E
    have hEV : XF.val (fun x => f_E x) (f.w + f.p + 1) = EN f av bv := by
      rw [← hEWe]; exact b_E
    have b_ovf : f_ovf 0 = decide (ovfE f (EN f av bv)) :=
      g_ovf f (EN f av bv) _ _ _ f_ovf f_E (by omega) (by omega) (by omega) hEV eq_ovf_plain_17
    have b_dsh := g_dsh f (EN f av bv) _ _ f_dsh f_E (by omega) (by omega) hEVp eq_dsh_plain_18
    have b_qs : XF.val (fun x => f_qs x) (f.p + 1) = qsN f av bv :=
      g_qs f.p _ (qmN f av bv) (dshE f (EN f av bv)) f_qs f_qm f_dsh b_qm b_dsh eq_qs_plain_19
    have b_inc : f_inc 0 = decide (incN f av bv) := by
      have h := g_inc f.p _ _ (qsN f av bv) (qmN f av bv) (qqN f av bv) (rrN f av bv) (dshE f (EN f av bv)) _
        (by omega) (by omega) f_qs f_qm f_dsh f_qq f_rr f_inc b_qs b_qm b_dsh hqq (by rw [hrtop2]; exact hrr_top) rfl hqm_lt
        eq_inc_plain_20
      rw [h]
      exact decide_eq_decide.2 Iff.rfl
    have b_ef : XF.val (fun x => f_ef x) f.w = efN f av bv :=
      g_ef f (EN f av bv) _ _ _ _ f_ef f_E (by omega) (by omega) (by omega) (by omega) hEVp eq_ef_plain_21
    have hinc : (f_inc 0).toNat = if incN f av bv then 1 else 0 := by
      rw [b_inc]
      by_cases h : incN f av bv <;> simp [h]
    have b_mag := g_mag f.t f.w _ _ _ f.p (qsN f av bv) (efN f av bv) (if incN f av bv then 1 else 0)
      (by omega) (by omega) (by omega) (by omega) (by omega) f_mag f_qs f_ef f_inc b_qs b_ef hinc
      eq_mag_plain_22
    have hMe : ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 = f.w + f.t := by omega
    rw [hMe] at b_mag
    refine ⟨?_, b_mag⟩
    rw [b_ovf]
    exact decide_eq_decide.2 Iff.rfl
  -- the output
  have hfield := g_qfield _ _ _ f.w (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) f_q f_onesW f_mag (by omega)
    (by omega) eq_onesW_plain_14 eq_q_plain_24
  have hout := g_out _ _ f.w _ (f.w + f.p) (by omega) (by omega) (by omega) _ (by omega)
    (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_q f_mag _ eq_q_plain_23 hfield eq_q_plain_25
    eq_q_lo_0
  rw [hout]
  exact g_final f av bv (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ f_mag _ _ _ (by omega)
    (by omega) b_cn b_ci b_cz b_s hdp rfl rfl

end Glue
end SvGolf.FdivParam

end DpG5

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

set_option maxHeartbeats 300000 in
theorem fdiv_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20) :
    CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
  sv_structure (rank := rippleRank
      (fun p =>
        if p ≤ 2 then 0 else if p ≤ 9 then 1 else if p ≤ 11 then P + 1 else if p ≤ 13 then 3 * P + 6
        else if p = 14 then 0 else if p = 15 then 1 else if p = 16 then 3 * P + 7
        else if p ≤ 18 then 3 * P + 8 else if p = 19 then 3 * P + 9 else if p = 20 then 3 * P + 10
        else if p = 21 then 3 * P + 8 else if p = 22 then 3 * P + 11 else if p = 23 then 2
        else 3 * P + 12)
      (fun blk p i =>
        if blk = "norm" then 2 + i.toNat
        else if blk = "div" then (if p = 2 then P + 3 + 2 * i.toNat else P + 2 + 2 * i.toNat)
        else 3 * P + 12))
  all_goals (intros; sv_rowmajor; omega)

theorem fdiv_interface (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20)
    (hc : CombDesign (design.sem W P)) :
    (SvGolf.Tasks.FdivP.task W P).Interface 0 (design.sem W P) := by
  unfold SvGolf.Tasks.FdivP.task
  sv_interface

set_option maxHeartbeats 500000 in
theorem solution : Goal := by
  intro W P hWP
  obtain ⟨hW, hP, hR⟩ := hWP
  obtain ⟨hc, ha, hso⟩ := fdiv_struct W P hW hP hR
  refine CombTask.satisfiedAt_of_comb (fdiv_interface W P hW hP hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨a, b, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.FdivP.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hav, hbv⟩ := hv
  sv_equations
  · have ha' : ∀ k, k < W + P → st.boolAt "a" k = a.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hav hk]; rfl
    have hb' : ∀ k, k < W + P → st.boolAt "b" k = b.toNat.testBit k := fun k hk => by
      rw [SvState.boolAt_ofBitVec hbv hk]; rfl
    have hch := SvGolf.FdivParam.Glue.chain ⟨W, P, hW, hP⟩ (st.boolAt "s") (st.boolAt "ea_nz") (st.boolAt "eb_nz")
      (st.boolAt "c_nan") (st.boolAt "c_inf") (st.boolAt "c_zero") (st.boolAt "na_r") (st.boolAt "nb_r")
      (st.boolAt "ya_r") (st.boolAt "yb_r") (st.boolAt "nbx") (st.boolAt "rr") (st.boolAt "adj") (st.boolAt "qm")
      (st.boolAt "onesW") (st.boolAt "emw") (st.boolAt "E") (st.boolAt "ovf") (st.boolAt "dsh") (st.boolAt "qs")
      (st.boolAt "inc") (st.boolAt "ef") (st.boolAt "mag") (st.boolAt "q") (st.boolAt "qq") (st.boolAt "dd")
      (st.boolAt "a") (st.boolAt "b") a.toNat b.toNat ha' hb'
      eq_s_plain_0 eq_ea_nz_plain_1 eq_eb_nz_plain_2 eq_c_nan_plain_3 eq_c_inf_plain_4 eq_c_zero_plain_5
      eq_na_r_plain_6 eq_nb_r_plain_7 eq_ya_r_plain_8 eq_yb_r_plain_9 eq_nbx_plain_10 eq_rr_plain_11
      eq_adj_plain_12 eq_qm_plain_13 eq_onesW_plain_14 eq_emw_plain_15 eq_E_plain_16 eq_ovf_plain_17
      eq_dsh_plain_18 eq_qs_plain_19 eq_inc_plain_20 eq_ef_plain_21 eq_mag_plain_22 eq_q_plain_23
      eq_q_plain_24 eq_q_plain_25 eq_na_r_norm_0 eq_nb_r_norm_1 eq_ya_r_norm_2 eq_yb_r_norm_3
      eq_qq_div_0 eq_dd_div_1 eq_rr_div_2 eq_q_lo_0
    have hval : XF.val (st.boolAt "q") (W + P) = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat :=
      hch.trans (SvGolf.FdivParam.OutN_fdivBits W P ⟨hW, hP⟩ a b)
    have hkq : ∀ k, k < W + P → KnownBit st "q" k := by
      intro k hk
      by_cases h1 : k = W + P - 1
      · have := known_q_plain_23.2
        rwa [show ((W : Int) + (P : Int) + -1).toNat = k by omega] at this
      · by_cases h2 : P - 1 ≤ k
        · have := (known_q_plain_24 (k - (P - 1)) (by omega)).2
          rwa [show ((P : Int) - 1).toNat + (k - (P - 1)) = k by omega] at this
        · by_cases h3 : k = P - 2
          · have := known_q_plain_25.2
            rwa [show ((P : Int) - 1 + -1).toNat = k by omega] at this
          · exact (known_q_lo_0 k (by omega)).2
    obtain ⟨vs, hvs, hvsw⟩ := known_q_plain_23.1
    have hq := SvState.lookup_eq_ofBitVec_bv (W := W + P) hvs (by omega) hkq
    have hbq : XF.bv (W + P) (st.boolAt "q") = SvGolf.Tasks.FdivP.fdivBits W P a b := by
      apply BitVec.eq_of_toNat_eq
      rw [XF.toNat_bv, hval]
    rw [hvs, hq, hbq]
  case inputsKnown_1 => exact inKnown_ofBitVec hav (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hbv (by omega)
  all_goals first | (intros; omega) | sv_cover | (intros; split <;> omega) | (intros; refine ⟨?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover)) | (intros; refine ⟨?_, ?_, ?_⟩ <;> first | sv_cover | (intro k hk; sv_cover)) | skip

-- (no `#print axioms` pin: check.py's comparator checks the solution's axioms against the task's allowed set)

end Submission
