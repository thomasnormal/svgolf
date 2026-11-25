-- MAINTAINER PORT (2026-11-16): the svGolf maintainers' port of the player's proof to the checker at Proglib 4fcda4c8 (Lean v4.35.0); the design is the player's, byte for byte, and the player's own proof is in the record this one replaces (the repository's history). The lines below say what changed versus the player's file.
-- pin2 port: the tree's proof of this design against the library statement (tests/fdivp/baselines/fdivp_d2.lean, pin1 item D: float1's library-based proof), with the range premise (hR : W + P < 2 ^ 20) of the reduced range; replaces the player's proof of the former statement.
import Submission.Design
import SvGolf.Comb
import LeanModels.SoftFloat.Binary
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib

/-!
# A proof for the baseline `fdivp_d2.sv` of task `fdivp` (D2, the fragment-friendly divider), for every `W >= 2`, `P >= 2`

D2 computes the same function as the reference D3 (`reference/fdivp.sv`) by the same algorithm, with an offset exponent,
a linear denormalizer of `P + 1` one-bit stages and the output as a priority multiplexer over four words. The sections
`DpN` .. `DpU` (the `Nat` model `OutN` of the datapath and `OutN_fdivBits`; the facts about the spec and the rounding
certificate are Proglib's library `LeanModels.SoftFloat.Binary`, the statement's own) and the glue lemmas `normIter_succ'`, `div_rows`, `g_s`, `g_adj`, `g_qm` are copied verbatim from the
reference proof `reference/fdivp.lean`; the section `D2Glue` is the glue of this netlist: its printed equations give
`XF.val q (W + P) = OutN f a b`, the value of the reference's model.
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

end Glue
end SvGolf.FdivParam

end DpG3


/-! # Section `D2Glue`: the glue of the netlist `fdivp_d2.sv`, from its printed equations to `OutN` -/

section D2Glue

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
One lemma per shape of the printed equations of `fdivp_d2.sv` (the equation is the hypothesis `h`, its Int-typed widths
abstracted to `Nat` variables with side conditions), the denormalizer model `denIter` with its invariant, and `chain2`:
the 90 equations in, `XF.val q (W + P) = OutN f a b` out, where `OutN` is the reference's model of the datapath
(section `DpQ`). D2's exponent is offset by `H = 2^(W+P)`: `exp_off` shows it is the true exponent plus `H` exactly.
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

theorem g2_ewin (f : Format) (av n m : Nat) (fe fa : Nat → Bool) (hn : n = f.w) (hm : m = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k)
    (h : ∀ k, k < n → fe k = fa (m + k)) :
    XF.val (fun x => fe x) f.w = eF f av := by
  have hfp := f.hp
  subst hn hm
  rw [XF.val_congr_lt (fun j hj => h j hj),
    val_window_of_testBit fa av (f.p - 1) f.w (fun j hj => ha j (by omega))]
  try rfl

theorem g2_fwin (f : Format) (av n : Nat) (ff fa : Nat → Bool) (hn : n = f.p - 1)
    (ha : ∀ k, k < f.w + f.p → fa k = av.testBit k)
    (h : ∀ k, k < n → ff k = fa k) :
    XF.val (fun x => ff x) (f.p - 1) = fF f av := by
  have hfp := f.hp
  subst hn
  rw [XF.val_congr_lt (fun j hj => h j hj), val_of_testBit (w := f.p - 1) (fun j hj => ha j (by omega))]
  try rfl

theorem g2_all (n w e : Nat) (fx fe : Nat → Bool) (hn : n = w) (hv : XF.val (fun x => fe x) w = e)
    (h : fx 0 = XF.all n fun x => fe x) : fx 0 = decide (e = 2 ^ w - 1) := by
  subst hn
  rw [h, all_eq_decide_val, hv]

theorem g2_nany (n w e : Nat) (fx fe : Nat → Bool) (hn : n = w) (hv : XF.val (fun x => fe x) w = e)
    (h : fx 0 = !XF.any n fun x => fe x) : fx 0 = decide (e = 0) := by
  subst hn
  rw [h, any_eq_decide_val, hv]
  simp

theorem g2_sig (f : Format) (av m n : Nat) (hm : m = f.p - 1) (hn : n = f.p) (fm ff fz : Nat → Bool)
    (hf : XF.val (fun x => ff x) (f.p - 1) = fF f av) (hz : fz 0 = decide (eF f av ≠ 0))
    (h : ∀ k, k < n → fm k = if k < m then ff k else fz (k - m)) :
    XF.val (fun x => fm x) f.p = sigN f av := by
  have hfp := f.hp
  subst hn
  have hP1 : f.p = m + 1 := by omega
  have ht : f.t = m := by simp only [Format.t]; omega
  have hfm : XF.val ff m = fF f av := by rw [hm]; exact hf
  have h1 : XF.val fz 1 = (fz 0).toNat := val_one fz
  rw [XF.val_congr_lt (fun j hj => h j hj), hP1, val_cat ff fz m 1, hfm, h1, hz]
  unfold sigN fF
  rw [ht]
  by_cases hz0 : eF f av = 0
  · simp [hz0]
  · simp [hz0] <;> omega

theorem g2_xe (f : Format) (av n : Nat) (hn : n = f.w) (fx fe fz : Nat → Bool)
    (he : XF.val (fun x => fe x) f.w = eF f av) (hz : fz 0 = decide (eF f av ≠ 0))
    (h : ∀ k, k < n → fx k =
      if max n 32 < n then (if fz 0 = true then XF.zext n (fun x => fe x) k else XF.constBit 1 n k)
      else XF.zext (max n 32) (fun x =>
        if fz 0 = true then XF.zext n (fun x => fe x) x else XF.constBit 1 (max n 32) x) k) :
    XF.val (fun x => fx x) f.w = xeN f av := by
  have hfw := f.hw
  subst hn
  have hc : ¬ (max f.w 32 < f.w) := by omega
  rw [XF.val_congr_lt (fun j hj => (h j hj).trans (if_neg hc)),
    val_zext_trunc (max f.w 32) f.w _ (by omega), val_ite,
    XF.val_zext f.w (fun x => fe x) f.w (Nat.le_refl _),
    val_constBit_one (max f.w 32) f.w (by omega) (by omega), he, hz]
  unfold xeN
  by_cases h0 : eF f av = 0 <;> simp [h0]

/-! ## Copies, extensions, row 0 -/

theorem zext_lt {n j : Nat} (g : Nat → Bool) (h : j < n) : XF.zext n g j = g j := by
  simp [XF.zext, h]

theorem g2_zx (E n w v : Nat) (fy fx : Nat → Bool) (hn : n = w) (hw : w ≤ E)
    (hv : XF.val (fun x => fx x) w = v)
    (h : ∀ k, k < E → fy k = XF.zext n (fun k => fx k) k) :
    XF.val (fun x => fy x) E = v := by
  subst hn
  rw [XF.val_congr_lt (fun j hj => h j hj), XF.val_zext n (fun k => fx k) E hw]
  exact hv

theorem g2_copy (n w v : Nat) (fy fx : Nat → Bool) (hn : n = w) (hv : XF.val (fun x => fx x) w = v)
    (h : ∀ k, k < n → fy k = fx k) : XF.val (fun x => fy x) w = v := by
  subst hn
  rw [XF.val_congr_lt (fun j hj => h j hj)]
  exact hv

theorem g2_copyoff (n w r v : Nat) (fy fx : Nat → Bool) (hn : n = w)
    (hv : XF.val (fun x => fx (r + x)) w = v)
    (h : ∀ k, k < n → fy k = fx (r + k)) : XF.val (fun x => fy x) w = v := by
  subst hn
  rw [XF.val_congr_lt (fun j hj => h j hj)]
  exact hv

theorem g2_ext (P m v : Nat) (fx fn : Nat → Bool) (hm : m = P)
    (hv : XF.val (fun x => fn x) P = v)
    (h : ∀ k, k < P + 1 → fx k = if k < m then fn k else false) :
    XF.val (fun x => fx x) (P + 1) = v := by
  rw [hm] at h
  have htop : (if P < P then fn P else false) = false := if_neg (Nat.lt_irrefl P)
  rw [XF.val_congr_lt (fun j hj => h j hj), val_succ, htop, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, ← hv]
  exact XF.val_congr_lt (fun j hj => by simp [hj])

/-! ## The normalizer family (`za` a separate bit, the branches swapped against the reference) -/

theorem norm_rows2 (P w : Nat) (wI : Int) (hwI : wI = (w : Int)) (hP : 2 ≤ P) (hw : 1 ≤ w)
    (fn fy fz : Nat → Bool) (n0 y0 : Nat)
    (hn0 : XF.val (fun x => fn x) P = n0) (hy0 : XF.val (fun x => fy x) w = y0)
    (hz : ∀ i : Nat, (i : Int) < (P : Int) + -1 → fz i = !fn (rmN (P : Int) (i : Int) ((P : Int) + -1)))
    (hn : ∀ i : Nat, (i : Int) < (P : Int) + -1 → ∀ k, k < P →
        fn (rmN (P : Int) ((i : Int) + 1) 0 + k) =
          if fz i = true then
            XF.shlBits (XF.zext P fun x => fn (rmN (P : Int) (i : Int) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k
          else fn (rmN (P : Int) (i : Int) 0 + k))
    (hy : ∀ i : Nat, (i : Int) < (P : Int) + -1 → ∀ k, k < w →
        fy (rmN wI ((i : Int) + 1) 0 + k) =
          if max (max w 32) w < w then
            if fz i = true then
              XF.subBits w (fun x => XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x) w
                (fun x => XF.constBit 1 w x) k
            else XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) k
          else
            XF.zext (max (max w 32) w)
              (fun x =>
                if fz i = true then
                  XF.subBits (max (max w 32) w) (fun x => XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x)
                    (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) x
                else XF.zext w (fun k => fy (rmN wI (i : Int) 0 + k)) x) k) :
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
    have hzi := hz i hlt
    simp only [rmN_succ0, rmN_row0, rmN_last_col P i (by omega)] at hnrow hyrow hzi
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
        (fun j hj => by rw [hnrow j hj, hzi]; cases fn (i * P + (P - 1)) <;> simp)]
      rw [val_ite, val_shlBits_one _ _ 32 (by omega), hrn]
    have hM : ¬ (max (max w 32) w < w) := by omega
    have hy' : XF.val (fun x => fy ((i + 1) * w + x)) w =
        if fn (i * P + (P - 1)) = true then ry else (ry + (2 ^ w - 1)) % 2 ^ w := by
      rw [XF.val_congr_lt (g := fun k => if fn (i * P + (P - 1)) = true then
            XF.zext w (fun k => fy (i * w + k)) k
          else XF.subBits (max (max w 32) w) (fun x => XF.zext w (fun k => fy (i * w + k)) x)
            (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) k)
        (fun j hj => by
          have hjM : j < max (max w 32) w := by omega
          rw [hyrow j hj, if_neg hM, zext_lt _ hjM, hzi]
          cases fn (i * P + (P - 1)) <;> rfl)]
      rw [val_ite]
      have h1 : XF.val (fun k => XF.zext w (fun k => fy (i * w + k)) k) w = ry := by
        rw [XF.val_zext w _ w (Nat.le_refl w)]; exact hry
      have h2 : XF.val (fun k => XF.subBits (max (max w 32) w) (fun x => XF.zext w (fun k => fy (i * w + k)) x)
            (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) k) w =
          (ry + (2 ^ w - 1)) % 2 ^ w := by
        rw [val_subBits]
        have hwM : w ≤ max (max w 32) w := by omega
        have hz' : XF.val (fun x => XF.zext w (fun k => fy (i * w + k)) x) (max (max w 32) w) = ry := by
          rw [XF.val_zext w _ _ hwM]; exact hry
        have hc1 : XF.val (fun x => XF.constBit 1 (max (max w 32) w) x) (max (max w 32) w) = 1 :=
          val_constBit_one (max (max w 32) w) (max (max w 32) w) (by omega) (Nat.le_refl _)
        rw [hz', hc1, Nat.max_self]
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

/-! ## The divider family (`ge` a separate bit; reduced to the reference's `div_rows`) -/

theorem div_rows2 (P : Nat) (rr dd qq ge nbx : Nat → Bool) (na nb : Nat) (hP : 2 ≤ P)
    (hnb0 : 0 < nb) (hnbP : nb < 2 ^ P) (hna : na < 2 * nb)
    (hnbv : XF.val (fun x => nbx x) (P + 1) = nb)
    (hr0 : XF.val (fun x => rr x) (P + 1) = na)
    (hge : ∀ i : Nat, (i : Int) < (P : Int) + 2 →
        ge i = decide (XF.val (fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) (P + 1) ≥
            XF.val (fun x => nbx x) (P + 1)))
    (hdd : ∀ i : Nat, (i : Int) < (P : Int) + 2 → ∀ k, k < P + 1 →
        dd (rmN ((P : Int) + 1) (i : Int) 0 + k) =
          XF.subBits (P + 1) (fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) (P + 1) (fun x => nbx x) k)
    (hqq : ∀ i : Nat, (i : Int) < (P : Int) + 2 → qq ((P : Int) + -1 * (i : Int) + 1).toNat = ge i)
    (hrr : ∀ i : Nat, (i : Int) < (P : Int) + 2 → ∀ k, k < P + 1 →
        rr (rmN ((P : Int) + 1) ((i : Int) + 1) 0 + k) =
          if ge i = true then
            XF.shlBits (XF.zext (P + 1) fun x => dd (rmN ((P : Int) + 1) (i : Int) 0 + x)) 32
              (fun x => XF.constBit 1 32 x) k
          else
            XF.shlBits (XF.zext (P + 1) fun x => rr (rmN ((P : Int) + 1) (i : Int) 0 + x)) 32
              (fun x => XF.constBit 1 32 x) k) :
    (∀ i, i ≤ P + 2 → XF.val (fun x => rr (i * (P + 1) + x)) (P + 1) = restRem nb na i) ∧
    XF.val (fun k => qq k) (P + 2) = restQuo nb na (P + 2) :=
  div_rows P rr dd qq nbx na nb hP hnb0 hnbP hna hnbv hr0
    (fun i hi => (hqq i hi).trans (hge i hi)) hdd
    (fun i hi k hk => by rw [hrr i hi k hk, hqq i hi])

/-! ## The constants `kv`, `nrmth`, `ovfth` -/

theorem g2_kv (f : Format) (fkv : Nat → Bool) (n1 j1 n2 j2 : Nat) (hn1 : n1 = f.w - 1) (hj1 : j1 = f.w - 1)
    (hn2 : n2 = f.p) (hj2 : j2 = f.w + f.p)
    (h1 : ∀ k, k < n1 → fkv k = true) (h2 : fkv j1 = false)
    (h3 : ∀ k, k < n2 → fkv (f.w + k) = false) (h4 : fkv j2 = true) :
    XF.val (fun x => fkv x) (f.w + f.p + 1) = f.emax + 2 ^ (f.w + f.p) := by
  have hfw := f.hw
  subst hn1 hj1 hn2 hj2
  have hw1 : XF.val fkv f.w = XF.val fkv (f.w - 1) + 2 ^ (f.w - 1) * (fkv (f.w - 1)).toNat := by
    have := val_succ fkv (f.w - 1)
    rwa [show f.w - 1 + 1 = f.w by omega] at this
  rw [val_succ, val_split fkv f.w f.p, hw1, val_all_true fkv (f.w - 1) h1, h2,
    val_all_false (fun x => fkv (f.w + x)) f.p h3, h4]
  unfold Format.emax
  simp

theorem g2_nrmth (f : Format) (fc : Nat → Bool) (one n j : Nat) (hone : one = 1) (hn : n = f.w + f.p - 1)
    (hj : j = f.w + f.p)
    (h1 : fc 0 = true) (h2 : ∀ k, k < n → fc (one + k) = false) (h3 : fc j = true) :
    XF.val (fun x => fc x) (f.w + f.p + 1) = 1 + 2 ^ (f.w + f.p) := by
  have hfw := f.hw
  have hfp := f.hp
  subst hone hn hj
  have e : f.w + f.p + 1 = 1 + (f.w + f.p - 1) + 1 := by omega
  rw [e, val_succ, val_split fc 1 (f.w + f.p - 1), val_one, h1,
    val_all_false (fun x => fc (1 + x)) (f.w + f.p - 1) h2]
  have e2 : 1 + (f.w + f.p - 1) = f.w + f.p := by omega
  rw [e2, h3]
  simp

theorem g2_ovfth (f : Format) (fc : Nat → Bool) (n1 n2 j : Nat) (hn1 : n1 = f.w) (hn2 : n2 = f.p)
    (hj : j = f.w + f.p)
    (h1 : ∀ k, k < n1 → fc k = true) (h2 : ∀ k, k < n2 → fc (f.w + k) = false) (h3 : fc j = true) :
    XF.val (fun x => fc x) (f.w + f.p + 1) = 2 ^ f.w - 1 + 2 ^ (f.w + f.p) := by
  subst hn1 hn2 hj
  rw [val_succ, val_split fc f.w f.p, val_all_true fc f.w h1, val_all_false (fun x => fc (f.w + x)) f.p h2, h3]
  simp

/-! ## The offset exponent -/

theorem g2_eoff (EW Z yav ybv kvv adjv : Nat) (feo fya fyb fkv fadj : Nat → Bool)
    (hZ : 2 ^ EW = Z) (hEW : 1 ≤ EW)
    (hya : XF.val (fun x => fya x) EW = yav) (hyb : XF.val (fun x => fyb x) EW = ybv)
    (hkv : XF.val (fun x => fkv x) EW = kvv) (hadj : (fadj 0).toNat = adjv)
    (h : ∀ k, k < EW → feo k =
      XF.subBits EW
        (fun x => XF.addBits EW (fun x => XF.subBits EW (fun x => fya x) EW (fun x => fyb x) x) EW
          (fun x => fkv x) x)
        EW (fun x => XF.zext 1 (fun k => fadj k) x) k) :
    XF.val (fun x => feo x) EW = (((yav + (Z - ybv)) % Z + kvv) % Z + (Z - adjv)) % Z := by
  subst hZ
  rw [XF.val_congr_lt (fun j hj => h j hj), val_subBits, Nat.max_self, val_addBits, val_subBits, Nat.max_self,
    hya, hyb, hkv, XF.val_zext 1 (fun k => fadj k) EW hEW, val_one, hadj]

/-- The offset exponent is the true exponent plus `H` (no wrap: `|E| < H`). -/
theorem exp_off (Z H A emax t xa xb la lb ya yb adj : Nat)
    (hZH : Z = 2 * H) (hZ : 4 * A + 2 * t + 8 ≤ Z) (hA : 4 ≤ A) (hem : 2 * emax + 2 = A)
    (hxa1 : 1 ≤ xa) (hxa2 : xa + 2 ≤ A) (hxb1 : 1 ≤ xb) (hxb2 : xb + 2 ≤ A)
    (hla : la ≤ t) (hlb : lb ≤ t) (hadj : adj ≤ 1)
    (hya : ya < Z) (hya' : ya + la = xa ∨ ya + la = xa + Z)
    (hyb : yb < Z) (hyb' : yb + lb = xb ∨ yb + lb = xb + Z) :
    (((((ya + (Z - yb)) % Z + (emax + H)) % Z + (Z - adj)) % Z : Nat) : Int) =
      (xa : Int) - la - xb + lb + emax - adj + H := by
  have hZ0 : 0 < Z := by omega
  have h1 := mod_cases_of_lt_three_mul (ya + (Z - yb)) Z (by omega)
  have hm1 := Nat.mod_lt (ya + (Z - yb)) hZ0
  generalize (ya + (Z - yb)) % Z = E1 at *
  have h2 := mod_cases_of_lt_three_mul (E1 + (emax + H)) Z (by omega)
  have hm2 := Nat.mod_lt (E1 + (emax + H)) hZ0
  generalize (E1 + (emax + H)) % Z = E2 at *
  have h3 := mod_cases_of_lt_three_mul (E2 + (Z - adj)) Z (by omega)
  have hm3 := Nat.mod_lt (E2 + (Z - adj)) hZ0
  generalize (E2 + (Z - adj)) % Z = E3 at *
  omega

/-! ## The linear denormalizer -/

/-- One stage of the denormalizer: while the exponent register is below `H1`, count it up, shift the significand
right by one and collect the dropped bit into the sticky bit. -/
def denStep (H1 : Nat) (s : Nat × Nat × Bool) : Nat × Nat × Bool :=
  if s.1 < H1 then (s.1 + 1, s.2.1 / 2, s.2.2 || decide (s.2.1 % 2 = 1)) else s

/-- `k` stages. -/
def denIter (H1 : Nat) : Nat → Nat × Nat × Bool → Nat × Nat × Bool
  | 0, s => s
  | k + 1, s => denStep H1 (denIter H1 k s)

theorem or_mod_pow_succ (q k : Nat) :
    (decide (q % 2 ^ k ≠ 0) || decide (q / 2 ^ k % 2 = 1)) = decide (q % 2 ^ (k + 1) ≠ 0) := by
  have hp := Nat.two_pow_pos k
  rw [Nat.mod_pow_succ]
  have hb : q / 2 ^ k % 2 = 0 ∨ q / 2 ^ k % 2 = 1 := by omega
  generalize q / 2 ^ k % 2 = B at hb ⊢
  rcases hb with rfl | rfl <;> simp <;> omega

/-- **The denormalizer invariant**, below the threshold: after `k` stages the register has counted
`s = min k (H1 - e)` stages, the significand is shifted right by `s` and the sticky bit is the OR of the dropped bits. -/
theorem denIter_lt (H1 e q : Nat) (he : e < H1) : ∀ k, denIter H1 k (e, q, false) =
    (e + min k (H1 - e), q / 2 ^ min k (H1 - e), decide (q % 2 ^ min k (H1 - e) ≠ 0))
  | 0 => by simp [denIter, Nat.mod_one]
  | k + 1 => by
    show denStep H1 (denIter H1 k (e, q, false)) = _
    rw [denIter_lt H1 e q he k]
    unfold denStep
    dsimp only
    by_cases hk : k < H1 - e
    · have e1 : min k (H1 - e) = k := by omega
      have e2 : min (k + 1) (H1 - e) = k + 1 := by omega
      rw [e1, e2, if_pos (by omega : e + k < H1), Nat.div_div_eq_div_mul, ← Nat.pow_succ, or_mod_pow_succ]
      have e3 : e + k + 1 = e + (k + 1) := by omega
      rw [e3]
    · have e1 : min k (H1 - e) = H1 - e := by omega
      have e2 : min (k + 1) (H1 - e) = H1 - e := by omega
      rw [e1, e2, if_neg (by omega : ¬ (e + (H1 - e) < H1))]

/-- At or above the threshold no stage acts. -/
theorem denIter_ge (H1 e q : Nat) (he : H1 ≤ e) : ∀ k, denIter H1 k (e, q, false) = (e, q, false)
  | 0 => rfl
  | k + 1 => by
    show denStep H1 (denIter H1 k (e, q, false)) = _
    rw [denIter_ge H1 e q he k]
    unfold denStep
    dsimp only
    rw [if_neg (by omega)]

theorem shr_min (q n d : Nat) (hq : q < 2 ^ n) :
    q / 2 ^ (min n d) = q / 2 ^ d ∧ q % 2 ^ (min n d) = q % 2 ^ d := by
  by_cases h : d ≤ n
  · rw [Nat.min_eq_right h]; exact ⟨rfl, rfl⟩
  · rw [Nat.min_eq_left (by omega)]
    have h1 : 2 ^ n ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.div_eq_of_lt hq, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩

/-- After `P + 1` stages from `qm < 2^(P+1)`: the right shift by the reference's `dsh` and its sticky bit. -/
theorem den_final (H1 eo qm d P : Nat) (hq : qm < 2 ^ (P + 1))
    (hd0 : H1 ≤ eo → d = 0) (hd : ¬ (H1 ≤ eo) → d = H1 - eo) :
    (denIter H1 (P + 1) (eo, qm, false)).2.1 = qm / 2 ^ d ∧
      (denIter H1 (P + 1) (eo, qm, false)).2.2 = decide (qm % 2 ^ d ≠ 0) := by
  by_cases h : H1 ≤ eo
  · rw [denIter_ge H1 eo qm h, hd0 h]
    simp [Nat.mod_one]
  · rw [denIter_lt H1 eo qm (by omega), hd h]
    dsimp only
    obtain ⟨h1, h2⟩ := shr_min qm (P + 1) (H1 - eo) hq
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

/-- **The denormalizer family.** The rows `(e_r, q_r, t_r)` are `denIter` of row 0. -/
theorem den_rows (P w : Nat) (wI : Int) (hwI : wI = (w : Int)) (hw : 1 ≤ w) (MX : Nat) (hMX : MX = w)
    (fe fq ft fa fc : Nat → Bool) (e0 q0 H1 : Nat)
    (he0 : XF.val (fun x => fe x) w = e0) (hq0 : XF.val (fun x => fq x) (P + 1) = q0) (ht0 : ft 0 = false)
    (hc : XF.val (fun x => fc x) MX = H1) (hH1 : H1 < 2 ^ w)
    (hact : ∀ i : Nat, (i : Int) < (P : Int) + 1 →
       fa i = decide (XF.val (fun x => fe (rmN wI (i : Int) 0 + x)) MX < XF.val (fun x => fc x) MX))
    (he : ∀ i : Nat, (i : Int) < (P : Int) + 1 → ∀ k, k < w →
        fe (rmN wI ((i : Int) + 1) 0 + k) =
          if max (max w 32) w < w then
            if fa i = true then
              XF.addBits w (fun x => XF.zext w (fun k => fe (rmN wI (i : Int) 0 + k)) x) w
                (fun x => XF.constBit 1 w x) k
            else XF.zext w (fun k => fe (rmN wI (i : Int) 0 + k)) k
          else
            XF.zext (max (max w 32) w)
              (fun x =>
                if fa i = true then
                  XF.addBits (max (max w 32) w) (fun x => XF.zext w (fun k => fe (rmN wI (i : Int) 0 + k)) x)
                    (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) x
                else XF.zext w (fun k => fe (rmN wI (i : Int) 0 + k)) x) k)
    (hq : ∀ i : Nat, (i : Int) < (P : Int) + 1 → ∀ k, k < P + 1 →
        fq (rmN ((P : Int) + 1) ((i : Int) + 1) 0 + k) =
          if fa i = true then
            XF.shrBits (P + 1) (fun x => fq (rmN ((P : Int) + 1) (i : Int) 0 + x)) 32
              (fun x => XF.constBit 1 32 x) k
          else fq (rmN ((P : Int) + 1) (i : Int) 0 + k))
    (ht : ∀ i : Nat, (i : Int) < (P : Int) + 1 →
        ft (i + 1) = (ft i || fa i && fq (rmN ((P : Int) + 1) (i : Int) 0))) :
    ∀ i, i ≤ P + 1 →
      (XF.val (fun x => fe (i * w + x)) w, XF.val (fun x => fq (i * (P + 1) + x)) (P + 1), ft i) =
        denIter H1 i (e0, q0, false) := by
  subst hwI
  rw [hMX] at hact hc
  have hP1 : ((P : Int) + 1).toNat = P + 1 := by omega
  have hrow0 : ∀ (i : Nat), rmN ((P : Int) + 1) (i : Int) 0 = i * (P + 1) := by
    intro i
    have h1 : (i : Int).toNat = i := by omega
    unfold rmN; rw [h1, hP1]; rfl
  have hrow1 : ∀ (i : Nat), rmN ((P : Int) + 1) ((i : Int) + 1) 0 = (i + 1) * (P + 1) := by
    intro i
    have h1 : ((i : Int) + 1).toNat = i + 1 := by omega
    unfold rmN; rw [h1, hP1]; rfl
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Nat.zero_mul, Nat.zero_add, denIter]
    exact Prod.ext he0 (Prod.ext hq0 ht0)
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    show _ = denStep H1 (denIter H1 i (e0, q0, false))
    rw [← ih']
    have hlt : (i : Int) < (P : Int) + 1 := by omega
    have harow := hact i hlt
    have herow := he i hlt
    have hqrow := hq i hlt
    have htrow := ht i hlt
    simp only [rmN_succ0, rmN_row0, hrow0, hrow1] at harow herow hqrow htrow
    obtain ⟨re, hre⟩ : ∃ re, XF.val (fun x => fe (i * w + x)) w = re := ⟨_, rfl⟩
    obtain ⟨rq, hrq⟩ : ∃ rq, XF.val (fun x => fq (i * (P + 1) + x)) (P + 1) = rq := ⟨_, rfl⟩
    have hrelt : re < 2 ^ w := hre ▸ XF.val_lt _ w
    rw [hre, hrq]
    have ha' : fa i = decide (re < H1) := by rw [harow, hre, hc]
    have hb0 : fq (i * (P + 1)) = decide (rq % 2 = 1) := by
      have := bit_eq_of_val (fun x => fq (i * (P + 1) + x)) (P + 1) rq 0 hrq (by omega)
      simpa using this
    have hM : ¬ (max (max w 32) w < w) := by omega
    have he' : XF.val (fun x => fe ((i + 1) * w + x)) w = if fa i = true then (re + 1) % 2 ^ w else re := by
      rw [XF.val_congr_lt (g := fun k => if fa i = true then
            XF.addBits (max (max w 32) w) (fun x => XF.zext w (fun k => fe (i * w + k)) x)
              (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) k
          else XF.zext w (fun k => fe (i * w + k)) k)
        (fun j hj => by
          have hjM : j < max (max w 32) w := by omega
          rw [herow j hj, if_neg hM, zext_lt _ hjM])]
      rw [val_ite]
      have h1 : XF.val (fun k => XF.zext w (fun k => fe (i * w + k)) k) w = re := by
        rw [XF.val_zext w _ w (Nat.le_refl w)]; exact hre
      have h2 : XF.val (fun k => XF.addBits (max (max w 32) w) (fun x => XF.zext w (fun k => fe (i * w + k)) x)
            (max (max w 32) w) (fun x => XF.constBit 1 (max (max w 32) w) x) k) w = (re + 1) % 2 ^ w := by
        rw [val_addBits]
        have hwM : w ≤ max (max w 32) w := by omega
        have hz' : XF.val (fun x => XF.zext w (fun k => fe (i * w + k)) x) (max (max w 32) w) = re := by
          rw [XF.val_zext w _ _ hwM]; exact hre
        have hc1 : XF.val (fun x => XF.constBit 1 (max (max w 32) w) x) (max (max w 32) w) = 1 :=
          val_constBit_one (max (max w 32) w) (max (max w 32) w) (by omega) (Nat.le_refl _)
        rw [hz', hc1]
      rw [h1, h2]
    have hq' : XF.val (fun x => fq ((i + 1) * (P + 1) + x)) (P + 1) = if fa i = true then rq / 2 else rq := by
      rw [XF.val_congr_lt (g := fun k => if fa i = true then
            XF.shrBits (P + 1) (fun x => fq (i * (P + 1) + x)) 32 (fun x => XF.constBit 1 32 x) k
          else fq (i * (P + 1) + k)) (fun j hj => hqrow j hj)]
      rw [val_ite, val_shrBits, hrq, val_constBit_one 32 32 (by omega) (Nat.le_refl _), Nat.pow_one]
    rw [he', hq', htrow, ha', hb0]
    unfold denStep
    dsimp only
    by_cases hl : re < H1
    · have hmod : (re + 1) % 2 ^ w = re + 1 := Nat.mod_eq_of_lt (by omega)
      simp [hl, hmod]
    · simp [hl]

/-! ## The output words -/

theorem g2_wnan (f : Format) (fn : Nat → Bool) (j1 n2 m2 j3 : Nat) (A : Int)
    (hj1 : j1 = f.w + f.p - 1) (hn2 : n2 = f.w) (hm2 : m2 = f.p - 1) (hj3 : j3 = f.p - 2)
    (hA : A = (f.p : Int) - 2)
    (h1 : fn j1 = false) (h2 : ∀ k, k < n2 → fn (m2 + k) = true) (h3 : fn j3 = true)
    (h4 : ∀ i : Nat, (i : Int) < A → fn i = false) :
    XF.val (fun x => fn x) (f.w + f.p) = (2 ^ f.w - 1) * 2 ^ f.t + 2 ^ (f.t - 1) := by
  have hfp := f.hp
  have hfw := f.hw
  subst hj1 hn2 hm2 hj3 hA
  have ht : f.t = f.p - 1 := rfl
  have e : f.w + f.p = (f.p - 2) + 1 + f.w + 1 := by omega
  rw [e, val_four fn (f.p - 2) f.w, val_all_false fn (f.p - 2) (fun k hk => h4 k (by omega))]
  have e1 : f.p - 2 + 1 = f.p - 1 := by omega
  have hmid : XF.val (fun x => fn (f.p - 2 + 1 + x)) f.w = 2 ^ f.w - 1 :=
    val_all_true _ f.w (fun k hk => by rw [e1]; exact h2 k hk)
  have htop : fn (f.p - 2 + 1 + f.w) = false := by
    rw [show f.p - 2 + 1 + f.w = f.w + f.p - 1 by omega]; exact h1
  rw [hmid, htop, h3, e1]
  have e2 : f.t - 1 = f.p - 2 := by omega
  rw [ht, e2]
  simp
  omega

theorem g2_winf (f : Format) (fi fs : Nat → Bool) (j1 n2 m2 n3 : Nat)
    (hj1 : j1 = f.w + f.p - 1) (hn2 : n2 = f.w) (hm2 : m2 = f.p - 1) (hn3 : n3 = f.p - 1)
    (h1 : fi j1 = fs 0) (h2 : ∀ k, k < n2 → fi (m2 + k) = true) (h3 : ∀ k, k < n3 → fi k = false) :
    XF.val (fun x => fi x) (f.w + f.p) = (fs 0).toNat * 2 ^ (f.w + f.t) + (2 ^ f.w - 1) * 2 ^ f.t := by
  have hfp := f.hp
  subst hj1 hn2 hm2 hn3
  have ht : f.t = f.p - 1 := rfl
  have e : f.w + f.p = f.t + f.w + 1 := by omega
  rw [e, val_succ, val_split fi f.t f.w, val_all_false fi f.t (fun k hk => h3 k (by omega)),
    val_all_true (fun x => fi (f.t + x)) f.w (fun k hk => h2 k hk)]
  have e1 : f.t + f.w = f.w + f.p - 1 := by omega
  rw [e1, h1, show f.w + f.p - 1 = f.w + f.t by omega]
  rw [Nat.mul_comm (2 ^ f.t) (2 ^ f.w - 1), Nat.mul_comm (2 ^ (f.w + f.t)) (fs 0).toNat]
  omega

theorem g2_wzero (f : Format) (fz fs : Nat → Bool) (j1 n2 : Nat)
    (hj1 : j1 = f.w + f.p - 1) (hn2 : n2 = f.w + f.p - 1)
    (h1 : fz j1 = fs 0) (h2 : ∀ k, k < n2 → fz k = false) :
    XF.val (fun x => fz x) (f.w + f.p) = (fs 0).toNat * 2 ^ (f.w + f.t) := by
  have hfp := f.hp
  subst hj1 hn2
  have ht : f.t = f.p - 1 := rfl
  have e : f.w + f.p = (f.w + f.p - 1) + 1 := by omega
  rw [e, val_succ, val_all_false fz (f.w + f.p - 1) h2, h1, show f.w + f.p - 1 = f.w + f.t by omega,
    Nat.mul_comm]
  omega

theorem g2_wfin (f : Format) (ff fm fs : Nat → Bool) (n m v : Nat) (hn : n = f.w + f.p) (hm : m = f.w + f.t)
    (hv : XF.val (fun x => fm x) (f.w + f.t) = v)
    (h : ∀ k, k < n → ff k = if k < m then fm k else fs (k - m)) :
    XF.val (fun x => ff x) (f.w + f.p) = (fs 0).toNat * 2 ^ (f.w + f.t) + v := by
  have hfp := f.hp
  subst hn hm
  have e : f.w + f.p = (f.w + f.t) + 1 := by simp only [Format.t]; omega
  rw [XF.val_congr_lt (fun j hj => h j hj), e, val_cat fm fs (f.w + f.t) 1, val_one]
  have hv' : XF.val fm (f.w + f.t) = v := hv
  rw [hv', Nat.mul_comm (2 ^ (f.w + f.t)) (fs 0).toNat]
  omega

theorem g2_q (K nK : Nat) (hK : nK = K) (fq fn fi fz ff : Nat → Bool) (cn ci cz ov : Bool)
    (h : ∀ k, k < nK → fq k = if cn = true then fn k else if ci = true then fi k else if cz = true then fz k
      else if ov = true then fi k else ff k) :
    XF.val (fun x => fq x) K = if cn = true then XF.val (fun x => fn x) K else if ci = true then
      XF.val (fun x => fi x) K else if cz = true then XF.val (fun x => fz x) K else if ov = true then
      XF.val (fun x => fi x) K else XF.val (fun x => ff x) K := by
  subst hK
  rw [XF.val_congr_lt (fun j hj => h j hj)]
  cases cn <;> cases ci <;> cases cz <;> cases ov <;> simp

/-- **The output** in each case of the flags is the reference's `OutN`. -/
theorem g2_final (f : Format) (av bv : Nat) (cn ci cz ov s : Bool) (magv : Nat)
    (hcn : cn = decide (cNanN f av bv)) (hci : ci = decide (cInfN f av bv)) (hcz : cz = decide (cZeroN f av bv))
    (hs : s = decide ((sF f av + sF f bv) % 2 = 1))
    (hdp : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) →
      ov = decide (ovfN f av bv) ∧ magv = magN f av bv) :
    (if cn = true then (2 ^ f.w - 1) * 2 ^ f.t + 2 ^ (f.t - 1)
     else if ci = true then s.toNat * 2 ^ (f.w + f.t) + (2 ^ f.w - 1) * 2 ^ f.t
     else if cz = true then s.toNat * 2 ^ (f.w + f.t)
     else if ov = true then s.toNat * 2 ^ (f.w + f.t) + (2 ^ f.w - 1) * 2 ^ f.t
     else s.toNat * 2 ^ (f.w + f.t) + magv) = OutN f av bv := by
  have hfp := f.hp
  have hst : s.toNat = (sF f av + sF f bv) % 2 := by
    rw [hs]
    have : (sF f av + sF f bv) % 2 = 0 ∨ (sF f av + sF f bv) % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]
  unfold OutN
  by_cases hN : cNanN f av bv
  · have c1 : cNanN f av bv ∨ cInfN f av bv ∨ (¬ cZeroN f av bv ∧ ovfN f av bv) := Or.inl hN
    have c2 : cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1) := Or.inl hN
    have hfin : ¬ finN f av bv := fun h => h (Or.inl hN)
    have hcn' : cn = true := by rw [hcn]; exact decide_eq_true hN
    rw [if_pos hcn', if_pos hN, if_pos c1, if_pos c2, if_neg hfin]
    omega
  · have hcn' : ¬ cn = true := by rw [hcn]; simpa using hN
    by_cases hI : cInfN f av bv
    · have c1 : cNanN f av bv ∨ cInfN f av bv ∨ (¬ cZeroN f av bv ∧ ovfN f av bv) := Or.inr (Or.inl hI)
      have hfin : ¬ finN f av bv := fun h => h (Or.inr (Or.inl hI))
      have c2 : ¬ (cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1)) :=
        fun h => h.elim hN (fun h2 => hfin h2.1)
      have hci' : ci = true := by rw [hci]; exact decide_eq_true hI
      rw [if_neg hcn', if_pos hci', if_neg hN, if_pos c1, if_neg c2, if_neg hfin, hst]
      omega
    · have hci' : ¬ ci = true := by rw [hci]; simpa using hI
      by_cases hZ : cZeroN f av bv
      · have c1 : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ (¬ cZeroN f av bv ∧ ovfN f av bv)) :=
          fun h => h.elim hN (fun h2 => h2.elim hI (fun h3 => h3.1 hZ))
        have hfin : ¬ finN f av bv := fun h => h (Or.inr (Or.inr (Or.inl hZ)))
        have c2 : ¬ (cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1)) :=
          fun h => h.elim hN (fun h2 => hfin h2.1)
        have hcz' : cz = true := by rw [hcz]; exact decide_eq_true hZ
        rw [if_neg hcn', if_neg hci', if_pos hcz', if_neg hN, if_neg c1, if_pos hZ, if_neg c2, if_neg hfin, hst]
        omega
      · have hcz' : ¬ cz = true := by rw [hcz]; simpa using hZ
        have h0 : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ cZeroN f av bv) :=
          fun h => h.elim hN (fun h2 => h2.elim hI hZ)
        obtain ⟨hov, hmag⟩ := hdp h0
        by_cases hO : ovfN f av bv
        · have c1 : cNanN f av bv ∨ cInfN f av bv ∨ (¬ cZeroN f av bv ∧ ovfN f av bv) := Or.inr (Or.inr ⟨hZ, hO⟩)
          have hfin : ¬ finN f av bv := fun h => h (Or.inr (Or.inr (Or.inr hO)))
          have c2 : ¬ (cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1)) :=
            fun h => h.elim hN (fun h2 => hfin h2.1)
          have hov' : ov = true := by rw [hov]; exact decide_eq_true hO
          rw [if_neg hcn', if_neg hci', if_neg hcz', if_pos hov', if_neg hN, if_pos c1, if_neg c2, if_neg hfin, hst]
          omega
        · have hov' : ¬ ov = true := by rw [hov]; simpa using hO
          have hfin : finN f av bv := fun h => h.elim hN (fun h2 => h2.elim hI (fun h3 => h3.elim hZ hO))
          have c1 : ¬ (cNanN f av bv ∨ cInfN f av bv ∨ (¬ cZeroN f av bv ∧ ovfN f av bv)) :=
            fun h => h.elim hN (fun h2 => h2.elim hI (fun h3 => hO h3.2))
          rw [if_neg hcn', if_neg hci', if_neg hcz', if_neg hov', if_neg hN, if_neg c1, if_neg hZ, if_pos hfin, hst,
            hmag]
          have ht1 : 1 ≤ f.t := by simp only [Format.t]; omega
          obtain ⟨t', ht'⟩ : ∃ t', f.t = t' + 1 := ⟨f.t - 1, by omega⟩
          have ht2 : 2 ^ f.t = 2 * 2 ^ (f.t - 1) := by
            have : f.t - 1 = t' := by omega
            rw [this, ht', Nat.pow_succ]; omega
          have hdm := Nat.div_add_mod' (magN f av bv) (2 ^ f.t)
          have fs := Nat.mod_mul (x := magN f av bv) (a := 2 ^ (f.t - 1)) (b := 2)
          rw [show 2 ^ (f.t - 1) * 2 = 2 ^ f.t by omega] at fs
          by_cases hb : magN f av bv / 2 ^ (f.t - 1) % 2 = 1
          · have c2 : cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1) := Or.inr ⟨hfin, hb⟩
            rw [if_pos c2]
            rw [hb] at fs
            omega
          · have c2 : ¬ (cNanN f av bv ∨ (finN f av bv ∧ magN f av bv / 2 ^ (f.t - 1) % 2 = 1)) :=
              fun h => h.elim hN (fun h2 => hb h2.2)
            rw [if_neg c2]
            rw [Nat.mod_two_ne_one.mp hb] at fs
            omega

end Glue
end SvGolf.FdivParam

end D2Glue


/-! # Section `D2Chain`: the chain of the netlist `fdivp_d2.sv` -/

section D2Chain

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SvGolf.FdivParam
namespace Glue

open LeanModels.Sv LeanModels.Sv.CombView
open LeanModels.Sv.Lib
open LeanModels.Sv.XF (val_ne_zero_iff val_of_testBit val_window val_cat any_eq_decide_val all_eq_decide_val
  bit_eq_of_val val_zext_trunc val_constBit val_constBit_one val_ite val_addBits val_subBits val_shlBits_zext
  val_shrBits val_shlBits_one top_bit_iff val_succ_low val_succ val_one val_false val_window_of_testBit val_prefix
  val_split constBit_zero val_constBit_zero val_all_true val_all_false top_bit_succ_iff eqv_eq_decide_val val_four)
open LeanModels.SoftFloat.Binary

theorem g2_efq (t w M pm one P qsv efv : Nat) (hM : M = t + w) (hpm : pm = t) (hone : one = 1) (hP : t + 1 = P)
    (fefq fqs fef : Nat → Bool)
    (hqs : XF.val (fun x => fqs x) (P + 1) = qsv) (hef : XF.val (fun x => fef x) w = efv)
    (h : ∀ k, k < M → fefq k = if k < pm then fqs (one + k) else fef (k - pm)) :
    XF.val (fun x => fefq x) M = efv * 2 ^ t + qsv / 2 % 2 ^ t := by
  subst hM hone
  rw [hpm] at h
  have e1 := val_cat (fun x => fqs (1 + x)) fef t w
  have e2 := val_window fqs 1 t (P + 1) (by omega)
  have hqs' : XF.val fqs (P + 1) = qsv := hqs
  have hef' : XF.val fef w = efv := hef
  rw [XF.val_congr_lt (fun j hj => h j hj), e1, e2, hqs', Nat.pow_one, hef', Nat.mul_comm (2 ^ t) efv]
  omega

theorem g2_mag2 (M v incv : Nat) (fmag fefq finc : Nat → Bool) (hM : 1 ≤ M)
    (hv : XF.val (fun x => fefq x) M = v) (hinc : (finc 0).toNat = incv)
    (h : ∀ k, k < M → fmag k = XF.addBits M (fun x => fefq x) M (fun x => XF.zext 1 (fun k => finc k) x) k) :
    XF.val (fun x => fmag x) M = (v + incv) % 2 ^ M := by
  rw [XF.val_congr_lt (fun j hj => h j hj), val_addBits, hv, XF.val_zext 1 (fun k => finc k) M hM, val_one, hinc]

set_option maxHeartbeats 4000000 in
/-- **The chain of `fdivp_d2.sv`.** The 90 equations as `sv_equations` prints them (the signal `x` is `f_x`) and
the operands as numbers give the value of `q`: the reference's model `OutN`. -/
theorem chain2 (f : Format)
    (f_sa f_a f_sb f_b f_s f_ea f_eb f_fa f_fb f_eall_a f_eall_b f_ez_a f_ez_b f_fz_a f_fz_b f_a_nan f_b_nan f_a_inf f_b_inf f_a_zero f_b_zero f_nza f_nzb f_ma f_mb f_xa f_xb f_na_r f_nb_r f_ya_r f_yb_r f_na4 f_nb4 f_ya f_yb f_nbx f_rr f_adj f_qq f_qm f_rnz f_st0 f_kv f_nrmth f_ovfth f_eoff f_ovf f_nrm f_e_r f_q_r f_t_r f_qs f_st1 f_rb f_inc f_efq f_ef f_mag f_c_nan f_c_inf f_c_zero f_w_nan f_w_inf f_w_zero f_w_fin f_q f_za f_zb f_ge f_dd f_act : Nat → Bool)
    (av bv : Nat)
    (ha : ∀ k, k < f.w + f.p → f_a k = av.testBit k) (hb : ∀ k, k < f.w + f.p → f_b k = bv.testBit k)
    (eq_sa_plain_0 : f_sa 0 = f_a ((f.w : Int) + (f.p : Int) + -1).toNat)
    (eq_sb_plain_1 : f_sb 0 = f_b ((f.w : Int) + (f.p : Int) + -1).toNat)
    (eq_s_plain_2 : f_s 0 = (f_sa 0 ^^ f_sb 0))
    (eq_ea_plain_3 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_ea k = f_a (((f.p : Int) - 1).toNat + k))
    (eq_eb_plain_4 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_eb k = f_b (((f.p : Int) - 1).toNat + k))
    (eq_fa_plain_5 : ∀ (k : Nat), k < ((f.p : Int) - 1 + -1).natAbs + 1 → f_fa k = f_a k)
    (eq_fb_plain_6 : ∀ (k : Nat), k < ((f.p : Int) - 1 + -1).natAbs + 1 → f_fb k = f_b k)
    (eq_eall_a_plain_7 : f_eall_a 0 = XF.all (((f.w : Int) + -1).natAbs + 1) fun x => f_ea x)
    (eq_eall_b_plain_8 : f_eall_b 0 = XF.all (((f.w : Int) + -1).natAbs + 1) fun x => f_eb x)
    (eq_ez_a_plain_9 : f_ez_a 0 = !XF.any (((f.w : Int) + -1).natAbs + 1) fun x => f_ea x)
    (eq_ez_b_plain_10 : f_ez_b 0 = !XF.any (((f.w : Int) + -1).natAbs + 1) fun x => f_eb x)
    (eq_fz_a_plain_11 : f_fz_a 0 = !XF.any (((f.p : Int) - 1 + -1).natAbs + 1) fun x => f_fa x)
    (eq_fz_b_plain_12 : f_fz_b 0 = !XF.any (((f.p : Int) - 1 + -1).natAbs + 1) fun x => f_fb x)
    (eq_a_nan_plain_13 : f_a_nan 0 = (f_eall_a 0 && !f_fz_a 0))
    (eq_b_nan_plain_14 : f_b_nan 0 = (f_eall_b 0 && !f_fz_b 0))
    (eq_a_inf_plain_15 : f_a_inf 0 = (f_eall_a 0 && f_fz_a 0))
    (eq_b_inf_plain_16 : f_b_inf 0 = (f_eall_b 0 && f_fz_b 0))
    (eq_a_zero_plain_17 : f_a_zero 0 = (f_ez_a 0 && f_fz_a 0))
    (eq_b_zero_plain_18 : f_b_zero 0 = (f_ez_b 0 && f_fz_b 0))
    (eq_nza_plain_19 : f_nza 0 = !f_ez_a 0)
    (eq_nzb_plain_20 : f_nzb 0 = !f_ez_b 0)
    (eq_ma_plain_21 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_ma k = if k < ((f.p : Int) - 1 + -1).natAbs + 1 then f_fa k else f_nza (k - (((f.p : Int) - 1 + -1).natAbs + 1)))
    (eq_mb_plain_22 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_mb k = if k < ((f.p : Int) - 1 + -1).natAbs + 1 then f_fb k else f_nzb (k - (((f.p : Int) - 1 + -1).natAbs + 1)))
    (eq_xa_plain_23 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_xa k = if max (((f.w : Int) + -1).natAbs + 1) 32 < ((f.w : Int) + -1).natAbs + 1 then if f_nza 0 = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_ea x) k else XF.constBit 1 (((f.w : Int) + -1).natAbs + 1) k else XF.zext (max (((f.w : Int) + -1).natAbs + 1) 32) (fun x => if f_nza 0 = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_ea x) x else XF.constBit 1 (max (((f.w : Int) + -1).natAbs + 1) 32) x) k)
    (eq_xb_plain_24 : ∀ (k : Nat), k < ((f.w : Int) + -1).natAbs + 1 → f_xb k = if max (((f.w : Int) + -1).natAbs + 1) 32 < ((f.w : Int) + -1).natAbs + 1 then if f_nzb 0 = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_eb x) k else XF.constBit 1 (((f.w : Int) + -1).natAbs + 1) k else XF.zext (max (((f.w : Int) + -1).natAbs + 1) 32) (fun x => if f_nzb 0 = true then XF.zext (((f.w : Int) + -1).natAbs + 1) (fun x => f_eb x) x else XF.constBit 1 (max (((f.w : Int) + -1).natAbs + 1) 32) x) k)
    (eq_na_r_plain_25 : ∀ (k : Nat), k < f.p → f_na_r k = f_ma k)
    (eq_nb_r_plain_26 : ∀ (k : Nat), k < f.p → f_nb_r k = f_mb k)
    (eq_ya_r_plain_27 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r k = XF.zext (((f.w : Int) + -1).natAbs + 1) (fun k => f_xa k) k)
    (eq_yb_r_plain_28 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r k = XF.zext (((f.w : Int) + -1).natAbs + 1) (fun k => f_xb k) k)
    (eq_na4_plain_29 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_na4 k = f_na_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k))
    (eq_nb4_plain_30 : ∀ (k : Nat), k < ((f.p : Int) + -1).natAbs + 1 → f_nb4 k = f_nb_r (rmN ((f.p : Int)) ((f.p : Int) + -1) 0 + k))
    (eq_ya_plain_31 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_ya k = f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + k))
    (eq_yb_plain_32 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_yb k = f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((f.p : Int) + -1) 0 + k))
    (eq_nbx_plain_33 : ∀ (k : Nat), k < f.p + 1 → f_nbx k = if k < ((f.p : Int) + -1).natAbs + 1 then f_nb4 k else false)
    (eq_rr_plain_34 : ∀ (k : Nat), k < f.p + 1 → f_rr k = if k < ((f.p : Int) + -1).natAbs + 1 then f_na4 k else false)
    (eq_adj_plain_35 : f_adj 0 = !f_qq (f.p + 1))
    (eq_qm_plain_36 : ∀ (k : Nat), k < f.p + 1 → f_qm k = if f_qq (f.p + 1) = true then f_qq (Int.toNat 1 + k) else f_qq k)
    (eq_rnz_plain_37 : f_rnz 0 = XF.any (f.p + 1) fun x => f_rr (rmN ((f.p : Int) + 1) ((f.p : Int) + 2) 0 + x))
    (eq_st0_plain_38 : f_st0 0 = (f_qq (f.p + 1) && f_qq 0 || f_rnz 0))
    (eq_kv_plain_39 : ∀ (k : Nat), k < ((f.w : Int) + -2 + 1).toNat → f_kv k = true)
    (eq_kv_plain_40 : f_kv ((f.w : Int) + -1).toNat = false)
    (eq_kv_plain_41 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -2 - (f.w : Int) + 1).toNat → f_kv (f.w + k) = false)
    (eq_kv_plain_42 : f_kv ((f.w : Int) + (f.p : Int) + 1 + -1).toNat = true)
    (eq_nrmth_plain_43 : f_nrmth 0 = true)
    (eq_nrmth_plain_44 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -2).toNat → f_nrmth (Int.toNat 1 + k) = false)
    (eq_nrmth_plain_45 : f_nrmth ((f.w : Int) + (f.p : Int) + 1 + -1).toNat = true)
    (eq_ovfth_plain_46 : ∀ (k : Nat), k < ((f.w : Int) + -1 + 1).toNat → f_ovfth k = true)
    (eq_ovfth_plain_47 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -2 - (f.w : Int) + 1).toNat → f_ovfth (f.w + k) = false)
    (eq_ovfth_plain_48 : f_ovfth ((f.w : Int) + (f.p : Int) + 1 + -1).toNat = true)
    (eq_eoff_plain_49 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 → f_eoff k = XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.addBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.subBits (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_ya x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_yb x) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => f_kv x) x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) (fun x => XF.zext 1 (fun k => f_adj k) x) k)
    (eq_ovf_plain_50 : f_ovf 0 = decide (XF.val (fun x => f_eoff x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) ≥ XF.val (fun x => f_ovfth x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)))
    (eq_nrm_plain_51 : f_nrm 0 = decide (XF.val (fun x => f_eoff x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) ≥ XF.val (fun x => f_nrmth x) (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)))
    (eq_e_r_plain_52 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_e_r k = f_eoff k)
    (eq_q_r_plain_53 : ∀ (k : Nat), k < f.p + 1 → f_q_r k = f_qm k)
    (eq_t_r_plain_54 : f_t_r 0 = false)
    (eq_qs_plain_55 : ∀ (k : Nat), k < f.p + 1 → f_qs k = f_q_r (rmN ((f.p : Int) + 1) ((f.p : Int) + 1) 0 + k))
    (eq_st1_plain_56 : f_st1 0 = (f_st0 0 || f_t_r (f.p + 1)))
    (eq_rb_plain_57 : f_rb 0 = f_qs 0)
    (eq_inc_plain_58 : f_inc 0 = (f_rb 0 && (f_st1 0 || f_qs (Int.toNat 1))))
    (eq_efq_plain_59 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 → f_efq k = if k < ((f.p : Int) + -1).toNat then f_qs (Int.toNat 1 + k) else f_ef (k - ((f.p : Int) + -1).toNat))
    (eq_mag_plain_60 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 → f_mag k = XF.addBits (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => f_efq x) (((f.w : Int) + (f.p : Int) + -2).natAbs + 1) (fun x => XF.zext 1 (fun k => f_inc k) x) k)
    (eq_c_nan_plain_61 : f_c_nan 0 = (f_a_nan 0 || f_b_nan 0 || f_a_inf 0 && f_b_inf 0 || f_a_zero 0 && f_b_zero 0))
    (eq_c_inf_plain_62 : f_c_inf 0 = (f_a_inf 0 || f_b_zero 0))
    (eq_c_zero_plain_63 : f_c_zero 0 = (f_b_inf 0 || f_a_zero 0))
    (eq_w_nan_plain_64 : f_w_nan ((f.w : Int) + (f.p : Int) + -1).toNat = false)
    (eq_w_nan_plain_65 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat → f_w_nan (((f.p : Int) - 1).toNat + k) = true)
    (eq_w_nan_plain_66 : f_w_nan ((f.p : Int) - 1 + -1).toNat = true)
    (eq_w_inf_plain_67 : f_w_inf ((f.w : Int) + (f.p : Int) + -1).toNat = f_s 0)
    (eq_w_inf_plain_68 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 - ((f.p : Int) - 1) + 1).toNat → f_w_inf (((f.p : Int) - 1).toNat + k) = true)
    (eq_w_inf_plain_69 : ∀ (k : Nat), k < ((f.p : Int) - 1 + -1 + 1).toNat → f_w_inf k = false)
    (eq_w_zero_plain_70 : f_w_zero ((f.w : Int) + (f.p : Int) + -1).toNat = f_s 0)
    (eq_w_zero_plain_71 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -2 + 1).toNat → f_w_zero k = false)
    (eq_w_fin_plain_72 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -1).natAbs + 1 → f_w_fin k = if k < ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 then f_mag k else f_s (k - (((f.w : Int) + (f.p : Int) + -2).natAbs + 1)))
    (eq_q_plain_73 : ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + -1).natAbs + 1 → f_q k = if f_c_nan 0 = true then f_w_nan k else if f_c_inf 0 = true then f_w_inf k else if f_c_zero 0 = true then f_w_zero k else if f_ovf 0 = true then f_w_inf k else f_w_fin k)
    (eq_za_norm_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → f_za i = !f_na_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)))
    (eq_zb_norm_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → f_zb i = !f_nb_r (rmN ((f.p : Int)) ((i : Int)) ((f.p : Int) + -1)))
    (eq_na_r_norm_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_na_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_za i = true then XF.shlBits (XF.zext f.p fun x => f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k else f_na_r (rmN ((f.p : Int)) ((i : Int)) 0 + k))
    (eq_nb_r_norm_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < f.p → f_nb_r (rmN ((f.p : Int)) ((i : Int) + 1) 0 + k) = if f_zb i = true then XF.shlBits (XF.zext f.p fun x => f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k else f_nb_r (rmN ((f.p : Int)) ((i : Int)) 0 + k))
    (eq_ya_r_norm_4 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_za i = true then XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.zext (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => if f_za i = true then XF.subBits (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.constBit 1 (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) x) x else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_ya_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) k)
    (eq_yb_r_norm_5 : ∀ (i : Nat), (i : Int) < (f.p : Int) + -1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_zb i = true then XF.subBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.zext (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => if f_zb i = true then XF.subBits (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.constBit 1 (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) x) x else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_yb_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) k)
    (eq_ge_div_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → f_ge i = decide (XF.val (fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) (f.p + 1) ≥ XF.val (fun x => f_nbx x) (f.p + 1)))
    (eq_dd_div_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → ∀ (k : Nat), k < f.p + 1 → f_dd (rmN ((f.p : Int) + 1) ((i : Int)) 0 + k) = XF.subBits (f.p + 1) (fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) (f.p + 1) (fun x => f_nbx x) k)
    (eq_qq_div_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → f_qq ((f.p : Int) + -1 * (i : Int) + 1).toNat = f_ge i)
    (eq_rr_div_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 2 → ∀ (k : Nat), k < f.p + 1 → f_rr (rmN ((f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if f_ge i = true then XF.shlBits (XF.zext (f.p + 1) fun x => f_dd (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k else XF.shlBits (XF.zext (f.p + 1) fun x => f_rr (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k)
    (eq_act_den_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 1 → f_act i = decide (XF.val (fun x => f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + x)) (max ((f.w : Int) + (f.p : Int) + 1).toNat (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)) < XF.val (fun x => f_nrmth x) (max ((f.w : Int) + (f.p : Int) + 1).toNat (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1))))
    (eq_e_r_den_1 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 1 → ∀ (k : Nat), k < ((f.w : Int) + (f.p : Int) + 1).toNat → f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat < ((f.w : Int) + (f.p : Int) + 1).toNat then if f_act i = true then XF.addBits ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) ((f.w : Int) + (f.p : Int) + 1).toNat (fun x => XF.constBit 1 ((f.w : Int) + (f.p : Int) + 1).toNat x) k else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) k else XF.zext (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => if f_act i = true then XF.addBits (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) (fun x => XF.constBit 1 (max (max ((f.w : Int) + (f.p : Int) + 1).toNat 32) ((f.w : Int) + (f.p : Int) + 1).toNat) x) x else XF.zext ((f.w : Int) + (f.p : Int) + 1).toNat (fun k => f_e_r (rmN ((f.w : Int) + (f.p : Int) + 1) ((i : Int)) 0 + k)) x) k)
    (eq_q_r_den_2 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 1 → ∀ (k : Nat), k < f.p + 1 → f_q_r (rmN ((f.p : Int) + 1) ((i : Int) + 1) 0 + k) = if f_act i = true then XF.shrBits (f.p + 1) (fun x => f_q_r (rmN ((f.p : Int) + 1) ((i : Int)) 0 + x)) 32 (fun x => XF.constBit 1 32 x) k else f_q_r (rmN ((f.p : Int) + 1) ((i : Int)) 0 + k))
    (eq_t_r_den_3 : ∀ (i : Nat), (i : Int) < (f.p : Int) + 1 → f_t_r (i + 1) = (f_t_r i || f_act i && f_q_r (rmN ((f.p : Int) + 1) ((i : Int)) 0)))
    (eq_ef_efg_0 : ∀ (i : Nat), i < f.w → f_ef i = (f_eoff i && f_nrm 0))
    (eq_w_nan_nanz_0 : ∀ (i : Nat), (i : Int) < (f.p : Int) - 1 + -1 → f_w_nan i = false)
    : XF.val (fun x => f_q x) (f.w + f.p) = OutN f av bv := by
  have hfw := f.hw
  have hfp := f.hp
  -- the operand classes, while the context is still small
  have hfin : ∀ x, ¬ (nanN f x ∨ infN f x ∨ zeroN f x) → eF f x ≠ 2 ^ f.w - 1 ∧ ¬ (eF f x = 0 ∧ fF f x = 0) := by
    intro x hx
    unfold nanN infN zeroN at hx
    omega
  have ht : f.t = f.p - 1 := rfl
  -- unpack and classify
  have b_s : f_s 0 = decide ((sF f av + sF f bv) % 2 = 1) :=
    g_s f av bv (((f.w : Int) + (f.p : Int) + -1).toNat) f_s f_a f_b (by omega) ha hb
      (by rw [eq_s_plain_2, eq_sa_plain_0, eq_sb_plain_1])
  have b_ea := g2_ewin f av _ _ f_ea f_a (by omega) (by omega) ha eq_ea_plain_3
  have b_eb := g2_ewin f bv _ _ f_eb f_b (by omega) (by omega) hb eq_eb_plain_4
  have b_fa := g2_fwin f av _ f_fa f_a (by omega) ha eq_fa_plain_5
  have b_fb := g2_fwin f bv _ f_fb f_b (by omega) hb eq_fb_plain_6
  have b_eall_a := g2_all _ _ _ f_eall_a f_ea (by omega) b_ea eq_eall_a_plain_7
  have b_eall_b := g2_all _ _ _ f_eall_b f_eb (by omega) b_eb eq_eall_b_plain_8
  have b_ez_a := g2_nany _ _ _ f_ez_a f_ea (by omega) b_ea eq_ez_a_plain_9
  have b_ez_b := g2_nany _ _ _ f_ez_b f_eb (by omega) b_eb eq_ez_b_plain_10
  have b_fz_a := g2_nany _ _ _ f_fz_a f_fa (by omega) b_fa eq_fz_a_plain_11
  have b_fz_b := g2_nany _ _ _ f_fz_b f_fb (by omega) b_fb eq_fz_b_plain_12
  have b_nza : f_nza 0 = decide (eF f av ≠ 0) := by rw [eq_nza_plain_19, b_ez_a]; simp
  have b_nzb : f_nzb 0 = decide (eF f bv ≠ 0) := by rw [eq_nzb_plain_20, b_ez_b]; simp
  have b_cn : f_c_nan 0 = decide (cNanN f av bv) := by
    rw [eq_c_nan_plain_61, eq_a_nan_plain_13, eq_b_nan_plain_14, eq_a_inf_plain_15, eq_b_inf_plain_16,
      eq_a_zero_plain_17, eq_b_zero_plain_18, b_eall_a, b_eall_b, b_fz_a, b_fz_b, b_ez_a, b_ez_b, Bool.eq_iff_iff]
    simp [cNanN, nanN, infN, zeroN] <;> first | omega | grind
  have b_ci : f_c_inf 0 = decide (cInfN f av bv) := by
    rw [eq_c_inf_plain_62, eq_a_inf_plain_15, eq_b_zero_plain_18, b_eall_a, b_fz_a, b_fz_b, b_ez_b,
      Bool.eq_iff_iff]
    simp [cInfN, infN, zeroN] <;> first | omega | grind
  have b_cz : f_c_zero 0 = decide (cZeroN f av bv) := by
    rw [eq_c_zero_plain_63, eq_b_inf_plain_16, eq_a_zero_plain_17, b_eall_b, b_fz_b, b_fz_a, b_ez_a,
      Bool.eq_iff_iff]
    simp [cZeroN, infN, zeroN] <;> first | omega | grind
  -- the significands, the effective exponents, row 0 of the normalizer
  have b_ma := g2_sig f av _ _ (by omega) (by omega) f_ma f_fa f_nza b_fa b_nza eq_ma_plain_21
  have b_mb := g2_sig f bv _ _ (by omega) (by omega) f_mb f_fb f_nzb b_fb b_nzb eq_mb_plain_22
  have b_xa := g2_xe f av _ (by omega) f_xa f_ea f_nza b_ea b_nza eq_xa_plain_23
  have b_xb := g2_xe f bv _ (by omega) f_xb f_eb f_nzb b_eb b_nzb eq_xb_plain_24
  have hn0a := g2_copy _ _ _ f_na_r f_ma (by omega) b_ma eq_na_r_plain_25
  have hn0b := g2_copy _ _ _ f_nb_r f_mb (by omega) b_mb eq_nb_r_plain_26
  have hy0a := g2_zx _ _ _ _ f_ya_r f_xa (by omega) (by omega) b_xa eq_ya_r_plain_27
  have hy0b := g2_zx _ _ _ _ f_yb_r f_xb (by omega) (by omega) b_xb eq_yb_r_plain_28
  -- the normalizer rows
  have hrows_a := norm_rows2 f.p _ _ (by omega) f.hp (by omega) f_na_r f_ya_r f_za (sigN f av) (xeN f av) hn0a hy0a
    eq_za_norm_0 eq_na_r_norm_2 eq_ya_r_norm_4
  have hrows_b := norm_rows2 f.p _ _ (by omega) f.hp (by omega) f_nb_r f_yb_r f_zb (sigN f bv) (xeN f bv) hn0b hy0b
    eq_zb_norm_1 eq_nb_r_norm_3 eq_yb_r_norm_5
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
  have hrtopQ : rmN ((f.p : Int) + 1) ((f.p : Int) + 1) 0 = (f.p + 1) * (f.p + 1) :=
    rmN_eq _ _ _ (f.p + 1) (f.p + 1) 0 (by omega) (by omega) (by omega)
  -- the copies of the last rows and the extensions
  have b_na4 := g2_copyoff _ f.p _ (naN f av) f_na4 f_na_r (by omega) (by rw [hrtop]; exact hna_val) eq_na4_plain_29
  have b_nb4 := g2_copyoff _ f.p _ (naN f bv) f_nb4 f_nb_r (by omega) (by rw [hrtop]; exact hnb_val) eq_nb4_plain_30
  have b_ya := g2_copyoff _ (f.w + f.p + 1) _ (yaN f av) f_ya f_ya_r (by omega) (by rw [hrtopE]; exact hya_val)
    eq_ya_plain_31
  have b_yb := g2_copyoff _ (f.w + f.p + 1) _ (yaN f bv) f_yb f_yb_r (by omega) (by rw [hrtopE]; exact hyb_val)
    eq_yb_plain_32
  have hnbx : XF.val (fun x => f_nbx x) (f.p + 1) = naN f bv :=
    g2_ext f.p _ _ f_nbx f_nb4 (by omega) b_nb4 eq_nbx_plain_33
  have hr0 : XF.val (fun x => f_rr x) (f.p + 1) = naN f av :=
    g2_ext f.p _ _ f_rr f_na4 (by omega) b_na4 eq_rr_plain_34
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
    obtain ⟨hxa1, hxa2⟩ := xe_facts f av hfa.1
    obtain ⟨hxb1, hxb2⟩ := xe_facts f bv hfb.1
    clear hns hfa hfb
    have hp2 : 2 ^ f.p = 2 * 2 ^ f.t := two_pow_t f
    have hnb0 : 0 < naN f bv := by have := Nat.two_pow_pos f.t; omega
    have hnalt : naN f av < 2 * naN f bv := by omega
    obtain ⟨hrowsd, hqqval⟩ := div_rows2 f.p f_rr f_dd f_qq f_ge f_nbx (naN f av) (naN f bv) f.hp hnb0 hnb_hi
      hnalt hnbx hr0 eq_ge_div_0 eq_dd_div_1 eq_qq_div_2 eq_rr_div_3
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
    -- quotient normalization and the sticky bit of the division
    have b_adj : (f_adj 0).toNat = adjN f av bv := g_adj f.p (qqN f av bv) f_adj f_qq hqq eq_adj_plain_35
    have b_qm : XF.val (fun x => f_qm x) (f.p + 1) = qmN f av bv :=
      g_qm f.p _ (qqN f av bv) (by omega) f_qm f_qq hqq eq_qm_plain_36
    have hrrN : XF.val (fun x => f_rr (rmN ((f.p : Int) + 1) ((f.p : Int) + 2) 0 + x)) (f.p + 1) = rrN f av bv := by
      rw [hrtop2]; exact hrr_top
    have b_rnz : f_rnz 0 = decide (rrN f av bv ≠ 0) := by
      rw [eq_rnz_plain_37, any_eq_decide_val, hrrN]
    have hqqtop : f_qq (f.p + 1) = decide (2 ^ (f.p + 1) ≤ qqN f av bv) := by
      have := top_bit_succ_iff f_qq (f.p + 1) (qqN f av bv) hqq
      by_cases hc : 2 ^ (f.p + 1) ≤ qqN f av bv
      · rw [this.2 hc]; simp [hc]
      · have hb' : ¬ f_qq (f.p + 1) = true := fun hh => hc (this.1 hh)
        simp at hb'
        rw [hb']; simp [hc]
    have hqq0 : f_qq 0 = decide (qqN f av bv % 2 = 1) := by
      have := bit_eq_of_val f_qq (f.p + 2) (qqN f av bv) 0 hqq (by omega)
      simpa using this
    have b_st0 : f_st0 0 = decide (st0N f av bv) := by
      have hst0d : decide (st0N f av bv) =
          decide ((2 ^ (f.p + 1) ≤ qqN f av bv ∧ qqN f av bv % 2 = 1) ∨ rrN f av bv ≠ 0) :=
        decide_eq_decide.2 Iff.rfl
      rw [eq_st0_plain_38, hqqtop, hqq0, b_rnz, hst0d, Bool.eq_iff_iff]
      simp
    -- the constants
    have hEWe : ((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1 = f.w + f.p + 1 := by omega
    have b_kv := g2_kv f f_kv _ _ _ _ (by omega) (by omega) (by omega) (by omega) eq_kv_plain_39 eq_kv_plain_40
      eq_kv_plain_41 eq_kv_plain_42
    have b_nrmth := g2_nrmth f f_nrmth _ _ _ (by omega) (by omega) (by omega) eq_nrmth_plain_43 eq_nrmth_plain_44
      eq_nrmth_plain_45
    have b_ovfth := g2_ovfth f f_ovfth _ _ _ (by omega) (by omega) (by omega) eq_ovfth_plain_46 eq_ovfth_plain_47
      eq_ovfth_plain_48
    -- the offset exponent
    have b_eoff := g2_eoff _ (ZN f) (yaN f av) (yaN f bv) (f.emax + 2 ^ (f.w + f.p)) (adjN f av bv) f_eoff f_ya f_yb
      f_kv f_adj (by rw [hEWe]; rfl) (by omega) (by rw [hEWe]; exact b_ya) (by rw [hEWe]; exact b_yb)
      (by rw [hEWe]; exact b_kv) b_adj eq_eoff_plain_49
    rw [hEWe] at b_eoff
    have hZ := Z_big f
    have hw4 := four_le_two_pow_w f
    have hw2 := two_pow_w_emax f
    have hZH : ZN f = 2 * 2 ^ (f.w + f.p) := ZN_eq f
    have hadj1 : adjN f av bv ≤ 1 := by unfold adjN; split <;> omega
    obtain ⟨Ei, hEi⟩ : ∃ Ei : Int, Ei = (xeN f av : Int) - la - xeN f bv + lb + f.emax - adjN f av bv := ⟨_, rfl⟩
    have hEdec := exp_facts (ZN f) (2 ^ f.w) f.emax f.t (xeN f av) (xeN f bv) la lb (yaN f av) (yaN f bv)
      (adjN f av bv) hZ hw4 hw2.symm hxa1 hxa2 hxb1 hxb2 hla hlb hadj1 hya_lt hya_l hyb_lt hyb_l
    have hE : (0 ≤ Ei ∧ (EN f av bv : Int) = Ei) ∨ (Ei < 0 ∧ (EN f av bv : Int) = Ei + ZN f) := by
      rw [hEi]; unfold EN; exact hEdec
    have hE2 : EN f av bv < ZN f := by unfold EN; exact Nat.mod_lt _ (by omega)
    have hEi1 : -(ZN f : Int) < 2 * Ei := by omega
    have hEi2 : 2 * Ei < ZN f := by omega
    obtain ⟨hnrm_iff, hovf_iff, hdsh⟩ := nrm_ovf_dsh f (EN f av bv) Ei hE hEi1 hEi2 hE2
    have heo := exp_off (ZN f) (2 ^ (f.w + f.p)) (2 ^ f.w) f.emax f.t (xeN f av) (xeN f bv) la lb (yaN f av)
      (yaN f bv) (adjN f av bv) hZH hZ hw4 hw2.symm hxa1 hxa2 hxb1 hxb2 hla hlb hadj1 hya_lt hya_l hyb_lt hyb_l
    obtain ⟨eo, heo_def⟩ : ∃ eo, XF.val (fun x => f_eoff x) (f.w + f.p + 1) = eo := ⟨_, rfl⟩
    have heoI : (eo : Int) = Ei + ((2 ^ (f.w + f.p) : Nat) : Int) := by
      rw [← heo_def, b_eoff, heo, hEi]
    clear heo hEdec hya_l hyb_l
    have hHpos := Nat.two_pow_pos (f.w + f.p)
    have b_ovf : f_ovf 0 = decide (ovfN f av bv) := by
      rw [eq_ovf_plain_50, hEWe, heo_def, b_ovfth]
      apply decide_eq_decide.2
      show _ ↔ ovfE f (EN f av bv)
      rw [hovf_iff]
      constructor <;> intro h <;> omega
    have b_nrm : f_nrm 0 = decide (nrmE f (EN f av bv)) := by
      rw [eq_nrm_plain_51, hEWe, heo_def, b_nrmth]
      apply decide_eq_decide.2
      rw [hnrm_iff]
      constructor <;> intro h <;> omega
    -- the exponent field
    have b_ef : XF.val (fun x => f_ef x) f.w = efN f av bv := by
      have hwEW : f.w ≤ f.w + f.p + 1 := by omega
      by_cases hn : nrmE f (EN f av bv)
      · have hnr : f_nrm 0 = true := by rw [b_nrm]; exact decide_eq_true hn
        rw [XF.val_congr_lt (g := fun x => f_eoff x) (fun j hj => by rw [eq_ef_efg_0 j hj, hnr, Bool.and_true]),
          val_prefix f_eoff (f.w + f.p + 1) f.w hwEW]
        have hEN : eo = EN f av bv + 2 ^ f.w * 2 ^ f.p := by
          have h1 := hnrm_iff.1 hn
          rw [← Nat.pow_add]; omega
        unfold efN
        rw [heo_def, if_pos hn, hEN, Nat.add_mul_mod_self_left]
      · have hnr : f_nrm 0 = false := by rw [b_nrm]; exact decide_eq_false hn
        unfold efN
        rw [if_neg hn]
        exact val_all_false _ f.w (fun j hj => by rw [eq_ef_efg_0 j hj, hnr, Bool.and_false])
    -- the denormalizer
    have hwe2 : max ((f.w : Int) + (f.p : Int) + 1).toNat (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1) =
        ((f.w : Int) + (f.p : Int) + 1).toNat := by omega
    have he0 : XF.val (fun x => f_e_r x) ((f.w : Int) + (f.p : Int) + 1).toNat = eo :=
      g2_copy _ _ _ f_e_r f_eoff (by omega) (by rw [hwe]; exact heo_def) eq_e_r_plain_52
    have hq0 : XF.val (fun x => f_q_r x) (f.p + 1) = qmN f av bv :=
      g2_copy _ _ _ f_q_r f_qm (by omega) b_qm eq_q_r_plain_53
    have hc : XF.val (fun x => f_nrmth x)
        (max ((f.w : Int) + (f.p : Int) + 1).toNat (((f.w : Int) + (f.p : Int) + 1 + -1).natAbs + 1)) =
        2 ^ (f.w + f.p) + 1 := by
      rw [hwe2, hwe, b_nrmth]; omega
    have hH1 : 2 ^ (f.w + f.p) + 1 < 2 ^ ((f.w : Int) + (f.p : Int) + 1).toNat := by
      rw [hwe, Nat.pow_succ]; omega
    have hden := den_rows f.p _ _ (by omega) (by omega) _ (by omega) f_e_r f_q_r f_t_r f_act f_nrmth eo
      (qmN f av bv) (2 ^ (f.w + f.p) + 1) he0 hq0 eq_t_r_plain_54 hc hH1 eq_act_den_0 eq_e_r_den_1 eq_q_r_den_2
      eq_t_r_den_3 (f.p + 1) (Nat.le_refl _)
    have hdsh0 : nrmE f (EN f av bv) → dshE f (EN f av bv) = 0 := fun h => by unfold dshE; rw [if_pos h]
    have hdf := den_final (2 ^ (f.w + f.p) + 1) eo (qmN f av bv) (dshE f (EN f av bv)) f.p hqm_lt
      (fun h => hdsh0 (hnrm_iff.2 (by omega)))
      (fun h => by
        have hn : ¬ nrmE f (EN f av bv) := fun hn => h (by have := hnrm_iff.1 hn; omega)
        have := hdsh hn
        omega)
    have hqrow : XF.val (fun x => f_q_r ((f.p + 1) * (f.p + 1) + x)) (f.p + 1) =
        qmN f av bv / 2 ^ dshE f (EN f av bv) := by
      rw [← hdf.1]; exact congrArg (fun t => t.2.1) hden
    have b_qs : XF.val (fun x => f_qs x) (f.p + 1) = qsN f av bv :=
      g2_copyoff _ _ _ (qsN f av bv) f_qs f_q_r (by omega) (by rw [hrtopQ]; exact hqrow) eq_qs_plain_55
    have b_t : f_t_r (f.p + 1) = decide (qmN f av bv % 2 ^ dshE f (EN f av bv) ≠ 0) := by
      rw [← hdf.2]; exact congrArg (fun t => t.2.2) hden
    -- the rounding increment
    have hqs0 : f_qs 0 = decide (qsN f av bv % 2 = 1) := by
      have := bit_eq_of_val f_qs (f.p + 1) (qsN f av bv) 0 b_qs (by omega)
      simpa using this
    have hqs1 : f_qs 1 = decide (qsN f av bv / 2 % 2 = 1) := by
      have := bit_eq_of_val f_qs (f.p + 1) (qsN f av bv) 1 b_qs (by omega)
      simpa using this
    have b_inc : f_inc 0 = decide (incN f av bv) := by
      have hincd : decide (incN f av bv) = decide (qsN f av bv % 2 = 1 ∧ (st0N f av bv ∨
          qmN f av bv % 2 ^ dshE f (EN f av bv) ≠ 0 ∨ qsN f av bv / 2 % 2 = 1)) :=
        decide_eq_decide.2 Iff.rfl
      rw [eq_inc_plain_58, eq_rb_plain_57, eq_st1_plain_56, b_st0, b_t, hqs0, show Int.toNat 1 = 1 from rfl, hqs1,
        hincd, Bool.eq_iff_iff]
      simp [or_assoc]
    have hinc : (f_inc 0).toNat = if incN f av bv then 1 else 0 := by
      rw [b_inc]
      by_cases h : incN f av bv <;> simp [h]
    -- the packed magnitude
    have b_efq := g2_efq f.t f.w _ _ _ f.p (qsN f av bv) (efN f av bv) (by omega) (by omega) (by omega) (by omega)
      f_efq f_qs f_ef b_qs b_ef eq_efq_plain_59
    have b_mag := g2_mag2 _ _ _ f_mag f_efq f_inc (by omega) b_efq hinc eq_mag_plain_60
    have hMe : ((f.w : Int) + (f.p : Int) + -2).natAbs + 1 = f.w + f.t := by omega
    rw [hMe] at b_mag
    exact ⟨b_ovf, b_mag⟩
  -- the output words and the output
  have b_wnan := g2_wnan f f_w_nan _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    eq_w_nan_plain_64 eq_w_nan_plain_65 eq_w_nan_plain_66 eq_w_nan_nanz_0
  have b_winf := g2_winf f f_w_inf f_s _ _ _ _ (by omega) (by omega) (by omega) (by omega)
    eq_w_inf_plain_67 eq_w_inf_plain_68 eq_w_inf_plain_69
  have b_wzero := g2_wzero f f_w_zero f_s _ _ (by omega) (by omega) eq_w_zero_plain_70 eq_w_zero_plain_71
  have b_wfin := g2_wfin f f_w_fin f_mag f_s _ _ _ (by omega) (by omega) rfl eq_w_fin_plain_72
  have b_q := g2_q (f.w + f.p) _ (by omega) f_q f_w_nan f_w_inf f_w_zero f_w_fin (f_c_nan 0) (f_c_inf 0)
    (f_c_zero 0) (f_ovf 0) eq_q_plain_73
  rw [b_q, b_wnan, b_winf, b_wzero, b_wfin]
  exact g2_final f av bv (f_c_nan 0) (f_c_inf 0) (f_c_zero 0) (f_ovf 0) (f_s 0) _ b_cn b_ci b_cz b_s hdp

end Glue
end SvGolf.FdivParam

end D2Chain

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
theorem fdiv_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20) :
    CombDesign (design.sem W P) ∧ Acyclic (design.sem W P) ∧ SharedObl design.pdesign [W, P] := by
  sv_structure (rank := rippleRank
      (fun p =>
        if p ≤ 1 then 0 else if p = 2 then 1 else if p ≤ 6 then 0 else if p ≤ 12 then 1
        else if p ≤ 20 then 2 else if p ≤ 24 then 3 else if p ≤ 28 then 4 else if p ≤ 32 then 2 * P + 3
        else if p ≤ 34 then 2 * P + 4 else if p ≤ 37 then 4 * P + 9 else if p = 38 then 4 * P + 10
        else if p ≤ 48 then 0 else if p = 49 then 4 * P + 10 else if p ≤ 52 then 4 * P + 11
        else if p = 53 then 4 * P + 10 else if p = 54 then 0 else if p ≤ 56 then 6 * P + 14
        else if p = 57 then 6 * P + 15 else if p = 58 then 6 * P + 16 else if p = 59 then 6 * P + 15
        else if p = 60 then 6 * P + 17 else if p ≤ 63 then 3 else if p ≤ 66 then 0 else if p = 67 then 3
        else if p ≤ 69 then 0 else if p = 70 then 3 else if p = 71 then 0 else if p = 72 then 6 * P + 18
        else 6 * P + 19)
      (fun blk p i =>
        if blk = "norm" then (if p ≤ 1 then 5 + 2 * i.toNat else 6 + 2 * i.toNat)
        else if blk = "div" then (if p ≤ 1 then 2 * P + 5 + 2 * i.toNat else 2 * P + 6 + 2 * i.toNat)
        else if blk = "den" then (if p = 0 then 4 * P + 12 + 2 * i.toNat else 4 * P + 13 + 2 * i.toNat)
        else if blk = "efg" then 4 * P + 12
        else 0))
  all_goals (intros; sv_rowmajor; omega)

theorem fdiv_interface (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hR : W + P < 2 ^ 20)
    (hc : CombDesign (design.sem W P)) :
    (SvGolf.Tasks.FdivP.task W P).Interface 0 (design.sem W P) := by
  unfold SvGolf.Tasks.FdivP.task
  sv_interface

set_option maxHeartbeats 4000000 in
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
    have hch := SvGolf.FdivParam.Glue.chain2 ⟨W, P, hW, hP⟩ (st.boolAt "sa") (st.boolAt "a") (st.boolAt "sb") (st.boolAt "b") (st.boolAt "s") (st.boolAt "ea") (st.boolAt "eb") (st.boolAt "fa") (st.boolAt "fb") (st.boolAt "eall_a") (st.boolAt "eall_b") (st.boolAt "ez_a") (st.boolAt "ez_b") (st.boolAt "fz_a") (st.boolAt "fz_b") (st.boolAt "a_nan") (st.boolAt "b_nan") (st.boolAt "a_inf") (st.boolAt "b_inf") (st.boolAt "a_zero") (st.boolAt "b_zero") (st.boolAt "nza") (st.boolAt "nzb") (st.boolAt "ma") (st.boolAt "mb") (st.boolAt "xa") (st.boolAt "xb") (st.boolAt "na_r") (st.boolAt "nb_r") (st.boolAt "ya_r") (st.boolAt "yb_r") (st.boolAt "na4") (st.boolAt "nb4") (st.boolAt "ya") (st.boolAt "yb") (st.boolAt "nbx") (st.boolAt "rr") (st.boolAt "adj") (st.boolAt "qq") (st.boolAt "qm") (st.boolAt "rnz") (st.boolAt "st0") (st.boolAt "kv") (st.boolAt "nrmth") (st.boolAt "ovfth") (st.boolAt "eoff") (st.boolAt "ovf") (st.boolAt "nrm") (st.boolAt "e_r") (st.boolAt "q_r") (st.boolAt "t_r") (st.boolAt "qs") (st.boolAt "st1") (st.boolAt "rb") (st.boolAt "inc") (st.boolAt "efq") (st.boolAt "ef") (st.boolAt "mag") (st.boolAt "c_nan") (st.boolAt "c_inf") (st.boolAt "c_zero") (st.boolAt "w_nan") (st.boolAt "w_inf") (st.boolAt "w_zero") (st.boolAt "w_fin") (st.boolAt "q") (st.boolAt "za") (st.boolAt "zb") (st.boolAt "ge") (st.boolAt "dd") (st.boolAt "act") a.toNat b.toNat ha' hb'
      eq_sa_plain_0 eq_sb_plain_1 eq_s_plain_2 eq_ea_plain_3 eq_eb_plain_4 eq_fa_plain_5 eq_fb_plain_6 eq_eall_a_plain_7 eq_eall_b_plain_8 eq_ez_a_plain_9 eq_ez_b_plain_10 eq_fz_a_plain_11 eq_fz_b_plain_12 eq_a_nan_plain_13 eq_b_nan_plain_14 eq_a_inf_plain_15 eq_b_inf_plain_16 eq_a_zero_plain_17 eq_b_zero_plain_18 eq_nza_plain_19 eq_nzb_plain_20 eq_ma_plain_21 eq_mb_plain_22 eq_xa_plain_23 eq_xb_plain_24 eq_na_r_plain_25 eq_nb_r_plain_26 eq_ya_r_plain_27 eq_yb_r_plain_28 eq_na4_plain_29 eq_nb4_plain_30 eq_ya_plain_31 eq_yb_plain_32 eq_nbx_plain_33 eq_rr_plain_34 eq_adj_plain_35 eq_qm_plain_36 eq_rnz_plain_37 eq_st0_plain_38 eq_kv_plain_39 eq_kv_plain_40 eq_kv_plain_41 eq_kv_plain_42 eq_nrmth_plain_43 eq_nrmth_plain_44 eq_nrmth_plain_45 eq_ovfth_plain_46 eq_ovfth_plain_47 eq_ovfth_plain_48 eq_eoff_plain_49 eq_ovf_plain_50 eq_nrm_plain_51 eq_e_r_plain_52 eq_q_r_plain_53 eq_t_r_plain_54 eq_qs_plain_55 eq_st1_plain_56 eq_rb_plain_57 eq_inc_plain_58 eq_efq_plain_59 eq_mag_plain_60 eq_c_nan_plain_61 eq_c_inf_plain_62 eq_c_zero_plain_63 eq_w_nan_plain_64 eq_w_nan_plain_65 eq_w_nan_plain_66 eq_w_inf_plain_67 eq_w_inf_plain_68 eq_w_inf_plain_69 eq_w_zero_plain_70 eq_w_zero_plain_71 eq_w_fin_plain_72 eq_q_plain_73 eq_za_norm_0 eq_zb_norm_1 eq_na_r_norm_2 eq_nb_r_norm_3 eq_ya_r_norm_4 eq_yb_r_norm_5 eq_ge_div_0 eq_dd_div_1 eq_qq_div_2 eq_rr_div_3 eq_act_den_0 eq_e_r_den_1 eq_q_r_den_2 eq_t_r_den_3 eq_ef_efg_0 eq_w_nan_nanz_0
    have hval : XF.val (st.boolAt "q") (W + P) = (SvGolf.Tasks.FdivP.fdivBits W P a b).toNat :=
      hch.trans (SvGolf.FdivParam.OutN_fdivBits W P ⟨hW, hP⟩ a b)
    have hkq : ∀ k, k < W + P → KnownBit st "q" k := fun k hk => (known_q_plain_73 k (by omega)).2
    obtain ⟨vs, hvs, hvsw⟩ := (known_q_plain_73 0 (by omega)).1
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
