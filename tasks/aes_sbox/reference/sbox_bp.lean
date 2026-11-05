import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Reference solution for task `aes_sbox`: the Boyar-Peralta 113-gate netlist

This is a submission file like any player's `Solution.lean`: the checker generates `Submission.Design`
(`Submission.design`, `Submission.Goal`) and this file proves `theorem Submission.solution : Submission.Goal`
for the fixed-size S-box statement (`SvGolf.Tasks.AesSbox.Statement`, i.e. `y = sbox x` for every known `x`).
The design is `reference/sbox_bp.sv`: 113 continuous assigns over `^` and `&` (XNOR as `a ^ b ^ 1'b1`),
no generate loop, 105 internal one-bit nets. This file is GENERATED from it by
`tests/aes_sbox/validate/gen_bp_proof.py` (`--check` regenerates it and compares); every line that
mentions a gate number is a table. `PROVING.md`, section "A flat 113-gate netlist", says what scaled and what did not.

## Route

1. **Structure** (`bp_struct`): `CombDesign` and `Acyclic` in one theorem, by `sv_structure`. The design has no
   parameter and no generate loop, so the tactic decides its four obligations (reads and windows in range, one
   driver per bit, rank decreases) as closed statements about the list of 113 sites instead of normalizing
   them. The rank is the gate's depth (`bpRank`).
2. **Ports** (`bp_interface`): `sv_interface`.
3. **Equations** (`solution`): `CombTask.satisfiedAt_of_comb`, then `sv_equations`, which hands over the 113
   equations and knownness facts under their stable names (`eq_<net>_<k>`, `known_<net>_<k>`; the nets
   `y[0] .. y[7]` are `eq_y_1 .. eq_y_8` in source order). `gok_chain` chains them into `GOK`. The design is a
   flat netlist (every site plain, no parameter), so `sv_equations` also DECIDES its other obligations (in
   range, widths, bit reads, and the coverage of all 221 reads) and returns only `inputsKnown`.
4. **Arithmetic**: the netlist is also a plain-Lean straight-line program (`bpProg`) whose environment is
   packed in one natural number (`runN`, one bit per net); the kernel evaluates it on all 256 inputs
   (`bp_correct`, GMP arithmetic on a 121-bit natural; no native-code decision procedure), and `bp_vals` (an induction over
   the gate list) says that a state meeting the gates' equations holds the program's values.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.AesSbox


/-! ## 0. The netlist as data (plain Lean)

The 113 gates of `reference/sbox_bp.sv`, in source order: gate `k` computes the value of environment
index `8 + k` from two earlier indices; indices `0 .. 7` are the input bits `x[0] .. x[7]`. -/

inductive GOp | xor | and | xnor

structure Gate where
  op : GOp
  a : Nat
  b : Nat

def evalGate : GOp → Bool → Bool → Bool
  | .xor, u, v => u ^^ v
  | .and, u, v => u && v
  | .xnor, u, v => u ^^ v ^^ true

/-- The gates, in the order of the `assign`s of `sbox_bp.sv` (`plain#k` is gate `k`). -/
def bpProg : List Gate :=
  [⟨.xor, 4, 2⟩, ⟨.xor, 7, 1⟩, ⟨.xor, 7, 4⟩, ⟨.xor, 7, 2⟩,
   ⟨.xor, 6, 5⟩, ⟨.xor, 12, 0⟩, ⟨.xor, 13, 4⟩, ⟨.xor, 9, 8⟩,
   ⟨.xor, 13, 7⟩, ⟨.xor, 13, 1⟩, ⟨.xor, 17, 11⟩, ⟨.xor, 3, 15⟩,
   ⟨.xor, 19, 2⟩, ⟨.xor, 19, 6⟩, ⟨.xor, 20, 0⟩, ⟨.xor, 20, 12⟩,
   ⟨.xor, 21, 10⟩, ⟨.xor, 0, 24⟩, ⟨.xor, 23, 24⟩, ⟨.xor, 23, 11⟩,
   ⟨.xor, 12, 24⟩, ⟨.xor, 9, 28⟩, ⟨.xor, 7, 28⟩, ⟨.and, 15, 20⟩,
   ⟨.and, 18, 22⟩, ⟨.xor, 32, 31⟩, ⟨.and, 14, 0⟩, ⟨.xor, 34, 31⟩,
   ⟨.and, 9, 28⟩, ⟨.and, 17, 13⟩, ⟨.xor, 37, 36⟩, ⟨.and, 16, 25⟩,
   ⟨.xor, 39, 36⟩, ⟨.and, 10, 24⟩, ⟨.and, 8, 26⟩, ⟨.xor, 42, 41⟩,
   ⟨.and, 11, 23⟩, ⟨.xor, 44, 41⟩, ⟨.xor, 33, 21⟩, ⟨.xor, 35, 45⟩,
   ⟨.xor, 38, 43⟩, ⟨.xor, 40, 45⟩, ⟨.xor, 46, 43⟩, ⟨.xor, 47, 27⟩,
   ⟨.xor, 48, 29⟩, ⟨.xor, 49, 30⟩, ⟨.xor, 50, 51⟩, ⟨.and, 50, 52⟩,
   ⟨.xor, 53, 55⟩, ⟨.and, 54, 56⟩, ⟨.xor, 57, 51⟩, ⟨.xor, 52, 53⟩,
   ⟨.xor, 51, 55⟩, ⟨.and, 60, 59⟩, ⟨.xor, 61, 53⟩, ⟨.xor, 52, 62⟩,
   ⟨.xor, 56, 62⟩, ⟨.and, 53, 64⟩, ⟨.xor, 65, 63⟩, ⟨.xor, 56, 65⟩,
   ⟨.and, 58, 67⟩, ⟨.xor, 54, 68⟩, ⟨.xor, 69, 66⟩, ⟨.xor, 58, 62⟩,
   ⟨.xor, 58, 69⟩, ⟨.xor, 62, 66⟩, ⟨.xor, 71, 70⟩, ⟨.and, 73, 20⟩,
   ⟨.and, 66, 22⟩, ⟨.and, 62, 0⟩, ⟨.and, 72, 28⟩, ⟨.and, 69, 13⟩,
   ⟨.and, 58, 25⟩, ⟨.and, 71, 24⟩, ⟨.and, 74, 26⟩, ⟨.and, 70, 23⟩,
   ⟨.and, 73, 15⟩, ⟨.and, 66, 18⟩, ⟨.and, 62, 14⟩, ⟨.and, 72, 9⟩,
   ⟨.and, 69, 17⟩, ⟨.and, 58, 16⟩, ⟨.and, 71, 10⟩, ⟨.and, 74, 8⟩,
   ⟨.and, 70, 11⟩, ⟨.xor, 90, 91⟩, ⟨.xor, 85, 93⟩, ⟨.xor, 84, 94⟩,
   ⟨.xor, 75, 77⟩, ⟨.xor, 76, 75⟩, ⟨.xor, 78, 79⟩, ⟨.xor, 87, 96⟩,
   ⟨.xor, 82, 98⟩, ⟨.xor, 83, 99⟩, ⟨.xor, 100, 101⟩, ⟨.xor, 98, 97⟩,
   ⟨.xor, 78, 80⟩, ⟨.xor, 88, 93⟩, ⟨.xor, 96, 104⟩, ⟨.xor, 95, 103⟩,
   ⟨.xor, 81, 100⟩, ⟨.xor, 89, 102⟩, ⟨.xor, 105, 106⟩, ⟨.xnor, 87, 110⟩,
   ⟨.xor, 90, 108⟩, ⟨.xor, 94, 86⟩, ⟨.xor, 95, 108⟩, ⟨.xnor, 102, 110⟩,
   ⟨.xor, 106, 107⟩, ⟨.xnor, 107, 108⟩, ⟨.xor, 109, 112⟩, ⟨.xnor, 118, 92⟩,
   ⟨.xor, 113, 109⟩]

/-- The signal bit each environment index stands for: `("x", i)` for the inputs, then the target of
each gate. -/
def bpLocs : List (String × Nat) :=
  [("x", 0), ("x", 1), ("x", 2), ("x", 3), ("x", 4), ("x", 5),
   ("x", 6), ("x", 7), ("y14", 0), ("y13", 0), ("y9", 0), ("y8", 0),
   ("t0", 0), ("y1", 0), ("y4", 0), ("y12", 0), ("y2", 0), ("y5", 0),
   ("y3", 0), ("t1", 0), ("y15", 0), ("y20", 0), ("y6", 0), ("y10", 0),
   ("y11", 0), ("y7", 0), ("y17", 0), ("y19", 0), ("y16", 0), ("y21", 0),
   ("y18", 0), ("t2", 0), ("t3", 0), ("t4", 0), ("t5", 0), ("t6", 0),
   ("t7", 0), ("t8", 0), ("t9", 0), ("t10", 0), ("t11", 0), ("t12", 0),
   ("t13", 0), ("t14", 0), ("t15", 0), ("t16", 0), ("t17", 0), ("t18", 0),
   ("t19", 0), ("t20", 0), ("t21", 0), ("t22", 0), ("t23", 0), ("t24", 0),
   ("t25", 0), ("t26", 0), ("t27", 0), ("t28", 0), ("t29", 0), ("t30", 0),
   ("t31", 0), ("t32", 0), ("t33", 0), ("t34", 0), ("t35", 0), ("t36", 0),
   ("t37", 0), ("t38", 0), ("t39", 0), ("t40", 0), ("t41", 0), ("t42", 0),
   ("t43", 0), ("t44", 0), ("t45", 0), ("z0", 0), ("z1", 0), ("z2", 0),
   ("z3", 0), ("z4", 0), ("z5", 0), ("z6", 0), ("z7", 0), ("z8", 0),
   ("z9", 0), ("z10", 0), ("z11", 0), ("z12", 0), ("z13", 0), ("z14", 0),
   ("z15", 0), ("z16", 0), ("z17", 0), ("tc1", 0), ("tc2", 0), ("tc3", 0),
   ("tc4", 0), ("tc5", 0), ("tc6", 0), ("tc7", 0), ("tc8", 0), ("tc9", 0),
   ("tc10", 0), ("tc11", 0), ("tc12", 0), ("tc13", 0), ("tc14", 0), ("y", 4),
   ("tc16", 0), ("tc17", 0), ("tc18", 0), ("y", 0), ("tc20", 0), ("tc21", 0),
   ("y", 7), ("y", 1), ("y", 3), ("y", 6), ("tc26", 0), ("y", 5),
   ("y", 2)]

/-- The gate driving `y[j]`. -/
def bpYGate : List Nat := [103, 107, 112, 108, 99, 111, 109, 106]

/-- The site depths: the rank of `sv_structure`. -/
def bpRank : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 4, 3, 4, 4, 5, 5, 5, 6, 6, 6, 6, 7, 7, 5, 6, 7, 4, 6, 7, 4, 8, 7, 8, 6, 7, 8, 6, 7, 8, 8, 9, 9, 9, 9, 10, 10, 10, 11, 12, 13, 14, 11, 12, 13, 14, 15, 15, 16, 17, 17, 18, 19, 20, 15, 20, 18, 21, 19, 18, 15, 21, 20, 15, 16, 22, 21, 19, 18, 15, 21, 20, 15, 16, 22, 21, 23, 24, 25, 20, 20, 22, 22, 23, 23, 24, 23, 22, 24, 23, 26, 24, 25, 25, 26, 25, 25, 26, 26, 27, 27, 26, 27, 26]

/-! ## 1. Structure -/

/-- `CombDesign` and `Acyclic` of the netlist, with the rank `bpRank` (site `k` is gate `k`). -/
theorem bp_struct : CombDesign design.sem ∧ Acyclic design.sem := by
  sv_structure (rank := rippleRank (fun p => bpRank.getD p 0) (fun _ _ _ => 0))

/-! ## 2. The ports -/

/-- The task's interface: exactly the ports `x` (8 bits in) and `y` (8 bits out). -/
theorem bp_interface (hc : CombDesign design.sem) : task.Interface 0 design.sem := by
  sv_interface


/-- The packed environment after `gs` (starting at gate number `k`): bit `i` of the result is the
value of environment index `i`. -/
def stepN (e k : Nat) (g : Gate) : Nat :=
  if evalGate g.op (e.testBit g.a) (e.testBit g.b) then e ||| 2 ^ (8 + k) else e

def runN : Nat → List Gate → Nat → Nat
  | _, [], e => e
  | k, g :: gs, e => runN (k + 1) gs (stepN e k g)

/-- The gates of `gs` (numbered from `k`) read only earlier indices, and `P` satisfies each gate's
equation. -/
inductive GOK (P : Nat → Bool) : Nat → List Gate → Prop
  | nil (k : Nat) : GOK P k []
  | cons (k : Nat) (g : Gate) (gs : List Gate) (ha : g.a < 8 + k) (hb : g.b < 8 + k)
      (hp : P (8 + k) = evalGate g.op (P g.a) (P g.b)) (h : GOK P (k + 1) gs) : GOK P k (g :: gs)

theorem testBit_stepN (e k : Nat) (g : Gate) (i : Nat) :
    (stepN e k g).testBit i =
      (e.testBit i || (decide (8 + k = i) && evalGate g.op (e.testBit g.a) (e.testBit g.b))) := by
  unfold stepN
  by_cases h : evalGate g.op (e.testBit g.a) (e.testBit g.b) = true
  · simp [h, Nat.testBit_or, Nat.testBit_two_pow]
  · simp at h
    simp [h]

theorem runN_inv (P : Nat → Bool) : ∀ (gs : List Gate) (k e : Nat), GOK P k gs →
    (∀ i, i < 8 + k → P i = e.testBit i) → (∀ i, 8 + k ≤ i → e.testBit i = false) →
    ∀ i, i < 8 + k + gs.length → P i = (runN k gs e).testBit i := by
  intro gs
  induction gs with
  | nil =>
    intro k e _ h1 _ i hi
    exact h1 i (by simpa using hi)
  | cons g gs ih =>
    intro k e hgok h1 h2 i hi
    cases hgok with
    | cons _ _ _ ha hb hp hrest =>
      have hstep : ∀ i, i < 8 + (k + 1) → P i = (stepN e k g).testBit i := by
        intro i hi
        rw [testBit_stepN]
        by_cases hik : i = 8 + k
        · subst hik
          rw [h2 _ (Nat.le_refl _)]
          simp [hp, h1 _ ha, h1 _ hb]
        · have hlt : i < 8 + k := by omega
          have hne : ¬ (8 + k = i) := fun h => hik h.symm
          simp [hne, h1 i hlt]
      have hzero : ∀ i, 8 + (k + 1) ≤ i → (stepN e k g).testBit i = false := by
        intro i hi
        rw [testBit_stepN]
        have hne : ¬ (8 + k = i) := by omega
        simp [hne, h2 i (by omega)]
      exact ih (k + 1) (stepN e k g) hrest hstep hzero i (by simp at hi ⊢; omega)

/-- **The environment of the netlist, from the equations.** If `P` agrees with the input bits of
`x` and satisfies every gate's equation, then at every environment index it is the packed
program's value. -/
theorem bp_vals (P : Nat → Bool) (x : BitVec 8) (hin : ∀ i, i < 8 → P i = x.getLsbD i)
    (hg : GOK P 0 bpProg) : ∀ i, i < 8 + bpProg.length → P i = (runN 0 bpProg x.toNat).testBit i := by
  intro i hi
  refine runN_inv P bpProg 0 x.toNat hg (fun i hi => ?_) (fun i hi => ?_) i (by omega)
  · rw [BitVec.testBit_toNat]; exact hin i (by omega)
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

/-- **The S-box, by evaluation**: on each of the 256 inputs, the packed program's outputs are the algebraic
`sbox` (kernel evaluation of a closed function; no native-code decision procedure). -/
theorem bp_correct : ∀ n : Fin 256, ∀ j : Fin 8,
    (runN 0 bpProg n.val).testBit (8 + bpYGate.getD j.val 0) =
      (sbox (BitVec.ofFin n)).getLsbD j.val := by
  decide +kernel

/-- The environment indices of the outputs are the bits of `y`; those of the inputs are the bits of `x`. -/
theorem bp_locs_y : ∀ j : Fin 8, bpLocs.getD (8 + bpYGate.getD j.val 0) ("", 0) = ("y", j.val) := by decide

theorem bp_locs_x : ∀ i : Fin 8, bpLocs.getD i.val ("", 0) = ("x", i.val) := by decide

theorem bp_len : bpProg.length = 113 := by decide

/-- **From the equations to the outputs.** `hx`: the state's `x` bits are those of `x`; `hg`: the state meets
every gate's equation; `hs`, `hsw`, `hks`: `y` is a known 8-bit vector. Then `y = sbox x`. -/
theorem bp_out {st : SvState} {x : BitVec 8}
    (hx : ∀ i, i < 8 → st.boolAt "x" i = x.getLsbD i)
    (hg : GOK (fun i => st.boolAt (bpLocs.getD i ("", 0)).1 (bpLocs.getD i ("", 0)).2) 0 bpProg)
    {vs : LVec} (hs : SvState.lookup st "y" = some vs) (hsw : vs.width = 8)
    (hks : ∀ k, k < 8 → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (sbox x)) := by
  have hvals := bp_vals _ x (fun i hi => by rw [bp_locs_x ⟨i, hi⟩]; exact hx i hi) hg
  have hvs := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  rw [hvs] at hs
  have hy : ∀ j : Fin 8, bpYGate.getD j.val 0 < 113 := by decide
  have hy' : ∀ j, j < 8 → bpYGate.getD j 0 < 113 := fun j hj => hy ⟨j, hj⟩
  have heq : XF.bv 8 (st.boolAt "y") = sbox x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [XF.getLsbD_bv hj]
    have h1 := hvals (8 + bpYGate.getD j 0) (by have := hy' j hj; rw [bp_len]; omega)
    rw [bp_locs_y ⟨j, hj⟩] at h1
    simp only at h1
    rw [h1]
    simpa using bp_correct x.toFin ⟨j, hj⟩
  rw [hs, heq]
/-! ## 4. The statement -/

open Lean Elab Tactic in
/-- `gok_chain h₀ … h₁₁₂` proves `GOK P 0 bpProg` from the equations of the gates, in order: one
`GOK.cons` per name (the side conditions `g.a < 8 + k`, `g.b < 8 + k` by `decide`), then `GOK.nil`. -/
elab "gok_chain " hs:ident* : tactic => do
  for h in hs do
    evalTactic (← `(tactic| refine GOK.cons _ _ _ (by decide) (by decide) $h ?_))
  evalTactic (← `(tactic| exact GOK.nil _))

-- `solution` takes about 400 M heartbeats (the default limit is 200 M): `sv_equations` 276 M, the rest 125 M.
set_option maxHeartbeats 1000000 in
/-- **The reference solution**: the `aes_sbox` statement for the Boyar-Peralta netlist. -/
theorem solution : Goal := by
  obtain ⟨hc, ha⟩ := bp_struct
  refine CombTask.satisfiedAt_of_comb (bp_interface hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.AesSbox.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  sv_equations
  · obtain ⟨vs, hvs, hvsw⟩ := (known_y_1).1
    exact bp_out (fun i hi => SvState.boolAt_ofBitVec hv hi)
      (by gok_chain
        eq_y14_1 eq_y13_1 eq_y9_1 eq_y8_1 eq_t0_1 eq_y1_1
        eq_y4_1 eq_y12_1 eq_y2_1 eq_y5_1 eq_y3_1 eq_t1_1
        eq_y15_1 eq_y20_1 eq_y6_1 eq_y10_1 eq_y11_1 eq_y7_1
        eq_y17_1 eq_y19_1 eq_y16_1 eq_y21_1 eq_y18_1 eq_t2_1
        eq_t3_1 eq_t4_1 eq_t5_1 eq_t6_1 eq_t7_1 eq_t8_1
        eq_t9_1 eq_t10_1 eq_t11_1 eq_t12_1 eq_t13_1 eq_t14_1
        eq_t15_1 eq_t16_1 eq_t17_1 eq_t18_1 eq_t19_1 eq_t20_1
        eq_t21_1 eq_t22_1 eq_t23_1 eq_t24_1 eq_t25_1 eq_t26_1
        eq_t27_1 eq_t28_1 eq_t29_1 eq_t30_1 eq_t31_1 eq_t32_1
        eq_t33_1 eq_t34_1 eq_t35_1 eq_t36_1 eq_t37_1 eq_t38_1
        eq_t39_1 eq_t40_1 eq_t41_1 eq_t42_1 eq_t43_1 eq_t44_1
        eq_t45_1 eq_z0_1 eq_z1_1 eq_z2_1 eq_z3_1 eq_z4_1
        eq_z5_1 eq_z6_1 eq_z7_1 eq_z8_1 eq_z9_1 eq_z10_1
        eq_z11_1 eq_z12_1 eq_z13_1 eq_z14_1 eq_z15_1 eq_z16_1
        eq_z17_1 eq_tc1_1 eq_tc2_1 eq_tc3_1 eq_tc4_1 eq_tc5_1
        eq_tc6_1 eq_tc7_1 eq_tc8_1 eq_tc9_1 eq_tc10_1 eq_tc11_1
        eq_tc12_1 eq_tc13_1 eq_tc14_1 eq_y_1 eq_tc16_1 eq_tc17_1
        eq_tc18_1 eq_y_2 eq_tc20_1 eq_tc21_1 eq_y_3 eq_y_4
        eq_y_5 eq_y_6 eq_tc26_1 eq_y_7 eq_y_8)
      hvs hvsw (fun k hk => match k, hk with
        | 0, _ => (known_y_2).2
        | 1, _ => (known_y_4).2
        | 2, _ => (known_y_8).2
        | 3, _ => (known_y_5).2
        | 4, _ => (known_y_1).2
        | 5, _ => (known_y_7).2
        | 6, _ => (known_y_6).2
        | 7, _ => (known_y_3).2
        | k + 8, hk => absurd hk (by omega))
  case inputsKnown => exact inKnown_ofBitVec hv (by omega)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
