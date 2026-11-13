import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Proof of `sbox_bp_d16.sv` for task `aes_sbox`: the depth-16 Boyar-Peralta netlist

The checker generates `Submission.Design` (`Submission.design`, `Submission.Goal`) and this file proves
`theorem Submission.solution : Submission.Goal` for the fixed-size S-box statement
(`SvGolf.Tasks.AesSbox.Statement`, i.e. `y = sbox x` for every known `x`). The design is
`tests/aes_sbox/baselines/sbox_bp_d16.sv`, unchanged: 125 continuous assigns over `^` and `&` (XNOR as
`a ^ b ^ 1'b1`), no generate loop, 117 internal one-bit nets. The task has no parameter (`inRange N := N = 0`),
so the one point is the whole range. The proof is the route of `tasks/aes_sbox/reference/sbox_bp.lean` (the 113-gate circuit)
(`PROVING.md`, section 12) with this netlist's tables: this file is generated from the netlist by
`tests/aes_sbox/validate/gen_d16_proof.py` (a copy of that proof's generator `gen_bp_proof.py` beside it, adapted to
this netlist; `--check` regenerates the file and compares); every line that mentions a gate number is a table.

## Route

1. **Structure** (`bp_struct`): `CombDesign` and `Acyclic` in one theorem, by `sv_structure`. The design has no
   parameter and no generate loop, so the tactic decides its four obligations (reads and windows in range, one
   driver per bit, rank decreases) as closed statements about the list of 125 sites. The rank is the gate's
   depth (`bpRank`).
2. **Ports** (`bp_interface`): `sv_interface`.
3. **Equations** (`solution`): `CombTask.satisfiedAt_of_comb`, then `sv_equations`, which hands over the 125
   equations and knownness facts under their stable names (`eq_<net>_<k>`, `known_<net>_<k>`; the nets
   `y[7], y[5], ...` are `eq_y_1 .. eq_y_8` in source order). `gok_chain` chains them into `GOK`. The design is a
   flat netlist (every site plain, no parameter), so `sv_equations` also decides its other obligations (in
   range, widths, bit reads, coverage of the reads) and returns only `inputsKnown`.
4. **Arithmetic**: the netlist is also a plain-Lean straight-line program (`bpProg`) whose environment is
   packed in one natural number (`runN`, one bit per net); the kernel evaluates it on all 256 inputs
   (`bp_correct`, GMP arithmetic on a 133-bit natural; no native-code decision procedure), and `bp_vals` (an
   induction over the gate list) says that a state meeting the gates' equations holds the program's values.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.AesSbox


/-! ## 0. The netlist as data (plain Lean)

The 125 gates of `sbox_bp_d16.sv`, in source order: gate `k` computes the value of environment
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

/-- The gates, in the order of the `assign`s of `sbox_bp_d16.sv` (`plain#k` is gate `k`). -/
def bpProg : List Gate :=
  [⟨.xor, 1, 3⟩, ⟨.xor, 4, 7⟩, ⟨.xor, 6, 5⟩, ⟨.xor, 0, 10⟩,
   ⟨.xor, 8, 9⟩, ⟨.xor, 6, 2⟩, ⟨.xor, 7, 1⟩, ⟨.xor, 8, 13⟩,
   ⟨.xor, 1, 11⟩, ⟨.xor, 4, 11⟩, ⟨.xor, 0, 12⟩, ⟨.xor, 12, 13⟩,
   ⟨.xor, 5, 2⟩, ⟨.xor, 10, 12⟩, ⟨.xor, 2, 14⟩, ⟨.xor, 7, 2⟩,
   ⟨.xor, 0, 15⟩, ⟨.xor, 1, 2⟩, ⟨.xor, 9, 25⟩, ⟨.xor, 11, 22⟩,
   ⟨.xor, 8, 20⟩, ⟨.xor, 7, 11⟩, ⟨.xor, 28, 12⟩, ⟨.xor, 28, 14⟩,
   ⟨.xor, 14, 26⟩, ⟨.xor, 23, 21⟩, ⟨.xor, 29, 24⟩, ⟨.and, 26, 12⟩,
   ⟨.and, 27, 18⟩, ⟨.xor, 19, 35⟩, ⟨.and, 17, 0⟩, ⟨.xor, 38, 35⟩,
   ⟨.and, 14, 28⟩, ⟨.and, 16, 11⟩, ⟨.xor, 31, 40⟩, ⟨.and, 29, 24⟩,
   ⟨.xor, 43, 40⟩, ⟨.and, 9, 15⟩, ⟨.and, 32, 30⟩, ⟨.xor, 46, 45⟩,
   ⟨.and, 23, 21⟩, ⟨.xor, 48, 45⟩, ⟨.xor, 37, 36⟩, ⟨.xor, 39, 33⟩,
   ⟨.xor, 42, 41⟩, ⟨.xor, 44, 49⟩, ⟨.xor, 50, 47⟩, ⟨.xor, 51, 49⟩,
   ⟨.xor, 52, 47⟩, ⟨.xor, 53, 34⟩, ⟨.xor, 56, 57⟩, ⟨.and, 56, 54⟩,
   ⟨.xor, 55, 59⟩, ⟨.xor, 54, 55⟩, ⟨.xor, 57, 59⟩, ⟨.and, 62, 61⟩,
   ⟨.and, 60, 58⟩, ⟨.and, 54, 57⟩, ⟨.and, 61, 65⟩, ⟨.xor, 61, 59⟩,
   ⟨.and, 55, 56⟩, ⟨.and, 58, 68⟩, ⟨.xor, 58, 59⟩, ⟨.xor, 55, 63⟩,
   ⟨.xor, 66, 67⟩, ⟨.xor, 57, 64⟩, ⟨.xor, 69, 70⟩, ⟨.xor, 72, 74⟩,
   ⟨.xor, 71, 73⟩, ⟨.xor, 71, 72⟩, ⟨.xor, 73, 74⟩, ⟨.xor, 76, 75⟩,
   ⟨.and, 78, 12⟩, ⟨.and, 74, 18⟩, ⟨.and, 73, 0⟩, ⟨.and, 77, 28⟩,
   ⟨.and, 72, 11⟩, ⟨.and, 71, 24⟩, ⟨.and, 76, 15⟩, ⟨.and, 79, 30⟩,
   ⟨.and, 75, 21⟩, ⟨.and, 78, 26⟩, ⟨.and, 74, 27⟩, ⟨.and, 73, 17⟩,
   ⟨.and, 77, 14⟩, ⟨.and, 72, 16⟩, ⟨.and, 71, 29⟩, ⟨.and, 76, 9⟩,
   ⟨.and, 79, 32⟩, ⟨.and, 75, 23⟩, ⟨.xor, 95, 96⟩, ⟨.xor, 84, 90⟩,
   ⟨.xor, 87, 98⟩, ⟨.xor, 89, 99⟩, ⟨.xor, 82, 92⟩, ⟨.xor, 80, 83⟩,
   ⟨.xor, 98, 103⟩, ⟨.xor, 81, 101⟩, ⟨.xor, 80, 86⟩, ⟨.xor, 85, 93⟩,
   ⟨.xor, 88, 94⟩, ⟨.xor, 82, 105⟩, ⟨.xor, 102, 108⟩, ⟨.xor, 91, 99⟩,
   ⟨.xor, 83, 86⟩, ⟨.xor, 101, 112⟩, ⟨.xor, 97, 110⟩, ⟨.xor, 95, 106⟩,
   ⟨.xor, 102, 107⟩, ⟨.xor, 100, 113⟩, ⟨.xnor, 114, 115⟩, ⟨.xor, 85, 98⟩,
   ⟨.xor, 104, 105⟩, ⟨.xor, 109, 119⟩, ⟨.xor, 84, 92⟩, ⟨.xor, 103, 111⟩,
   ⟨.xnor, 104, 116⟩, ⟨.xor, 88, 107⟩, ⟨.xor, 122, 125⟩, ⟨.xor, 84, 106⟩,
   ⟨.xnor, 100, 126⟩, ⟨.xor, 110, 123⟩, ⟨.xor, 100, 129⟩, ⟨.xor, 105, 127⟩,
   ⟨.xnor, 100, 131⟩]

/-- The signal bit each environment index stands for: `("x", i)` for the inputs, then the target of
each gate. -/
def bpLocs : List (String × Nat) :=
  [("x", 0), ("x", 1), ("x", 2), ("x", 3), ("x", 4), ("x", 5),
   ("x", 6), ("x", 7), ("T1", 0), ("T2", 0), ("T3", 0), ("T4", 0),
   ("T5", 0), ("T6", 0), ("T7", 0), ("T8", 0), ("T9", 0), ("T10", 0),
   ("T11", 0), ("T12", 0), ("T13", 0), ("T14", 0), ("T15", 0), ("T16", 0),
   ("T17", 0), ("T18", 0), ("T19", 0), ("T20", 0), ("T21", 0), ("T22", 0),
   ("T39", 0), ("T40", 0), ("T41", 0), ("T42", 0), ("T43", 0), ("T44", 0),
   ("T45", 0), ("T46", 0), ("T47", 0), ("T48", 0), ("T49", 0), ("T50", 0),
   ("T51", 0), ("T52", 0), ("T53", 0), ("T54", 0), ("T55", 0), ("T56", 0),
   ("T57", 0), ("T58", 0), ("T59", 0), ("T60", 0), ("T61", 0), ("T62", 0),
   ("T63", 0), ("T64", 0), ("T65", 0), ("T66", 0), ("T67", 0), ("T68", 0),
   ("T69", 0), ("T70", 0), ("T71", 0), ("T72", 0), ("T73", 0), ("T74", 0),
   ("T75", 0), ("T76", 0), ("T77", 0), ("T78", 0), ("T79", 0), ("T80", 0),
   ("T81", 0), ("T82", 0), ("T83", 0), ("T84", 0), ("T85", 0), ("T86", 0),
   ("T87", 0), ("T88", 0), ("T89", 0), ("T90", 0), ("T91", 0), ("T92", 0),
   ("T93", 0), ("T94", 0), ("T95", 0), ("T96", 0), ("T97", 0), ("T98", 0),
   ("T99", 0), ("T100", 0), ("T101", 0), ("T102", 0), ("T103", 0), ("T104", 0),
   ("T105", 0), ("T106", 0), ("T107", 0), ("T108", 0), ("T109", 0), ("T110", 0),
   ("T111", 0), ("T112", 0), ("T113", 0), ("T114", 0), ("T115", 0), ("T116", 0),
   ("T117", 0), ("T118", 0), ("T119", 0), ("T120", 0), ("T121", 0), ("T122", 0),
   ("T123", 0), ("T124", 0), ("T125", 0), ("y", 7), ("y", 5), ("T128", 0),
   ("y", 4), ("y", 3), ("T131", 0), ("T132", 0), ("y", 0), ("T134", 0),
   ("T135", 0), ("T136", 0), ("y", 1), ("T138", 0), ("y", 2), ("T140", 0),
   ("y", 6)]

/-- The gate driving `y[j]`. -/
def bpYGate : List Nat := [116, 120, 122, 113, 112, 110, 124, 109]

/-- The site depths: the rank of `sv_structure`. -/
def bpRank : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 3, 1, 3, 2, 1, 3, 1, 2, 3, 2, 3, 3, 3, 3, 4, 4, 3, 4, 4, 4, 5, 3, 4, 4, 4, 5, 3, 4, 5, 4, 5, 5, 6, 5, 6, 6, 7, 6, 7, 8, 7, 8, 8, 8, 9, 9, 8, 9, 9, 8, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 11, 11, 12, 11, 11, 12, 13, 12, 12, 11, 11, 12, 11, 11, 12, 13, 12, 14, 12, 15, 13, 13, 13, 15, 14, 13, 12, 13, 15, 14, 13, 13, 14, 15, 14, 14, 16, 16, 15, 16, 16, 13, 14, 16, 13, 14, 14, 16, 15, 16, 15, 16]

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

-- `decide` stops here with `maximum recursion depth has been reached` (the elaborator evaluates the instance on a
-- 125-element list; at 113 it fit); the kernel decides it.
theorem bp_len : bpProg.length = 125 := by decide +kernel

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
  have hy : ∀ j : Fin 8, bpYGate.getD j.val 0 < 125 := by decide
  have hy' : ∀ j, j < 8 → bpYGate.getD j 0 < 125 := fun j hj => hy ⟨j, hj⟩
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
/-- `gok_chain h₀ … h_124` proves `GOK P 0 bpProg` from the equations of the gates, in order: one
`GOK.cons` per name (the side conditions `g.a < 8 + k`, `g.b < 8 + k` by `decide`), then `GOK.nil`. -/
elab "gok_chain " hs:ident* : tactic => do
  for h in hs do
    evalTactic (← `(tactic| refine GOK.cons _ _ _ (by decide) (by decide) $h ?_))
  evalTactic (← `(tactic| exact GOK.nil _))

-- `solution` needs between 300 M and 400 M heartbeats (measured: a heartbeat timeout at 300 000, accepted at 400 000;
-- the default limit is 200 000).
set_option maxHeartbeats 1000000 in
/-- **The solution**: the `aes_sbox` statement for the depth-16 Boyar-Peralta netlist. -/
theorem solution : Goal := by
  obtain ⟨hc, ha⟩ := bp_struct
  refine CombTask.satisfiedAt_of_comb (bp_interface hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.AesSbox.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  sv_equations
  · obtain ⟨vs, hvs, hvsw⟩ := (known_y_3).1
    exact bp_out (fun i hi => SvState.boolAt_ofBitVec hv hi)
      (by gok_chain
        eq_T1_1 eq_T2_1 eq_T3_1 eq_T4_1 eq_T5_1 eq_T6_1
        eq_T7_1 eq_T8_1 eq_T9_1 eq_T10_1 eq_T11_1 eq_T12_1
        eq_T13_1 eq_T14_1 eq_T15_1 eq_T16_1 eq_T17_1 eq_T18_1
        eq_T19_1 eq_T20_1 eq_T21_1 eq_T22_1 eq_T39_1 eq_T40_1
        eq_T41_1 eq_T42_1 eq_T43_1 eq_T44_1 eq_T45_1 eq_T46_1
        eq_T47_1 eq_T48_1 eq_T49_1 eq_T50_1 eq_T51_1 eq_T52_1
        eq_T53_1 eq_T54_1 eq_T55_1 eq_T56_1 eq_T57_1 eq_T58_1
        eq_T59_1 eq_T60_1 eq_T61_1 eq_T62_1 eq_T63_1 eq_T64_1
        eq_T65_1 eq_T66_1 eq_T67_1 eq_T68_1 eq_T69_1 eq_T70_1
        eq_T71_1 eq_T72_1 eq_T73_1 eq_T74_1 eq_T75_1 eq_T76_1
        eq_T77_1 eq_T78_1 eq_T79_1 eq_T80_1 eq_T81_1 eq_T82_1
        eq_T83_1 eq_T84_1 eq_T85_1 eq_T86_1 eq_T87_1 eq_T88_1
        eq_T89_1 eq_T90_1 eq_T91_1 eq_T92_1 eq_T93_1 eq_T94_1
        eq_T95_1 eq_T96_1 eq_T97_1 eq_T98_1 eq_T99_1 eq_T100_1
        eq_T101_1 eq_T102_1 eq_T103_1 eq_T104_1 eq_T105_1 eq_T106_1
        eq_T107_1 eq_T108_1 eq_T109_1 eq_T110_1 eq_T111_1 eq_T112_1
        eq_T113_1 eq_T114_1 eq_T115_1 eq_T116_1 eq_T117_1 eq_T118_1
        eq_T119_1 eq_T120_1 eq_T121_1 eq_T122_1 eq_T123_1 eq_T124_1
        eq_T125_1 eq_y_1 eq_y_2 eq_T128_1 eq_y_3 eq_y_4
        eq_T131_1 eq_T132_1 eq_y_5 eq_T134_1 eq_T135_1 eq_T136_1
        eq_y_6 eq_T138_1 eq_y_7 eq_T140_1 eq_y_8)
      hvs hvsw (fun k hk => match k, hk with
        | 0, _ => (known_y_5).2
        | 1, _ => (known_y_6).2
        | 2, _ => (known_y_7).2
        | 3, _ => (known_y_4).2
        | 4, _ => (known_y_3).2
        | 5, _ => (known_y_2).2
        | 6, _ => (known_y_8).2
        | 7, _ => (known_y_1).2
        | k + 8, hk => absurd hk (by omega))
  case inputsKnown => exact inKnown_ofBitVec hv (by omega)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
