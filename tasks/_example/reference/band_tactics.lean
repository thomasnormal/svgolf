import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic

/-!
# Reference solution for task `_example`, proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. The design is `reference/band_tactics.sv`, byte for byte `reference/band.sv`
(`assign y = a & b;`); `reference/band.lean` proves the same statement with no tactic, in about four
times as many code lines. The route is the one of the first real task's proof
(`tasks/add/reference/add_n.lean`):

1. **Structure** (`band_struct`): `sv_structure` proves `CombDesign` and `Acyclic` of `design.sem N`
   and returns small arithmetic goals, each closed by `intros; omega`. The rank is 0 for every site:
   the one assign reads only the inputs.
2. **Ports** (`band_interface`): `sv_interface` proves the port names, order and widths.
3. **Equations** (in `solution`): `CombTask.satisfiedAt_of_comb` reduces the statement to one
   settled state; `sv_equations` states the assign as an equation over `Bool`, bit by bit
   (`eq_y_1 k`: bit `k` of `y` is the AND of bit `k` of `a` and of `b`), the knownness of `y`
   (`known_y_1`) and the obligations it does not discharge, closed by the same `first` list as in
   `add_n.lean`. The arithmetic is the first bullet: `y` is the vector of its known bits
   (`SvState.lookup_eq_ofBitVec_bv`), and bit `k` of that vector is the AND of the inputs' bits.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq SvGolf

/-! ## 1. Structure: `sv_structure` -/

theorem band_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-! ## 2. The ports (the task's `Interface`) -/

theorem band_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Example.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The statement -/

/-- **The reference solution**: the `_example` statement, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := band_struct N hN'
  refine CombTask.satisfiedAt_of_comb (band_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, z, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Example.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    rw [hvy, SvState.lookup_eq_ofBitVec_bv hvy (W := N) (by omega)
      (fun k hk => (known_y_1 k (by omega)).2)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, eq_y_1 k (by omega)]
    simp [SvState.boolAt_ofBitVec hA, SvState.boolAt_ofBitVec hB, hk]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
