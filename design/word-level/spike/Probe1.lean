import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_word.gen

theorem p_add_same (N : Nat) (hN : 1 ≤ N) :
    add_same.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x + y)) := by
  have hc : CombDesign (add_same.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (add_same.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations?
  all_goals sorry

theorem p_addw (N : Nat) (hN : 1 ≤ N) :
    addw.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  have hc : CombDesign (addw.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (addw.sem N) := by
    sv_structure (rank := rippleRank (fun p => [0, 1, 1].getD p 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations?
  all_goals sorry
