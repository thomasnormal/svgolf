import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_word.gen

theorem p_add_wide (N : Nat) (hN : 1 ≤ N) (st : SvState) (x y : BitVec N)
    (hc : CombDesign (add_wide.sem N)) (ha : Acyclic (add_wide.sem N))
    (heqs : CombEqs (add_wide.sem N) st) (hsh : StateShape (add_wide.sem N) st)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) : True := by
  sv_equations?
  all_goals trivial

theorem p_sub_wide (N : Nat) (hN : 1 ≤ N) (st : SvState) (x y : BitVec N)
    (hc : CombDesign (sub_wide.sem N)) (ha : Acyclic (sub_wide.sem N))
    (heqs : CombEqs (sub_wide.sem N) st) (hsh : StateShape (sub_wide.sem N) st)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) : True := by
  sv_equations?
  all_goals trivial

theorem p_add_same (N : Nat) (hN : 1 ≤ N) (st : SvState) (x y : BitVec N)
    (hc : CombDesign (add_same.sem N)) (ha : Acyclic (add_same.sem N))
    (heqs : CombEqs (add_same.sem N) st) (hsh : StateShape (add_same.sem N) st) : True := by
  sv_equations?
  all_goals trivial

theorem p_addw (N : Nat) (hN : 1 ≤ N) (st : SvState) (x y : BitVec N)
    (hc : CombDesign (addw.sem N)) (ha : Acyclic (addw.sem N))
    (heqs : CombEqs (addw.sem N) st) (hsh : StateShape (addw.sem N) st) : True := by
  sv_equations?
  all_goals trivial
