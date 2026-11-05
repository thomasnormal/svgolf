import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000

load_sv p18 from "<scratchpad>/wph3/g0/probes/p18_cmp_into_loop_mux.sv" (top := "p18_cmp_into_loop_mux")

theorem p18_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (p18.sem W P) ∧ Acyclic (p18.sem W P) := by
  sv_structure (rank := rippleRank
    (fun p => if p ≤ 1 then 0 else 2 * P + 10)
    (fun blk p i => if p = 3 then 2 * i.toNat + 2 else if p = 2 then 2 * i.toNat + 2 else 2 * i.toNat + 1))
  all_goals (intros; omega)

example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (p18.sem W P)) (ha : Acyclic (p18.sem W P)) (st : SvState)
    (heqs : CombEqs (p18.sem W P) st) (hsh : StateShape (p18.sem W P) st) : True := by
  sv_equations
  trivial
