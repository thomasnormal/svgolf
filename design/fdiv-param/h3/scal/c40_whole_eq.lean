import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

load_sv c40_whole from "<scratchpad>/wph3/g0/chain/c40_whole.sv" (top := "c40_whole")

set_option maxHeartbeats 4000000 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (c40_whole.sem W P)) (ha : Acyclic (c40_whole.sem W P)) (st : SvState)
    (heqs : CombEqs (c40_whole.sem W P) st) (hsh : StateShape (c40_whole.sem W P) st) : True := by
  sv_equations
  trivial
