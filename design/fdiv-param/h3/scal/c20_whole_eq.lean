import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

load_sv c20_whole from "<scratchpad>/wph3/g0/chain/c20_whole.sv" (top := "c20_whole")

set_option maxHeartbeats 4000000 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (c20_whole.sem W P)) (ha : Acyclic (c20_whole.sem W P)) (st : SvState)
    (heqs : CombEqs (c20_whole.sem W P) st) (hsh : StateShape (c20_whole.sem W P) st) : True := by
  sv_equations
  trivial
