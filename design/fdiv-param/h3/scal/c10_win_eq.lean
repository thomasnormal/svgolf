import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

load_sv c10_win from "<scratchpad>/wph3/g0/chain/c10_win.sv" (top := "c10_win")

set_option maxHeartbeats 4000000 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (c10_win.sem W P)) (ha : Acyclic (c10_win.sem W P)) (st : SvState)
    (heqs : CombEqs (c10_win.sem W P) st) (hsh : StateShape (c10_win.sem W P) st) : True := by
  sv_equations
  trivial
