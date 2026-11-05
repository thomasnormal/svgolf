import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

open Lean Elab Tactic in
/-- run a tactic sequence and log the heartbeats it consumed, in the unit of `maxHeartbeats` (thousands) -/
elab "hb_measure " t:tacticSeq : tactic => do
  let a ← IO.getNumHeartbeats
  evalTactic t
  let b ← IO.getNumHeartbeats
  logInfo m!"HEARTBEATS {(b - a) / 1000}"

load_sv d3 from "<scratchpad>/wph3/d3/fdivp3.sv" (top := "fdiv")

set_option maxHeartbeats 0 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (d3.sem W P)) (ha : Acyclic (d3.sem W P))
    (st : SvState) (heqs : CombEqs (d3.sem W P) st) (hsh : StateShape (d3.sem W P) st) : True := by
  hb_measure (sv_equations?)
  trivial

set_option maxHeartbeats 0 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (d3.sem W P)) (ha : Acyclic (d3.sem W P))
    (st : SvState) (heqs : CombEqs (d3.sem W P) st) (hsh : StateShape (d3.sem W P) st) : True := by
  hb_measure (sv_equations)
  trivial
