import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000

load_sv d2 from "<scratchpad>/wph3/g0/fdivp2.sv" (top := "fdiv")

example (W P : Nat) : CombDesign (d2.sem W P) := by
  sv_structure?

example (W P : Nat) (hc : CombDesign (d2.sem W P)) (ha : Acyclic (d2.sem W P)) (st : SvState)
    (heqs : CombEqs (d2.sem W P) st) (hsh : StateShape (d2.sem W P) st) : True := by
  sv_equations?
  trivial
