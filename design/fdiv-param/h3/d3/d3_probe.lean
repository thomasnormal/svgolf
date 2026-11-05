import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

load_sv d3 from "<scratchpad>/wph3/d3/fdivp3.sv" (top := "fdiv")
example (W P : Nat) : CombDesign (d3.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (d3.sem W P)) (ha : Acyclic (d3.sem W P)) (st : SvState)
    (heqs : CombEqs (d3.sem W P) st) (hsh : StateShape (d3.sem W P) st) : True := by
  sv_equations?
  trivial
