import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 300

load_sv c10_whole from "<scratchpad>/wph3/g0/chain/c10_whole.sv" (top := "c10_whole")

set_option maxHeartbeats 1000000 in
theorem c10_whole_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c10_whole.sem W P) ∧ Acyclic (c10_whole.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p) (fun _ _ _ => 0))
  all_goals (intros; omega)

set_option maxHeartbeats 1000000 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (c10_whole.sem W P)) (ha : Acyclic (c10_whole.sem W P)) (st : SvState)
    (heqs : CombEqs (c10_whole.sem W P) st) (hsh : StateShape (c10_whole.sem W P) st) : True := by
  sv_equations
  trivial

load_sv c10_win from "<scratchpad>/wph3/g0/chain/c10_win.sv" (top := "c10_win")

set_option maxHeartbeats 1000000 in
theorem c10_win_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c10_win.sem W P) ∧ Acyclic (c10_win.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p / 2) (fun _ _ _ => 0))
  all_goals (intros; omega)

set_option maxHeartbeats 1000000 in
example (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hc : CombDesign (c10_win.sem W P)) (ha : Acyclic (c10_win.sem W P)) (st : SvState)
    (heqs : CombEqs (c10_win.sem W P) st) (hsh : StateShape (c10_win.sem W P) st) : True := by
  sv_equations
  trivial

load_sv c20_whole from "<scratchpad>/wph3/g0/chain/c20_whole.sv" (top := "c20_whole")

set_option maxHeartbeats 1000000 in
theorem c20_whole_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c20_whole.sem W P) ∧ Acyclic (c20_whole.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p) (fun _ _ _ => 0))
  all_goals (intros; omega)

load_sv c20_win from "<scratchpad>/wph3/g0/chain/c20_win.sv" (top := "c20_win")

set_option maxHeartbeats 1000000 in
theorem c20_win_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c20_win.sem W P) ∧ Acyclic (c20_win.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p / 2) (fun _ _ _ => 0))
  all_goals (intros; omega)
