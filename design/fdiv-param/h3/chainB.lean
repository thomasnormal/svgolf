import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 300

load_sv c40_whole from "<scratchpad>/wph3/g0/chain/c40_whole.sv" (top := "c40_whole")

set_option maxHeartbeats 1000000 in
theorem c40_whole_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c40_whole.sem W P) ∧ Acyclic (c40_whole.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p) (fun _ _ _ => 0))
  all_goals (intros; omega)

load_sv c40_win from "<scratchpad>/wph3/g0/chain/c40_win.sv" (top := "c40_win")

set_option maxHeartbeats 1000000 in
theorem c40_win_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c40_win.sem W P) ∧ Acyclic (c40_win.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p / 2) (fun _ _ _ => 0))
  all_goals (intros; omega)
