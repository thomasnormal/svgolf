import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

load_sv c20_win from "<scratchpad>/wph3/g0/chain/c20_win.sv" (top := "c20_win")

set_option maxHeartbeats 4000000 in
theorem c20_win_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (c20_win.sem W P) ∧ Acyclic (c20_win.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p / 2) (fun _ _ _ => 0))
  all_goals (intros; omega)
