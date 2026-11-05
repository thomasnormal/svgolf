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

set_option sv_comb.profile true

set_option maxHeartbeats 0 in
theorem d3_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (d3.sem W P) ∧ Acyclic (d3.sem W P) := by
  hb_measure (
    sv_structure (rank := rippleRank
      (fun p =>
        if p ≤ 2 then 0 else if p ≤ 9 then 1 else if p ≤ 11 then P + 1 else if p ≤ 13 then 3 * P + 6
        else if p = 14 then 0 else if p = 15 then 1 else if p = 16 then 3 * P + 7
        else if p ≤ 18 then 3 * P + 8 else if p = 19 then 3 * P + 9 else if p = 20 then 3 * P + 10
        else if p = 21 then 3 * P + 8 else if p = 22 then 3 * P + 11 else if p = 23 then 2
        else 3 * P + 12)
      (fun blk p i =>
        if blk = "norm" then 2 + i.toNat
        else if blk = "div" then (if p = 2 then P + 3 + 2 * i.toNat else P + 2 + 2 * i.toNat)
        else 3 * P + 12));
    all_goals (intros; sv_rowmajor; omega))

theorem d3_struct_default (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (d3.sem W P) ∧ Acyclic (d3.sem W P) := by
  (
    sv_structure (rank := rippleRank
      (fun p =>
        if p ≤ 2 then 0 else if p ≤ 9 then 1 else if p ≤ 11 then P + 1 else if p ≤ 13 then 3 * P + 6
        else if p = 14 then 0 else if p = 15 then 1 else if p = 16 then 3 * P + 7
        else if p ≤ 18 then 3 * P + 8 else if p = 19 then 3 * P + 9 else if p = 20 then 3 * P + 10
        else if p = 21 then 3 * P + 8 else if p = 22 then 3 * P + 11 else if p = 23 then 2
        else 3 * P + 12)
      (fun blk p i =>
        if blk = "norm" then 2 + i.toNat
        else if blk = "div" then (if p = 2 then P + 3 + 2 * i.toNat else P + 2 + 2 * i.toNat)
        else 3 * P + 12));
    all_goals (intros; sv_rowmajor; omega))
