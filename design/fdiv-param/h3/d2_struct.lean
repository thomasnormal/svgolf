import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 2000

load_sv d2 from "<scratchpad>/wph3/g0/fdivp2.sv" (top := "fdiv")

set_option maxHeartbeats 4000000 in
theorem d2_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) :
    CombDesign (d2.sem W P) ∧ Acyclic (d2.sem W P) := by
  sv_structure (rank := rippleRank
    (fun p =>
      if p ≤ 1 then 0 else if p = 2 then 1 else if p ≤ 6 then 0 else if p ≤ 12 then 1
      else if p ≤ 20 then 2 else if p ≤ 24 then 3 else if p ≤ 28 then 4
      else if p ≤ 32 then 3 * P + 1 else if p ≤ 34 then 3 * P + 2
      else if p ≤ 37 then 5 * P + 7 else if p = 38 then 5 * P + 8
      else if p ≤ 48 then 0 else if p = 49 then 5 * P + 8 else if p ≤ 52 then 5 * P + 9
      else if p = 53 then 5 * P + 8 else if p = 54 then 0
      else if p ≤ 56 then 7 * P + 12 else if p = 57 then 7 * P + 13 else if p = 58 then 7 * P + 14
      else if p = 59 then 7 * P + 13 else if p = 60 then 7 * P + 15
      else if p ≤ 63 then 3 else if p ≤ 66 then 0 else if p = 67 then 2 else if p ≤ 69 then 0
      else if p = 70 then 2 else if p = 71 then 0 else if p = 72 then 7 * P + 16 else 7 * P + 17)
    (fun blk p i =>
      if blk = "norm" then (if p ≤ 1 then 5 + 3 * i.toNat else 6 + 3 * i.toNat)
      else if blk = "div" then (if p ≤ 1 then 3 * P + 3 + 2 * i.toNat else 3 * P + 4 + 2 * i.toNat)
      else if blk = "den" then (if p = 0 then 5 * P + 10 + 2 * i.toNat else 5 * P + 11 + 2 * i.toNat)
      else if blk = "efg" then 5 * P + 10
      else 0))
  all_goals (intros; omega)
