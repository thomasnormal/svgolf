import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

/-! ## p20_cmp_lit -/
load_sv p20_cmp_lit from "<scratchpad>/wph3/g0/probes/p20_cmp_lit.sv" (top := "p20_cmp_lit")
example (W P : Nat) : CombDesign (p20_cmp_lit.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p20_cmp_lit.sem W P)) (ha : Acyclic (p20_cmp_lit.sem W P)) (st : SvState)
    (heqs : CombEqs (p20_cmp_lit.sem W P) st) (hsh : StateShape (p20_cmp_lit.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p21_cmp_param -/
load_sv p21_cmp_param from "<scratchpad>/wph3/g0/probes/p21_cmp_param.sv" (top := "p21_cmp_param")
example (W P : Nat) : CombDesign (p21_cmp_param.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p21_cmp_param.sem W P)) (ha : Acyclic (p21_cmp_param.sem W P)) (st : SvState)
    (heqs : CombEqs (p21_cmp_param.sem W P) st) (hsh : StateShape (p21_cmp_param.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p22_cmp_paramexpr -/
load_sv p22_cmp_paramexpr from "<scratchpad>/wph3/g0/probes/p22_cmp_paramexpr.sv" (top := "p22_cmp_paramexpr")
example (W P : Nat) : CombDesign (p22_cmp_paramexpr.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p22_cmp_paramexpr.sem W P)) (ha : Acyclic (p22_cmp_paramexpr.sem W P)) (st : SvState)
    (heqs : CombEqs (p22_cmp_paramexpr.sem W P) st) (hsh : StateShape (p22_cmp_paramexpr.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p23_add_param -/
load_sv p23_add_param from "<scratchpad>/wph3/g0/probes/p23_add_param.sv" (top := "p23_add_param")
example (W P : Nat) : CombDesign (p23_add_param.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p23_add_param.sem W P)) (ha : Acyclic (p23_add_param.sem W P)) (st : SvState)
    (heqs : CombEqs (p23_add_param.sem W P) st) (hsh : StateShape (p23_add_param.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p24_localparam_arith -/
load_sv p24_localparam_arith from "<scratchpad>/wph3/g0/probes/p24_localparam_arith.sv" (top := "p24_localparam_arith")
example (W P : Nat) : CombDesign (p24_localparam_arith.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p24_localparam_arith.sem W P)) (ha : Acyclic (p24_localparam_arith.sem W P)) (st : SvState)
    (heqs : CombEqs (p24_localparam_arith.sem W P) st) (hsh : StateShape (p24_localparam_arith.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p25_sized_localparam -/
load_sv p25_sized_localparam from "<scratchpad>/wph3/g0/probes/p25_sized_localparam.sv" (top := "p25_sized_localparam")
example (W P : Nat) : CombDesign (p25_sized_localparam.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p25_sized_localparam.sem W P)) (ha : Acyclic (p25_sized_localparam.sem W P)) (st : SvState)
    (heqs : CombEqs (p25_sized_localparam.sem W P) st) (hsh : StateShape (p25_sized_localparam.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p26_lit_vec_cmp -/
load_sv p26_lit_vec_cmp from "<scratchpad>/wph3/g0/probes/p26_lit_vec_cmp.sv" (top := "p26_lit_vec_cmp")
example (W P : Nat) : CombDesign (p26_lit_vec_cmp.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p26_lit_vec_cmp.sem W P)) (ha : Acyclic (p26_lit_vec_cmp.sem W P)) (st : SvState)
    (heqs : CombEqs (p26_lit_vec_cmp.sem W P) st) (hsh : StateShape (p26_lit_vec_cmp.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p27 structure with a valid W range -/
set_option profiler true
set_option profiler.threshold 300
load_sv p27 from "<scratchpad>/wph3/g0/probes/p27_div_family.sv" (top := "p27_div_family")

theorem p27_struct (W P : Nat) (hW : 3 ≤ W) (hP : 2 ≤ P) :
    CombDesign (p27.sem W P) ∧ Acyclic (p27.sem W P) := by
  sv_structure (rank := rippleRank
    (fun p => if p ≤ 1 then 0 else 2 * P + 10)
    (fun blk p i => if p = 3 then 2 * i.toNat + 2 else if p = 2 then 2 * i.toNat + 2 else 2 * i.toNat + 1))
  all_goals (intros; omega)
