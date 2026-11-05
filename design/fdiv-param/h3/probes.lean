import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

/-! ## p01_base -/
load_sv p01_base from "<scratchpad>/wph3/g0/probes/p01_base.sv" (top := "p01_base")
example (W P : Nat) : CombDesign (p01_base.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p01_base.sem W P)) (ha : Acyclic (p01_base.sem W P)) (st : SvState)
    (heqs : CombEqs (p01_base.sem W P) st) (hsh : StateShape (p01_base.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p02_clog2 -/
load_sv p02_clog2 from "<scratchpad>/wph3/g0/probes/p02_clog2.sv" (top := "p02_clog2")
example (W P : Nat) : CombDesign (p02_clog2.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p02_clog2.sem W P)) (ha : Acyclic (p02_clog2.sem W P)) (st : SvState)
    (heqs : CombEqs (p02_clog2.sem W P) st) (hsh : StateShape (p02_clog2.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p03_rows -/
load_sv p03_rows from "<scratchpad>/wph3/g0/probes/p03_rows.sv" (top := "p03_rows")
example (W P : Nat) : CombDesign (p03_rows.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p03_rows.sem W P)) (ha : Acyclic (p03_rows.sem W P)) (st : SvState)
    (heqs : CombEqs (p03_rows.sem W P) st) (hsh : StateShape (p03_rows.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p04_genvar_shift -/
load_sv p04_genvar_shift from "<scratchpad>/wph3/g0/probes/p04_genvar_shift.sv" (top := "p04_genvar_shift")
example (W P : Nat) : CombDesign (p04_genvar_shift.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p04_genvar_shift.sem W P)) (ha : Acyclic (p04_genvar_shift.sem W P)) (st : SvState)
    (heqs : CombEqs (p04_genvar_shift.sem W P) st) (hsh : StateShape (p04_genvar_shift.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p05_pow2_localparam -/
load_sv p05_pow2_localparam from "<scratchpad>/wph3/g0/probes/p05_pow2_localparam.sv" (top := "p05_pow2_localparam")
example (W P : Nat) : CombDesign (p05_pow2_localparam.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p05_pow2_localparam.sem W P)) (ha : Acyclic (p05_pow2_localparam.sem W P)) (st : SvState)
    (heqs : CombEqs (p05_pow2_localparam.sem W P) st) (hsh : StateShape (p05_pow2_localparam.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p06_replication -/
load_sv p06_replication from "<scratchpad>/wph3/g0/probes/p06_replication.sv" (top := "p06_replication")
example (W P : Nat) : CombDesign (p06_replication.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p06_replication.sem W P)) (ha : Acyclic (p06_replication.sem W P)) (st : SvState)
    (heqs : CombEqs (p06_replication.sem W P) st) (hsh : StateShape (p06_replication.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p07_fill_windows -/
load_sv p07_fill_windows from "<scratchpad>/wph3/g0/probes/p07_fill_windows.sv" (top := "p07_fill_windows")
example (W P : Nat) : CombDesign (p07_fill_windows.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p07_fill_windows.sem W P)) (ha : Acyclic (p07_fill_windows.sem W P)) (st : SvState)
    (heqs : CombEqs (p07_fill_windows.sem W P) st) (hsh : StateShape (p07_fill_windows.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p08_reduce_cmp -/
load_sv p08_reduce_cmp from "<scratchpad>/wph3/g0/probes/p08_reduce_cmp.sv" (top := "p08_reduce_cmp")
example (W P : Nat) : CombDesign (p08_reduce_cmp.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p08_reduce_cmp.sem W P)) (ha : Acyclic (p08_reduce_cmp.sem W P)) (st : SvState)
    (heqs : CombEqs (p08_reduce_cmp.sem W P) st) (hsh : StateShape (p08_reduce_cmp.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p09_const_cmp -/
load_sv p09_const_cmp from "<scratchpad>/wph3/g0/probes/p09_const_cmp.sv" (top := "p09_const_cmp")
example (W P : Nat) : CombDesign (p09_const_cmp.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p09_const_cmp.sem W P)) (ha : Acyclic (p09_const_cmp.sem W P)) (st : SvState)
    (heqs : CombEqs (p09_const_cmp.sem W P) st) (hsh : StateShape (p09_const_cmp.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p10_genvar_value -/
load_sv p10_genvar_value from "<scratchpad>/wph3/g0/probes/p10_genvar_value.sv" (top := "p10_genvar_value")
example (W P : Nat) : CombDesign (p10_genvar_value.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p10_genvar_value.sem W P)) (ha : Acyclic (p10_genvar_value.sem W P)) (st : SvState)
    (heqs : CombEqs (p10_genvar_value.sem W P) st) (hsh : StateShape (p10_genvar_value.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p11_unsized_arith -/
load_sv p11_unsized_arith from "<scratchpad>/wph3/g0/probes/p11_unsized_arith.sv" (top := "p11_unsized_arith")
example (W P : Nat) : CombDesign (p11_unsized_arith.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p11_unsized_arith.sem W P)) (ha : Acyclic (p11_unsized_arith.sem W P)) (st : SvState)
    (heqs : CombEqs (p11_unsized_arith.sem W P) st) (hsh : StateShape (p11_unsized_arith.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p12_ternary_vec -/
load_sv p12_ternary_vec from "<scratchpad>/wph3/g0/probes/p12_ternary_vec.sv" (top := "p12_ternary_vec")
example (W P : Nat) : CombDesign (p12_ternary_vec.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p12_ternary_vec.sem W P)) (ha : Acyclic (p12_ternary_vec.sem W P)) (st : SvState)
    (heqs : CombEqs (p12_ternary_vec.sem W P) st) (hsh : StateShape (p12_ternary_vec.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p13_cond_generate -/
load_sv p13_cond_generate from "<scratchpad>/wph3/g0/probes/p13_cond_generate.sv" (top := "p13_cond_generate")
example (W P : Nat) : CombDesign (p13_cond_generate.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p13_cond_generate.sem W P)) (ha : Acyclic (p13_cond_generate.sem W P)) (st : SvState)
    (heqs : CombEqs (p13_cond_generate.sem W P) st) (hsh : StateShape (p13_cond_generate.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p14_unpacked -/
load_sv p14_unpacked from "<scratchpad>/wph3/g0/probes/p14_unpacked.sv" (top := "p14_unpacked")
example (W P : Nat) : CombDesign (p14_unpacked.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p14_unpacked.sem W P)) (ha : Acyclic (p14_unpacked.sem W P)) (st : SvState)
    (heqs : CombEqs (p14_unpacked.sem W P) st) (hsh : StateShape (p14_unpacked.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p15_bounds -/
load_sv p15_bounds from "<scratchpad>/wph3/g0/probes/p15_bounds.sv" (top := "p15_bounds")
example (W P : Nat) : CombDesign (p15_bounds.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p15_bounds.sem W P)) (ha : Acyclic (p15_bounds.sem W P)) (st : SvState)
    (heqs : CombEqs (p15_bounds.sem W P) st) (hsh : StateShape (p15_bounds.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p16_down_index -/
load_sv p16_down_index from "<scratchpad>/wph3/g0/probes/p16_down_index.sv" (top := "p16_down_index")
example (W P : Nat) : CombDesign (p16_down_index.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p16_down_index.sem W P)) (ha : Acyclic (p16_down_index.sem W P)) (st : SvState)
    (heqs : CombEqs (p16_down_index.sem W P) st) (hsh : StateShape (p16_down_index.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p17_shift_amount_param -/
load_sv p17_shift_amount_param from "<scratchpad>/wph3/g0/probes/p17_shift_amount_param.sv" (top := "p17_shift_amount_param")
example (W P : Nat) : CombDesign (p17_shift_amount_param.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p17_shift_amount_param.sem W P)) (ha : Acyclic (p17_shift_amount_param.sem W P)) (st : SvState)
    (heqs : CombEqs (p17_shift_amount_param.sem W P) st) (hsh : StateShape (p17_shift_amount_param.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p18_cmp_into_loop_mux -/
load_sv p18_cmp_into_loop_mux from "<scratchpad>/wph3/g0/probes/p18_cmp_into_loop_mux.sv" (top := "p18_cmp_into_loop_mux")
example (W P : Nat) : CombDesign (p18_cmp_into_loop_mux.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p18_cmp_into_loop_mux.sem W P)) (ha : Acyclic (p18_cmp_into_loop_mux.sem W P)) (st : SvState)
    (heqs : CombEqs (p18_cmp_into_loop_mux.sem W P) st) (hsh : StateShape (p18_cmp_into_loop_mux.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## p19_full_d1 -/
load_sv p19_full_d1 from "<scratchpad>/wph3/g0/probes/p19_full_d1.sv" (top := "p19_full_d1")
example (W P : Nat) : CombDesign (p19_full_d1.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (p19_full_d1.sem W P)) (ha : Acyclic (p19_full_d1.sem W P)) (st : SvState)
    (heqs : CombEqs (p19_full_d1.sem W P) st) (hsh : StateShape (p19_full_d1.sem W P) st) : True := by
  sv_equations?
  trivial
