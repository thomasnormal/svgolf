import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
set_option maxRecDepth 100000

/-! ## q01_red_in_bitwise -/
load_sv q01_red_in_bitwise from "<scratchpad>/wph3/d3/probes3/q01_red_in_bitwise.sv" (top := "q01_red_in_bitwise")
example (W P : Nat) : CombDesign (q01_red_in_bitwise.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q01_red_in_bitwise.sem W P)) (ha : Acyclic (q01_red_in_bitwise.sem W P)) (st : SvState)
    (heqs : CombEqs (q01_red_in_bitwise.sem W P) st) (hsh : StateShape (q01_red_in_bitwise.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q02_cmp_in_bitwise -/
load_sv q02_cmp_in_bitwise from "<scratchpad>/wph3/d3/probes3/q02_cmp_in_bitwise.sv" (top := "q02_cmp_in_bitwise")
example (W P : Nat) : CombDesign (q02_cmp_in_bitwise.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q02_cmp_in_bitwise.sem W P)) (ha : Acyclic (q02_cmp_in_bitwise.sem W P)) (st : SvState)
    (heqs : CombEqs (q02_cmp_in_bitwise.sem W P) st) (hsh : StateShape (q02_cmp_in_bitwise.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q03_shift_cmp_wide -/
load_sv q03_shift_cmp_wide from "<scratchpad>/wph3/d3/probes3/q03_shift_cmp_wide.sv" (top := "q03_shift_cmp_wide")
example (W P : Nat) : CombDesign (q03_shift_cmp_wide.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q03_shift_cmp_wide.sem W P)) (ha : Acyclic (q03_shift_cmp_wide.sem W P)) (st : SvState)
    (heqs : CombEqs (q03_shift_cmp_wide.sem W P) st) (hsh : StateShape (q03_shift_cmp_wide.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q04_const_left_sub -/
load_sv q04_const_left_sub from "<scratchpad>/wph3/d3/probes3/q04_const_left_sub.sv" (top := "q04_const_left_sub")
example (W P : Nat) : CombDesign (q04_const_left_sub.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q04_const_left_sub.sem W P)) (ha : Acyclic (q04_const_left_sub.sem W P)) (st : SvState)
    (heqs : CombEqs (q04_const_left_sub.sem W P) st) (hsh : StateShape (q04_const_left_sub.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q05_fill_arm -/
load_sv q05_fill_arm from "<scratchpad>/wph3/d3/probes3/q05_fill_arm.sv" (top := "q05_fill_arm")
example (W P : Nat) : CombDesign (q05_fill_arm.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q05_fill_arm.sem W P)) (ha : Acyclic (q05_fill_arm.sem W P)) (st : SvState)
    (heqs : CombEqs (q05_fill_arm.sem W P) st) (hsh : StateShape (q05_fill_arm.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q06_zero_arm -/
load_sv q06_zero_arm from "<scratchpad>/wph3/d3/probes3/q06_zero_arm.sv" (top := "q06_zero_arm")
example (W P : Nat) : CombDesign (q06_zero_arm.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q06_zero_arm.sem W P)) (ha : Acyclic (q06_zero_arm.sem W P)) (st : SvState)
    (heqs : CombEqs (q06_zero_arm.sem W P) st) (hsh : StateShape (q06_zero_arm.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q07_wide_shift -/
load_sv q07_wide_shift from "<scratchpad>/wph3/d3/probes3/q07_wide_shift.sv" (top := "q07_wide_shift")
example (W P : Nat) : CombDesign (q07_wide_shift.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q07_wide_shift.sem W P)) (ha : Acyclic (q07_wide_shift.sem W P)) (st : SvState)
    (heqs : CombEqs (q07_wide_shift.sem W P) st) (hsh : StateShape (q07_wide_shift.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q08_not_plus_const -/
load_sv q08_not_plus_const from "<scratchpad>/wph3/d3/probes3/q08_not_plus_const.sv" (top := "q08_not_plus_const")
example (W P : Nat) : CombDesign (q08_not_plus_const.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q08_not_plus_const.sem W P)) (ha : Acyclic (q08_not_plus_const.sem W P)) (st : SvState)
    (heqs : CombEqs (q08_not_plus_const.sem W P) st) (hsh : StateShape (q08_not_plus_const.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q09_red_concat_part -/
load_sv q09_red_concat_part from "<scratchpad>/wph3/d3/probes3/q09_red_concat_part.sv" (top := "q09_red_concat_part")
example (W P : Nat) : CombDesign (q09_red_concat_part.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q09_red_concat_part.sem W P)) (ha : Acyclic (q09_red_concat_part.sem W P)) (st : SvState)
    (heqs : CombEqs (q09_red_concat_part.sem W P) st) (hsh : StateShape (q09_red_concat_part.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q10_cmp_bit_target_family -/
load_sv q10_cmp_bit_target_family from "<scratchpad>/wph3/d3/probes3/q10_cmp_bit_target_family.sv" (top := "q10_cmp_bit_target_family")
example (W P : Nat) : CombDesign (q10_cmp_bit_target_family.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q10_cmp_bit_target_family.sem W P)) (ha : Acyclic (q10_cmp_bit_target_family.sem W P)) (st : SvState)
    (heqs : CombEqs (q10_cmp_bit_target_family.sem W P) st) (hsh : StateShape (q10_cmp_bit_target_family.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q11_inline_mag -/
load_sv q11_inline_mag from "<scratchpad>/wph3/d3/probes3/q11_inline_mag.sv" (top := "q11_inline_mag")
example (W P : Nat) : CombDesign (q11_inline_mag.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q11_inline_mag.sem W P)) (ha : Acyclic (q11_inline_mag.sem W P)) (st : SvState)
    (heqs : CombEqs (q11_inline_mag.sem W P) st) (hsh : StateShape (q11_inline_mag.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q12_norm_family_inline_cond -/
load_sv q12_norm_family_inline_cond from "<scratchpad>/wph3/d3/probes3/q12_norm_family_inline_cond.sv" (top := "q12_norm_family_inline_cond")
example (W P : Nat) : CombDesign (q12_norm_family_inline_cond.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q12_norm_family_inline_cond.sem W P)) (ha : Acyclic (q12_norm_family_inline_cond.sem W P)) (st : SvState)
    (heqs : CombEqs (q12_norm_family_inline_cond.sem W P) st) (hsh : StateShape (q12_norm_family_inline_cond.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q13_red_cond -/
load_sv q13_red_cond from "<scratchpad>/wph3/d3/probes3/q13_red_cond.sv" (top := "q13_red_cond")
example (W P : Nat) : CombDesign (q13_red_cond.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q13_red_cond.sem W P)) (ha : Acyclic (q13_red_cond.sem W P)) (st : SvState)
    (heqs : CombEqs (q13_red_cond.sem W P) st) (hsh : StateShape (q13_red_cond.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q14_bit_and_red -/
load_sv q14_bit_and_red from "<scratchpad>/wph3/d3/probes3/q14_bit_and_red.sv" (top := "q14_bit_and_red")
example (W P : Nat) : CombDesign (q14_bit_and_red.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q14_bit_and_red.sem W P)) (ha : Acyclic (q14_bit_and_red.sem W P)) (st : SvState)
    (heqs : CombEqs (q14_bit_and_red.sem W P) st) (hsh : StateShape (q14_bit_and_red.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q15_add_onebit_signal -/
load_sv q15_add_onebit_signal from "<scratchpad>/wph3/d3/probes3/q15_add_onebit_signal.sv" (top := "q15_add_onebit_signal")
example (W P : Nat) : CombDesign (q15_add_onebit_signal.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q15_add_onebit_signal.sem W P)) (ha : Acyclic (q15_add_onebit_signal.sem W P)) (st : SvState)
    (heqs : CombEqs (q15_add_onebit_signal.sem W P) st) (hsh : StateShape (q15_add_onebit_signal.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q16_row_red_inline -/
load_sv q16_row_red_inline from "<scratchpad>/wph3/d3/probes3/q16_row_red_inline.sv" (top := "q16_row_red_inline")
example (W P : Nat) : CombDesign (q16_row_red_inline.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q16_row_red_inline.sem W P)) (ha : Acyclic (q16_row_red_inline.sem W P)) (st : SvState)
    (heqs : CombEqs (q16_row_red_inline.sem W P) st) (hsh : StateShape (q16_row_red_inline.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q17_low_family_bits -/
load_sv q17_low_family_bits from "<scratchpad>/wph3/d3/probes3/q17_low_family_bits.sv" (top := "q17_low_family_bits")
example (W P : Nat) : CombDesign (q17_low_family_bits.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q17_low_family_bits.sem W P)) (ha : Acyclic (q17_low_family_bits.sem W P)) (st : SvState)
    (heqs : CombEqs (q17_low_family_bits.sem W P) st) (hsh : StateShape (q17_low_family_bits.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q18_ovf_inline -/
load_sv q18_ovf_inline from "<scratchpad>/wph3/d3/probes3/q18_ovf_inline.sv" (top := "q18_ovf_inline")
example (W P : Nat) : CombDesign (q18_ovf_inline.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q18_ovf_inline.sem W P)) (ha : Acyclic (q18_ovf_inline.sem W P)) (st : SvState)
    (heqs : CombEqs (q18_ovf_inline.sem W P) st) (hsh : StateShape (q18_ovf_inline.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q19_sub_chain_emax -/
load_sv q19_sub_chain_emax from "<scratchpad>/wph3/d3/probes3/q19_sub_chain_emax.sv" (top := "q19_sub_chain_emax")
example (W P : Nat) : CombDesign (q19_sub_chain_emax.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q19_sub_chain_emax.sem W P)) (ha : Acyclic (q19_sub_chain_emax.sem W P)) (st : SvState)
    (heqs : CombEqs (q19_sub_chain_emax.sem W P) st) (hsh : StateShape (q19_sub_chain_emax.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q20_concat_cmp_operand -/
load_sv q20_concat_cmp_operand from "<scratchpad>/wph3/d3/probes3/q20_concat_cmp_operand.sv" (top := "q20_concat_cmp_operand")
example (W P : Nat) : CombDesign (q20_concat_cmp_operand.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q20_concat_cmp_operand.sem W P)) (ha : Acyclic (q20_concat_cmp_operand.sem W P)) (st : SvState)
    (heqs : CombEqs (q20_concat_cmp_operand.sem W P) st) (hsh : StateShape (q20_concat_cmp_operand.sem W P) st) : True := by
  sv_equations?
  trivial

/-! ## q21_ternary_chain_fields -/
load_sv q21_ternary_chain_fields from "<scratchpad>/wph3/d3/probes3/q21_ternary_chain_fields.sv" (top := "q21_ternary_chain_fields")
example (W P : Nat) : CombDesign (q21_ternary_chain_fields.sem W P) := by
  sv_structure?
example (W P : Nat) (hc : CombDesign (q21_ternary_chain_fields.sem W P)) (ha : Acyclic (q21_ternary_chain_fields.sem W P)) (st : SvState)
    (heqs : CombEqs (q21_ternary_chain_fields.sem W P) st) (hsh : StateShape (q21_ternary_chain_fields.sem W P) st) : True := by
  sv_equations?
  trivial
