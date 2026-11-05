import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.CombProcTactic

open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 neg_trunc from "Examples/system-verilog/comb_word/neg/neg_trunc.sv.json"
load_design_sv2 neg_mul from "Examples/system-verilog/comb_word/neg/neg_mul.sv.json"
load_design_sv2 neg_lt from "Examples/system-verilog/comb_word/neg/neg_lt.sv.json"
load_design_sv2 neg_shift from "Examples/system-verilog/comb_word/neg/neg_shift.sv.json"
load_design_sv2 neg_unsized from "Examples/system-verilog/comb_word/neg/neg_unsized.sv.json"
load_design_sv2 neg_selfdet from "Examples/system-verilog/comb_word/neg/neg_selfdet.sv.json"
load_design_sv2 neg_proc from "Examples/system-verilog/comb_word/neg/neg_proc.sv.json"

example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_trunc.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_mul.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_lt.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_shift.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_unsized.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : CombDesign (neg_selfdet.sem N) := by
  sv_structure
example (N : Nat) (hN : 1 ≤ N) : ∃ d', (neg_proc.sem N).lowerComb = some d' ∧ CombDesign d' := by
  sv_structure
