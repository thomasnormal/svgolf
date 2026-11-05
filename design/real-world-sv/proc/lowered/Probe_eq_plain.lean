import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

theorem struct_sorry (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by sorry
theorem iface_sorry (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by sorry

example : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN
  obtain ⟨hc, ha⟩ := struct_sorry N hN'
  refine CombTask.satisfiedAt_of_comb (iface_sorry N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations?

end Submission
