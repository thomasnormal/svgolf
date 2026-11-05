import Submission.Design
import LeanModels.Sv.CombProcTactic

namespace Submission

example (N : Nat) : ∃ d', (design.sem N).lowerComb = some d' ∧ LeanModels.Sv.CombDesign d' ∧ LeanModels.Sv.Acyclic d' := by
  sv_structure?

end Submission
