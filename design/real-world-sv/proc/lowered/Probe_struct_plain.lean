import Submission.Design
import LeanModels.Sv.CombViewTactic

namespace Submission

example (N : Nat) : LeanModels.Sv.CombDesign (design.sem N) := by
  sv_structure?

end Submission
