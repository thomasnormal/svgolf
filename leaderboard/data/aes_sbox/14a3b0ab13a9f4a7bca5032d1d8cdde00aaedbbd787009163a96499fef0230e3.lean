import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombExhaustiveTactic

namespace Submission

set_option maxHeartbeats 0 in
theorem solution : Goal := by sv_exhaustive

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
