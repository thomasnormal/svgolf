import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombExhaustiveTactic

/-!
# aes_sbox: a tower-field (composite-field GF(((2^2)^2)^2)) netlist, proved by exhaustive kernel evaluation

`sv_exhaustive` (LeanModels/Sv/CombExhaustiveTactic.lean) compiles the flat netlist once into a packed gate
program, checks the compilation, and decides `y = sbox x` on all 256 inputs by kernel evaluation.
-/

namespace Submission

set_option maxHeartbeats 0 in
theorem solution : Goal := by sv_exhaustive

end Submission
