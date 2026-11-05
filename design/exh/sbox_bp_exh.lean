import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombExhaustiveTactic

/-! `aes_sbox` for the Boyar-Peralta netlist (`tasks/aes_sbox/reference/sbox_bp.sv`) by `sv_exhaustive`. -/

set_option maxHeartbeats 1000000 in
theorem Submission.solution : Submission.Goal := by sv_exhaustive
