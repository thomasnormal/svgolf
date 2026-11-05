import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombExhaustiveTactic

/-!
# Reference solution for task `aes_sbox`: the 256-entry `case` table (WP-G S3a)

This is a submission file like any player's `Solution.lean`: the checker generates `Submission.Design`
(`Submission.design`, `Submission.Goal`) and this file proves `theorem Submission.solution : Submission.Goal`
for the fixed-size S-box statement (`SvGolf.Tasks.AesSbox.Statement`, i.e. `y = sbox x` for every known `x`).
The design is `reference/sbox_table.sv`: one `always_comb` with a plain `case (x)` of 256 constant items
`8'dK: y = 8'dS;` and a `default`.

The proof is `sv_exhaustive` (`LeanModels/Sv/CombExhaustiveTactic.lean`): the design is read through its
lowering (`CombTask.satisfiedAt_of_lowered`, no qualified `case` by `NoQ.sem_noQ`), the `case` is compiled
once into a word-level table lookup (one bitmap per output bit), and `y` is decided against the task's `sbox`
on all 256 inputs by kernel evaluation. `PROVING.md`, section 15.
-/

namespace Submission

set_option maxHeartbeats 1000000 in
/-- **The reference solution**: the `aes_sbox` statement for the `case` table. -/
theorem solution : Goal := by sv_exhaustive

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
