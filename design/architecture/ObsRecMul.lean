import Submission.Solution
import ObsCombRedrive

/-!
# The `mul` record under the trusted convention (instance, provisional over `run2`)

Not in any lake library. Compiles against a check.py staging tree of an accepted `mul` record
(`leaderboard/data/mul/6811ad4e…`): `compile-obs.sh` with `STAGE=<stage dir>` and `MODULES=ObsRecMul`, after the default modules.

From the record's own `solution` (v1, over `run2`) and its own `mul_comb` lemma, the `mul`
statement in the Task v2 convention (inputs read from the pre sample, receptiveness included), over
`Obs_run2`, at every declared-type predicate `ty`, and as `Sat` of the compiled `Spec`. No line of
the record is re-proved (`statement_obs_of_comb`).
-/

namespace SvGolf.Arch.RecObsMul

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch

theorem mul_obs (ty : Nat → Prop) :
    SvGolf.Tasks.Mul.task.Statement_obs ty Obs_run2 Unclocked Submission.design.sem :=
  statement_obs_of_comb ty (fun _ hN => Submission.mul_comb hN)
    (fun N _ => by simp [SvGolf.Tasks.Mul.task]) Submission.solution

theorem mul_obs_sat (ty : Nat → Prop) :
    Sat Obs_run2 Unclocked (SvGolf.Tasks.Mul.task.toSpec ty) Submission.design.sem :=
  SvGolf.Tasks.Mul.task.statement_obs_iff_sat.mp (mul_obs ty)

#print axioms mul_obs
#print axioms mul_obs_sat

end SvGolf.Arch.RecObsMul
