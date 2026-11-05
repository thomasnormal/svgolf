import Submission.Solution
import ObsCombRedrive

/-!
# The `add` record under the trusted convention (instance, provisional over `run2`)

Not in any lake library. Compiles against a check.py staging tree of an accepted `add` record
(`leaderboard/data/add/d4a292db…`): `compile-obs.sh` with `STAGE=<stage dir>` and `MODULES=ObsRecAdd`, after the default modules.

From the record's own `solution` (v1, over `run2`) and its own `ripple_comb` lemma, the `add`
statement in the Task v2 convention (inputs read from the pre sample, receptiveness included), over
`Obs_run2`, at every declared-type predicate `ty`, and as `Sat` of the compiled `Spec`. No line of
the record is re-proved (`statement_obs_of_comb`).
-/

namespace SvGolf.Arch.RecObsAdd

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch

theorem add_obs (ty : Nat → Prop) :
    SvGolf.Tasks.Add.task.Statement_obs ty Obs_run2 Unclocked Submission.design.sem :=
  statement_obs_of_comb ty (fun N hN => Submission.ripple_comb N hN)
    (fun N _ => by simp [SvGolf.Tasks.Add.task]) Submission.solution

theorem add_obs_sat (ty : Nat → Prop) :
    Sat Obs_run2 Unclocked (SvGolf.Tasks.Add.task.toSpec ty) Submission.design.sem :=
  SvGolf.Tasks.Add.task.statement_obs_iff_sat.mp (add_obs ty)

#print axioms add_obs
#print axioms add_obs_sat

end SvGolf.Arch.RecObsAdd
