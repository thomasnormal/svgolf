import Submission.Solution
import ObsCombRedrive

/-!
# The `_example` records under the trusted convention (instance, provisional over `run2`)

Not in any lake library. Compiles against a check.py staging tree of an accepted `_example` record
(both `leaderboard/data/_example/*` records name the same lemmas): `compile-obs.sh` with `STAGE=<stage dir>` and `MODULES=ObsRecExample`, after the default modules.

From the record's own `solution` (v1, over `run2`) and its own `band_comb` lemma, the `_example`
statement in the Task v2 convention (inputs read from the pre sample, receptiveness included), over
`Obs_run2`, at every declared-type predicate `ty`, and as `Sat` of the compiled `Spec`. No line of
the record is re-proved (`statement_obs_of_comb`).
-/

namespace SvGolf.Arch.RecObsExample

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch

theorem example_obs (ty : Nat → Prop) :
    SvGolf.Tasks.Example.task.Statement_obs ty Obs_run2 Unclocked Submission.design.sem :=
  statement_obs_of_comb ty (fun _ hN => Submission.band_comb hN)
    (fun N _ => by simp [SvGolf.Tasks.Example.task]) Submission.solution

theorem example_obs_sat (ty : Nat → Prop) :
    Sat Obs_run2 Unclocked (SvGolf.Tasks.Example.task.toSpec ty) Submission.design.sem :=
  SvGolf.Tasks.Example.task.statement_obs_iff_sat.mp (example_obs ty)

#print axioms example_obs
#print axioms example_obs_sat

end SvGolf.Arch.RecObsExample
