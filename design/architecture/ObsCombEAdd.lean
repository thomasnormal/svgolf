import Submission.Solution
import ObsCombE

/-!
# The `add` record over E-core-0 (transport theorem, instance)

Not in any lake library. Compiles against a check.py staging tree of the accepted `add` record
(`leaderboard/data/add/d4a292db…`): `compile-obsE.sh` with `STAGE=<stage dir>` and
`MODULES=ObsCombEAdd`, after the default modules.

From the record's own `solution` (the v1 statement over `run2`) and its named lemmas `ripple_comb`,
`ripple_acyclic` and `ripple_sem_decls`, the `add` statement over E-core-0 in the Task v2
convention, at every declared-type predicate `ty`.
-/

namespace SvGolf.Arch.RecAdd

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Sv.Kernel SvGolf

theorem add_E0 (ty : Nat → Prop) :
    SvGolf.Tasks.Add.task.Statement_obs ty Obs_E0 (fun _ => True)
      fun N => Elab.ofDesign2 (Submission.design.sem N) :=
  statement_E0 ty Submission.solution
    (fun N hN _ => by
      have hN' : 1 ≤ N := hN
      refine ⟨Submission.ripple_comb N hN', Submission.ripple_acyclic N hN', ?_, ?_⟩
      · intro dc hdc
        rw [Submission.ripple_sem_decls N hN'] at hdc
        simp only [Submission.rippleDecls, List.mem_cons, List.not_mem_nil, or_false] at hdc
        rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · intro dc hdc v hv
        rw [Submission.ripple_sem_decls N hN'] at hdc
        simp only [Submission.rippleDecls, List.mem_cons, List.not_mem_nil, or_false] at hdc
        rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hv)
    (fun N => by simp [SvGolf.Tasks.Add.task])

#print axioms add_E0

end SvGolf.Arch.RecAdd
