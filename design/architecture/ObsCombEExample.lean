import Submission.Solution
import ObsCombE

/-!
# The `_example` records over E-core-0 (transport theorem, instance)

Not in any lake library. Compiles against a check.py staging tree of an accepted `_example` record
(both `leaderboard/data/_example/*` records name the same lemmas): `compile-obsE.sh` with
`STAGE=<stage dir>` and `MODULES=ObsCombEExample`, after the default modules.

From the record's own `solution` (the v1 statement over `run2`) and its named lemmas `band_comb`,
`band_acyclic` and `band_sem_decls`, the `_example` statement over E-core-0 in the Task v2
convention, at every declared-type predicate `ty`.
-/

namespace SvGolf.Arch.RecExample

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Sv.Kernel SvGolf

theorem example_E0 (ty : Nat → Prop) :
    SvGolf.Tasks.Example.task.Statement_obs ty Obs_E0 (fun _ => True)
      fun N => Elab.ofDesign2 (Submission.design.sem N) :=
  statement_E0 ty Submission.solution
    (fun N hN _ => by
      have hN' : 1 ≤ N := hN
      refine ⟨Submission.band_comb hN', Submission.band_acyclic hN', ?_, ?_⟩
      · intro dc hdc
        rw [Submission.band_sem_decls N hN'] at hdc
        simp only [Submission.bandDecls, List.mem_cons, List.not_mem_nil, or_false] at hdc
        rcases hdc with rfl | rfl | rfl <;> rfl
      · intro dc hdc v hv
        rw [Submission.band_sem_decls N hN'] at hdc
        simp only [Submission.bandDecls, List.mem_cons, List.not_mem_nil, or_false] at hdc
        rcases hdc with rfl | rfl | rfl <;> simp at hv)
    (fun N => by simp [SvGolf.Tasks.Example.task])

/-- **The unrestricted converse fails on the record's own design** (non-vacuity of
`not_included_run2_E0`): the stimulus that binds `a` to an `(N + 1)`-bit value has a `run2`
behaviour that is no E behaviour. -/
theorem example_not_included (N : Nat) (hN : 1 ≤ N) (k : Clocking) :
    ¬ Included Obs_run2 Obs_E0 k (Elab.ofDesign2 (Submission.design.sem N)).toDesign2
      (Elab.ofDesign2 (Submission.design.sem N)) := by
  have hd := Submission.band_comb hN
  have hE := Elab.toDesign2_ofDesign2_of_comb hd
  have h4 : ∀ dc ∈ (Submission.design.sem N).decls.toList, dc.twoState = false := by
    intro dc hdc
    rw [Submission.band_sem_decls N hN] at hdc
    simp only [Submission.bandDecls, List.mem_cons, List.not_mem_nil, or_false] at hdc
    rcases hdc with rfl | rfl | rfl <;> rfl
  have hP : Profile0 (Elab.ofDesign2 (Submission.design.sem N)) :=
    ⟨by rw [hE]; exact hd, fun dc hdc => h4 dc hdc⟩
  obtain ⟨rank, -, hS⟩ := Settles.ofProfile0' hP (by rw [hE]; exact Submission.band_acyclic hN)
  refine not_included_run2_E0 hS (n := "a") (w := N) ?_ (v := LVec.ofNat (N + 1) 0) ?_ k
  · rw [hE]; simp [inputSigs, Submission.band_sem_decls N hN, Submission.bandDecls]
  · simp [LVec.ofNat, LVec.width]

#print axioms example_E0
#print axioms example_not_included

end SvGolf.Arch.RecExample
