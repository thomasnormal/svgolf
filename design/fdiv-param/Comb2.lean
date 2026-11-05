import SvGolf.Comb

/-!
# DRAFT: proof helpers for two-parameter combinational tasks (UNTRUSTED, kernel-checked)

The helpers of `SvGolf/Comb.lean` apply to a two-parameter task UNCHANGED, because the
statement at one parameter pair is `CombTask.SatisfiedAt` of `CombTask2.atPoint` at its
parameter `0` (the fields of `atPoint` reduce to `t.inputs N M` etc. by `rfl`). The restatements
below are the three entry points a proof uses, in the two-parameter vocabulary; each is the
one-parameter theorem applied to `t.atPoint N M`. To be appended to `SvGolf/Comb.lean` together
with `CombTask2` in `SvGolf/Task.lean` if the maintainers approve the latter.
-/

namespace SvGolf

open LeanModels.Sv

/-- `SatisfiedAt` for the fixed-size task `atPoint` unfolds to the 2-parameter fields. -/
theorem CombTask2.satisfiedAt_iff (t : CombTask2) (N M : Nat) (d : Design2) :
    t.SatisfiedAt N M d ↔ (t.atPoint N M).SatisfiedAt 0 d := Iff.rfl

/-- **The two-parameter comb reduction**: interface plus one settled-state lemma. -/
theorem CombTask2.satisfiedAt_of_comb {t : CombTask2} {N M : Nat} {d : Design2}
    (hI : (t.atPoint N M).Interface 0 d) (hd : CombDesign d) (ha : Acyclic d)
    (hset : ∀ st, CombEqs d st → StateShape d st → ∀ v, HoldAll st (t.inputs N M) v →
      HoldAll st (t.outputs N M) (t.fn N M v)) :
    t.SatisfiedAt N M d :=
  CombTask.satisfiedAt_of_comb hI hd ha hset

/-- **Non-vacuity** at a parameter pair. -/
theorem CombTask2.SatisfiedAt.exists_run {t : CombTask2} {N M : Nat} {d : Design2}
    (h : t.SatisfiedAt N M d) (hnd : ((t.inputs N M).map Prod.fst).Nodup) (σ : ScheduleOracle)
    (v : Vals ((t.inputs N M).map Prod.snd)) :
    ∃ st, Runs2 d σ [entryOf (t.inputs N M) v] [st] ∧ HoldAll st (t.outputs N M) (t.fn N M v) :=
  CombTask.SatisfiedAt.exists_run (t := t.atPoint N M) (N := 0) h hnd σ v

/-- One counterexample refutes the statement at a parameter pair. -/
theorem CombTask2.not_statement_of {t : CombTask2} {sem : Nat → Nat → Design2} {N M : Nat}
    (hNM : t.inRange N M) (h : ¬ t.SatisfiedAt N M (sem N M)) : ¬ t.Statement sem :=
  fun hs => h (hs N M hNM)

end SvGolf
