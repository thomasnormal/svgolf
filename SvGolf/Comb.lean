import SvGolf.Task
import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2
import LeanModels.Sv.Comb2Proc

/-!
# Proof helpers for combinational tasks (untrusted, kernel-checked)

Nothing here is part of the trusted base: every theorem is proved, and a
submission may use or ignore it. It connects `SvGolf.Task`'s statement to the
ls-sv combinational settle theorem (`LeanModels/Sv/Comb2.lean`) and proves
the non-vacuity facts the trusted docstring promises.

## API

* `HoldAll_nil`, `HoldAll_cons` (simp): unfold `HoldAll` on a concrete port
  list into one `SvState.lookup` equation per port.
* `inputPorts_map_fst`: the input ports' names are `Design2.inputNames`.
* `unclocked_of_edgeIndices`: an empty edge phase gives the `Unclocked` half
  of conjunct 2 (`satisfiedAt_of_comb` uses it; a design outside the
  assign-only comb profile, e.g. with `always_comb`, can too).
* **`CombTask.satisfiedAt_of_comb`**: the main reduction. For a design in the
  comb profile (`CombDesign`) with an acyclicity certificate (`Acyclic`), the
  whole statement at one parameter value follows from the interface and ONE
  settled-state lemma: in every state solving the design's equations, known
  inputs give the function's outputs. That lemma is pure combinational
  reasoning (no runs, no fuel, no schedule); the ripple-carry adder in
  `Examples/system-verilog/ripple_add/proof.lean` (`ripple_settled`) is the
  worked example of one.
* **`CombTask.satisfiedAt_of_lowered`**: the same for a design with `always_comb`
  processes, through its lowering (`Design2.lowerComb`): the comb profile and
  acyclicity are those of the lowering, and `hnq` (no qualified `case`) comes
  from `NoQ.sem_noQ` (`LeanModels/Sv/ProcNoQualified.lean`).
* Non-vacuity: `entryOf` (the stimulus entry that drives a valuation),
  `holdAll_entryOf`, and **`CombTask.SatisfiedAt.exists_run`**: a design that
  satisfies the statement has, for every schedule and every input valuation,
  a completed one-cycle run whose snapshot carries the function's value.
* Refutation: `holdAllB` (a `Bool` twin of `HoldAll`), `CombTask.counterexample`
  and **`CombTask.not_computes_of_counterexample`**: one concrete run whose
  output differs from the function refutes `Computes`, decided by
  `decide +kernel` on closed data (the tasks' `tests/<name>/negative/` refutations).
-/

namespace SvGolf

open LeanModels.Sv

/-! ## `HoldAll` on concrete port lists -/

@[simp] theorem HoldAll_nil (st : SvState) (v : Vals (([] : List Sig).map Prod.snd)) :
    HoldAll st [] v ↔ True := Iff.rfl

@[simp] theorem HoldAll_cons (st : SvState) (n : String) (w : Nat) (sigs : List Sig)
    (v : Vals (((n, w) :: sigs).map Prod.snd)) :
    HoldAll st ((n, w) :: sigs) v ↔
      SvState.lookup st n = some (LVec.ofBitVec v.1) ∧ HoldAll st sigs v.2 := Iff.rfl

/-- `HoldAll` moves along any state that agrees on the ports' bindings. -/
theorem HoldAll.transfer {a b : SvState} :
    ∀ {sigs : List Sig} {v : Vals (sigs.map Prod.snd)}, HoldAll a sigs v →
      (∀ n ∈ sigs.map Prod.fst, ∀ val, SvState.lookup a n = some val →
        SvState.lookup b n = some val) →
      HoldAll b sigs v
  | [], _, _, _ => trivial
  | (n, _) :: _, _, ⟨h1, h2⟩, h =>
      ⟨h n (by simp) _ h1, HoldAll.transfer h2 fun m hm => h m (by simp [hm])⟩

/-! ## Ports and input names -/

private theorem filterMap_inputs_fst (l : List Decl) :
    (l.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none).map Prod.fst =
      l.filterMap fun dc => if dc.isInput then some dc.name else none := by
  induction l with
  | nil => rfl
  | cons dc l ih =>
      by_cases h : dc.isInput = true
      · simp [h, ih]
      · simp [h, ih]

/-- The input ports' names are the design's `inputNames` (the names
`applyInputs2` reads). -/
theorem inputPorts_map_fst (d : Design2) : (inputPorts d).map Prod.fst = d.inputNames.toList := by
  simp only [inputPorts, Design2.inputNames, Array.toList_filterMap]
  exact filterMap_inputs_fst _

/-! ## No clocked process -/

/-- A design whose edge phase is empty (`d.edgeIndices = []`, which every
comb-profile design has: `CombDesign.edgeIndices_eq`, and the `always_comb`
profile's `Comb2Proc` lemmas give too) has no clocked process. -/
theorem unclocked_of_edgeIndices {d : Design2} (h : d.edgeIndices = []) : Unclocked d := by
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hi
  have hlt : i < d.processes.size := by
    rcases Nat.lt_or_ge i d.processes.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none hge] at hi
      cases hi
  unfold Design2.edgeIndices at h
  rw [List.filter_eq_nil_iff] at h
  have := h i (List.mem_range.mpr hlt)
  simpa [hi] using this

/-- `Unclocked` is decidable on a concrete design (`decide +kernel` refutes a
design with a clocked process). -/
instance (d : Design2) : Decidable (Unclocked d) :=
  inferInstanceAs (Decidable (∀ p ∈ d.processes.toList, p.isEdgePhase = false))

/-! ## The comb reduction -/

/-- **The statement at one parameter value, for a comb design.** Given the
interface, a comb-profile certificate and an acyclicity certificate,
`SatisfiedAt` follows from one settled-state lemma `hset`: every state that
solves the design's equations (`CombEqs`) and has the comb shape
(`StateShape`), and whose input ports hold known values `v`, holds
`t.fn N v` on the output ports. -/
theorem CombTask.satisfiedAt_of_comb {t : CombTask} {N : Nat} {d : Design2}
    (hI : t.Interface N d) (hd : CombDesign d) (ha : Acyclic d)
    (hset : ∀ st, CombEqs d st → StateShape d st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  refine ⟨hI, ⟨unclocked_of_edgeIndices hd.edgeIndices_eq, Terminates2.of_acyclic hd ha⟩, ?_⟩
  apply Models2.of_comb_inputs hd
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  rw [← inputPorts_map_fst, hI.1]
  exact hn

/-- **The statement at one parameter value, for a design that lowers** to a comb design: the interface
of the design, the comb profile and acyclicity of its lowering `d'`, no qualified `case` (`hnq`), and ONE
settled-state lemma about `d'`. -/
theorem CombTask.satisfiedAt_of_lowered {t : CombTask} {N : Nat} {d d' : Design2}
    (hI : t.Interface N d) (hl : d.lowerComb = some d') (hd : CombDesign d') (ha : Acyclic d')
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hset : ∀ st, CombEqs d' st → StateShape d' st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  obtain ⟨hph, -, -⟩ := Design2.lowerComb_phases hl
  refine ⟨hI, ⟨unclocked_of_edgeIndices hph, Terminates2.of_lowerComb_acyclic hl hd ha hnq⟩, ?_⟩
  apply Models2.of_combProc_inputs hl hd (hnq := hnq)
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  have hdec : d'.decls = d.decls := by
    unfold Design2.lowerComb at hl
    rcases hp : d.lowerProcs d.processes.toList with _ | ps
    · simp [hp] at hl
    · simp only [hp, Option.map_some, Option.some.injEq] at hl
      rw [← hl]
  rw [show d'.inputNames = d.inputNames by simp [Design2.inputNames, hdec], ← inputPorts_map_fst, hI.1]
  exact hn

/-! ## Non-vacuity: the hypothesis is met by a run -/

/-- The stimulus entry that drives every port of `sigs` with its value in `v`. -/
def entryOf : (sigs : List Sig) → Vals (sigs.map Prod.snd) → SvState
  | [], _ => []
  | (n, _) :: sigs, v => (n, LVec.ofBitVec v.1) :: entryOf sigs v.2

/-- With distinct port names, `entryOf sigs v` meets the hypothesis
`HoldAll · sigs v`. -/
theorem holdAll_entryOf :
    ∀ (sigs : List Sig), (sigs.map Prod.fst).Nodup →
      ∀ v : Vals (sigs.map Prod.snd), HoldAll (entryOf sigs v) sigs v
  | [], _, _ => trivial
  | (n, _) :: sigs, hnd, v => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      refine ⟨by simp [entryOf, SvState.lookup], ?_⟩
      refine (holdAll_entryOf sigs hnd.2 v.2).transfer fun m hm val hval => ?_
      have hne : (n == m) = false := by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        exact hnd.1 hm
      simp only [entryOf, SvState.lookup, hne, Bool.false_eq_true, if_false]
      exact hval

/-- **Non-vacuity.** If a design satisfies the statement at `N` and the task's
input names are distinct, then for every schedule and every input valuation
`v` there is a completed one-cycle run, on the stimulus that drives `v`,
whose snapshot holds `t.fn N v` on the output ports. -/
theorem CombTask.SatisfiedAt.exists_run {t : CombTask} {N : Nat} {d : Design2}
    (h : t.SatisfiedAt N d) (hnd : ((t.inputs N).map Prod.fst).Nodup) (σ : ScheduleOracle)
    (v : Vals ((t.inputs N).map Prod.snd)) :
    ∃ st, Runs2 d σ [entryOf (t.inputs N) v] [st] ∧ HoldAll st (t.outputs N) (t.fn N v) := by
  obtain ⟨tr, hr⟩ := h.2.1.2 σ [entryOf (t.inputs N) v]
  have hlen := hr.length
  match tr, hlen with
  | [st], _ =>
      exact ⟨st, hr, h.2.2 σ _ _ hr 0 _ st rfl rfl v (holdAll_entryOf _ hnd v)⟩

/-! ## Refutation by one concrete run -/

/-- `Bool` twin of `HoldAll`, for `decide`-style evaluation on closed data. -/
def holdAllB (st : SvState) : (sigs : List Sig) → Vals (sigs.map Prod.snd) → Bool
  | [], _ => true
  | (n, _) :: sigs, v => SvState.lookup st n == some (LVec.ofBitVec v.1) && holdAllB st sigs v.2

theorem holdAllB_iff (st : SvState) :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)), holdAllB st sigs v = true ↔ HoldAll st sigs v
  | [], _ => by simp [holdAllB]
  | (n, _) :: sigs, v => by
      simp [holdAllB, holdAllB_iff st sigs v.2]

/-- A counterexample: the one-cycle run of `d` under `σ` at `fuel`, on the
entry driving `v`, completes with a snapshot whose outputs are NOT
`t.fn N v`. Closed data, so `decide +kernel` evaluates it. -/
def CombTask.counterexample (t : CombTask) (N : Nat) (d : Design2) (σ : ScheduleOracle)
    (fuel : Nat) (v : Vals ((t.inputs N).map Prod.snd)) : Bool :=
  match run2 d σ fuel [entryOf (t.inputs N) v] with
  | .ok [st] => !holdAllB st (t.outputs N) (t.fn N v)
  | _ => false

/-- **One counterexample refutes `Computes`** (with distinct input names). -/
theorem CombTask.not_computes_of_counterexample {t : CombTask} {N : Nat} {d : Design2}
    {σ : ScheduleOracle} {fuel : Nat} {v : Vals ((t.inputs N).map Prod.snd)}
    (hnd : ((t.inputs N).map Prod.fst).Nodup) (hce : t.counterexample N d σ fuel v = true) :
    ¬ t.Computes N d := by
  intro hc
  unfold CombTask.counterexample at hce
  split at hce
  · rename_i st hrun
    have hgood := hc σ _ _ ⟨fuel, hrun⟩ 0 _ st rfl rfl v (holdAll_entryOf _ hnd v)
    rw [← holdAllB_iff] at hgood
    simp [hgood] at hce
  · simp at hce

/-- `Statement` refuted at one parameter value in range. -/
theorem CombTask.not_statement_of {t : CombTask} {sem : Nat → Design2} {N : Nat}
    (hN : t.inRange N) (h : ¬ t.SatisfiedAt N (sem N)) : ¬ t.Statement sem :=
  fun hs => h (hs N hN)

end SvGolf
