import SvGolf.Comb
import LeanModels.Sv.Loop2Frag

/-!
# Bridge S as a task lemma (WS3 plan item C) — *provisional over `run2`*, untrusted

`CombTask.satisfiedAt_of_loop` is the loop twin of `SvGolf.Comb`'s `CombTask.satisfiedAt_of_comb`: a
design whose only process is one `always_comb` whose body runs to `f` (the `SingleBody` that
`sv_loop_rows` produces), with `f` writing one non-input signal at its width, satisfies a
combinational task at `N` once `f` maps every reachable state that holds the task's inputs to one
that holds its outputs (`hout`, the per-state functional correctness: the agent's arithmetic). The
run, the settle, termination, the start state and the input transfer are discharged here, from the
declarations, once for every such design.

Not trusted text: it sits under `svgolf/design/` and is imported by nothing trusted. Compiled by
`compile-loop.sh`.
-/

namespace SvGolf.Design.Loop

open LeanModels.Sv LeanModels.Sv.Loop2 SvGolf

/-- The run invariant of a single-process loop design: every declaration bound, every non-input at
its declared width. -/
def LoopInv (d : Design2) (st : SvState) : Prop :=
  BoundAll (d.decls.toList.map (·.name)) st ∧
    ∀ dc ∈ d.decls.toList, dc.isInput = false → (sig st dc.name).width = dc.width

theorem lookup_map_of_mem {V : Decl → LVec} :
    ∀ {l : List Decl}, (l.map (·.name)).Nodup → ∀ {dc : Decl}, dc ∈ l →
      SvState.lookup (l.map fun dc => (dc.name, V dc)) dc.name = some (V dc)
  | [], _, _, h => absurd h List.not_mem_nil
  | dc' :: rest, hnd, dc, h => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with rfl | h
      · simp [SvState.lookup]
      · have hne : dc'.name ≠ dc.name := fun he => hnd.1 (he ▸ List.mem_map_of_mem h)
        simp [SvState.lookup, hne, lookup_map_of_mem hnd.2 h]

theorem decl_eq_of_name : ∀ {l : List Decl}, (l.map (·.name)).Nodup → ∀ {a b : Decl}, a ∈ l → b ∈ l →
    a.name = b.name → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: rest, hnd, a, b, ha, hb, he => by
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
      · rw [h1, h2]
      · subst h1
        exact absurd (he ▸ List.mem_map_of_mem (f := (·.name)) h2) hnd.1
      · subst h2
        exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.name)) h1) hnd.1
      · exact decl_eq_of_name hnd.2 h1 h2 he

/-- **The task at `N` from the loop's per-state correctness** (Bridge S, packaged). -/
theorem CombTask.satisfiedAt_of_loop {t : CombTask} {N : Nat} {d : Design2} {body : Stmt2}
    {f : SvState → SvState} {n : String}
    (hI : t.Interface N d) (hp : d.processes = #[.alwaysComb body])
    (hdc : ∀ dc ∈ d.decls.toList, dc.init = none ∧ dc.twoState = false)
    (hnd : (d.decls.toList.map (·.name)).Nodup)
    (hrun : SingleBody (BoundAll (d.decls.toList.map (·.name))) body f)
    (hq : body.hasQualifiedCase = false) (hset : ∀ st, ∃ v, f st = SvState.set st n v)
    (hw : ∀ st, (sig (f st) n).width = (sig st n).width)
    (hout : ∀ st, LoopInv d st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll (f st) (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  have h4 : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false :=
    fun dc h _ => (hdc dc h).2
  have hinit : initState2 d = d.decls.toList.map fun dc => (dc.name, LVec.xVec dc.width) := by
    unfold initState2
    exact List.map_congr_left fun dc h => by simp [(hdc dc h).1, (hdc dc h).2]
  have hs : SingleComb d body (LoopInv d) f :=
    { procs := hp
      noq := hq
      run := hrun.1.weaken fun _ h => h.1
      inv := fun st h => ⟨hrun.2.1 st h.1, fun dc hdc hin => by
        obtain ⟨v, hv⟩ := hset st
        by_cases he : dc.name = n
        · rw [he, hw, ← he]; exact h.2 dc hdc hin
        · rw [hv, sig_set_ne _ _ he]; exact h.2 dc hdc hin⟩
      idem := fun st _ => hrun.2.2 st
      inputs := fun inputs st h => by
        refine ⟨fun x hx => ?_, fun dc hdc hin => ?_⟩
        · obtain ⟨v, hv⟩ := h.1 x hx
          rw [lookup_applyInputs2 d inputs st x h4, hv]
          split <;> cases SvState.lookup inputs x <;> simp
        · have hni : dc.name ∉ d.inputNames.toList := by
            intro hm
            simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap,
              Option.ite_none_right_eq_some, Option.some.injEq] at hm
            obtain ⟨dc', hdc', hin', hn'⟩ := hm
            have := decl_eq_of_name hnd hdc' hdc hn'
            subst this
            simp [hin] at hin'
          rw [← h.2 dc hdc hin]
          simp only [sig]
          rw [lookup_applyInputs2 d inputs st _ h4, if_neg hni]
      init := by
        rw [hinit]
        refine ⟨fun x hx => ?_, fun dc hdc _ => ?_⟩
        · obtain ⟨dc, hdc, rfl⟩ := List.mem_map.mp hx
          exact ⟨_, lookup_map_of_mem hnd hdc⟩
        · simp [sig, lookup_map_of_mem hnd hdc, LVec.xVec, LVec.replicate, LVec.width] }
  refine ⟨hI, ⟨fun p hp' => ?_, hs.terminates⟩, ?_⟩
  · rw [hp] at hp'
    simp at hp'
    subst hp'
    rfl
  · intro σ stim tr hr c inputs st hi hst v hv
    obtain ⟨prev, hprev, rfl⟩ := hs.runs hr hi hst
    refine hout _ (hs.inputs inputs prev hprev) v (hv.transfer fun x hx val hval => ?_)
    have hx' : x ∈ d.inputNames.toList := by
      rw [← inputPorts_map_fst, hI.1]; exact hx
    rw [lookup_applyInputs2 d inputs prev x h4, if_pos hx', hval]
    rfl

/-- **The task at `N` over `run2` for a fragment loop body** (`loop1_single`): what is left is the
per-state correctness of the body's meaning. -/
theorem CombTask.satisfiedAt_of_frag {t : CombTask} {N : Nat} {d : Design2} {n : String}
    {c : LVec} {Nl : Nat} {T : Nat → Stmt2} (hI : t.Interface N d)
    (hp : d.processes = #[.alwaysComb (initLoop n c Nl T)])
    (hdc : ∀ dc ∈ d.decls.toList, dc.init = none ∧ dc.twoState = false)
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hn : n ∈ d.decls.toList.map (·.name))
    (hT : ∀ k, k < Nl → (T k).fragOk n (fun _ _ => true)
      (fun x => decide (x ∈ d.decls.toList.map (·.name))) = true)
    (hout : ∀ st, LoopInv d st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll (initLoop.meaning n c Nl T st) (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d :=
  satisfiedAt_of_loop hI hp hdc hnd (loop1_single _ hn hT) (initLoop_noq hT) (fun _ => ⟨_, rfl⟩)
    (fun st => by simp only [initLoop.meaning, sig_set_self, Stmt2.width_step]) hout

end SvGolf.Design.Loop

#pin_axioms SvGolf.Design.Loop.lookup_map_of_mem SvGolf.Design.Loop.decl_eq_of_name
  SvGolf.Design.Loop.CombTask.satisfiedAt_of_loop SvGolf.Design.Loop.CombTask.satisfiedAt_of_frag
