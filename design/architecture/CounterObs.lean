import CounterCycle
import ObsComb
import LeanModels.Sv.REdgeRun2

/-!
# The counter under the trusted convention (Day 5)

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status: provisional over `run2`.** The statement is `TaskV2.lean`'s `SeqTask.SatisfiedAt_obs` over
`Obs_run2`: inputs read from the pre sample, the claim on the post sample, receptiveness included.
It is about the hand-built family `cntD` of `../sequential/CounterCycle.lean`, whose agreement with
`cnt.sem N` that file checks by `#guard` at seven points.

## What is here

1. `follows_obs_of_cycle`: the reduction theorem of the trusted convention over `Obs_run2`. An
   invariant on the state, a simulation relation, and two one-cycle lemmas, now about `cycleObs2`
   (pre and post samples) and with the hypothesis read from the PRE sample, give `Follows_obs`. It is
   `SeqTask.satisfiedAt_of_cycle`'s proof, re-done over `runFromObs2_cycle`.
2. The counter's one cycle with both samples (`cnt_cycleObs_ok`), from the sketch's `cnt_cycle` and
   the decomposition `cycleStep2_eq_pre_post`: pre = the inputs applied (no comb process, no reset
   event), post = the register updated.
3. `cnt_satisfiedAt_obs`: the counter satisfies the trusted statement at every `N`, so the Task v2
   skeleton holds (`cnt_sat`). `Receptive` comes from the library theorem
   (`receptive_of_writesInput`). Its side condition `(cntD N).writesInput = false` is closed by
   `rfl` at symbolic `N`, and by `decide` at any concrete `N` (MEASURED: `decide` refuses the free
   variable).
-/

namespace SvGolf.Arch.Seq

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Seq SvGolf.Arch

/-! ## 1. The reduction theorem, trusted convention, over `Obs_run2` -/

/-- **Reduction theorem (trusted convention, over `Obs_run2`)**: an invariant `Inv` on states, a
simulation relation `R` to the spec state, a reset cycle lemma and a step cycle lemma about
`cycleObs2` (hypotheses read from the pre sample, conclusions about the post sample) give
`Follows_obs` for a task with a reset port. -/
theorem follows_obs_of_cycle (t : SeqTask) (N : Nat) (d : Design2)
    (hrst : ∃ r, t.rst = some r)
    (Inv : SvState → Prop) (R : SvState → t.State N → Prop)
    (hinit : Inv (initState2 d))
    (hinv : ∀ σ F inputs prev k (o : CycleObs SvState) k', Inv prev →
        cycleObs2 d σ F inputs prev k = .ok (o, k') → Inv o.post)
    (hreset : ∀ σ F inputs prev k (o : CycleObs SvState) k' (v : t.Ins N), Inv prev →
        cycleObs2 d σ F inputs prev k = .ok (o, k') → t.Holds N (Obs_run2.sample d o.pre) (true, v) →
        R o.post (t.init N) ∧ t.ObsOKS N (Obs_run2.sample d o.post) (t.init N, v))
    (hstep : ∀ σ F inputs prev k (o : CycleObs SvState) k' (s : t.State N) (v : t.Ins N),
        Inv prev → R prev s →
        cycleObs2 d σ F inputs prev k = .ok (o, k') → t.Holds N (Obs_run2.sample d o.pre) (false, v) →
        R o.post (t.step N s v) ∧ t.ObsOKS N (Obs_run2.sample d o.post) (t.step N s v, v)) :
    t.Follows_obs Obs_run2 N d := by
  intro σ stim b _ hb
  obtain ⟨r, ⟨F, hrun⟩, rfl⟩ := hb
  -- the invariant holds of every cycle's start state
  have hall : ∀ (c : Nat) (o : CycleObs SvState), r[c]? = some o → Inv o.post := by
    intro c
    induction c with
    | zero =>
        intro o ho
        obtain ⟨inputs, prev, kc, kc', -, hp, hcyc⟩ := runFromObs2_cycle hrun ho
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
        subst hp
        exact hinv σ F inputs _ kc o kc' hinit hcyc
    | succ c ih =>
        intro o ho
        obtain ⟨inputs, prev, kc, kc', -, hp, hcyc⟩ := runFromObs2_cycle hrun ho
        simp only [List.getElem?_cons_succ, List.getElem?_map] at hp
        cases hrc : r[c]? with
        | none => rw [hrc] at hp; cases hp
        | some oc =>
            rw [hrc] at hp
            simp only [Option.map_some, Option.some.injEq] at hp
            subst hp
            exact hinv σ F inputs _ kc o kc' (ih oc hrc) hcyc
  have hprevInv : ∀ (c : Nat) (prev : SvState),
      (initState2 d :: r.map CycleObs.post)[c]? = some prev → Inv prev := by
    intro c prev h
    cases c with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h; exact hinit
    | succ c =>
        simp only [List.getElem?_cons_succ, List.getElem?_map] at h
        cases hrc : r[c]? with
        | none => rw [hrc] at h; cases h
        | some oc =>
            rw [hrc] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h; exact hall c oc hrc
  intro c0 ps hstart hdrv
  obtain ⟨rr, hrr⟩ := hrst
  simp only [SeqTask.StartOK, hrr] at hstart
  have main : ∀ (ps : List (Bool × t.Ins N)) (c : Nat) (s : t.State N),
      (∀ j p, ps[j]? = some p →
        ∃ o, (r.map (CycleObs.map (Obs_run2.sample d)))[c + j]? = some o ∧ t.Holds N o.pre p) →
      (ps.head?.map Prod.fst = some true ∨
        ∃ prev, (initState2 d :: r.map CycleObs.post)[c]? = some prev ∧ R prev s) →
      ∀ j a, (t.scan N s ps)[j]? = some a →
        ∃ o, (r.map (CycleObs.map (Obs_run2.sample d)))[c + j]? = some o ∧ t.ObsOKS N o.post a := by
    intro ps
    induction ps with
    | nil => intro c s _ _ j a ha; simp [SeqTask.scan] at ha
    | cons p rest ih =>
        intro c s hdrv hpre j a ha
        obtain ⟨rb, v⟩ := p
        obtain ⟨o0, ho0, hd0⟩ := hdrv 0 (rb, v) (by simp)
        rw [Nat.add_zero] at ho0
        obtain ⟨o0', hrc, rfl⟩ := obs_run2_cycle ho0
        obtain ⟨inputs, prev, kc, kc', -, hprev, hcyc⟩ := runFromObs2_cycle hrun hrc
        have hInv := hprevInv c prev hprev
        have hboth : R o0'.post (t.next N s rb v) ∧
            t.ObsOKS N (Obs_run2.sample d o0'.post) (t.next N s rb v, v) := by
          cases rb with
          | true => exact hreset σ F inputs prev kc o0' kc' v hInv hcyc hd0
          | false =>
              have hRp : R prev s := by
                rcases hpre with hh | ⟨prev', hprev', hR'⟩
                · simp at hh
                · rw [hprev] at hprev'
                  have := Option.some.inj hprev'
                  subst this
                  exact hR'
              exact hstep σ F inputs prev kc o0' kc' s v hInv hRp hcyc hd0
        cases j with
        | zero =>
            simp only [SeqTask.scan, List.getElem?_cons_zero, Option.some.injEq] at ha
            subst ha
            exact ⟨o0'.map (Obs_run2.sample d), by simpa using ho0, hboth.2⟩
        | succ j =>
            simp only [SeqTask.scan, List.getElem?_cons_succ] at ha
            have hrest := ih (c + 1) (t.next N s rb v)
              (fun j' p' hp' => by
                obtain ⟨o, ho, hd⟩ := hdrv (j' + 1) p' (by simpa using hp')
                exact ⟨o, by rw [show c + 1 + j' = c + (j' + 1) by omega]; exact ho, hd⟩)
              (Or.inr ⟨o0'.post, by simp [hrc], hboth.1⟩) j a ha
            obtain ⟨o2, h2, h3⟩ := hrest
            exact ⟨o2, by rw [show c + (j + 1) = c + 1 + j by omega]; exact h2, h3⟩
  exact main ps c0 (t.init N) hdrv (Or.inl hstart)

/-! ## 2. The counter's cycle with both samples -/

open SvGolf.Seq.Counter

/-- The counter's pre part: the inputs applied, nothing else (no comb process, no reset event). -/
theorem cnt_pre (N : Nat) (σ : ScheduleOracle) (inputs : SvState) (c r e q : LVec) (k f : Nat) :
    cyclePre2 (cntD N) σ (f + 1) inputs (S c r e q) k =
      .ok (S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e) q, k + 1) := by
  unfold cyclePre2
  simp only [apply_cnt, cnt_combSettle, Res.ok_bind]
  exact resetPhase2_of_nil (cntD_resetIndices N _ _)

/-- The counter's state as the closed form's parameter: `clk`, `rst`, `en`, `q`. -/
def cntEnc (x : LVec × LVec × LVec × LVec) : SvState := S x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The counter's pre sample: the inputs applied, the old register. -/
def cntPreF (x : LVec × LVec × LVec × LVec) (e : SvState) : LVec × LVec × LVec × LVec :=
  (appIn e "clk" x.1, appIn e "rst" x.2.1, appIn e "en" x.2.2.1, x.2.2.2)

/-- The counter's post sample: the register updated by `cntNext`. -/
def cntPostF (N : Nat) (x : LVec × LVec × LVec × LVec) (e : SvState) : LVec × LVec × LVec × LVec :=
  (appIn e "clk" x.1, appIn e "rst" x.2.1, appIn e "en" x.2.2.1,
    cntNext N (appIn e "rst" x.2.1) (appIn e "en" x.2.2.1) x.2.2.2)

/-- **The counter's closed-form cycle** (`REdgeRun2`, R-EDGE's `run2` form), at every fuel from 12:
the sketch's `cnt_cycle` and `cnt_pre`. -/
theorem cnt_redge (N : Nat) : REdgeRun2 (cntD N) cntEnc (fun _ => True) cntPreF (cntPostF N) 12 := by
  rintro σ e ⟨c, r, en, q⟩ k f -
  exact ⟨⟨_, cnt_pre N σ e c r en q k (f + 11)⟩, ⟨_, cnt_cycle N σ e c r en q k (f + 12) (by omega)⟩⟩

/-- **The counter's cycle with both samples**, at any fuel: the pre sample is the state with the
inputs applied and the old register; the post sample has the register updated by `cntNext`. From the
generic `REdgeRun2.samples`. -/
theorem cnt_cycleObs_ok {N : Nat} {σ : ScheduleOracle} {inputs : SvState} {c r e q : LVec}
    {k F : Nat} {o : CycleObs SvState} {k' : Nat}
    (h : cycleObs2 (cntD N) σ F inputs (S c r e q) k = .ok (o, k')) :
    o.pre = S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e) q ∧
    o.post = S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e)
      (cntNext N (appIn inputs "rst" r) (appIn inputs "en" e) q) :=
  (cnt_redge N).samples (x := (c, r, e, q)) trivial h

/-! ## 3. The counter under the trusted convention -/

/-- The counter's ports, as read from a trusted sample of its state. -/
theorem cnt_read (N : Nat) (c r e q : LVec) :
    (Obs_run2.sample (cntD N) (S c r e q)).read "rst" = some r ∧
    (Obs_run2.sample (cntD N) (S c r e q)).read "en" = some e ∧
    (Obs_run2.sample (cntD N) (S c r e q)).read "q" = some q := by
  have hmem : ∀ n ∈ ["rst", "en", "q"], n ∈ (Obs_run2.iface (cntD N)).names := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;>
      simp [Iface.names, inputSigs, outputSigs, cntD]
  refine ⟨?_, ?_, ?_⟩
  · rw [Obs_run2.read_sample (hmem "rst" (by simp))]; simp [S, SvState.lookup]
  · rw [Obs_run2.read_sample (hmem "en" (by simp))]; simp [S, SvState.lookup]
  · rw [Obs_run2.read_sample (hmem "q" (by simp))]; simp [S, SvState.lookup]

theorem cnt_reset_cycleObs (N : Nat) :
    ∀ (σ : ScheduleOracle) (F : Nat) (inputs prev : SvState) (k : Nat) (o : CycleObs SvState)
      (k' : Nat) (v : cntTask.Ins N), Sh N prev →
      cycleObs2 (cntD N) σ F inputs prev k = .ok (o, k') →
      cntTask.Holds N (Obs_run2.sample (cntD N) o.pre) (true, v) →
      Rel N o.post (cntTask.init N) ∧
        cntTask.ObsOKS N (Obs_run2.sample (cntD N) o.post) (cntTask.init N, v) := by
  intro σ F inputs prev k o k' v hs h hd
  obtain ⟨en, ⟨⟩⟩ := v
  obtain ⟨c, r, e, q, rfl, hw⟩ := hs
  obtain ⟨hpre, hpost⟩ := cnt_cycleObs_ok h
  rw [hpre] at hd
  rw [hpost]
  obtain ⟨hr, -, -⟩ := cnt_read N (appIn inputs "clk" c) (appIn inputs "rst" r)
    (appIn inputs "en" e) q
  simp only [SeqTask.Holds, SeqTask.RstHolds, cntTask, hr, Option.some.injEq] at hd
  have hc : (appIn inputs "rst" r).condTrue = true := by
    rw [hd.1, LVec.condTrue_ofBitVec]; decide
  rw [cntNext_reset N _ q hc hw]
  refine ⟨⟨_, _, _, rfl⟩, ?_⟩
  obtain ⟨-, -, hq⟩ := cnt_read N (appIn inputs "clk" c) (appIn inputs "rst" r)
    (appIn inputs "en" e) (LVec.ofBitVec (0#N))
  simp [SeqTask.ObsOKS, cntTask, HoldAllS, hq]

theorem cnt_step_cycleObs (N : Nat) :
    ∀ (σ : ScheduleOracle) (F : Nat) (inputs prev : SvState) (k : Nat) (o : CycleObs SvState)
      (k' : Nat) (s : BitVec N) (v : cntTask.Ins N), Sh N prev → Rel N prev s →
      cycleObs2 (cntD N) σ F inputs prev k = .ok (o, k') →
      cntTask.Holds N (Obs_run2.sample (cntD N) o.pre) (false, v) →
      Rel N o.post (cntTask.step N s v) ∧
        cntTask.ObsOKS N (Obs_run2.sample (cntD N) o.post) (cntTask.step N s v, v) := by
  intro σ F inputs prev k o k' s v _ hrel h hd
  obtain ⟨en, ⟨⟩⟩ := v
  obtain ⟨c, r, e, hprev⟩ := hrel
  subst hprev
  obtain ⟨hpre, hpost⟩ := cnt_cycleObs_ok h
  rw [hpre] at hd
  rw [hpost]
  obtain ⟨hr, he, -⟩ := cnt_read N (appIn inputs "clk" c) (appIn inputs "rst" r)
    (appIn inputs "en" e) (LVec.ofBitVec s)
  simp only [SeqTask.Holds, SeqTask.RstHolds, cntTask, HoldAllS, hr, he, Option.some.injEq] at hd
  obtain ⟨hrst, hen, -⟩ := hd
  have hc : (appIn inputs "rst" r).condTrue = false := by
    rw [hrst, LVec.condTrue_ofBitVec]; rfl
  rcases bv1_cases en with h0 | h1
  · have hec : (appIn inputs "en" e).condTrue = false := by
      rw [hen, h0, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_hold N _ hc hec]
    obtain ⟨-, -, hq⟩ := cnt_read N (appIn inputs "clk" c) (appIn inputs "rst" r)
      (appIn inputs "en" e) (LVec.ofBitVec s)
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, h0]
    · simp [SeqTask.ObsOKS, cntTask, HoldAllS, hq, h0]
  · have hec : (appIn inputs "en" e).condTrue = true := by
      rw [hen, h1, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_inc N s hc hec]
    obtain ⟨-, -, hq⟩ := cnt_read N (appIn inputs "clk" c) (appIn inputs "rst" r)
      (appIn inputs "en" e) (LVec.ofBitVec (s + 1#N))
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, h1]
    · simp [SeqTask.ObsOKS, cntTask, HoldAllS, hq, h1]

theorem cnt_sh_cycleObs {N : Nat} :
    ∀ (σ : ScheduleOracle) (F : Nat) (inputs prev : SvState) (k : Nat) (o : CycleObs SvState)
      (k' : Nat), Sh N prev → cycleObs2 (cntD N) σ F inputs prev k = .ok (o, k') → Sh N o.post := by
  intro σ F inputs prev k o k' hs h
  obtain ⟨c, r, e, q, rfl, hw⟩ := hs
  rw [(cnt_cycleObs_ok h).2]
  exact ⟨_, _, _, _, rfl, by rw [cntNext_width]; exact hw⟩

/-- The counter writes none of its input ports: the syntactic check (`rfl` at symbolic `N`; `decide`
closes it at a concrete `N`). -/
theorem cnt_writesInput (N : Nat) : (cntD N).writesInput = false := by
  rfl

/-- **The counter under the trusted convention**, at every `N`: interface; the clock discipline,
progress and receptiveness; and from every reset, with inputs read from the pre samples, the post
samples of `q` are the spec counter. -/
theorem cnt_satisfiedAt_obs (N : Nat) :
    cntTask.SatisfiedAt_obs Obs_run2 cntTask.Disciplined N (cntD N) := by
  refine ⟨cnt_interface N, ⟨cnt_disciplined N, Obs_run2.progress_of_terminates _ _ (cnt_terminates N),
    receptive_of_writesInput (cnt_writesInput N) (cnt_terminates N) ?_ ?_⟩, ?_⟩
  · intro p hp
    simp [SeqTask.free, cntTask] at hp
    rcases hp with rfl | rfl <;> simp [Design2.inputNames, cntD]
  · simp [SeqTask.free, cntTask]
  · exact follows_obs_of_cycle cntTask N (cntD N) ⟨_, rfl⟩ (Sh N) (Rel N) (sh_init N)
      (fun σ F inputs prev k o k' hs h => cnt_sh_cycleObs σ F inputs prev k o k' hs h)
      (cnt_reset_cycleObs N) (cnt_step_cycleObs N)

/-- The counter's challenge statement under the trusted convention, for any declared-type range. -/
theorem cnt_statement_obs (ty : Nat → Prop) :
    cntTask.Statement_obs ty Obs_run2 cntTask.Disciplined cntD :=
  fun N _ _ => cnt_satisfiedAt_obs N

/-- **The counter satisfies the Task v2 skeleton** (`Sat` of its compiled `Spec`), provisional over
`run2`, with the parameter bounded by `int`'s range. -/
theorem cnt_sat : Sat Obs_run2 cntTask.Disciplined (cntTask.toSpec IntParam) cntD :=
  (cntTask.statement_obs_iff_sat).mp (cnt_statement_obs IntParam)

#print axioms follows_obs_of_cycle
#print axioms cnt_pre
#print axioms cnt_redge
#print axioms cnt_cycleObs_ok
#print axioms cnt_read
#print axioms cnt_reset_cycleObs
#print axioms cnt_step_cycleObs
#print axioms cnt_sh_cycleObs
#print axioms cnt_writesInput
#print axioms cnt_satisfiedAt_obs
#print axioms cnt_statement_obs
#print axioms cnt_sat

end SvGolf.Arch.Seq
