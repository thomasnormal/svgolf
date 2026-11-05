import CounterObs
import LeanModels.Sv.CycleMachine

/-!
# The counter's cycle machine (D6) and its provisional R-CYCLE (Day 6)

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status: provisional over `run2`.** R-CYCLE here is against `Obs_run2`, and the design is the
hand-built family `cntD` of `../sequential/CounterCycle.lean`.

**Superseded (lead's ruling, 11-03) for the counter's cycle step.** Agent A derives that step from E
(`cnt_rise_step`, arch-x1 728b6ee2, against this directory's `cntTask` step and init), so it carries
the authority label. This `run2` version is a provisional duplicate. It is kept, unchanged, only as
the exemplar of the D6 shape and of `followsB_run`; do not extend it.

## What is here

1. `SeqTask.followsB_run`: **`satisfiedAt_of_cycle` restated over D6** (ARCH-NOTE §5.6, item 3),
   losing the schedule, the fuel and the `SvState`. A store invariant, a simulation relation to the
   spec state, and a reset and a step lemma about the pure `out`/`next` of a machine give the
   sequential guarantee for every run of the machine from its start policy.
2. `cntMachine N`: the counter as a cycle machine.
   - `Store = LVec` (the register `q`); `In` = the held `clk`, `rst`, `en`; `Tick = Unit`.
   - Start policy: `q = x` (`run2`'s start: no initializer).
   - `out`: the four ports. `next`: `cntNext`.
   `cnt_rcycle` is R-CYCLE for it: every completed `Obs_run2` behaviour of `cntD N` IS the machine's
   run on the stimulus's held inputs (exact on observations). Its one-cycle obligation is the
   closed-form cycle `cnt_cycleObs_ok`.
3. `cnt_follows_obs_via_machine`: the counter's trusted guarantee, proved on the machine only (pure
   `cntNext` algebra, no `run2`) and moved to the design by `Obs_run2.safe_of_rcycle`. This is the
   proof route D6 is for. `CounterObs.lean` proves the same statement directly on `run2`
   (`follows_obs_of_cycle`); the two routes are compared in the report.
-/

namespace SvGolf.Arch.Seq

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Seq SvGolf.Arch

/-! ## 1. `satisfiedAt_of_cycle` over D6 -/

/-- **The sequential guarantee from a machine's one-cycle facts** (no schedule, no fuel, no state of
the interpreter). For a task with a reset port: a store invariant `Inv` (true on the start policy,
kept by `next`), a simulation `R` to the spec state, a reset lemma and a step lemma about the pure
`out`/`next` give `FollowsB` for every run from the start policy. -/
theorem followsB_run (t : SeqTask) (N : Nat) (m : CycleMachine) (tk : m.Tick)
    (hrst : ∃ r, t.rst = some r)
    (Inv : m.Store → Prop) (R : m.Store → t.State N → Prop)
    (hinit : ∀ s, m.init s → Inv s) (hinv : ∀ s i, Inv s → Inv (m.next s i tk))
    (hreset : ∀ s i (v : t.Ins N), Inv s → t.Holds N (m.out s i) (true, v) →
      R (m.next s i tk) (t.init N) ∧ t.ObsOKS N (m.out (m.next s i tk) i) (t.init N, v))
    (hstep : ∀ s i (q : t.State N) (v : t.Ins N), Inv s → R s q →
      t.Holds N (m.out s i) (false, v) →
      R (m.next s i tk) (t.step N q v) ∧ t.ObsOKS N (m.out (m.next s i tk) i) (t.step N q v, v)) :
    ∀ s0, m.init s0 → ∀ is, t.FollowsB N (m.run tk s0 is) := by
  have hInvAt : ∀ (s : m.Store) (is : List m.In), Inv s → Inv (m.storeAt tk s is) := by
    intro s is
    induction is generalizing s with
    | nil => exact id
    | cons i is ih => exact fun h => ih _ (hinv s i h)
  -- the main induction, from cycle 0 of a run: along `ps`, from a reset or from an `R`-related store
  have main : ∀ (ps : List (Bool × t.Ins N)) (s : m.Store) (is : List m.In) (q : t.State N),
      Inv s → (ps.head?.map Prod.fst = some true ∨ R s q) →
      (∀ (j : Nat) (p : Bool × t.Ins N), ps[j]? = some p →
        ∃ o : CycleObs PortSample, (m.run tk s is)[j]? = some o ∧ t.Holds N o.pre p) →
      ∀ (j : Nat) (a : t.State N × t.Ins N), (t.scan N q ps)[j]? = some a →
        ∃ o : CycleObs PortSample, (m.run tk s is)[j]? = some o ∧ t.ObsOKS N o.post a := by
    intro ps
    induction ps with
    | nil => intro s is q _ _ _ j a ha; simp [SeqTask.scan] at ha
    | cons p rest ih =>
        intro s is q hI hpre hdrv j a ha
        obtain ⟨rb, v⟩ := p
        obtain ⟨o0, ho0, hd0⟩ := hdrv 0 (rb, v) (by simp)
        cases is with
        | nil => simp at ho0
        | cons i is =>
            simp only [CycleMachine.run_cons, List.getElem?_cons_zero, Option.some.injEq] at ho0
            subst ho0
            have hboth : R (m.next s i tk) (t.next N q rb v) ∧
                t.ObsOKS N (m.out (m.next s i tk) i) (t.next N q rb v, v) := by
              cases rb with
              | true => exact hreset s i v hI hd0
              | false =>
                  have hR : R s q := by
                    rcases hpre with hh | hR
                    · simp at hh
                    · exact hR
                  exact hstep s i q v hI hR hd0
            cases j with
            | zero =>
                simp only [SeqTask.scan, List.getElem?_cons_zero, Option.some.injEq] at ha
                subst ha
                exact ⟨_, rfl, hboth.2⟩
            | succ j =>
                simp only [SeqTask.scan, List.getElem?_cons_succ] at ha
                obtain ⟨o, ho, hok⟩ := ih (m.next s i tk) is (t.next N q rb v) (hinv s i hI)
                  (Or.inr hboth.1)
                  (fun j' p' hp' => by
                    obtain ⟨o, ho, hd⟩ := hdrv (j' + 1) p' (by simpa using hp')
                    exact ⟨o, by simpa using ho, hd⟩) j a ha
                exact ⟨o, by simpa using ho, hok⟩
  intro s0 hs0 is c0 ps hstart hdrv j a ha
  obtain ⟨rr, hrr⟩ := hrst
  simp only [SeqTask.StartOK, hrr] at hstart
  -- shift to cycle `c0`: the run from the store after `c0` cycles
  have hshift : ∀ n, (m.run tk s0 is)[c0 + n]? =
      (m.run tk (m.storeAt tk s0 (is.take c0)) (is.drop c0))[n]? := by
    intro n
    rw [← CycleMachine.run_drop, List.getElem?_drop]
  obtain ⟨o, ho, hok⟩ := main ps _ _ (t.init N) (hInvAt s0 _ (hinit s0 hs0)) (Or.inl hstart)
    (fun j p hp => by
      obtain ⟨o, ho, hd⟩ := hdrv j p hp
      exact ⟨o, by rw [← hshift]; exact ho, hd⟩) j a ha
  exact ⟨o, by rw [hshift]; exact ho, hok⟩

/-! ## 2. The counter as a cycle machine, and R-CYCLE -/

open SvGolf.Seq.Counter

/-- The counter's ports as a trusted sample. -/
def cntOut (q : LVec) (i : LVec × LVec × LVec) : PortSample :=
  ⟨[("clk", i.1), ("rst", i.2.1), ("en", i.2.2), ("q", q)]⟩

/-- **The counter's cycle machine** at width `N`. -/
def cntMachine (N : Nat) : CycleMachine where
  Store := LVec
  In := LVec × LVec × LVec
  Tick := Unit
  init q := q = LVec.xVec N
  out := cntOut
  next q i _ := cntNext N i.2.1 i.2.2 q

/-- How a stimulus entry updates the held `clk`, `rst`, `en` (`applyInputs2`'s rule). -/
def cntHold (i : LVec × LVec × LVec) (e : SvState) : LVec × LVec × LVec :=
  (appIn e "clk" i.1, appIn e "rst" i.2.1, appIn e "en" i.2.2)

/-- The held inputs before the first entry (`initState2`: no initializers, so `x`). -/
def cntI0 : LVec × LVec × LVec := (LVec.xVec 1, LVec.xVec 1, LVec.xVec 1)

theorem cnt_sample_S (N : Nat) (c r e q : LVec) :
    Obs_run2.sample (cntD N) (S c r e q) = cntOut q (c, r, e) := by
  rfl

/-- **R-CYCLE for the counter** (provisional over `run2`): every completed `Obs_run2` behaviour of
`cntD N` is the machine's run, from the start policy, on the stimulus's held inputs. -/
theorem cnt_rcycle (N : Nat) :
    ∀ σ stim b, Obs_run2.Behaves (cntD N) σ stim b →
      ∃ s, (cntMachine N).init s ∧
        b = (cntMachine N).run () s (heldInputs cntHold cntI0 stim) := by
  refine rcycle_run2 (cntMachine N) () cntHold cntI0
    (fun st q i => st = S i.1 i.2.1 i.2.2 q) (LVec.xVec N) rfl
    (by simp [initState2, cntD, S, cntI0]) ?_
  rintro σ F e prev k o k' q ⟨c, r, en⟩ rfl h
  obtain ⟨hpre, hpost⟩ := cnt_cycleObs_ok h
  refine ⟨?_, ?_, hpost⟩
  · rw [hpre]; exact cnt_sample_S N _ _ _ _
  · rw [hpost]; exact cnt_sample_S N _ _ _ _

/-! ## 3. The counter's guarantee, proved on the machine -/

theorem cntOut_read (q : LVec) (i : LVec × LVec × LVec) :
    (cntOut q i).read "rst" = some i.2.1 ∧ (cntOut q i).read "en" = some i.2.2 ∧
    (cntOut q i).read "q" = some q := by
  simp [cntOut, PortSample.read, SvState.lookup]

/-- **The counter's guarantee on its machine**: pure `cntNext` algebra. -/
theorem cnt_followsB_machine (N : Nat) :
    ∀ s0, (cntMachine N).init s0 → ∀ is, cntTask.FollowsB N ((cntMachine N).run () s0 is) := by
  refine followsB_run cntTask N (cntMachine N) () ⟨_, rfl⟩ (fun q => q.width = N)
    (fun q s => q = LVec.ofBitVec s) ?_ ?_ ?_ ?_
  · rintro q rfl; simp [LVec.xVec, LVec.width, LVec.replicate]
  · intro q i h; exact (cntNext_width N _ _ q).trans h
  · rintro q ⟨c, r, e⟩ ⟨en, ⟨⟩⟩ hw hd
    obtain ⟨hr, -, -⟩ := cntOut_read q (c, r, e)
    simp only [SeqTask.Holds, SeqTask.RstHolds, cntTask, cntMachine, hr, Option.some.injEq] at hd
    have hc : r.condTrue = true := by
      rw [hd.1, LVec.condTrue_ofBitVec]; rfl
    have hn : (cntMachine N).next q (c, r, e) () = LVec.ofBitVec (0#N) := cntNext_reset N e q hc hw
    refine ⟨hn, ?_⟩
    rw [hn]
    simp [SeqTask.ObsOKS, cntTask, cntMachine, HoldAllS, cntOut, PortSample.read, SvState.lookup]
  · rintro q ⟨c, r, e⟩ s ⟨en, ⟨⟩⟩ _ rfl hd
    change BitVec N at s
    obtain ⟨hr, he, -⟩ := cntOut_read (LVec.ofBitVec s) (c, r, e)
    simp only [SeqTask.Holds, SeqTask.RstHolds, cntTask, cntMachine, HoldAllS, hr, he,
      Option.some.injEq] at hd
    obtain ⟨hrst, hen, -⟩ := hd
    have hc : r.condTrue = false := by
      rw [hrst, LVec.condTrue_ofBitVec]; rfl
    rcases bv1_cases en with h0 | h1
    · have hec : e.condTrue = false := by
        rw [hen, h0, LVec.condTrue_ofBitVec]; rfl
      have hn : (cntMachine N).next (LVec.ofBitVec s) (c, r, e) () = LVec.ofBitVec s :=
        cntNext_hold N _ hc hec
      refine ⟨by rw [hn]; simp [cntTask, h0] <;> rfl, ?_⟩
      rw [hn]
      simp [SeqTask.ObsOKS, cntTask, cntMachine, HoldAllS, cntOut, PortSample.read, SvState.lookup, h0]
    · have hec : e.condTrue = true := by
        rw [hen, h1, LVec.condTrue_ofBitVec]; rfl
      have hn : (cntMachine N).next (LVec.ofBitVec s) (c, r, e) () = LVec.ofBitVec (s + 1#N) :=
        cntNext_inc N s hc hec
      refine ⟨by rw [hn]; simp [cntTask, h1] <;> rfl, ?_⟩
      rw [hn]
      simp [SeqTask.ObsOKS, cntTask, cntMachine, HoldAllS, cntOut, PortSample.read, SvState.lookup, h1]

/-- **The counter's trusted guarantee, through D6**: proved on the machine
(`cnt_followsB_machine`) and moved to the design by R-CYCLE (`Obs_run2.safe_of_rcycle`). The same
statement as `CounterObs.lean`'s, by the other route. -/
theorem cnt_follows_obs_via_machine (N : Nat) : cntTask.Follows_obs Obs_run2 N (cntD N) :=
  Obs_run2.safe_of_rcycle (cntMachine N) () cntHold cntI0 (cnt_rcycle N)
    (Q := fun _ b => cntTask.FollowsB N b) fun s hs is => cnt_followsB_machine N s hs is

#print axioms followsB_run
#print axioms cnt_sample_S
#print axioms cnt_rcycle
#print axioms cntOut_read
#print axioms cnt_followsB_machine
#print axioms cnt_follows_obs_via_machine

end SvGolf.Arch.Seq
