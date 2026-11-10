import SvGolf.TaskSeq
import LeanModels.Sv.Known2
import LeanModels.Sv.Seq2Cycle

/-!
# Proof helpers for sequential tasks (untrusted, kernel-checked)

Nothing here is part of the trusted base. It goes with the trusted text `SvGolf/TaskSeq.lean` (`ClockedBy`,
`TxTask` and `StreamTask` final; `SeqTask` a DRAFT): the reductions a clocked reference proof targets, each from a few facts about
ONE cycle.

## API

* `SeqTask.scan_getElem?_snd`: the spec machine's `scan` keeps each cycle's inputs.
* `CombTask.toSeq`, `toSeq_interface`, `toSeq_follows_iff`, **`toSeq_satisfiedAt_iff`**: a combinational task is
  the one-point-state case of a sequential one (no clock, no reset, `State = Unit`), and the two statements agree
  but for two conjuncts: `SeqTask.Interface` asks for distinct declaration names, which `CombTask.Interface` does
  not (decided 2026-11-06), and the combinational statement asks for `LoopFree` (2026-11-06), which the sequential
  statement does not. So the sequential statement does not move any combinational task beyond those two.
* **`SeqTask.satisfiedAt_of_cycle`**, the reduction theorem of `SeqTask`: for a task with a reset port, the
  statement at one parameter value follows from the interface, the discipline, termination, and three facts about
  ONE cycle (`cycleStep2`): an invariant `Inv` on snapshots, a reset lemma (a cycle that asserts reset yields the
  spec's `init` and its observation, from ANY invariant state), and a step lemma (a cycle that does not assert
  reset, from a snapshot related to the spec state `s` by `R`, yields `step s v` and its observation). Fuel,
  schedules, the trace and the stimulus list never appear in those facts.
* `BitIs.unique`, `StimBit.unique`, `BitIs.appIn_eq`: known bits of states and stimulus entries.
* **`TxTask.satisfiedAt_of_phases`**, the transaction-protocol reduction: the `TxTask` statement from the
  interface, the discipline, termination and a `TxTask.PhaseModel` (phases `Ready`, `Busy x m` with a measure
  `m < lat` counting down to `done`, `Fin x`; one-`Step` reset, start, busy and hold obligations). Release, horizon,
  `Idle`, held operands and back-to-back starts (C1 to C5, interpretation points 4 and 5) are discharged once, here.
* **`StreamTask.satisfiedAt_of_phases`**, the stream-protocol reduction (C8): a `StreamTask.PhaseModel` (phases
  `Ready`, `At ys j` and the schedule `out`); `Idle`, `in_valid` and back-to-back starts are discharged once, here.
  Its helpers: `StreamTask.InputsAt` (the inputs after a start) with `inputs_unique`/`inputs_snoc`, the emitted
  values (`emitted_nil`, `emitted_add`, `emitted_stable`, `emitted_match`), and the history `Hist` of a trace
  (`hist_snoc`, `shows_hist`).

Both phase models extend `LeanModels.Sv.CycleModel` (`Seq2Cycle.lean`): the design's clock step as a relation on
a `Shape` of states.
-/

namespace SvGolf

open LeanModels.Sv

namespace SeqTask

variable (t : SeqTask)

/-- `scan` keeps each cycle's data inputs: the `j`-th entry of the scan carries `ps[j]`'s. -/
theorem scan_getElem?_snd (N : Nat) :
    ∀ (s : t.State N) (ps : List (Bool × t.Ins N)) (j : Nat),
      ((t.scan N s ps)[j]?).map Prod.snd = (ps[j]?).map Prod.snd
  | _, [], j => by simp [scan]
  | s, (r, v) :: rest, 0 => by simp [scan]
  | s, (r, v) :: rest, j + 1 => by
      simp only [scan, List.getElem?_cons_succ]
      exact scan_getElem?_snd N _ rest j

end SeqTask

/-! ## `CombTask` is the degenerate case -/

/-- A combinational task as a sequential one: no clock, no reset, a one-point state. -/
def CombTask.toSeq (c : CombTask) : SeqTask where
  inRange := c.inRange
  clk := none
  rst := none
  inputs := c.inputs
  outputs := c.outputs
  State := fun _ => Unit
  init := fun _ => ()
  step := fun _ _ _ => ()
  obs := fun N _ v => c.fn N v

/-- The sequential interface of `c.toSeq` is `c`'s interface and distinct declaration names. -/
theorem CombTask.toSeq_interface (c : CombTask) (N : Nat) (d : Design2) :
    c.toSeq.Interface N d ↔ c.Interface N d ∧ (d.decls.toList.map Decl.name).Nodup := by
  simp [SeqTask.Interface, SeqTask.ports, CombTask.toSeq, CombTask.Interface, and_assoc]

/-- **The combinational claim is the one-point-state case of the sequential one.** -/
theorem CombTask.toSeq_follows_iff (c : CombTask) (N : Nat) (d : Design2) :
    c.toSeq.Follows N d ↔ c.Computes N d := by
  constructor
  · intro h σ stim tr hr cyc inputs st hi hc v hv
    have key := h σ stim tr hr cyc [(false, v)] trivial
      (fun j p hjp => by
        cases j with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hjp
            subst hjp
            exact ⟨inputs, by simpa using hi, rfl, hv⟩
        | succ j => simp at hjp)
      0 ((), v) (by rfl)
    obtain ⟨st', hst', hobs⟩ := key
    have : st' = st := by
      rw [Nat.add_zero] at hst'
      rw [hc] at hst'
      exact (Option.some.inj hst').symm
    subst this
    exact hobs
  · intro h σ stim tr hr c0 ps _ hps j a ha
    have hsnd := (SeqTask.scan_getElem?_snd c.toSeq N (c.toSeq.init N) ps j)
    rw [ha] at hsnd
    obtain ⟨p, hp⟩ : ∃ p, ps[j]? = some p := by
      cases hpj : ps[j]? with
      | none => rw [hpj] at hsnd; simp at hsnd
      | some p => exact ⟨p, rfl⟩
    rw [hp] at hsnd
    simp only [Option.map_some, Option.some.injEq] at hsnd
    obtain ⟨e, he, hrd, hhold⟩ := hps j p hp
    have hlt : c0 + j < stim.length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨st, hst⟩ := hr.exists_snapshot hlt
    refine ⟨st, hst, ?_⟩
    have := h σ stim tr hr (c0 + j) e st he hst p.2 hhold
    have key : ∀ (x y : Vals ((c.inputs N).map Prod.snd)), x = y →
        HoldAll st (c.outputs N) (c.fn N y) → HoldAll st (c.outputs N) (c.fn N x) := by
      intro x y hxy hy; subst hxy; exact hy
    exact key a.2 p.2 hsnd this

/-- The whole statements agree at a parameter value: **`CombTask` is the degenerate case of
`SeqTask`** (same interface, plus distinct declaration names; same `Unclocked`, same termination,
same claim), with the combinational statement's `LoopFree` on top. -/
theorem CombTask.toSeq_satisfiedAt_iff (c : CombTask) (N : Nat) (d : Design2) :
    c.toSeq.SatisfiedAt N d ∧ LoopFree d ↔
      c.SatisfiedAt N d ∧ (d.decls.toList.map Decl.name).Nodup := by
  unfold SeqTask.SatisfiedAt CombTask.SatisfiedAt
  rw [CombTask.toSeq_interface, CombTask.toSeq_follows_iff]
  constructor
  · rintro ⟨⟨⟨hi, hn⟩, ⟨hu, ht⟩, hc⟩, hl⟩
    exact ⟨⟨hi, ⟨hu, hl, ht⟩, hc⟩, hn⟩
  · rintro ⟨⟨hi, ⟨hu, hl, ht⟩, hc⟩, hn⟩
    exact ⟨⟨⟨hi, hn⟩, ⟨hu, ht⟩, hc⟩, hl⟩

/-! ## Runs from a start state

`RunFrom d σ st0 stim tr`: some fuel completes `runFrom2` from `st0`. It is what the reductions below
read off a run: v1's `Runs2` is a `RunFrom` from `initState2 d` (`Runs2.runFrom`), and txtask-v2's
`RunsAt` a `RunFrom` from a power-up state (`RunsAt.runFrom`, `SvGolf/SeqV2.lean`), so one proof of a
claim from a start state of the invariant serves both. -/

/-- A completed `runFrom2` from `st0`. -/
def RunFrom (d : Design2) (σ : ScheduleOracle) (st0 : SvState) (stim tr : List SvState) : Prop :=
  ∃ fuel, runFrom2 d σ fuel st0 0 stim = .ok tr

theorem Runs2.runFrom {d : Design2} {σ : ScheduleOracle} {stim tr : List SvState}
    (h : Runs2 d σ stim tr) : RunFrom d σ (initState2 d) stim tr :=
  let ⟨fuel, hr⟩ := h; ⟨fuel, run2_from_ok hr⟩

theorem RunFrom.exists_snapshot {d : Design2} {σ : ScheduleOracle} {st0 : SvState}
    {stim tr : List SvState} (h : RunFrom d σ st0 stim tr) {c : Nat} (hc : c < stim.length) :
    ∃ st, tr[c]? = some st := by
  obtain ⟨fuel, hr⟩ := h
  have hl := runFrom2_length hr
  exact ⟨tr[c]'(hl ▸ hc), List.getElem?_eq_getElem _⟩

theorem RunFrom.snapshot_step {d : Design2} {σ : ScheduleOracle} {st0 : SvState}
    {stim tr : List SvState} (h : RunFrom d σ st0 stim tr) {c : Nat} {st : SvState}
    (hc : tr[c]? = some st) : ∃ fuel inputs prev k k', stim[c]? = some inputs ∧
      (st0 :: tr)[c]? = some prev ∧ cycleStep2 d σ fuel inputs prev k = .ok (st, k') := by
  obtain ⟨fuel, hr⟩ := h
  obtain ⟨inputs, prev, k, k', hi, hp, hs⟩ := runFrom2_snapshot hr hc
  exact ⟨fuel, inputs, prev, k, k', hi, hp, hs⟩

theorem RunFrom.forall_of_step {d : Design2} {σ : ScheduleOracle} {st0 : SvState}
    {stim tr : List SvState} {I : SvState → Prop} (hinit : I st0)
    (hstep : ∀ (fuel : Nat) (inputs prev : SvState) (k : Nat) (st : SvState) (k' : Nat),
      I prev → cycleStep2 d σ fuel inputs prev k = .ok (st, k') → I st)
    (h : RunFrom d σ st0 stim tr) : ∀ (c : Nat) (st : SvState), tr[c]? = some st → I st := by
  intro c
  induction c with
  | zero =>
      intro st hc
      obtain ⟨fuel, inputs, prev, k, k', _, hp, hs⟩ := h.snapshot_step hc
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact hstep fuel inputs _ k st k' hinit hs
  | succ c ih =>
      intro st hc
      obtain ⟨fuel, inputs, prev, k, k', _, hp, hs⟩ := h.snapshot_step hc
      simp only [List.getElem?_cons_succ] at hp
      exact hstep fuel inputs prev k st k' (ih prev hp) hs

/-- `CycleModel.snapshot` from a start state of the shape: every snapshot of a run from `st0` is a
`Step` from the previous snapshot (`st0` at cycle 0), which has the shape. -/
theorem CycleModel.snapshotFrom {d : Design2} (M : CycleModel d) {σ : ScheduleOracle}
    {st0 : SvState} {stim tr : List SvState} (h0 : M.Shape st0) (hr : RunFrom d σ st0 stim tr)
    {c : Nat} {st : SvState} (hc : tr[c]? = some st) : ∃ e prev, stim[c]? = some e ∧
      (st0 :: tr)[c]? = some prev ∧ M.Shape prev ∧ M.Step e prev st := by
  obtain ⟨F, e, prev, k, k', he, hp, hs⟩ := hr.snapshot_step hc
  have hsh : M.Shape prev := by
    cases c with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; exact hp ▸ h0
    | succ c => exact hr.forall_of_step h0 (fun F e q k s k' hq hs =>
        M.shape e q s hq (M.cycle σ F e q k s k' hq hs)) c prev (by simpa using hp)
  exact ⟨e, prev, he, hp, hsh, M.cycle σ F e prev k st k' hsh hs⟩

/-! ## The reduction theorem: refinement by an invariant -/

/-- **The claim of `SeqTask` from a cycle invariant**, for one completed run from a start state
`st0` of the invariant `Inv` (kept by every successful cycle): a relation `R` between a snapshot
and the spec state, a RESET cycle lemma (any successful cycle whose entry asserts reset yields `R`
with `init` and the spec's observation, from ANY invariant state) and a STEP cycle lemma (any
successful cycle whose entry does not assert reset, from a snapshot related to `s`, yields `R`
with `step s v` and the observation) give the claim on that run. -/
theorem SeqTask.claim_of_cycle (t : SeqTask) (N : Nat) (d : Design2)
    (hrst : ∃ r, t.rst = some r)
    (Inv : SvState → Prop) (R : SvState → t.State N → Prop)
    (hinv : ∀ σ F inputs prev k st k', Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → Inv st)
    (hreset : ∀ σ F inputs prev k st k' (v : t.Ins N), Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (true, v) →
        R st (t.init N) ∧ t.ObsOK N st (t.init N, v))
    (hstep : ∀ σ F inputs prev k st k' (s : t.State N) (v : t.Ins N), Inv prev → R prev s →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (false, v) →
        R st (t.step N s v) ∧ t.ObsOK N st (t.step N s v, v))
    {σ : ScheduleOracle} {st0 : SvState} {stim tr : List SvState} (hinit : Inv st0)
    (hr : RunFrom d σ st0 stim tr) :
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a := by
  intro c0 ps hstart hdrv
  obtain ⟨rr, hrr⟩ := hrst
  simp only [SeqTask.StartOK, hrr] at hstart
  have hall : ∀ (c : Nat) (st : SvState), tr[c]? = some st → Inv st :=
    hr.forall_of_step hinit (fun fuel inputs prev k st k' hp hc => hinv σ fuel inputs prev k st k' hp hc)
  have hprevInv : ∀ (c : Nat) (prev : SvState), (st0 :: tr)[c]? = some prev → Inv prev := by
    intro c prev h
    cases c with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h; exact hinit
    | succ c =>
        simp only [List.getElem?_cons_succ] at h
        exact hall c prev h
  have main : ∀ (ps : List (Bool × t.Ins N)) (c : Nat) (s : t.State N),
      (∀ j p, ps[j]? = some p → ∃ e, stim[c + j]? = some e ∧ t.Drives N e p) →
      (ps.head?.map Prod.fst = some true ∨
        ∃ prev, (st0 :: tr)[c]? = some prev ∧ R prev s) →
      ∀ j a, (t.scan N s ps)[j]? = some a → ∃ st, tr[c + j]? = some st ∧ t.ObsOK N st a := by
    intro ps
    induction ps with
    | nil => intro c s _ _ j a ha; simp [SeqTask.scan] at ha
    | cons p rest ih =>
        intro c s hdrv hpre j a ha
        obtain ⟨r, v⟩ := p
        obtain ⟨e0, he0, hd0⟩ := hdrv 0 (r, v) (by simp)
        rw [Nat.add_zero] at he0
        have hlt : c < stim.length := (List.getElem?_eq_some_iff.mp he0).1
        obtain ⟨st, hst⟩ := hr.exists_snapshot hlt
        obtain ⟨fuel, inputs, prev, k, k', hin, hprev, hcyc⟩ := hr.snapshot_step hst
        have hinputs : inputs = e0 := Option.some.inj (hin.symm.trans he0)
        subst hinputs
        have hInv := hprevInv c prev hprev
        have hboth : R st (t.next N s r v) ∧ t.ObsOK N st (t.next N s r v, v) := by
          cases r with
          | true => exact hreset σ fuel inputs prev k st k' v hInv hcyc hd0
          | false =>
              have hRp : R prev s := by
                rcases hpre with hh | ⟨prev', hprev', hR'⟩
                · simp at hh
                · rw [hprev] at hprev'
                  have := Option.some.inj hprev'
                  subst this
                  exact hR'
              exact hstep σ fuel inputs prev k st k' s v hInv hRp hcyc hd0
        cases j with
        | zero =>
            simp only [SeqTask.scan, List.getElem?_cons_zero, Option.some.injEq] at ha
            subst ha
            exact ⟨st, by simpa using hst, hboth.2⟩
        | succ j =>
            simp only [SeqTask.scan, List.getElem?_cons_succ] at ha
            have hrest := ih (c + 1) (t.next N s r v)
              (fun j' p' hp' => by
                obtain ⟨e, he, hd⟩ := hdrv (j' + 1) p' (by simpa using hp')
                exact ⟨e, by rw [show c + 1 + j' = c + (j' + 1) by omega]; exact he, hd⟩)
              (Or.inr ⟨st, by simpa using hst, hboth.1⟩) j a ha
            obtain ⟨st2, h2, h3⟩ := hrest
            exact ⟨st2, by rw [show c + (j + 1) = c + 1 + j by omega]; exact h2, h3⟩
  exact main ps c0 (t.init N) hdrv (Or.inl hstart) |> fun f j a ha => by simpa using f j a ha

/-- **A design satisfies the statement (task with a reset port) as soon as, besides the interface,
the clock discipline and termination, it has** an invariant `Inv` on snapshots (true initially,
kept by every successful cycle), a relation `R` between a snapshot and the spec state, a RESET
cycle lemma (any successful cycle whose entry asserts reset yields `R` with `init` and the spec's
observation, from ANY invariant state: reset forgets history, x included) and a STEP cycle lemma
(any successful cycle whose entry does not assert reset, from a snapshot related to `s`, yields
`R` with `step s v` and the observation). The cycle lemmas are about `cycleStep2` at any fuel.
The claim itself, from any start state of the invariant, is `SeqTask.claim_of_cycle`. -/
theorem SeqTask.satisfiedAt_of_cycle (t : SeqTask) (N : Nat) (d : Design2)
    (hrst : ∃ r, t.rst = some r)
    (hI : t.Interface N d) (hD : t.Disciplined d) (hT : Terminates2 d)
    (Inv : SvState → Prop) (R : SvState → t.State N → Prop)
    (hinit : Inv (initState2 d))
    (hinv : ∀ σ F inputs prev k st k', Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → Inv st)
    (hreset : ∀ σ F inputs prev k st k' (v : t.Ins N), Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (true, v) →
        R st (t.init N) ∧ t.ObsOK N st (t.init N, v))
    (hstep : ∀ σ F inputs prev k st k' (s : t.State N) (v : t.Ins N), Inv prev → R prev s →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (false, v) →
        R st (t.step N s v) ∧ t.ObsOK N st (t.step N s v, v)) :
    t.SatisfiedAt N d :=
  ⟨hI, ⟨hD, hT⟩, fun _ _ _ hr => t.claim_of_cycle N d hrst Inv R hinv hreset hstep hinit (Runs2.runFrom hr)⟩

/-- A signal holds at most one known bit. -/
theorem BitIs.unique {st : SvState} {n : String} {a b : Bool} (ha : BitIs st n a)
    (hb : BitIs st n b) : a = b := by
  unfold BitIs at ha hb
  rw [ha, Option.some.injEq] at hb
  cases a <;> cases b <;> first | rfl | exact absurd hb (by decide)

/-- A stimulus entry drives a signal with at most one known bit. -/
theorem StimBit.unique {stim : List SvState} {c : Nat} {n : String} {a b : Bool}
    (ha : StimBit stim c n a) (hb : StimBit stim c n b) : a = b := by
  obtain ⟨e, he, ha⟩ := ha
  obtain ⟨e', he', hb⟩ := hb
  rw [he, Option.some.injEq] at he'
  subst he'; exact BitIs.unique ha hb

/-- A stimulus entry binding `n` to the bit `b` applies it (`appIn`, the inputs of a cycle). -/
theorem BitIs.appIn_eq {e : SvState} {n : String} {b : Bool} (h : BitIs e n b) (old : LVec) :
    LeanModels.Sv.appIn e n old = knownBit b := by
  simp only [LeanModels.Sv.appIn, show SvState.lookup e n = _ from h, Option.getD_some]

/-! ## The transaction-protocol reduction (`TxTask`) -/

namespace TxTask

variable {P : Type} (t : TxTask P)

/-- **A phase model of `d` for `t` at `p` and latency `lat`**: the clock step, three phases of the
snapshots and one obligation per kind of cycle, each about ONE `Step` (no trace, horizon or fuel):
* `Ready st`: idle with nothing to show (after a reset, before the first start); `done` = 0.
* `Busy x m st`: working on the operands `x`, `done` = 0; `done` shows within `m + 1` more cycles
  (the measure drops by at least one per busy cycle).
* `Fin x st`: finished with `x`: `done` = 1 and the payload is `result x`.

The cycles: a reset entry yields `Ready` from any state of the shape (C1); a start from an idle
state (`Ready` or `Fin`, so back-to-back starts are covered, C2) yields `Fin x` (latency 0,
interpretation point 4) or `Busy x m` with `m < lat`; a busy cycle (the operands held) yields
`Fin x` or a smaller measure; an idle cycle without start keeps `Ready` and `Fin x` (the hold, C4).
A start while busy is excluded by the rely, so no obligation covers it. -/
structure PhaseModel (p : P) (lat : Nat) (d : Design2) extends CycleModel d where
  /-- The idle phase with nothing to show: after a reset, before the first start. -/
  Ready : SvState → Prop
  /-- `Busy x m st`: working on the operands `x`, `done` showing within `m + 1` more cycles (`m` the measure). -/
  Busy : t.Ops p → Nat → SvState → Prop
  /-- `Fin x st`: finished with the operands `x`. -/
  Fin : t.Ops p → SvState → Prop
  /-- In `Ready`, `done` is `0` (nothing is claimed before the first start). -/
  ready_done : ∀ st, Ready st → BitIs st t.done false
  /-- In `Busy`, `done` is `0`. -/
  busy_done : ∀ x m st, Busy x m st → BitIs st t.done false
  /-- In `Fin x`, `done` is `1` and the payload ports hold `result x`. -/
  fin_done : ∀ x st, Fin x st → BitIs st t.done true ∧ HoldAll st (t.payload p) (t.result p x)
  /-- A cycle whose stimulus entry asserts reset yields `Ready`, from any state of the shape (C1). -/
  reset : ∀ e prev st, Shape prev → Step e prev st → BitIs e t.rst true → Ready st
  /-- A start (reset low, `start` high, the operands `x` applied) from `Ready` or a `Fin y` yields `Fin x`
  (latency 0) or `Busy x m` with `m < lat`. -/
  start : ∀ e prev st x, Shape prev → Step e prev st → (Ready prev ∨ ∃ y, Fin y prev) →
    BitIs e t.rst false → BitIs e t.start true → HoldAll e (t.operands p) x →
    Fin x st ∨ ∃ m, m < lat ∧ Busy x m st
  /-- A busy cycle (reset and `start` low, the operands `x` still applied) from `Busy x m` yields `Fin x` or
  `Busy x m'` with a smaller measure `m' < m`. -/
  busy : ∀ e prev st x m, Shape prev → Step e prev st → Busy x m prev → BitIs e t.rst false →
    BitIs e t.start false → HoldAll e (t.operands p) x → Fin x st ∨ ∃ m', m' < m ∧ Busy x m' st
  /-- A cycle with reset and `start` low keeps `Ready`. -/
  hold_ready : ∀ e prev st, Shape prev → Step e prev st → Ready prev → BitIs e t.rst false →
    BitIs e t.start false → Ready st
  /-- A cycle with reset and `start` low keeps `Fin x` (the hold, C4). -/
  hold_fin : ∀ e prev st x, Shape prev → Step e prev st → Fin x prev → BitIs e t.rst false →
    BitIs e t.start false → Fin x st

/-- Proof-internal: no `start` at the entries `(a, b]`. -/
private abbrev NoStart (stim : List SvState) (a b : Nat) : Prop :=
  ∀ s, a < s → s ≤ b → ¬ StimBit stim s t.start true

/-- Proof-internal: the transaction started at `s0`, seen in the snapshot `st` of cycle `c`. -/
private abbrev Ph {p : P} {lat : Nat} {d : Design2} (M : t.PhaseModel p lat d)
    (stim tr : List SvState) (s0 c : Nat) (st : SvState) : Prop :=
  ∀ x, t.OpsAt p stim s0 x → M.Fin x st ∨
    ∃ m, c + m < s0 + lat ∧ M.Busy x m st ∧ ∀ c', s0 ≤ c' → c' ≤ c → ¬ TraceBit tr c' t.done true

/-- Proof-internal: the trace invariant at cycle `c`, from the reset snapshot `c0`. -/
private abbrev Inv {p : P} {lat : Nat} {d : Design2} (M : t.PhaseModel p lat d)
    (stim tr : List SvState) (c0 c : Nat) : Prop :=
  ∃ st, tr[c]? = some st ∧ ((M.Ready st ∧ t.NoStart stim c0 c) ∨
    ∃ s0, c0 < s0 ∧ s0 ≤ c ∧ StimBit stim s0 t.start true ∧ t.NoStart stim s0 c ∧
      t.Ph M stim tr s0 c st)

/-- **The transaction-protocol claim from a phase model**, for one completed run from a start state
`st0` of the model's shape: from every release, at every horizon, the rely gives the guarantee.
The release, the horizon, `Idle`, the held operands and back-to-back starts are handled here. -/
theorem guar_of_phases {p : P} {lat : Nat} {d : Design2} (M : t.PhaseModel p lat d)
    {σ : ScheduleOracle} {st0 : SvState} {stim tr : List SvState} (h0 : M.Shape st0)
    (hr : RunFrom d σ st0 stim tr) :
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h := by
  intro c1 h hrel hR
  obtain ⟨hc1, ⟨e0, he0, hb0⟩, hoff⟩ := hrel
  obtain ⟨c0, rfl⟩ : ∃ c0, c1 = c0 + 1 := ⟨c1 - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at he0
  have hsnap : ∀ c, c0 ≤ c → c < h → ∃ st, tr[c]? = some st := by
    intro c h1 h2
    obtain ⟨e, he⟩ : ∃ e, stim[c]? = some e := by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · exact ⟨e0, he0⟩
      · obtain ⟨e, he, -⟩ := hoff c h1 h2; exact ⟨e, he⟩
    exact hr.exists_snapshot (List.getElem?_eq_some_iff.mp he).1
  have nd : ∀ {c : Nat} {st : SvState}, tr[c]? = some st → BitIs st t.done false →
      ¬ TraceBit tr c t.done true := by
    rintro c st hc hb ⟨st', hc', hb'⟩
    rw [hc, Option.some.injEq] at hc'; subst hc'; exact Bool.false_ne_true (BitIs.unique hb hb')
  have onE : ∀ {c : Nat} {e : SvState} {n : String} {b : Bool}, stim[c]? = some e →
      StimBit stim c n b → BitIs e n b := by
    rintro c e n b he ⟨e', he', hb⟩
    rw [he, Option.some.injEq] at he'; subst he'; exact hb
  have toE : ∀ {c : Nat} {e : SvState} {x : t.Ops p}, stim[c]? = some e → t.OpsAt p stim c x →
      HoldAll e (t.operands p) x := by
    rintro c e x he ⟨e', he', hx⟩
    rw [he, Option.some.injEq] at he'; subst he'; exact hx
  have G : ∀ n, c0 + n < h → t.Inv M stim tr c0 (c0 + n) := by
    intro n
    induction n with
    | zero =>
        intro hh
        obtain ⟨st, hst⟩ := hsnap c0 (Nat.le_refl _) hh
        obtain ⟨e, prev, he, -, hsh, hs⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
        rw [he0, Option.some.injEq] at he; subst he
        exact ⟨st, hst, .inl ⟨M.reset _ prev st hsh hs hb0, fun s h1 h2 => absurd h2 (by omega)⟩⟩
    | succ n ih =>
        show c0 + n + 1 < h → t.Inv M stim tr c0 (c0 + n + 1)
        intro hh
        obtain ⟨prev, hprev, hG⟩ := ih (by omega)
        have hle : c0 ≤ c0 + n := Nat.le_add_right _ _
        generalize c0 + n = c at hprev hG hh hle
        obtain ⟨st, hst⟩ := hsnap (c + 1) (by omega) hh
        obtain ⟨e, prev', he, hp, hsh, hs⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
        rw [List.getElem?_cons_succ, hprev, Option.some.injEq] at hp; subst hp
        have hr0 : BitIs e t.rst false := onE he (hoff (c + 1) (by omega) hh)
        obtain ⟨⟨b, hb⟩, -, hidle, hheld⟩ := hR (c + 1) (by omega) hh
        cases b with
        | true =>
            have hidl : M.Ready prev ∨ ∃ y, M.Fin y prev := by
              rcases hG with ⟨hrd, -⟩ | ⟨s0, h1, h2, hs0, -, hph⟩
              · exact .inl hrd
              · obtain ⟨-, ⟨x, hx⟩, -⟩ := hR s0 (by omega) (by omega)
                rcases hph x hx with hf | ⟨m, -, -, hnd⟩
                · exact .inr ⟨x, hf⟩
                · obtain ⟨c', h3, h4, hd⟩ := hidle hb s0 (by omega) (by omega) hs0
                  exact absurd hd (hnd c' h3 (by omega))
            refine ⟨st, hst, .inr ⟨c + 1, by omega, Nat.le_refl _, hb,
              fun s h1 h2 => absurd h2 (by omega), fun x hx => ?_⟩⟩
            rcases M.start e prev st x hsh hs hidl hr0 (onE he hb) (toE he hx) with hf | ⟨m, hm, hbz⟩
            · exact .inl hf
            · refine .inr ⟨m, by omega, hbz, fun c' h1 h2 => ?_⟩
              obtain rfl : c' = c + 1 := by omega
              exact nd hst (M.busy_done x m st hbz)
        | false =>
            have hns : ∀ a, t.NoStart stim a c → t.NoStart stim a (c + 1) := by
              intro a hn s h1 h2 hs'
              rcases Nat.lt_or_ge c s with h3 | h3
              · obtain rfl : s = c + 1 := by omega
                exact Bool.false_ne_true (StimBit.unique hb hs')
              · exact hn s h1 h3 hs'
            refine ⟨st, hst, ?_⟩
            rcases hG with ⟨hrd, hn⟩ | ⟨s0, h1, h2, hs0, hn, hph⟩
            · exact .inl ⟨M.hold_ready e prev st hsh hs hrd hr0 (onE he hb), hns c0 hn⟩
            · refine .inr ⟨s0, h1, by omega, hs0, hns s0 hn, fun x hx => ?_⟩
              rcases hph x hx with hf | ⟨m, hm, hbz, hnd⟩
              · exact .inl (M.hold_fin e prev st x hsh hs hf hr0 (onE he hb))
              · have hx' := hheld s0 x (by omega) (by omega) hs0 hx
                  (fun c' h3 h4 => hnd c' h3 (by omega))
                rcases M.busy e prev st x m hsh hs hbz hr0 (onE he hb) (toE he hx') with
                  hf | ⟨m', hm', hbz'⟩
                · exact .inl hf
                · refine .inr ⟨m', by omega, hbz', fun c' h3 h4 => ?_⟩
                  rcases Nat.lt_or_ge c c' with h5 | h5
                  · obtain rfl : c' = c + 1 := by omega
                    exact nd hst (M.busy_done x m' st hbz')
                  · exact hnd c' h3 h5
  have hInv : ∀ c, c0 ≤ c → c < h → t.Inv M stim tr c0 c := fun c h1 h2 => by
    obtain ⟨n, rfl⟩ : ∃ n, c = c0 + n := ⟨c - c0, by omega⟩
    exact G n h2
  -- a start `s`, seen at every later cycle before the next start
  have key : ∀ s, c0 < s → StimBit stim s t.start true → ∀ c, s ≤ c → c < h →
      t.NoStart stim s c → ∃ st, tr[c]? = some st ∧ t.Ph M stim tr s c st := by
    intro s hs hst c h1 h2 hn
    obtain ⟨st, hc, hG⟩ := hInv c (by omega) h2
    refine ⟨st, hc, ?_⟩
    rcases hG with ⟨-, hn0⟩ | ⟨s0, h3, h4, hs0, hn0, hph⟩
    · exact absurd hst (hn0 s hs h1)
    · obtain rfl : s0 = s := by
        rcases Nat.lt_trichotomy s0 s with h5 | h5 | h5
        · exact absurd hst (hn0 s h5 h1)
        · exact h5
        · exact absurd hs0 (hn s0 h5 h4)
      exact hph
  refine ⟨fun c h1 h2 => ?_, fun c h1 h2 hn => ?_, fun s x h1 h2 hs hx => ⟨fun hl => ?_, fun c h3 h4 hd hn => ?_⟩⟩
  · -- `done` is known from the release on
    obtain ⟨st, hc, hG⟩ := hInv c (by omega) h2
    rcases hG with ⟨hrd, -⟩ | ⟨s0, h3, h4, -, -, hph⟩
    · exact ⟨false, st, hc, M.ready_done st hrd⟩
    · obtain ⟨-, ⟨x, hx⟩, -⟩ := hR s0 (by omega) (by omega)
      rcases hph x hx with hf | ⟨m, -, hbz, -⟩
      · exact ⟨true, st, hc, (M.fin_done x st hf).1⟩
      · exact ⟨false, st, hc, M.busy_done x m st hbz⟩
  · -- `done` = 0 before the first start
    obtain ⟨st, hc, hG⟩ := hInv c (by omega) h2
    rcases hG with ⟨hrd, -⟩ | ⟨s0, h3, h4, hs0, -, -⟩
    · exact ⟨st, hc, M.ready_done st hrd⟩
    · exact absurd hs0 (hn s0 (by omega) h4)
  · -- `done` within the latency: at `s + lat`, or before a next start (which needs `Idle`)
    by_cases hn : t.NoStart stim s (s + lat)
    · obtain ⟨st, hc, hph⟩ := key s h1 hs (s + lat) (by omega) hl hn
      rcases hph x hx with hf | ⟨m, hm, -⟩
      · exact ⟨s + lat, by omega, Nat.le_refl _, st, hc, (M.fin_done x st hf).1⟩
      · omega
    · obtain ⟨s', h3, h4, hs'⟩ : ∃ s', s < s' ∧ s' ≤ s + lat ∧ StimBit stim s' t.start true :=
        Classical.byContradiction fun hne => hn fun s' h3 h4 hs' => hne ⟨s', h3, h4, hs'⟩
      obtain ⟨-, -, hidle, -⟩ := hR s' (by omega) (by omega)
      obtain ⟨c', h5, h6, hd⟩ := hidle hs' s h1 h3 hs
      exact ⟨c', h5, by omega, hd⟩
  · -- the hold: `done` and `result x` until the next start
    obtain ⟨c', h5, h6, hd⟩ := hd
    obtain ⟨st, hc, hph⟩ := key s h1 hs c h3 h4 hn
    rcases hph x hx with hf | ⟨m, -, -, hnd⟩
    · exact ⟨st, hc, M.fin_done x st hf⟩
    · exact absurd hd (hnd c' h5 h6)

/-- **The transaction-protocol reduction**: a design satisfies the `TxTask` statement at `p` and
`lat ≥ 1` as soon as, besides the interface, the clock discipline and termination, it has a phase
model (`PhaseModel`: the clock step and the one-cycle reset, start, busy and hold obligations).
The claim on each run is `guar_of_phases`. -/
theorem satisfiedAt_of_phases {p : P} {lat : Nat} {d : Design2} (hI : t.Interface p d)
    (hD : t.Disciplined d) (hT : Terminates2 d) (hlat : 1 ≤ lat) (M : t.PhaseModel p lat d) :
    t.SatisfiedAt p lat d :=
  ⟨hI, ⟨hD, hT⟩, hlat, fun _ _ _ hr => t.guar_of_phases M M.init (Runs2.runFrom hr)⟩

end TxTask

/-! ## The stream-protocol reduction (`StreamTask`) -/

namespace StreamTask

variable {P : Type} (t : StreamTask P)

/-- The values `ys` are the first inputs after the start `s`: entry `s + 1 + j` carries `ys[j]`. -/
def InputsAt (p : P) (stim : List SvState) (s : Nat) (ys : List (BitVec (t.width p))) : Prop :=
  ∀ j v, ys[j]? = some v → ∃ e, stim[s + 1 + j]? = some e ∧ t.DataIs p e t.inData v

/-- **A phase model of `d` for `t` at `p` and latency `lat`**, each obligation about ONE `Step`:
`Ready` (idle, `out_valid` = 0) and `At ys j` (`j` cycles after a start, its first `min j count`
inputs `ys` received, showing `out ys j`: nothing before the last input is sampled or after `lat`,
`spec xs` up to `lat`). A start comes from `Ready` or from an `At` with nothing left to show. -/
structure PhaseModel (p : P) (lat : Nat) (d : Design2) extends CycleModel d where
  /-- The idle phase: after a reset, before the first start. -/
  Ready : SvState → Prop
  /-- `At ys j st`: `j` cycles after a start, the first `min j count` inputs `ys` received. -/
  At : List (BitVec (t.width p)) → Nat → SvState → Prop
  /-- The output schedule: `out xs j` (valid bit, data) is what the design shows `j` cycles after a start whose
  inputs are `xs`. -/
  out : List (BitVec (t.width p)) → Nat → t.Obs p
  /-- Nothing is valid before the last input is sampled (`j < count`). -/
  out_feed : ∀ xs j, j < t.count p → (out xs j).1 = false
  /-- Nothing is valid after the latency (`j > lat`), for a full input list. -/
  out_lat : ∀ xs j, xs.length = t.count p → lat < j → (out xs j).1 = false
  /-- The valid outputs of cycles `0 … lat`, in order, are `spec xs`, for a full input list. -/
  out_spec : ∀ xs, xs.length = t.count p → t.emitted p ((List.range (lat + 1)).map (out xs)) = t.spec p xs
  /-- In `Ready`, `out_valid` is `0`. -/
  ready_out : ∀ st, Ready st → BitIs st t.outValid false
  /-- In `At ys j`, `out_valid` is the schedule's valid bit `(out ys j).1`, and when it is `1` the data port
  holds `(out ys j).2`. -/
  at_out : ∀ ys j st, At ys j st → BitIs st t.outValid (out ys j).1 ∧
    ((out ys j).1 = true → t.DataIs p st t.outData (out ys j).2)
  /-- A cycle whose stimulus entry asserts reset yields `Ready`, from any state of the shape. -/
  reset : ∀ e prev st, Shape prev → Step e prev st → BitIs e t.rst true → Ready st
  /-- A cycle with reset, `start` and `in_valid` low keeps `Ready`. -/
  hold : ∀ e prev st, Shape prev → Step e prev st → Ready prev → BitIs e t.rst false →
    BitIs e t.start false → BitIs e t.inValid false → Ready st
  /-- A start (reset low, `start` high, `in_valid` low) from `Ready`, or from an `At xs j` with a full input list
  and nothing valid after cycle `j`, yields `At [] 0`. -/
  start : ∀ e prev st, Shape prev → Step e prev st →
    (Ready prev ∨ ∃ xs j, xs.length = t.count p ∧ At xs j prev ∧ ∀ k, j < k → (out xs k).1 = false) →
    BitIs e t.rst false → BitIs e t.start true → BitIs e t.inValid false → At [] 0 st
  /-- An input cycle (reset and `start` low, `in_valid` high, the data `x`) from `At ys j` with `j = ys.length`
  inputs received, `j < count`, yields `At (ys ++ [x]) (j + 1)`. -/
  feed : ∀ e prev st ys j x, Shape prev → Step e prev st → At ys j prev → ys.length = j → j < t.count p →
    BitIs e t.rst false → BitIs e t.start false → BitIs e t.inValid true → t.DataIs p e t.inData x →
    At (ys ++ [x]) (j + 1) st
  /-- A cycle after the last input (reset, `start` and `in_valid` low) from `At xs j` with all `count` inputs
  received, `count ≤ j`, yields `At xs (j + 1)`. -/
  run : ∀ e prev st xs j, Shape prev → Step e prev st → At xs j prev → xs.length = t.count p →
    t.count p ≤ j → BitIs e t.rst false → BitIs e t.start false → BitIs e t.inValid false →
    At xs (j + 1) st

variable {p : P}

/-- A signal holds at most one value of the data width. -/
theorem dataIs_unique {st : SvState} {n : String} {a b : BitVec (t.width p)} (ha : t.DataIs p st n a)
    (hb : t.DataIs p st n b) : a = b := by
  unfold DataIs at ha hb; rw [ha, Option.some.injEq] at hb; exact LVec.ofBitVec_inj.mp hb

/-- Two lists of the same length both received after the start `s` are equal. -/
theorem inputs_unique {stim : List SvState} {s : Nat} {xs ys : List (BitVec (t.width p))}
    (hx : t.InputsAt p stim s xs) (hy : t.InputsAt p stim s ys) (hl : xs.length = ys.length) : xs = ys :=
  List.ext_getElem hl fun j h1 h2 => by
    obtain ⟨e, he, ha⟩ := hx j _ (List.getElem?_eq_getElem h1)
    obtain ⟨e', he', hb⟩ := hy j _ (List.getElem?_eq_getElem h2)
    rw [he, Option.some.injEq] at he'; subst he'; exact t.dataIs_unique ha hb

/-- The inputs after `s` extend by the value at the next entry. -/
theorem inputs_snoc {stim : List SvState} {s : Nat} {ys : List (BitVec (t.width p))} {v : BitVec (t.width p)}
    (hy : t.InputsAt p stim s ys) (hv : ∃ e, stim[s + 1 + ys.length]? = some e ∧ t.DataIs p e t.inData v) :
    t.InputsAt p stim s (ys ++ [v]) := by
  intro j w hj
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_or_ge j ys.length with h | h
  · rw [List.getElem_append_left h]; exact hy j _ (List.getElem?_eq_getElem h)
  · obtain rfl : j = ys.length := (by simp at hlt; omega); simpa using hv

/-- Observations that are all not valid emit nothing. -/
theorem emitted_nil {f : Nat → t.Obs p} {n : Nat} (h : ∀ k, k < n → (f k).1 = false) :
    t.emitted p ((List.range n).map f) = [] := by
  simp only [emitted, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map, List.mem_range]
  rintro _ ⟨k, hk, rfl⟩; simp [h k hk]

/-- What `a + b` observations emit: the first `a`'s, then the next `b`'s. -/
theorem emitted_add (f : Nat → t.Obs p) (a b : Nat) : t.emitted p ((List.range (a + b)).map f) =
    t.emitted p ((List.range a).map f) ++ t.emitted p ((List.range b).map fun i => f (a + i)) := by
  simp [emitted, List.range_add, List.filter_append, List.map_map, Function.comp_def]

/-- Observations not valid from `n` on emit, up to any `m ≥ n`, what the first `n` emit. -/
theorem emitted_stable {f : Nat → t.Obs p} {n m : Nat} (h : ∀ j, n ≤ j → (f j).1 = false) (hm : n ≤ m) :
    t.emitted p ((List.range m).map f) = t.emitted p ((List.range n).map f) := by
  obtain ⟨b, rfl⟩ : ∃ b, m = n + b := ⟨m - n, by omega⟩
  rw [t.emitted_add, t.emitted_nil (f := fun i => f (n + i)) (n := b) fun k _ => h _ (by omega), List.append_nil]

/-- Observations that agree with `f` on validity, and on the data where valid, emit what `f` does. -/
theorem emitted_match : ∀ (obs : List (t.Obs p)) (f : Nat → t.Obs p),
    (∀ k o, obs[k]? = some o → o.1 = (f k).1 ∧ (o.1 = true → o.2 = (f k).2)) →
    t.emitted p obs = t.emitted p ((List.range obs.length).map f)
  | [], _, _ => rfl
  | o :: obs, f, h => by
    have ih := emitted_match obs (fun k => f (k + 1)) fun k o' hk => h (k + 1) o' (by simpa using hk)
    obtain ⟨h1, h2⟩ := h 0 o rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [emitted, List.filter_cons, ← h1] at ih ⊢
    cases ho : o.1
    · simpa [Function.comp_def] using ih
    · simp only [if_true, List.map_cons, h2 ho, ih, Function.comp_def]

/-- The snapshots `s, …, s + n` show `f 0, …, f n`. -/
abbrev Hist (tr : List SvState) (s n : Nat) (f : Nat → t.Obs p) : Prop :=
  ∀ k, k ≤ n → ∃ st, tr[s + k]? = some st ∧ BitIs st t.outValid (f k).1 ∧
    ((f k).1 = true → t.DataIs p st t.outData (f k).2)

/-- A history extends by the next snapshot's observation. -/
theorem hist_snoc {tr : List SvState} {s n : Nat} {f : Nat → t.Obs p} {st : SvState}
    (hh : t.Hist tr s n f) (hst : tr[s + (n + 1)]? = some st) (hb : BitIs st t.outValid (f (n + 1)).1 ∧
      ((f (n + 1)).1 = true → t.DataIs p st t.outData (f (n + 1)).2)) : t.Hist tr s (n + 1) f := by
  intro k hk
  exact (Nat.lt_or_ge k (n + 1)).elim (fun h => hh k (by omega)) fun h => by
    obtain rfl : k = n + 1 := (by omega); exact ⟨st, hst, hb⟩

/-- What a trace shows from `s`, within the history, is emitted as `f` emits. -/
theorem shows_hist {tr : List SvState} {s n : Nat} {f : Nat → t.Obs p} {obs : List (t.Obs p)}
    (hh : t.Hist tr s n f) (hs : t.Shows p tr s obs) (hl : obs.length ≤ n + 1) :
    t.emitted p obs = t.emitted p ((List.range obs.length).map f) := by
  refine t.emitted_match obs f fun k o hk => ?_
  obtain ⟨st, h1, h2, h3⟩ := hs k o hk
  obtain ⟨st', h1', h2', h3'⟩ := hh k (by have := (List.getElem?_eq_some_iff.mp hk).1; omega)
  rw [h1, Option.some.injEq] at h1'; subst h1'
  have e1 := BitIs.unique h2 h2'
  exact ⟨e1, fun ho => t.dataIs_unique (h3 ho) (h3' (e1 ▸ ho))⟩

section

variable {lat : Nat} {d : Design2} (M : t.PhaseModel p lat d)
  (hlen : ∀ xs, xs.length = t.count p → (t.spec p xs).length = t.count p)

private abbrev NoStart (stim : List SvState) (a b : Nat) : Prop :=
  ∀ s, a < s → s ≤ b → ¬ StimBit stim s t.start true

-- the transaction started at `s`, seen in the snapshot `st` of cycle `c`
private abbrev Ph (stim tr : List SvState) (s c : Nat) (st : SvState) : Prop :=
  ∃ ys, ys.length = min (c - s) (t.count p) ∧ t.InputsAt p stim s ys ∧ M.At ys (c - s) st ∧
    t.Hist tr s (c - s) (M.out ys)

-- the trace invariant at cycle `c`, from the reset snapshot `c0`
private abbrev Inv (stim tr : List SvState) (c0 c : Nat) : Prop :=
  ∃ st, tr[c]? = some st ∧ ((M.Ready st ∧ t.NoStart stim c0 c) ∨
    ∃ s, c0 < s ∧ s ≤ c ∧ StimBit stim s t.start true ∧ t.NoStart stim s c ∧
      (∀ s0, c0 < s0 → s0 < s → StimBit stim s0 t.start true → s0 + t.count p < s) ∧ t.Ph M stim tr s c st)

include hlen
/-- Once `count` values are shown, nothing is left to show. -/
theorem PhaseModel.out_eq_false_of_emitted {xs : List (BitVec (t.width p))} (hx : xs.length = t.count p) {n : Nat}
    (hn : t.count p ≤ (t.emitted p ((List.range n).map (M.out xs))).length) :
    ∀ j, n ≤ j → (M.out xs j).1 = false := by
  have hV := (t.emitted_add (M.out xs) n (lat + 1)).symm.trans ((t.emitted_stable (fun j hj =>
    M.out_lat xs j hx (by omega)) (Nat.le_add_left (lat + 1) n)).trans (M.out_spec xs hx))
  have hW := congrArg List.length hV; rw [List.length_append, hlen xs hx] at hW
  intro j hj
  rcases Nat.lt_or_ge (j - n) (lat + 1) with h | h
  · have h0 := List.eq_nil_of_length_eq_zero (show (t.emitted p ((List.range (lat + 1)).map
      fun i => M.out xs (n + i))).length = 0 by omega)
    simp only [emitted, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map, List.mem_range] at h0
    simpa [show n + (j - n) = j by omega] using h0 _ ⟨j - n, h, rfl⟩
  · exact M.out_lat xs j hx (by omega)

/-- At a start after `s`, `Idle` says the transaction `s` has shown everything. -/
private theorem idle_done (hcount : 1 ≤ t.count p) {stim tr : List SvState} {s c : Nat} {st : SvState}
    (hsc : s ≤ c) (hob : ∃ obs : List (t.Obs p), s + obs.length ≤ c + 1 ∧ t.Shows p tr s obs ∧
      (t.emitted p obs).length = t.count p) (hph : t.Ph M stim tr s c st) :
    ∃ xs, xs.length = t.count p ∧ t.InputsAt p stim s xs ∧ t.count p ≤ c - s ∧ M.At xs (c - s) st ∧
      t.Hist tr s (c - s) (M.out xs) ∧ ∀ j, c - s < j → (M.out xs j).1 = false := by
  obtain ⟨⟨obs, hl, hsh, hc⟩, ⟨ys, hy, hin, hat, hh⟩⟩ := And.intro hob hph
  rw [t.shows_hist hh hsh (by omega)] at hc
  by_cases hlt : c - s < t.count p
  · rw [t.emitted_nil (n := obs.length) fun k hk => M.out_feed ys k (by omega)] at hc; simp at hc; omega
  · have hx : ys.length = t.count p := by omega
    exact ⟨ys, hx, hin, by omega, hat, hh, fun j hj =>
      PhaseModel.out_eq_false_of_emitted t M hlen hx (n := obs.length) (by omega) j (by omega)⟩

end

/-- **The stream-protocol claim from a phase model** (`1 ≤ count p ≤ lat`, `spec` keeping the length), for one
completed run from a start state `st0` of the model's shape. The release, the horizon, `Idle`, `in_valid`,
back-to-back starts and C8's points 6 and 7 are handled here. -/
theorem guar_of_phases {lat : Nat} {d : Design2} (hcount : 1 ≤ t.count p) (hle : t.count p ≤ lat)
    (hlen : ∀ xs, xs.length = t.count p → (t.spec p xs).length = t.count p)
    (M : t.PhaseModel p lat d) {σ : ScheduleOracle} {st0 : SvState} {stim tr : List SvState}
    (h0 : M.Shape st0) (hr : RunFrom d σ st0 stim tr) :
    ∀ c1 h, Released t.rst stim c1 h → t.Rely p stim tr c1 h → t.Guar p lat stim tr c1 h := by
  intro c1 h hrel hR
  obtain ⟨hc1, ⟨e0, he0, hb0⟩, hoff⟩ := hrel
  obtain ⟨c0, rfl⟩ : ∃ c0, c1 = c0 + 1 := ⟨c1 - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at he0
  have hsnap : ∀ c, c0 ≤ c → c < h → ∃ st, tr[c]? = some st := fun c h1 h2 => by
    obtain ⟨e, he⟩ : ∃ e, stim[c]? = some e := by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1 <;>
        first | exact ⟨e0, he0⟩ | exact (hoff c h1 h2).imp fun _ h => h.1
    exact hr.exists_snapshot (List.getElem?_eq_some_iff.mp he).1
  have onE : ∀ {c e n b}, stim[c]? = some e → StimBit stim c n b → BitIs e n b := by
    rintro c e n b he ⟨e', he', hb⟩; rw [he, Option.some.injEq] at he'; subst he'; exact hb
  have closed : ∀ c st, (M.Ready st ∧ t.NoStart stim c0 c) ∨ (∃ s, c0 < s ∧ s ≤ c ∧ t.NoStart stim s c ∧
      (∀ s0, c0 < s0 → s0 < s → StimBit stim s0 t.start true → s0 + t.count p < s) ∧ t.count p ≤ c - s) →
      ∀ s0, c0 < s0 → s0 ≤ c → StimBit stim s0 t.start true → s0 + t.count p ≤ c := by
    rintro c st (⟨-, hn⟩ | ⟨s, h1, h2, hn, hw, hge⟩) s0 h3 h4 hs0
    · exact absurd hs0 (hn s0 h3 h4)
    · rcases Nat.lt_trichotomy s0 s with h5 | rfl | h5
      · have := hw s0 h3 h5 hs0; omega
      · omega
      · exact absurd hs0 (hn s0 h5 h4)
  have G : ∀ n, c0 + n < h → t.Inv M stim tr c0 (c0 + n) := by
    intro n
    induction n with
    | zero =>
        intro hh
        obtain ⟨st, hst⟩ := hsnap c0 (Nat.le_refl _) hh
        obtain ⟨e, prev, he, -, hsh, hs⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
        rw [he0, Option.some.injEq] at he; subst he
        exact ⟨st, hst, .inl ⟨M.reset _ prev st hsh hs hb0, fun s h1 h2 => absurd h2 (by omega)⟩⟩
    | succ n ih =>
        show c0 + n + 1 < h → t.Inv M stim tr c0 (c0 + n + 1)
        intro hh
        obtain ⟨prev, hprev, hG⟩ := ih (by omega)
        have hle : c0 ≤ c0 + n := Nat.le_add_right _ _
        generalize c0 + n = c at hprev hG hh hle
        obtain ⟨st, hst⟩ := hsnap (c + 1) (by omega) hh
        obtain ⟨e, prev', he, hp, hsh, hstp⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
        rw [List.getElem?_cons_succ, hprev, Option.some.injEq] at hp; subst hp
        have hr0 : BitIs e t.rst false := onE he (hoff (c + 1) (by omega) hh)
        obtain ⟨⟨b, hb⟩, ⟨e', v, he', hv⟩, hidle, hon, hoff'⟩ := hR (c + 1) (by omega) hh
        rw [he, Option.some.injEq] at he'; subst he'
        cases b with
        | true =>
            obtain ⟨hidl, hcl⟩ : (M.Ready prev ∨ ∃ xs j, xs.length = t.count p ∧ M.At xs j prev ∧
                ∀ k, j < k → (M.out xs k).1 = false) ∧ ∀ s0, c0 < s0 → s0 ≤ c → StimBit stim s0 t.start true →
                s0 + t.count p ≤ c := by
              rcases hG with hrd | ⟨s, h1, h2, hs0, hn, hw, hph⟩
              · exact ⟨.inl hrd.1, closed c prev (.inl hrd)⟩
              · obtain ⟨xs, hx, -, hge, hat, -, hnp⟩ :=
                  t.idle_done M hlen hcount h2 (hidle hb s (by omega) (by omega) hs0) hph
                exact ⟨.inr ⟨xs, _, hx, hat, hnp⟩, closed c prev (.inr ⟨s, h1, h2, hn, hw, hge⟩)⟩
            have hiv := onE he (hoff' fun s0 h1 h2 h3 hs0 => by have := hcl s0 (by omega) (by omega) hs0; omega)
            have hat := M.start e prev st hsh hstp hidl hr0 (onE he hb) hiv
            refine ⟨st, hst, .inr ⟨c + 1, by omega, Nat.le_refl _, hb, fun s h1 h2 => absurd h2 (by omega),
              fun s0 h1 h2 hs0 => by have := hcl s0 h1 (by omega) hs0; omega, [], by simp,
              fun j v h => by simp at h, by simpa using hat, fun k hk => ?_⟩⟩
            obtain rfl : k = 0 := by omega
            exact ⟨st, by simpa using hst, M.at_out [] 0 st hat⟩
        | false =>
            have hns : ∀ a, t.NoStart stim a c → t.NoStart stim a (c + 1) := by
              intro a hn s h1 h2 hs'
              rcases Nat.lt_or_ge c s with h3 | h3
              · obtain rfl : s = c + 1 := by omega
                exact Bool.false_ne_true (StimBit.unique hb hs')
              · exact hn s h1 h3 hs'
            have hs0 : BitIs e t.start false := onE he hb
            rcases hG with ⟨hrd, hn⟩ | ⟨s, h1, h2, hs, hn, hw, ys, hy, hin, hat, hh⟩
            · have hiv := onE he (hoff' fun s0 h3 h4 _ hs0' => hn s0 (by omega) (by omega) hs0')
              exact ⟨st, hst, .inl ⟨M.hold e prev st hsh hstp hrd hr0 hs0 hiv, hns c0 hn⟩⟩
            have hidx : tr[s + (c - s + 1)]? = some st := by rw [show s + (c - s + 1) = c + 1 by omega]; exact hst
            refine ⟨st, hst, .inr ⟨s, h1, by omega, hs, hns s hn, hw, ?_⟩⟩
            simp only [Ph]
            rw [show c + 1 - s = c - s + 1 by omega]
            rcases Nat.lt_or_ge (c - s) (t.count p) with hlt | hge
            · have hiv := onE he (hon s (by omega) (by omega) (by omega) hs)
              have hat' := M.feed e prev st ys (c - s) v hsh hstp hat (by omega) hlt hr0 hs0 hiv hv
              refine ⟨ys ++ [v], by rw [List.length_append, List.length_singleton]; omega, t.inputs_snoc hin
                ⟨e, by rw [show s + 1 + ys.length = c + 1 by omega]; exact he, hv⟩, hat',
                t.hist_snoc (fun k hk => ?_) hidx (M.at_out _ _ st hat')⟩
              obtain ⟨st', h3, h4, -⟩ := hh k hk
              rw [M.out_feed ys k (by omega)] at h4
              exact ⟨st', h3, by rwa [M.out_feed _ k (by omega)], fun h5 => by
                rw [M.out_feed _ k (by omega)] at h5; cases h5⟩
            · have hcl := closed c prev (.inr ⟨s, h1, h2, hn, hw, hge⟩)
              have hiv := onE he (hoff' fun s0 h3 h4 h5 hs0' => by have := hcl s0 (by omega) (by omega) hs0'; omega)
              have hat' := M.run e prev st ys (c - s) hsh hstp hat (by omega) hge hr0 hs0 hiv
              exact ⟨ys, by omega, hin, hat', t.hist_snoc hh hidx (M.at_out _ _ st hat')⟩
  have hInv : ∀ c, c0 ≤ c → c < h → t.Inv M stim tr c0 c := fun c h1 h2 => by
    obtain ⟨n, rfl⟩ : ∃ n, c = c0 + n := ⟨c - c0, by omega⟩
    exact G n h2
  -- a start `s`, seen at every later cycle before the next start
  have key : ∀ s, c0 < s → StimBit stim s t.start true → ∀ c, s ≤ c → c < h →
      t.NoStart stim s c → ∃ st, tr[c]? = some st ∧ t.Ph M stim tr s c st := by
    intro s hs hst c h1 h2 hn
    obtain ⟨st, hc, ⟨-, hn0⟩ | ⟨s0, h3, h4, hs0, hn0, -, hph⟩⟩ := hInv c (by omega) h2
    · exact absurd hst (hn0 s hs h1)
    · rcases Nat.lt_trichotomy s0 s with h5 | rfl | h5 <;>
        first | exact ⟨st, hc, hph⟩ | exact absurd hst (hn0 s h5 h1) | exact absurd hs0 (hn s0 h5 h4)
  refine ⟨fun c h1 h2 => ?_, fun c h1 h2 hn => ?_, fun s xs h1 h2 hs hx hin e h3 h4 hne he => ?_⟩
  · -- `out_valid` is known from the release on
    obtain ⟨st, hc, ⟨hrd, -⟩ | ⟨s, -, -, -, -, -, ys, -, -, hat, -⟩⟩ := hInv c (by omega) h2
    · exact ⟨false, st, hc, M.ready_out st hrd⟩
    · exact ⟨_, st, hc, (M.at_out ys _ st hat).1⟩
  · -- `out_valid` = 0 before the first start
    obtain ⟨st, hc, ⟨hrd, -⟩ | ⟨s, h3, h4, hs, -⟩⟩ := hInv c (by omega) h2
    · exact ⟨st, hc, M.ready_out st hrd⟩
    · exact absurd hs (hn s (by omega) h4)
  · -- the transaction `s`: its inputs, what it shows before `e`, and nothing after (`Idle` or `lat`)
    obtain ⟨st, -, hph⟩ := key s (by omega) hs (e - 1) (by omega) (by omega) fun s' h5 h6 => hne s' h5 (by omega)
    obtain ⟨xs', hx', hin', hh, hnp⟩ : ∃ xs', xs'.length = t.count p ∧ t.InputsAt p stim s xs' ∧
        t.Hist tr s (e - 1 - s) (M.out xs') ∧ ∀ j, e - s ≤ j → (M.out xs' j).1 = false := by
      rcases Nat.lt_or_ge e h with he' | he'
      · obtain ⟨xs', hx', hin', -, -, hh, hnp⟩ := t.idle_done M hlen hcount (by omega) (by
          rw [show e - 1 + 1 = e by omega]; exact (hR e (by omega) he').2.2.1 (he he') s (by omega) (by omega) hs) hph
        exact ⟨xs', hx', hin', hh, fun j hj => hnp j (by omega)⟩
      · obtain ⟨ys, hy, hin', -, hh⟩ := hph
        exact ⟨ys, by omega, hin', hh, fun j hj => M.out_lat ys j (by omega) (by omega)⟩
    rw [t.inputs_unique hin' hin (by rw [hx, hx'])] at hh hnp
    refine ⟨(List.range (e - s)).map (M.out xs), by simp, fun k o hk => ?_,
      ((t.emitted_stable hnp (Nat.le_add_right _ (lat + 1))).symm.trans (t.emitted_stable (fun j hj =>
        M.out_lat xs j hx (by omega)) (Nat.le_add_left _ _))).trans (M.out_spec xs hx), fun k o hk hl => ?_⟩
    all_goals obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    all_goals (simp only [List.length_map, List.length_range] at hlt
               simp only [List.getElem_map, List.getElem_range])
    · exact hh k (by omega)
    · exact M.out_lat xs k hx hl

/-- **The stream-protocol reduction**: the `StreamTask` statement at `p` and `lat` (`1 ≤ count p ≤ lat`,
`spec` keeping the length) from the interface, the discipline, termination and a phase model. The claim
on each run is `guar_of_phases`. -/
theorem satisfiedAt_of_phases {lat : Nat} {d : Design2} (hI : t.Interface p d) (hD : t.Disciplined d)
    (hT : Terminates2 d) (hcount : 1 ≤ t.count p) (hle : t.count p ≤ lat)
    (hlen : ∀ xs, xs.length = t.count p → (t.spec p xs).length = t.count p)
    (M : t.PhaseModel p lat d) : t.SatisfiedAt p lat d :=
  ⟨hI, ⟨hD, hT⟩, by omega, fun _ _ _ hr => t.guar_of_phases hcount hle hlen M M.init (Runs2.runFrom hr)⟩

end StreamTask

#print axioms SeqTask.scan_getElem?_snd
#print axioms CombTask.toSeq_follows_iff
#print axioms CombTask.toSeq_satisfiedAt_iff
#print axioms SeqTask.claim_of_cycle
#print axioms SeqTask.satisfiedAt_of_cycle
#print axioms TxTask.guar_of_phases
#print axioms StreamTask.guar_of_phases
#print axioms TxTask.satisfiedAt_of_phases
#print axioms StreamTask.satisfiedAt_of_phases

end SvGolf
