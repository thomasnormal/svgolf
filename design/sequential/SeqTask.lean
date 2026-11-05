import SvGolf.Comb
import LeanModels.Sv.Hier2

/-!
# SeqTask: the sequential task statement (DESIGN SKETCH, not trusted, not in any lake library)

Companion of `README.md` in this directory (sections 2 and 3). Everything here compiles against the
built `svgolf` libraries (`lake env lean design/sequential/SeqTask.lean`, run from `svgolf/`) and
contains no `sorry`. It is a DRAFT of what would go into `SvGolf/Task.lean` after the maintainers approve
the statement shape.

## What is here

1. `SeqTask`, the data of a sequential task: a Lean state machine (`State`, `init`, `step`, `obs`),
   the data inputs and outputs, and the clock and reset PROTOCOL (an `Option` each, so that a
   combinational task is the case "no clock, no reset, one-point state").
2. `ClockedBy`, the clock discipline that replaces `Unclocked` (and closes the undriven-clock
   exploit without touching ls-sv's one-edge-per-cycle model): every edge process is clocked by the
   task's clock port, the clock is an input port, and NOTHING ELSE mentions it; an asynchronous
   reset block uses the task's reset port.
3. `SeqTask.SatisfiedAt` and `SeqTask.Statement`: interface, discipline and termination, and the
   claim "from every reset, every good input trace gives the spec machine's output trace".
4. `CombTask.toSeq` and `toSeq_satisfiedAt_iff`: the combinational statement is the degenerate case
   (proved, so the new statement does not move the old one).
5. `SeqTask.satisfiedAt_of_cycle`: the REDUCTION THEOREM the player-side tactics target. A design
   satisfies the statement as soon as there is an invariant `Inv` on snapshots, a simulation
   relation `R` to the spec state, and ONE-CYCLE lemmas (reset cycle, ordinary cycle) in the shape
   `cycleStep2 d σ F inputs prev k = .ok (st', k')`. Proved from `Runs2.snapshot_step`.

## Reading guide for the statement (`Follows`)

For every completed run (every schedule, every stimulus), every start cycle `c0`, and every list
`ps` of spec-side inputs `(reset asserted?, data values)` whose first entry asserts reset and
such that the stimulus entries `c0, c0+1, ...` drive exactly those (the reset port at its
asserted or deasserted level, every data input at a known value of the right width): the snapshots
`c0, c0+1, ...` hold, on the output ports, the spec machine's observation after each step, the
machine being restarted at `init` by that first reset. Nothing is claimed before the first reset,
and nothing about the clock port's value (ls-sv ignores it; the discipline says nothing else may
read it).
-/

namespace LeanModels.Sv

open SvGolf

/-! ## Names mentioned by a design (for the clock discipline)

These helpers live in `LeanModels.Sv` so that dot notation (`p.mentionsData k`) works on `Process2`. -/

mutual
/-- Does an assignment target mention `n` (write it, or read it in an index)? -/
def Lhs2.mentions (n : String) : Lhs2 → Bool
  | .ident m => m == n
  | .slice m _ _ => m == n
  | .index m i _ => m == n || i.idents.contains n
  | .concat ps => Lhs2.mentionsList n ps
termination_by structural t => t

def Lhs2.mentionsList (n : String) : List Lhs2 → Bool
  | [] => false
  | t :: ts => t.mentions n || Lhs2.mentionsList n ts
termination_by structural ts => ts
end

mutual
/-- Does a statement mention the signal `n`, anywhere (targets, conditions, right-hand sides)? -/
def Stmt2.mentions (n : String) : Stmt2 → Bool
  | .blockingAssign t e | .nbaAssign t e => t.mentions n || e.idents.contains n
  | .ifStmt c t e => c.idents.contains n || t.mentions n || Stmt2.mentionsOpt n e
  | .block body => Stmt2.mentionsList n body.toList
  | .caseStmt s items dflt _ _ =>
      s.idents.contains n || CaseItem2.mentionsList n items.toList || Stmt2.mentionsOpt n dflt
  | .unsupported _ _ => false
termination_by structural s => s

def Stmt2.mentionsOpt (n : String) : Option Stmt2 → Bool
  | none => false
  | some s => s.mentions n
termination_by structural o => o

def Stmt2.mentionsList (n : String) : List Stmt2 → Bool
  | [] => false
  | s :: ss => s.mentions n || Stmt2.mentionsList n ss
termination_by structural ss => ss

def CaseItem2.mentions (n : String) : CaseItem2 → Bool
  | .mk pats body => (Expr2.listIdents pats.toList).contains n || body.mentions n
termination_by structural it => it

def CaseItem2.mentionsList (n : String) : List CaseItem2 → Bool
  | [] => false
  | it :: rest => it.mentions n || CaseItem2.mentionsList n rest
termination_by structural its => its
end

/-- Does a process mention `n` as DATA? The clock (and reset) names that an edge process carries in
its sensitivity list are not data mentions. -/
def Process2.mentionsData (n : String) : Process2 → Bool
  | .alwaysFF _ b | .alwaysPlain _ b | .alwaysFFR _ _ b _ | .alwaysComb b => b.mentions n
  | .assign t e => t.mentions n || e.idents.contains n
  | .unsupported _ _ => false

/-- The asynchronous-reset name of an edge process, if it has one. -/
def Process2.resetName? : Process2 → Option String
  | .alwaysFFR _ r _ _ => some r
  | _ => none

end LeanModels.Sv

namespace SvGolf.Seq

open LeanModels.Sv SvGolf

/-- **The clock discipline** (replaces `Unclocked` for a task with a clock). `k` is an input port;
every edge-phase process is clocked by `k` and, when it has an asynchronous reset, by the task's
reset port `rst`; no process mentions `k` as data. With this, "one stimulus entry = one rising edge
of `k`" is not an approximation of the simulators' reading but the definition of the protocol, and
an undriven, tied, derived or gated clock cannot occur. -/
def ClockedBy (k : String) (rst : Option String) (d : Design2) : Prop :=
  k ∈ d.inputNames.toList ∧
  ∀ p ∈ d.processes.toList,
    (p.isEdgePhase = true → p.clock? = some k) ∧
    (∀ r, p.resetName? = some r → rst = some r) ∧
    p.mentionsData k = false

/-! ## The task -/

/-- A sequential task for a one-parameter design family. `clk` and `rst` are `none` for a
combinational task. `rst = some (name, level)`: the port `name` asserts reset when it carries
`level`. `State`, `init`, `step`, `obs` are the spec machine: `obs` is read AFTER the edge, with the
cycle's inputs still applied (ls-sv's snapshot); a task with registers should ignore its input
argument (`Moore`), so that the observation is the registered one. -/
structure SeqTask where
  inRange : Nat → Prop
  clk : Option String
  rst : Option (String × Bool)
  inputs : Nat → List Sig
  outputs : Nat → List Sig
  State : Nat → Type
  init : (N : Nat) → State N
  step : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → State N
  obs : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → Vals ((outputs N).map Prod.snd)

namespace SeqTask

variable (t : SeqTask)

/-- A Moore task: the observation does not read the current input. The reviewer checks it for every
task with a non-trivial state (the statement does not depend on it). -/
def Moore : Prop := ∀ N s v w, t.obs N s v = t.obs N s w

/-- The input ports of the interface, in order: clock, reset, then the data inputs. -/
def ports (N : Nat) : List Sig :=
  (t.clk.map fun k => (k, 1)).toList ++ (t.rst.map fun r => (r.1, 1)).toList ++ t.inputs N

/-- Conjunct 1: exactly these ports, names, order, widths. -/
def Interface (N : Nat) (d : Design2) : Prop :=
  inputPorts d = t.ports N ∧ outputPorts d = t.outputs N

/-- Conjunct 2a: the clock discipline (no clock: no edge-phase process at all, as `Unclocked`). -/
def Disciplined (d : Design2) : Prop :=
  match t.clk with
  | none => Unclocked d
  | some k => ClockedBy k (t.rst.map Prod.fst) d

/-! ### Spec-side inputs and the spec machine -/

/-- The data values of one cycle. -/
abbrev Ins (N : Nat) := Vals ((t.inputs N).map Prod.snd)

/-- Does the reset port of entry `e` carry the level that means `r` (asserted if `r`)? Without a
reset port only `r = false` is available. -/
def RstDrives (e : SvState) (r : Bool) : Prop :=
  match t.rst with
  | none => r = false
  | some (n, lvl) =>
      SvState.lookup e n = some (LVec.ofBitVec (BitVec.ofBool (if r then lvl else !lvl)))

/-- The stimulus entry `e` drives the spec-side input `(r, v)`: the reset port at the level for `r`,
every data input at the known value in `v`. (The clock port may or may not be bound: ls-sv ignores
its value.) -/
def Drives (N : Nat) (e : SvState) (p : Bool × t.Ins N) : Prop :=
  t.RstDrives e p.1 ∧ HoldAll e (t.inputs N) p.2

/-- The spec state after one cycle: a reset restarts at `init`, any other input applies `step`. -/
def next (N : Nat) (s : t.State N) (r : Bool) (v : t.Ins N) : t.State N :=
  if r then t.init N else t.step N s v

/-- The spec machine's state after each cycle of `ps`, with the cycle's inputs. -/
def scan (N : Nat) : t.State N → List (Bool × t.Ins N) → List (t.State N × t.Ins N)
  | _, [] => []
  | s, (r, v) :: rest => (t.next N s r v, v) :: scan N (t.next N s r v) rest

/-- The snapshot `st` shows the observation of spec state `s` under input `v`. -/
def ObsOK (N : Nat) (st : SvState) (a : t.State N × t.Ins N) : Prop :=
  HoldAll st (t.outputs N) (t.obs N a.1 a.2)

/-- Where a claim may start: at a reset entry (with a reset port); anywhere without one (such a
task is stateless, which the reviewer checks). -/
def StartOK (N : Nat) (ps : List (Bool × t.Ins N)) : Prop :=
  match t.rst with
  | none => True
  | some _ => ps.head?.map Prod.fst = some true

/-- Conjunct 3: from every start, every good input list gives the spec machine's observations.
Index form: if the stimulus entries from `c0` drive `ps` (entry `c0 + j` drives `ps[j]`), then the
snapshot `c0 + j` shows the `j`-th spec observation. -/
def Follows (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
        ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a

/-- The statement at one parameter value. -/
def SatisfiedAt (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ t.Follows N d

/-- **The challenge statement** for a design family `sem : Nat → Design2`. -/
def Statement (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAt N (sem N)

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
def _root_.SvGolf.CombTask.toSeq (c : CombTask) : SeqTask where
  inRange := c.inRange
  clk := none
  rst := none
  inputs := c.inputs
  outputs := c.outputs
  State := fun _ => Unit
  init := fun _ => ()
  step := fun _ _ _ => ()
  obs := fun N _ v => c.fn N v

theorem toSeq_interface (c : CombTask) (N : Nat) (d : Design2) :
    c.toSeq.Interface N d ↔ c.Interface N d := by
  simp [SeqTask.Interface, SeqTask.ports, _root_.SvGolf.CombTask.toSeq, CombTask.Interface]

/-- **The combinational statement is the one-point-state case of the sequential one.** -/
theorem toSeq_follows_iff (c : CombTask) (N : Nat) (d : Design2) :
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
`SeqTask`** (same interface, same `Unclocked`, same termination, same claim). -/
theorem toSeq_satisfiedAt_iff (c : CombTask) (N : Nat) (d : Design2) :
    c.toSeq.SatisfiedAt N d ↔ c.SatisfiedAt N d := by
  unfold SeqTask.SatisfiedAt CombTask.SatisfiedAt
  rw [toSeq_interface, toSeq_follows_iff]
  exact Iff.rfl

/-! ## The reduction theorem: refinement by an invariant -/

/-- **A design satisfies the statement (task with a reset port) as soon as, besides the interface,
the clock discipline and termination, it has**

* `Inv`, an invariant on snapshots (the shape of the state: names, widths, and for the real
  tactics the comb equations), true initially and preserved by every successful cycle;
* `R`, a simulation relation between a snapshot and the spec state;
* a RESET cycle lemma: any successful cycle whose entry drives reset yields `R` with `init` and
  the spec's observation, from ANY invariant state (reset forgets history, x included);
* a STEP cycle lemma: any successful cycle whose entry drives no reset, from a snapshot related to
  `s`, yields `R` with `step s v` and the observation.

The cycle lemmas are about `cycleStep2` at any fuel (so they are `.ok` inversions, which the
register-transfer view of the tactics delivers). Fuel, schedules and the trace never appear. -/
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
    t.SatisfiedAt N d := by
  refine ⟨hI, ⟨hD, hT⟩, ?_⟩
  intro σ stim tr hr c0 ps hstart hdrv
  obtain ⟨rr, hrr⟩ := hrst
  simp only [SeqTask.StartOK, hrr] at hstart
  have hall : ∀ (c : Nat) (st : SvState), tr[c]? = some st → Inv st :=
    hr.forall_of_step hinit (fun fuel inputs prev k st k' hp hc => hinv σ fuel inputs prev k st k' hp hc)
  have hprevInv : ∀ (c : Nat) (prev : SvState), (initState2 d :: tr)[c]? = some prev → Inv prev := by
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
        ∃ prev, (initState2 d :: tr)[c]? = some prev ∧ R prev s) →
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

end SvGolf.Seq
