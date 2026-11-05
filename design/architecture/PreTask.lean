import TaskV2
import LeanModels.Sv.CycleMachine

/-!
# `PreTask`: a Mealy task, its claim on the PRE sample (DRAFT, register-file exemplar)

**Status.** `PreTask`, `FollowsPreB`, `SatisfiedAt_obs`, `toSpec`: **DRAFT of trusted text**, a third
task class beside `CombTask` and `SeqTask` (ruling (d), Day 4: a register-file or Mealy-output task
states its claim on pre). `statement_obs_iff_sat` (the `Sat` instance) and `followsPreB_run` (the
reduction to a cycle machine) are proved, backend-independent.

## The claim

A `PreTask` has a clock, data inputs, outputs and a spec machine (`State`, `init`, `step`). Its
observation `obs` is a claim on the PRE sample of a cycle, the value a synchronous consumer sees at
the edge, from the spec state BEFORE the cycle's step and the cycle's inputs. `none` means no claim.
A register file's spec state holds `Option` words: an unwritten word makes no claim, so the
power-up `x` contents need no reset.

`FollowsPreB`: from every start cycle `c0`, if the pre samples of cycles `c0, c0 + 1, …` hold known
inputs `ps`, then at each of those cycles the pre sample's outputs are what `obs` claims from the spec
machine run from `init` on `ps`. Because claims may start at any cycle, `init` must be a state that
claims nothing about the past (all words unwritten).
-/

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe SvGolf

/-- **A Mealy task with its claim on the pre sample.** -/
structure PreTask (P : Type) where
  inRange : P → Prop
  inType : P → Prop
  clk : String
  inputs : P → List Sig
  outputs : P → List Sig
  State : P → Type
  init : (p : P) → State p
  step : (p : P) → State p → Vals ((inputs p).map Prod.snd) → State p
  obs : (p : P) → State p → Vals ((inputs p).map Prod.snd) → Option (Vals ((outputs p).map Prod.snd))

namespace PreTask

variable {P : Type} (t : PreTask P)

/-- The spec state before input `j` of `ps`, from `init`. -/
def stateAt (p : P) (ps : List (Vals ((t.inputs p).map Prod.snd))) (j : Nat) : t.State p :=
  (ps.take j).foldl (t.step p) (t.init p)

/-- **The claim on one behaviour.** -/
def FollowsPreB (p : P) (b : List (CycleObs PortSample)) : Prop :=
  ∀ (c0 : Nat) (ps : List (Vals ((t.inputs p).map Prod.snd))),
    (∀ (j : Nat) (v : Vals ((t.inputs p).map Prod.snd)), ps[j]? = some v →
      ∃ o : CycleObs PortSample, b[c0 + j]? = some o ∧ HoldAllS o.pre (t.inputs p) v) →
    ∀ (j : Nat) (v : Vals ((t.inputs p).map Prod.snd)) (out : Vals ((t.outputs p).map Prod.snd)),
      ps[j]? = some v → t.obs p (t.stateAt p ps j) v = some out →
      ∃ o : CycleObs PortSample, b[c0 + j]? = some o ∧ HoldAllS o.pre (t.outputs p) out

def clocking : Clocking := ⟨some t.clk, none⟩

/-- The statement at one parameter value over `M`. -/
def SatisfiedAt_obs (M : ObservationModel) (Adm : M.Design → Prop) (p : P) (d : M.Design) : Prop :=
  M.iface d = ⟨(t.clk, 1) :: t.inputs p, t.outputs p⟩ ∧
    (Adm d ∧ M.Progress t.clocking d ∧ Receptive M t.clocking d (t.inputs p)) ∧
    ∀ ch env b, M.Disciplined t.clocking env → M.Behaves d ch env b → t.FollowsPreB p b

/-- `PreTask` compiled into a `Spec`. -/
def toSpec : Spec P where
  inRange := t.inRange
  inType := t.inType
  iface p := ⟨(t.clk, 1) :: t.inputs p, t.outputs p⟩
  clocking := t.clocking
  free := t.inputs
  rely _ _ := True
  guar := t.FollowsPreB

theorem followsPreB_prefixClosed (p : P) : PrefixClosed (t.FollowsPreB p) := by
  intro b n h c0 ps hdrv j v out hv hobs
  obtain ⟨o, ho, hok⟩ := h c0 ps (fun j v hv => by
    obtain ⟨o, ho, hh⟩ := hdrv j v hv
    exact ⟨o, getElem?_of_take ho, hh⟩) j v out hv hobs
  obtain ⟨o', ho', -⟩ := hdrv j v hv
  have : o' = o := Option.some.inj ((getElem?_of_take ho').symm.trans ho)
  subst this
  exact ⟨o', ho', hok⟩

/-- **`PreTask` is an instance of the skeleton** (Task v2 `Sat`). -/
theorem satisfiedAt_obs_iff_satAt {M : ObservationModel} {Adm : M.Design → Prop} {p : P}
    {d : M.Design} : t.SatisfiedAt_obs M Adm p d ↔ SatAt M Adm t.toSpec p d := by
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  unfold ObservationModel.Safe
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun b =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact (prefixes_iff (t.followsPreB_prefixClosed p) b).symm

/-- **The claim from a cycle machine's one-cycle facts** (pure: no schedule, no fuel, no interpreter
state). `R` relates a machine store to the spec state. Every store relates to `init` (claims may
start anywhere), the step keeps `R`, and the claim holds of `out s i` when `R s q` and the sample holds
the cycle's known inputs. -/
theorem followsPreB_run (p : P) (m : CycleMachine) (tk : m.Tick) (R : m.Store → t.State p → Prop)
    (hR0 : ∀ s, R s (t.init p))
    (hobs : ∀ s i q v out, R s q → HoldAllS (m.out s i) (t.inputs p) v →
      t.obs p q v = some out → HoldAllS (m.out s i) (t.outputs p) out)
    (hstep : ∀ s i q v, R s q → HoldAllS (m.out s i) (t.inputs p) v →
      R (m.next s i tk) (t.step p q v)) :
    ∀ s0 is, t.FollowsPreB p (m.run tk s0 is) := by
  -- from cycle 0 of a run, any store related to the spec state `q`
  have main : ∀ (ps : List (Vals ((t.inputs p).map Prod.snd))) (s : m.Store) (is : List m.In)
      (q : t.State p), R s q →
      (∀ (j : Nat) (v : Vals ((t.inputs p).map Prod.snd)), ps[j]? = some v →
        ∃ o : CycleObs PortSample, (m.run tk s is)[j]? = some o ∧ HoldAllS o.pre (t.inputs p) v) →
      ∀ (j : Nat) (v : Vals ((t.inputs p).map Prod.snd)) (out : Vals ((t.outputs p).map Prod.snd)),
        ps[j]? = some v → t.obs p ((ps.take j).foldl (t.step p) q) v = some out →
        ∃ o : CycleObs PortSample, (m.run tk s is)[j]? = some o ∧ HoldAllS o.pre (t.outputs p) out := by
    intro ps
    induction ps with
    | nil => intro s is q _ _ j v out hv; simp at hv
    | cons v0 rest ih =>
        intro s is q hR hdrv j v out hv hobs'
        obtain ⟨o0, ho0, hd0⟩ := hdrv 0 v0 (by simp)
        cases is with
        | nil => simp at ho0
        | cons i is =>
            simp only [CycleMachine.run_cons, List.getElem?_cons_zero, Option.some.injEq] at ho0
            subst ho0
            cases j with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
                subst hv
                exact ⟨_, rfl, hobs s i q _ out hR hd0 (by simpa using hobs')⟩
            | succ j =>
                obtain ⟨o, ho, hok⟩ := ih (m.next s i tk) is (t.step p q v0) (hstep s i q v0 hR hd0)
                  (fun j' v' hv' => by
                    obtain ⟨o, ho, hh⟩ := hdrv (j' + 1) v' (by simpa using hv')
                    exact ⟨o, by simpa using ho, hh⟩) j v out (by simpa using hv)
                  (by simpa [List.take_succ_cons] using hobs')
                exact ⟨o, by simpa using ho, hok⟩
  intro s0 is c0 ps hdrv j v out hv hobs'
  have hshift : ∀ n, (m.run tk s0 is)[c0 + n]? =
      (m.run tk (m.storeAt tk s0 (is.take c0)) (is.drop c0))[n]? := by
    intro n
    rw [← CycleMachine.run_drop, List.getElem?_drop]
  obtain ⟨o, ho, hok⟩ := main ps _ _ (t.init p) (hR0 _)
    (fun j v hv => by
      obtain ⟨o, ho, hh⟩ := hdrv j v hv
      exact ⟨o, by rw [← hshift]; exact ho, hh⟩) j v out hv hobs'
  exact ⟨o, by rw [hshift]; exact ho, hok⟩

end PreTask

#print axioms PreTask.followsPreB_prefixClosed
#print axioms PreTask.satisfiedAt_obs_iff_satAt
#print axioms PreTask.followsPreB_run

end SvGolf.Arch
