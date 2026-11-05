import SvGolf.Task
import SeqTask
import LeanModels.Sv.Observe

/-!
# Task v2: the trusted skeleton `Sat` over an observation model (DRAFT, Day 4)

**Status: DRAFT of trusted text, for review (Day 5).** Not in any lake library; imported by
nothing trusted. Compile with `compile-obs.sh`. It imports the sequential sketch `SeqTask.lean`
(itself an untrusted 10/30 sketch) for the `SeqTask` structure. The proofs here (the two instance
theorems and the transport lemma) are kernel-checked like any other; what needs review is the
definitions.

## The skeleton (ARCH-NOTE §4.5, specialized to the observation interface of `LeanModels/Sv/Observe.lean`)

A **specification** `Spec P` over a parameter type `P` fixes, per parameter: the ports (`iface`), the
clock and reset ports (`clocking`), the input ports the environment controls freely (`free`), a
**rely** and a **guarantee**, both over the trusted observations (one pre and one post sample of the
ports per cycle). `SatAt M Adm C p d` says that design `d` satisfies `C` at `p` over backend `M`:

1. **interface**: the design's ports are exactly `C.iface p`;
2. **admission and non-vacuity**:
   - `Adm d`, the backend's admission predicate: `Unclocked`/`ClockedBy` for `run2`. These are
     `Design2` syntax, and exist because `run2` ignores the clock's value;
   - `Progress`: every disciplined environment has a completed behaviour, under every choice;
   - `Receptive`: every sequence of known values on the free inputs is seen in the pre samples of
     some behaviour, under every choice;
3. **safety**: for every choice, every environment satisfying the **clocking discipline** (an
   environment rely, ruling (c)), every completed behaviour, and every finite prefix of it on which
   the rely holds, the guarantee holds.

`Sat M Adm C sem` is `SatAt` at every parameter in the task's range (`inRange`) that the parameter's
**declared type** can hold (`inType`). For `parameter int N`, that is `IntParam`: `N < 2^31`.

**The declared type's range** (lead's input of 2026-11-02, from agent L's loop work; a decision for
the maintainers). A `parameter int N` cannot hold 2^31 or more, and the faithful 32-bit loop semantics needs
`N < 2^31`. v1 statements quantify over every `N` in range, because the model reads parameters as
unbounded `Int` (a recorded restriction). The skeleton intersects the task's range with the type's.
That makes it weaker than v1, so v1 records keep holding (`Sat.mono_inType` here;
`statement_stim_bounded` in `ObsComb.lean` and `ObsSeq.lean`).

**Refinement (lead, Day 5), part of decision (1).** Bounding the parameter alone (`IntParam`) is
not the faithful range. Elaboration evaluates width and index expressions in 32-bit `int` too:
`clmul`'s port `logic [2*N-2:0] p` overflows once `N` passes about 2^30, so its faithful range is
about `N ≤ 2^30`. The faithful notion is "every elaboration-time INT-class expression stays in
32 bits at this point", which `PDesign.int32Agrees` (`Param2.lean`) checks at one point. JUDGED:
the range must stay **per task, explicit and independent of the player's design**. A range defined
from the submitted design's own `int32Agrees` would let a design that overflows at every `N` (say,
through an unused `2*N*N*N` width) make the statement vacuous. So `inType` stays a per-task
predicate (`IntParam`, or a tighter task bound such as `N ≤ 2^30` for `clmul`). Its faithfulness is
an obligation on the task's REFERENCE: `int32Agrees ref [N]` on the bounded range, checked by
`#guard` at sample points now, and by a symbolic theorem once elaboration lemmas exist. Either way
v1 implies the bounded statement.

**Rulings this follows** (lead, 2026-11-02, Day 4):
* (a) **inputs are read from the pre sample**: an input's value in a cycle is the value it holds at
  the cycle's edge (E's convention). No environment view appears in trusted text.
* (b) ports only: the guarantee reads trusted samples, which hold the ports and nothing else.
* (c) the clocking discipline is an environment rely (`ObservationModel.Disciplined`), separate from
  the backend's admission predicate `Adm`.
* (d) both samples are exposed; each task chooses. `CombTask` and `SeqTask` keep v1's claims on the
  **post** sample, reading inputs from the **pre** sample. A register-file or Mealy-output task states
  its claim on pre (`ObsSeq.lean`'s `ReadsBeforeWrite`).

**Why `Receptive` is a conjunct** (JUDGED, new with ruling (a)). Once inputs are read from the pre
sample, a guarantee of the form "if the pre sample holds known inputs `v`, the post sample holds
`fn v`" is vacuous on any cycle whose pre sample never holds those inputs. Over `run2`, a design can
write its own input ports during the settle (for example `assign a = 1'b1` on input `a`): its pre
sample then never shows `a = 0`, and `fn` is never checked there. In E the same design has a second
driver on the input net, so the pre sample shows `x` where the two drivers disagree; the claim is
vacuous there too. `Receptive` closes this: every sequence of known values on the free inputs must
appear in the pre samples of some behaviour. It is the realizability/receptiveness twin of ARCH-NOTE
D11. The clock is not free: E's pre sample of a posedge slot always shows the clock low.

**Instances** (`CombTask.statement_obs_iff_sat`, `SeqTask.statement_obs_iff_sat`): the task-shaped
statements `CombTask.Statement_obs` and `SeqTask.Statement_obs` (the restatements under ruling (a))
are exactly `Sat` of the compiled `Spec`s `toSpec`. Their guarantees are prefix-closed, so "on every
prefix" adds nothing for them.

**Not decided here** (questions for the review):
* For a task with a non-trivial rely, `Receptive` should probably range over input sequences the
  rely admits. Both instances have `rely = True`.
* `Adm` stays a parameter until E exists. Under E the admission predicate for `CombTask` is empty: a
  clocked process whose clock never rises is simply never run.
-/

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe SvGolf

/-! ## Reading ports -/

/-- `HoldAllS s sigs v`: in the trusted sample `s`, every port `(n, w)` of `sigs` holds the fully
known `w`-bit vector that `v` assigns it (the sample form of v1's `HoldAll`). -/
def HoldAllS (s : PortSample) : (sigs : List Sig) → Vals (sigs.map Prod.snd) → Prop
  | [], _ => True
  | (n, _) :: sigs, v => s.read n = some (LVec.ofBitVec v.1) ∧ HoldAllS s sigs v.2

/-! ## The skeleton (DRAFT of trusted text) -/

/-- **A Task v2 specification** over parameters `P`: ports, clocking, the freely driven inputs, and a
rely and a guarantee over the trusted observations (one `CycleObs PortSample` per cycle). -/
structure Spec (P : Type) where
  /-- The parameter values the task covers. -/
  inRange : P → Prop
  /-- The values the parameter's declared type can hold (`IntParam` for `parameter int N`). The
  statement covers `inRange ∩ inType`. -/
  inType : P → Prop
  /-- The ports at each parameter value. -/
  iface : P → Iface
  /-- The clock and reset ports the clocking discipline refers to. -/
  clocking : Clocking
  /-- The inputs the environment drives freely in every cycle (receptiveness): every input except
  the clock. -/
  free : P → List Sig
  /-- The task's rely on the observed history (`True` for both v1 task classes). -/
  rely : P → List (CycleObs PortSample) → Prop
  /-- The guarantee, required on every finite prefix on which the rely holds. -/
  guar : P → List (CycleObs PortSample) → Prop

/-- **Receptiveness**: under every choice, every finite sequence `s` of known values on the free
inputs `free` is seen: some disciplined environment gives a completed behaviour with one cycle per
entry of `s`, whose pre sample in cycle `c` holds exactly `s[c]` on the free inputs. -/
def Receptive (M : ObservationModel) (k : Clocking) (d : M.Design) (free : List Sig) : Prop :=
  ∀ (ch : M.Choice) (s : List (Vals (free.map Prod.snd))),
    ∃ env b, M.Disciplined k env ∧ M.Behaves d ch env b ∧ b.length = s.length ∧
      ∀ (c : Nat) (o : CycleObs PortSample) (v : Vals (free.map Prod.snd)),
        b[c]? = some o → s[c]? = some v → HoldAllS o.pre free v

/-- **The statement at one parameter value**: interface; admission, progress and receptiveness;
safety under the clocking discipline, on every prefix where the rely holds. -/
def SatAt {P : Type} (M : ObservationModel) (Adm : M.Design → Prop) (C : Spec P) (p : P)
    (d : M.Design) : Prop :=
  M.iface d = C.iface p ∧
    (Adm d ∧ M.Progress C.clocking d ∧ Receptive M C.clocking d (C.free p)) ∧
    M.Safe C.clocking d fun _ b => ∀ n, C.rely p (b.take n) → C.guar p (b.take n)

/-- **`Sat`**: the design family `sem` satisfies `C` at every parameter value in the task's range
that the parameter's declared type can hold. -/
def Sat {P : Type} (M : ObservationModel) (Adm : M.Design → Prop) (C : Spec P)
    (sem : P → M.Design) : Prop :=
  ∀ p, C.inRange p → C.inType p → SatAt M Adm C p (sem p)

/-- The range of a parameter of SystemVerilog type `int` (32-bit signed, IEEE 1800 §6.11), read as a
`Nat`: below 2^31. -/
def IntParam (N : Nat) : Prop := N < 2 ^ 31

/-- Narrowing the type's range weakens `Sat` (this is how the bounded statement inherits v1's
records). -/
theorem Sat.mono_inType {P : Type} {M : ObservationModel} {Adm : M.Design → Prop} {C : Spec P}
    {sem : P → M.Design} {ty : P → Prop} (hty : ∀ p, ty p → C.inType p) (h : Sat M Adm C sem) :
    Sat M Adm { C with inType := ty } sem :=
  fun p hr ht => h p hr (hty p ht)

/-- The safety conjunct moves between backends (`Safe.of_included`); progress and receptiveness
are existence claims and are proved per backend. -/
theorem SatAt.safe_of_included {P : Type} {M₁ M₂ : ObservationModel} {C : Spec P} {p : P}
    {d₁ : M₁.Design} {d₂ : M₂.Design} (hinc : Included M₁ M₂ C.clocking d₁ d₂)
    (h : M₂.Safe C.clocking d₂ fun _ b => ∀ n, C.rely p (b.take n) → C.guar p (b.take n)) :
    M₁.Safe C.clocking d₁ fun _ b => ∀ n, C.rely p (b.take n) → C.guar p (b.take n) :=
  Safe.of_included hinc h

/-! ## Prefixes -/

/-- A guarantee is prefix-closed when it survives truncation of the behaviour. -/
def PrefixClosed (G : List (CycleObs PortSample) → Prop) : Prop :=
  ∀ b n, G b → G (b.take n)

/-- For a prefix-closed guarantee and the trivial rely, "on every prefix" is the guarantee itself. -/
theorem prefixes_iff {G : List (CycleObs PortSample) → Prop} (hG : PrefixClosed G)
    (b : List (CycleObs PortSample)) : (∀ n, True → G (b.take n)) ↔ G b :=
  ⟨fun h => by simpa using h b.length trivial, fun h n _ => hG b n h⟩

theorem getElem?_of_take {α : Type} :
    ∀ {b : List α} {n c : Nat} {o : α}, (b.take n)[c]? = some o → b[c]? = some o
  | [], _, _, _, h => by simp at h
  | _ :: _, 0, _, _, h => by simp at h
  | _ :: _, _ + 1, 0, _, h => by simpa using h
  | _ :: _, _ + 1, _ + 1, _, h => by
      simp only [List.take_succ_cons, List.getElem?_cons_succ] at h ⊢
      exact getElem?_of_take h

theorem Iface.eq_mk_iff {I : Iface} {a b : List Sig} :
    I = ⟨a, b⟩ ↔ I.inputs = a ∧ I.outputs = b := by
  cases I; simp

end SvGolf.Arch

/-! ## `CombTask` as an instance (DRAFT of trusted text; the instance theorem is proved) -/

namespace SvGolf.CombTask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf.Arch

variable (t : CombTask)

/-- Conjunct 1 over `M`: the design's ports are exactly the task's, names, order and widths
included. -/
def InterfaceObs (M : ObservationModel) (N : Nat) (d : M.Design) : Prop :=
  (M.iface d).inputs = t.inputs N ∧ (M.iface d).outputs = t.outputs N

/-- **Conjunct 3 over `M`, inputs read from the pre sample** (ruling (a)): in every completed
behaviour (every choice, every environment), every cycle whose pre sample holds every input port
at a known value of the port's width ends with a post sample whose output ports hold exactly
`t.fn N` of those values. -/
def Computes_obs (M : ObservationModel) (N : Nat) (d : M.Design) : Prop :=
  ∀ ch env b, M.Disciplined {} env → M.Behaves d ch env b →
    ∀ (c : Nat) (o : CycleObs PortSample), b[c]? = some o →
      ∀ v, HoldAllS o.pre (t.inputs N) v → HoldAllS o.post (t.outputs N) (t.fn N v)

/-- The statement at one parameter value over `M`: interface; admission, progress, receptiveness on
every input; function. -/
def SatisfiedAt_obs (M : ObservationModel) (Adm : M.Design → Prop) (N : Nat) (d : M.Design) :
    Prop :=
  t.InterfaceObs M N d ∧ (Adm d ∧ M.Progress {} d ∧ Receptive M {} d (t.inputs N)) ∧
    t.Computes_obs M N d

/-- **The challenge statement over `M`**, at every `N` in the task's range that the parameter's
declared type can hold (`ty`; `IntParam` for `parameter int N`). -/
def Statement_obs (ty : Nat → Prop) (M : ObservationModel) (Adm : M.Design → Prop)
    (sem : Nat → M.Design) : Prop :=
  ∀ N, t.inRange N → ty N → t.SatisfiedAt_obs M Adm N (sem N)

/-- The per-cycle guarantee of a combinational task. -/
def guarObs (N : Nat) (b : List (CycleObs PortSample)) : Prop :=
  ∀ (c : Nat) (o : CycleObs PortSample), b[c]? = some o →
    ∀ v, HoldAllS o.pre (t.inputs N) v → HoldAllS o.post (t.outputs N) (t.fn N v)

/-- **`CombTask` compiled into a `Spec`**, for a parameter whose declared type holds `ty`: no clock,
no reset, every input free, trivial rely. -/
def toSpec (ty : Nat → Prop) : Spec Nat where
  inRange := t.inRange
  inType := ty
  iface N := ⟨t.inputs N, t.outputs N⟩
  clocking := {}
  free := t.inputs
  rely _ _ := True
  guar := t.guarObs

theorem guarObs_prefixClosed (N : Nat) : PrefixClosed (t.guarObs N) :=
  fun _ _ h c o hc v hv => h c o (getElem?_of_take hc) v hv

/-- **`CombTask` is an instance of the skeleton**, at one parameter value. -/
theorem satisfiedAt_obs_iff_satAt {ty : Nat → Prop} {M : ObservationModel}
    {Adm : M.Design → Prop} {N : Nat} {d : M.Design} :
    t.SatisfiedAt_obs M Adm N d ↔ SatAt M Adm (t.toSpec ty) N d := by
  unfold SatisfiedAt_obs SatAt InterfaceObs
  rw [show ((t.toSpec ty).iface N) = ⟨t.inputs N, t.outputs N⟩ from rfl, Iface.eq_mk_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  unfold Computes_obs ObservationModel.Safe
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun b =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact (prefixes_iff (t.guarObs_prefixClosed N) b).symm

/-- **`CombTask` is an instance of the skeleton**: the challenge statement over `M` is `Sat` of
`t.toSpec`. -/
theorem statement_obs_iff_sat {ty : Nat → Prop} {M : ObservationModel} {Adm : M.Design → Prop}
    {sem : Nat → M.Design} : t.Statement_obs ty M Adm sem ↔ Sat M Adm (t.toSpec ty) sem :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    t.satisfiedAt_obs_iff_satAt

end SvGolf.CombTask

/-! ## `SeqTask` as an instance (DRAFT of trusted text; the instance theorem is proved) -/

namespace SvGolf.Seq.SeqTask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch

variable (t : SeqTask)

/-- The task's clock and reset ports. -/
def clocking : Clocking := ⟨t.clk, t.rst⟩

/-- The free inputs: the reset port (if any) and the data inputs. Not the clock. -/
def free (N : Nat) : List Sig := (t.rst.map fun r => (r.1, 1)).toList ++ t.inputs N

/-- The trusted sample `s` holds the reset port at the level that means `r` (asserted if `r`).
Without a reset port only `r = false` is available. -/
def RstHolds (s : PortSample) (r : Bool) : Prop :=
  match t.rst with
  | none => r = false
  | some (n, lvl) => s.read n = some (LVec.ofBitVec (BitVec.ofBool (if r then lvl else !lvl)))

/-- The trusted sample `s` holds the spec-side input `(r, v)`: reset at the level for `r`, every data
input at the known value in `v`. -/
def Holds (N : Nat) (s : PortSample) (p : Bool × t.Ins N) : Prop :=
  t.RstHolds s p.1 ∧ HoldAllS s (t.inputs N) p.2

/-- The trusted sample `s` shows the observation of spec state `a.1` under input `a.2`. -/
def ObsOKS (N : Nat) (s : PortSample) (a : t.State N × t.Ins N) : Prop :=
  HoldAllS s (t.outputs N) (t.obs N a.1 a.2)

/-- Conjunct 1 over `M`: exactly the task's ports (clock, reset, data inputs; outputs). -/
def InterfaceObs (M : ObservationModel) (N : Nat) (d : M.Design) : Prop :=
  (M.iface d).inputs = t.ports N ∧ (M.iface d).outputs = t.outputs N

/-- **The sequential guarantee on one behaviour, inputs read from the pre samples**: from every start
`c0`, if the pre samples of cycles `c0, c0 + 1, …` hold the spec-side inputs `ps` (the first one
asserting reset), then the post samples of those cycles show the spec machine's observations (v1's
Moore claim, ruling (d)). -/
def FollowsB (N : Nat) (b : List (CycleObs PortSample)) : Prop :=
  ∀ (c0 : Nat) (ps : List (Bool × t.Ins N)), t.StartOK N ps →
    (∀ j p, ps[j]? = some p → ∃ o, b[c0 + j]? = some o ∧ t.Holds N o.pre p) →
    ∀ j a, (t.scan N (t.init N) ps)[j]? = some a →
      ∃ o, b[c0 + j]? = some o ∧ t.ObsOKS N o.post a

/-- **Conjunct 3 over `M`**: every completed behaviour in a disciplined environment follows the spec
machine. -/
def Follows_obs (M : ObservationModel) (N : Nat) (d : M.Design) : Prop :=
  ∀ ch env b, M.Disciplined t.clocking env → M.Behaves d ch env b → t.FollowsB N b

/-- The statement at one parameter value over `M`. -/
def SatisfiedAt_obs (M : ObservationModel) (Adm : M.Design → Prop) (N : Nat) (d : M.Design) :
    Prop :=
  t.InterfaceObs M N d ∧
    (Adm d ∧ M.Progress t.clocking d ∧ Receptive M t.clocking d (t.free N)) ∧
    t.Follows_obs M N d

/-- **The challenge statement over `M`**, at every `N` in the task's range that the parameter's
declared type can hold (`ty`). -/
def Statement_obs (ty : Nat → Prop) (M : ObservationModel) (Adm : M.Design → Prop)
    (sem : Nat → M.Design) : Prop :=
  ∀ N, t.inRange N → ty N → t.SatisfiedAt_obs M Adm N (sem N)

/-- **`SeqTask` compiled into a `Spec`**: its clock and reset, the free inputs, trivial rely, the
`FollowsB` guarantee. -/
def toSpec (ty : Nat → Prop) : Spec Nat where
  inRange := t.inRange
  inType := ty
  iface N := ⟨t.ports N, t.outputs N⟩
  clocking := t.clocking
  free := t.free
  rely _ _ := True
  guar := t.FollowsB

theorem followsB_prefixClosed (N : Nat) : PrefixClosed (t.FollowsB N) := by
  intro b n h c0 ps hstart hdrv j a ha
  -- the hypothesis on the prefix is a hypothesis on `b`
  obtain ⟨o, ho, hok⟩ := h c0 ps hstart
    (fun j p hp => by
      obtain ⟨o, ho, hh⟩ := hdrv j p hp
      exact ⟨o, getElem?_of_take ho, hh⟩) j a ha
  -- cycle `c0 + j` is inside the prefix, because `ps` has an entry `j`
  have hsnd := t.scan_getElem?_snd N (t.init N) ps j
  rw [ha] at hsnd
  obtain ⟨p, hp⟩ : ∃ p, ps[j]? = some p := by
    cases hpj : ps[j]? with
    | none => rw [hpj] at hsnd; simp at hsnd
    | some p => exact ⟨p, rfl⟩
  obtain ⟨o', ho', -⟩ := hdrv j p hp
  have : o' = o := Option.some.inj ((getElem?_of_take ho').symm.trans ho)
  subst this
  exact ⟨o', ho', hok⟩

/-- **`SeqTask` is an instance of the skeleton**, at one parameter value. -/
theorem satisfiedAt_obs_iff_satAt {ty : Nat → Prop} {M : ObservationModel}
    {Adm : M.Design → Prop} {N : Nat} {d : M.Design} :
    t.SatisfiedAt_obs M Adm N d ↔ SatAt M Adm (t.toSpec ty) N d := by
  unfold SatisfiedAt_obs SatAt InterfaceObs
  rw [show ((t.toSpec ty).iface N) = ⟨t.ports N, t.outputs N⟩ from rfl, Iface.eq_mk_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  unfold Follows_obs ObservationModel.Safe
  refine forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun b =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact (prefixes_iff (t.followsB_prefixClosed N) b).symm

/-- **`SeqTask` is an instance of the skeleton**: the challenge statement over `M` is `Sat` of
`t.toSpec`. -/
theorem statement_obs_iff_sat {ty : Nat → Prop} {M : ObservationModel} {Adm : M.Design → Prop}
    {sem : Nat → M.Design} : t.Statement_obs ty M Adm sem ↔ Sat M Adm (t.toSpec ty) sem :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    t.satisfiedAt_obs_iff_satAt

end SvGolf.Seq.SeqTask

#print axioms SvGolf.Arch.SatAt.safe_of_included
#print axioms SvGolf.Arch.Sat.mono_inType
#print axioms SvGolf.Arch.prefixes_iff
#print axioms SvGolf.Arch.getElem?_of_take
#print axioms SvGolf.Arch.Iface.eq_mk_iff
#print axioms SvGolf.CombTask.guarObs_prefixClosed
#print axioms SvGolf.CombTask.satisfiedAt_obs_iff_satAt
#print axioms SvGolf.CombTask.statement_obs_iff_sat
#print axioms SvGolf.Seq.SeqTask.followsB_prefixClosed
#print axioms SvGolf.Seq.SeqTask.satisfiedAt_obs_iff_satAt
#print axioms SvGolf.Seq.SeqTask.statement_obs_iff_sat
