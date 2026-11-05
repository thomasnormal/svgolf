import TaskV2
import SvGolf.Comb
import LeanModels.Sv.ObserveFrame

/-!
# `CombTask` over `Obs_run2`: v1's convention (`_stim`) and the cost of moving to the pre-sample convention

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status: provisional over `run2`.** Everything here is about the `run2` backend. The trusted
convention is `TaskV2.lean`'s (inputs read from the pre sample, ruling (a)). This file keeps v1's
convention as a separately named variant and measures how far the two are apart over `run2`.

## What is here

1. **`CombTask.Computes_stim` / `SatisfiedAt_stim` / `Statement_stim`**: v1 restated over the
   observation interface of `Obs_run2`, but with v1's input convention: the stimulus entry of cycle
   `c` binds the input (`stimDrive`, a `run2` detail). These were Day 2's `Computes_obs`, renamed
   when ruling (a) made the pre-sample convention the trusted one. `computes_stim_iff`,
   `satisfiedAt_stim_iff` and `statement_stim_iff` prove that they are v1 exactly for designs with no
   qualified `case` (`hnq`: `Obs_run2` omits master's qualified-case trace check, `Observe.lean`), so
   every record stands on them (records are assign-only: `CombDesign.noQualified`).
2. **The cost of the trusted convention over `run2`** (ruling (a) asked for it):
   - `computes_of_computes_obs`, **pre convention ⇒ v1**: one lemma, under `EntryInPre d`. That
     hypothesis says the pre sample holds every input the stimulus entry binds at a known value.
   - It is NOT immediate without `EntryInPre`. `applyInputs2` writes the inputs before the settle,
     and a comb or reset process may then overwrite an input name, which `run2` allows (it has no
     driver resolution). `EntryInPre` follows from a frame lemma ("a settle that writes no input
     keeps the inputs"). No such lemma exists for the general `Design2` interpreter (`execStmt2`'s
     fuel-indexed mutual block); it exists for the assign-only profile only (`Runs2.comb_snapshot`).
   - **v1 ⇒ pre convention** is the direction records need. It is NOT proved here. It covers cycles
     whose known inputs were held from earlier entries, and needs three generic pieces (JUDGED,
     about 250 to 400 lines): (i) the frame lemma above; (ii) a shape invariant (the state's keys are
     the declarations, without duplicates) so that `applyInputs2` with a re-driving entry gives the
     same state; (iii) the replacement argument: re-driving the held values at cycle `c` leaves the
     whole run unchanged, so v1 applies there. And per design, `Receptive`, which `TaskV2` requires.
     **Closed for comb-profile designs** (lead's item (2), Day 9): `ObsCombRedrive.lean`
     (`computes_obs_of_computes`, `statement_obs_of_statement`), by agent A's re-driving argument
     (`LeanModels/Sv/ObserveRedrive.lean`). Re-driving every entry to its pre sample's inputs leaves
     the WHOLE run unchanged, so no per-cycle replacement is needed, and the piece cost 111
     code lines instead of the estimate.
   So records stay on the `_stim` variant (which is v1). **Recorded debt** (lead, Day 5): records
   remain under the `_stim` variants until R-DESIGN2. Their transfer to the trusted convention
   belongs with that transport work (WS1), where receptiveness and driver resolution are native.
   Retirement condition: R-DESIGN2 proved for the record's design.
3. **Receptiveness for free** (lead's steer, Day 5: golfers never prove it by hand).
   `receptive_of_writesInput`: a design that writes no input port (`Design2.writesInput d = false`,
   a decidable syntactic check, true for every design the loader admits; `decide` at a concrete
   parameter, `rfl` at a symbolic one) and terminates
   is `Receptive` on any list of distinct input ports. `entryInPre_of_writesInput`: the same
   hypothesis gives `EntryInPre`, so `computes_of_computes_obs` holds with no semantic hypothesis.
   Both rest on one frame lemma, `LeanModels/Sv/ObserveFrame.lean`.
-/

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe SvGolf

/-- `DrivesAll drive c sigs v`: in cycle `c`, `drive` gives every port `(n, w)` of `sigs` the fully
known `w`-bit vector that `v` assigns it. -/
def DrivesAll (drive : Nat → String → Option LVec) (c : Nat) :
    (sigs : List Sig) → Vals (sigs.map Prod.snd) → Prop
  | [], _ => True
  | (n, _) :: sigs, v => drive c n = some (LVec.ofBitVec v.1) ∧ DrivesAll drive c sigs v.2

end SvGolf.Arch

namespace SvGolf.CombTask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf.Arch

variable (t : CombTask)

/-- **v1's conjunct 3 over `Obs_run2`, v1's input convention**: every cycle whose stimulus entry binds
each input port to a known value ends with a post sample whose output ports hold `t.fn N` of those
values. -/
def Computes_stim (N : Nat) (d : Design2) : Prop :=
  ∀ σ stim b, Obs_run2.Behaves d σ stim b →
    ∀ (c : Nat) (o : CycleObs PortSample), b[c]? = some o →
      ∀ v, DrivesAll (stimDrive stim) c (t.inputs N) v → HoldAllS o.post (t.outputs N) (t.fn N v)

def SatisfiedAt_stim (N : Nat) (d : Design2) : Prop :=
  t.InterfaceObs Obs_run2 N d ∧ (Unclocked d ∧ Obs_run2.Progress {} d) ∧ t.Computes_stim N d

def Statement_stim (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAt_stim N (sem N)

/-- The `_stim` statement restricted to the parameter values the declared type can hold (`ty`;
`IntParam` for `parameter int N`), as the Task v2 skeleton does. -/
def Statement_stim_bounded (ty : Nat → Prop) (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → ty N → t.SatisfiedAt_stim N (sem N)

end SvGolf.CombTask

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe SvGolf

/-! ## The `_stim` variant is v1 -/

/-- `stimDrive` reads entry `c` as `HoldAll` does. -/
theorem drivesAll_stimDrive {stim : List SvState} {c : Nat} {e : SvState}
    (he : stim[c]? = some e) :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)),
      DrivesAll (stimDrive stim) c sigs v ↔ HoldAll e sigs v
  | [], _ => Iff.rfl
  | (n, w) :: sigs, v => by
      have hd : stimDrive stim c n = SvState.lookup e n := by simp [stimDrive, he]
      simp only [DrivesAll, HoldAll, hd, drivesAll_stimDrive he sigs v.2]

/-- On ports, the trusted sample of a `run2` state reads as `HoldAll` reads the state. -/
theorem holdAllS_sample {d : Design2} {st : SvState} :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)),
      (∀ p ∈ sigs, p.1 ∈ (Obs_run2.iface d).names) →
      (HoldAllS (Obs_run2.sample d st) sigs v ↔ HoldAll st sigs v)
  | [], _, _ => Iff.rfl
  | (n, w) :: sigs, v, h => by
      have hn : n ∈ (Obs_run2.iface d).names := h (n, w) (by simp)
      have ih := holdAllS_sample (d := d) (st := st) sigs v.2 fun p hp => h p (by simp [hp])
      simp only [HoldAllS, HoldAll, Obs_run2.read_sample hn, ih]

/-- A trusted `Obs_run2` behaviour, opened at cycle `c`: the proof observation behind the trusted
one. -/
theorem obs_run2_cycle {d : Design2} {r : List (CycleObs SvState)} {c : Nat}
    {o : CycleObs PortSample}
    (hc : (r.map (CycleObs.map (Obs_run2.sample d)))[c]? = some o) :
    ∃ o', r[c]? = some o' ∧ o = o'.map (Obs_run2.sample d) := by
  rw [List.getElem?_map] at hc
  cases hrc : r[c]? with
  | none => rw [hrc] at hc; cases hc
  | some o' =>
      rw [hrc] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact ⟨o', rfl, hc.symm⟩

/-- **`Computes ↔ Computes_stim`**, whenever the task's output names are ports of the design. -/
theorem computes_stim_iff {t : CombTask} {N : Nat} {d : Design2}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hout : ∀ p ∈ t.outputs N, p.1 ∈ (Obs_run2.iface d).names) :
    t.Computes N d ↔ t.Computes_stim N d := by
  constructor
  · intro h σ stim b hb c o hc v hv
    obtain ⟨r, hr, rfl⟩ := hb
    obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle hc
    have hruns := Obs_run2.runs2_of_runs hnq hr
    have htr : (r.map CycleObs.post)[c]? = some o'.post := by simp [hrc]
    have hlt : c < stim.length := by
      rw [← hruns.length]
      exact (List.getElem?_eq_some_iff.mp htr).1
    obtain ⟨e, he⟩ : ∃ e, stim[c]? = some e := ⟨stim[c], List.getElem?_eq_getElem hlt⟩
    have hv' := (drivesAll_stimDrive he _ v).mp hv
    exact (holdAllS_sample _ _ hout).mpr (h σ stim _ hruns c e o'.post he htr v hv')
  · intro h σ stim tr htr c e st he hst v hv
    obtain ⟨r, hr, rfl⟩ := Obs_run2.runs_of_runs2 htr
    rw [List.getElem?_map] at hst
    cases hrc : r[c]? with
    | none => rw [hrc] at hst; cases hst
    | some o' =>
        rw [hrc] at hst
        simp only [Option.map_some, Option.some.injEq] at hst
        subst hst
        have := h σ stim (r.map (CycleObs.map (Obs_run2.sample d))) ⟨r, hr, rfl⟩ c
          (o'.map (Obs_run2.sample d)) (by simp [hrc]) v ((drivesAll_stimDrive he _ v).mpr hv)
        exact (holdAllS_sample _ _ hout).mp this

/-- `InterfaceObs` over `Obs_run2` is v1's `Interface` (the same port lists, by definition). -/
theorem interfaceObs_iff {t : CombTask} {N : Nat} {d : Design2} :
    t.InterfaceObs Obs_run2 N d ↔ t.Interface N d :=
  Iff.rfl

/-- The output names of a `Design2` are ports of its `Obs_run2` interface. -/
theorem mem_names_of_outputs {d : Design2} {p : Sig} (hp : p ∈ outputSigs d) :
    p.1 ∈ (Obs_run2.iface d).names := by
  simp only [Iface.names, List.mem_append, List.mem_map]
  exact Or.inr ⟨p, hp, rfl⟩

/-- The input names of a `Design2` are ports of its `Obs_run2` interface. -/
theorem mem_names_of_inputs {d : Design2} {p : Sig} (hp : p ∈ inputSigs d) :
    p.1 ∈ (Obs_run2.iface d).names := by
  simp only [Iface.names, List.mem_append, List.mem_map]
  exact Or.inl ⟨p, hp, rfl⟩

/-- Under `Interface`, every task output is a port. -/
theorem outputs_mem_of_interface {t : CombTask} {N : Nat} {d : Design2} (h : t.Interface N d) :
    ∀ p ∈ t.outputs N, p.1 ∈ (Obs_run2.iface d).names := by
  intro p hp
  have : outputSigs d = t.outputs N := h.2
  exact mem_names_of_outputs (this ▸ hp)

/-- **v1's `SatisfiedAt` is exactly the `_stim` variant over `Obs_run2`**, for a design with no
qualified `case`. -/
theorem satisfiedAt_stim_iff {t : CombTask} {N : Nat} {d : Design2}
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false) :
    t.SatisfiedAt N d ↔ t.SatisfiedAt_stim N d := by
  constructor
  · rintro ⟨hI, ⟨hU, hT⟩, hC⟩
    exact ⟨hI, ⟨hU, Obs_run2.progress_of_terminates {} d hT⟩,
      (computes_stim_iff hnq (outputs_mem_of_interface hI)).mp hC⟩
  · rintro ⟨hI, ⟨hU, hP⟩, hC⟩
    exact ⟨hI, ⟨hU, (Obs_run2.progress_iff {} d hnq).mp hP⟩,
      (computes_stim_iff hnq (outputs_mem_of_interface hI)).mpr hC⟩

/-- **Every v1 `CombTask.Statement` is the `_stim` variant over `Obs_run2`**, so every record
stands. -/
theorem statement_stim_iff {t : CombTask} {sem : Nat → Design2}
    (hnq : ∀ N, t.inRange N → (sem N).processes.toList.any Process2.hasQualifiedCase = false) :
    t.Statement sem ↔ t.Statement_stim sem :=
  forall_congr' fun N => imp_congr_right fun hr => satisfiedAt_stim_iff (hnq N hr)

/-- **v1 implies the bounded statement**, for any declared type's range: the bound only removes
parameter values, so every v1 record keeps holding. -/
theorem statement_stim_bounded {t : CombTask} {sem : Nat → Design2} (ty : Nat → Prop)
    (hnq : ∀ N, t.inRange N → (sem N).processes.toList.any Process2.hasQualifiedCase = false)
    (h : t.Statement sem) : t.Statement_stim_bounded ty sem :=
  fun N hr _ => (satisfiedAt_stim_iff (hnq N hr)).mp (h N hr)

/-! ## The cost of the pre-sample convention over `run2` -/

/-- **`EntryInPre sigs d`**: in every completed run of `d`, the pre sample of each cycle holds every
port of `sigs` that the cycle's stimulus entry binds at a known value. It fails exactly when a comb
or reset process of `d` overwrites an input name before the edge. -/
def EntryInPre (sigs : List Sig) (d : Design2) : Prop :=
  ∀ σ stim r, Obs_run2.Runs d σ stim r →
    ∀ (c : Nat) (e : SvState) (o : CycleObs SvState), stim[c]? = some e → r[c]? = some o →
    ∀ p ∈ sigs, ∀ x : BitVec p.2, SvState.lookup e p.1 = some (LVec.ofBitVec x) →
      SvState.lookup o.pre p.1 = some (LVec.ofBitVec x)

theorem holdAll_of_entry {e pre : SvState} :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)),
      (∀ p ∈ sigs, ∀ x : BitVec p.2, SvState.lookup e p.1 = some (LVec.ofBitVec x) →
        SvState.lookup pre p.1 = some (LVec.ofBitVec x)) →
      HoldAll e sigs v → HoldAll pre sigs v
  | [], _, _, _ => trivial
  | (n, w) :: sigs, v, h, ⟨h1, h2⟩ =>
      ⟨h (n, w) (by simp) v.1 h1,
        holdAll_of_entry sigs v.2 (fun p hp => h p (by simp [hp])) h2⟩

/-- **Pre convention ⇒ v1** over `run2`, under `EntryInPre`: one lemma. The converse (the direction
records need) is costed in the module docstring and not proved. -/
theorem computes_of_computes_obs {t : CombTask} {N : Nat} {d : Design2}
    (hin : EntryInPre (t.inputs N) d) (hinp : ∀ p ∈ t.inputs N, p.1 ∈ (Obs_run2.iface d).names)
    (hout : ∀ p ∈ t.outputs N, p.1 ∈ (Obs_run2.iface d).names)
    (h : t.Computes_obs Obs_run2 N d) : t.Computes N d := by
  intro σ stim tr htr c e st he hst v hv
  obtain ⟨r, hr, rfl⟩ := Obs_run2.runs_of_runs2 htr
  rw [List.getElem?_map] at hst
  cases hrc : r[c]? with
  | none => rw [hrc] at hst; cases hst
  | some o' =>
      rw [hrc] at hst
      simp only [Option.map_some, Option.some.injEq] at hst
      subst hst
      have hpre : HoldAll o'.pre (t.inputs N) v :=
        holdAll_of_entry _ v (hin σ stim r hr c e o' he hrc) hv
      have := h σ stim (r.map (CycleObs.map (Obs_run2.sample d))) trivial ⟨r, hr, rfl⟩ c
        (o'.map (Obs_run2.sample d)) (by simp [hrc]) v ((holdAllS_sample _ _ hinp).mpr hpre)
      exact (holdAllS_sample _ _ hout).mp this

/-! ## Receptiveness and `EntryInPre` from the syntactic check -/

/-- An input name is a port of the `Obs_run2` interface. -/
theorem mem_names_of_inputName {d : Design2} {n : String} (hn : n ∈ d.inputNames.toList) :
    n ∈ (Obs_run2.iface d).names := by
  obtain ⟨dc, hdc, hin, rfl⟩ : ∃ dc ∈ d.decls.toList, dc.isInput = true ∧ dc.name = n := by
    simpa [Design2.inputNames] using hn
  exact mem_names_of_inputs (p := (dc.name, dc.width))
    (List.mem_filterMap.mpr ⟨dc, hdc, by simp [hin]⟩)

/-- **`EntryInPre` from the syntactic check**: in a design that writes no input port, the pre sample
holds every input the stimulus entry binds at a known value. -/
theorem entryInPre_of_writesInput {d : Design2} {sigs : List Sig} (hd : d.writesInput = false)
    (hs : ∀ p ∈ sigs, p.1 ∈ d.inputNames.toList) : EntryInPre sigs d :=
  fun _ _ _ hr _ _ _ he ho p hp _ hx => Obs_run2.pre_input hd hr he ho (hs p hp) hx

/-- **Receptiveness for free** (library theorem). A terminating design that writes no input port is
`Receptive` over `Obs_run2` on any list of distinct input ports, for every clocking: the stimulus
that binds each entry of `s` shows it in the pre samples. -/
theorem receptive_of_writesInput {d : Design2} {k : Clocking} {free : List Sig}
    (hd : d.writesInput = false) (hT : Terminates2 d)
    (hfree : ∀ p ∈ free, p.1 ∈ d.inputNames.toList) (hnd : (free.map Prod.fst).Nodup) :
    Receptive Obs_run2 k d free := by
  intro σ s
  obtain ⟨tr, htr⟩ := hT σ (s.map (entryOf free))
  obtain ⟨r, hr, rfl⟩ := Obs_run2.runs_of_runs2 htr
  refine ⟨s.map (entryOf free), r.map (CycleObs.map (Obs_run2.sample d)), trivial, ⟨r, hr, rfl⟩,
    ?_, ?_⟩
  · obtain ⟨fuel, hrun⟩ := hr
    simp [runObs2_length hrun]
  · intro c o v hc hv
    obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle hc
    have he : (s.map (entryOf free))[c]? = some (entryOf free v) := by simp [hv]
    have hpre : HoldAll o'.pre free v :=
      holdAll_of_entry free v (fun p hp _ hx => Obs_run2.pre_input hd hr he hrc (hfree p hp) hx)
        (holdAll_entryOf free hnd v)
    exact (holdAllS_sample free v fun p hp => mem_names_of_inputName (hfree p hp)).mpr hpre

/-- `computes_of_computes_obs` with its semantic hypothesis discharged by the syntactic check. -/
theorem computes_of_computes_obs' {t : CombTask} {N : Nat} {d : Design2}
    (hd : d.writesInput = false) (hI : t.Interface N d) (h : t.Computes_obs Obs_run2 N d) :
    t.Computes N d := by
  have hin : ∀ p ∈ t.inputs N, p.1 ∈ d.inputNames.toList := by
    intro p hp
    have h1 : inputSigs d = t.inputs N := hI.1
    rw [← h1] at hp
    obtain ⟨dc, hdc, hp⟩ := List.mem_filterMap.mp hp
    by_cases hin : dc.isInput = true
    · simp only [hin, if_true, Option.some.injEq] at hp
      subst hp
      simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap]
      exact ⟨dc, by simpa using hdc, by simp [hin]⟩
    · simp [hin] at hp
  exact computes_of_computes_obs (entryInPre_of_writesInput hd hin)
    (fun p hp => mem_names_of_inputName (hin p hp)) (outputs_mem_of_interface hI) h

#print axioms mem_names_of_inputName
#print axioms entryInPre_of_writesInput
#print axioms receptive_of_writesInput
#print axioms computes_of_computes_obs'
#print axioms drivesAll_stimDrive
#print axioms holdAllS_sample
#print axioms obs_run2_cycle
#print axioms computes_stim_iff
#print axioms interfaceObs_iff
#print axioms mem_names_of_outputs
#print axioms mem_names_of_inputs
#print axioms outputs_mem_of_interface
#print axioms satisfiedAt_stim_iff
#print axioms statement_stim_iff
#print axioms statement_stim_bounded
#print axioms holdAll_of_entry
#print axioms computes_of_computes_obs

end SvGolf.Arch
