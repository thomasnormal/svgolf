import ObsComb
import LeanModels.Sv.Kernel.Core0Obs

/-!
# `CombTask` transported to E-core-0 (R-DESIGN2, comb slice): a **transport theorem**

Not in any lake library and imported by nothing trusted. Compile with `compile-obsE.sh` (after
`lake build LeanModels.Sv.Kernel.Core0Obs LeanModels.Sv.ObserveFrame LeanModels.Sv.Hier2` at the
repository root).

**What it says.** A v1 `CombTask` record (`t.Statement sem`, proved over `run2`) gives the task's
statement over the authority's backend E-core-0, in the trusted convention of the Task v2 draft
(`Statement_obs`, inputs read from the pre sample, `TaskV2.lean`), for the E elaboration of the
same designs (`Elab.ofDesign2`), whenever each design is in the R-COMB fragment:

* `CombDesign (sem N)`: one driver per bit, every process an assign (debt D-X1a);
* `Acyclic (sem N)`: the rank certificate;
* every declaration 4-state, every initializer at its declared width (`InitTyped`).

The v1 statement does NOT contain these: they are the hypotheses the transfer needs and the
statement does not expose. Every accepted `add` and `_example` record proves the first two as named
lemmas (`band_comb`/`band_acyclic`, `ripple_comb`/`ripple_acyclic`), and the last two are
syntactic facts about the loaded declarations.

**How.** The three conjuncts of `SatisfiedAt_obs` over `Obs_E0`:

1. interface: the same port lists (E's corresponding Design2 is the design itself);
2. progress (`progress_E0`: every slot closes, R-COMB-0) and receptiveness (`pre_input`: the pre
   sample holds what the entry binds); admission is empty under E;
3. function: every E behaviour is a `run2` behaviour under the stimulus that re-drives every input to
   its pre-sample value (`runObs2_of_runs_E0`, the strong form of `included_E0_run2`), so v1's
   conjunct 3 (stimulus convention) applies to it, and its known inputs are exactly those of the
   pre sample. This is `Safe.of_included` with the environment made explicit: the plain inclusion
   forgets which stimulus reproduces the behaviour, and v1 needs it.
-/

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Sv.Kernel SvGolf

/-- A port of `inputSigs d` is an input name. -/
theorem mem_inputNames_of_inputSigs {d : Design2} {p : Sig} (hp : p ∈ inputSigs d) :
    p.1 ∈ d.inputNames.toList := by
  obtain ⟨dc, hdc, hp⟩ := List.mem_filterMap.mp hp
  cases hin : dc.isInput with
  | false => simp [hin] at hp
  | true =>
      simp only [hin, if_true, Option.some.injEq] at hp
      subst hp
      simp only [Design2.inputNames, Array.toList_filterMap, List.mem_filterMap]
      exact ⟨dc, by simpa using hdc, by simp [hin]⟩

/-- With distinct declaration names, a port of `inputSigs d` has its declared width. -/
theorem declWidth_of_inputSigs {d : Design2} (hnd : (d.decls.toList.map Decl.name).Nodup)
    {p : Sig} (hp : p ∈ inputSigs d) : d.declWidth p.1 = some p.2 := by
  obtain ⟨dc, hdc, hp⟩ := List.mem_filterMap.mp hp
  cases hin : dc.isInput with
  | false => simp [hin] at hp
  | true =>
      simp only [hin, if_true, Option.some.injEq] at hp
      subst hp
      exact Design2.declWidth_of_mem hnd hdc

/-- Re-driving the inputs of `st` keeps every known input value. -/
theorem holdAll_inputsOf {d : Design2} {st : SvState} :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)),
      (∀ p ∈ sigs, p.1 ∈ d.inputNames.toList) → HoldAll st sigs v → HoldAll (inputsOf d st) sigs v
  | [], _, _, _ => trivial
  | (n, w) :: sigs, v, hs, ⟨h1, h2⟩ => by
      refine ⟨?_, holdAll_inputsOf sigs v.2 (fun p hp => hs p (by simp [hp])) h2⟩
      rw [lookup_inputsOf, if_pos (hs (n, w) (by simp))]
      exact h1

theorem width_ofBitVec {w : Nat} (x : BitVec w) : (LVec.ofBitVec x).width = w := by
  simp [LVec.ofBitVec, LVec.ofNat, LVec.width]

/-- **v1 at one parameter value ⇒ the task over E-core-0** (transport theorem), for a design in
the R-COMB fragment. -/
theorem satisfiedAt_E0 {t : CombTask} {N : Nat} {d : Design2} (h : t.SatisfiedAt N d)
    (hd : CombDesign d) (ha : Acyclic d) (h4 : ∀ dc ∈ d.decls.toList, dc.twoState = false)
    (hinit : InitTyped d) (hnd : ((t.inputs N).map Prod.fst).Nodup) :
    t.SatisfiedAt_obs Obs_E0 (fun _ => True) N (Elab.ofDesign2 d) := by
  have hE : (Elab.ofDesign2 d).toDesign2 = d := Elab.toDesign2_ofDesign2_of_comb hd
  have hP : Profile0 (Elab.ofDesign2 d) := ⟨by rw [hE]; exact hd, fun dc hdc => h4 dc hdc⟩
  obtain ⟨rank, -, hS⟩ := Settles.ofProfile0' hP (by rw [hE]; exact ha)
  have hinitE : InitTyped (Elab.ofDesign2 d).toDesign2 := by rw [hE]; exact hinit
  obtain ⟨hI, -, hC⟩ := h
  have hin_ports : ∀ p ∈ t.inputs N, p.1 ∈ (Obs_run2.iface d).names := fun p hp =>
    mem_names_of_inputs (p := p) (by rw [show inputSigs d = t.inputs N from hI.1]; exact hp)
  have hin_names : ∀ p ∈ t.inputs N, p.1 ∈ d.inputNames.toList := fun p hp =>
    mem_inputNames_of_inputSigs (by rw [show inputSigs d = t.inputs N from hI.1]; exact hp)
  refine ⟨?_, ⟨trivial, progress_E0 hS {}, ?_⟩, ?_⟩
  · -- the interface: E's corresponding Design2 is `d`
    show inputSigs (Elab.ofDesign2 d).toDesign2 = t.inputs N ∧
      outputSigs (Elab.ofDesign2 d).toDesign2 = t.outputs N
    rw [hE]; exact hI
  · -- receptiveness: the pre sample holds what the entry binds
    intro ch s
    let E := Elab.ofDesign2 d
    let env := s.map (entryOf (t.inputs N))
    let cfg := runCfg E ch env
    have hb0 : Behaves0 E env ch cfg := exists_behaves0 hS ch env
    let r : List (CycleObs SvState) := (List.range env.length).map fun c =>
      ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩
    have hreq : r = (List.range (E0.cycles env)).map fun c =>
        (⟨E0.preponed (fun t => E.view (cfg t).store) (E0.edgeSlot env c),
          (fun t => E.view (cfg t).store) (E0.edgeSlot env c)⟩ : CycleObs SvState) := by
      apply List.map_congr_left
      intro c _
      show _ = (⟨E.view (cfg (2 * c + 1 - 1)).store, E.view (cfg (2 * c + 1)).store⟩ :
        CycleObs SvState)
      rw [Nat.add_sub_cancel]
    refine ⟨env, r.map (CycleObs.map (Obs_run2.sample d)), trivial,
      ⟨r, ⟨fun t => E.view (cfg t).store, ⟨cfg, hb0, fun _ => rfl⟩, hreq⟩, rfl⟩,
      by simp [r, env], ?_⟩
    intro c o v hc hv
    obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle (d := d) hc
    have hcs : c < s.length := (List.getElem?_eq_some_iff.mp hv).1
    simp only [r, env, List.getElem?_map, List.getElem?_range, List.length_map, hcs,
      Option.map_some, Option.some.injEq] at hrc
    subst hrc
    have he : env[c]? = some (entryOf (t.inputs N) v) := by
      simp [env, hv]
    refine (holdAllS_sample (t.inputs N) v hin_ports).mpr ?_
    refine holdAll_of_entry (t.inputs N) v (fun p hp x hx => ?_) (holdAll_entryOf _ hnd v)
    refine pre_input hS hb0 he (by rw [hE]; exact hin_names p hp) hx ?_
    rw [hE, width_ofBitVec]
    exact declWidth_of_inputSigs hd.nodup (by rw [show inputSigs d = t.inputs N from hI.1]; exact hp)
  · -- the function: every E behaviour is a `run2` behaviour that re-drives the pre-sample inputs
    intro ch env b _ hb c o hc v hv
    obtain ⟨r, hr, rfl⟩ := hb
    have hrun := runObs2_of_runs_E0 hS hinitE hr ch
    rw [hE] at hrun
    have hruns : Runs2 d ch (r.map fun o => inputsOf d o.pre) (r.map CycleObs.post) :=
      ⟨_, (run2_ok_iff (CombDesign.noQualified hd)).mpr ⟨r, hrun, rfl⟩⟩
    obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle (d := d) hc
    have hrc' : (r : List (CycleObs SvState))[c]? = some o' := hrc
    have hpre : HoldAll o'.pre (t.inputs N) v := (holdAllS_sample (t.inputs N) v hin_ports).mp hv
    have hs1 : (r.map fun o => inputsOf d o.pre)[c]? = some (inputsOf d o'.pre) := by
      rw [List.getElem?_map, hrc']; rfl
    have hs2 : (r.map CycleObs.post)[c]? = some o'.post := by
      rw [List.getElem?_map, hrc']; rfl
    have := hC ch _ _ hruns c (inputsOf d o'.pre) o'.post hs1 hs2 v
      (holdAll_inputsOf (t.inputs N) v hin_names hpre)
    exact (holdAllS_sample _ _ (outputs_mem_of_interface hI)).mpr this

/-- **A v1 `CombTask` record transfers to E-core-0** (transport theorem): from the v1 statement
over `run2` and the R-COMB fragment hypotheses at each parameter value, the task's statement over
E-core-0 in the Task v2 convention, for the E elaboration of the same designs. -/
theorem statement_E0 {t : CombTask} {sem : Nat → Design2} (ty : Nat → Prop) (h : t.Statement sem)
    (hfrag : ∀ N, t.inRange N → ty N →
      CombDesign (sem N) ∧ Acyclic (sem N) ∧ (∀ dc ∈ (sem N).decls.toList, dc.twoState = false) ∧
        InitTyped (sem N))
    (hnd : ∀ N, ((t.inputs N).map Prod.fst).Nodup) :
    t.Statement_obs ty Obs_E0 (fun _ => True) fun N => Elab.ofDesign2 (sem N) := by
  intro N hr hty
  obtain ⟨hd, ha, h4, hinit⟩ := hfrag N hr hty
  exact satisfiedAt_E0 (h N hr) hd ha h4 hinit (hnd N)

#print axioms satisfiedAt_E0
#print axioms statement_E0

end SvGolf.Arch
