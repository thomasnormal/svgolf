import LoopTask
import ObsCombE
import LeanModels.Sv.Loop2Slot

/-!
# A loop design's task statement over E-core-0 (WS3) — *derived from E*, untrusted

`CombTask.satisfiedAt_obs_of_frag`: a design whose only process is one `always_comb` of the
`initLoop` shape, its trips in the fragment and in range, satisfies the task at `N` over the
authority's backend `Obs_E0` (A's `Core0Obs.lean`), in the Task v2 convention (`SatisfiedAt_obs`,
P's `TaskV2.lean`), for its E elaboration `Elab.ofDesign2 d`. The chain is E's only:

* the body's activation, `Stmt2.frag_denE` (the seam primitives over `Kernel.execBody`);
* the slots, `SingleE` (`Loop2Slot.lean`): every slot of every behaviour closes settled, every
  choice and environment has a behaviour, the sample slot repeats the edge slot;
* the samples: the pre sample is the edge slot's closed store (inputs the entry's, A's
  `Elab.lookup_view_applyInputs_input`), the post sample the same store.

What is left is `hout`, the per-state correctness of the body's meaning (the design's arithmetic, no
backend). Every other hypothesis is a structural fact of the design, decided at a symbolic bound.

Not trusted text; compiled by `compile-loop.sh` (with A's and P's `ObsCombE`, `ObsComb`, `TaskV2`,
`SeqTask`, unchanged, in the scratch copy).
-/

namespace SvGolf.Design.Loop

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Kernel LeanModels.Sv.Observe SvGolf SvGolf.Arch

/-- A typed store's view meets the loop invariant. -/
theorem loopInv_view {d : Design2} {E : Kernel.Elab} (hd : E.decls = d.decls)
    (hnd : (d.decls.toList.map (·.name)).Nodup) {σ : Kernel.Store} (hT : E.Typed σ) :
    LoopInv d (E.view σ) := by
  have hw : ∀ dc ∈ d.decls.toList, E.toDesign2.declWidth dc.name = some dc.width := fun dc hdc => by
    simp only [Design2.declWidth, Kernel.Elab.toDesign2, hd]
    cases hf : d.decls.toList.find? (fun x => x.name == dc.name) with
    | none => exact absurd (List.find?_eq_none.mp hf dc hdc) (by simp)
    | some dc' =>
        rw [decl_eq_of_name hnd (List.mem_of_find?_eq_some hf) hdc (by simpa using List.find?_some hf)]
        rfl
  refine ⟨fun x hx => ?_, fun dc hdc _ => ?_⟩
  · obtain ⟨dc, hdc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨old, hold, -⟩ := Kernel.Elab.lookup_declared hT (hw dc hdc)
    exact ⟨old, hold⟩
  · obtain ⟨old, hold, hw'⟩ := Kernel.Elab.lookup_declared hT (hw dc hdc)
    simp [sig, hold, hw']

/-- **A fragment `initLoop` as the single process is a `SingleE`**, from structural facts only. -/
theorem singleE_frag {d : Design2} {n : String} {c : LVec} {Nl W : Nat} {T : Nat → Stmt2}
    (hp : d.processes = #[.alwaysComb (initLoop n c Nl T)]) (h4 : AllFour (Elab.ofDesign2 d))
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hn : n ∈ d.decls.toList.map (·.name))
    (hW : d.declWidth n = some W) (hnin : n ∉ d.inputNames.toList)
    (hfr : (initLoop n c Nl T).fragOk n (fun lo w => decide (lo + w ≤ W))
      (fun x => decide (x ∈ d.decls.toList.map (·.name))) = true) :
    SingleE (Elab.ofDesign2 d) (initLoop n c Nl T) (BoundAll (d.decls.toList.map (·.name)))
      (initLoop.meaning n c Nl T) [n] := by
  have hE : (Elab.ofDesign2 d).toDesign2 = d := Elab.toDesign2_ofDesign2 fun p hp' => by
    rw [hp] at hp'; simp only [List.mem_singleton] at hp'; subst hp'; rfl
  have hpr : (Elab.ofDesign2 d).procs = #[.comb (initLoop n c Nl T)] := by
    simp [Elab.ofDesign2, hp, Proc0.ofProcess2]
  have hI : ∀ σ, (Elab.ofDesign2 d).Typed σ → BoundAll (d.decls.toList.map (·.name))
      ((Elab.ofDesign2 d).view σ) := fun σ hT => (loopInv_view rfl hnd hT).1
  refine ⟨hpr, Stmt2.frag_denE h4 hn (by rw [hE]; exact hW) _ hfr, hI,
    fun st _ => initLoop_idem n c Nl T st,
    fun st x hx => CombGuard.lookup_set_ne _ _ (by simpa using hx), fun σ entry hT hF hq => ?_⟩
  exact settled_of_quiet (by simp [hpr]) hfr hn (hI σ hT) (hI _ (hT.applyInputs entry))
    (Elab.lookup_view_applyInputs_of_not_input _ _ (by rw [hE]; exact hnin))
    (Elab.not_triggered (by simp [hpr]) hq) hF

/-- `Obs_E0`'s trusted sample, spelled with its port list over the view (definitionally
`Obs_E0.sample E`, `sampleE_eq`): `Obs_E` is not reducible, so the spelled form is what `simp` sees. -/
@[reducible] def sampleE (E : Kernel.Elab) (st : SvState) : PortSample :=
  ⟨(Iface.names ⟨inputSigs E.toDesign2, outputSigs E.toDesign2⟩).filterMap fun n =>
    (SvState.lookup st n).map fun v => (n, v)⟩

theorem sampleE_eq (E : Kernel.Elab) : sampleE E = Obs_E0.sample E := rfl

/-- On ports, the sample reads as `HoldAll` reads the view. -/
theorem holdAllS_sampleE {E : Kernel.Elab} {st : SvState} :
    ∀ (sigs : List Sig) (v : Vals (sigs.map Prod.snd)),
      (∀ p ∈ sigs, p.1 ∈ Iface.names ⟨inputSigs E.toDesign2, outputSigs E.toDesign2⟩) →
      (HoldAllS (sampleE E st) sigs v ↔ HoldAll st sigs v)
  | [], _, _ => Iff.rfl
  | (n, w) :: sigs, v, h => by
      have ih := holdAllS_sampleE (E := E) (st := st) sigs v.2 fun p hp => h p (by simp [hp])
      have hr : (sampleE E st).read n = SvState.lookup st n := by
        simp only [PortSample.read, sampleE]
        rw [lookup_filterMap (SvState.lookup st), if_pos (show n ∈ _ from h (n, w) (by simp))]
      rw [HoldAllS, HoldAll, hr, ih]

/-- **The task at `N` over E-core-0 for a fragment loop body** (derived from E; see the module
docstring). -/
theorem CombTask.satisfiedAt_obs_of_frag {t : CombTask} {N : Nat} {d : Design2} {n : String}
    {c : LVec} {Nl W : Nat} {T : Nat → Stmt2} (hI : t.Interface N d)
    (hp : d.processes = #[.alwaysComb (initLoop n c Nl T)])
    (h4 : ∀ dc ∈ d.decls.toList, dc.twoState = false)
    (hnd : (d.decls.toList.map (·.name)).Nodup) (hn : n ∈ d.decls.toList.map (·.name))
    (hW : d.declWidth n = some W) (hnin : n ∉ d.inputNames.toList)
    (hfr : (initLoop n c Nl T).fragOk n (fun lo w => decide (lo + w ≤ W))
      (fun x => decide (x ∈ d.decls.toList.map (·.name))) = true)
    (hnt : ((t.inputs N).map Prod.fst).Nodup)
    (hout : ∀ st, LoopInv d st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll (initLoop.meaning n c Nl T st) (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt_obs Obs_E0 (fun _ => True) N (Elab.ofDesign2 d) := by
  let E := Elab.ofDesign2 d
  have hE : E.toDesign2 = d := Elab.toDesign2_ofDesign2 fun p hp' => by
    rw [hp] at hp'; simp only [List.mem_singleton] at hp'; subst hp'; rfl
  have hs := singleE_frag hp h4 hnd hn hW hnin hfr
  have hports : ∀ p ∈ t.inputs N ++ t.outputs N,
      p.1 ∈ Iface.names ⟨inputSigs E.toDesign2, outputSigs E.toDesign2⟩ := fun p hp' => by
    simp only [Iface.names, List.mem_append, List.mem_map]
    rcases List.mem_append.mp hp' with h | h
    · exact .inl ⟨p, by rw [hE, show inputSigs d = t.inputs N from hI.1]; exact h, rfl⟩
    · exact .inr ⟨p, by rw [hE, show outputSigs d = t.outputs N from hI.2]; exact h, rfl⟩
  have hin := fun p hp' => hports p (List.mem_append_left (t.outputs N) hp')
  have hout' := fun p hp' => hports p (List.mem_append_right (t.inputs N) hp')
  -- the closed edge slot holds the task's function of its inputs, and the sample slot repeats it
  have hcycle : ∀ {env ch cfg}, Behaves0 E env ch cfg → ∀ c v,
      HoldAll (E.view (cfg (2 * c)).store) (t.inputs N) v →
        HoldAll (E.view (cfg (2 * c + 1)).store) (t.outputs N) (t.fn N v) := by
    intro env ch cfg hb c v hv
    obtain ⟨-, hT, hF⟩ := hs.behaves hb (2 * c)
    rw [hs.post_eq_pre hb c, ← hF]
    exact hout _ (loopInv_view rfl hnd hT) v hv
  refine ⟨?_, ⟨trivial, ?_, ?_⟩, ?_⟩
  · show inputSigs E.toDesign2 = t.inputs N ∧ outputSigs E.toDesign2 = t.outputs N
    rw [hE]; exact hI
  · intro ch env _
    exact ⟨_, _, ⟨fun t => E.view (runCfg E ch env t).store,
      ⟨runCfg E ch env, hs.exists_behaves ch env, fun _ => rfl⟩, rfl⟩, rfl⟩
  · intro ch s
    let env := s.map (entryOf (t.inputs N))
    let cfg := runCfg E ch env
    have hb0 : Behaves0 E env ch cfg := hs.exists_behaves ch env
    let r : List (CycleObs SvState) := (List.range env.length).map fun c =>
      ⟨E.view (cfg (2 * c)).store, E.view (cfg (2 * c + 1)).store⟩
    refine ⟨env, r.map (CycleObs.map (sampleE E)), trivial,
      ⟨r, ⟨fun t => E.view (cfg t).store, ⟨cfg, hb0, fun _ => rfl⟩, ?_⟩, rfl⟩, by simp [r, env], ?_⟩
    · apply List.map_congr_left
      intro c _
      show _ = (⟨E.view (cfg (2 * c + 1 - 1)).store, E.view (cfg (2 * c + 1)).store⟩ :
        CycleObs SvState)
      rw [Nat.add_sub_cancel]
    intro c o v hc hv
    have hcs : c < s.length := (List.getElem?_eq_some_iff.mp hv).1
    simp only [r, env, List.getElem?_map, List.getElem?_range, List.length_map, hcs, if_true,
      Option.map_some, Option.some.injEq] at hc
    subst hc
    refine (holdAllS_sampleE (t.inputs N) v hin).mpr ?_
    obtain ⟨σ, hT, hpre⟩ := hs.pre_view hb0 (2 * c)
    have hse : slotEntry env (2 * c) = entryOf (t.inputs N) v := by
      simp [slotEntry, env, hv]
    refine holdAll_of_entry (t.inputs N) v (fun p hp' x hx => ?_) (holdAll_entryOf _ hnt v)
    have hpn : p.1 ∈ d.inputNames.toList :=
      mem_inputNames_of_inputSigs (by rw [show inputSigs d = t.inputs N from hI.1]; exact hp')
    have hne : p.1 ≠ n := fun h => hnin (h ▸ hpn)
    rw [hpre, hs.frame _ p.1 (by simpa using hne), hse]
    refine Elab.lookup_view_applyInputs_input (E := E) hnd h4 hT (by rw [hE]; exact hpn) hx ?_
    rw [hE, width_ofBitVec]
    exact declWidth_of_inputSigs hnd (by rw [show inputSigs d = t.inputs N from hI.1]; exact hp')
  · intro ch env b _ hb c o hc v hv
    obtain ⟨r, ⟨bb, ⟨cfg, hb0, hbb⟩, rfl⟩, rfl⟩ := hb
    change (((List.range env.length).map fun c =>
      (⟨bb (2 * c + 1 - 1), bb (2 * c + 1)⟩ : CycleObs SvState)).map (CycleObs.map (sampleE E)))[c]?
        = some o at hc
    rcases Nat.lt_or_ge c env.length with hcl | hcl
    · simp only [List.getElem?_map, List.getElem?_range hcl, Option.map_some, Option.some.injEq] at hc
      subst hc
      change HoldAllS (sampleE E (bb (2 * c + 1 - 1))) (t.inputs N) v at hv
      show HoldAllS (sampleE E (bb (2 * c + 1))) (t.outputs N) (t.fn N v)
      rw [Nat.add_sub_cancel, hbb] at hv
      rw [hbb]
      exact (holdAllS_sampleE _ _ hout').mpr (hcycle hb0 c v ((holdAllS_sampleE _ _ hin).mp hv))
    · simp [hcl] at hc

end SvGolf.Design.Loop

#pin_axioms SvGolf.Design.Loop.loopInv_view SvGolf.Design.Loop.singleE_frag
  SvGolf.Design.Loop.sampleE_eq SvGolf.Design.Loop.holdAllS_sampleE
  SvGolf.Design.Loop.CombTask.satisfiedAt_obs_of_frag
