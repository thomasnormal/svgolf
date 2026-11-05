import CounterObs
import CounterE
import LeanModels.Sv.Kernel.Core1Obs

/-!
# The counter: E-core-1's behaviours are `run2`'s, off the clock (D-X1h, the Obs-level inclusion)

Not in any lake library and imported by nothing trusted. Compile with `compile-obsE.sh`
(`MODULES="SeqTask CounterCycle TaskV2 ObsComb CounterObs CounterE CounterEObs"`). P's files are
read, not edited.

**Status: transport theorems** (between `Obs_E1`, `LeanModels/Sv/Kernel/Core1Obs.lean`, and
`Obs_run2`). The E side of the slot lemmas (`cnt_low_slot`, `cnt_rise_slot`, `cnt_slots`) is derived
from E; `cnt_included` and `cnt_follows_E1` mention `run2`, so they are not.

`cnt_included`: every behaviour of `cntE N` over `Obs_E1 "clk"` is a behaviour of `cntD N` over
`Obs_run2`, with the clock port hidden (`IncludedOnPorts … ["clk"]`), at every `N`. The `run2`
environment is E's own data inputs before each edge. The clock is hidden because the two backends
show different things there: E drives it (low in the pre sample, high in the post sample), `run2`
keeps the stimulus's value. The statement assumes the clock's observation carries nothing a task
reads (X1-NOTE §12; the TASKV2 decision on the clock port). P's `cntTask` statement reads `rst`
and `en` from the pre samples and `q` from the post samples, never `clk`.

`cnt_follows_E1`: the counter's task statement over `Obs_E1` (progress, and P's `Follows_obs`
moved along `cnt_included`), the first sequential task statement over an E backend (a transport
theorem: its safety conjunct is P's `run2` proof).

The proof: the E side slot by slot (`cnt_low_slot`, `cnt_rise_slot`, from `cnt_low`/`cnt_rise` and
`SlotCloses1.unique`), the `run2` side cycle by cycle (P's `cnt_cycleObs_ok`), then the samples
compared off the clock (`sample_hide_congr`).
-/

namespace SvGolf.Arch.CntE

open LeanModels.Sv LeanModels.Sv.Kernel LeanModels.Sv.Observe SvGolf SvGolf.Seq
  SvGolf.Seq.Counter SvGolf.Arch SvGolf.Arch.Seq

/-- Component `i` of the store (`cntD N`'s declaration order: clk, rst, en, q). -/
def comp (s : Store) (i : Nat) : LVec := (s { decl := i }).bits

theorem cntE_view (N : Nat) (s : Store) :
    (cntE N).base.view s = S (comp s 0) (comp s 1) (comp s 2) (comp s 3) := rfl

/-- The clock reads what the slot's input events drive it to. -/
theorem cntE_clk (N : Nat) {s : Store} (hT : (cntE N).base.Typed s) {entry : SvState} {b : Nat}
    (h : SvState.lookup entry "clk" = some (LVec.ofNat 1 b)) :
    comp ((cntE N).base.applyInputs s entry) 0 = LVec.ofNat 1 b := by
  have hty := hT { decl := 0 } { name := "clk", width := 1, isInput := true } rfl
  simp [comp, Elab.applyInputs, Elab.declOf, Elab1.base, cntE, cntD, h, Val.ofLVec, hty,
    VType.ofDecl, VType.conv, Kernel.LVec.resizeU_of_width]

theorem cntE_width_q (N : Nat) {s : Store} (hT : (cntE N).base.Typed s) : (comp s 3).width = N := by
  have hty := hT { decl := 3 } { name := "q", width := N, isOutput := true } rfl
  rw [comp, Val.width_eq, hty]
  rfl

/-- **A clock-low slot** closes where it opens: typed, clock low, `q` kept. -/
theorem cnt_low_slot (N : Nat) (ch : Choice) {c c' : Config1} (hT : (cntE N).base.Typed c.store)
    (entry : SvState)
    (h : SlotCloses1 (cntE N) ch
      (Config1.nextSlot (cntE N) c (SvState.set entry "clk" (LVec.ofNat 1 0))) c') :
    (cntE N).base.Typed c'.store ∧ SvState.bit0 ((cntE N).base.view c'.store) "clk" = .l0 ∧
      comp c'.store 3 = comp c.store 3 := by
  have hc0 := cntE_clk N hT (SvState.lookup_set_self entry "clk" (LVec.ofNat 1 0))
  have hlow : SvState.bit0 ((cntE N).base.view
      ((cntE N).base.applyInputs c.store (SvState.set entry "clk" (LVec.ofNat 1 0)))) "clk" = .l0 := by
    rw [cntE_view, hc0]; rfl
  obtain rfl := SlotCloses1.unique h (cnt_low N ch c _ hlow)
  exact ⟨hT.applyInputs _, hlow, rfl⟩

/-- **The clock-rise slot** (from `cnt_rise`): typed, `rst`/`en` kept, `q` stepped by `cntNext`. -/
theorem cnt_rise_slot (N : Nat) (ch : Choice) {c c' : Config1} (hT : (cntE N).base.Typed c.store)
    (h0 : SvState.bit0 ((cntE N).base.view c.store) "clk" = .l0)
    (h : SlotCloses1 (cntE N) ch (Config1.nextSlot (cntE N) c [("clk", LVec.ofNat 1 1)]) c') :
    (cntE N).base.Typed c'.store ∧ comp c'.store 1 = comp c.store 1 ∧
      comp c'.store 2 = comp c.store 2 ∧
      comp c'.store 3 = cntNext N (comp c.store 1) (comp c.store 2) (comp c.store 3) := by
  have hT' := hT.applyInputs [("clk", LVec.ofNat 1 1)]
  have h1 : SvState.bit0 ((cntE N).base.view
      ((cntE N).base.applyInputs c.store [("clk", LVec.ofNat 1 1)])) "clk" = .l1 := by
    rw [cntE_view, cntE_clk N hT (b := 1) rfl]; rfl
  have hs : ∀ i, i ≠ 0 → i < 4 →
      comp ((cntE N).base.applyInputs c.store [("clk", LVec.ofNat 1 1)]) i = comp c.store i := by
    intro i h0 h4
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;>
      simp [comp, Elab.applyInputs, Elab.declOf, Elab1.base, cntE, cntD, SvState.lookup]
  obtain ⟨c₁, hcl, hq, hrest⟩ := cnt_rise N ch hT' c.k
    (by rw [cntE_view]; rfl) (by rw [cntE_view]; rfl) (by rw [cntE_view]; rfl) (cntE_width_q N hT')
  have hopen : Config1.nextSlot (cntE N) c [("clk", LVec.ofNat 1 1)] =
      { store := (cntE N).base.applyInputs c.store [("clk", LVec.ofNat 1 1)], active := [0],
        nba := [], k := c.k } := by
    simp only [Config1.nextSlot, cnt_rise_open N h0 h1]
  rw [hopen] at h
  obtain rfl := SlotCloses1.unique h hcl
  have hT₁ := hcl.1.typed hT'
  have hr := hrest "rst" (by decide)
  have he := hrest "en" (by decide)
  generalize (cntE N).base.applyInputs c.store [("clk", LVec.ofNat 1 1)] = s' at hs hq hr he
  simp only [cntE_view, S, SvState.lookup] at hq hr he
  simp at hq hr he
  refine ⟨hT₁, ?_, ?_, ?_⟩
  · rw [hr, hs 1 (by decide) (by decide)]
  · rw [he, hs 2 (by decide) (by decide)]
  · rw [hq, hs 1 (by decide) (by decide), hs 2 (by decide) (by decide), hs 3 (by decide) (by decide)]

theorem slotEntry1_even (env : List SvState) (c : Nat) :
    slotEntry1 "clk" env (2 * c) = SvState.set ((env[c]?).getD []) "clk" (LVec.ofNat 1 0) := by
  simp [slotEntry1]

theorem slotEntry1_odd (env : List SvState) (c : Nat) :
    slotEntry1 "clk" env (2 * c + 1) = [("clk", LVec.ofNat 1 1)] := by
  simp [slotEntry1, Nat.add_mod]

/-- **E's slots, cycle by cycle.** Before every edge the store is typed and the clock low; the edge
keeps `rst`/`en` and steps `q`; the next clock-low slot keeps `q`; slot 0 keeps the start `q`. -/
theorem cnt_slots (N : Nat) {env : List SvState} {ch : Choice} {cfg : Nat → Config1}
    (hB : Behaves1 (cntE N) "clk" env ch cfg) :
    comp (cfg 0).store 3 = comp (cntE N).base.initStore 3 ∧
    ∀ c, (cntE N).base.Typed (cfg (2 * c)).store ∧
      comp (cfg (2 * c + 1)).store 1 = comp (cfg (2 * c)).store 1 ∧
      comp (cfg (2 * c + 1)).store 2 = comp (cfg (2 * c)).store 2 ∧
      comp (cfg (2 * c + 1)).store 3 =
        cntNext N (comp (cfg (2 * c)).store 1) (comp (cfg (2 * c)).store 2)
          (comp (cfg (2 * c)).store 3) ∧
      comp (cfg (2 * c + 2)).store 3 = comp (cfg (2 * c + 1)).store 3 := by
  have h0 := hB.1
  rw [show (0 : Nat) = 2 * 0 from rfl, slotEntry1_even] at h0
  have hlow0 := cnt_low_slot N ch (c := Config1.init (cntE N)) (Elab.typed_initStore _) _ h0
  have step : ∀ c, (cntE N).base.Typed (cfg (2 * c)).store →
      SvState.bit0 ((cntE N).base.view (cfg (2 * c)).store) "clk" = .l0 →
      ((cntE N).base.Typed (cfg (2 * c + 1)).store ∧
        comp (cfg (2 * c + 1)).store 1 = comp (cfg (2 * c)).store 1 ∧
        comp (cfg (2 * c + 1)).store 2 = comp (cfg (2 * c)).store 2 ∧
        comp (cfg (2 * c + 1)).store 3 =
          cntNext N (comp (cfg (2 * c)).store 1) (comp (cfg (2 * c)).store 2)
            (comp (cfg (2 * c)).store 3)) ∧
      ((cntE N).base.Typed (cfg (2 * (c + 1))).store ∧
        SvState.bit0 ((cntE N).base.view (cfg (2 * (c + 1))).store) "clk" = .l0 ∧
        comp (cfg (2 * c + 2)).store 3 = comp (cfg (2 * c + 1)).store 3) := by
    intro c hT hc
    have hr := hB.2 (2 * c)
    rw [slotEntry1_odd] at hr
    have hrise := cnt_rise_slot N ch hT hc hr
    have hl := hB.2 (2 * c + 1)
    rw [show 2 * c + 1 + 1 = 2 * (c + 1) by omega, slotEntry1_even] at hl
    have hlow := cnt_low_slot N ch hrise.1 _ hl
    exact ⟨hrise, hlow.1, hlow.2.1, hlow.2.2⟩
  have hpre : ∀ c, (cntE N).base.Typed (cfg (2 * c)).store ∧
      SvState.bit0 ((cntE N).base.view (cfg (2 * c)).store) "clk" = .l0 := by
    intro c
    induction c with
    | zero => exact ⟨hlow0.1, hlow0.2.1⟩
    | succ c ih => exact ⟨(step c ih.1 ih.2).2.1, (step c ih.1 ih.2).2.2.1⟩
  refine ⟨hlow0.2.2, fun c => ?_⟩
  obtain ⟨⟨-, h1, h2, h3⟩, -, -, h4⟩ := step c (hpre c).1 (hpre c).2
  exact ⟨(hpre c).1, h1, h2, h3, h4⟩

theorem lookup_S_off_clk (a a' r e q : LVec) (n : String) (hn : n ∉ ["clk"]) :
    SvState.lookup (S a r e q) n = SvState.lookup (S a' r e q) n := by
  have : ("clk" == n) = false := by simp at hn ⊢; exact Ne.symm hn
  simp [S, SvState.lookup, this]

/-- **The counter's E-core-1 behaviours are `run2` behaviours off the clock**, at every `N`. -/
theorem cnt_included (N : Nat) :
    IncludedOnPorts (Obs_E1 "clk") Obs_run2 cntTask.clocking (cntE N) (cntD N) ["clk"] := by
  refine ⟨rfl, fun (ch : Choice) (env : List SvState) b₁ _ hb => ?_⟩
  obtain ⟨r₁, ⟨bb, ⟨cfg, hB, hbt⟩, rfl⟩, rfl⟩ := hb
  obtain ⟨hq0, hcyc⟩ := cnt_slots N hB
  -- `run2`'s environment: E's data inputs before each edge
  let R c := comp (cfg (2 * c)).store 1
  let En c := comp (cfg (2 * c)).store 2
  let Q c := comp (cfg (2 * c)).store 3
  let stim : List SvState := (List.range env.length).map fun c => [("rst", R c), ("en", En c)]
  obtain ⟨b₂, r₂, ⟨F, hr⟩, rfl⟩ :=
    Obs_run2.progress_of_terminates cntTask.clocking (cntD N) (cnt_terminates N) ch stim trivial
  refine ⟨ch, stim, _, trivial, ⟨r₂, ⟨F, hr⟩, rfl⟩, ?_⟩
  have hlen : r₂.length = env.length := by
    rw [runObs2_length hr]; simp [stim]
  -- cycle `c` of `run2` reads E's inputs and steps E's `q`
  have hrun : ∀ c o, r₂[c]? = some o → ∃ a,
      o.pre = S a (R c) (En c) (Q c) ∧ o.post = S a (R c) (En c) (cntNext N (R c) (En c) (Q c)) := by
    intro c
    induction c with
    | zero => ?_
    | succ c ih => ?_
    all_goals
      intro o ho
      have hc := (List.getElem?_eq_some_iff.mp ho).1
      rw [hlen] at hc
      obtain ⟨inputs, prev, kc, kc', hin, hprev, hob⟩ := runFromObs2_cycle hr ho
      rw [List.getElem?_map, List.getElem?_range hc, Option.map_some, Option.some.injEq] at hin
      subst hin
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hprev
      subst hprev
      rw [show initState2 (cntD N) = S (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec 1) (LVec.xVec N) by
        simp [initState2, cntD, S]] at hob
      obtain ⟨hpre, hpost⟩ := cnt_cycleObs_ok hob
      have hQ : Q 0 = LVec.xVec N := by
        show comp (cfg 0).store 3 = _
        rw [hq0]
        simp [comp, Elab.initStore, Elab.declOf, Elab1.base, cntE, cntD, Val.ofLVec, VType.ofDecl,
          VType.conv, Kernel.LVec.resizeU_of_width]
      exact ⟨LVec.xVec 1, by rw [hpre, hQ]; simp [appIn, SvState.lookup],
        by rw [hpost, hQ]; simp [appIn, SvState.lookup]⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_map, Option.map_eq_some_iff] at hprev
      obtain ⟨o', ho', rfl⟩ := hprev
      obtain ⟨a, -, hpost'⟩ := ih o' ho'
      obtain ⟨-, -, -, h3, h4⟩ := hcyc c
      have hQ : cntNext N (R c) (En c) (Q c) = Q (c + 1) := by
        show _ = comp (cfg (2 * (c + 1))).store 3
        rw [show 2 * (c + 1) = 2 * c + 2 by omega, h4, h3]
      rw [hpost', hQ] at hob
      obtain ⟨hpre, hpost⟩ := cnt_cycleObs_ok hob
      exact ⟨a, by rw [hpre]; simp [appIn, SvState.lookup],
        by rw [hpost]; simp [appIn, SvState.lookup]⟩
  -- the samples agree off the clock (E's trusted sample of `cntE N` is `run2`'s of `cntD N`)
  show hideB ["clk"] (((List.range env.length).map fun c =>
      (⟨bb (2 * c + 1 - 1), bb (2 * c + 1)⟩ : CycleObs SvState)).map
        (CycleObs.map (Obs_run2.sample (cntD N)))) =
    hideB ["clk"] (r₂.map (CycleObs.map (Obs_run2.sample (cntD N))))
  apply List.ext_getElem?
  intro c
  simp only [hideB, List.getElem?_map]
  by_cases hc : c < env.length
  · obtain ⟨o, ho⟩ : ∃ o, r₂[c]? = some o := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨a, hpre, hpost⟩ := hrun c o ho
    obtain ⟨-, h1, h2, h3, -⟩ := hcyc c
    rw [ho, List.getElem?_range hc]
    simp only [Option.map_some, Option.some.injEq, CycleObs.map, Nat.add_sub_cancel, hbt,
      cntE_view, hpre, hpost, CycleObs.mk.injEq]
    rw [h3, h1, h2]
    exact ⟨sample_hide_congr rfl (lookup_S_off_clk _ _ _ _ _),
      sample_hide_congr rfl (lookup_S_off_clk _ _ _ _ _)⟩
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

/-! ## The counter's task statement over `Obs_E1` (transport) -/

/-- One cycle of two behaviours equal off the hidden ports. -/
theorem hideB_get {xs : List String} {b b' : List (CycleObs PortSample)}
    (h : hideB xs b = hideB xs b') {i : Nat} {o : CycleObs PortSample} (ho : b[i]? = some o) :
    ∃ o', b'[i]? = some o' ∧ hidePorts xs o.pre = hidePorts xs o'.pre ∧
      hidePorts xs o.post = hidePorts xs o'.post := by
  have := congrArg (·[i]?) h
  simp only [hideB, List.getElem?_map, ho] at this
  cases ho' : b'[i]? with
  | none => rw [ho'] at this; cases this
  | some o' =>
      rw [ho'] at this
      simp only [Option.map_some, Option.some.injEq, CycleObs.map, CycleObs.mk.injEq] at this
      exact ⟨o', rfl, this⟩

/-- `cntTask` reads no clock: `Holds` and `ObsOKS` ignore a hidden `clk`. -/
theorem cnt_holds_hide (N : Nat) (s : PortSample) (p : Bool × cntTask.Ins N) :
    cntTask.Holds N (hidePorts ["clk"] s) p ↔ cntTask.Holds N s p := by
  simp [SeqTask.Holds, SeqTask.RstHolds, cntTask, HoldAllS, read_hidePorts]

theorem cnt_obsOK_hide (N : Nat) (s : PortSample) (a : cntTask.State N × cntTask.Ins N) :
    cntTask.ObsOKS N (hidePorts ["clk"] s) a ↔ cntTask.ObsOKS N s a := by
  simp [SeqTask.ObsOKS, cntTask, HoldAllS, read_hidePorts]

theorem cnt_followsB_hide (N : Nat) {b b' : List (CycleObs PortSample)}
    (h : hideB ["clk"] b = hideB ["clk"] b') (hf : cntTask.FollowsB N b') :
    cntTask.FollowsB N b := by
  intro c0 ps hst hdrv j a hscan
  obtain ⟨o', ho', hok⟩ := hf c0 ps hst (fun j p hp => by
    obtain ⟨o, ho, hh⟩ := hdrv j p hp
    obtain ⟨o', ho', hpre, -⟩ := hideB_get h ho
    refine ⟨o', ho', (cnt_holds_hide N o'.pre p).mp ?_⟩
    rw [← hpre]; exact (cnt_holds_hide N o.pre p).mpr hh) j a hscan
  obtain ⟨o, ho, -, hpost⟩ := hideB_get h.symm ho'
  refine ⟨o, ho, (cnt_obsOK_hide N o.post a).mp ?_⟩
  rw [← hpost]; exact (cnt_obsOK_hide N o'.post a).mpr hok

/-- **The counter's task statement over `Obs_E1`** (a transport theorem: the safety and progress conjuncts of
`SatisfiedAt_obs` over `Obs_E1 "clk"`, at every `N`): every disciplined E-core-1 behaviour of
`cntE N` follows the spec counter, P's `cnt_satisfiedAt_obs` moved along `cnt_included`. -/
theorem cnt_follows_E1 (N : Nat) :
    (Obs_E1 "clk").Progress cntTask.clocking (cntE N) ∧
      cntTask.Follows_obs (Obs_E1 "clk") N (cntE N) :=
  ⟨progress_E1 (cntE_profile N) "clk" cntTask.clocking,
    Safe.of_includedOnPorts (Q := fun _ b => cntTask.FollowsB N b) (cnt_included N)
      (fun _ _ _ h hf => cnt_followsB_hide N h hf) (cnt_satisfiedAt_obs N).2.2⟩

#print axioms cnt_low_slot
#print axioms cnt_rise_slot
#print axioms cnt_slots
#print axioms cnt_included
#print axioms cnt_followsB_hide
#print axioms cnt_follows_E1

end SvGolf.Arch.CntE
