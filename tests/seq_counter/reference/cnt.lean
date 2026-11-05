import Submission.Design
import SvGolf.Seq
import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# The counter fixture's proof (`tests/seq_counter`, check.py kind `seq-family`)

The positive case of the clocked checker (PLAN4 Gate 2): `Submission.Goal` is
`SvGolf.Tests.SeqCounter.Statement design.sem` for `design` loaded from
`tests/seq_counter/reference/cnt.sv`. A one-file port of the design study's counter proof
(`design/sequential/CounterCycle.lean`, `CounterInst.lean`) to the frozen trusted `SeqTask`
(`SvGolf/TaskSeq.lean`) and its reduction theorem `SeqTask.satisfiedAt_of_cycle`
(`SvGolf/Seq.lean`): the hand-built family `cntD`, its one-cycle closed form, the register
algebra, the reset and step cycles, and the instantiation `design.sem N = cntD N` at symbolic `N`.
-/

namespace Submission

open LeanModels.Sv SvGolf

abbrev cntTask : SeqTask := SvGolf.Tests.SeqCounter.task

/-! ## 1. The instantiated design, by hand -/

def cntD (N : Nat) : Design2 where
  name := "cnt"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "rst", width := 1, isInput := true },
             { name := "en", width := 1, isInput := true },
             { name := "q", width := N, isOutput := true }]
  processes := #[.alwaysFF "clk"
    (.ifStmt (.ident "rst")
      (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
      (some (.ifStmt (.ident "en")
        (.nbaAssign (.ident "q")
          (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
        none)))]

/-! ## 2. One cycle, in closed form -/

def S (c r e q : LVec) : SvState := [("clk", c), ("rst", r), ("en", e), ("q", q)]

def cntNext (N : Nat) (r e q : LVec) : LVec :=
  if r.condTrue then q.insertAt 0 ((LVec.replicate N .l0).resizeU q.width)
  else if e.condTrue then
    q.insertAt 0 ((q.add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU q.width)
  else q

theorem cntD_combIndices (N : Nat) : (cntD N).combIndices = [] := by
  first | rfl | simp [Design2.combIndices, cntD, Process2.isCombPhase]

theorem cntD_edgeIndices (N : Nat) : (cntD N).edgeIndices = [0] := by
  first | rfl | simp [Design2.edgeIndices, cntD, Process2.isEdgePhase]

theorem cntD_resetIndices (N : Nat) (a b : SvState) : (cntD N).resetIndices a b = [] := by
  first | rfl | simp [Design2.resetIndices, cntD]

theorem cnt_combSettle (N : Nat) (σ : ScheduleOracle) (f : Nat) (st : SvState) (k : Nat) :
    combSettle2 (cntD N) σ (f + 1) st k = .ok (st, k + 1) := by
  simp [combSettle2, cntD_combIndices, σ.choose_nil]

theorem apply_cnt (N : Nat) (inputs : SvState) (c r e q : LVec) :
    applyInputs2 (cntD N) inputs (S c r e q) =
      S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e) q := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup inputs "clk" <;> cases h2 : SvState.lookup inputs "rst" <;>
    cases h3 : SvState.lookup inputs "en" <;>
    simp [cntD, S, appIn, h1, h2, h3, SvState.set]

theorem cnt_cycle (N : Nat) (σ : ScheduleOracle) (inputs : SvState) (c r e q : LVec) (k F : Nat)
    (hF : 12 ≤ F) :
    cycleStep2 (cntD N) σ F inputs (S c r e q) k =
      .ok (S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e)
            (cntNext N (appIn inputs "rst" r) (appIn inputs "en" e) q), k + 3) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 12 := ⟨F - 12, by omega⟩
  simp only [cycleStep2, apply_cnt, cnt_combSettle, Res.pure_eq, Res.ok_bind, cntD_resetIndices,
    cntD_edgeIndices, σ.choose_singleton]
  by_cases hr : (appIn inputs "rst" r).condTrue = true
  · simp [edgePass2, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, cntD, S,
      SvState.lookup, commitNba2, cntNext, hr, SvState.set]
  · by_cases he : (appIn inputs "en" e).condTrue = true
    · simp [edgePass2, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, cntD, S,
        SvState.lookup, commitNba2, cntNext, hr, he, SvState.set]
    · simp [edgePass2, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, cntD, S,
        SvState.lookup, commitNba2, cntNext, hr, he]

theorem cnt_cycle_ok {N : Nat} {σ : ScheduleOracle} {inputs : SvState} {c r e q : LVec}
    {k F : Nat} {st : SvState} {k' : Nat}
    (h : cycleStep2 (cntD N) σ F inputs (S c r e q) k = .ok (st, k')) :
    st = S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e)
          (cntNext N (appIn inputs "rst" r) (appIn inputs "en" e) q) ∧ k' = k + 3 := by
  have h1 := cycleStep2_mono h (by simp) (max F 12) (Nat.le_max_left _ _)
  have h2 := cnt_cycle N σ inputs c r e q k (max F 12) (Nat.le_max_right _ _)
  rw [h1] at h2
  simpa using h2

/-! ## 3. The register algebra -/

theorem cntNext_width (N : Nat) (r e q : LVec) : (cntNext N r e q).width = q.width := by
  unfold cntNext
  split
  · simp
  · split <;> simp

theorem cntNext_reset (N : Nat) {r : LVec} (e q : LVec) (hr : r.condTrue = true)
    (hw : q.width = N) : cntNext N r e q = LVec.ofBitVec (0#N) := by
  unfold cntNext
  have hw' : ((LVec.replicate N .l0).resizeU q.width).width = q.width := by simp
  rw [if_pos hr, LVec.insertAt_zero_of_width_eq hw']
  simp [hw]

theorem lit_one : (⟨#[.l1]⟩ : LVec) = LVec.ofBitVec (1#1) := by
  first | decide | rfl

theorem cntNext_inc (N : Nat) {r e : LVec} (x : BitVec N) (hr : r.condTrue = false)
    (he : e.condTrue = true) : cntNext N r e (LVec.ofBitVec x) = LVec.ofBitVec (x + 1#N) := by
  unfold cntNext
  have hr' : ¬ (r.condTrue = true) := by simp [hr]
  have hw' : (((LVec.ofBitVec x).add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU
      (LVec.ofBitVec x).width).width = (LVec.ofBitVec x).width := by simp
  rw [if_neg hr', if_pos he, LVec.insertAt_zero_of_width_eq hw', lit_one]
  simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt]

theorem cntNext_hold (N : Nat) {r e : LVec} (q : LVec) (hr : r.condTrue = false)
    (he : e.condTrue = false) : cntNext N r e q = q := by
  unfold cntNext
  have hr' : ¬ (r.condTrue = true) := by simp [hr]
  have he' : ¬ (e.condTrue = true) := by simp [he]
  rw [if_neg hr', if_neg he']

theorem bv1_cases (b : BitVec 1) : b = 0#1 ∨ b = 1#1 := by
  have h := b.isLt
  have : b.toNat = 0 ∨ b.toNat = 1 := by simp at h; omega
  rcases this with h0 | h1
  · left; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  · right; exact BitVec.eq_of_toNat_eq (by simpa using h1)

/-! ## 4. The statement for the hand-built family -/

theorem cnt_interface (N : Nat) : cntTask.Interface N (cntD N) := by
  simp [SeqTask.Interface, SeqTask.ports, cntTask, SvGolf.Tests.SeqCounter.task, inputPorts,
    outputPorts, cntD]

theorem cnt_disciplined (N : Nat) : cntTask.Disciplined (cntD N) := by
  simp [SeqTask.Disciplined, cntTask, SvGolf.Tests.SeqCounter.task, ClockedBy, cntD,
    Design2.inputNames, Process2.isEdgePhase, edgeClock, asyncReset, processDataNames, stmtNames,
    stmtOptNames, lhsNames, exprNames]

def Sh (N : Nat) (st : SvState) : Prop := ∃ c r e q, st = S c r e q ∧ q.width = N

theorem sh_init (N : Nat) : Sh N (initState2 (cntD N)) :=
  ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec 1, LVec.xVec N, by simp [initState2, cntD, S], by simp⟩

theorem sh_step {N : Nat} {σ : ScheduleOracle} {F : Nat} {inputs prev st : SvState} {k k' : Nat}
    (hs : Sh N prev) (h : cycleStep2 (cntD N) σ F inputs prev k = .ok (st, k')) : Sh N st := by
  obtain ⟨c, r, e, q, rfl, hw⟩ := hs
  obtain ⟨rfl, -⟩ := cnt_cycle_ok h
  exact ⟨_, _, _, _, rfl, by rw [cntNext_width]; exact hw⟩

theorem cnt_terminates (N : Nat) : Terminates2 (cntD N) :=
  Terminates2.of_invariant (Sh N) (sh_init N) (fun σ =>
    ⟨12, fun inputs st k hs => by
      obtain ⟨c, r, e, q, rfl, hw⟩ := hs
      exact ⟨_, _, cnt_cycle N σ inputs c r e q k 12 (Nat.le_refl _),
        _, _, _, _, rfl, by rw [cntNext_width]; exact hw⟩⟩) rfl

def Rel (N : Nat) (st : SvState) (s : BitVec N) : Prop :=
  ∃ c r e, st = S c r e (LVec.ofBitVec s)

theorem cnt_reset_cycle (N : Nat) :
    ∀ (σ : ScheduleOracle) (F : Nat) (inputs prev : SvState) (k : Nat) (st : SvState) (k' : Nat)
      (v : cntTask.Ins N), Sh N prev →
      cycleStep2 (cntD N) σ F inputs prev k = .ok (st, k') → cntTask.Drives N inputs (true, v) →
      Rel N st (cntTask.init N) ∧ cntTask.ObsOK N st (cntTask.init N, v) := by
  intro σ F inputs prev k st k' v hs h hd
  obtain ⟨en, ⟨⟩⟩ := v
  obtain ⟨c, r, e, q, rfl, hw⟩ := hs
  obtain ⟨rfl, -⟩ := cnt_cycle_ok h
  simp [SeqTask.Drives, SeqTask.RstDrives, cntTask, SvGolf.Tests.SeqCounter.task, HoldAll] at hd
  obtain ⟨hrst, -⟩ := hd
  have hr' : appIn inputs "rst" r = LVec.ofBitVec (1#1) := by simp [appIn, hrst]
  have hc : (appIn inputs "rst" r).condTrue = true := by rw [hr', LVec.condTrue_ofBitVec]; decide
  rw [cntNext_reset N _ q hc hw]
  refine ⟨⟨_, _, _, rfl⟩, ?_⟩
  simp [SeqTask.ObsOK, cntTask, SvGolf.Tests.SeqCounter.task, HoldAll, S, SvState.lookup]

theorem cnt_step_cycle (N : Nat) :
    ∀ (σ : ScheduleOracle) (F : Nat) (inputs prev : SvState) (k : Nat) (st : SvState) (k' : Nat)
      (s : BitVec N) (v : cntTask.Ins N), Sh N prev → Rel N prev s →
      cycleStep2 (cntD N) σ F inputs prev k = .ok (st, k') → cntTask.Drives N inputs (false, v) →
      Rel N st (cntTask.step N s v) ∧ cntTask.ObsOK N st (cntTask.step N s v, v) := by
  intro σ F inputs prev k st k' s v _ hrel h hd
  obtain ⟨en, ⟨⟩⟩ := v
  obtain ⟨c, r, e, hprev⟩ := hrel
  subst hprev
  obtain ⟨rfl, -⟩ := cnt_cycle_ok h
  simp [SeqTask.Drives, SeqTask.RstDrives, cntTask, SvGolf.Tests.SeqCounter.task, HoldAll] at hd
  obtain ⟨hrst, hen⟩ := hd
  have hr' : appIn inputs "rst" r = LVec.ofBitVec (0#1) := by simp [appIn, hrst]
  have hc : (appIn inputs "rst" r).condTrue = false := by rw [hr', LVec.condTrue_ofBitVec]; decide
  have he' : appIn inputs "en" e = LVec.ofBitVec en := by simp [appIn, hen]
  rcases bv1_cases en with h0 | h1
  · have hec : (appIn inputs "en" e).condTrue = false := by
      rw [he', h0, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_hold N _ hc hec]
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, SvGolf.Tests.SeqCounter.task, h0]
    · simp [SeqTask.ObsOK, cntTask, SvGolf.Tests.SeqCounter.task, HoldAll, S, SvState.lookup, h0]
  · have hec : (appIn inputs "en" e).condTrue = true := by
      rw [he', h1, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_inc N s hc hec]
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, SvGolf.Tests.SeqCounter.task, h1]
    · simp [SeqTask.ObsOK, cntTask, SvGolf.Tests.SeqCounter.task, HoldAll, S, SvState.lookup, h1]

theorem cnt_satisfiedAt (N : Nat) : cntTask.SatisfiedAt N (cntD N) :=
  SeqTask.satisfiedAt_of_cycle cntTask N (cntD N) ⟨_, rfl⟩ (cnt_interface N) (cnt_disciplined N)
    (cnt_terminates N) (Sh N) (Rel N) (sh_init N)
    (fun _ _ _ _ _ _ _ hs h => sh_step hs h)
    (cnt_reset_cycle N) (cnt_step_cycle N)

/-! ## 5. The loaded family is `cntD`, for every `N ≥ 1` (`instantiate2` at symbolic `N`) -/

def cntScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

def cntEnv (N : Int) : IEnv :=
  { cntScope N with dims := dimTable (cntScope N) design.pdesign.decls }

def cntDeclsRaw (w : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true },
   { name := "rst", width := 1, isInput := true },
   { name := "en", width := 1, isInput := true },
   { name := "q", width := w, isOutput := true }]

def cntElems : List (String × Nat) := [("clk", 1), ("rst", 1), ("en", 1), ("q", 1)]

def cntProc (w : Nat) : Process2 :=
  .alwaysFF "clk"
    (.ifStmt (.ident "rst")
      (.nbaAssign (.ident "q") (.lit (LVec.replicate w .l0)))
      (some (.ifStmt (.ident "en")
        (.nbaAssign (.ident "q")
          (.binary .add (.ident "q") (.resize w (.lit ⟨#[.l1]⟩))))
        none)))

theorem cnt_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (cntEnv N) := by
  rfl

theorem cnt_decls (N : Int) :
    buildDecls (cntEnv N) design.pdesign.decls = .ok (cntDeclsRaw ((N - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    cntEnv, cntScope, List.lookup, cntDeclsRaw, Gen2.except_ok_bind]

theorem cnt_elems (N : Int) : buildElems (cntEnv N) design.pdesign.decls = .ok cntElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, cntEnv,
    cntScope, List.lookup, cntElems, Gen2.except_ok_bind]

theorem cnt_static (N : Nat) (w : Nat) (hw : 1 ≤ w) :
    design.pdesign.processes.map
        (instProcess2 ((cntEnv N).withDecls (cntDeclsRaw w)) cntElems) = [cntProc w] := by
  sv2_inst_simp [instStmt2, design.pdesign, cntEnv, cntScope, cntDeclsRaw, cntElems, cntProc,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, hw]

theorem cnt_gens (N : Nat) (w : Nat) :
    expandList2 ((cntEnv N).withDecls (cntDeclsRaw w)) cntElems
      (PDesign.surfaceFuel [(N : Int)]) design.pdesign.generates = .ok [] := by
  rw [show design.pdesign.generates = [] from rfl, expandList2_nil]

theorem cnt_instantiate2 (N : Nat) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (cntEnv N) (cntDeclsRaw (((N : Int) - 1).natAbs + 1))
        cntElems []) :=
  PDesign.instantiate2_of_ok rfl (cnt_paramEnv N) (cnt_decls N) (cnt_elems N) (cnt_gens N _)

theorem cnt_processes (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList =
      [cntProc (((N : Int) - 1).natAbs + 1)] := by
  rw [PDesign.instantiateD2_of_ok (cnt_instantiate2 N), PDesign.assemble2_processes,
    cnt_static N _ (by omega)]
  simp [design.pdesign]

theorem cnt_driversOk (w : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames [cntProc w] = true := by
  rfl

theorem cnt_sem_eq_inst (N : Nat) :
    design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [cnt_processes]
  exact cnt_driversOk _

theorem cnt_sem_eq (N : Nat) (hN : 1 ≤ N) : design.sem N = cntD N := by
  have hw : ((N : Int) - 1).natAbs + 1 = N := by omega
  rw [cnt_sem_eq_inst, PDesign.instantiateD2_of_ok (cnt_instantiate2 N), hw]
  simp only [PDesign.assemble2, cnt_static N N hN, cntD, cntProc]
  simp [design.pdesign, cntDeclsRaw]

/-- **The counter's statement, of the loaded family.** -/
theorem solution : Goal := fun N hN => by
  rw [cnt_sem_eq N hN]
  exact cnt_satisfiedAt N

end Submission
