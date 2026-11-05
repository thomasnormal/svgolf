import SvGolf.Seq
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import LeanModels.Sv.Comb2

/-!
# A toy `TxTask` through `TxTask.satisfiedAt_of_phases` (usability test of the reduction)

Not built by any library: compile with `lake env lean design/sequential/wip/TxToy.lean` from
`svgolf/` (through the Lean slot wrapper). The worked example for a `TxTask` reference: the
`CycleModel` fields (`Shape`, a `Step` that carries the shape, `cycle` by `cycleStep2_det` against
the evaluated cycle) and the five one-`Step` obligations.

A one-bit transaction: on `start` the register `y` captures the operand `a` and `busy` rises;
the next cycle `done` rises (`lat = 1`: `done` shows in the snapshot after the start's). Every
phase is used: `Ready` after reset, `Busy x 0` at the start's snapshot, `Fin x` from the next.
-/

namespace TxToy

open LeanModels.Sv SvGolf

def task : TxTask Unit where
  inRange _ := True
  clk := "clk"
  rst := "rst"
  start := "start"
  operands _ := [("a", 1)]
  done := "done"
  payload _ := [("y", 1)]
  result _ x := x

abbrev nb (n : String) (b : Logic) : Stmt2 := .nbaAssign (.ident n) (.lit ⟨#[b]⟩)

def toyD : Design2 where
  name := "tx1"
  decls := #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "start", width := 1, isInput := true }, { name := "a", width := 1, isInput := true },
    { name := "done", width := 1, isOutput := true }, { name := "y", width := 1, isOutput := true },
    { name := "busy", width := 1 }]
  processes := #[.alwaysFF "clk" (.ifStmt (.ident "rst") (.block #[nb "busy" .l0, nb "done" .l0])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" .l1, nb "done" .l0, .nbaAssign (.ident "y") (.ident "a")])
      (some (.ifStmt (.ident "busy") (.block #[nb "busy" .l0, nb "done" .l1]) none)))))]

def S (ck r s a dn y bz : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("a", a), ("done", dn), ("y", y), ("busy", bz)]

abbrev bit (b : Bool) : LVec := LVec.ofBitVec (BitVec.ofBool b)

/-- One cycle, evaluated (pre-edge values, inputs applied). -/
def toyNext (ck r s a dn y bz : LVec) : SvState :=
  if r.condTrue then S ck r s a (bit false) y (bit false)
  else if s.condTrue then S ck r s a (bit false) (a.resizeU 1) (bit true)
  else if bz.condTrue then S ck r s a (bit true) y (bit false)
  else S ck r s a dn y bz

theorem insertAt_full {v p : LVec} (h : p.width = v.width) : v.insertAt 0 p = p := by
  have h1 := LVec.extract_insertAt_self (v := v) (p := p) (lo := 0) (w := p.width) rfl (by omega)
  have h2 : (v.insertAt 0 p).extract 0 p.width = v.insertAt 0 p := by
    have := LVec.extract_full (v.insertAt 0 p)
    rw [LVec.width_insertAt] at this
    rw [h]; exact this
  exact h2.symm.trans h1

theorem apply_toy (e : SvState) (ck r s a dn y bz : LVec) :
    applyInputs2 toyD e (S ck r s a dn y bz) =
      S (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "a" a) dn y bz := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "a" <;>
    simp [toyD, S, appIn, h1, h2, h3, h4, SvState.set]

theorem l0_bit : (⟨#[.l0]⟩ : LVec).resizeU 1 = bit false := by decide
theorem l1_bit : (⟨#[.l1]⟩ : LVec).resizeU 1 = bit true := by decide

theorem toyD_combIndices : toyD.combIndices = [] := by
  first | rfl | simp [Design2.combIndices, toyD, Process2.isCombPhase]
theorem toyD_edgeIndices : toyD.edgeIndices = [0] := by
  first | rfl | simp [Design2.edgeIndices, toyD, Process2.isEdgePhase]
theorem toyD_resetIndices (a b : SvState) : toyD.resetIndices a b = [] := by
  first | rfl | simp [Design2.resetIndices, toyD]
theorem toy_combSettle (σ : ScheduleOracle) (f : Nat) (st : SvState) (k : Nat) :
    combSettle2 toyD σ (f + 1) st k = .ok (st, k + 1) := by
  simp [combSettle2, toyD_combIndices, σ.choose_nil]

theorem toy_cycle (σ : ScheduleOracle) (e : SvState) (ck r s a dn y bz : LVec) (k F : Nat)
    (hF : 12 ≤ F) (h1 : dn.width = 1) (h2 : y.width = 1) (h3 : bz.width = 1) :
    cycleStep2 toyD σ F e (S ck r s a dn y bz) k = .ok (toyNext (appIn e "clk" ck) (appIn e "rst" r)
      (appIn e "start" s) (appIn e "a" a) dn y bz, k + 3) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 12 := ⟨F - 12, by omega⟩
  simp only [cycleStep2, apply_toy, toy_combSettle, Res.pure_eq, Res.ok_bind, toyD_resetIndices,
    toyD_edgeIndices, σ.choose_singleton]
  unfold toyNext
  by_cases c1 : (appIn e "rst" r).condTrue = true <;> by_cases c2 : (appIn e "start" s).condTrue = true <;>
    by_cases c3 : bz.condTrue = true <;>
    simp [edgePass2, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, toyD, S,
      SvState.lookup, commitNba2, c1, c2, c3, SvState.set, insertAt_full, h1, h2, h3, l0_bit, l1_bit]

/-! ## The phase model -/

@[simp] theorem cond_bit (b : Bool) : (bit b).condTrue = b := by cases b <;> simp [LVec.condTrue_ofBitVec]

theorem S_inj {ck r s a dn y bz ck' r' s' a' dn' y' bz' : LVec}
    (h : S ck r s a dn y bz = S ck' r' s' a' dn' y' bz') :
    ck = ck' ∧ r = r' ∧ s = s' ∧ a = a' ∧ dn = dn' ∧ y = y' ∧ bz = bz' := by
  simpa [S] using h

def Sh (st : SvState) : Prop :=
  ∃ ck r s a dn y bz, st = S ck r s a dn y bz ∧ dn.width = 1 ∧ y.width = 1 ∧ bz.width = 1

/-- One cycle from a state of the shape (the shape carried, so obligations need not ask). -/
def Stp (e prev st : SvState) : Prop :=
  ∃ ck r s a dn y bz, prev = S ck r s a dn y bz ∧ (dn.width = 1 ∧ y.width = 1 ∧ bz.width = 1) ∧
    st = toyNext (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "a" a) dn y bz

theorem toyNext_sh {ck r s a dn y bz : LVec} (h1 : dn.width = 1) (h2 : y.width = 1) (h3 : bz.width = 1) :
    Sh (toyNext ck r s a dn y bz) := by
  unfold toyNext
  repeat' split
  all_goals exact ⟨_, _, _, _, _, _, _, rfl, by simp [*]⟩

theorem sh_init : Sh (initState2 toyD) :=
  ⟨.xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, by simp [initState2, toyD, S], by simp⟩

theorem ops_appIn {e : SvState} {x : task.Ops ()} (h : HoldAll e (task.operands ()) x) (a : LVec) :
    appIn e "a" a = LVec.ofBitVec x.1 := by
  simp only [task, HoldAll] at h; simp [appIn, h.1]

def model : task.PhaseModel () 1 toyD where
  Shape := Sh
  Step := Stp
  init := sh_init
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, dn, y, bz, rfl, h1, h2, h3⟩ hc
    exact ⟨ck, r, s, a, dn, y, bz, rfl, ⟨h1, h2, h3⟩, (Prod.mk.inj (cycleStep2_det hc
      (toy_cycle σ e ck r s a dn y bz k 12 (Nat.le_refl _) h1 h2 h3))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, dn, y, bz, -, ⟨h1, h2, h3⟩, rfl⟩
    exact toyNext_sh h1 h2 h3
  Ready st := ∃ ck r s a y, st = S ck r s a (bit false) y (bit false)
  Busy x m st := m = 0 ∧ ∃ ck r s a, st = S ck r s a (bit false) (LVec.ofBitVec x.1) (bit true)
  Fin x st := ∃ ck r s a, st = S ck r s a (bit true) (LVec.ofBitVec x.1) (bit false)
  ready_done := by
    rintro st ⟨ck, r, s, a, y, rfl⟩; exact ⟨false, by simp [BitIs, task, S, SvState.lookup]⟩
  busy_done := by
    rintro x m st ⟨-, ck, r, s, a, rfl⟩; simp [BitIs, task, S, SvState.lookup]
  fin_done := by
    rintro x st ⟨ck, r, s, a, rfl⟩; simp [BitIs, HoldAll, task, S, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, dn, y, bz, -, -, rfl⟩ hr
    rw [show appIn e "rst" r = bit true from BitIs.appIn_eq hr r]
    exact ⟨appIn e "clk" ck, bit true, appIn e "start" s, appIn e "a" a, y, by simp [toyNext]⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, dn, y, bz, -, -, rfl⟩ - hr hs hx
    rw [show appIn e "rst" r = bit false from BitIs.appIn_eq hr r, show appIn e "start" s = bit true from BitIs.appIn_eq hs s, ops_appIn hx]
    exact .inr ⟨0, by decide, rfl, appIn e "clk" ck, bit false, bit true, LVec.ofBitVec x.1, by simp [toyNext]⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, dn, y, bz, hp, -, rfl⟩ ⟨rfl, ck', r', s', a', hb⟩ hr hs -
    obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := S_inj (hp.symm.trans hb)
    rw [show appIn e "rst" r = bit false from BitIs.appIn_eq hr r, show appIn e "start" s = bit false from BitIs.appIn_eq hs s]
    exact .inl ⟨appIn e "clk" ck, bit false, bit false, appIn e "a" a, by simp [toyNext]⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, dn, y, bz, hp, -, rfl⟩ ⟨ck', r', s', a', y', hb⟩ hr hs
    obtain ⟨-, -, -, -, rfl, -, rfl⟩ := S_inj (hp.symm.trans hb)
    rw [show appIn e "rst" r = bit false from BitIs.appIn_eq hr r, show appIn e "start" s = bit false from BitIs.appIn_eq hs s]
    exact ⟨appIn e "clk" ck, bit false, bit false, appIn e "a" a, y, by simp [toyNext]⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, dn, y, bz, hp, -, rfl⟩ ⟨ck', r', s', a', hb⟩ hr hs
    obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := S_inj (hp.symm.trans hb)
    rw [show appIn e "rst" r = bit false from BitIs.appIn_eq hr r, show appIn e "start" s = bit false from BitIs.appIn_eq hs s]
    exact ⟨appIn e "clk" ck, bit false, bit false, appIn e "a" a, by simp [toyNext]⟩

theorem toy_interface : task.Interface () toyD :=
  ⟨by first | rfl | simp [inputPorts, toyD, task], by first | rfl | simp [outputPorts, toyD, task]⟩

theorem toy_disciplined : task.Disciplined toyD := by
  simp [TxTask.Disciplined, task, ClockedBy, toyD, Design2.inputNames, Process2.isEdgePhase, edgeClock,
    asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames]

theorem toy_terminates : Terminates2 toyD := by
  refine Terminates2.of_invariant Sh sh_init (fun σ => ⟨12, ?_⟩) (by rfl)
  rintro e st k ⟨ck, r, s, a, dn, y, bz, rfl, h1, h2, h3⟩
  exact ⟨_, _, toy_cycle σ e ck r s a dn y bz k 12 (Nat.le_refl _) h1 h2 h3, toyNext_sh h1 h2 h3⟩

/-- **The toy satisfies the `TxTask` statement at latency 1**, through the reduction. -/
theorem toy_satisfiedAt : task.SatisfiedAt () 1 toyD :=
  task.satisfiedAt_of_phases toy_interface toy_disciplined toy_terminates (Nat.le_refl 1) model

theorem toy_statement : task.Statement (fun _ => toyD) (fun _ => 1) := fun _ _ => toy_satisfiedAt

#print axioms toy_statement

end TxToy
