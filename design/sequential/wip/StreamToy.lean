import SvGolf.Seq
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import LeanModels.Sv.Comb2
import LeanModels.Sv.SeqFamily

/-!
# A toy `StreamTask` through `StreamTask.satisfiedAt_of_phases` (usability and non-vacuity test)

Not built by any library: compile with `lake env lean design/sequential/wip/StreamToy.lean` from
`svgolf/` (through the Lean slot wrapper). The `TxToy` of the stream reduction.

A one-value stream (`count = 1`, width 1, `spec = id`, which is `sortAsc` at one value):
`out_valid <= in_valid; out_data <= in_data`, a one-cycle delay. After a start at `s`, the input is
sampled at entry `s + 1` and shown in snapshot `s + 1` (`lat = 1`). `toyD false` satisfies the
statement through the reduction (`toy_statement`); `toyD true` drives `out_valid <= start` instead,
which emits one value too early (in the start's own snapshot, before any input), and it admits NO
phase model at any latency (`early_no_model`): the reduction is not vacuous.
-/

namespace StreamToy

open LeanModels.Sv SvGolf

attribute [local simp] cond_bit

def task : StreamTask Unit where
  inRange _ := True
  clk := "clk"
  rst := "rst"
  start := "start"
  inValid := "in_valid"
  inData := "in_data"
  outValid := "out_valid"
  outData := "out_data"
  width _ := 1
  count _ := 1
  spec _ xs := xs

/-- `early = false`: `out_valid <= in_valid`; `early = true`: `out_valid <= start` (too early). -/
def toyD (early : Bool) : Design2 where
  name := "stream1"
  decls := #[{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
    { name := "start", width := 1, isInput := true }, { name := "in_valid", width := 1, isInput := true },
    { name := "in_data", width := 1, isInput := true }, { name := "out_valid", width := 1, isOutput := true },
    { name := "out_data", width := 1, isOutput := true }]
  processes := #[.alwaysFF "clk" (.ifStmt (.ident "rst") (.nbaAssign (.ident "out_valid") (.lit ⟨#[.l0]⟩))
    (some (.block #[.nbaAssign (.ident "out_valid") (.ident (if early then "start" else "in_valid")),
      .nbaAssign (.ident "out_data") (.ident "in_data")])))]

def S (ck r s iv id ov od : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("in_valid", iv), ("in_data", id), ("out_valid", ov),
    ("out_data", od)]

/-- One cycle, evaluated (pre-edge values, inputs applied). -/
def toyNext (early : Bool) (ck r s iv id _ov od : LVec) : SvState :=
  if r.condTrue then S ck r s iv id (bit false) od
  else S ck r s iv id ((if early then s else iv).resizeU 1) (id.resizeU 1)

theorem apply_toy (early : Bool) (e : SvState) (ck r s iv id ov od : LVec) :
    applyInputs2 (toyD early) e (S ck r s iv id ov od) = S (appIn e "clk" ck) (appIn e "rst" r)
      (appIn e "start" s) (appIn e "in_valid" iv) (appIn e "in_data" id) ov od := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "in_valid" <;>
    cases h5 : SvState.lookup e "in_data" <;>
    simp [toyD, S, appIn, h1, h2, h3, h4, h5, SvState.set]

theorem toy_combSettle (early : Bool) (σ : ScheduleOracle) (f : Nat) (st : SvState) (k : Nat) :
    combSettle2 (toyD early) σ (f + 1) st k = .ok (st, k + 1) := by
  have : (toyD early).combIndices = [] := by
    first | rfl | simp [Design2.combIndices, toyD, Process2.isCombPhase]
  simp [combSettle2, this, σ.choose_nil]

theorem toy_cycle (early : Bool) (σ : ScheduleOracle) (e : SvState) (ck r s iv id ov od : LVec)
    (k F : Nat) (hF : 12 ≤ F) (h1 : ov.width = 1) (h2 : od.width = 1) :
    cycleStep2 (toyD early) σ F e (S ck r s iv id ov od) k = .ok (toyNext early (appIn e "clk" ck)
      (appIn e "rst" r) (appIn e "start" s) (appIn e "in_valid" iv) (appIn e "in_data" id) ov od, k + 3) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 12 := ⟨F - 12, by omega⟩
  have he : (toyD early).edgeIndices = [0] := by
    first | rfl | simp [Design2.edgeIndices, toyD, Process2.isEdgePhase]
  have hr : ∀ a b, (toyD early).resetIndices a b = [] := fun a b => by
    first | rfl | simp [Design2.resetIndices, toyD]
  simp only [cycleStep2, apply_toy, toy_combSettle, Res.pure_eq, Res.ok_bind, hr, he, σ.choose_singleton]
  unfold toyNext
  cases early <;> by_cases c1 : (appIn e "rst" r).condTrue = true <;>
    simp [edgePass2, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, toyD, S,
      SvState.lookup, commitNba2, c1, SvState.set, insertAt_full, h1, h2, l0_bit]

def Sh (st : SvState) : Prop :=
  ∃ ck r s iv id ov od, st = S ck r s iv id ov od ∧ ov.width = 1 ∧ od.width = 1

/-- One cycle from a state of the shape (the shape carried, so obligations need not ask). -/
def Stp (early : Bool) (e prev st : SvState) : Prop :=
  ∃ ck r s iv id ov od, prev = S ck r s iv id ov od ∧ (ov.width = 1 ∧ od.width = 1) ∧
    st = toyNext early (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "in_valid" iv)
      (appIn e "in_data" id) ov od

theorem toyNext_sh (early : Bool) {ck r s iv id ov od : LVec} (_h1 : ov.width = 1) (h2 : od.width = 1) :
    Sh (toyNext early ck r s iv id ov od) := by
  unfold toyNext
  split
  · exact ⟨_, _, _, _, _, _, _, rfl, by simp, h2⟩
  · exact ⟨_, _, _, _, _, _, _, rfl, by simp, by simp⟩

theorem sh_init (early : Bool) : Sh (initState2 (toyD early)) :=
  ⟨.xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec 1, by simp [initState2, toyD, S], by simp,
    by simp⟩

/-- The clock step of `toyD early`. -/
def cyc (early : Bool) : CycleModel (toyD early) where
  Shape := Sh
  Step := Stp early
  init := sh_init early
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, iv, id, ov, od, rfl, h1, h2⟩ hc
    exact ⟨ck, r, s, iv, id, ov, od, rfl, ⟨h1, h2⟩, (Prod.mk.inj (cycleStep2_det hc
      (toy_cycle early σ e ck r s iv id ov od k 12 (Nat.le_refl _) h1 h2))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, -, ⟨h1, h2⟩, rfl⟩
    exact toyNext_sh early h1 h2

theorem dataIs_appIn {e : SvState} {x : BitVec (task.width ())} (h : task.DataIs () e task.inData x)
    (old : LVec) : appIn e "in_data" old = LVec.ofBitVec x := by
  simp only [appIn, show SvState.lookup e "in_data" = _ from h, Option.getD_some]

/-! ## The phase model of `toyD false` at `lat = 1` -/

def model : task.PhaseModel () 1 (toyD false) where
  toCycleModel := cyc false
  Ready st := ∃ ck r s iv id od, st = S ck r s iv id (bit false) od
  At ys j st := ∃ ck r s iv id od, st = S ck r s iv id (bit (decide (j = 1))) od ∧
    (j = 1 → od = LVec.ofBitVec (ys.headD 0))
  out ys j := (decide (j = 1), ys.headD 0)
  out_feed := by intro xs j hj; simp [task] at hj; simp [hj]
  out_lat := by intro xs j _ hj; simp; omega
  out_spec := by
    intro xs hx
    cases xs with
    | nil => simp [task] at hx
    | cons x xs => cases xs with
      | nil => rfl
      | cons _ _ => have h1 : task.count () = 1 := rfl; simp only [List.length_cons] at hx; omega
  ready_out := by rintro st ⟨ck, r, s, iv, id, od, rfl⟩; simp [BitIs, task, S, SvState.lookup]
  at_out := by
    rintro ys j st ⟨ck, r, s, iv, id, od, rfl, hd⟩
    refine ⟨by simp [BitIs, task, S, SvState.lookup], fun hj => ?_⟩
    simp only [decide_eq_true_eq] at hj
    simp [StreamTask.DataIs, task, S, SvState.lookup, hd hj]
  reset := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, -, -, rfl⟩ hr
    rw [show appIn e "rst" r = bit true from BitIs.appIn_eq hr r]
    exact ⟨appIn e "clk" ck, bit true, appIn e "start" s, appIn e "in_valid" iv, appIn e "in_data" id, od,
      by simp [toyNext, bit]⟩
  hold := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, -, -, rfl⟩ - hr hs hiv
    simp only [task] at hr hs hiv
    rw [BitIs.appIn_eq hr r, BitIs.appIn_eq hs s, BitIs.appIn_eq hiv iv]
    exact ⟨appIn e "clk" ck, bit false, bit false, bit false, appIn e "in_data" id,
      (appIn e "in_data" id).resizeU 1, by simp [toyNext, bit]⟩
  start := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, -, -, rfl⟩ - hr hs hiv
    simp only [task] at hr hs hiv
    rw [BitIs.appIn_eq hr r, BitIs.appIn_eq hs s, BitIs.appIn_eq hiv iv]
    exact ⟨appIn e "clk" ck, bit false, bit true, bit false, appIn e "in_data" id,
      (appIn e "in_data" id).resizeU 1, by simp [toyNext, bit], by simp⟩
  feed := by
    rintro e prev st ys j x - ⟨ck, r, s, iv, id, ov, od, -, -, rfl⟩ - hl hj hr hs hiv hx
    obtain rfl : j = 0 := by simp [task] at hj; omega
    obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hl
    simp only [task] at hr hs hiv
    rw [BitIs.appIn_eq hr r, BitIs.appIn_eq hs s, BitIs.appIn_eq hiv iv, dataIs_appIn hx]
    have hxw : LVec.ofBitVec (BitVec.setWidth 1 x) = LVec.ofBitVec x := congrArg _ (BitVec.setWidth_eq (x : BitVec 1))
    exact ⟨appIn e "clk" ck, bit false, bit false, bit true, LVec.ofBitVec x, LVec.ofBitVec x,
      by simp [toyNext, bit, hxw], by simp⟩
  run := by
    rintro e prev st xs j - ⟨ck, r, s, iv, id, ov, od, -, -, rfl⟩ - - hj hr hs hiv
    simp only [task] at hr hs hiv
    rw [BitIs.appIn_eq hr r, BitIs.appIn_eq hs s, BitIs.appIn_eq hiv iv]
    have hj0 : j ≠ 0 := by simp only [task] at hj; omega
    exact ⟨appIn e "clk" ck, bit false, bit false, bit false, appIn e "in_data" id,
      (appIn e "in_data" id).resizeU 1, by simp [toyNext, bit, hj0], fun h => absurd h (by omega)⟩

theorem toy_interface (early : Bool) : task.Interface () (toyD early) :=
  ⟨by cases early <;> first | rfl | simp [inputPorts, toyD, task],
    by cases early <;> first | rfl | simp [outputPorts, toyD, task]⟩

theorem toy_disciplined (early : Bool) : task.Disciplined (toyD early) := by
  cases early <;>
    simp [StreamTask.Disciplined, task, ClockedBy, toyD, Design2.inputNames, Process2.isEdgePhase, edgeClock,
      asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames]

theorem toy_terminates (early : Bool) : Terminates2 (toyD early) := by
  refine Terminates2.of_invariant Sh (sh_init early) (fun σ => ⟨12, ?_⟩) (by cases early <;> rfl)
  rintro e st k ⟨ck, r, s, iv, id, ov, od, rfl, h1, h2⟩
  exact ⟨_, _, toy_cycle early σ e ck r s iv id ov od k 12 (Nat.le_refl _) h1 h2, toyNext_sh early h1 h2⟩

/-- **The toy satisfies the `StreamTask` statement at latency 1**, through the reduction. -/
theorem toy_satisfiedAt : task.SatisfiedAt () 1 (toyD false) :=
  task.satisfiedAt_of_phases (toy_interface false) (toy_disciplined false) (toy_terminates false)
    (Nat.le_refl 1) (Nat.le_refl 1) (fun _ h => h) model

theorem toy_statement : task.Statement (fun _ => toyD false) (fun _ => 1) := fun _ _ => toy_satisfiedAt

/-! ## Non-vacuity: a toy that emits one value too early admits no phase model -/

/-- **No phase model exists for `toyD true`, at any latency**: from the reset state, a start entry
yields (by `start`) an `At [] 0` state, which must show `out_valid` = 0 (`at_out`, `out_feed`); the
design shows 1 there. -/
theorem early_no_model (lat : Nat) (M : task.PhaseModel () lat (toyD true)) : False := by
  obtain ⟨ck, r, s, iv, id, ov, od, h0, h1, h2⟩ := sh_init true
  let e1 : SvState := [("rst", bit true)]
  let e2 : SvState := [("rst", bit false), ("start", bit true), ("in_valid", bit false)]
  have c1 := toy_cycle true σ_src e1 ck r s iv id ov od 0 12 (Nat.le_refl _) h1 h2
  rw [← h0] at c1
  have hs1 := M.cycle σ_src 12 e1 _ 0 _ 3 M.init c1
  have hrd := M.reset e1 _ _ M.init hs1 (by simp [BitIs, e1, task, SvState.lookup])
  have hsh1 := M.shape _ _ _ M.init hs1
  have hst1 : toyNext true (appIn e1 "clk" ck) (appIn e1 "rst" r) (appIn e1 "start" s) (appIn e1 "in_valid" iv)
      (appIn e1 "in_data" id) ov od = S ck (bit true) s iv id (bit false) od := by
    simp [toyNext, appIn, e1, SvState.lookup]
  rw [hst1] at hs1 hrd hsh1
  have c2 := toy_cycle true σ_src e2 ck (bit true) s iv id (bit false) od 3 12 (Nat.le_refl _) (by simp) h2
  have hs2 := M.cycle σ_src 12 e2 _ 3 _ 6 hsh1 c2
  have hat := M.start e2 _ _ hsh1 hs2 (.inl hrd) (by simp [BitIs, e2, task, SvState.lookup])
    (by simp [BitIs, e2, task, SvState.lookup]) (by simp [BitIs, e2, task, SvState.lookup])
  have hb := (M.at_out [] 0 _ hat).1
  rw [M.out_feed [] 0 (by simp [task])] at hb
  revert hb
  simp [BitIs, toyNext, appIn, e2, task, S, SvState.lookup]

#print axioms toy_statement
#print axioms early_no_model

end StreamToy
