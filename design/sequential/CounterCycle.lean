import SeqTask
import SvGolf.LoadSv
import LeanModels.Sv.Mono2

/-!
# The N-bit counter at symbolic `N`: one-cycle lemma and the sequential statement (SPIKE SKETCH)

Companion of `README.md` section 7. `cnt.sv` is the design (`always_ff @(posedge clk)`, synchronous
reset, enable). This file shows, with the CURRENT ls-sv library and `SeqTask.lean`:

1. `cntD N`, the instantiated design written by hand in the shape `load_design_sv2` produces, and its
   agreement with the real envelope at `N = 1, 2, 3, 4, 8, 16, 32` (`#guard`). A symbolic-`N`
   instantiation theorem for an `always_ff` body does not exist yet (the `asDesign N` precedent of
   `Comb2ProcExample`/`addsub_comb/agree.lean` is the same: hand-built family plus concrete agreement);
   it is the same gap WP-G has for `always_comb` bodies, and it is what the `sv_seq` front end closes.
2. `cnt_cycle`: ONE closed-form lemma for `cycleStep2 (cntD N)` on the 4-signal state, for every `N`, every
   schedule, every stimulus entry, every 4-state register content, every fuel from `12` on.
3. The facts about `cntNext` (reset forgets the old register, x included; enable increments a known
   register; hold keeps it).
4. `cntTask`, the `SeqTask` of the counter, and `cnt_statement : cntTask.Statement cntD`, proved for ALL `N ≥ 1`
   and all cycles by `SeqTask.satisfiedAt_of_cycle`.

The open part, stated in `README.md`: `cntD N = cnt.sem N` for symbolic `N` (instead of the concrete
`#guard`s), and the tactic that produces `cnt_cycle` and the lemmas around it from `cnt.sem N` directly.
-/

namespace SvGolf.Seq.Counter

open LeanModels.Sv SvGolf SvGolf.Seq

load_sv cntSv from "tests/seq_counter/reference/cnt.sv" (top := "cnt") (probes := "N=1;N=2;N=3;N=4;N=8;N=16")

/-! ## 1. The instantiated design -/

/-- The counter, hand-built in the shape the instantiation produces. -/
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

def agrees (N : Nat) : Bool :=
  (cntSv.sem N).name == (cntD N).name &&
  (cntSv.sem N).decls.toList == (cntD N).decls.toList &&
  toString (repr (cntSv.sem N).processes) == toString (repr (cntD N).processes)

#guard [1, 2, 3, 4, 8, 16, 32].all agrees

/-! ## 2. One cycle, in closed form -/

/-- The 4-signal state of the counter (declaration order). -/
def S (c r e q : LVec) : SvState := [("clk", c), ("rst", r), ("en", e), ("q", q)]

/-- The next value of the register `q`, as the edge process computes it from the settled pre-edge
values of `rst` and `en` (4-state, nothing assumed about `q`). -/
def cntNext (N : Nat) (r e q : LVec) : LVec :=
  if r.condTrue then q.insertAt 0 ((LVec.replicate N .l0).resizeU q.width)
  else if e.condTrue then
    q.insertAt 0 ((q.add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU q.width)
  else q

theorem cntD_combIndices (N : Nat) : (cntD N).combIndices = [] := by
  first
  | rfl
  | decide
  | simp [Design2.combIndices, cntD, Process2.isCombPhase]

theorem cntD_edgeIndices (N : Nat) : (cntD N).edgeIndices = [0] := by
  first
  | rfl
  | decide
  | simp [Design2.edgeIndices, cntD, Process2.isEdgePhase]

theorem cntD_resetIndices (N : Nat) (a b : SvState) : (cntD N).resetIndices a b = [] := by
  first
  | rfl
  | decide
  | simp [Design2.resetIndices, cntD]

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

/-- **The one-cycle lemma, for every `N`.** From the state `S c r e q`, one cycle of the counter
under any schedule and any stimulus entry succeeds (at every fuel from 12) and returns the state
with the inputs applied and `q` replaced by `cntNext`. -/
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

/-- `cnt_cycle` at ANY fuel: a successful cycle is the closed form (cross-fuel determinism). -/
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

/-- Writing a whole-width vector replaces the old content, x bits included. -/
theorem insertAt_full {v p : LVec} (h : p.width = v.width) : v.insertAt 0 p = p := by
  have h1 := LVec.extract_insertAt_self (v := v) (p := p) (lo := 0) (w := p.width) rfl (by omega)
  have h2 : (v.insertAt 0 p).extract 0 p.width = v.insertAt 0 p := by
    have := LVec.extract_full (v.insertAt 0 p)
    rw [LVec.width_insertAt] at this
    rw [h]; exact this
  exact h2.symm.trans h1

theorem cntNext_width (N : Nat) (r e q : LVec) : (cntNext N r e q).width = q.width := by
  unfold cntNext
  split
  · simp
  · split <;> simp

/-- **Reset forgets the old register**, whatever it held (x included). -/
theorem cntNext_reset (N : Nat) {r : LVec} (e q : LVec) (hr : r.condTrue = true)
    (hw : q.width = N) : cntNext N r e q = LVec.ofBitVec (0#N) := by
  unfold cntNext
  have hw' : ((LVec.replicate N .l0).resizeU q.width).width = q.width := by simp
  rw [if_pos hr, insertAt_full hw']
  simp [hw]

/-- The one-bit constant `1'b1`. -/
theorem lit_one : (⟨#[.l1]⟩ : LVec) = LVec.ofBitVec (1#1) := by
  first
  | decide
  | rfl

/-- Enable increments a known register. -/
theorem cntNext_inc (N : Nat) {r e : LVec} (x : BitVec N) (hr : r.condTrue = false)
    (he : e.condTrue = true) : cntNext N r e (LVec.ofBitVec x) = LVec.ofBitVec (x + 1#N) := by
  unfold cntNext
  have hr' : ¬ (r.condTrue = true) := by simp [hr]
  have hw' : (((LVec.ofBitVec x).add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU
      (LVec.ofBitVec x).width).width = (LVec.ofBitVec x).width := by simp
  rw [if_neg hr', if_pos he, insertAt_full hw', lit_one]
  simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt]

/-- No enable holds the register. -/
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

/-! ## 4. The task and the statement for every `N` -/

/-- **The counter task.** `N`-bit up-counter, enable `en`, synchronous active-high reset `rst`, clock
`clk`; output `q` (registered). -/
def cntTask : SeqTask where
  inRange N := 1 ≤ N
  clk := some "clk"
  rst := some ("rst", true)
  inputs _ := [("en", 1)]
  outputs N := [("q", N)]
  State N := BitVec N
  init N := 0#N
  step N s := fun (en, ()) => if en = 1#1 then s + 1#N else s
  obs _ s := fun _ => (s, ())

theorem cnt_moore : cntTask.Moore := fun _ _ _ _ => rfl

theorem cnt_interface (N : Nat) : cntTask.Interface N (cntD N) := by
  simp [SeqTask.Interface, SeqTask.ports, cntTask, inputPorts, outputPorts, cntD]

theorem cnt_disciplined (N : Nat) : cntTask.Disciplined (cntD N) := by
  simp [SeqTask.Disciplined, cntTask, ClockedBy, cntD, Design2.inputNames, Process2.isEdgePhase,
    Process2.clock?, Process2.resetName?, Process2.mentionsData, Stmt2.mentions,
    Stmt2.mentionsOpt, Lhs2.mentions, Expr2.idents]

/-- The shape invariant: the 4-signal state with a `q` of width `N`. -/
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

/-- The simulation relation: the snapshot is the 4-signal state whose `q` is the spec state, known. -/
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
  simp [SeqTask.Drives, SeqTask.RstDrives, cntTask, HoldAll] at hd
  obtain ⟨hrst, -⟩ := hd
  have hr' : appIn inputs "rst" r = LVec.ofBitVec (1#1) := by simp [appIn, hrst]
  have hc : (appIn inputs "rst" r).condTrue = true := by rw [hr', LVec.condTrue_ofBitVec]; decide
  rw [cntNext_reset N _ q hc hw]
  refine ⟨⟨_, _, _, rfl⟩, ?_⟩
  simp [SeqTask.ObsOK, cntTask, HoldAll, S, SvState.lookup]

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
  simp [SeqTask.Drives, SeqTask.RstDrives, cntTask, HoldAll] at hd
  obtain ⟨hrst, hen⟩ := hd
  have hr' : appIn inputs "rst" r = LVec.ofBitVec (0#1) := by simp [appIn, hrst]
  have hc : (appIn inputs "rst" r).condTrue = false := by rw [hr', LVec.condTrue_ofBitVec]; decide
  have he' : appIn inputs "en" e = LVec.ofBitVec en := by simp [appIn, hen]
  rcases bv1_cases en with h0 | h1
  · have hec : (appIn inputs "en" e).condTrue = false := by rw [he', h0, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_hold N _ hc hec]
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, h0]
    · simp [SeqTask.ObsOK, cntTask, HoldAll, S, SvState.lookup, h0]
  · have hec : (appIn inputs "en" e).condTrue = true := by rw [he', h1, LVec.condTrue_ofBitVec]; decide
    rw [cntNext_inc N s hc hec]
    refine ⟨⟨appIn inputs "clk" c, appIn inputs "rst" r, appIn inputs "en" e, ?_⟩, ?_⟩
    · simp [cntTask, h1]
    · simp [SeqTask.ObsOK, cntTask, HoldAll, S, SvState.lookup, h1]

/-- **The counter satisfies the sequential statement at every `N ≥ 1`**: for every schedule, every
stimulus and every completed run, from every reset, the register `q` is the spec counter, for all
cycles. (For the hand-built family `cntD`; see the module docstring for the instantiation gap.) -/
theorem cnt_satisfiedAt (N : Nat) : cntTask.SatisfiedAt N (cntD N) :=
  SeqTask.satisfiedAt_of_cycle cntTask N (cntD N) ⟨_, rfl⟩ (cnt_interface N) (cnt_disciplined N)
    (cnt_terminates N) (Sh N) (Rel N) (sh_init N)
    (fun _ _ _ _ _ _ _ hs h => sh_step hs h)
    (cnt_reset_cycle N) (cnt_step_cycle N)

theorem cnt_statement : cntTask.Statement cntD := fun N _ => cnt_satisfiedAt N

#print axioms cnt_statement

end SvGolf.Seq.Counter
