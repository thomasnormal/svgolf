import CounterMachine
import PreTask
import LeanModels.Sv.REdgeRun2
import LeanModels.Sv.FlatMemRun2

/-!
# The register file: the array view (D7), its cycle machine, and R-CYCLE over `run2`

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status: provisional over `run2`.** The design is hand-built, at a symbolic address width `A`
(depth `2^A`) and word width `W`, in the shape the loader produces for `logic [W-1:0] mem [0:2^A-1]`:
one `2^A * W`-bit vector, a write port written by NBA at the clock edge, and a combinational read port
`assign rdata = mem[raddr]`.

## Part A: the `run2`-facing R-CYCLE obligation (the stop-rule measure)

1. The closed-form cycle (`rf_cycleObs_ok`): the pre sample is the inputs applied and the read port
   settled on the OLD memory; the post sample is the memory written (`rfWrite`) and the read port
   settled again.
2. The array view (D7, `arrRead`/`arrWrite` on `Fin (2^A) → LVec`), abstraction `Abs`: word `j` of
   `mem` is `s j`. The flat read and write are the array's (`rfRead_eq`, `rfWrite_abs`).
3. `rfMachine`: the cycle machine whose store is the array, and `rf_rcycle`: every completed
   `Obs_run2` behaviour of `rfD A W` is the machine's run on the held inputs.
-/

namespace SvGolf.Arch.RF

open LeanModels.Sv LeanModels.Sv.Observe LeanModels.Sv.FlatMem SvGolf SvGolf.Seq SvGolf.Arch
  SvGolf.Seq.Counter

/-! ## A1. The design and its closed-form cycle -/

/-- The register file, depth `2^A`, words of `W` bits. -/
def rfD (A W : Nat) : Design2 where
  name := "rf"
  decls := #[{ name := "clk", width := 1, isInput := true },
             { name := "we", width := 1, isInput := true },
             { name := "waddr", width := A, isInput := true },
             { name := "wdata", width := W, isInput := true },
             { name := "raddr", width := A, isInput := true },
             { name := "rdata", width := W, isOutput := true },
             { name := "mem", width := 2 ^ A * W }]
  processes := #[
    .alwaysFF "clk"
      (.ifStmt (.ident "we") (.nbaAssign (.index "mem" (.ident "waddr") W) (.ident "wdata")) none),
    .assign (.ident "rdata") (.index (.ident "mem") (.ident "raddr") W)]

/-- The register file's state (declaration order). -/
def RS (c we wa wd ra rd mem : LVec) : SvState :=
  [("clk", c), ("we", we), ("waddr", wa), ("wdata", wd), ("raddr", ra), ("rdata", rd), ("mem", mem)]

theorem apply_rf (A W : Nat) (e : SvState) (c we wa wd ra rd mem : LVec) :
    applyInputs2 (rfD A W) e (RS c we wa wd ra rd mem) =
      RS (appIn e "clk" c) (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd)
        (appIn e "raddr" ra) rd mem := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "we" <;>
    cases h3 : SvState.lookup e "waddr" <;> cases h4 : SvState.lookup e "wdata" <;>
    cases h5 : SvState.lookup e "raddr" <;>
    simp [rfD, RS, appIn, h1, h2, h3, h4, h5, SvState.set]

theorem rf_procs (A W : Nat) :
    (rfD A W).processes[0]? = some (.alwaysFF "clk" (.ifStmt (.ident "we")
      (.nbaAssign (.index "mem" (.ident "waddr") W) (.ident "wdata")) none)) ∧
    (rfD A W).processes[1]? = some (.assign (.ident "rdata") (.index (.ident "mem") (.ident "raddr") W)) :=
  ⟨rfl, rfl⟩

/-- One pass of the read port, from a state whose `rdata` has width `W`. -/
theorem rf_pass {A W F : Nat} (hF : 2 ≤ F) (c we wa wd ra rd mem : LVec) (hw : rd.width = W) :
    combPass2 (rfD A W) F (RS c we wa wd ra rd mem) [1] =
      .ok (RS c we wa wd ra (rfRead W mem ra) mem) := by
  have hev := eval_index (W := W) hF (st := RS c we wa wd ra rd mem) (m := "mem") (r := "raddr")
    rfl rfl
  have hrd : SvState.lookup (RS c we wa wd ra rd mem) "rdata" = some rd := rfl
  simp only [combPass2, (rf_procs A W).2, runCombProcess2, hev, Res.ok_bind, resolveLhs2, hrd,
    Res.pure_eq]
  rw [insertAt_full (by simp [hw]), resizeU_of_width (by rw [rfRead_width, hw])]
  rfl

/-- **The read port settles in at most two passes**, to the word at `raddr`. -/
theorem rf_settle {A W F : Nat} (hF : 4 ≤ F) (σ : ScheduleOracle) (c we wa wd ra rd mem : LVec)
    (k : Nat) (hw : rd.width = W) : ∃ k', combSettle2 (rfD A W) σ F (RS c we wa wd ra rd mem) k =
      .ok (RS c we wa wd ra (rfRead W mem ra) mem, k') := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 4 := ⟨F - 4, by omega⟩
  have hci : (rfD A W).combIndices = [1] := rfl
  unfold combSettle2
  rw [hci, σ.choose_singleton, rf_pass (by omega) c we wa wd ra rd mem hw, Res.ok_bind]
  split
  · exact ⟨_, rfl⟩
  · unfold combSettle2
    rw [hci, σ.choose_singleton, rf_pass (by omega) c we wa wd ra _ mem (rfRead_width W mem ra),
      Res.ok_bind, if_pos (by simp)]
    exact ⟨_, rfl⟩

/-- **The edge**: the write port's NBA, committed. -/
theorem rf_edge {A W F : Nat} (hF : 3 ≤ F) (c we wa wd ra rd mem : LVec) :
    (edgePass2 (rfD A W) F (RS c we wa wd ra rd mem) [] [0] >>= fun x =>
      Res.ok (commitNba2 x.1 x.2)) = .ok (RS c we wa wd ra rd (rfWrite W mem we wa wd)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 3 := ⟨F - 3, by omega⟩
  have hwe : SvState.lookup (RS c we wa wd ra rd mem) "we" = some we := rfl
  have hwd : SvState.lookup (RS c we wa wd ra rd mem) "wdata" = some wd := rfl
  have hwa : SvState.lookup (RS c we wa wd ra rd mem) "waddr" = some wa := rfl
  have hm : SvState.lookup (RS c we wa wd ra rd mem) "mem" = some mem := rfl
  simp only [edgePass2, (rf_procs A W).1, runEdgeProcess2, execStmt2, evalExpr2, readSignal, hwe,
    Res.ok_bind]
  unfold rfWrite
  by_cases hc : we.condTrue = true
  · simp only [hc, if_true, evalExpr2, readSignal, hwd, hwa, hm, resolveLhs2, Res.ok_bind]
    cases wa.toNat? with
    | none => rfl
    | some i => dsimp only; split <;> rfl
  · simp only [hc, Bool.false_eq_true, if_false]
    rfl

/-- The register file's state, as the closed form's parameter. -/
structure RFS where
  c : LVec
  we : LVec
  wa : LVec
  wd : LVec
  ra : LVec
  rd : LVec
  mem : LVec

def rfEnc (x : RFS) : SvState := RS x.c x.we x.wa x.wd x.ra x.rd x.mem

/-- The inputs held after stimulus entry `e`. -/
def rfIn (x : RFS) (e : SvState) : RFS :=
  { x with c := appIn e "clk" x.c, we := appIn e "we" x.we, wa := appIn e "waddr" x.wa,
           wd := appIn e "wdata" x.wd, ra := appIn e "raddr" x.ra }

/-- The pre sample: the inputs applied, the read port settled on the OLD memory. -/
def rfPre (W : Nat) (x : RFS) (e : SvState) : RFS :=
  { rfIn x e with rd := rfRead W x.mem (rfIn x e).ra }

/-- The post sample: the memory written, the read port settled again. -/
def rfPost (W : Nat) (x : RFS) (e : SvState) : RFS :=
  { rfIn x e with rd := rfRead W (rfWrite W x.mem (rfIn x e).we (rfIn x e).wa (rfIn x e).wd) (rfIn x e).ra,
                  mem := rfWrite W x.mem (rfIn x e).we (rfIn x e).wa (rfIn x e).wd }

/-- **The register file's closed-form cycle** (`REdgeRun2`, R-EDGE's `run2` form), from every state
whose `rdata` has width `W`, at every fuel from 4. -/
theorem rf_redge (A W : Nat) :
    REdgeRun2 (rfD A W) rfEnc (fun x => x.rd.width = W) (rfPre W) (rfPost W) 4 := by
  rintro σ e ⟨c, we, wa, wd, ra, rd, mem⟩ k f (hw : rd.width = W)
  simp only [rfEnc, rfPre, rfPost, rfIn]
  obtain ⟨k1, hs1⟩ := rf_settle (A := A) (by omega : 4 ≤ f + 4) σ (appIn e "clk" c)
    (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd) (appIn e "raddr" ra) rd mem k hw
  have hpre : cyclePre2 (rfD A W) σ (f + 4) e (RS c we wa wd ra rd mem) k =
      .ok (RS (appIn e "clk" c) (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd)
        (appIn e "raddr" ra) (rfRead W mem (appIn e "raddr" ra)) mem, k1) := by
    unfold cyclePre2
    rw [apply_rf, hs1, Res.ok_bind]
    exact resetPhase2_of_nil rfl
  refine ⟨⟨k1, hpre⟩, ?_⟩
  obtain ⟨k', hs2⟩ := rf_settle (A := A) (by omega : 4 ≤ f + 4) σ (appIn e "clk" c)
    (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd) (appIn e "raddr" ra)
    (rfRead W mem (appIn e "raddr" ra))
    (rfWrite W mem (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd)) (k1 + 1)
    (rfRead_width W _ _)
  refine ⟨k', ?_⟩
  rw [cycleStep2_eq_pre_post, hpre, Res.ok_bind]
  unfold cyclePost2
  rw [show (rfD A W).edgeIndices = [0] from rfl, σ.choose_singleton]
  have hedge := rf_edge (A := A) (W := W) (by omega : 3 ≤ f + 4) (appIn e "clk" c)
    (appIn e "we" we) (appIn e "waddr" wa) (appIn e "wdata" wd) (appIn e "raddr" ra)
    (rfRead W mem (appIn e "raddr" ra)) mem
  rw [Res.bind_eq_ok] at hedge
  obtain ⟨⟨st3, nba⟩, he3, hc3⟩ := hedge
  simp only [Res.ok.injEq] at hc3
  rw [he3, Res.ok_bind]
  simp only
  rw [hc3, hs2]

/-! ## A3. The cycle machine and R-CYCLE -/

/-- The register file's ports as a trusted sample (`mem` is internal). -/
def rfOut (W : Nat) {A : Nat} (s : Fin (2 ^ A) → LVec) (i : LVec × LVec × LVec × LVec × LVec) :
    PortSample :=
  ⟨[("clk", i.1), ("we", i.2.1), ("waddr", i.2.2.1), ("wdata", i.2.2.2.1), ("raddr", i.2.2.2.2),
    ("rdata", arrRead W s i.2.2.2.2)]⟩

/-- **The register file's cycle machine** (D6 with the D7 store): store = the array; held inputs =
`clk, we, waddr, wdata, raddr`; `out` reads the array at `raddr` (Mealy); `next` writes it. -/
def rfMachine (A W : Nat) : CycleMachine where
  Store := Fin (2 ^ A) → LVec
  In := LVec × LVec × LVec × LVec × LVec
  Tick := Unit
  init s := ∀ j, s j = LVec.xVec W
  out := rfOut W
  next s i _ := arrWrite W s i.2.1 i.2.2.1 i.2.2.2.1

/-- How a stimulus entry updates the held inputs (`applyInputs2`'s rule). -/
def rfHold (i : LVec × LVec × LVec × LVec × LVec) (e : SvState) :
    LVec × LVec × LVec × LVec × LVec :=
  (appIn e "clk" i.1, appIn e "we" i.2.1, appIn e "waddr" i.2.2.1, appIn e "wdata" i.2.2.2.1,
    appIn e "raddr" i.2.2.2.2)

/-- The held inputs before the first entry (`x`). -/
def rfI0 (A W : Nat) : LVec × LVec × LVec × LVec × LVec :=
  (LVec.xVec 1, LVec.xVec 1, LVec.xVec A, LVec.xVec W, LVec.xVec A)

theorem rf_sample (A W : Nat) (c we wa wd ra rd mem : LVec) :
    Obs_run2.sample (rfD A W) (RS c we wa wd ra rd mem) =
      ⟨[("clk", c), ("we", we), ("waddr", wa), ("wdata", wd), ("raddr", ra), ("rdata", rd)]⟩ := by
  rfl

/-- **R-CYCLE for the register file** (provisional over `run2`): every completed `Obs_run2`
behaviour of `rfD A W` is the array machine's run, from an all-`x` array, on the held inputs. -/
theorem rf_rcycle (A W : Nat) (hW : 1 ≤ W) :
    ∀ σ stim b, Obs_run2.Behaves (rfD A W) σ stim b →
      ∃ s, (rfMachine A W).init s ∧
        b = (rfMachine A W).run () s (heldInputs rfHold (rfI0 A W) stim) := by
  refine (rf_redge A W).rcycle (rfMachine A W) () rfHold (rfI0 A W)
    (fun x s i => (x.c, x.we, x.wa, x.wd, x.ra) = i ∧ Abs A W x.mem s)
    (x0 := ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec A, LVec.xVec W, LVec.xVec A, LVec.xVec W,
      LVec.xVec (2 ^ A * W)⟩) (s0 := fun _ => LVec.xVec W)
    (by simp [initState2, rfD, rfEnc, RS]) (by simp) (fun _ => rfl) ⟨rfl, by simp, fun j => ?_⟩ ?_
  · apply LVec.ext_getD (by simp)
    intro b hb
    simp only [LVec.width_extract] at hb
    simp only [LVec.extract, LVec.xVec, LVec.replicate, Array.getElem?_ofFn, Array.getElem?_replicate]
    split <;> split <;> simp
  · rintro ⟨c, we, wa, wd, ra, rd, mem⟩ s i e (hw : rd.width = W) ⟨rfl, habs⟩
    refine ⟨?_, ?_, rfRead_width W _ _, rfl, rfWrite_abs hW habs _ _ _⟩
    · simp only [rfEnc, rf_sample, rfPre, rfIn]
      rw [rfRead_eq hW habs]; rfl
    · simp only [rfEnc, rf_sample, rfPost, rfIn]
      rw [rfRead_eq hW (rfWrite_abs hW habs _ _ _)]; rfl

/-! ## Part B: the register-file task (DRAFT of trusted text) and its proof over `Obs_run2`

`rfTask` is a `PreTask`: parameters `(A, W)` (depth `2^A`, words of `W` bits). The spec state holds
`Option` words (`none` = never written, so no claim and no reset needed); a write with `we = 1`
stores `wdata` at `waddr`. The claim on the PRE sample: `rdata` is the word at `raddr` from the state
BEFORE the cycle's write. A read during a write of the same address returns the OLD word. The proof
is pure on the array machine (`rf_followsPreB`) and moved to the design by R-CYCLE. -/

/-- **The register-file task** (DRAFT). -/
def rfTask : PreTask (Nat × Nat) where
  inRange p := 1 ≤ p.2
  inType p := IntParam p.1 ∧ IntParam p.2
  clk := "clk"
  inputs p := [("we", 1), ("waddr", p.1), ("wdata", p.2), ("raddr", p.1)]
  outputs p := [("rdata", p.2)]
  State p := Fin (2 ^ p.1) → Option (BitVec p.2)
  init _ := fun _ => none
  step _ s := fun (we, wa, wd, _, ()) =>
    if we = 1#1 then (fun j => if j = ⟨wa.toNat, wa.isLt⟩ then some wd else s j) else s
  obs _ s := fun (_, _, _, ra, ()) => (s ⟨ra.toNat, ra.isLt⟩).map fun v => (v, ())

theorem rfOut_read (W : Nat) {A : Nat} (s : Fin (2 ^ A) → LVec) (c we wa wd ra : LVec) :
    (rfOut W s (c, we, wa, wd, ra)).read "we" = some we ∧
    (rfOut W s (c, we, wa, wd, ra)).read "waddr" = some wa ∧
    (rfOut W s (c, we, wa, wd, ra)).read "wdata" = some wd ∧
    (rfOut W s (c, we, wa, wd, ra)).read "raddr" = some ra ∧
    (rfOut W s (c, we, wa, wd, ra)).read "rdata" = some (arrRead W s ra) := by
  simp [rfOut, PortSample.read, SvState.lookup]

/-- **The register file's claim on its machine** (pure array algebra). -/
theorem rf_followsPreB (A W : Nat) :
    ∀ s0 is, rfTask.FollowsPreB (A, W) ((rfMachine A W).run () s0 is) := by
  refine rfTask.followsPreB_run (A, W) (rfMachine A W) ()
    (fun s q => ∀ a v, q a = some v → s a = LVec.ofBitVec v) (fun _ a v h => by cases h) ?_ ?_
  · rintro (s : Fin (2 ^ A) → LVec) ⟨c, we, wa, wd, ra⟩ (q : Fin (2 ^ A) → Option (BitVec W))
      ⟨vwe, vwa, vwd, vra, ⟨⟩⟩ out hR hin hobs
    obtain ⟨-, -, -, hra, hrd⟩ := rfOut_read W s c we wa wd ra
    have hra' : ra = LVec.ofBitVec vra := Option.some.inj (hra.symm.trans hin.2.2.2.1)
    cases hq : q ⟨vra.toNat, vra.isLt⟩ with
    | none => simp only [rfTask, hq, Option.map_none] at hobs; cases hobs
    | some v =>
        simp only [rfTask, hq, Option.map_some] at hobs
        cases hobs
        refine ⟨hrd.trans ?_, trivial⟩
        rw [hra']
        simp only [arrRead, LVec.toNat?_ofBitVec, dif_pos vra.isLt]
        exact congrArg some (hR _ _ hq)
  · rintro (s : Fin (2 ^ A) → LVec) ⟨c, we, wa, wd, ra⟩ (q : Fin (2 ^ A) → Option (BitVec W))
      ⟨vwe, vwa, vwd, vra, ⟨⟩⟩ hR hin
    obtain ⟨hwe, hwa, hwd, -, -⟩ := rfOut_read W s c we wa wd ra
    have e1 : we = LVec.ofBitVec vwe := Option.some.inj (hwe.symm.trans hin.1)
    have e2 : wa = LVec.ofBitVec vwa := Option.some.inj (hwa.symm.trans hin.2.1)
    have e3 : wd = LVec.ofBitVec vwd := Option.some.inj (hwd.symm.trans hin.2.2.1)
    subst e1 e2 e3
    show ∀ (a : Fin (2 ^ A)) (v : BitVec W),
      (if vwe = 1#1 then (fun j => if j = ⟨vwa.toNat, vwa.isLt⟩ then some vwd else q j) else q) a =
        some v → arrWrite W s (LVec.ofBitVec vwe) (LVec.ofBitVec vwa) (LVec.ofBitVec vwd) a =
          LVec.ofBitVec v
    intro a v hq
    simp only [arrWrite, LVec.condTrue_ofBitVec, LVec.toNat?_ofBitVec, dif_pos vwa.isLt,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rcases bv1_cases vwe with rfl | rfl
    · simp only [show ((0#1 : BitVec 1) = 1#1) = False by decide, if_false] at hq
      simp only [show decide ((0#1 : BitVec 1) ≠ 0#1) = false by decide, Bool.false_eq_true,
        if_false]
      exact hR a v hq
    · simp only [if_true] at hq
      simp only [show decide ((1#1 : BitVec 1) ≠ 0#1) = true by decide, if_true]
      by_cases ha : a = ⟨vwa.toNat, vwa.isLt⟩
      · rw [if_pos ha] at hq ⊢
        cases hq; rfl
      · rw [if_neg ha] at hq ⊢
        exact hR a v hq

/-- The all-`x` start state of `rfD A W`. -/
def rfX0 (A W : Nat) : RFS :=
  ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec A, LVec.xVec W, LVec.xVec A, LVec.xVec W, LVec.xVec (2 ^ A * W)⟩

theorem rf_terminates (A W : Nat) : Terminates2 (rfD A W) :=
  (rf_redge A W).terminates (x0 := rfX0 A W) (by simp [initState2, rfD, rfEnc, RS, rfX0])
    (by simp [rfX0]) (fun _ _ _ => rfRead_width W _ _) rfl

/-- **The register file satisfies its task over `Obs_run2`** at every `(A, W)` with `W ≥ 1`
(provisional over `run2`): ports, the clock discipline (`ClockedBy`), progress, receptiveness (the
library theorem), and the claim on the pre samples. -/
theorem rf_satisfiedAt_obs (A W : Nat) (hW : 1 ≤ W) :
    rfTask.SatisfiedAt_obs Obs_run2 (ClockedBy "clk" none) (A, W) (rfD A W) := by
  refine ⟨rfl, ⟨?_, Obs_run2.progress_of_terminates _ _ (rf_terminates A W),
    receptive_of_writesInput rfl (rf_terminates A W) ?_ ?_⟩, ?_⟩
  · simp [ClockedBy, rfD, Design2.inputNames, Process2.isEdgePhase, Process2.clock?,
      Process2.resetName?, Process2.mentionsData, Stmt2.mentions, Stmt2.mentionsOpt, Lhs2.mentions,
      Expr2.idents]
  · intro p hp
    simp only [rfTask, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [Design2.inputNames, rfD]
  · simp [rfTask]
  · exact Obs_run2.safe_of_rcycle (rfMachine A W) () rfHold (rfI0 A W) (rf_rcycle A W hW)
      (Q := fun _ b => rfTask.FollowsPreB (A, W) b) fun s _ is => rf_followsPreB A W s is

/-- **The register file satisfies the Task v2 skeleton** (`Sat` of `rfTask.toSpec`), provisional over
`run2`. -/
theorem rf_sat : Sat Obs_run2 (ClockedBy "clk" none) rfTask.toSpec fun p => rfD p.1 p.2 :=
  fun p hp _ => rfTask.satisfiedAt_obs_iff_satAt.mp (rf_satisfiedAt_obs p.1 p.2 hp)

#print axioms rf_redge
#print axioms rf_rcycle
#print axioms rf_followsPreB
#print axioms rf_terminates
#print axioms rf_satisfiedAt_obs
#print axioms rf_sat

end SvGolf.Arch.RF
