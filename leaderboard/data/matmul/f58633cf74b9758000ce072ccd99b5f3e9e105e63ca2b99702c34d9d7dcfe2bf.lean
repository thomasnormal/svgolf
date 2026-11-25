-- svgolf-latency: 4
-- MAINTAINER PORT (2026-11-19): the svGolf maintainers' port of the player's proof to the checker at Proglib 4fcda4c8 (Lean v4.35.0); the design is the player's, byte for byte. The player's proof was written for an earlier checker and is refused at this one. What changed versus the player's file: the instantiation is taken from svGolf's generator sv_mirror instead of the hand-written stages of instantiate2 (the agreement mm_sem_eq re-proved from it), a range hypothesis hR32 threaded to its users, the one-clock guard passed to Terminates2.of_invariant, and the destructuring of matmul's range (1 ≤ N < 2^5, 1 ≤ W < 2^10, 1 ≤ AccW < 2^12) in `solution`, which derives hR32; the rest of the proof is unchanged.
-- range of 2026-11-19 (1 ≤ N ≤ 256, W ≤ 127, AccW ≤ 64): the destructuring of inRange in `solution`, and the two port-width bounds it derives, N * N * W < 2 ^ 31 and N * N * AccW < 2 ^ 31, from the new bounds (256 * 256 * 127 and 256 * 256 * 64); the rest of the proof unchanged
import Submission.Design
import SvGolf.Cycle
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.BitVecArith
import LeanModels.Sv.CombViewArith
import LeanModels.Sv.Mono2
import SvGolf.SeqV2

/-!
# G16: local-weight output cores with a shifted B feeder

On `start`, `reference/matmul_g1.sv` captures `A`, `B` into shift registers and clears `C`; for `N`
busy cycles PE `(i, j)` adds `A[i][k]·B[k][j]` (sign-extended, mod `2^AccW`); `done` shows in the
snapshot `N` cycles after the start's (`lat = N`). Proved at every in-range `(N, W, AccW)`:
1. **Agreement** (`mm_sem_eq`): the loaded family `design.sem N W AccW` is the hand-built `mmD`.
2. **G0's clock step** (`mm_profile`, `mm_cycle`): one cycle of the loaded design, from any state
   of its shape, any schedule, is the evaluated commit `mmNext`.
3. **The invariant on `k`** (`pe_step`, `next_step`): busy cycle `t` turns every accumulator's
   `Σ_{k' < t} A[i][k']·B[k'][j]` into the sum to `t + 1`, mod `2^AccW` (`accC`).
4. **The spec's arithmetic** (`product_eq`, `accC_N`): `product` is `accC` at `t = N`.
5. **The protocol** (`model`): the phases of `TxTask.satisfiedAt_of_phases`.
6. **txtask-v2** (section 8): rule 2 (`mm_powerUp`: every power-up state has the model's shape, so
   the claim and termination hold from every power-up), rule 1 (`mm_moore`: every process an
   `always_ff`, so no combinational dependency) and rule 3 (`mm_xsafe`), then `solution`.

The design-independent lemmas are in the library: the packed view and its commit (`packBV`,
`LVec.insertEntries_ofBitVec`) in `LeanModels.Sv.SeqFamily`, the clock step (`ffDisjB_of_pairwise`,
`flatMap_ffUpd`) in `LeanModels.Sv.SeqProfile`, the window arithmetic and the datapath's `BitVec` facts in
`LeanModels.Sv.Lib.NatArith` and `LeanModels.Sv.Lib.BitVecArith`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `N` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- A local-weight output core at `(i,j)`. -/
def mmPE (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[.nbaAssign (.slice "w_cur" ((i * N + j) * W) W) (.lit (LVec.replicate W .l0)),
      .nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0))])
    (some (.ifStmt (.ident "start")
      (.block #[.nbaAssign (.slice "w_cur" ((i * N + j) * W) W) (.slice (.ident "B") (j * W) W),
        .nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.slice "w_cur" ((i * N + j) * W) W) (.slice (.ident "b_next") (j * W) W),
          .nbaAssign (.slice "C" ((i * N + j) * AccW) AccW)
            (.resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "C") ((i * N + j) * AccW) AccW))
              (.binary .mul (sext "a_sh" AccW (i * N * W) W)
                (sext "w_cur" AccW ((i * N + j) * W) W))))]) none)))))

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- The control: `busy`, `done`, the step counter, and the A/B feeders. -/
def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "a_sh") (.ident "A"),
        .nbaAssign (.ident "b_next") (.binary (.shr false) (.ident "B") (.binary .mul (c32 N) (c32 W)))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "k") (.binary .add (.ident "k") (c32 1)),
          .nbaAssign (.ident "a_sh") (.binary (.shr false) (.ident "a_sh") (c32 W)),
          .nbaAssign (.ident "b_next") (.binary (.shr false) (.ident "b_next") (.binary .mul (c32 N) (c32 W))),
          .ifStmt (.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The declarations, `A`/`B`/`a_sh`/`b_next` at `wa` bits and `C` at `wc`. -/
def mmDecls (wa wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "k", width := 32 },
   { name := "busy", width := 1 }, { name := "a_sh", width := wa }, { name := "b_next", width := wa },
   { name := "w_cur", width := wa }]

/-- The PEs, row-major. -/
def mmPEs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => mmPE N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * N * AccW)).toArray
  processes := (mmCtrl N W :: mmPEs N W AccW).toArray

theorem pe_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ a ∈ (mmPE N W AccW i j).procWins, ∀ b ∈ (mmPE N W AccW i' j').procWins,
      a.overlaps b = false := by
  have hA := rowMajor_le (K := AccW) h
  have hW := rowMajor_le (K := W) h
  simp [mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    DrvWin.overlaps_some_eq_false]
  all_goals omega

theorem mm_pe_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPEs N W AccW) :
    ∃ i j, p = mmPE N W AccW i j := by
  simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, j, -, rfl⟩ := hp
  exact ⟨i, j, rfl⟩

/-- The control and the PEs drive pairwise disjoint windows. -/
theorem mm_pairwise (N W AccW : Nat) : (mmCtrl N W :: mmPEs N W AccW).Pairwise
    fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false := by
  refine List.Pairwise.cons (fun p hp => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)
  · obtain ⟨i, j, rfl⟩ := mm_pe_mem hp
    simp [mmCtrl, mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins]
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ h => pe_disj (by omega))
  · intro i i' hii _ a ha b hb
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨j', -, rfl⟩ := hb
    exact pe_disj (by have := rowMajor_le (K := N) hii; omega)

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mmCtrl N W :: mmPEs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hp; exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, List.mem_cons]
    rintro n ⟨p, hp | hp, hn⟩
    all_goals first | subst hp | obtain ⟨i, j, rfl⟩ := mm_pe_mem hp
    all_goals revert n; simp [mmCtrl, mmPE, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide

/-- (port) The exact 32-bit `int` instantiation: the parameters' ranges (`N < 46341` from `N * N * W < 2^31`). -/
abbrev Rng32 (N W AccW : Nat) : Prop := N < 46341 ∧ W < 2147483648 ∧ AccW < 2147483648

/-- (port) The statement's range gives it. -/
theorem rng32_of {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31)
    (hNA : N * N * AccW < 2 ^ 31) : Rng32 N W AccW := by
  have h2 := Nat.le_mul_of_pos_right (N * N) hW
  have h3 := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  have h4 := Nat.le_mul_of_pos_left AccW (Nat.mul_pos hN hN)
  refine ⟨Nat.lt_of_not_le fun h => ?_, by omega, by omega⟩
  have := Nat.mul_le_mul h h
  omega

-- (port) The instantiation, generated.
sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hN46 : N < 46341)

/-- (port) The generated mirror is the hand-built one. -/
theorem mmG_D (N W AccW : Nat) : mmG.D N W AccW = mmD N W AccW := by
  have hg : mmG.g_core N W AccW = fun i j => mmPE N W AccW i j := by
    funext i j; simp [mmG.g_core, mmPE, sext, LVec.ofInt_eq_ofBitVec]
  simp [mmG.D, mmD, mmG.decls, mmDecls, mmG.procs, mmPEs, mmG.p0, mmCtrl, LVec.ofInt_eq_ofBitVec, hg]

/-- **The loaded family is `mmD`** (port: from the generated instantiation, `SvGolf.Cycle.sem_eq_of_mirror`). -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    design.sem N W AccW = mmD N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror (mmG.instantiate N W AccW hN hW hA (by have := hR32.1; omega) hR32.2.1 hR32.2.2 hR32.1) (mmG_D N W AccW)
    (by simpa [mmD] using mm_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by simp [mmD, mmCtrl, mmPEs, mmPE, List.all_flatMap, List.all_map,
      SvGolf.Cycle.notComb]))

/-! ## 2. G0's clock step for the loaded family, at every `(N, W, AccW)` -/

/-- **`mmD` is in G0's decidable FF-only profile at every `(N, W, AccW)`** (symbolic, not `rfl`). -/
theorem mm_profile (N W AccW : Nat) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simpa [mmD] using mm_pairwise N W AccW)⟩
  simp [mmD, mmCtrl, mmPEs, mmPE, nb, List.all_flatMap, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, mmDecls]

/-- The 11 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c k bz ash bsh wc : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("k", k),
    ("busy", bz), ("a_sh", ash), ("b_next", bsh), ("w_cur", wc)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz ash bsh wc : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c k bz ash bsh wc) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz ash bsh wc := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

def ctrlQ (N W : Nat) (r s a b dn k bz ash bsh : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "k" k (LVec.replicate 32 .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩,
    wr "k" k (LVec.replicate 32 .l0), wr "a_sh" ash a,
    wr "b_next" bsh (b.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))]
  else if bz.condTrue then
    if (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue then
      [wr "k" k (k.add (LVec.ofInt 32 1)), wr "a_sh" ash (ash.shr (LVec.ofInt 32 (W : Int))),
        wr "b_next" bsh (bsh.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))),
        wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
    else [wr "k" k (k.add (LVec.ofInt 32 1)), wr "a_sh" ash (ash.shr (LVec.ofInt 32 (W : Int))),
      wr "b_next" bsh (bsh.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))]
  else []

def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

def peV (N W AccW i j : Nat) (c ash wc : LVec) : LVec :=
  (((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
    ((sxv ash AccW (i * N * W) W).mul (sxv wc AccW ((i * N + j) * W) W))).resizeU AccW

def peQ (N W AccW : Nat) (r s bz b c ash bsh wc : LVec) (i j : Nat) : NbaQueue2 :=
  if r.condTrue then [("w_cur", (i * N + j) * W, (LVec.replicate W .l0).resizeU W),
    ("C", (i * N + j) * AccW, (LVec.replicate AccW .l0).resizeU AccW)]
  else if s.condTrue then [("w_cur", (i * N + j) * W, b.extract (j * W) W),
    ("C", (i * N + j) * AccW, (LVec.replicate AccW .l0).resizeU AccW)]
  else if bz.condTrue then [("w_cur", (i * N + j) * W, bsh.extract (j * W) W),
    ("C", (i * N + j) * AccW, (peV N W AccW i j c ash wc).resizeU AccW)]
  else []

theorem ctrl_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh wc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh wc) [] (mmCtrl N W) =
      .ok (MS ck r s a b dn c k bz ash bsh wc, ctrlQ N W r s a b dn k bz ash bsh) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [mmCtrl, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem pe_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh wc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh wc) [] (mmPE N W AccW i j) =
      .ok (MS ck r s a b dn c k bz ash bsh wc, peQ N W AccW r s bz b c ash bsh wc i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold peQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    simp [mmPE, sext, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, peV, sxv, h1, h2, h3]
  all_goals simp only [LVec.resizeU_of_width (LVec.width_extract _ _ _)]

def mmNext (N W AccW : Nat) (ck r s a b dn c k bz ash bsh wc : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c k bz ash bsh wc)
    (ctrlQ N W r s a b dn k bz ash bsh ++
      (List.range N).flatMap fun i => (List.range N).flatMap
        (peQ N W AccW r s bz b c ash bsh wc i))

theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c k bz ash bsh wc : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c k bz ash bsh wc) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c k bz ash bsh wc, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm; rfl
  rw [mm_sem_eq N W AccW hN hW hA hR32, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD, List.toList_toArray, List.flatMap_cons, ctrl_run N W F hF, mmPEs, List.flatMap_assoc,
      List.flatMap_map, pe_run N W AccW _ _ F hF, mmNext]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ mmCtrl N W :: mmPEs N W AccW :=
      List.mem_of_getElem? (by simpa [mmD] using hp : (mmCtrl N W :: mmPEs N W AccW)[i]? = some p)
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ctrl_run N W F hF _ _ _ _ _ _ _ _ _ _ _ _⟩
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm
      exact ⟨_, pe_run N W AccW i j F hF _ _ _ _ _ _ _ _ _ _ _ _⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The busy cycle on known values: the invariant on `k` -/

attribute [local simp] condTrue_knownBit

/-- `Σ_{k' < t} A[i][k']·B[k'][j]` in the integers (`Tasks.Matmul.dot` at `t = N`). -/
def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

/-- The accumulators after `t` busy cycles: entry `(i, j)` is `psum t i j` mod `2^AccW`. -/
def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r => BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

/-! Each output core carries the B word for its current inner-product row. -/
def localWeight (N W : Nat) (B : BitVec (N * N * W)) (t : Nat) : BitVec (N * N * W) :=
  packBV W (N * N) fun r => BitVec.extractLsb' ((t * N + r % N) * W) W B

theorem localWeight_extract {N W : Nat} (B : BitVec (N * N * W)) (t r : Nat)
    (hr : r < N * N) :
    BitVec.extractLsb' (r * W) W (localWeight N W B t) =
      BitVec.extractLsb' ((t * N + r % N) * W) W B := by
  unfold localWeight
  exact extractLsb'_packBV _ hr

theorem localWeight_cell {N W : Nat} (B : BitVec (N * N * W)) (t i j : Nat)
    (hi : i < N) (hj : j < N) :
    BitVec.extractLsb' ((i * N + j) * W) W (localWeight N W B t) =
      BitVec.extractLsb' ((t * N + j) * W) W B := by
  have hr : i * N + j < N * N := by
    have h := Lib.rowMajor_window_le (M := N) (N := N) (w := 1) hi hj
    omega
  rw [localWeight_extract B t (i * N + j) hr]
  have hm : (i * N + j) % N = j := by
    rw [Nat.mul_comm i N, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp [hm]

theorem localWeight_sign {N W : Nat} (hW : 1 ≤ W) (B : BitVec (N * N * W)) (t r : Nat)
    (hr : r < N * N) :
    BitVec.extractLsb' (r * W + W - 1) 1 (localWeight N W B t) =
      BitVec.extractLsb' ((t * N + r % N) * W + W - 1) 1 B := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  have hq0 : q = 0 := by omega
  subst q
  simp only [BitVec.getLsbD_extractLsb']
  have hword := localWeight_extract B t r hr
  have hbits := congrArg (fun x : BitVec W => x.getLsbD (W - 1)) hword
  simp only [BitVec.getLsbD_extractLsb'] at hbits
  have hWlt : W - 1 < W := by omega
  simp [hWlt] at hbits
  rw [Nat.add_sub_assoc (by omega), Nat.add_sub_assoc (by omega)]
  exact hbits

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 1) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

/-! The local-weight busy-step theorem is proved below, after the paired queue model. -/

/-! The registered local-weight PE truncates one widened signed product. -/
theorem setWidth_add_mul_signExtend {m n w : Nat} (h : m ≤ n) (x : BitVec m)
    (a b : BitVec w) :
    (x.setWidth n + a.signExtend n * b.signExtend n).setWidth m =
      x + BitVec.ofInt m (a.toInt * b.toInt) := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    BitVec.setWidth_mul _ _ h, Lib.setWidth_signExtend_of_le _ h,
    Lib.setWidth_signExtend_of_le _ h, BitVec.ofInt_mul]
  rfl

/-! ## 4. The spec's arithmetic: `product` is the packed vector of the wrapped dot products -/

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- After `N` busy cycles the accumulators hold the product (`psum N` is `dot`). -/
theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

/-! ## 5. The registers through a cycle: the commit, then the invariant on `k` -/

section commit
variable {ck r s a b dn c k bz ash bsh wc : LVec} {lo : Nat} {v : LVec}
theorem nb_busy : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("busy", lo, v) =
    MS ck r s a b dn c k (bz.insertAt lo v) ash bsh wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_done : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c k bz ash bsh wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_k : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("k", lo, v) =
    MS ck r s a b dn c (k.insertAt lo v) bz ash bsh wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ash : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("a_sh", lo, v) =
    MS ck r s a b dn c k bz (ash.insertAt lo v) bsh wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bsh : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("b_next", lo, v) =
    MS ck r s a b dn c k bz ash (bsh.insertAt lo v) wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_wcur : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("w_cur", lo, v) =
    MS ck r s a b dn c k bz ash bsh (wc.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_C : nbaStep (MS ck r s a b dn c k bz ash bsh wc) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) k bz ash bsh wc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- Commit a queue of C writes, leaving the other packed registers unchanged. -/
theorem commit_C {ck r s a b dn k bz ash bsh wc : LVec} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 = "C") → ∀ c,
    commitNba2 (MS ck r s a b dn c k bz ash bsh wc) q =
      MS ck r s a b dn (q.foldl (fun acc u => acc.insertAt u.2.1 u.2.2) c) k bz ash bsh wc
  | [], _, _ => rfl
  | ⟨n, lo, v⟩ :: q, h, c => by
    obtain rfl : n = "C" := h _ List.mem_cons_self
    rw [commitNba2_cons, List.foldl_cons, ← commit_C (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    rw [nb_C]

/-- Commit a queue of paired local-weight and C writes. -/
theorem commit_pair (wlo clo : Nat → Nat) (wv cv : Nat → LVec) : ∀ (l : List Nat) (c wc : LVec),
    commitNba2 (MS ck r s a b dn c k bz ash bsh wc)
      (l.flatMap fun x => [("w_cur", wlo x, wv x), ("C", clo x, cv x)]) =
      MS ck r s a b dn
        (l.foldl (fun z x => z.insertAt (clo x) (cv x)) c) k bz ash bsh
        (l.foldl (fun z x => z.insertAt (wlo x) (wv x)) wc) := by
  intro l
  induction l with
  | nil => intro c wc; rfl
  | cons x l ih =>
    intro c wc
    simp only [List.flatMap_cons, commitNba2_append, commitNba2_nil]
    rw [commitNba2_cons, nb_wcur, commitNba2_cons, nb_C, commitNba2_nil]
    rw [ih]
    simp [List.foldl]

/-- The PEs' paired updates, row-major. -/
theorem rowMajor_pair {N AccW W : Nat} {q : Nat → Nat → NbaQueue2}
    (gW gC : Nat → Nat) (vw vc : Nat → LVec)
    (h : ∀ i j, i < N → j < N → q i j = [("w_cur", gW (i * N + j), vw (i * N + j)),
      ("C", gC (i * N + j), vc (i * N + j))]) :
    (List.range N).flatMap (fun i => (List.range N).flatMap (q i)) =
      (List.range (N * N)).flatMap (fun r => [("w_cur", gW r, vw r), ("C", gC r, vc r)]) := by
  suffices ∀ M, M ≤ N →
      (List.range M).flatMap (fun i => (List.range N).flatMap (q i)) =
        (List.range (M * N)).flatMap (fun r => [("w_cur", gW r, vw r), ("C", gC r, vc r)]) from this N (Nat.le_refl _)
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [CombView.flatMap_congr' fun j hj => h M j (by omega) (List.mem_range.mp hj)]
    congr 1
    induction (List.range N) with
    | nil => rfl
    | cons a l ih' => rw [List.flatMap_cons, ih']; rfl


/-- The control in a busy cycle `t < N`: `k` and the shift registers step. -/
theorem peQ_flat (N W AccW : Nat) (r s bz b c ash bsh wc : LVec) :
    (List.range N).flatMap (fun i => (List.range N).flatMap (peQ N W AccW r s bz b c ash bsh wc i)) =
      if r.condTrue then
        (List.range (N * N)).flatMap (fun q =>
          [("w_cur", q * W, (LVec.replicate W .l0).resizeU W),
           ("C", q * AccW, (LVec.replicate AccW .l0).resizeU AccW)])
      else if s.condTrue then
        (List.range (N * N)).flatMap (fun q =>
          [("w_cur", q * W, b.extract ((q % N) * W) W),
           ("C", q * AccW, (LVec.replicate AccW .l0).resizeU AccW)])
      else if bz.condTrue then
        (List.range (N * N)).flatMap (fun q =>
          [("w_cur", q * W, bsh.extract ((q % N) * W) W),
           ("C", q * AccW, (peV N W AccW (q / N) (q % N) c ash wc).resizeU AccW)])
      else [] := by
  by_cases hr : r.condTrue = true
  · rw [rowMajor_pair (N := N) (AccW := AccW) (W := W)
      (q := peQ N W AccW r s bz b c ash bsh wc)
      (fun q => q * W) (fun q => q * AccW)
      (fun _ => (LVec.replicate W .l0).resizeU W)
      (fun _ => (LVec.replicate AccW .l0).resizeU AccW)
      (fun i j hi hj => by simp [peQ, hr])]
    simp [hr]
  · by_cases hs : s.condTrue = true
    · rw [rowMajor_pair (N := N) (AccW := AccW) (W := W)
        (q := peQ N W AccW r s bz b c ash bsh wc)
        (fun q => q * W) (fun q => q * AccW)
        (fun q => b.extract ((q % N) * W) W)
        (fun _ => (LVec.replicate AccW .l0).resizeU AccW)
        (fun i j hi hj => by have hm : j % N = j := Nat.mod_eq_of_lt hj; simp [peQ, hr, hs, hm])]
      simp [hr, hs]
    · by_cases hb : bz.condTrue = true
      · rw [rowMajor_pair (N := N) (AccW := AccW) (W := W)
          (q := peQ N W AccW r s bz b c ash bsh wc)
          (fun q => q * W) (fun q => q * AccW)
          (fun q => bsh.extract ((q % N) * W) W)
          (fun q => (peV N W AccW (q / N) (q % N) c ash wc).resizeU AccW)
          (fun i j hi hj => by
            have hm : j % N = j := Nat.mod_eq_of_lt hj
            have hd : (i * N + j) / N = i := by
              rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
            simp [peQ, hr, hs, hb, hm, hd])]
        simp [hr, hs, hb]
      · simp [peQ, hr, hs, hb]


theorem ctrl_busy {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t < N) (ck a b c : LVec) (wc : LVec) :
    commitNba2 (MS ck (knownBit false) (knownBit false) a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) (LVec.ofBitVec (A >>> (t * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) wc)
      (ctrlQ N W (knownBit false) (knownBit false) a b (knownBit false) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (A >>> (t * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W))))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N))) c (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
      (knownBit (decide (t + 1 ≠ N))) (LVec.ofBitVec (A >>> (t * W + W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W) + N * W))) wc := by
  have hNW0 : N * W ≤ N * N * W := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hN
  have hNW : N * W < 2 ^ 32 := by simp only [Nat.reducePow] at hr ⊢; omega
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW', Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW]
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [ctrlQ, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
    BitVec.ofInt_natCast, BitVec.ofInt_ofNat, h1', LVec.mul_ofBitVec, LVec.sub_ofBitVec,
    LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq, Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN'),
    LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW, ← BitVec.shiftRight_add]
  by_cases hf : t + 1 = N <;>
    simp [hf, commitNba2_cons, commitNba2_nil, nb_k, nb_ash, nb_bsh, nb_busy, nb_done,
      LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1, BitVec.ofNat_add_ofNat]

/-- A PE cycle updates its local weight and accumulator. -/
theorem pe_step {N W AccW : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {t i j : Nat}
    (hi : i < N) (hj : j < N) :
    peQ N W AccW (knownBit false) (knownBit false) (knownBit true)
      (LVec.ofBitVec B) (accC N W AccW A B t) (LVec.ofBitVec (A >>> (t * W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) (LVec.ofBitVec (localWeight N W B t)) i j =
      [("w_cur", (i * N + j) * W, (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract (j * W) W),
       ("C", (i * N + j) * AccW,
        LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 1) ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hcellW : (i * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le (w := W) hi hj
  have ha : i * N * W + W ≤ N * N * W := by have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
  have hb : j * W + W ≤ N * N * W := by have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj; simpa using this
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have hsign := localWeight_sign hW B t (i * N + j) hr
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  simp (disch := omega) only [peQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, peV, sxv, accC,
    LVec.extract_ofBitVec, extractLsb'_packBV, localWeight_cell, hsign, hd, hm, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.resizeU_of_width (LVec.width_resizeU _ _),
    LVec.resizeU_of_width (LVec.width_extract _ _ _), LVec.add_ofBitVec, BitVec.setWidth_eq,
    setWidth_add_mul_signExtend,
    Lib.extractLsb'_ushiftRight, e1, e2, psum_succ, BitVec.ofInt_add, Tasks.Matmul.entry]

/-- The invariant on `k`, one step. -/
theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a : LVec) (wc : LVec)
    (hwc : wc = LVec.ofBitVec (localWeight N W B t)) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a (LVec.ofBitVec B) (knownBit false) (accC N W AccW A B t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec (A >>> (t * W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) wc =
    MS ck (knownBit false) (knownBit false) a (LVec.ofBitVec B) (knownBit (decide (t + 1 = N))) (accC N W AccW A B (t + 1))
      (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ N))) (LVec.ofBitVec (A >>> ((t + 1) * W)))
      (LVec.ofBitVec (B >>> ((t + 2) * (N * W))))
      (LVec.insertEntries W (fun r => (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract ((r % N) * W) W) (N * N) wc) := by
  have hq := rowMajor_pair (N := N) (AccW := AccW) (W := W)
    (q := peQ N W AccW (knownBit false) (knownBit false) (knownBit true)
      (LVec.ofBitVec B) (accC N W AccW A B t) (LVec.ofBitVec (A >>> (t * W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) (LVec.ofBitVec (localWeight N W B t)))
    (fun r => r * W) (fun r => r * AccW)
    (fun r => (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract ((r % N) * W) W)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 1) (r / N) (r % N))))
    (fun i j hi hj => by
      have hm : (i * N + j) % N = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      simpa [hm] using (pe_step (AccW := AccW) hW A B hi hj))
  rw [hwc, mmNext, commitNba2_append,
    ctrl_busy hN hW hr A B ht ck a (LVec.ofBitVec B) (accC N W AccW A B t)
      (LVec.ofBitVec (localWeight N W B t)), hq]
  rw [commit_pair]
  change MS ck (knownBit false) (knownBit false) a (LVec.ofBitVec B)
      (knownBit (decide (t + 1 = N)))
      (LVec.insertEntries AccW (fun r => LVec.ofBitVec (BitVec.ofInt AccW
        (psum N W A B (t + 1) (r / N) (r % N)))) (N * N) (accC N W AccW A B t))
      (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ N)))
      (LVec.ofBitVec (A >>> (t * W + W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W) + N * W)))
      (LVec.insertEntries W (fun r =>
        (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract (r % N * W) W) (N * N)
        (LVec.ofBitVec (localWeight N W B t))) = _
  rw [LVec.insertEntries_ofBitVec
    (fun r => BitVec.ofInt AccW (psum N W A B (t + 1) (r / N) (r % N)))
    (accC N W AccW A B t) (by simp [accC])]
  simp [accC, Nat.succ_mul, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem feed_eq_localWeight {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (B : BitVec (N * N * W))
    (t : Nat) (wc0 : LVec) (hwc0 : wc0.width = N * N * W) :
    LVec.insertEntries W
        (fun r => (LVec.ofBitVec (B >>> (t * (N * W)))).extract ((r % N) * W) W)
        (N * N) wc0 = LVec.ofBitVec (localWeight N W B t) := by
  have hfun : (fun r => (LVec.ofBitVec (B >>> (t * (N * W)))).extract ((r % N) * W) W) =
      (fun r => LVec.ofBitVec (BitVec.extractLsb' ((t * N + r % N) * W) W B)) := by
    funext r
    have hN0 : 0 < N := by omega
    have hrN : r % N < N := Nat.mod_lt r hN0
    have hbound : (r % N) * W + W ≤ N * N * W := by
      simpa [Nat.zero_mul, Nat.zero_add] using (Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (j := r % N)
        (by omega) hrN)
    rw [LVec.extract_ofBitVec _ hbound, Lib.extractLsb'_ushiftRight]
    have heq : t * (N * W) + r % N * W = (t * N + r % N) * W := by
      calc
        t * (N * W) + r % N * W = (t * N) * W + r % N * W := by rw [Nat.mul_assoc]
        _ = (t * N + r % N) * W := by rw [Nat.add_mul]
    exact congrArg LVec.ofBitVec (congrArg (fun q : Nat => BitVec.extractLsb' q W B) heq)
  rw [hfun, LVec.insertEntries_ofBitVec
    (fun r => BitVec.extractLsb' ((t * N + r % N) * W) W B) wc0 hwc0]
  rfl

/-! ## 6. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c k bz ash bsh wc : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧ ash.width = N * N * W ∧
    bsh.width = N * N * W ∧ wc.width = N * N * W

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh wc, st = MS ck r s a b dn c k bz ash bsh wc ∧ Wd N W AccW dn c k bz ash bsh wc

theorem width_update_fold {K : Nat} (f : Nat → LVec) :
    ∀ (xs : List Nat) (z : LVec),
      (xs.foldl (fun z x => z.insertAt (x * K) (f x)) z).width = z.width
  | [], z => rfl
  | x :: xs, z => by
      rw [List.foldl_cons]
      simpa using width_update_fold f xs (z.insertAt (x * K) (f x))

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz ash bsh wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bsh wc) :
    I N W AccW (mmNext N W AccW ck r s a b dn c k bz ash bsh wc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  have hIdle : I N W AccW (MS ck r s a b dn c k bz ash bsh wc) := by
    exact ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, h1, h2, h3, h4, h5, h6, h7⟩
  rw [mmNext, commitNba2_append, peQ_flat]
  by_cases c1 : r.condTrue = true <;> by_cases c2 : s.condTrue = true <;> by_cases c3 : bz.condTrue = true <;>
    by_cases c4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp only [ctrlQ, c1, c2, c3, c4, Bool.false_eq_true, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy, nb_done, nb_k,
      nb_ash, nb_bsh, wr] <;>
    try rw [commit_pair] <;>
    first
    | exact hIdle
    | exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl,
      by
        have hC : ∀ (f : Nat → LVec),
            (List.foldl (fun z x => z.insertAt (x * AccW) (f x)) c
              (List.range (N * N))).width = c.width :=
          fun f => width_update_fold f (List.range (N * N)) c
        have hW : ∀ (f : Nat → LVec),
            (List.foldl (fun z x => z.insertAt (x * W) (f x)) wc
              (List.range (N * N))).width = wc.width :=
          fun f => width_update_fold f (List.range (N * N)) wc
        simp [Wd, hC, hW, *]⟩
  all_goals exact hIdle

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmCtrl, mmPEs, mmPE, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
    Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * W), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-- **Termination**: every schedule and every stimulus completes. -/
theorem mm_terminates (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Terminates2 (design.sem N W AccW) := by
  refine Terminates2.of_invariant (I N W AccW) (mm_init N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
    (run2ClockGuard_ok_of_profile (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_profile N W AccW))
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz ash bsh wc kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh wc hw⟩

/-! ## 7. The protocol: the phases of `TxTask.satisfiedAt_of_phases`, and the statement -/

set_option maxHeartbeats 1000000

theorem MS_inj {ck r s a b dn c k bz ash bsh wc ck' r' s' a' b' dn' c' k' bz' ash' bsh' wc' : LVec}
    (h : MS ck r s a b dn c k bz ash bsh wc = MS ck' r' s' a' b' dn' c' k' bz' ash' bsh' wc') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ ash = ash' ∧ bsh = bsh' ∧ wc = wc' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- A cycle without `rst` and `start` from an idle state (`busy` = 0) changes no register. -/
theorem next_idle (N W AccW : Nat) (ck a b dn c k ash bsh wc : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bsh wc =
      MS ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bsh wc := by
  have h : ((List.range N).flatMap fun i => (List.range N).flatMap
      (peQ N W AccW (knownBit false) (knownBit false) (knownBit false) b c ash bsh wc i)) = [] := by
    simp [List.flatMap_eq_nil_iff, peQ]
  rw [mmNext, h]; simp [ctrlQ]; rfl

/-- A reset cycle clears `busy` and `done`. -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz ash bsh wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bsh wc) :
    ∃ c' k', mmNext N W AccW ck (knownBit true) s a b dn c k bz ash bsh wc =
      MS ck (knownBit true) s a b (knownBit false) c' k' (knownBit false) ash bsh
        (LVec.insertEntries W (fun _ => LVec.replicate W .l0) (N * N) wc) := by
  obtain ⟨h1, -, -, h4, -, -, -⟩ := hw
  rw [mmNext, commitNba2_append, peQ_flat]
  simp only [ctrlQ, condTrue_knownBit, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, wr, h1, h4, LVec.resizeU_one_l0]
  rw [commit_pair]
  let c' := List.foldl (fun z x => z.insertAt (x * AccW) ((LVec.replicate AccW .l0).resizeU AccW)) c
    (List.range (N * N))
  let k' := k.insertAt 0 ((LVec.replicate 32 .l0).resizeU k.width)
  refine ⟨c', k', ?_⟩
  simp [c', k', LVec.insertEntries, LVec.insertAt_zero_of_width_eq, h1, h4]

/-- A start cycle captures the operands and clears the accumulators: the state at `t = 0`. -/
theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hNW : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) (ck dn c k bz ash bsh wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bsh wc) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn c k bz ash bsh wc =
      MS ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false) (accC N W AccW A B 0)
        (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true) (LVec.ofBitVec (A >>> (0 * W)))
        (LVec.ofBitVec (B >>> (N * W)))
        (LVec.insertEntries W (fun r => (LVec.ofBitVec B).extract ((r % N) * W) W) (N * N) wc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  have hq := rowMajor_pair (N := N) (AccW := AccW) (W := W)
    (q := peQ N W AccW (knownBit false) (knownBit true) bz (LVec.ofBitVec B) c ash bsh wc)
    (fun r => r * W) (fun r => r * AccW)
    (fun r => (LVec.ofBitVec B).extract ((r % N) * W) W)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N))))
    (fun i j hi hj => by
      have hm : j % N = j := Nat.mod_eq_of_lt hj
      simp [peQ, psum, hm])
  rw [mmNext, commitNba2_append, hq]
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, nb_ash, nb_bsh, wr, h1, h3, h4, h5, h6, LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.replicate_l0,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  rw [commit_pair]
  have hCfold :
      (List.range (N * N)).foldl
          (fun z x => z.insertAt (x * AccW)
            (LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (x / N) (x % N))))) c =
        LVec.insertEntries AccW
          (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N))))
          (N * N) c := by rfl
  have hWfold :
      (List.range (N * N)).foldl
          (fun z x => z.insertAt (x * W) ((LVec.ofBitVec B).extract (x % N * W) W)) wc =
        LVec.insertEntries W (fun r => (LVec.ofBitVec B).extract (r % N * W) W) (N * N) wc := by rfl
  have hNW_le : N * W ≤ N * N * W := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hN
  have hNW32 : N * W < 2 ^ 32 := by
    have hlt : N * N * W < 2 ^ 32 := by omega
    exact Nat.lt_of_le_of_lt hNW_le hlt
  have hN32 : N < 2 ^ 32 := by
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) (by omega)
  have hW32 : W < 2 ^ 32 := by
    exact Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) (by omega)
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hW32, Nat.mod_eq_of_lt hN32, Nat.mod_eq_of_lt hNW32]
  have hBshift :
      ((LVec.ofBitVec B).shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))).resizeU (N * N * W) =
        LVec.ofBitVec (B >>> (N * W)) := by
    simp only [LVec.shr_ofBitVec, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast,
      LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyNW]
  rw [hCfold, hWfold, LVec.insertEntries_ofBitVec _ _ h2, LVec.insertAt_zero_of_width_eq (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (by simp [h3]), LVec.insertAt_zero_of_width_eq (by simp [h4]),
    LVec.insertAt_zero_of_width_eq (by simp [h5]), LVec.insertAt_zero_of_width_eq (by simp [h6])]
  simp [accC, hBshift]

/-- The state `t` busy cycles after a start with operands `A`, `B` (the invariant on `k`). -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a wc0 wc, st = MS ck r s a (LVec.ofBitVec B) (knownBit false) (accC N W AccW A B t) (LVec.ofBitVec (BitVec.ofNat 32 t))
    (knownBit true) (LVec.ofBitVec (A >>> (t * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) wc ∧
    wc = LVec.insertEntries W (fun r => (LVec.ofBitVec (B >>> (t * (N * W)))).extract ((r % N) * W) W) (N * N) wc0

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k ash bsh wc, st = MS ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k
    (knownBit false) ash bsh wc

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh wc, prev = MS ck r s a b dn c k bz ash bsh wc ∧ Wd N W AccW dn c k bz ash bsh wc ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz ash bsh wc

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- **The phase model** at `(N, W, AccW)`, latency `N`: `Ready` after a reset, `Busy x m` the state
`t = N - 1 - m` busy cycles after a start, `Fin x` the product shown. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hR32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, wc, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, wc, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c kk bz ash bsh wc k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh wc hw
  Ready st := ∃ ck r s a b c k ash bsh wc, st = MS ck r s a b (knownBit false) c k (knownBit false) ash bsh wc
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, ash, bsh, wc, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, wc, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, ash, bsh, wc, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', h⟩ := next_reset (appIn e "clk" ck) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
      dn c k bz ash bsh wc hw
    rw [h]
    exact ⟨appIn e "clk" ck, knownBit true, appIn e "start" s, appIn e "A" a,
      appIn e "B" b, c', k', ash, bsh,
      LVec.insertEntries W (fun _ => LVec.replicate W .l0) (N * N) wc, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb,
      next_start hN hW hNW _ _ _ dn c k bz ash bsh wc hw]
    refine .inr ⟨N - 1, by omega, 0, by omega, ?_⟩
    refine ⟨appIn e "clk" ck, knownBit false, knownBit true, LVec.ofBitVec x.fst,
      wc, LVec.insertEntries W (fun r => (LVec.ofBitVec x.snd.fst).extract (r % N * W) W) (N * N) wc,
      ?_⟩
    simp
  busy := by
    rintro e prev st x m hshape ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', wc0', wc', hb, hfeed⟩
      hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    have hwc0 : wc0'.width = N * N * W := by
      rcases hshape with ⟨ck0, r0, s0, a0, b0, dn0, c0, k0, bz0, ash0, bsh0, wc1, hs0, hw0⟩
      have hwc_eq : wc = wc1 := (MS_inj hs0).2.2.2.2.2.2
      have hwc : wc.width = N * N * W := by rw [hwc_eq]; exact hw0.2.2.2.2.2.2
      rw [hfeed] at hwc
      simpa using hwc
    have hfeed' := feed_eq_localWeight hN hW x.2.1 t wc0' hwc0
    have hfeedLocal : wc = LVec.ofBitVec (localWeight N W x.2.1 t) := hfeed.trans hfeed'
    have hnext := next_step (N := N) (W := W) (AccW := AccW) hN hW hNW
      (A := x.1) (B := x.2.1) (t := t) (by omega) (appIn e "clk" ck)
      (appIn e "A" a) wc hfeedLocal
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      show appIn e "B" b = LVec.ofBitVec x.2.1 from (ops_appIn hx a b).2, hnext]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      refine ⟨appIn e "clk" ck, knownBit false, knownBit false, appIn e "A" a,
        LVec.ofBitVec x.2.1, LVec.ofBitVec (BitVec.ofNat 32 N),
        LVec.ofBitVec (x.fst >>> (N * W)),
        LVec.ofBitVec (x.snd.fst >>> ((t + 2) * (N * W))),
        LVec.insertEntries W
          (fun r => (LVec.ofBitVec (x.snd.fst >>> (N * (N * W)))).extract (r % N * W) W)
          (N * N) wc, ?_⟩
      rfl
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      refine ⟨m - 1, by omega, t + 1, by omega, appIn e "clk" ck, knownBit false,
        knownBit false, appIn e "A" a, wc,
        LVec.insertEntries W
          (fun r => (LVec.ofBitVec (x.snd.fst >>> ((t + 1) * (N * W)))).extract (r % N * W) W)
          (N * N) wc, ?_⟩
      simp [Nat.add_assoc]
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, -, rfl⟩ ⟨ck', r', s', a', b', c', k', ash',
      bsh', wc', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨appIn e "clk" ck, knownBit false, knownBit false, appIn e "A" a, appIn e "B" b,
      c, k, ash, bsh, wc, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, -, rfl⟩ ⟨ck', r', s', a', b', k', ash',
      bsh', wc', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨appIn e "clk" ck, knownBit false, knownBit false, appIn e "A" a, appIn e "B" b,
      k, ash, bsh, wc, rfl⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_sh", "b_next", "w_cur"] : List String).Nodup
    decide
    ⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · simp [Tasks.Matmul.task, mmCtrl, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm
    simp [Tasks.Matmul.task, mmPE, sext, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]

/-! ## 8. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3)

Rule 2: the phase model's shape `I` (the register widths, any values) holds at every power-up state
(`mm_powerUp`), and every obligation of the model holds from any state of the shape, so the claim holds
from every power-up (`TxTask.satisfiedAtV2_of_phases`, `SvGolf.SeqV2`); the same cycle gives
termination from every power-up (`mm_terminatesPU`). Rule 1: every process is an `always_ff`
(`mm_profile`), so the design has no combinational dependency at all (`combDeps_of_ffOnly`). Rule 3
(`mm_xsafe`): every expression is a known literal, a declared signal, an in-range constant slice
(`C`'s windows, the operand entries), a concatenation, a replication, a width conversion or `+`, `-`,
`*`, `>>`, `==` on operands of matching widths. -/

/-- **Rule 1.** -/
theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA hR32] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨k, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨ash, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bsh, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨wc, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain rfl := powerUp_nil.mp h12
  exact ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, w6, w7, w8, w9, w10, w11, w12⟩

/-- **Termination from every power-up** (the cycle of `mm_terminates`). -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, wc, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz ash bsh wc kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh wc hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

/-- The control passes rule 3. -/
theorem ctrl_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (mmCtrl N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmCtrl, nb, c32, mmD, mmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

/-- A PE passes rule 3: its windows of `C` and of the operand registers are in range. -/
theorem pe_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (mmPE N W AccW i j) = true := by
  have hN : 0 < N := by omega
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have hA : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
    simpa [Nat.add_zero] using this
  have hB : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
    simpa using this
  have hA1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
  have hB1 : j * W + W - 1 + 1 ≤ N * N * W := by omega
  have hWC : (i * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le (w := W) hi hj
  have hWC1 : (i * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmPE, sext, mmD, mmDecls,
    LVec.replicate_l0, hC, hA, hB, hA1, hB1, hWC, hWC1]

theorem mm_pe_mem' {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPEs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p = mmPE N W AccW i j := by
  simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp
  exact ⟨i, j, hi, hj, rfl⟩

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ctrl_xsafe N W AccW
  · obtain ⟨i, j, hi, hj, rfl⟩ := mm_pe_mem' hm
    exact pe_xsafe hW hi hj

/-- **The reference satisfies the matmul statement (txtask-v2) at latency `N`** (`4` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hNW : N * N * W < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hW127) (by decide)
  have hNA : N * N * AccW < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hA64) (by decide)
  have hR32 : Rng32 N W AccW := rng32_of hN hW hA hNW hNA
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA hR32)
    (mm_disciplined N W AccW hN hW hA hR32) (mm_terminatesPU N W AccW hN hW hA hR32) hN
    (model N W AccW hN hW hA hR32 hNW) (mm_powerUp N W AccW hN hW hA hR32) (mm_moore N W AccW hN hW hA hR32)
    (mm_xsafe N W AccW hN hW hA hR32)

end Submission
