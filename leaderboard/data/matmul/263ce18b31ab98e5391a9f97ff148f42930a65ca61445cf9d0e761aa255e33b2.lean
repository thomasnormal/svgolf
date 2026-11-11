-- svgolf-latency: 5
import Submission.Design
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
# Pipelined variation of the `matmul` reference: a registered product, latency `N + 1`

`work/g2.sv` is the reference's `N²` multiply-accumulate units with the multiplier and the accumulator split
by a register `P` (one product per PE), so the clock period is that of the slower stage, not of their sum:
* step `t` registers the product `A[i][t]·B[t][j]` in `P` (a signed `W × W` multiply, truncated to `AccW`);
* the next cycle adds `P` to `C`; the last product is added one cycle after the last step: latency `N + 1`;
* everything is free-running: `a_sh`, `b_sh`, `k` (loaded on `start`), `P` and `C` (cleared on `start`)
  have no hold multiplexer. After the `N` steps `b_sh` has been shifted out (all zero), so `P` is 0 and `C`
  holds. Only `busy` and `done` are controlled; `busy` ends when `k = N`.
The proof is the free-running variation's (every register family has its updates evaluated, the invariant on
`k` steps the whole state) with the product register added to the shape:
1. `mmPE`, `peQ`, `prodV`: the PE writes `P` then `C`; `Ep`/`patV`: the registered products; `psum_Ep`.
2. `commit_PC`, `commit_pairs`, `rowMajor_map2`: the commit of the PEs' (`P`, `C`) pairs.
3. `next_step` (busy, `t ≤ N`), `next_run` (idle, past the end; `accC_ge`), `FinAt` at `t ≥ N + 1`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `N + 1` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := N + 1

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The PE at `(i, j)`: on `start` clear `P` and `C`; in every other cycle register the product of the
operands' front entries in `P` and add the previous step's `P` to `C` (no gate: once the steps are over
`b_sh` is all zero, so `P` is 0 and `C` holds). -/
def mmPE (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[.ifStmt (.ident "start")
    (.block #[.nbaAssign (.slice "P" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0)),
      .nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0))])
    (some (.block #[
      .nbaAssign (.slice "P" ((i * N + j) * AccW) AccW)
        (.resize AccW (.binary .mul (sext "a_sh" AccW (i * N * W) W) (sext "b_sh" AccW (j * W) W))),
      .nbaAssign (.slice "C" ((i * N + j) * AccW) AccW)
        (.binary .add (.slice (.ident "C") ((i * N + j) * AccW) AccW)
          (.slice (.ident "P") ((i * N + j) * AccW) AccW))]))])

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- The control: the operand shift registers and the step counter run free (loaded on `start`, stepped
in every other cycle); `busy` and `done` hold the handshake. -/
def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .ifStmt (.ident "start")
      (.block #[.nbaAssign (.ident "a_sh") (.ident "A"), .nbaAssign (.ident "b_sh") (.ident "B"),
        nb "k" (LVec.replicate 32 .l0)])
      (some (.block #[
        .nbaAssign (.ident "a_sh") (.binary (.shr false) (.ident "a_sh") (c32 W)),
        .nbaAssign (.ident "b_sh") (.binary (.shr false) (.ident "b_sh") (.binary .mul (c32 N) (c32 W))),
        .nbaAssign (.ident "k") (.binary .add (.ident "k") (c32 1))])),
    .ifStmt (.ident "rst")
      (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩])
      (some (.ifStmt (.ident "start")
        (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩])
        (some (.ifStmt (.ident "busy")
          (.block #[.ifStmt (.binary .eq (.ident "k") (c32 N))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
          none))))])

/-- The declarations, `A`/`B`/`a_sh`/`b_sh` at `wa` bits and `C` at `wc`. -/
def mmDecls (wa wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "k", width := 32 },
   { name := "busy", width := 1 }, { name := "a_sh", width := wa }, { name := "b_sh", width := wa },
   { name := "P", width := wc }]

/-- The PEs, row-major. -/
def mmPEs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => mmPE N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * N * AccW)).toArray
  processes := (mmCtrl N W :: mmPEs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("N", N), ("W", W), ("AccW", AccW)], pwidths := [("N", 32), ("W", 32), ("AccW", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_sh", "b_sh", "P"].map (·, 1)

theorem mm_decls (N W AccW : Int) :
    buildDecls (mmEnv N W AccW) design.pdesign.decls =
      .ok (mmDecls ((N * N * W - 1).natAbs + 1) ((N * N * AccW - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, mmDecls, Gen2.except_ok_bind]

theorem mm_elems (N W AccW : Int) : buildElems (mmEnv N W AccW) design.pdesign.decls = .ok mmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, mmElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev mmE (N W AccW : Nat) : IEnv :=
  (mmEnv N W AccW).withDecls (mmDecls (N * N * W) (N * N * AccW))

theorem mm_ctrl (N W AccW : Nat) :
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [mmCtrl N W] := by
  sv2_inst_simp [instStmt2, instStmts2, design.pdesign, mmEnv, mmScope, mmDecls, mmElems, mmCtrl,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2]
  try and_intros
  all_goals first | rfl | decide

/-- The PE template (the process inside `g_row`/`g_col`). -/
def peT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

/-- The `sv2_inst_simp` set of the PE template (with the window facts in scope). `instExpr2` tries
to constant-fold the `*` of the two sign-extending concatenations, and the fold must reduce to its
error; `sv2_inst_simp`'s default set carries the constant folder (`ctype`/`evalAt` and their
workers), so of the evaluators only `evalSized`, which is outside that set, is named here. -/
macro "pe_simp" : tactic => `(tactic| sv2_inst_simp [peT, evalSized, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2, design.pdesign,
  mmEnv, mmScope, mmDecls, mmElems, mmPE, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, *])

theorem pe_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N)
    (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems peT =
      mmPE N W AccW i j := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hNW : (1 : Int) ≤ N * N * W := by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega
  have hNA : (1 : Int) ≤ N * N * AccW := by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega
  have hcA : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  have hcC : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pA
  have hC := Lib.window_bounds_of_natCast (((i : Int) * N + j) * AccW) (N * N * AccW)
    (Lib.rowMajor_window_le (w := AccW) hi hj) hA (by simp) (by simp)
  have ha := Lib.window_bounds_of_natCast ((i : Int) * N * W) (N * N * W)
    (Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega)) hW (by simp) (by simp)
  have hb := Lib.window_bounds_of_natCast ((j : Int) * W) (N * N * W)
    (Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj) hW (by simp) (by simp)
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  pe_simp
  -- `simp` cannot use `instExpr2`'s `resize` equation (measured): unfold it by hand.
  repeat (unfold instExpr2; pe_simp)

/-- `for (g = 0; g < N; g++) body`. -/
def genN (lbl g : String) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) (.paramRef "N" none))
    (.unary .inc (.genvarRef g)) (some 4) body

theorem mm_gens_src : design.pdesign.generates = [genN "g_row" "i" [genN "g_col" "j" ([peT].map .process)]] :=
  rfl

/-- **The nested generate expands to the row-major PEs** (`mul2d_pp_expand`'s route). -/
theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates = .ok (mmPEs N W AccW) := by
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  rw [mm_gens_src]
  apply expandList2_singleton_ok
  rw [genN, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [peT].map (instProcess2 (((mmE N W AccW).bindVal "i" v).bindVal "j" w) mmElems))
      (evalInt_int 0) (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv]))
      (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv])) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map, mmPEs]
    congr 1
    simp only [List.flatMap_def]
    congr 1
    refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
    exact pe_inst N W AccW i j hN hW hA (List.mem_range.mp hi) (List.mem_range.mp hj)
  · intro v _ _
    apply expandList2_singleton_ok
    have hv : ((mmE N W AccW).bindVal "i" v).vals.lookup "N" = some (N : Int) := by
      simp [IEnv.bindVal, List.lookup, hNv]
    rw [genN, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hv]))
      (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hv]))
      (by simpa using hF)]
    simp

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (mmDecls (N * N * W) (N * N * AccW)) mmElems
        (mmPEs N W AccW)) := by
  have hd := mm_decls N W AccW
  rw [← Int.natCast_mul N N, ← Int.natCast_mul (N * N) W,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hW), ← Int.natCast_mul (N * N) AccW,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hA)] at hd
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv _ _ _) hd (mm_elems _ _ _)
    (mm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      mmCtrl N W :: mmPEs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_ctrl]
  simp [design.pdesign]

/-- Two PEs write disjoint windows of `C`. -/
theorem pe_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ a ∈ (mmPE N W AccW i j).procWins, ∀ b ∈ (mmPE N W AccW i' j').procWins,
      a.overlaps b = false := by
  have := rowMajor_le (K := AccW) h
  simp [mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  omega

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

/-- **The loaded family is `mmD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.sem N W AccW = mmD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA]; exact mm_driversOk N W AccW)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, mm_ctrl, mmD]
  simp [design.pdesign]

/-! ## 2. G0's clock step for the loaded family, at every `(N, W, AccW)` -/

/-- **`mmD` is in G0's decidable FF-only profile at every `(N, W, AccW)`** (symbolic, not `rfl`). -/
theorem mm_profile (N W AccW : Nat) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simpa [mmD] using mm_pairwise N W AccW)⟩
  simp [mmD, mmCtrl, mmPEs, mmPE, nb, List.all_flatMap, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, mmDecls]

/-- The 12 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c k bz ash bsh pp : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("k", k),
    ("busy", bz), ("a_sh", ash), ("b_sh", bsh), ("P", pp)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz ash bsh pp : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c k bz ash bsh pp) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz ash bsh pp := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The control's updates, from the pre-edge values: the free-running registers, then the handshake. -/
def ctrlQ (N W : Nat) (r s a b dn k bz ash bsh : LVec) : NbaQueue2 :=
  (if s.condTrue then [wr "a_sh" ash a, wr "b_sh" bsh b, wr "k" k (LVec.replicate 32 .l0)]
   else [wr "a_sh" ash (ash.shr (LVec.ofInt 32 (W : Int))),
     wr "b_sh" bsh (bsh.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))),
     wr "k" k (k.add (LVec.ofInt 32 1))]) ++
  (if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩]
   else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩]
   else if bz.condTrue then
     if (LVec.ofLogic (k.eqLogical (LVec.ofInt 32 (N : Int)))).condTrue then
       [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
     else []
   else [])

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- The product registered by PE `(i, j)`, evaluated. -/
def prodV (N W AccW i j : Nat) (ash bsh : LVec) : LVec :=
  ((sxv ash AccW (i * N * W) W).mul (sxv bsh AccW (j * W) W)).resizeU AccW

/-- The PE's updates (`P`, then `C`), from the pre-edge values. -/
def peQ (N W AccW : Nat) (s c pp ash bsh : LVec) (i j : Nat) : NbaQueue2 :=
  if s.condTrue then
    [("P", (i * N + j) * AccW, (LVec.replicate AccW .l0).resizeU AccW),
     ("C", (i * N + j) * AccW, (LVec.replicate AccW .l0).resizeU AccW)]
  else
    [("P", (i * N + j) * AccW, (prodV N W AccW i j ash bsh).resizeU AccW),
     ("C", (i * N + j) * AccW,
       ((c.extract ((i * N + j) * AccW) AccW).add (pp.extract ((i * N + j) * AccW) AccW)).resizeU AccW)]

theorem ctrl_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh pp : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh pp) [] (mmCtrl N W) =
      .ok (MS ck r s a b dn c k bz ash bsh pp, ctrlQ N W r s a b dn k bz ash bsh) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp [mmCtrl, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem pe_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh pp : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh pp) [] (mmPE N W AccW i j) =
      .ok (MS ck r s a b dn c k bz ash bsh pp, peQ N W AccW s c pp ash bsh i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold peQ
  by_cases h1 : s.condTrue = true <;>
    simp [mmPE, sext, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, prodV, sxv, h1]

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c k bz ash bsh pp : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c k bz ash bsh pp) (ctrlQ N W r s a b dn k bz ash bsh ++
    (List.range N).flatMap fun i => (List.range N).flatMap (peQ N W AccW s c pp ash bsh i))

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus
entry, any state of the design's shape, every fuel from 30). -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c k bz ash bsh pp : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c k bz ash bsh pp) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c k bz ash bsh pp, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm; rfl
  rw [mm_sem_eq N W AccW hN hW hA, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
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

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 1) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

/-- The products registered by step `t - 1` (entry `(i, j)` is `A[i][t-1]·B[t-1][j]`); `0` at `t = 0`, when nothing is
registered yet. -/
def Ep (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  if t = 0 then 0 else
    Tasks.Matmul.entry W A (i * N + (t - 1)) * Tasks.Matmul.entry W B ((t - 1) * N + j)

/-- The product registers `P` after `t` cycles: the products of step `t - 1`, mod `2^AccW`. -/
def patV (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r => BitVec.ofInt AccW (Ep N W A B t (r / N) (r % N)))

/-- Accumulate-then-register: the sum to `t` is the sum to `t - 1` plus the registered products. -/
theorem psum_Ep (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B t i j = psum N W A B (t - 1) i j + Ep N W A B t i j := by
  cases t with
  | zero => simp [Ep]
  | succ u => simp [Ep, psum_succ]

/-- A signed product at a wider width, truncated: the signed product. -/
theorem setWidth_mul_signExtend' {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := Lib.setWidth_add_mul_signExtend h (0#m) a b
  simpa using this

/-- **PE `(i, j)` in a cycle without `start`** registers `A[i][t]·B[t][j]` in `P` and adds the registered
products of step `t - 1` to `C` (the sum to `t - 1`), reaching the sum to `t`. -/
theorem pe_step {N W AccW : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {t i j : Nat} (hi : i < N)
    (hj : j < N) : peQ N W AccW (knownBit false) (accC N W AccW A B (t - 1)) (patV N W AccW A B t)
      (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))) i j =
    [("P", (i * N + j) * AccW,
        .ofBitVec (BitVec.ofInt AccW (Ep N W A B (t + 1) ((i * N + j) / N) ((i * N + j) % N)))),
     ("C", (i * N + j) * AccW,
        .ofBitVec (BitVec.ofInt AccW (psum N W A B t ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have ha : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
  have hb : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj; simpa using this
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  have hE : Ep N W A B (t + 1) i j =
      Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by simp [Ep]
  have hs : psum N W A B t i j = psum N W A B (t - 1) i j + Ep N W A B t i j := psum_Ep N W A B t i j
  simp (disch := omega) only [peQ, prodV, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, sxv, accC, patV,
    LVec.extract_ofBitVec, extractLsb'_packBV, hd, hm, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.add_ofBitVec, BitVec.setWidth_eq, setWidth_mul_signExtend',
    Lib.extractLsb'_ushiftRight, e1, e2, hE, hs, BitVec.ofInt_add, Tasks.Matmul.entry]

/-! ## 4. The spec's arithmetic: `product` is the packed vector of the wrapped dot products -/

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- After `N` busy cycles the accumulators hold the product (`psum N` is `dot`). -/
theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

/-- Entries past the end of a flat vector are zero. -/
theorem entry_ge {W n : Nat} (x : BitVec n) {idx : Nat} (h : n ≤ idx * W) : Tasks.Matmul.entry W x idx = 0 := by
  have h0 : x.extractLsb' (idx * W) W = 0#W := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_zero]
    first | exact BitVec.getLsbD_of_ge x _ (by omega) | exact BitVec.getLsbD_ge x _ (by omega)
  simp [Tasks.Matmul.entry, h0]

/-- Past `N` steps the partial sums do not change: `B` has only `N` rows. -/
theorem psum_ge (N W : Nat) (A B : BitVec (N * N * W)) (i j : Nat) : ∀ t, N ≤ t →
    psum N W A B t i j = psum N W A B N i j := by
  intro t ht
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction d with
  | zero => rfl
  | succ d ih =>
    have h1 : N * N ≤ (N + d) * N + j :=
      Nat.le_trans (Nat.mul_le_mul (Nat.le_add_right N d) (Nat.le_refl N)) (Nat.le_add_right _ _)
    have h2 : N * N * W ≤ ((N + d) * N + j) * W := Nat.mul_le_mul_right W h1
    show psum N W A B (N + d + 1) i j = _
    rw [psum_succ, ih (Nat.le_add_right _ _), entry_ge B h2]
    simp

theorem accC_ge (N W AccW : Nat) (A B : BitVec (N * N * W)) {t : Nat} (ht : N ≤ t) :
    accC N W AccW A B t = accC N W AccW A B N := by
  have h : ∀ i j, psum N W A B t i j = psum N W A B N i j := fun i j => psum_ge N W A B i j t ht
  simp only [accC, h]

/-! ## 5. The registers through a cycle: the commit, then the invariant on `k` -/

section commit
variable {ck r s a b dn c k bz ash bsh pp : LVec} {lo : Nat} {v : LVec}
theorem nb_busy : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("busy", lo, v) =
    MS ck r s a b dn c k (bz.insertAt lo v) ash bsh pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_done : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c k bz ash bsh pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_k : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("k", lo, v) =
    MS ck r s a b dn c (k.insertAt lo v) bz ash bsh pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ash : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("a_sh", lo, v) =
    MS ck r s a b dn c k bz (ash.insertAt lo v) bsh pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bsh : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("b_sh", lo, v) =
    MS ck r s a b dn c k bz ash (bsh.insertAt lo v) pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_C : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) k bz ash bsh pp := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_P : nbaStep (MS ck r s a b dn c k bz ash bsh pp) ("P", lo, v) =
    MS ck r s a b dn c k bz ash bsh (pp.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- Committing writes of `C` and `P` only. -/
theorem commit_PC {ck r s a b dn k bz ash bsh : LVec} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 = "C" ∨ u.1 = "P") →
    ∀ c pp, commitNba2 (MS ck r s a b dn c k bz ash bsh pp) q =
      MS ck r s a b dn (q.foldl (fun acc u => if u.1 = "C" then acc.insertAt u.2.1 u.2.2 else acc) c) k bz ash bsh
        (q.foldl (fun acc u => if u.1 = "P" then acc.insertAt u.2.1 u.2.2 else acc) pp)
  | [], _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, h, c, pp => by
    have hq : ∀ u ∈ q, u.1 = "C" ∨ u.1 = "P" := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with rfl | rfl
    · rw [commitNba2_cons, nb_C, commit_PC hq]
      simp
    · rw [commitNba2_cons, nb_P, commit_PC hq]
      simp

/-- Writing windows by name keeps the width. -/
theorem width_foldl_if (p : String) : ∀ (q : NbaQueue2) (c : LVec),
    (q.foldl (fun acc u => if u.1 = p then acc.insertAt u.2.1 u.2.2 else acc) c).width = c.width
  | [], _ => rfl
  | u :: q, c => by
    rw [List.foldl_cons, width_foldl_if p q]
    split <;> simp

/-- The PEs' updates, row-major, when PE `(i, j)` writes `P` and `C` window `i·N + j` with `gp` and `gc`. -/
theorem rowMajor_map2 {N AccW : Nat} {q : Nat → Nat → NbaQueue2} (gp gc : Nat → LVec)
    (h : ∀ i j, i < N → j < N → q i j =
      [("P", (i * N + j) * AccW, gp (i * N + j)), ("C", (i * N + j) * AccW, gc (i * N + j))]) :
    ((List.range N).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (N * N)).flatMap fun r => [("P", r * AccW, gp r), ("C", r * AccW, gc r)] := by
  suffices ∀ M, M ≤ N → ((List.range M).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (M * N)).flatMap (fun r => [("P", r * AccW, gp r), ("C", r * AccW, gc r)]) from
    this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.flatMap_append, List.flatMap_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [CombView.flatMap_congr' fun j hj => h M j (by omega) (List.mem_range.mp hj)]

/-- Committing the PEs' pairs of updates. -/
theorem commit_pairs {ck r s a b dn k bz ash bsh : LVec} (AccW : Nat) (gp gc : Nat → LVec) :
    ∀ (n : Nat) (c pp : LVec),
    commitNba2 (MS ck r s a b dn c k bz ash bsh pp)
        ((List.range n).flatMap fun r' => [("P", r' * AccW, gp r'), ("C", r' * AccW, gc r')]) =
      MS ck r s a b dn (LVec.insertEntries AccW gc n c) k bz ash bsh (LVec.insertEntries AccW gp n pp)
  | 0, _, _ => rfl
  | n + 1, c, pp => by
    rw [List.range_succ, List.flatMap_append, commitNba2_append, commit_pairs AccW gp gc n c pp]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, commitNba2_cons, commitNba2_nil, nb_P, nb_C,
      LVec.insertEntries_succ]

theorem ofNat_eq_iff32 {t N : Nat} (ht : t < 2 ^ 32) (hN : N < 2 ^ 32) :
    BitVec.ofNat 32 t = BitVec.ofNat 32 N ↔ t = N := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hN]

/-- The control in a busy cycle `t ≤ N`: `k` and the shift registers step; the cycle with `k = N` ends it. -/
theorem ctrl_busy {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t ≤ N) (ck a b c pp : LVec) :
    commitNba2 (MS ck (knownBit false) (knownBit false) a b (knownBit false) c (.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))) pp)
      (ctrlQ N W (knownBit false) (knownBit false) a b (knownBit false) (.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W))))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t = N))) c (.ofBitVec (BitVec.ofNat 32 (t + 1)))
      (knownBit (decide (t ≠ N))) (.ofBitVec (A >>> (t * W + W))) (.ofBitVec (B >>> (t * (N * W) + N * W))) pp := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc N N W]; exact Nat.le_mul_of_pos_left _ hN
  have hNW : N * W < 2 ^ 32 := by simp only [Nat.reducePow] at hr ⊢; omega
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW
  have ht' : t < 2 ^ 32 := Nat.lt_of_le_of_lt ht hN'
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW', Nat.mod_eq_of_lt hN',
      Nat.mod_eq_of_lt hNW]
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [ctrlQ, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
    LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast,
    BitVec.ofInt_ofNat, h1', LVec.mul_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    decide_eq_true_eq, ofNat_eq_iff32 ht' hN', LVec.width_ofBitVec, LVec.shr_ofBitVec,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW, ← BitVec.shiftRight_add]
  by_cases hf : t = N <;>
    simp [hf, List.cons_append, List.nil_append, List.append_nil, commitNba2_cons, commitNba2_nil, nb_k, nb_ash, nb_bsh,
      nb_busy, nb_done, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
      BitVec.ofNat_add_ofNat]

/-- **The invariant, one busy step**: from the state `t ≤ N` cycles after a start (`C` the partial sums of the
first `t - 1` steps, `P` the products of step `t - 1`, `k = t`, the operands shifted by `t` entries), one cycle
without `start` reaches the state at `t + 1`; `done` rises (and `busy` falls) exactly when `t = N`. -/
theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t ≤ N) (ck a b : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) (accC N W AccW A B (t - 1))
      (.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (.ofBitVec (A >>> (t * W)))
      (.ofBitVec (B >>> (t * (N * W)))) (patV N W AccW A B t) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t = N))) (accC N W AccW A B t)
      (.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t ≠ N))) (.ofBitVec (A >>> ((t + 1) * W)))
      (.ofBitVec (B >>> ((t + 1) * (N * W)))) (patV N W AccW A B (t + 1)) := by
  have hq := rowMajor_map2 (N := N) (AccW := AccW) (q := peQ N W AccW (knownBit false)
    (accC N W AccW A B (t - 1)) (patV N W AccW A B t) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (Ep N W A B (t + 1) (r / N) (r % N))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B t (r / N) (r % N))))
    (fun i j hi hj => pe_step hW A B hi hj)
  rw [mmNext, commitNba2_append, ctrl_busy hN hW hr A B ht, hq, commit_pairs,
    LVec.insertEntries_ofBitVec _ _ (by simp [accC]), LVec.insertEntries_ofBitVec _ _ (by simp [patV]),
    Nat.succ_mul, Nat.succ_mul]
  rfl

/-- The free-running registers in an idle cycle (`busy` = 0), from the state `t` cycles after a start. -/
theorem ctrl_idle {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    (t : Nat) (ck a b dn c pp : LVec) :
    commitNba2 (MS ck (knownBit false) (knownBit false) a b dn c (.ofBitVec (BitVec.ofNat 32 t))
      (knownBit false) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))) pp)
      (ctrlQ N W (knownBit false) (knownBit false) a b dn (.ofBitVec (BitVec.ofNat 32 t)) (knownBit false)
        (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W))))) =
    MS ck (knownBit false) (knownBit false) a b dn c (.ofBitVec (BitVec.ofNat 32 (t + 1)))
      (knownBit false) (.ofBitVec (A >>> (t * W + W))) (.ofBitVec (B >>> (t * (N * W) + N * W))) pp := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc N N W]; exact Nat.le_mul_of_pos_left _ hN
  have hNW : N * W < 2 ^ 32 := by simp only [Nat.reducePow] at hr ⊢; omega
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW', Nat.mod_eq_of_lt hN',
      Nat.mod_eq_of_lt hNW]
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [ctrlQ, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
    List.append_nil, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat, h1', LVec.mul_ofBitVec,
    LVec.add_ofBitVec, LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW,
    ← BitVec.shiftRight_add]
  simp [commitNba2_cons, commitNba2_nil, nb_k, nb_ash, nb_bsh, LVec.insertAt_zero_of_width_eq,
    BitVec.ofNat_add_ofNat]

/-- **An idle step after the steps are over**: `P` holds the products of step `t - 1`, which are zero from
`t - 1 ≥ N` on (`b_sh` has been shifted out), so `C` holds; `k` and the shift registers keep running. -/
theorem next_run {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) (t : Nat) (ck a b dn : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn (accC N W AccW A B (t - 1))
      (.ofBitVec (BitVec.ofNat 32 t)) (knownBit false) (.ofBitVec (A >>> (t * W)))
      (.ofBitVec (B >>> (t * (N * W)))) (patV N W AccW A B t) =
    MS ck (knownBit false) (knownBit false) a b dn (accC N W AccW A B t)
      (.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit false) (.ofBitVec (A >>> ((t + 1) * W)))
      (.ofBitVec (B >>> ((t + 1) * (N * W)))) (patV N W AccW A B (t + 1)) := by
  have hq := rowMajor_map2 (N := N) (AccW := AccW) (q := peQ N W AccW (knownBit false)
    (accC N W AccW A B (t - 1)) (patV N W AccW A B t) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (Ep N W A B (t + 1) (r / N) (r % N))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B t (r / N) (r % N))))
    (fun i j hi hj => pe_step hW A B hi hj)
  rw [mmNext, commitNba2_append, ctrl_idle hN hW hr A B t, hq, commit_pairs,
    LVec.insertEntries_ofBitVec _ _ (by simp [accC]), LVec.insertEntries_ofBitVec _ _ (by simp [patV]),
    Nat.succ_mul, Nat.succ_mul]
  rfl

/-! ## 6. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c k bz ash bsh pp : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧ ash.width = N * N * W ∧
    bsh.width = N * N * W ∧ pp.width = N * N * AccW

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh pp, st = MS ck r s a b dn c k bz ash bsh pp ∧ Wd N W AccW dn c k bz ash bsh pp

theorem peQ_PC (N W AccW : Nat) (s c pp ash bsh : LVec) :
    ∀ u ∈ (List.range N).flatMap fun i => (List.range N).flatMap (peQ N W AccW s c pp ash bsh i),
      u.1 = "C" ∨ u.1 = "P" := by
  intro u hu
  simp only [List.mem_flatMap] at hu
  obtain ⟨_, _, _, _, hu⟩ := hu
  unfold peQ at hu
  by_cases h1 : s.condTrue = true <;> simp [h1] at hu <;> rcases hu with rfl | rfl <;> simp

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz ash bsh pp : LVec) (hw : Wd N W AccW dn c k bz ash bsh pp) :
    I N W AccW (mmNext N W AccW ck r s a b dn c k bz ash bsh pp) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  simp only [mmNext, commitNba2_append, ctrlQ]
  by_cases c1 : r.condTrue = true <;> by_cases c2 : s.condTrue = true <;> by_cases c3 : bz.condTrue = true <;>
    by_cases c4 : (LVec.ofLogic (k.eqLogical (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp only [c1, c2, c3, c4, Bool.false_eq_true, ↓reduceIte, commitNba2_append, commitNba2_cons, commitNba2_nil,
      nb_busy, nb_done, nb_k, nb_ash, nb_bsh, wr] <;>
    rw [commit_PC (peQ_PC N W AccW _ _ _ _ _)] <;>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, width_foldl_insertAt, width_foldl_if, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmCtrl, mmPEs, mmPE, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
    Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-- **Termination**: every schedule and every stimulus completes. -/
theorem mm_terminates (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Terminates2 (design.sem N W AccW) := by
  refine Terminates2.of_invariant (I N W AccW) (mm_init N W AccW hN hW hA) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c k bz ash bsh pp kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh pp hw⟩

/-! ## 7. The protocol: the phases of `TxTask.satisfiedAt_of_phases`, and the statement -/

theorem MS_inj {ck r s a b dn c k bz ash bsh pp ck' r' s' a' b' dn' c' k' bz' ash' bsh' pp' : LVec}
    (h : MS ck r s a b dn c k bz ash bsh pp = MS ck' r' s' a' b' dn' c' k' bz' ash' bsh' pp') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ ash = ash' ∧ bsh = bsh' ∧ pp = pp' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- A cycle without `rst` and `start` from `Ready` (`busy` = 0, `done` = 0): `C` and `P` are not claimed (they
register and accumulate whatever the operand registers hold), and the free-running registers step. -/
theorem next_idle (N W AccW : Nat) (ck a b dn c k ash bsh pp : LVec) :
    ∃ c' k' ash' bsh' pp', mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bsh pp =
      MS ck (knownBit false) (knownBit false) a b dn c' k' (knownBit false) ash' bsh' pp' := by
  simp only [mmNext, commitNba2_append, ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    wr, commitNba2_cons, commitNba2_nil, nb_k, nb_ash, nb_bsh]
  rw [commit_PC (peQ_PC N W AccW _ _ _ _ _)]
  exact ⟨_, _, _, _, _, rfl⟩

/-- A reset cycle clears `busy` and `done` (the free-running registers step or load, whatever `start` shows). -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz ash bsh pp : LVec) (hw : Wd N W AccW dn c k bz ash bsh pp) :
    ∃ c' k' ash' bsh' pp', mmNext N W AccW ck (knownBit true) s a b dn c k bz ash bsh pp =
      MS ck (knownBit true) s a b (knownBit false) c' k' (knownBit false) ash' bsh' pp' := by
  obtain ⟨h1, -, -, h4, -, -, -⟩ := hw
  by_cases hs : s.condTrue = true <;>
  simp only [mmNext, commitNba2_append, ctrlQ, hs, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, commitNba2_cons,
    commitNba2_nil, nb_busy, nb_done, nb_k, nb_ash, nb_bsh, wr, h1, h4, LVec.resizeU_one_l0] <;>
  rw [commit_PC (peQ_PC N W AccW _ _ _ _ _)] <;>
  exact ⟨_, _, _, _, _, by rw [LVec.insertAt_zero_of_width_eq (v := dn) (p := knownBit false) (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (v := bz) (p := knownBit false) (by simp [h4])]⟩

/-- A start cycle captures the operands and clears the accumulators and the product registers: the state at
`t = 0`. -/
theorem next_start {N W AccW : Nat} (A B : BitVec (N * N * W)) (ck dn c k bz ash bsh pp : LVec)
    (hw : Wd N W AccW dn c k bz ash bsh pp) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c k bz ash bsh pp =
      MS ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) (knownBit false) (accC N W AccW A B (0 - 1))
        (.ofBitVec (BitVec.ofNat 32 0)) (knownBit true) (.ofBitVec (A >>> (0 * W)))
        (.ofBitVec (B >>> (0 * (N * W)))) (patV N W AccW A B 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  have hq := rowMajor_map2 (N := N) (AccW := AccW) (q := peQ N W AccW (knownBit true) c pp ash bsh)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (Ep N W A B 0 (r / N) (r % N))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N))))
    (fun i j _ _ => by simp [peQ, Ep, psum])
  rw [mmNext, commitNba2_append, hq]
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append,
    commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, nb_ash, nb_bsh, wr, h1, h3, h4, h5, h6, LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.replicate_l0,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  rw [commit_pairs, LVec.insertEntries_ofBitVec _ _ h2, LVec.insertEntries_ofBitVec _ _ h7,
    LVec.insertAt_zero_of_width_eq (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (by simp [h3]), LVec.insertAt_zero_of_width_eq (by simp [h4]),
    LVec.insertAt_zero_of_width_eq (by simp [h5]), LVec.insertAt_zero_of_width_eq (by simp [h6])]
  simp [accC, patV]

/-- The state `t ≤ N` cycles after a start with operands `A`, `B` (the invariant on `k`): `C` the partial sums
of the first `t - 1` steps, `P` the products of step `t - 1`. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b, st = MS ck r s a b (knownBit false) (accC N W AccW A B (t - 1)) (.ofBitVec (BitVec.ofNat 32 t))
    (knownBit true) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W)))) (patV N W AccW A B t)

/-- Finished with `A`, `B`: `done` = 1 and `C` the product (`t > N` cycles after the start). -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ t, N + 1 ≤ t ∧ ∃ ck r s a b, st = MS ck r s a b (knownBit true) (accC N W AccW A B N)
    (.ofBitVec (BitVec.ofNat 32 t)) (knownBit false) (.ofBitVec (A >>> (t * W))) (.ofBitVec (B >>> (t * (N * W))))
    (patV N W AccW A B t)

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh pp, prev = MS ck r s a b dn c k bz ash bsh pp ∧ Wd N W AccW dn c k bz ash bsh pp ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz ash bsh pp

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- **The phase model** at `(N, W, AccW)`, latency `N + 1`: `Ready` after a reset, `Busy x m` the state
`t = N - m` cycles after a start, `Fin x` the product shown. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (N + 1) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, pp, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, pp, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA σ e ck r s a b dn c kk bz ash bsh pp k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh pp hw
  Ready st := ∃ ck r s a b c k ash bsh pp, st = MS ck r s a b (knownBit false) c k (knownBit false) ash bsh pp
  Busy x m st := ∃ t, t + m = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, ash, bsh, pp, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨t, ht, ck, r, s, a, b, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup, accC_N]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', ash', bsh', pp', h⟩ := next_reset (appIn e "clk" ck) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz ash bsh pp hw
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb,
      next_start _ _ _ dn c k bz ash bsh pp hw]
    exact .inr ⟨N, by omega, 0, by omega, _, _, _, _, _, rfl⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, -, rfl⟩ ⟨t, ht, ck', r', s', a', b', hb⟩
      hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      next_step hN hW hNW _ _ (by omega : t ≤ N)]
    by_cases hf : t = N
    · left
      simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨N + 1, Nat.le_refl _, _, _, _, _, _, rfl⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, -, rfl⟩ ⟨ck', r', s', a', b', c', k', ash',
      bsh', pp', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨c₁, k₁, a₁, b₁, p₁, h⟩ := next_idle N W AccW (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
      (knownBit false) c k ash bsh pp
    rw [h]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, -, rfl⟩ ⟨t, ht, ck', r', s', a', b', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      ← accC_ge N W AccW x.fst x.snd.fst (by omega : N ≤ t - 1), next_run hN hW hNW x.fst x.snd.fst t]
    exact ⟨t + 1, by omega, _, _, _, _, _, by rw [accC_ge N W AccW x.fst x.snd.fst (by omega : N ≤ t)]⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_sh", "b_sh", "P"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
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
theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA] at h
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
  obtain ⟨pp, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain rfl := powerUp_nil.mp h12
  exact ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, w6, w7, w8, w9, w10, w11, w12⟩

/-- **Termination from every power-up** (the cycle of `mm_terminates`). -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, pp, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c k bz ash bsh pp kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh pp hw⟩

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
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmPE, sext, mmD, mmDecls,
    LVec.replicate_l0, hC, hA, hB, hA1, hB1]

theorem mm_pe_mem' {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPEs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p = mmPE N W AccW i j := by
  simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp
  exact ⟨i, j, hi, hj, rfl⟩

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
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
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA)
    (mm_disciplined N W AccW hN hW hA) (mm_terminatesPU N W AccW hN hW hA) (Nat.succ_le_succ (Nat.zero_le N))
    (model N W AccW hN hW hA hNW) (mm_powerUp N W AccW hN hW hA) (mm_moore N W AccW hN hW hA)
    (mm_xsafe N W AccW hN hW hA)

end Submission
