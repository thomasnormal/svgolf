-- svgolf-latency: 16
import Submission.Design
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import SvGolf.SeqV2

/-!
# Reference solution for task `sorter`: the insertion-cell array (cell sort), latency `2N`

`reference/sorter_ins.sv` (adapted from andrewpeck/cell-sort, MIT; provenance in its header) keeps `N`
cells, cell `k` at `data[k*W +: W]`, a valid token per cell and a registered output from cell `0`.
Proved at every in-range `(N, W)` through `StreamTask.satisfiedAt_of_phases` (`SvGolf.Seq`):
1. **Agreement** (`so_sem_eq`): `design.sem N W` is the hand-built `soD` (no cell family at `N = 1`).
2. **G0's clock step** (`so_profile`, `so_cycle`): one cycle is the commit `soNext` of the queues
   `topQ`, `outQ`, `cellQ`, register by register (`nbaFold`); a reset's write wins (`next_reset`).
3. **The sort** (`hw_ins`, `ins_comm`, `sort_snoc`, `tail_ins`): a load is `tail ∘ insertAsc x` on the
   ascending cells, and insertions commute, so `t` loads give `[0]^(N-t) ++ sortAsc` of the inputs.
4. **The invariant** (`cv`, `tokv`, `ovb`, `at_step`): the cells, the token delay line and the output
   `j` cycles after a start; a drain shifts the sorted list down, so the state ends all zero.
5. **The protocol** (`model`): `Ready` (zero) and `At ys j`; txtask-v2's rules (section 9); then
   `solution`. The packed-family lemmas (`bvInsertAt_packBV`, `foldl_range_ofBitVec_packBV`,
   `LVec.foldl_range_insertAt_last`) are in `LeanModels.Sv.SeqFamily`, `nbaFold` in `LeanModels.Sv.NbaCommit`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: the last output shows `2N` snapshots after the start's. -/
def lat (N _W : Nat) : Nat := 2 * N

/-! ## 1. Agreement: the loaded family is the hand-built `soD` -/

/-- `w` zero bits, and the select `data[lo +: W]`. -/
abbrev zW (w : Nat) : LVec := LVec.replicate w .l0
abbrev dw (lo W : Nat) : Expr2 := .slice (.ident "data") lo W

/-- The top cell `N - 1`: never pushed into; drains in `0`. -/
def topP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .ifStmt (.ident "in_valid")
      (.block #[.ifStmt (.binary .gt (.ident "in_data") (dw ((N - 1) * W) W))
        (.nbaAssign (.slice "data" ((N - 1) * W) W) (.ident "in_data")) none])
      (some (.nbaAssign (.slice "data" ((N - 1) * W) W) (.lit (zW W)))),
    .nbaAssign (.slice "tok" (N - 1) 1) (.ident "in_valid"),
    .ifStmt (.ident "rst") (.block #[.nbaAssign (.slice "data" ((N - 1) * W) W) (.lit (zW W)),
      .nbaAssign (.slice "tok" (N - 1) 1) (.lit (zW 1))]) none])

/-- The registered output: cell `0` and its token. -/
def outP (W : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[.nbaAssign (.ident "out_valid") (.slice (.ident "tok") 0 1),
    .nbaAssign (.ident "out_data") (dw 0 W),
    .ifStmt (.ident "rst") (.nbaAssign (.ident "out_valid") (.lit (zW 1))) none])

/-- Cell `k < N - 1`: take the pushed neighbour's value, or the input, or hold; drain down. -/
def cellP (W k : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .ifStmt (.ident "in_valid")
      (.block #[.ifStmt (.binary .gt (.ident "in_data") (dw ((k + 1) * W) W))
        (.nbaAssign (.slice "data" (k * W) W) (dw ((k + 1) * W) W))
        (some (.ifStmt (.binary .gt (.ident "in_data") (dw (k * W) W))
          (.nbaAssign (.slice "data" (k * W) W) (.ident "in_data")) none))])
      (some (.nbaAssign (.slice "data" (k * W) W) (dw ((k + 1) * W) W))),
    .nbaAssign (.slice "tok" k 1) (.slice (.ident "tok") (k + 1) 1),
    .ifStmt (.ident "rst") (.block #[.nbaAssign (.slice "data" (k * W) W) (.lit (zW W)),
      .nbaAssign (.slice "tok" k 1) (.lit (zW 1))]) none])

/-- The declarations, `in_data`/`out_data` at `w`, `data` at `nw`, `tok` at `n` bits. -/
def soDeclsW (w nw n : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "in_valid", width := 1, isInput := true },
   { name := "in_data", width := w, isInput := true }, { name := "out_valid", width := 1, isOutput := true },
   { name := "out_data", width := w, isOutput := true }, { name := "data", width := nw },
   { name := "tok", width := n }]

abbrev soDecls (N W : Nat) : List Decl := soDeclsW W (N * W) N

def soD (N W : Nat) : Design2 where
  name := "sorter"
  decls := (soDecls N W).toArray
  processes := (topP N W :: outP W :: (List.range (N - 1)).map (cellP W)).toArray

def soScope (N W : Int) : IEnv := { vals := [("N", N), ("W", W)], pwidths := [("N", 32), ("W", 32)] }

def soEnv (N W : Int) : IEnv := { soScope N W with dims := dimTable (soScope N W) design.pdesign.decls }

theorem so_paramEnv (N W : Int) : design.pdesign.paramEnv2 [N, W] = .ok (soEnv N W) := rfl

def soElems : List (String × Nat) :=
  ["clk", "rst", "start", "in_valid", "in_data", "out_valid", "out_data", "data", "tok"].map (·, 1)

theorem so_decls (N W : Int) : buildDecls (soEnv N W) design.pdesign.decls =
    .ok (soDeclsW ((W - 1).natAbs + 1) ((N * W - 1).natAbs + 1) ((N - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    soEnv, soScope, List.lookup, soDeclsW, Gen2.except_ok_bind]

theorem so_elems (N W : Int) : buildElems (soEnv N W) design.pdesign.decls = .ok soElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, soEnv,
    soScope, List.lookup, soElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev soE (N W : Nat) : IEnv := (soEnv N W).withDecls (soDecls N W)

/-- The cell template (the process inside `gen_cell`). -/
def cellT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p]] => p
  | _ => .alwaysFF "" (.block [])

macro "so_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, soEnv, soScope, soDeclsW, soElems,
  topP, outP, cellP, cellT, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, *])

/-- Window facts of `data[lo +: W]` inside `N·W` bits, for the instantiation `simp`. -/
theorem so_win {N W lo : Nat} (h : lo + W ≤ N * W) (hW : 1 ≤ W) (x : Int) (hx : (lo : Int) = x) :
    0 ≤ x ∧ x.toNat = lo ∧ x + W - 1 < N * W ∧ 1 ≤ x + W ∧ (x + W).toNat = lo + W :=
  Lib.window_bounds_of_natCast x (N * W) h hW hx (by simp)

/-- The facts every instantiation `simp` here needs. -/
theorem inst_facts {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) : ((0 : Int) < W ∧ 0 < W ∧ (1 : Int) ≤ N * W) ∧
    ((N : Int) * W - 1).natAbs + 1 = N * W ∧ (PartMode.up == PartMode.range) = false ∧
    ((N : Int) - 1).natAbs + 1 = N :=
  ⟨⟨by omega, hW, by have := Nat.mul_pos hN hW; omega⟩,
    by rw [← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one (Nat.mul_pos hN hW), rfl, Lib.natAbs_sub_one_add_one hN⟩

theorem so_static (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    design.pdesign.processes.map (instProcess2 (soE N W) soElems) = [topP N W, outP W] := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := inst_facts hN hW
  obtain ⟨h7, h8, h9, h10, h11⟩ : ((1 : Int) ≤ N ∧ 0 < N ∧ (0 : Int) ≤ N - 1 ∧ (N : Int) - 1 < N) ∧
      ((N : Int) - 1).toNat = N - 1 ∧ max ((W : Int) - 1) 0 = W - 1 ∧ min ((W : Int) - 1) 0 = 0 ∧
      ((W : Int) - 1 - 0 + 1).toNat = W := by omega
  have hd := so_win (N := N) (W := W) (lo := (N - 1) * W)
    (Nat.le_of_eq (by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN])) hW
    (((N : Int) - 1) * W) (by rw [Int.natCast_mul, Int.ofNat_sub hN]; rfl)
  so_simp
  try and_intros
  all_goals first | rfl | decide | omega | skip

theorem cell_inst (N W k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hk : k + 1 < N) :
    instProcess2 ((soE N W).bindVal "k" k) soElems cellT = cellP W k := by
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := inst_facts hN hW
  have hk : (k : Int) + 1 < N ∧ (k : Int) < N := by omega
  have hle := Nat.mul_le_mul_right W (show k + 1 + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hle
  have ha := so_win (N := N) (W := W) (lo := (k + 1) * W) (by rw [Nat.add_mul, Nat.one_mul]; omega) hW
    (((k : Int) + 1) * W) (by simp)
  have hb := so_win (N := N) (W := W) (lo := k * W) (by omega) hW ((k : Int) * W) (by simp)
  so_simp
  try and_intros
  all_goals first | rfl | decide

/-- `for (k = 0; k < N - 1; k++)` over the cell template. -/
theorem so_gens_src : design.pdesign.generates = [.genFor (some "gen_cell") "k" (.int 0)
    (.binary .slt (.genvarRef "k") (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)))
    (.unary .inc (.genvarRef "k")) (some 7) ([cellT].map .process)] := rfl

/-- **The generate expands to the cells `0 … N-2`** (none at `N = 1`). -/
theorem so_gens (N W F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hF : N < F) :
    expandList2 (soE N W) soElems F design.pdesign.generates = .ok ((List.range (N - 1)).map (cellP W)) := by
  have hNv : ∀ i : Int, ((soE N W).bindVal "k" i).vals.lookup "N" = some (N : Int) := fun i => rfl
  rw [so_gens_src]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int) - 1) (evalInt_int 0)
    (fun i => isInt_binary_of rfl (isInt_paramRef_of (hNv i)) rfl)
    (fun i => evalInt_sub_of (isInt_paramRef_of (hNv i)) rfl (evalInt_paramRef_of (hNv i)) rfl) (by omega)]
  have ht : ((N : Int) - 1 - 0).toNat = N - 1 := by omega
  simp only [ht, intRange_zero, List.flatMap_map, List.map_cons, List.map_nil, Gen2.flatMap_singleton_map]
  congr 1
  exact List.map_congr_left fun k hk => cell_inst N W k hN hW (by have := List.mem_range.mp hk; omega)

theorem so_instantiate2 (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    design.pdesign.instantiate2 [(N : Int), W] (PDesign.surfaceFuel [(N : Int), W]) =
      .ok (design.pdesign.assemble2 (soEnv N W) (soDecls N W) soElems ((List.range (N - 1)).map (cellP W))) := by
  have hd := so_decls N W
  rw [Lib.natAbs_sub_one_add_one hW, ← Int.natCast_mul, Lib.natAbs_sub_one_add_one (Nat.mul_pos hN hW),
    Lib.natAbs_sub_one_add_one hN] at hd
  refine PDesign.instantiate2_of_ok rfl (so_paramEnv _ _) hd (so_elems _ _) (so_gens N W _ hN hW ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  have := Nat.le_mul_self (N + (W + 0) + 2)
  omega

theorem so_processes (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    (design.pdesign.instantiateD2 [(N : Int), W]).processes.toList =
      topP N W :: outP W :: (List.range (N - 1)).map (cellP W) := by
  rw [PDesign.instantiateD2_of_ok (so_instantiate2 N W hN hW), PDesign.assemble2_processes,
    so_static N W hN hW]
  simp [design.pdesign]

/-- Two cells drive disjoint windows. -/
theorem cell_disj {W k k' : Nat} (h : k < k') :
    ∀ a ∈ (cellP W k).procWins, ∀ b ∈ (cellP W k').procWins, a.overlaps b = false := by
  have := Nat.mul_le_mul_right W (show k + 1 ≤ k' by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  simp [cellP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    DrvWin.overlaps]
  omega

/-- The top cell and the output register drive no window of a cell `k < N - 1`. -/
theorem top_disj {N W k : Nat} (h : k + 1 < N) :
    (∀ a ∈ (topP N W).procWins, ∀ b ∈ (cellP W k).procWins, a.overlaps b = false) ∧
      ∀ a ∈ (outP W).procWins, ∀ b ∈ (cellP W k).procWins, a.overlaps b = false := by
  have := Nat.mul_le_mul_right W (show k + 1 ≤ N - 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  constructor <;>
  simp [topP, outP, cellP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, DrvWin.overlaps] <;> omega

theorem so_pairwise (N W : Nat) : (topP N W :: outP W :: (List.range (N - 1)).map (cellP W)).Pairwise
    fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) ?_)
  · rcases List.mem_cons.mp hp with rfl | hp
    · simp [topP, outP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps]
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact (top_disj (by have := List.mem_range.mp hk; omega)).1
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact (top_disj (N := N) (by have := List.mem_range.mp hk; omega)).2
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ h => cell_disj h)

theorem so_driversOk (N W : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames
      (topP N W :: outP W :: (List.range (N - 1)).map (cellP W)) = true := by
  apply driversOk_of_ff ?_ ?_ (so_pairwise N W)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp; exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, List.mem_cons, List.mem_map]
    rintro n ⟨p, hp | hp | ⟨k, -, rfl⟩, hn⟩
    all_goals try subst hp
    all_goals revert n; simp [topP, outP, cellP, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide

/-- **The loaded family is `soD`**, at every `(N, W)` with positive parameters. -/
theorem so_sem_eq (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : design.sem N W = soD N W := by
  have h1 : design.sem N W = design.pdesign.instantiateD2 [(N : Int), W] := by
    show design.pdesign.instantiateGD2 [(N : Int), W] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [so_processes N W hN hW]; exact so_driversOk N W)
  rw [h1, PDesign.instantiateD2_of_ok (so_instantiate2 N W hN hW)]
  simp only [PDesign.assemble2, so_static N W hN hW, soD]
  simp [design.pdesign]

/-! ## 2. G0's clock step for the loaded family -/

theorem so_profile (N W : Nat) (hN : 1 ≤ N) : (soD N W).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simpa [soD] using so_pairwise N W)⟩
  have h1 := Nat.mul_le_mul_right W (show N - 1 + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  simp [soD, topP, outP, cellP, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, soDeclsW]

/-- The 9 signals of `soD`, in declaration order. -/
def SS (ck r s iv id ov od dt tk : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("in_valid", iv), ("in_data", id), ("out_valid", ov),
    ("out_data", od), ("data", dt), ("tok", tk)]

theorem apply_so (N W : Nat) (e : SvState) (ck r s iv id ov od dt tk : LVec) :
    applyInputs2 (soD N W) e (SS ck r s iv id ov od dt tk) = SS (appIn e "clk" ck) (appIn e "rst" r)
      (appIn e "start" s) (appIn e "in_valid" iv) (appIn e "in_data" id) ov od dt tk := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "in_valid" <;>
    cases h5 : SvState.lookup e "in_data" <;>
    simp [soD, soDeclsW, SS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- An `in_data > x` test, as the clock step evaluates it. -/
abbrev gtc (a b : LVec) : Bool := (LVec.ofLogic (a.gt b)).condTrue

/-- The top cell's updates, from the pre-edge values. -/
def topQ (N W : Nat) (r iv id dt : LVec) : NbaQueue2 :=
  (if iv.condTrue then (if gtc id (dt.extract ((N - 1) * W) W) then [("data", (N - 1) * W, id.resizeU W)] else [])
    else [("data", (N - 1) * W, .ofBitVec 0#W)]) ++ ("tok", N - 1, iv.resizeU 1) ::
  (if r.condTrue then [("data", (N - 1) * W, .ofBitVec 0#W), ("tok", N - 1, .ofBitVec 0#1)] else [])

/-- The output register's updates. -/
def outQ (W : Nat) (r ov od dt tk : LVec) : NbaQueue2 :=
  ("out_valid", 0, (tk.extract 0 1).resizeU ov.width) :: ("out_data", 0, (dt.extract 0 W).resizeU od.width) ::
  (if r.condTrue then [("out_valid", 0, .ofBitVec 0#ov.width)] else [])

/-- Cell `k`'s updates. -/
def cellQ (W : Nat) (r iv id dt tk : LVec) (k : Nat) : NbaQueue2 :=
  (if iv.condTrue then
      (if gtc id (dt.extract ((k + 1) * W) W) then [("data", k * W, (dt.extract ((k + 1) * W) W).resizeU W)]
      else if gtc id (dt.extract (k * W) W) then [("data", k * W, id.resizeU W)] else [])
    else [("data", k * W, (dt.extract ((k + 1) * W) W).resizeU W)]) ++
  ("tok", k, (tk.extract (k + 1) 1).resizeU 1) ::
  (if r.condTrue then [("data", k * W, .ofBitVec 0#W), ("tok", k, .ofBitVec 0#1)] else [])

section run
variable (F : Nat) (hF : 30 ≤ F) (ck r s iv id ov od dt tk : LVec)
include hF

theorem out_run (W : Nat) : runEdgeProcess2 F (SS ck r s iv id ov od dt tk) [] (outP W) =
    .ok (SS ck r s iv id ov od dt tk, outQ W r ov od dt tk) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  by_cases h1 : r.condTrue = true <;>
    simp [outP, outQ, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, h1]

theorem top_run (N W : Nat) : runEdgeProcess2 F (SS ck r s iv id ov od dt tk) [] (topP N W) =
    .ok (SS ck r s iv id ov od dt tk, topQ N W r iv id dt) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  by_cases h1 : r.condTrue = true <;> by_cases h2 : iv.condTrue = true <;>
    by_cases h3 : gtc id (dt.extract ((N - 1) * W) W) = true <;>
    simp [topP, topQ, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h1, h2, h3]

theorem cell_run (W k : Nat) : runEdgeProcess2 F (SS ck r s iv id ov od dt tk) [] (cellP W k) =
    .ok (SS ck r s iv id ov od dt tk, cellQ W r iv id dt tk k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  by_cases h1 : r.condTrue = true <;> by_cases h2 : iv.condTrue = true <;>
    by_cases h3 : gtc id (dt.extract ((k + 1) * W) W) = true <;>
    by_cases h4 : gtc id (dt.extract (k * W) W) = true <;>
    simp [cellP, cellQ, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h1, h2, h3, h4]

end run

/-- The cycle's updates, in process order. -/
def Q (N W : Nat) (r iv id ov od dt tk : LVec) : NbaQueue2 :=
  topQ N W r iv id dt ++ outQ W r ov od dt tk ++ (List.range (N - 1)).flatMap (cellQ W r iv id dt tk)

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def soNext (N W : Nat) (ck r s iv id ov od dt tk : LVec) : SvState :=
  commitNba2 (SS ck r s iv id ov od dt tk) (Q N W r iv id ov od dt tk)

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus
entry, any state of the design's shape, every fuel from 30). -/
theorem so_cycle (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (σ : ScheduleOracle) (e : SvState)
    (ck r s iv id ov od dt tk : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W) σ F e (SS ck r s iv id ov od dt tk) kk =
      .ok (soNext N W (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "in_valid" iv)
        (appIn e "in_data" id) ov od dt tk, kk + 3) := by
  have hmem : ∀ p ∈ (soD N W).processes.toList, p = topP N W ∨ p = outP W ∨ ∃ k, p = cellP W k := by
    intro p hp
    simp only [soD, List.toList_toArray, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨k, -, rfl⟩ <;>
      first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr ⟨_, rfl⟩)
  have hedge : ∀ p ∈ (soD N W).processes.toList, p.isEdgePhase = true := by
    intro p hp; rcases hmem p hp with rfl | rfl | ⟨k, rfl⟩ <;> rfl
  rw [so_sem_eq N W hN hW, cycleStep2_profile (so_profile N W hN) σ e _ kk ?_ ?_ (by omega),
    apply_so, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [soD, List.toList_toArray, List.flatMap_cons, top_run F hF, out_run F hF, List.flatMap_map,
      cell_run F hF, soNext, Q, List.append_assoc]
  · intro i p hp
    rw [apply_so]
    rcases hmem p (List.mem_of_getElem? (by simpa using hp)) with rfl | rfl | ⟨k, rfl⟩
    · exact ⟨_, top_run F hF _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, out_run F hF _ _ _ _ _ _ _ _ _ W⟩
    · exact ⟨_, cell_run F hF _ _ _ _ _ _ _ _ _ W k⟩
  · rw [apply_so]; simp [SS]

/-! ## 3. The commit, register by register (`nbaFold`, `LeanModels.Sv.SeqFamily`) -/

section commit
variable {ck r s iv id ov od dt tk : LVec} {lo : Nat} {v : LVec}
theorem nb_ov : nbaStep (SS ck r s iv id ov od dt tk) ("out_valid", lo, v) = SS ck r s iv id (ov.insertAt lo v) od dt tk := by
  simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_od : nbaStep (SS ck r s iv id ov od dt tk) ("out_data", lo, v) = SS ck r s iv id ov (od.insertAt lo v) dt tk := by
  simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_dt : nbaStep (SS ck r s iv id ov od dt tk) ("data", lo, v) = SS ck r s iv id ov od (dt.insertAt lo v) tk := by
  simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_tk : nbaStep (SS ck r s iv id ov od dt tk) ("tok", lo, v) = SS ck r s iv id ov od dt (tk.insertAt lo v) := by
  simp [nbaStep, SS, SvState.lookup, SvState.set]
end commit

/-- Committing a queue of writes to the four registers. -/
theorem commit_SS {ck r s iv id : LVec} : ∀ (q : NbaQueue2) (ov od dt tk : LVec),
    (∀ u ∈ q, u.1 = "out_valid" ∨ u.1 = "out_data" ∨ u.1 = "data" ∨ u.1 = "tok") →
    commitNba2 (SS ck r s iv id ov od dt tk) q =
      SS ck r s iv id (nbaFold "out_valid" q ov) (nbaFold "out_data" q od) (nbaFold "data" q dt) (nbaFold "tok" q tk)
  | [], _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, ov, od, dt, tk, h => by
    have hq := @commit_SS ck r s iv id q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;>
      simp [commitNba2_cons, nb_ov, nb_od, nb_dt, nb_tk, hq _ _ _ _ h', nbaFold]

/-! ## 4. The registers through a cycle -/

attribute [local simp] condTrue_knownBit

/-- A cell's load rule: take the pushed upper neighbour's value, or the input, or hold. -/
def hwCell {W : Nat} (N : Nat) (x : BitVec W) (v : Nat → BitVec W) (k : Nat) : BitVec W :=
  if k + 1 < N then (if v (k + 1) < x then v (k + 1) else if v k < x then x else v k)
  else if v k < x then x else v k

/-- The cells after a cycle without reset: a load of `x` (`b`), or a drain (shift down, `0` in). -/
def cstep {W : Nat} (N : Nat) (b : Bool) (x : BitVec W) (v : Nat → BitVec W) (k : Nat) : BitVec W :=
  if b then hwCell N x v k else if k + 1 < N then v (k + 1) else 0

/-- The tokens after a cycle without reset: shift down, `in_valid` in at the top. -/
def tstep (N : Nat) (b : Bool) (T : Nat → BitVec 1) (k : Nat) : BitVec 1 :=
  if k + 1 < N then T (k + 1) else BitVec.ofBool b

theorem so_names (N W : Nat) (r iv id ov od dt tk : LVec) : ∀ u ∈ Q N W r iv id ov od dt tk,
    u.1 = "out_valid" ∨ u.1 = "out_data" ∨ u.1 = "data" ∨ u.1 = "tok" := by
  have h : ∀ q : NbaQueue2, q.all (fun u => u.1 == "out_valid" || u.1 == "out_data" || u.1 == "data" ||
      u.1 == "tok") = true → ∀ u ∈ q, u.1 = "out_valid" ∨ u.1 = "out_data" ∨ u.1 = "data" ∨ u.1 = "tok" :=
    fun q h u hu => by simpa [or_assoc] using List.all_eq_true.mp h u hu
  refine h _ ?_
  simp only [Q, List.all_append, List.all_flatMap, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, List.all_eq_true.mpr fun k _ => ?_⟩
  · unfold topQ; (repeat' split) <;> simp
  · unfold outQ; (repeat' split) <;> simp
  · unfold cellQ; (repeat' split) <;> simp

section skip
variable {n : String} (x : LVec)
theorem top_skip (h1 : n ≠ "data") (h2 : n ≠ "tok") (N W : Nat) (r iv id dt : LVec) :
    nbaFold n (topQ N W r iv id dt) x = x := by
  unfold topQ; (repeat' split) <;> simp [nbaFold, Ne.symm h1, Ne.symm h2]
theorem cell_skip (h1 : n ≠ "data") (h2 : n ≠ "tok") (W : Nat) (r iv id dt tk : LVec) (k : Nat) :
    nbaFold n (cellQ W r iv id dt tk k) x = x := by
  unfold cellQ; (repeat' split) <;> simp [nbaFold, Ne.symm h1, Ne.symm h2]
end skip

/-- The output register's signals: only `outQ` writes them. -/
theorem fdQ_out (n : String) (h1 : n ≠ "data") (h2 : n ≠ "tok") {N W : Nat} {r iv id ov od dt tk : LVec}
    (x : LVec) : nbaFold n (Q N W r iv id ov od dt tk) x = nbaFold n (outQ W r ov od dt tk) x := by
  rw [Q, nbaFold_append, nbaFold_append, top_skip x h1 h2,
    nbaFold_flatMap_eq_self (fun k y => cell_skip y h1 h2 W r iv id dt tk k)]

/-- The cell array's signals: the top cell, then the cells `0 … N-2`. -/
theorem fdQ_reg (n : String) (h1 : n ≠ "out_valid") (h2 : n ≠ "out_data") {N W : Nat} {r iv id ov od dt tk : LVec}
    (x : LVec) : nbaFold n (Q N W r iv id ov od dt tk) x =
      (List.range (N - 1)).foldl (fun acc k => nbaFold n (cellQ W r iv id dt tk k) acc) (nbaFold n (topQ N W r iv id dt) x) := by
  have : nbaFold n (outQ W r ov od dt tk) = fun y => y := by
    funext y; unfold outQ; (repeat' split) <;> simp [nbaFold, Ne.symm h1, Ne.symm h2]
  rw [Q, nbaFold_append, nbaFold_append, this, nbaFold_flatMap]

theorem gtc_ofBitVec {W : Nat} (a b : BitVec W) : gtc (.ofBitVec a) (.ofBitVec b) = decide (b < a) := by
  by_cases h : b < a <;> simp [gtc, h]

attribute [local simp] gtc_ofBitVec

theorem cell_data {N W k : Nat} (hk : k + 1 < N) (b : Bool) (x : BitVec W) (v u : Nat → BitVec W)
    (hu : u k = v k) (id tk : LVec) (hid : b = true → id = .ofBitVec x) :
    nbaFold "data" (cellQ W (knownBit false) (knownBit b) id (.ofBitVec (packBV W N v)) tk k)
        (.ofBitVec (packBV W N u)) =
      .ofBitVec (packBV W N (fun i => if i = k then cstep N b x v k else u i)) := by
  have e1 := extract_ofBitVec_packBV (W := W) v hk rfl
  have e0 := extract_ofBitVec_packBV (W := W) v (show k < N by omega) rfl
  have hup := fun a => bvInsertAt_packBV (W := W) u a (show k < N by omega) rfl
  have hold : packBV W N (fun i => if i = k then v k else u i) = packBV W N u :=
    congrArg _ (funext fun i => by split <;> simp_all)
  cases b
  · simp [cellQ, nbaFold, e1, cstep, hk, hup]
  · obtain rfl := hid rfl
    by_cases h1 : v (k + 1) < x <;> by_cases h2 : v k < x <;>
      simp [cellQ, nbaFold, e1, e0, cstep, hwCell, hk, h1, h2, hup, hold]

theorem top_data {N W : Nat} (hN : 1 ≤ N) (b : Bool) (x : BitVec W) (v u : Nat → BitVec W)
    (hu : u (N - 1) = v (N - 1)) (id : LVec) (hid : b = true → id = .ofBitVec x) :
    nbaFold "data" (topQ N W (knownBit false) (knownBit b) id (.ofBitVec (packBV W N v))) (.ofBitVec (packBV W N u)) =
      .ofBitVec (packBV W N (fun i => if i = N - 1 then cstep N b x v (N - 1) else u i)) := by
  have e0 := extract_ofBitVec_packBV (W := W) v (show N - 1 < N by omega) rfl
  have hup := fun a => bvInsertAt_packBV (W := W) u a (show N - 1 < N by omega) rfl
  have hold : packBV W N (fun i => if i = N - 1 then v (N - 1) else u i) = packBV W N u :=
    congrArg _ (funext fun i => by split <;> simp_all)
  have hn : ¬ (N - 1 + 1 < N) := by omega
  cases b
  · simp [topQ, nbaFold, cstep, hn, hup]
  · obtain rfl := hid rfl
    by_cases h2 : v (N - 1) < x <;> simp [topQ, nbaFold, e0, cstep, hwCell, hn, h2, hup, hold]

theorem cell_tok {N W k : Nat} (hk : k + 1 < N) (iv id dt : LVec) (T u : Nat → BitVec 1) :
    nbaFold "tok" (cellQ W (knownBit false) iv id dt (.ofBitVec (packBV 1 N T)) k) (.ofBitVec (packBV 1 N u)) =
      .ofBitVec (packBV 1 N (fun i => if i = k then T (k + 1) else u i)) := by
  have e := extract_ofBitVec_packBV T hk (Nat.mul_one _).symm
  have hup := bvInsertAt_packBV u (T (k + 1)) (show k < N by omega) (Nat.mul_one k).symm
  simp only [cellQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte]; (repeat' split) <;> simp [nbaFold, e, hup]

theorem top_tok {N W : Nat} (hN : 1 ≤ N) (b : Bool) (id dt : LVec) (u : Nat → BitVec 1) :
    nbaFold "tok" (topQ N W (knownBit false) (knownBit b) id dt) (.ofBitVec (packBV 1 N u)) =
      .ofBitVec (packBV 1 N (fun i => if i = N - 1 then BitVec.ofBool b else u i)) := by
  have hup := bvInsertAt_packBV u (BitVec.ofBool b) (show N - 1 < N by omega) (Nat.mul_one _).symm
  simp only [topQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte]; (repeat' split) <;> simp [nbaFold, hup]

section reset
variable (x : LVec)
theorem top_reset (N W : Nat) (iv id dt : LVec) :
    nbaFold "data" (topQ N W (knownBit true) iv id dt) x = x.insertAt ((N - 1) * W) (.ofBitVec 0#W) ∧
      nbaFold "tok" (topQ N W (knownBit true) iv id dt) x = x.insertAt ((N - 1) * 1) (.ofBitVec 0#1) := by
  simp only [topQ, condTrue_knownBit, ↓reduceIte]; (repeat' split) <;>
    simp [nbaFold, LVec.insertAt_insertAt_of_width_le]
theorem cell_reset (W : Nat) (iv id dt tk : LVec) (k : Nat) :
    nbaFold "data" (cellQ W (knownBit true) iv id dt tk k) x = x.insertAt (k * W) (.ofBitVec 0#W) ∧
      nbaFold "tok" (cellQ W (knownBit true) iv id dt tk k) x = x.insertAt (k * 1) (.ofBitVec 0#1) := by
  simp only [cellQ, condTrue_knownBit, ↓reduceIte]; (repeat' split) <;>
    simp [nbaFold, LVec.insertAt_insertAt_of_width_le]
end reset

/-- The cells (or tokens) all `0`. -/
abbrev Z (W N : Nat) : LVec := .ofBitVec (packBV W N fun _ => 0)

/-- **A reset cycle** clears the cells, the tokens and `out_valid`. -/
theorem next_reset {N W : Nat} (hN : 1 ≤ N) (ck s iv id ov od dt tk : LVec) (hov : ov.width = 1)
    (hdt : dt.width = N * W) (htk : tk.width = N) :
    ∃ od', soNext N W ck (knownBit true) s iv id ov od dt tk =
      SS ck (knownBit true) s iv id (knownBit false) od' (Z W N) (Z 1 N) := by
  have h0 : LVec.ofBitVec 0#ov.width = knownBit false := by rw [← LVec.replicate_l0, hov]; decide
  rw [soNext, commit_SS _ _ _ _ _ (so_names _ _ _ _ _ _ _ _ _), fdQ_out "out_valid" (by decide) (by decide),
    fdQ_reg "data" (by decide) (by decide), fdQ_reg "tok" (by decide) (by decide), (top_reset ..).1, (top_reset ..).2]
  simp only [(cell_reset ..).1, (cell_reset ..).2]
  rw [LVec.foldl_range_insertAt_last hN _ dt (by simp), LVec.insertEntries_ofBitVec (fun _ => 0#W) dt hdt,
    LVec.foldl_range_insertAt_last hN _ tk (by simp), LVec.insertEntries_ofBitVec (fun _ => 0#1) tk (by simp [htk])]
  refine ⟨nbaFold "out_data" (Q N W (knownBit true) iv id ov od dt tk) od, ?_⟩
  congr 1
  simp [outQ, nbaFold, LVec.insertAt_zero_of_width_eq, hov, h0]

theorem data_fold {N W : Nat} (hN : 1 ≤ N) (b : Bool) (x : BitVec W) (v : Nat → BitVec W) (id tk : LVec)
    (hid : b = true → id = .ofBitVec x) :
    (List.range (N - 1)).foldl
        (fun acc k => nbaFold "data" (cellQ W (knownBit false) (knownBit b) id (.ofBitVec (packBV W N v)) tk k) acc)
      (nbaFold "data" (topQ N W (knownBit false) (knownBit b) id (.ofBitVec (packBV W N v)))
        (.ofBitVec (packBV W N v))) =
      .ofBitVec (packBV W N (cstep N b x v)) := by
  rw [top_data hN b x v v rfl id hid,
    foldl_range_ofBitVec_packBV (W := W) (N := N) _ (cstep N b x v) _ (N - 1) ?_]
  · refine congrArg _ (packBV_congr fun i hi => ?_)
    by_cases h : i < N - 1
    · simp [h]
    · obtain rfl : i = N - 1 := by omega
      simp
  · intro k u' hk hu'
    exact cell_data (by omega) b x v u' (by rw [hu']; simp [show k ≠ N - 1 by omega]) id tk hid

theorem tok_fold {N W : Nat} (hN : 1 ≤ N) (b : Bool) (T : Nat → BitVec 1) (id dt : LVec) :
    (List.range (N - 1)).foldl
        (fun acc k => nbaFold "tok" (cellQ W (knownBit false) (knownBit b) id dt (.ofBitVec (packBV 1 N T)) k) acc)
      (nbaFold "tok" (topQ N W (knownBit false) (knownBit b) id dt) (.ofBitVec (packBV 1 N T))) =
      .ofBitVec (packBV 1 N (tstep N b T)) := by
  rw [top_tok hN b id dt T,
    foldl_range_ofBitVec_packBV (W := 1) (N := N) _ (fun k => T (k + 1)) _ (N - 1) ?_]
  · refine congrArg _ (packBV_congr fun i hi => ?_)
    by_cases h : i < N - 1
    · simp [h, tstep, show i + 1 < N by omega]
    · obtain rfl : i = N - 1 := by omega
      simp [tstep, show ¬ (N - 1 + 1 < N) by omega]
  · intro k u' hk _
    exact cell_tok (by omega) _ _ _ T u'

/-- **A cycle without reset** on known cells and tokens: a load of `x` (`b`) or a drain. -/
theorem next_run {N W : Nat} (hN : 1 ≤ N) (b : Bool) (x : BitVec W) (v : Nat → BitVec W) (T : Nat → BitVec 1)
    (ck s id ov od : LVec) (hid : b = true → id = .ofBitVec x) (hov : ov.width = 1) (hod : od.width = W) :
    soNext N W ck (knownBit false) s (knownBit b) id ov od (.ofBitVec (packBV W N v)) (.ofBitVec (packBV 1 N T)) =
      SS ck (knownBit false) s (knownBit b) id (.ofBitVec (T 0)) (.ofBitVec (v 0))
        (.ofBitVec (packBV W N (cstep N b x v))) (.ofBitVec (packBV 1 N (tstep N b T))) := by
  rw [soNext, commit_SS _ _ _ _ _ (so_names _ _ _ _ _ _ _ _ _), fdQ_out "out_valid" (by decide) (by decide),
    fdQ_out "out_data" (by decide) (by decide), fdQ_reg "data" (by decide) (by decide),
    fdQ_reg "tok" (by decide) (by decide), data_fold hN b x v id _ hid, tok_fold hN b T id _]
  simp [outQ, nbaFold, extract_ofBitVec_packBV T (show 0 < N by omega) (Nat.zero_mul 1).symm,
    extract_ofBitVec_packBV v (show 0 < N by omega) (Nat.zero_mul W).symm, hov, hod, LVec.insertAt_zero_of_width_eq]

/-! ## 5. Shape and termination -/

/-- A snapshot of the design's shape (register widths; any values, `x` included). -/
def I (N W : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk, st = SS ck r s iv id ov od dt tk ∧
    (ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N)

theorem next_I {N W : Nat} (ck r s iv id ov od dt tk : LVec)
    (hw : ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N) :
    I N W (soNext N W ck r s iv id ov od dt tk) := by
  rw [soNext, commit_SS _ _ _ _ _ (so_names _ _ _ _ _ _ _ _ _)]
  exact ⟨_, _, _, _, _, _, _, _, _, rfl, by simp [width_nbaFold, hw]⟩

theorem so_init (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : I N W (initState2 (design.sem N W)) := by
  rw [so_sem_eq N W hN hW]
  exact ⟨.xVec 1, .xVec 1, .xVec 1, .xVec 1, .xVec W, .xVec 1, .xVec W, .xVec (N * W), .xVec N,
    by simp [initState2, soD, soDeclsW, SS], by simp⟩

/-- **Termination**: every schedule and every stimulus completes. -/
theorem so_terminates (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : Terminates2 (design.sem N W) := by
  refine Terminates2.of_invariant (I N W) (so_init N W hN hW) (fun σ => ⟨30, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hw⟩
    exact ⟨_, _, so_cycle N W hN hW σ e ck r s iv id ov od dt tk kk 30 (Nat.le_refl _), next_I _ _ _ _ _ _ _ _ _ hw⟩
  · rw [so_sem_eq N W hN hW]
    simp [soD, topP, outP, cellP, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

/-! ## 6. The sort: `insertAsc` and `sortAsc` (core Lean only) -/

open Tasks.Sorter (insertAsc sortAsc)

/-- Ascending in the unsigned order. -/
abbrev Srt {W : Nat} (l : List (BitVec W)) : Prop := l.Pairwise fun a b => a.toNat ≤ b.toNat

theorem mem_ins {W : Nat} (x y : BitVec W) : ∀ l, y ∈ insertAsc x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insertAsc]
  | b :: l => by unfold insertAsc; split <;> simp [mem_ins x y l, or_left_comm]

theorem srt_ins {W : Nat} (x : BitVec W) : ∀ l, Srt l → Srt (insertAsc x l)
  | [], _ => by simp [insertAsc]
  | b :: l, h => by
    have ⟨hb, hl⟩ := List.pairwise_cons.mp h
    unfold insertAsc
    split
    · next hx =>
      refine .cons (fun y hy => ?_) h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact Nat.le_trans hx (hb y hy)
    · next hx =>
      refine .cons (fun y hy => ?_) (srt_ins x l hl)
      rcases (mem_ins x y l).mp hy with rfl | hy
      · omega
      · exact hb y hy

theorem len_ins {W : Nat} (x : BitVec W) : ∀ l, (insertAsc x l).length = l.length + 1
  | [] => rfl
  | b :: l => by unfold insertAsc; split <;> simp [len_ins x l]

theorem len_sort {W : Nat} : ∀ l : List (BitVec W), (sortAsc l).length = l.length
  | [] => rfl
  | a :: l => by simp [sortAsc, len_ins, len_sort l]

theorem srt_sort {W : Nat} : ∀ l : List (BitVec W), Srt (sortAsc l)
  | [] => .nil
  | _ :: l => srt_ins _ _ (srt_sort l)

theorem ins_comm_lt {W : Nat} {a b : BitVec W} (h : a.toNat < b.toNat) :
    ∀ l, insertAsc a (insertAsc b l) = insertAsc b (insertAsc a l)
  | [] => by simp [insertAsc, Nat.le_of_lt h, Nat.not_le.mpr h]
  | c :: l => by
    by_cases hb : b.toNat ≤ c.toNat
    · simp [insertAsc, hb, Nat.le_of_lt h, Nat.not_le.mpr h, show a.toNat ≤ c.toNat by omega]
    · by_cases ha : a.toNat ≤ c.toNat
      · simp [insertAsc, hb, ha, Nat.not_le.mpr h]
      · simp [insertAsc, hb, ha, ins_comm_lt h l]

/-- **Insertions commute** (equal values are equal: the unsigned order is total). -/
theorem ins_comm {W : Nat} (a b : BitVec W) (l : List (BitVec W)) :
    insertAsc a (insertAsc b l) = insertAsc b (insertAsc a l) := by
  rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
  · exact ins_comm_lt h l
  · rw [BitVec.eq_of_toNat_eq h]
  · exact (ins_comm_lt h l).symm

/-- Inserting the last value last: `sortAsc (l ++ [x]) = insertAsc x (sortAsc l)`. -/
theorem sort_snoc {W : Nat} (x : BitVec W) : ∀ l : List (BitVec W), sortAsc (l ++ [x]) = insertAsc x (sortAsc l)
  | [] => rfl
  | a :: l => by simp only [List.cons_append, sortAsc, sort_snoc x l]; exact ins_comm ..

/-- The dropped head of a load is a padding `0` (or `x = 0` changes nothing). -/
theorem tail_ins {W : Nat} (x : BitVec W) (S : List (BitVec W)) (m : Nat) :
    (insertAsc x (List.replicate (m + 1) 0 ++ S)).tail = List.replicate m 0 ++ insertAsc x S := by
  by_cases hx : x.toNat = 0
  · obtain rfl : x = 0 := BitVec.eq_of_toNat_eq (by simp [hx])
    have h0 : ∀ L : List (BitVec W), insertAsc 0 L = 0 :: L := fun L => by cases L <;> simp [insertAsc]
    rw [h0, h0, List.tail_cons, List.replicate_succ', List.append_assoc]; rfl
  · have hz : ∀ m, insertAsc x (List.replicate m 0 ++ S) = List.replicate m 0 ++ insertAsc x S := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [List.replicate_succ, List.cons_append, insertAsc, if_neg (by simp [hx]), ih]; rfl
    rw [List.replicate_succ, List.cons_append, insertAsc, if_neg (by simp [hx]), List.tail_cons, hz]

theorem lt_or_le' (a b : Nat) : (a < b ∧ ¬ b ≤ a) ∨ (b ≤ a ∧ ¬ a < b) := by omega

/-- **The cell array's load is `tail ∘ insertAsc x`** on an ascending list. -/
theorem hw_ins {W : Nat} (x : BitVec W) : ∀ L : List (BitVec W), Srt L → ∀ k, k < L.length →
    hwCell L.length x (fun i => L.getD i 0) k = (insertAsc x L).tail.getD k 0
  | [], _, k, hk => absurd hk (Nat.not_lt_zero _)
  | b :: L, hs, k, hk => by
    have ⟨hb, hL⟩ := List.pairwise_cons.mp hs
    cases k with
    | zero =>
      cases L with
      | nil =>
        rcases lt_or_le' b.toNat x.toNat with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
          simp [hwCell, insertAsc, BitVec.lt_def, h1, h1']
      | cons c L =>
        have hbc := hb c (by simp)
        rcases lt_or_le' b.toNat x.toNat with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
          rcases lt_or_le' c.toNat x.toNat with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
          simp [hwCell, insertAsc, BitVec.lt_def, h1, h1', h2, h2'] <;> omega
    | succ k =>
      have e : hwCell (L.length + 1) x (fun i => (b :: L).getD i 0) (k + 1) =
          hwCell L.length x (fun i => L.getD i 0) k := by simp [hwCell]
      rw [List.length_cons, e, hw_ins x L hL k (by simp at hk; omega)]
      by_cases h1 : x.toNat ≤ b.toNat
      · have : (insertAsc x L).tail = L := by
          cases L with
          | nil => rfl
          | cons c L => simp [insertAsc, Nat.le_trans h1 (hb c (by simp))]
        simp [insertAsc, h1, this]
      · cases h : insertAsc x L <;> simp [insertAsc, h1, h]

/-! ## 7. The invariant: the cells, the tokens, the output -/

/-- The cells `j` cycles after a start that received `ys`: `[0]^(N-j) ++ sortAsc ys` while loading,
then shifted down by `j - N` with `0`s in (`getD`). -/
def cv {W : Nat} (N : Nat) (ys : List (BitVec W)) (j k : Nat) : BitVec W :=
  (List.replicate (N - j) 0 ++ sortAsc ys).getD (k + (j - N)) 0

/-- Token `k`, `j` cycles after a start: `in_valid` of the entry `j - (N - 1 - k)` after it (a delay line). -/
def tokv (N j : Nat) (k : Nat) : BitVec 1 := BitVec.ofBool (decide (N ≤ j + k ∧ j + k + 1 ≤ 2 * N))

/-- `out_valid`, `j` cycles after a start. -/
def ovb (N j : Nat) : Bool := decide (N < j ∧ j ≤ 2 * N)

theorem srt_pad {W : Nat} (m : Nat) {S : List (BitVec W)} (h : Srt S) : Srt (List.replicate m 0 ++ S) :=
  List.pairwise_append.mpr ⟨List.pairwise_replicate.mpr (.inr (Nat.le_refl _)), h,
    fun a ha b _ => by simp [List.eq_of_mem_replicate ha]⟩

theorem feed_cells {W N j : Nat} (ys : List (BitVec W)) (x : BitVec W) (hj : j < N) (hl : ys.length = j)
    {k : Nat} (hk : k < N) : cstep N true x (cv N ys j) k = cv N (ys ++ [x]) (j + 1) k := by
  have hL : (List.replicate (N - j) 0 ++ sortAsc ys).length = N := by simp [len_sort, hl]; omega
  have hv : cv N ys j = fun i => (List.replicate (N - j) 0 ++ sortAsc ys).getD i 0 := by
    funext i; simp [cv, Nat.sub_eq_zero_of_le (Nat.le_of_lt hj)]
  have := hw_ins x _ (srt_pad (N - j) (srt_sort ys)) k (by omega)
  rw [hL] at this
  simp only [cstep, ↓reduceIte]
  rw [hv, this, show N - j = N - (j + 1) + 1 by omega, tail_ins]
  simp [cv, sort_snoc, Nat.sub_eq_zero_of_le (show j + 1 ≤ N by omega)]

theorem run_cells {W N j : Nat} (xs : List (BitVec W)) (x : BitVec W) (hj : N ≤ j) (hl : xs.length = N)
    {k : Nat} (hk : k < N) : cstep N false x (cv N xs j) k = cv N xs (j + 1) k := by
  simp only [cstep, cv, Bool.false_eq_true, ↓reduceIte, Nat.sub_eq_zero_of_le hj,
    Nat.sub_eq_zero_of_le (show N ≤ j + 1 by omega), List.replicate_zero, List.nil_append]
  split
  · congr 1; omega
  · simp [List.getD_eq_getElem?_getD, len_sort, hl, show N ≤ k + (j + 1 - N) by omega]

theorem tok_step {N j k : Nat} (b : Bool) (hb : b = decide (j + 1 ≤ N)) (hk : k < N) :
    tstep N b (tokv N j) k = tokv N (j + 1) k := by
  simp only [tstep, tokv]; split
  · congr 1; simp only [decide_eq_decide]; omega
  · rw [hb]; congr 1; simp only [decide_eq_decide]; omega

/-- **One cycle of a transaction** (a load with `b`, or a drain): the invariant at `j` gives it at `j + 1`. -/
theorem at_step {N W : Nat} (hN : 1 ≤ N) (b : Bool) (x : BitVec W) (ys ys' : List (BitVec W)) (j : Nat)
    (ck s id ov od : LVec) (hid : b = true → id = .ofBitVec x) (hov : ov.width = 1) (hod : od.width = W)
    (hc : ∀ k, k < N → cstep N b x (cv N ys j) k = cv N ys' (j + 1) k) (hb : b = decide (j + 1 ≤ N))
    (ho : ovb N (j + 1) = true → cv N ys j 0 = (sortAsc ys').getD (j + 1 - N - 1) 0) :
    ∃ od', soNext N W ck (knownBit false) s (knownBit b) id ov od (.ofBitVec (packBV W N (cv N ys j)))
        (.ofBitVec (packBV 1 N (tokv N j))) = SS ck (knownBit false) s (knownBit b) id (knownBit (ovb N (j + 1))) od'
        (.ofBitVec (packBV W N (cv N ys' (j + 1)))) (.ofBitVec (packBV 1 N (tokv N (j + 1)))) ∧
      (ovb N (j + 1) = true → od' = .ofBitVec ((sortAsc ys').getD (j + 1 - N - 1) 0)) := by
  have h0 : tokv N j 0 = BitVec.ofBool (ovb N (j + 1)) := by
    simp only [tokv, ovb]; congr 1; simp only [decide_eq_decide]; omega
  rw [next_run hN b x _ _ ck s id ov od hid hov hod, packBV_congr hc, packBV_congr fun k hk => tok_step b hb hk, h0]
  exact ⟨_, rfl, fun h => by rw [ho h]⟩

/-! ## 8. The protocol: the phases of `StreamTask.satisfiedAt_of_phases`, and the statement -/

/-- One cycle from a state of the shape, evaluated (`so_cycle`). -/
def Stp (N W : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk, prev = SS ck r s iv id ov od dt tk ∧
    (ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N) ∧
    st = soNext N W (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "in_valid" iv)
      (appIn e "in_data" id) ov od dt tk

theorem SS_inj {ck r s iv id ov od dt tk ck' r' s' iv' id' ov' od' dt' tk' : LVec}
    (h : SS ck r s iv id ov od dt tk = SS ck' r' s' iv' id' ov' od' dt' tk') : ov = ov' ∧ dt = dt' ∧ tk = tk' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

/-- From zero cells and tokens, a cycle without reset or input shows nothing and stays. -/
theorem next_zero {N W : Nat} (hN : 1 ≤ N) (ck s id ov od : LVec) (hov : ov.width = 1) (hod : od.width = W) :
    ∃ od', soNext N W ck (knownBit false) s (knownBit false) id ov od (Z W N) (Z 1 N) =
      SS ck (knownBit false) s (knownBit false) id (knownBit false) od' (Z W N) (Z 1 N) := by
  rw [next_run hN false 0 (fun _ => 0) (fun _ => 0) ck s id ov od (by simp) hov hod]
  have h1 : cstep N false 0 (fun _ : Nat => (0 : BitVec W)) = fun _ => 0 := funext fun k => by simp [cstep]
  have h2 : tstep N false (fun _ => 0) = fun _ => 0 := funext fun k => by simp [tstep]
  rw [h1, h2]
  exact ⟨_, rfl⟩

theorem zero_at {W N : Nat} : packBV W N (cv N ([] : List (BitVec W)) 0) = packBV W N (fun _ => 0) ∧
    packBV 1 N (tokv N 0) = packBV 1 N (fun _ => 0) :=
  ⟨packBV_congr fun k hk => by simp [cv, sortAsc, List.getD_eq_getElem?_getD, hk],
    packBV_congr fun k hk => by simp [tokv, show ¬ N ≤ k by omega]⟩

theorem zero_done {W N j : Nat} (xs : List (BitVec W)) (hl : xs.length = N) (hj : 2 * N ≤ j) :
    packBV W N (cv N xs j) = packBV W N (fun _ => 0) ∧ packBV 1 N (tokv N j) = packBV 1 N (fun _ => 0) :=
  ⟨packBV_congr fun k _ => by simp [cv, Nat.sub_eq_zero_of_le (show N ≤ j by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (show (sortAsc xs).length ≤ k + (j - N) by rw [len_sort]; omega)],
    packBV_congr fun k _ => by simp only [tokv]; rw [decide_eq_false (by omega)]; rfl⟩

theorem out_spec_eq {N W : Nat} (xs : List (BitVec W)) (hx : xs.length = N) :
    List.map (·.2) (List.filter (·.1)
      ((List.range N).map fun i => (ovb N (N + 1 + i), (sortAsc xs).getD (N + 1 + i - N - 1) 0))) = sortAsc xs := by
  have h : ((List.range N).map fun i => (ovb N (N + 1 + i), (sortAsc xs).getD (N + 1 + i - N - 1) 0)) =
      (List.range N).map fun i => (true, (sortAsc xs).getD i 0) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi; simp [ovb, show N + 1 + i - N - 1 = i by omega]; omega
  rw [h, List.filter_eq_self.mpr (by simp), List.map_map]
  exact List.ext_getElem (by simp [len_sort, hx]) fun i _ h2 => by simp [List.getElem?_eq_getElem h2]

open Tasks.Sorter in
/-- **The phase model** at `(N, W)`, latency `2N`: `Ready` the zero state after a reset; `At ys j` the
cells, tokens and output `j` cycles after a start that received `ys` (`cv`, `tokv`, `ovb`). -/
def model (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : task.PhaseModel (N, W) (lat N W) (design.sem N W) where
  Shape := I N W
  Step := Stp N W
  init := so_init N W hN hW
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hw⟩ hc
    exact ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (so_cycle N W hN hW σ e ck r s iv id ov od dt tk k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, -, hw, rfl⟩
    exact next_I _ _ _ _ _ _ _ _ _ hw
  Ready st := ∃ ck r s iv id od, st = SS ck r s iv id (knownBit false) od (Z W N) (Z 1 N)
  At ys j st := ∃ ck r s iv id od, st = SS ck r s iv id (knownBit (ovb N j)) od
    (.ofBitVec (packBV W N (cv (W := W) N ys j))) (.ofBitVec (packBV 1 N (tokv N j))) ∧
    (ovb N j = true → od = .ofBitVec ((sortAsc (W := W) ys).getD (j - N - 1) 0))
  out ys j := (ovb N j, (sortAsc (W := W) ys).getD (j - N - 1) 0)
  out_feed _ j hj := by have : j < N := hj; simp [ovb]; omega
  out_lat _ j _ hj := by have : 2 * N < j := hj; simp [ovb]; omega
  out_spec xs hx := by
    rw [show lat N W + 1 = (N + 1) + N by simp [lat]; omega, task.emitted_add, task.emitted_nil ?_, List.nil_append]
    · exact out_spec_eq xs hx
    · intro k hk; simp [ovb]; omega
  ready_out := by rintro st ⟨ck, r, s, iv, id, od, rfl⟩; simp [BitIs, task, SS, SvState.lookup]
  at_out := by
    rintro ys j st ⟨ck, r, s, iv, id, od, rfl, hd⟩
    exact ⟨by simp [BitIs, task, SS, SvState.lookup],
      fun h => by simp [StreamTask.DataIs, task, SS, SvState.lookup, hd h]⟩
  reset := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, -, ⟨h1, -, h3, h4⟩, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨od', h⟩ := next_reset hN (appIn e "clk" ck) (appIn e "start" s) (appIn e "in_valid" iv)
      (appIn e "in_data" id) ov od dt tk h1 h3 h4
    exact ⟨_, _, _, _, _, _, h⟩
  hold := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, ⟨h1, h2, -⟩, rfl⟩ ⟨_, _, _, _, _, _, hb⟩ hr - hiv
    obtain ⟨-, rfl, rfl⟩ := SS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨od', h⟩ := next_zero hN (appIn e "clk" ck) (appIn e "start" s) (appIn e "in_data" id) ov od h1 h2
    exact ⟨_, _, _, _, _, _, h⟩
  start := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, ⟨h1, h2, -⟩, rfl⟩ hp hr - hiv
    have hz : dt = Z W N ∧ tk = Z 1 N := by
      rcases hp with ⟨_, _, _, _, _, _, hb⟩ | ⟨xs, j, hl, ⟨_, _, _, _, _, _, hb, -⟩, hk⟩
      · obtain ⟨-, rfl, rfl⟩ := SS_inj hb; exact ⟨rfl, rfl⟩
      · obtain ⟨-, rfl, rfl⟩ := SS_inj hb
        have hj : 2 * N ≤ j := Nat.le_of_not_lt fun hc => by
          have := hk (max (j + 1) (N + 1)) (by omega); simp [ovb] at this; omega
        exact ⟨congrArg _ (zero_done (W := W) xs hl hj).1, congrArg _ (zero_done (W := W) xs hl hj).2⟩
    obtain ⟨rfl, rfl⟩ := hz
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨od', h⟩ := next_zero hN (appIn e "clk" ck) (appIn e "start" s) (appIn e "in_data" id) ov od h1 h2
    refine ⟨appIn e "clk" ck, knownBit false, appIn e "start" s, knownBit false, appIn e "in_data" id, od', ?_,
      by simp [ovb]⟩
    rw [h, show ovb N 0 = false by simp [ovb]]
    congr 1
    · exact congrArg _ (zero_at (W := W)).1.symm
    · exact congrArg _ (zero_at (W := W)).2.symm
  feed := by
    rintro e prev st ys j x - ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, ⟨h1, h2, -⟩, rfl⟩
      ⟨_, _, _, _, _, _, hb, -⟩ hl hj hr - hiv hx
    have hj' : j < N := hj
    obtain ⟨rfl, rfl, rfl⟩ := SS_inj hb
    have hid : appIn e "in_data" id = .ofBitVec x := by
      simp only [appIn, show SvState.lookup e "in_data" = _ from hx, Option.getD_some]
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit true from BitIs.appIn_eq hiv iv]
    obtain ⟨od', h, ho⟩ := at_step (W := W) hN true x ys (ys ++ [x]) j (appIn e "clk" ck) (appIn e "start" s) _ _ od
      (fun _ => hid) h1 h2 (fun k hk => feed_cells ys x hj' hl hk) (by simp; omega)
      (fun h => by simp [ovb] at h; omega)
    exact ⟨_, _, _, _, _, _, h, ho⟩
  run := by
    rintro e prev st xs j - ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, ⟨h1, h2, -⟩, rfl⟩
      ⟨_, _, _, _, _, _, hb, -⟩ hl hj hr - hiv
    have hl' : xs.length = N := hl
    have hj' : N ≤ j := hj
    obtain ⟨rfl, rfl, rfl⟩ := SS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨od', h, ho⟩ := at_step (W := W) hN false 0 xs xs j (appIn e "clk" ck) (appIn e "start" s) _ _ od
      (by simp) h1 h2 (fun k hk => run_cells xs 0 hj' hl' hk) (by simp; omega)
      (fun _ => by simp [cv, Nat.sub_eq_zero_of_le hj', show j + 1 - N - 1 = j - N by omega])
    exact ⟨_, _, _, _, _, _, h, ho⟩

theorem so_interface (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    Tasks.Sorter.task.Interface (N, W) (design.sem N W) := by
  rw [so_sem_eq N W hN hW]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "in_valid", "in_data", "out_valid", "out_data", "data", "tok"] :
      List String).Nodup
    decide⟩

theorem so_disciplined (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : Tasks.Sorter.task.Disciplined (design.sem N W) := by
  rw [so_sem_eq N W hN hW]
  refine ⟨by simp [Tasks.Sorter.task, soD, soDeclsW, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ topP N W :: outP W :: (List.range (N - 1)).map (cellP W) := by simpa [soD] using hp
  simp only [List.mem_cons, List.mem_map] at hm
  rcases hm with rfl | rfl | ⟨k, -, rfl⟩ <;>
    simp [Tasks.Sorter.task, topP, outP, cellP, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]

/-! ## 9. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3)

Rule 2: the phase model's shape `I` (the register widths, any values) holds at every power-up state
(`so_powerUp`), and every obligation of the model holds from any state of the shape (a reset clears
every cell and token), so the claim holds from every power-up (`StreamTask.satisfiedAtV2_of_phases`,
`SvGolf.SeqV2`); the same cycle gives termination from every power-up (`so_terminatesPU`). Rule 1:
every process is an `always_ff` (`so_profile`), so the design has no combinational dependency at all
(`combDeps_of_ffOnly`). Rule 3 (`so_xsafe`): every expression is a known literal, a declared signal,
an in-range window of `data` or `tok`, or a comparison. -/

/-- **Rule 1.** -/
theorem so_moore (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    MooreOutDep (design.sem N W) [Tasks.Sorter.task.rst] := by
  rw [so_sem_eq N W hN hW]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (so_profile N W hN)))
    (by simp [soD, soDeclsW, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem so_powerUp (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (st : SvState)
    (h : PowerUp (design.sem N W) st) : I N W st := by
  rw [so_sem_eq N W hN hW] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨iv, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨id, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨ov, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨od, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨dt, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨tk, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain rfl := powerUp_nil.mp h9
  exact ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, w6, w7, w8, w9⟩

/-- **Termination from every power-up** (the cycle of `so_terminates`). -/
theorem so_terminatesPU (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : TerminatesPU (design.sem N W) := by
  refine TerminatesPU.of_invariant (I N W) (so_powerUp N W hN hW) (fun σ => ⟨30, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hw⟩
    exact ⟨_, _, so_cycle N W hN hW σ e ck r s iv id ov od dt tk kk 30 (Nat.le_refl _),
      next_I _ _ _ _ _ _ _ _ _ hw⟩
  · rw [so_sem_eq N W hN hW]
    simp [soD, topP, outP, cellP, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

/-- **Rule 3.** -/
theorem so_xsafe (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : XSafe (design.sem N W) := by
  rw [so_sem_eq N W hN hW]
  have hTop : (N - 1) * W + W ≤ N * W := rowMajor_le (K := W) (show N - 1 < N by omega)
  have hOut : 0 + W ≤ N * W := by
    have := rowMajor_le (K := W) (show 0 < N by omega); simpa using this
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ topP N W :: outP W :: (List.range (N - 1)).map (cellP W) := by simpa [soD] using hp
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hm
  rcases hm with rfl | rfl | ⟨k, hk, rfl⟩
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, topP, dw, zW, soD, soDeclsW,
      LVec.replicate_l0, hTop]
    all_goals omega
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, outP, dw, zW, soD, soDeclsW,
      LVec.replicate_l0, hOut]
    all_goals omega
  · have h1 : (k + 1) * W + W ≤ N * W := rowMajor_le (K := W) (show k + 1 < N by omega)
    have h2 : k * W + W ≤ N * W := rowMajor_le (K := W) (show k < N by omega)
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, cellP, dw, zW, soD, soDeclsW,
      LVec.replicate_l0, h1, h2]
    all_goals omega

/-- **The reference satisfies the sorter statement (txtask-v2) at latency `2N`** (`16` at the
scoring point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W⟩ := p
  obtain ⟨hN, hW, -⟩ := hp
  exact Tasks.Sorter.task.satisfiedAtV2_of_phases (so_interface N W hN hW) (so_disciplined N W hN hW)
    (so_terminatesPU N W hN hW) hN (show N ≤ 2 * N by omega) (fun xs h => (len_sort xs).trans h)
    (model N W hN hW) (so_powerUp N W hN hW) (so_moore N W hN hW) (so_xsafe N W hN hW)

end Submission
