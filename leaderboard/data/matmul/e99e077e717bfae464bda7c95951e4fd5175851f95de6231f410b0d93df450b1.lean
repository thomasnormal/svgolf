-- svgolf-latency: 3
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
# A cube of multipliers and a registered adder tree per entry, for task `matmul`

`solution.sv`: `N·N·N` product registers, one per `(i, j, k)`, written by the start edge with
`A[i][k]·B[k][j]` (both sign-extended, read from the held ports); per entry `(i, j)` one binary heap of
`2N - 1` nodes in `T` (leaves `N - 1 + k`, internal nodes `x < N - 1` with children `2x + 1`, `2x + 2`), every
internal node adding its children in every cycle; `C[i][j]` takes the root in every cycle; a step counter `t`
raises `done` on the edge that sees `t = clog2 N`. Proved at every in-range `(N, W, AccW)`, latency `clog2 N + 1`:
1. **Agreement** (`mm_sem_eq`): the loaded family is the hand-built `cbD` (three nested generate loops).
2. **The clock step** (`mm_profile`, `mm_cycle`, `mmNext_regs`): one cycle commits register by register.
3. **The tree** (`hv`, `hv_span`, `hv_root`): the heap value of the root is the dot product; a node is ready
   `t` levels after the start when `N ≤ (y + 1)·2^t` (`Good`, `T_step`, `T_start`), so every root is ready at
   `t = clog2 N` and `C` takes the product one cycle later (`C_root`).
4. **The protocol** (`model`), then txtask-v2's rules 1 to 3 and `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `clog2 N + 1` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := clog2 N + 1

/-! ## 1. Agreement -/

abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The bit offset of heap node `x` of entry `(i, j)` in `T` (heaps of `2N - 1` nodes of `AccW` bits). -/
def nd (N AccW i j x : Nat) : Nat := ((i * N + j) * (2 * N - 1) + x) * AccW

abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

def cbCtrl (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0)])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "t") (.binary .add (.ident "t") (c32 1)),
          .ifStmt (.binary .eq (.ident "t") (c32 (clog2 N)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- Internal node `x` of entry `(i, j)`: the sum of its children `2x+1`, `2x+2`, every cycle. -/
def cbNode (N AccW i j x : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "T" (nd N AccW i j x) AccW)
    (.binary .add (.slice (.ident "T") (nd N AccW i j (2 * x + 1)) AccW)
      (.slice (.ident "T") (nd N AccW i j (2 * x + 2)) AccW)))

/-- Leaf `N - 1 + k` of entry `(i, j)`: the product `A[i][k]·B[k][j]` on `start`. -/
def cbLeaf (N W AccW i j k : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "T" (nd N AccW i j (N - 1 + k)) AccW)
      (.resize AccW (.binary .mul (sext "A" AccW ((i * N + k) * W) W) (sext "B" AccW ((k * N + j) * W) W))))
    none)

/-- The output register of entry `(i, j)`: the root. -/
def cbOut (N AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.slice (.ident "T") (nd N AccW i j 0) AccW))

def cbDecls (wa wc wt : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "t", width := 32 },
   { name := "busy", width := 1 }, { name := "T", width := wt }]

/-- The processes of entry `(i, j)`, in source order. -/
def cbCell (N W AccW i j : Nat) : List Process2 :=
  (List.range (N - 1)).map (cbNode N AccW i j) ++ ((List.range N).map (cbLeaf N W AccW i j) ++ [cbOut N AccW i j])

def cbPEs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j => cbCell N W AccW i j

def cbD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (cbDecls (N * N * W) (N * N * AccW) (N * N * (2 * N - 1) * AccW)).toArray
  processes := (cbCtrl N :: cbPEs N W AccW).toArray

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("N", N), ("W", W), ("AccW", AccW)], pwidths := [("N", 32), ("W", 32), ("AccW", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "T"].map (·, 1)

theorem mm_decls (N W AccW : Int) :
    buildDecls (mmEnv N W AccW) design.pdesign.decls =
      .ok (cbDecls ((N * N * W - 1).natAbs + 1) ((N * N * AccW - 1).natAbs + 1)
        ((N * N * (2 * N - 1) * AccW - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, cbDecls, Gen2.except_ok_bind]

theorem mm_elems (N W AccW : Int) : buildElems (mmEnv N W AccW) design.pdesign.decls = .ok mmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, mmElems, Gen2.except_ok_bind]

abbrev mmE (N W AccW : Nat) : IEnv :=
  (mmEnv N W AccW).withDecls (cbDecls (N * N * W) (N * N * AccW) (N * N * (2 * N - 1) * AccW))

theorem mm_ctrl (N W AccW : Nat) :
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [cbCtrl N] := by
  sv2_inst_simp [instStmt2, instStmts2, design.pdesign, mmEnv, mmScope, cbDecls, mmElems, cbCtrl,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2]
  try and_intros
  all_goals first | rfl | decide

/-- The generate templates: node, leaf, output register (the processes inside `g_i`/`g_j`). -/
def nodeT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p], _, _]]] => p
  | _ => .alwaysFF "" (.block [])

def leafT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [_, .genFor _ _ _ _ _ _ [.process p], _]]] => p
  | _ => .alwaysFF "" (.block [])

def outT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [_, _, .process p]]] => p
  | _ => .alwaysFF "" (.block [])

macro "pe_simp" : tactic => `(tactic| sv2_inst_simp [nodeT, leafT, outT, evalSized, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, design.pdesign,
  mmEnv, mmScope, cbDecls, mmElems, cbNode, cbLeaf, cbOut, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, *])

/-- `Q = 2N - 1` nodes per heap, as an `Int`. -/
theorem q_cast {N : Nat} (hN : 1 ≤ N) : ((2 * N - 1 : Nat) : Int) = 2 * (N : Int) - 1 := by omega

theorem nd_cast {N AccW i j x : Nat} (hN : 1 ≤ N) :
    (nd N AccW i j x : Int) = (((i : Int) * N + j) * (2 * (N : Int) - 1) + x) * AccW := by
  simp only [nd, Int.natCast_mul, Int.natCast_add, q_cast hN]

/-- A node of `T` is an entry of the row-major `N·N × (2N-1)` array of `AccW`-bit entries. -/
theorem nd_le {N AccW i j x : Nat} (hi : i < N) (hj : j < N) (hx : x < 2 * N - 1) :
    nd N AccW i j x + AccW ≤ N * N * (2 * N - 1) * AccW := by
  have h1 : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  exact Lib.rowMajor_window_le (M := N * N) (N := 2 * N - 1) (w := AccW) h1 hx

/-- The `Int` facts the instantiated select of node `x` needs, for the label `X` it is written as. -/
theorem nd_win {N AccW i j x : Nat} (hN : 1 ≤ N) (hA : 1 ≤ AccW) (hi : i < N) (hj : j < N)
    (hx : x < 2 * N - 1) (X : Int) (hX : (((i : Int) * N + j) * (2 * (N : Int) - 1) + x) * AccW = X) :
    0 ≤ X ∧ X.toNat = nd N AccW i j x ∧ X + AccW - 1 < (N : Int) * N * (2 * N - 1) * AccW ∧ 1 ≤ X + AccW ∧
      (X + AccW).toNat = nd N AccW i j x + AccW := by
  refine Lib.window_bounds_of_natCast X _ (nd_le hi hj hx) hA (by rw [nd_cast hN, hX]) ?_
  rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, q_cast hN]

/-- The common facts of the instantiation lemmas. -/
theorem dims_facts {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (1 : Int) ≤ N * N * W ∧ (1 : Int) ≤ N * N * AccW ∧ (1 : Int) ≤ N * N * (2 * N - 1) * AccW ∧
    ((N : Int) * N * W - 1).natAbs + 1 = N * N * W ∧ ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW ∧
    ((N : Int) * N * (2 * N - 1) * AccW - 1).natAbs + 1 = N * N * (2 * N - 1) * AccW := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have pT := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * N - 1 by omega)) hA
  have eT : ((N : Int) * N * (2 * N - 1) * AccW) = ((N * N * (2 * N - 1) * AccW : Nat) : Int) := by
    rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_mul, q_cast hN]
  refine ⟨by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega, by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega,
    by rw [eT]; omega, ?_, ?_, ?_⟩
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pA
  · rw [eT]; exact Lib.natAbs_sub_one_add_one pT

theorem out_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N)
    (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems outT = cbOut N AccW i j := by
  obtain ⟨hNW, hNA, hNT, hcA, hcC, hcT⟩ := dims_facts hN hW hA
  have hq := q_cast hN
  have hC := Lib.window_bounds_of_natCast (((i : Int) * N + j) * AccW) (N * N * AccW)
    (Lib.rowMajor_window_le (w := AccW) hi hj) hA (by simp) (by simp)
  have hr := nd_win hN hA hi hj (x := 0) (by omega) (((i : Int) * N + j) * (2 * N - 1) * AccW) (by simp)
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  pe_simp
  repeat (unfold instExpr2; pe_simp)
  done

theorem node_inst (N W AccW i j x : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N)
    (hj : j < N) (hx : x + 1 < N) :
    instProcess2 ((((mmE N W AccW).bindVal "i" i).bindVal "j" j).bindVal "x" x) mmElems nodeT =
      cbNode N AccW i j x := by
  obtain ⟨hNW, hNA, hNT, hcA, hcC, hcT⟩ := dims_facts hN hW hA
  have hq := q_cast hN
  have h0 := nd_win hN hA hi hj (x := x) (by omega) _ rfl
  have h1 := nd_win hN hA hi hj (x := 2 * x + 1) (by omega)
    ((((i : Int) * N + j) * (2 * N - 1) + 2 * x + 1) * AccW) (by push_cast; congr 1; omega)
  have h2 := nd_win hN hA hi hj (x := 2 * x + 2) (by omega)
    ((((i : Int) * N + j) * (2 * N - 1) + 2 * x + 2) * AccW) (by push_cast; congr 1; omega)
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  pe_simp
  repeat (unfold instExpr2; pe_simp)
  done

theorem leaf_inst (N W AccW i j k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N)
    (hj : j < N) (hk : k < N) :
    instProcess2 ((((mmE N W AccW).bindVal "i" i).bindVal "j" j).bindVal "k" k) mmElems leafT =
      cbLeaf N W AccW i j k := by
  obtain ⟨hNW, hNA, hNT, hcA, hcC, hcT⟩ := dims_facts hN hW hA
  have hq := q_cast hN
  have hl := nd_win hN hA hi hj (x := N - 1 + k) (by omega)
    ((((i : Int) * N + j) * (2 * N - 1) + N - 1 + k) * AccW) (by rw [show ((N - 1 + k : Nat) : Int) = (N : Int) - 1 + k by omega]; congr 1; omega)
  have ha := Lib.window_bounds_of_natCast (((i : Int) * N + k) * W) (N * N * W)
    (Lib.rowMajor_window_le (w := W) hi hk) hW (by simp) (by simp)
  have hb := Lib.window_bounds_of_natCast (((k : Int) * N + j) * W) (N * N * W)
    (Lib.rowMajor_window_le (w := W) hk hj) hW (by simp) (by simp)
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  pe_simp
  repeat (unfold instExpr2; pe_simp)
  done

/-- `for (g = 0; g < bound; g++) body` (`rc`: the iteration count at the default point). -/
def genFor' (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

theorem mm_gens_src : design.pdesign.generates =
    [genFor' "g_i" "i" (.paramRef "N" none) 4 [genFor' "g_j" "j" (.paramRef "N" none) 4
      [genFor' "g_node" "x" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) 3 ([nodeT].map .process),
       genFor' "g_k" "k" (.paramRef "N" none) 4 ([leafT].map .process), .process outT]]] := rfl

/-- The expansion of the body of `g_j` at `(i, j) = (v, w)`. -/
def cellE (N W AccW : Nat) (v w : Int) : List Process2 :=
  (intRange 0 (N - 1)).flatMap (fun u =>
      [instProcess2 ((((mmE N W AccW).bindVal "i" v).bindVal "j" w).bindVal "x" u) mmElems nodeT]) ++
    ((intRange 0 N).flatMap (fun u =>
      [instProcess2 ((((mmE N W AccW).bindVal "i" v).bindVal "j" w).bindVal "k" u) mmElems leafT]) ++
    [instProcess2 (((mmE N W AccW).bindVal "i" v).bindVal "j" w) mmElems outT])

/-- **The three nested generate loops expand to the row-major cells.** -/
theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates = .ok (cbPEs N W AccW) := by
  have hv1 : ∀ v : Int, ((mmE N W AccW).bindVal "i" v).vals.lookup "N" = some (N : Int) := fun _ => rfl
  have hv2 : ∀ v w : Int, (((mmE N W AccW).bindVal "i" v).bindVal "j" w).vals.lookup "N" = some (N : Int) :=
    fun _ _ => rfl
  have hv3 : ∀ v w u : Int,
      ((((mmE N W AccW).bindVal "i" v).bindVal "j" w).bindVal "x" u).vals.lookup "N" = some (N : Int) :=
    fun _ _ _ => rfl
  have hv4 : ∀ v w u : Int,
      ((((mmE N W AccW).bindVal "i" v).bindVal "j" w).bindVal "k" u).vals.lookup "N" = some (N : Int) :=
    fun _ _ _ => rfl
  have ht : ((N : Int) - 1 - 0).toNat = N - 1 := by omega
  rw [mm_gens_src]
  apply expandList2_singleton_ok
  rw [genFor', GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w => cellE N W AccW v w)
      (evalInt_int 0) (fun i => isInt_paramRef_of (hv1 i)) (fun i => evalInt_paramRef_of (hv1 i))
      (by simpa using hF)]
  · simp only [intRange_zero, Int.sub_zero, Int.toNat_natCast, List.flatMap_map, cbPEs, cbCell]
    congr 1
    refine CombView.flatMap_congr' fun i hi => CombView.flatMap_congr' fun j hj => ?_
    have hi' := List.mem_range.mp hi
    have hj' := List.mem_range.mp hj
    simp only [cellE, intRange_zero, List.flatMap_map, Gen2.flatMap_singleton_map]
    refine congr (congrArg HAppend.hAppend ?_) (congr (congrArg HAppend.hAppend ?_) ?_)
    · exact List.map_congr_left fun x hx =>
        node_inst N W AccW i j x hN hW hA hi' hj' (by have := List.mem_range.mp hx; omega)
    · exact List.map_congr_left fun k hk => leaf_inst N W AccW i j k hN hW hA hi' hj' (List.mem_range.mp hk)
    · rw [out_inst N W AccW i j hN hW hA hi' hj']
  · intro v _ _
    apply expandList2_singleton_ok
    rw [genFor', GenItem.expand2_genFor_ascending_flatMap (N := (N : Int)) (f := cellE N W AccW v)
      (evalInt_int 0) (fun i => isInt_paramRef_of (hv2 v i)) (fun i => evalInt_paramRef_of (hv2 v i))
      (by simpa using hF)]
    · simp
    · intro w _ _
      refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_singleton_ok (GenItem.expand2_process _)))
      · rw [genFor', GenItem.expand2_genFor_ascending_processes (N := (N : Int) - 1) (evalInt_int 0)
          (fun i => isInt_binary_of rfl (isInt_paramRef_of (hv3 v w i)) rfl)
          (fun i => evalInt_sub_of (isInt_paramRef_of (hv3 v w i)) rfl (evalInt_paramRef_of (hv3 v w i)) rfl)
          (by omega)]
        simp
      · rw [genFor', GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
          (fun i => isInt_paramRef_of (hv4 v w i)) (fun i => evalInt_paramRef_of (hv4 v w i)) (by simpa using hF)]
        simp

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (cbDecls (N * N * W) (N * N * AccW) (N * N * (2 * N - 1) * AccW))
        mmElems (cbPEs N W AccW)) := by
  have hd := mm_decls N W AccW
  obtain ⟨-, -, -, hcA, hcC, hcT⟩ := dims_facts hN hW hA
  rw [hcA, hcC, hcT] at hd
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv _ _ _) hd (mm_elems _ _ _)
    (mm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      cbCtrl N :: cbPEs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_ctrl]
  simp [design.pdesign]

/-! ### The windows: every process writes one window, pairwise disjoint -/

theorem node_wins (N AccW i j x : Nat) :
    (cbNode N AccW i j x).procWins = [("T", some (nd N AccW i j x, AccW))] := by
  simp [cbNode, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]

theorem leaf_wins (N W AccW i j k : Nat) :
    (cbLeaf N W AccW i j k).procWins = [("T", some (nd N AccW i j (N - 1 + k), AccW))] := by
  simp [cbLeaf, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins]

theorem out_wins (N AccW i j : Nat) :
    (cbOut N AccW i j).procWins = [("C", some ((i * N + j) * AccW, AccW))] := by
  simp [cbOut, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]

/-- A process of cell `(i, j)` writes node `y < 2N - 1` of `T`, or entry `(i, j)` of `C`. -/
theorem cell_wins {N W AccW i j : Nat} {p : Process2} (hp : p ∈ cbCell N W AccW i j) :
    (∃ y, y < 2 * N - 1 ∧ p.procWins = [("T", some (nd N AccW i j y, AccW))]) ∨
      p.procWins = [("C", some ((i * N + j) * AccW, AccW))] := by
  simp only [cbCell, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨k, hk, rfl⟩ | rfl
  · exact .inl ⟨x, by omega, node_wins ..⟩
  · exact .inl ⟨N - 1 + k, by omega, leaf_wins ..⟩
  · exact .inr (out_wins ..)

/-- The relation of `Pairwise` in the profile: no window of `p` overlaps one of `q`. -/
abbrev Dj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

theorem dj_of {p q : Process2} {a b : DrvWin} (hp : p.procWins = [a]) (hq : q.procWins = [b])
    (h : a.overlaps b = false) : Dj p q := by
  intro a' ha b' hb; rw [hp] at ha; rw [hq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb; subst ha hb; exact h

theorem ov_lt {s : String} {lo lo' w : Nat} (h : lo + w ≤ lo') :
    DrvWin.overlaps (s, some (lo, w)) (s, some (lo', w)) = false := by
  simp [DrvWin.overlaps]; omega

theorem ov_ne {s s' : String} (h : s ≠ s') (a b : Option (Nat × Nat)) :
    DrvWin.overlaps (s, a) (s', b) = false := by
  simp [DrvWin.overlaps, h]

/-- Node offsets in row-major order: node `y` of block `b` before node `y'` of block `b' > b`. -/
theorem nd_lt_blk {N AccW i j i' j' y y' : Nat} (h : i * N + j < i' * N + j') (hy : y < 2 * N - 1) :
    nd N AccW i j y + AccW ≤ nd N AccW i' j' y' := by
  have h1 := rowMajor_le (K := 2 * N - 1) h
  have h2 : (i * N + j) * (2 * N - 1) + y < (i' * N + j') * (2 * N - 1) + y' := by omega
  exact rowMajor_le (K := AccW) h2

theorem nd_lt {N AccW i j y y' : Nat} (h : y < y') : nd N AccW i j y + AccW ≤ nd N AccW i j y' :=
  rowMajor_le (K := AccW) (show (i * N + j) * (2 * N - 1) + y < (i * N + j) * (2 * N - 1) + y' by omega)

/-- Two cells `(i, j)` before `(i', j')` in row-major order write disjoint windows. -/
theorem cell_cross {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ p ∈ cbCell N W AccW i j, ∀ q ∈ cbCell N W AccW i' j', Dj p q := by
  intro p hp q hq
  rcases cell_wins hp with ⟨y, hy, hpw⟩ | hpw <;> rcases cell_wins hq with ⟨y', hy', hqw⟩ | hqw
  · exact dj_of hpw hqw (ov_lt (nd_lt_blk h hy))
  · exact dj_of hpw hqw (ov_ne (by decide) _ _)
  · exact dj_of hpw hqw (ov_ne (by decide) _ _)
  · exact dj_of hpw hqw (ov_lt (rowMajor_le (K := AccW) h))

theorem cell_pairwise (N W AccW i j : Nat) : (cbCell N W AccW i j).Pairwise Dj := by
  unfold cbCell
  refine List.pairwise_append.mpr ⟨?_, List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩, ?_⟩
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h =>
      dj_of (node_wins ..) (node_wins ..) (ov_lt (nd_lt h)))
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h =>
      dj_of (leaf_wins ..) (leaf_wins ..) (ov_lt (nd_lt (by omega))))
  · intro a ha b hb
    simp only [List.mem_map, List.mem_range, List.mem_singleton] at ha hb
    obtain ⟨k, -, rfl⟩ := ha
    subst hb
    exact dj_of (leaf_wins ..) (out_wins ..) (ov_ne (by decide) _ _)
  · intro a ha b hb
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at ha hb
    obtain ⟨x, hx, rfl⟩ := ha
    rcases hb with ⟨k, -, rfl⟩ | rfl
    · exact dj_of (node_wins ..) (leaf_wins ..) (ov_lt (nd_lt (by omega)))
    · exact dj_of (node_wins ..) (out_wins ..) (ov_ne (by decide) _ _)

theorem pe_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ cbPEs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p ∈ cbCell N W AccW i j := by
  simp only [cbPEs, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, hp⟩ := hp
  exact ⟨i, j, hi, hj, hp⟩

theorem pe_cases {N W AccW : Nat} {p : Process2} (hp : p ∈ cbPEs N W AccW) :
    (∃ i j x, i < N ∧ j < N ∧ x + 1 < N ∧ p = cbNode N AccW i j x) ∨
      (∃ i j k, i < N ∧ j < N ∧ k < N ∧ p = cbLeaf N W AccW i j k) ∨ (∃ i j, i < N ∧ j < N ∧ p = cbOut N AccW i j) := by
  obtain ⟨i, j, hi, hj, hp⟩ := pe_mem hp
  simp only [cbCell, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨k, hk, rfl⟩ | rfl
  · exact .inl ⟨i, j, x, hi, hj, by omega, rfl⟩
  · exact .inr (.inl ⟨i, j, k, hi, hj, hk, rfl⟩)
  · exact .inr (.inr ⟨i, j, hi, hj, rfl⟩)

/-- The control and the cells drive pairwise disjoint windows. -/
theorem mm_pairwise (N W AccW : Nat) : (cbCtrl N :: cbPEs N W AccW).Pairwise Dj := by
  refine List.Pairwise.cons (fun p hp => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)
  · obtain ⟨i, j, -, -, hp⟩ := pe_mem hp
    rcases cell_wins hp with ⟨y, -, hw⟩ | hw <;>
    · intro a ha b hb
      rw [hw, List.mem_singleton] at hb
      subst hb
      revert ha; revert a
      simp [cbCtrl, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
        DrvWin.overlaps]
  · exact pairwise_flatMap_range (fun j _ => cell_pairwise N W AccW i j)
      (fun j j' hjj hj' => cell_cross (by omega))
  · intro i i' hii hi' a ha b hb
    simp only [List.mem_flatMap, List.mem_range] at ha hb
    obtain ⟨j, hj, ha⟩ := ha
    obtain ⟨j', -, hb⟩ := hb
    exact cell_cross (by have := rowMajor_le (K := N) hii; omega) a ha b hb

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (cbCtrl N :: cbPEs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    · rcases pe_cases hp with ⟨i, j, x, -, -, -, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
        exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, List.mem_cons]
    rintro n ⟨p, hp | hp, hn⟩
    · subst hp; revert n
      simp [cbCtrl, nb, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide
    · rcases pe_cases hp with ⟨i, j, x, -, -, -, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> revert n <;>
        simp [cbNode, cbLeaf, cbOut, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Lhs2.drvWins] <;> decide

/-- **The loaded family is `cbD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.sem N W AccW = cbD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA]; exact mm_driversOk N W AccW)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, mm_ctrl, cbD]
  simp [design.pdesign]

/-! ## 2. G0's clock step for the loaded family -/

theorem mm_profile (N W AccW : Nat) : (cbD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simp only [cbD, List.toList_toArray]; exact mm_pairwise N W AccW)⟩
  simp [cbD, cbCtrl, cbPEs, cbCell, cbNode, cbLeaf, cbOut, nb, List.all_flatMap, List.all_map, List.all_append,
    Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB,
    Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, cbDecls]

/-- The 10 signals of `cbD`, in declaration order. -/
def MS (ck r s a b dn c t bz tr : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("t", t),
    ("busy", bz), ("T", tr)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c t bz tr : LVec) :
    applyInputs2 (cbD N W AccW) e (MS ck r s a b dn c t bz tr) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c t bz tr := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [cbD, cbDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The control's updates, from the pre-edge values. -/
def ctrlQ (N : Nat) (r s dn t bz : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0)]
  else if bz.condTrue then
    if (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 (clog2 N)))).condTrue then
      [wr "t" t (t.add (LVec.ofInt 32 1)), wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
    else [wr "t" t (t.add (LVec.ofInt 32 1))]
  else []

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

def nodeQ (N AccW : Nat) (tr : LVec) (i j x : Nat) : NbaQueue2 :=
  [("T", nd N AccW i j x,
    ((tr.extract (nd N AccW i j (2 * x + 1)) AccW).add (tr.extract (nd N AccW i j (2 * x + 2)) AccW)).resizeU AccW)]

/-- The product of leaf `k`, evaluated. -/
def leafV (N W AccW : Nat) (a b : LVec) (i j k : Nat) : LVec :=
  ((sxv a AccW ((i * N + k) * W) W).mul (sxv b AccW ((k * N + j) * W) W)).resizeU AccW

def leafQ (N W AccW : Nat) (s a b : LVec) (i j k : Nat) : NbaQueue2 :=
  if s.condTrue then [("T", nd N AccW i j (N - 1 + k), (leafV N W AccW a b i j k).resizeU AccW)] else []

def outQ (N AccW : Nat) (tr : LVec) (i j : Nat) : NbaQueue2 :=
  [("C", (i * N + j) * AccW, (tr.extract (nd N AccW i j 0) AccW).resizeU AccW)]

def cellQ (N W AccW : Nat) (s a b tr : LVec) (i j : Nat) : NbaQueue2 :=
  (List.range (N - 1)).flatMap (nodeQ N AccW tr i j) ++
    ((List.range N).flatMap (leafQ N W AccW s a b i j) ++ outQ N AccW tr i j)

theorem ctrl_run (N F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t bz tr : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz tr) [] (cbCtrl N) =
      .ok (MS ck r s a b dn c t bz tr, ctrlQ N r s dn t bz) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 (clog2 N)))).condTrue = true <;>
    simp [cbCtrl, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem node_run (N AccW i j x F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t bz tr : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz tr) [] (cbNode N AccW i j x) =
      .ok (MS ck r s a b dn c t bz tr, nodeQ N AccW tr i j x) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [cbNode, nodeQ, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup, evalBinOp]

theorem leaf_run (N W AccW i j k F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t bz tr : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz tr) [] (cbLeaf N W AccW i j k) =
      .ok (MS ck r s a b dn c t bz tr, leafQ N W AccW s a b i j k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold leafQ
  by_cases h1 : s.condTrue = true <;>
    simp [cbLeaf, sext, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, leafV, sxv, h1]

theorem out_run (N AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t bz tr : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz tr) [] (cbOut N AccW i j) =
      .ok (MS ck r s a b dn c t bz tr, outQ N AccW tr i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [cbOut, outQ, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS, SvState.lookup]

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c t bz tr : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c t bz tr) (ctrlQ N r s dn t bz ++
    (List.range N).flatMap fun i => (List.range N).flatMap fun j => cellQ N W AccW s a b tr i j)

/-- **One cycle of the loaded design is G0's clock step**, evaluated. -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c t bz tr : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c t bz tr) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c t bz tr, kk + 3) := by
  have hedge : ∀ p ∈ (cbD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ cbCtrl N :: cbPEs N W AccW := by simpa [cbD] using hp
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · rcases pe_cases hm with ⟨i, j, x, -, -, -, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;> rfl
  rw [mm_sem_eq N W AccW hN hW hA, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [cbD, List.toList_toArray, List.flatMap_cons, ctrl_run N F hF, cbPEs, List.flatMap_assoc, cbCell,
      List.flatMap_append, List.flatMap_map, node_run _ _ _ _ _ F hF, leaf_run _ _ _ _ _ _ F hF, out_run _ _ _ _ F hF,
      List.flatMap_nil, List.append_nil, mmNext, cellQ]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ cbCtrl N :: cbPEs N W AccW :=
      List.mem_of_getElem? (by simpa [cbD] using hp : (cbCtrl N :: cbPEs N W AccW)[i]? = some p)
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ctrl_run N F hF _ _ _ _ _ _ _ _ _ _⟩
    · rcases pe_cases hm with ⟨i, j, x, -, -, -, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩
      · exact ⟨_, node_run N AccW i j x F hF _ _ _ _ _ _ _ _ _ _⟩
      · exact ⟨_, leaf_run N W AccW i j k F hF _ _ _ _ _ _ _ _ _ _⟩
      · exact ⟨_, out_run N AccW i j F hF _ _ _ _ _ _ _ _ _ _⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The arithmetic: the heap's values and the tree sum -/

/-- `A[i][k]·B[k][j]` (sign-extended entries), in the integers. -/
def prd (N W : Nat) {n : Nat} (A B : BitVec n) (i j k : Nat) : Int :=
  Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)

/-- The value of heap node `x` of entry `(i, j)`: a leaf `N - 1 + k` is its product, an internal node the
sum of its children `2x + 1`, `2x + 2`. -/
def hv (N W : Nat) {n : Nat} (A B : BitVec n) (i j x : Nat) : Int :=
  if N - 1 ≤ x then prd N W A B i j (x - (N - 1))
  else hv N W A B i j (2 * x + 1) + hv N W A B i j (2 * x + 2)
termination_by N - x

theorem hv_leaf {N W n : Nat} (A B : BitVec n) (i j : Nat) {x : Nat} (h : N - 1 ≤ x) :
    hv N W A B i j x = prd N W A B i j (x - (N - 1)) := by
  rw [hv, if_pos h]

theorem hv_node {N W n : Nat} (A B : BitVec n) (i j : Nat) {x : Nat} (h : x < N - 1) :
    hv N W A B i j x = hv N W A B i j (2 * x + 1) + hv N W A B i j (2 * x + 2) := by
  rw [hv, if_neg (by omega)]

/-- `Σ_{x ∈ [a, a + n)} f x`. -/
def isum (f : Nat → Int) (a : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => isum f a n + f (a + n)

theorem isum_add (f : Nat → Int) (a m : Nat) : ∀ n, isum f a (m + n) = isum f a m + isum f (a + m) n
  | 0 => by simp [isum]
  | n + 1 => by
    rw [← Nat.add_assoc, isum, isum, isum_add f a m n, Int.add_assoc, Nat.add_assoc]

theorem isum_congr {f g : Nat → Int} {a : Nat} : ∀ {n}, (∀ x, a ≤ x → x < a + n → f x = g x) →
    isum f a n = isum g a n
  | 0, _ => rfl
  | n + 1, h => by
    rw [isum, isum, isum_congr (fun x h1 h2 => h x h1 (by omega)), h (a + n) (by omega) (by omega)]

/-- Replacing every node of `[a, a + n)` by its two children: `[2a + 1, 2a + 1 + 2n)`. -/
theorem isum_children (f : Nat → Int) (a : Nat) : ∀ n,
    isum (fun x => f (2 * x + 1) + f (2 * x + 2)) a n = isum f (2 * a + 1) (2 * n)
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, isum, isum, isum, isum_children f a n,
      show 2 * (a + n) + 1 = 2 * a + 1 + 2 * n by omega, show 2 * (a + n) + 2 = 2 * a + 1 + (2 * n + 1) by omega,
      Int.add_assoc]

theorem isum_shift (f : Nat → Int) (a : Nat) : ∀ n, isum f a n = isum (fun k => f (a + k)) 0 n
  | 0 => rfl
  | n + 1 => by rw [isum, isum, isum_shift f a n, Nat.zero_add]

/-- **The nodes `[a, 2a + 1)` of the heap carry the sum of all leaves**, for `a ≤ N - 1`: replace the
internal ones by their children until only leaves are left. -/
theorem hv_span {N W n : Nat} (hN : 1 ≤ N) (A B : BitVec n) (i j : Nat) (a : Nat) (ha : a ≤ N - 1) :
    isum (hv N W A B i j) a (a + 1) = isum (hv N W A B i j) (N - 1) N := by
  by_cases h : N - 1 ≤ 2 * a + 1
  · have e1 : a + 1 = (N - 1 - a) + (2 * a + 2 - N) := by omega
    have e2 : a + (N - 1 - a) = N - 1 := by omega
    have e3 : N - 1 + (2 * a + 2 - N) = 2 * a + 1 := by omega
    have e4 : 2 * a + 2 - N + 2 * (N - 1 - a) = N := by omega
    rw [e1, isum_add, e2,
      isum_congr (g := fun x => hv N W A B i j (2 * x + 1) + hv N W A B i j (2 * x + 2))
        (fun x _ h2 => hv_node A B i j (by omega)),
      isum_children, Int.add_comm, ← e3, ← isum_add, e4]
  · have e5 : 2 * (a + 1) = 2 * a + 1 + 1 := by omega
    rw [isum_congr (g := fun x => hv N W A B i j (2 * x + 1) + hv N W A B i j (2 * x + 2))
        (fun x _ h2 => hv_node A B i j (by omega)),
      isum_children, e5]
    exact hv_span hN A B i j (2 * a + 1) (by omega)
termination_by N - 1 - a

theorem foldl_add_range (g : Nat → Int) : ∀ n, (List.range n).foldl (fun acc k => acc + g k) 0 = isum g 0 n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_add_range g n, isum, Nat.zero_add]; rfl

/-- **The root is the dot product.** -/
theorem hv_root {N W n : Nat} (hN : 1 ≤ N) (A B : BitVec n) (i j : Nat) :
    hv N W A B i j 0 = Tasks.Matmul.dot N W A B i j := by
  have h := hv_span (W := W) hN A B i j 0 (Nat.zero_le _)
  simp only [isum, Nat.zero_add, Int.zero_add] at h
  rw [h, isum_shift, Tasks.Matmul.dot, foldl_add_range]
  exact isum_congr fun k _ hk => by rw [hv_leaf A B i j (by omega), show N - 1 + k - (N - 1) = k by omega]; rfl

/-! ## 4. The commit, register by register -/

section commit
variable {ck r s a b dn c t bz tr : LVec} {lo : Nat} {v : LVec}
theorem nb_done : nbaStep (MS ck r s a b dn c t bz tr) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c t bz tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_C : nbaStep (MS ck r s a b dn c t bz tr) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) t bz tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_t : nbaStep (MS ck r s a b dn c t bz tr) ("t", lo, v) =
    MS ck r s a b dn c (t.insertAt lo v) bz tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_busy : nbaStep (MS ck r s a b dn c t bz tr) ("busy", lo, v) =
    MS ck r s a b dn c t (bz.insertAt lo v) tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_T : nbaStep (MS ck r s a b dn c t bz tr) ("T", lo, v) =
    MS ck r s a b dn c t bz (tr.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- Committing a queue of writes to the five registers. -/
theorem commit_MS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c t bz tr : LVec),
    (∀ u ∈ q, u.1 = "done" ∨ u.1 = "C" ∨ u.1 = "t" ∨ u.1 = "busy" ∨ u.1 = "T") →
    commitNba2 (MS ck r s a b dn c t bz tr) q =
      MS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "t" q t) (nbaFold "busy" q bz)
        (nbaFold "T" q tr)
  | [], _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, t, bz, tr, h => by
    have hq := @commit_MS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;>
      simp [commitNba2_cons, nb_done, nb_C, nb_t, nb_busy, nb_T, hq _ _ _ _ _ h', nbaFold]

theorem nbaFold_skip {n : String} : ∀ {q : NbaQueue2} (x : LVec), (∀ u ∈ q, u.1 ≠ n) → nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, x, h => by
    have h1 := h u List.mem_cons_self
    have ih := nbaFold_skip (q := q) x (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [nbaFold, List.foldl_cons, h1, if_false] at ih ⊢
    exact ih

theorem nbaFold_single (n : String) (lo : Nat) (v x : LVec) : nbaFold n [(n, lo, v)] x = x.insertAt lo v := by
  simp [nbaFold]

theorem nbaFold_flatMap_congr {α : Type} {n : String} {f g : α → NbaQueue2} :
    ∀ {l : List α}, (∀ k ∈ l, ∀ x, nbaFold n (f k) x = nbaFold n (g k) x) →
      ∀ x, nbaFold n (l.flatMap f) x = nbaFold n (l.flatMap g) x
  | [], _, _ => rfl
  | k :: l, h, x => by
    rw [List.flatMap_cons, List.flatMap_cons, nbaFold_append, nbaFold_append, h k List.mem_cons_self,
      nbaFold_flatMap_congr (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]

/-- The cells' queues of one cycle. -/
def cellsQ (N W AccW : Nat) (s a b tr : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j => cellQ N W AccW s a b tr i j

theorem mmNext_eq (N W AccW : Nat) (ck r s a b dn c t bz tr : LVec) :
    mmNext N W AccW ck r s a b dn c t bz tr =
      commitNba2 (MS ck r s a b dn c t bz tr) (ctrlQ N r s dn t bz ++ cellsQ N W AccW s a b tr) := rfl

theorem ctrlQ_names (N : Nat) (r s dn t bz : LVec) :
    ∀ u ∈ ctrlQ N r s dn t bz, u.1 = "busy" ∨ u.1 = "done" ∨ u.1 = "t" := by
  unfold ctrlQ; (repeat' split) <;> simp

theorem cellQ_names (N W AccW : Nat) (s a b tr : LVec) (i j : Nat) :
    ∀ u ∈ cellQ N W AccW s a b tr i j, u.1 = "T" ∨ u.1 = "C" := by
  intro u hu
  simp only [cellQ, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with ⟨x, -, hu⟩ | ⟨k, -, hu⟩ | hu
  · simp [nodeQ] at hu; subst hu; simp
  · unfold leafQ at hu; split at hu
    · simp at hu; subst hu; simp
    · simp at hu
  · simp [outQ] at hu; subst hu; simp

theorem cellsQ_names (N W AccW : Nat) (s a b tr : LVec) :
    ∀ u ∈ cellsQ N W AccW s a b tr, u.1 = "T" ∨ u.1 = "C" := by
  intro u hu
  simp only [cellsQ, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  exact cellQ_names N W AccW s a b tr i j u hu

theorem all_names (N W AccW : Nat) (r s a b dn t bz tr : LVec) :
    ∀ u ∈ ctrlQ N r s dn t bz ++ cellsQ N W AccW s a b tr,
      u.1 = "done" ∨ u.1 = "C" ∨ u.1 = "t" ∨ u.1 = "busy" ∨ u.1 = "T" := by
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · rcases ctrlQ_names N r s dn t bz u hu with h | h | h <;> simp [h]
  · rcases cellsQ_names N W AccW s a b tr u hu with h | h <;> simp [h]

/-- **One cycle, register by register.** -/
theorem mmNext_regs (N W AccW : Nat) (ck r s a b dn c t bz tr : LVec) :
    mmNext N W AccW ck r s a b dn c t bz tr =
      MS ck r s a b (nbaFold "done" (ctrlQ N r s dn t bz) dn) (nbaFold "C" (cellsQ N W AccW s a b tr) c)
        (nbaFold "t" (ctrlQ N r s dn t bz) t) (nbaFold "busy" (ctrlQ N r s dn t bz) bz)
        (nbaFold "T" (cellsQ N W AccW s a b tr) tr) := by
  have hc : ∀ n, n ≠ "T" → n ≠ "C" → ∀ x, nbaFold n (cellsQ N W AccW s a b tr) x = x := fun n h1 h2 x =>
    nbaFold_skip x fun u hu => by rcases cellsQ_names N W AccW s a b tr u hu with h | h <;> rw [h] <;> grind
  have hq : ∀ n, n ≠ "busy" → n ≠ "done" → n ≠ "t" → ∀ x, nbaFold n (ctrlQ N r s dn t bz) x = x :=
    fun n h1 h2 h3 x => nbaFold_skip x fun u hu => by
      rcases ctrlQ_names N r s dn t bz u hu with h | h | h <;> rw [h] <;> grind
  rw [mmNext_eq, commit_MS _ _ _ _ _ _ (all_names N W AccW r s a b dn t bz tr), nbaFold_append, nbaFold_append,
    nbaFold_append, nbaFold_append, nbaFold_append, hc "done" (by decide) (by decide),
    hc "t" (by decide) (by decide), hc "busy" (by decide) (by decide),
    hq "C" (by decide) (by decide) (by decide), hq "T" (by decide) (by decide) (by decide)]

/-! ### The windows of `T` and of `C` after a cycle -/

/-- At most one write, of an `AccW`-bit value into window `r` of `T`. -/
def OneW (AccW : Nat) (q : NbaQueue2) (r : Nat) : Prop :=
  q = [] ∨ ∃ v, v.width = AccW ∧ q = [("T", r * AccW, v)]

/-- What a window holds after the queue `q` of at most one write: the written value, or `old`. -/
def rdW (q : NbaQueue2) (old : LVec) : LVec :=
  match q with
  | [(_, _, v)] => v
  | _ => old

/-- **A family of single-window writes**, window `r` written (or not) by `h r`, read window by window. -/
theorem fold_windows {AccW : Nat} (h : Nat → NbaQueue2) (hh : ∀ r, OneW AccW (h r) r) (x : LVec) :
    ∀ n m, (m + 1) * AccW ≤ x.width →
      (nbaFold "T" ((List.range n).flatMap h) x).extract (m * AccW) AccW =
        if m < n then rdW (h m) (x.extract (m * AccW) AccW) else x.extract (m * AccW) AccW
  | 0, m, _ => by simp [nbaFold]
  | n + 1, m, hm => by
    have ih := fold_windows h hh x n m hm
    have hw : (nbaFold "T" ((List.range n).flatMap h) x).width = x.width := width_nbaFold _ _ _
    rw [List.range_succ, List.flatMap_append, nbaFold_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rcases hh n with h0 | ⟨v, hv, h1⟩
    · rw [h0, show ∀ y, nbaFold "T" [] y = y from fun _ => rfl, ih]
      by_cases hmn : m < n
      · rw [if_pos hmn, if_pos (by omega)]
      · by_cases hmn' : m = n
        · subst hmn'; rw [if_neg hmn, if_pos (by omega), h0]; rfl
        · rw [if_neg hmn, if_neg (by omega)]
    · rw [h1, nbaFold_single]
      by_cases hmn : m = n
      · subst hmn
        rw [LVec.extract_insertAt_self hv (by rw [hw]; rw [Nat.succ_mul] at hm; exact hm), if_pos (by omega), h1]
        rfl
      · have hd : m * AccW + AccW ≤ n * AccW ∨ n * AccW + v.width ≤ m * AccW := by
          rw [hv]
          rcases Nat.lt_or_gt_of_ne hmn with h' | h'
          · exact .inl (rowMajor_le h')
          · exact .inr (rowMajor_le h')
        rw [LVec.extract_insertAt_of_disjoint hd, ih]
        by_cases hmn' : m < n
        · rw [if_pos hmn', if_pos (by omega)]
        · rw [if_neg hmn', if_neg (by omega)]

/-- Reindexing a block-major double loop into one loop. -/
theorem flatMap_range_mul {α : Type} (K : Nat) (h : Nat → List α) : ∀ M,
    (List.range M).flatMap (fun b => (List.range K).flatMap (fun y => h (b * K + y))) =
      (List.range (M * K)).flatMap h
  | 0 => by simp
  | M + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul K h M, Nat.succ_mul, List.range_add,
      List.flatMap_append, List.flatMap_map]
    simp

theorem rowMajor_dec {N i j : Nat} (hj : j < N) : (i * N + j) / N = i ∧ (i * N + j) % N = j := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- Node `y` of entry `(i, j)` is entry `(i·N + j)·(2N - 1) + y` of `T`. -/
theorem nd_dec (N AccW r : Nat) :
    nd N AccW (r / (2 * N - 1) / N) (r / (2 * N - 1) % N) (r % (2 * N - 1)) = r * AccW := by
  unfold nd
  have h1 := Nat.div_add_mod (r / (2 * N - 1)) N
  have h2 := Nat.div_add_mod r (2 * N - 1)
  rw [Nat.mul_comm (r / (2 * N - 1) / N) N, h1, Nat.mul_comm (r / (2 * N - 1)) (2 * N - 1), h2]

/-- The queue of node `y` of entry `(i, j)`: a tree node's, or a leaf's. -/
def tq (N W AccW : Nat) (s a b tr : LVec) (i j y : Nat) : NbaQueue2 :=
  if y < N - 1 then nodeQ N AccW tr i j y else leafQ N W AccW s a b i j (y - (N - 1))

/-- `tq` at the global index `r`. -/
def tqr (N W AccW : Nat) (s a b tr : LVec) (r : Nat) : NbaQueue2 :=
  tq N W AccW s a b tr (r / (2 * N - 1) / N) (r / (2 * N - 1) % N) (r % (2 * N - 1))

theorem tqr_oneW (N W AccW : Nat) (s a b tr : LVec) (r : Nat) : OneW AccW (tqr N W AccW s a b tr r) r := by
  unfold tqr tq
  split
  · refine .inr ⟨_, ?_, by rw [nodeQ, nd_dec]⟩
    simp
  · unfold leafQ; split
    · refine .inr ⟨_, ?_, by rw [show N - 1 + (r % (2 * N - 1) - (N - 1)) = r % (2 * N - 1) by omega, nd_dec]⟩
      simp
    · exact .inl rfl

theorem cell_T (N W AccW : Nat) (hN : 1 ≤ N) (s a b tr : LVec) (i j : Nat) (hi : i < N) (hj : j < N) (x : LVec) :
    nbaFold "T" (cellQ N W AccW s a b tr i j) x =
      nbaFold "T" ((List.range (2 * N - 1)).flatMap fun y =>
        tqr N W AccW s a b tr ((i * N + j) * (2 * N - 1) + y)) x := by
  have hq : 0 < 2 * N - 1 := by omega
  have hdec : ∀ y, y < 2 * N - 1 → tqr N W AccW s a b tr ((i * N + j) * (2 * N - 1) + y) = tq N W AccW s a b tr i j y := by
    intro y hy
    have e1 : ((i * N + j) * (2 * N - 1) + y) / (2 * N - 1) = i * N + j := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hy, Nat.zero_add]
    have e2 : ((i * N + j) * (2 * N - 1) + y) % (2 * N - 1) = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
    rw [tqr, e1, e2, (rowMajor_dec hj).1, (rowMajor_dec hj).2]
  have h1 : ((List.range (2 * N - 1)).flatMap fun y => tqr N W AccW s a b tr ((i * N + j) * (2 * N - 1) + y)) =
      (List.range (2 * N - 1)).flatMap (tq N W AccW s a b tr i j) :=
    CombView.flatMap_congr' fun y hy => hdec y (List.mem_range.mp hy)
  have h2 : (List.range (N - 1)).flatMap (tq N W AccW s a b tr i j) = (List.range (N - 1)).flatMap (nodeQ N AccW tr i j) :=
    CombView.flatMap_congr' fun y hy => by rw [tq, if_pos (List.mem_range.mp hy)]
  have h3 : ((List.range N).flatMap fun k => tq N W AccW s a b tr i j (N - 1 + k)) =
      (List.range N).flatMap (leafQ N W AccW s a b i j) :=
    CombView.flatMap_congr' fun k _ => by
      show tq N W AccW s a b tr i j (N - 1 + k) = _
      rw [tq, if_neg (by omega), show N - 1 + k - (N - 1) = k by omega]
  rw [h1, show 2 * N - 1 = (N - 1) + N by omega, List.range_add, List.flatMap_append, List.flatMap_map, cellQ,
    nbaFold_append, nbaFold_append, nbaFold_append,
    nbaFold_skip (n := "T") _ (by intro u hu; simp [outQ] at hu; subst hu; simp)]
  rw [h2, h3]

/-- **Window `(i, j, y)` of `T` after a cycle**: written by its tree node or leaf, or held. -/
theorem T_window {N W AccW : Nat} (hN : 1 ≤ N) (s a b tr : LVec)
    (htr : tr.width = N * N * (2 * N - 1) * AccW) {i j y : Nat} (hi : i < N) (hj : j < N)
    (hy : y < 2 * N - 1) :
    (nbaFold "T" (cellsQ N W AccW s a b tr) tr).extract (nd N AccW i j y) AccW =
      rdW (tq N W AccW s a b tr i j y) (tr.extract (nd N AccW i j y) AccW) := by
  have hre : nbaFold "T" (cellsQ N W AccW s a b tr) tr =
      nbaFold "T" ((List.range (N * N * (2 * N - 1))).flatMap (tqr N W AccW s a b tr)) tr := by
    rw [cellsQ, nbaFold_flatMap_congr (g := fun i => (List.range N).flatMap fun j => (List.range (2 * N - 1)).flatMap
        fun y => tqr N W AccW s a b tr ((i * N + j) * (2 * N - 1) + y))
      (fun i hi x => nbaFold_flatMap_congr (fun j hj x => cell_T N W AccW hN s a b tr i j
        (List.mem_range.mp hi) (List.mem_range.mp hj) x) x) tr]
    rw [flatMap_range_mul N (fun q => (List.range (2 * N - 1)).flatMap fun y => tqr N W AccW s a b tr (q * (2 * N - 1) + y)),
      flatMap_range_mul]
  have hlt : (i * N + j) * (2 * N - 1) + y < N * N * (2 * N - 1) := by
    have h1 : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
    have := rowMajor_le (K := 2 * N - 1) h1; omega
  have hm : ((i * N + j) * (2 * N - 1) + y + 1) * AccW ≤ tr.width := by
    rw [htr]; exact Nat.mul_le_mul_right _ hlt
  rw [hre, show nd N AccW i j y = ((i * N + j) * (2 * N - 1) + y) * AccW from rfl,
    fold_windows _ (tqr_oneW N W AccW s a b tr) tr _ _ hm, if_pos hlt]
  have hq : 0 < 2 * N - 1 := by omega
  have e1 : ((i * N + j) * (2 * N - 1) + y) / (2 * N - 1) = i * N + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt hy, Nat.zero_add]
  have e2 : ((i * N + j) * (2 * N - 1) + y) % (2 * N - 1) = y := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  rw [tqr, e1, e2, (rowMajor_dec hj).1, (rowMajor_dec hj).2]

/-- **`C` after a cycle**: every entry takes its root. -/
theorem C_fold (N W AccW : Nat) (s a b tr c : LVec) :
    nbaFold "C" (cellsQ N W AccW s a b tr) c =
      LVec.insertEntries AccW (fun r => (tr.extract (nd N AccW (r / N) (r % N) 0) AccW).resizeU AccW) (N * N) c := by
  have hcell : ∀ i j, j < N → ∀ x, nbaFold "C" (cellQ N W AccW s a b tr i j) x =
      nbaFold "C" ((List.range 1).flatMap fun _ =>
        [("C", (i * N + j) * AccW, (tr.extract (nd N AccW ((i * N + j) / N) ((i * N + j) % N) 0) AccW).resizeU AccW)]) x := by
    intro i j hj x
    rw [cellQ, nbaFold_append, nbaFold_append, nbaFold_skip (n := "C") x (by
        intro u hu; simp only [List.mem_flatMap, List.mem_range, nodeQ, List.mem_singleton] at hu
        obtain ⟨_, _, rfl⟩ := hu; simp),
      nbaFold_skip (n := "C") x (by
        intro u hu; simp only [List.mem_flatMap, List.mem_range] at hu
        obtain ⟨k, _, hu⟩ := hu; unfold leafQ at hu; split at hu
        · simp at hu; subst hu; simp
        · simp at hu),
      (rowMajor_dec hj).1, (rowMajor_dec hj).2]
    simp [outQ]
  rw [cellsQ, nbaFold_flatMap_congr (g := fun i => (List.range N).flatMap fun j => (List.range 1).flatMap fun _ =>
      [("C", (i * N + j) * AccW, (tr.extract (nd N AccW ((i * N + j) / N) ((i * N + j) % N) 0) AccW).resizeU AccW)])
    (fun i _ x => nbaFold_flatMap_congr (fun j hj x => hcell i j (List.mem_range.mp hj) x) x) c]
  rw [show ((List.range N).flatMap fun i => (List.range N).flatMap fun j => (List.range 1).flatMap fun _ =>
      [("C", (i * N + j) * AccW, (tr.extract (nd N AccW ((i * N + j) / N) ((i * N + j) % N) 0) AccW).resizeU AccW)]) =
      (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
        [("C", (i * N + j) * AccW, (tr.extract (nd N AccW ((i * N + j) / N) ((i * N + j) % N) 0) AccW).resizeU AccW)] by
      simp]
  rw [flatMap_range_mul N (fun b => [("C", b * AccW, (tr.extract (nd N AccW (b / N) (b % N) 0) AccW).resizeU AccW)]) N,
    nbaFold_flatMap]
  simp only [nbaFold_single]
  rfl

/-! ## 5. The registers through a cycle: the invariant -/

attribute [local simp] condTrue_knownBit

theorem setWidth_mul_signExtend {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  rw [BitVec.setWidth_mul _ _ h, Lib.setWidth_signExtend_of_le _ h, Lib.setWidth_signExtend_of_le _ h,
    BitVec.ofInt_mul]; rfl

/-- **A leaf's product**, evaluated on known operands. -/
theorem leaf_val {N W AccW : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {i j k : Nat} (hi : i < N)
    (hj : j < N) (hk : k < N) :
    (leafV N W AccW (.ofBitVec A) (.ofBitVec B) i j k).resizeU AccW =
      .ofBitVec (BitVec.ofInt AccW (prd N W A B i j k)) := by
  have ha : (i * N + k) * W + W ≤ N * N * W := Lib.rowMajor_window_le hi hk
  have hb : (k * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le hk hj
  simp (disch := omega) only [leafV, sxv, LVec.extract_ofBitVec, LVec.concatMany_singleton,
    LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec,
    LVec.ofBitVec_replicate_append_eq_signExtend hW, LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    setWidth_mul_signExtend, prd, Tasks.Matmul.entry]

/-- Node `y` of entry `(i, j)` of `tr` holds its heap value. -/
abbrev NodeOK (N W AccW : Nat) (A B : BitVec (N * N * W)) (tr : LVec) (i j y : Nat) : Prop :=
  tr.extract (nd N AccW i j y) AccW = .ofBitVec (BitVec.ofInt AccW (hv N W A B i j y))

/-- **The tree after `t` levels**: every node `y` with `N ≤ (y + 1)·2^t` holds its value (the leaves at every
`t`, the root from `t = clog2 N` on). -/
def Good (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (tr : LVec) : Prop :=
  tr.width = N * N * (2 * N - 1) * AccW ∧
    ∀ i j y, i < N → j < N → y < 2 * N - 1 → N ≤ (y + 1) * 2 ^ t → NodeOK N W AccW A B tr i j y

theorem good_down {N W AccW : Nat} {A B : BitVec (N * N * W)} {t : Nat} {tr : LVec}
    (h : Good N W AccW A B (t + 1) tr) : Good N W AccW A B t tr :=
  ⟨h.1, fun i j y hi hj hy hle => h.2 i j y hi hj hy
    (Nat.le_trans hle (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))⟩

theorem pow_split (y t : Nat) : (y + 1) * 2 ^ (t + 1) = (2 * y + 1 + 1) * 2 ^ t := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ t) 2, ← Nat.mul_assoc]; congr 1; omega

/-- **One level of the tree in a cycle without `start`**: the leaves hold, every node whose children were
ready adds them. -/
theorem T_step {N W AccW : Nat} (hN : 1 ≤ N) (A B : BitVec (N * N * W)) (a b : LVec) {t : Nat} {tr : LVec}
    (h : Good N W AccW A B t tr) :
    Good N W AccW A B (t + 1) (nbaFold "T" (cellsQ N W AccW (knownBit false) a b tr) tr) := by
  refine ⟨by rw [width_nbaFold]; exact h.1, fun i j y hi hj hy hle => ?_⟩
  show LVec.extract _ _ _ = _
  rw [T_window hN _ _ _ tr h.1 hi hj hy]
  by_cases hyn : y < N - 1
  · rw [tq, if_pos hyn, nodeQ]
    simp only [rdW]
    rw [pow_split] at hle
    have hc1 := h.2 i j (2 * y + 1) hi hj (by omega) hle
    have hc2 := h.2 i j (2 * y + 2) hi hj (by omega)
      (Nat.le_trans hle (Nat.mul_le_mul_right _ (by omega)))
    rw [hc1, hc2, hv_node A B i j hyn]
    simp [LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.ofInt_add]
  · rw [tq, if_neg hyn, leafQ, if_neg (by simp)]
    simp only [rdW]
    exact h.2 i j y hi hj hy (Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t)))

/-- **The start edge** loads every leaf with its product: the tree at level `0`. -/
theorem T_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {tr : LVec}
    (htr : tr.width = N * N * (2 * N - 1) * AccW) :
    Good N W AccW A B 0 (nbaFold "T" (cellsQ N W AccW (knownBit true) (.ofBitVec A) (.ofBitVec B) tr) tr) := by
  refine ⟨by rw [width_nbaFold]; exact htr, fun i j y hi hj hy hle => ?_⟩
  show LVec.extract _ _ _ = _
  rw [T_window hN _ _ _ tr htr hi hj hy]
  simp only [Nat.pow_zero, Nat.mul_one] at hle
  rw [tq, if_neg (by omega), leafQ, if_pos (by simp)]
  simp only [rdW]
  rw [leaf_val hW A B hi hj (by omega), hv_leaf A B i j (by omega)]

theorem insertEntries_congr {W : Nat} {g g' : Nat → LVec} (c : LVec) :
    ∀ {n}, (∀ r, r < n → g r = g' r) → LVec.insertEntries W g n c = LVec.insertEntries W g' n c
  | 0, _ => rfl
  | n + 1, h => by
    rw [LVec.insertEntries_succ, LVec.insertEntries_succ, insertEntries_congr c (fun r hr => h r (by omega)),
      h n (by omega)]

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- **`C` takes the roots**: once every root is ready, `C` is the product after the cycle. -/
theorem C_root {N W AccW : Nat} (hN : 1 ≤ N) (A B : BitVec (N * N * W)) (s a b : LVec) {t : Nat} {tr c : LVec}
    (h : Good N W AccW A B t tr) (ht : N ≤ 2 ^ t) (hc : c.width = N * N * AccW) :
    nbaFold "C" (cellsQ N W AccW s a b tr) c = .ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [C_fold, insertEntries_congr (g' := fun r => .ofBitVec (BitVec.ofInt AccW (Tasks.Matmul.dot N W A B (r / N) (r % N))))
    c (fun r hr => ?_), LVec.insertEntries_ofBitVec _ _ hc, product_eq]
  have hrN : r / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have hrm : r % N < N := Nat.mod_lt _ (by omega)
  have hroot := h.2 (r / N) (r % N) 0 hrN hrm (by omega) (by simpa using ht)
  show (LVec.extract _ _ _).resizeU AccW = _
  rw [hroot, hv_root hN]
  simp [LVec.resizeU_ofBitVec]

/-! ### The control -/

theorem clog2_le_self (n : Nat) : clog2 n ≤ n := by
  unfold clog2; split
  · omega
  · have := Nat.log2_le_self (n - 1); omega

theorem le_pow_clog2 (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  by_cases h : n ≤ 1
  · rw [if_pos h, Nat.pow_zero]; omega
  · rw [if_neg h]; have := Nat.lt_log2_self (n := n - 1); omega

theorem ofNat32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    BitVec.ofNat 32 a = BitVec.ofNat 32 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · rintro rfl; rfl

/-- The control in a busy cycle: `t` counts, and the cycle that sees `t = clog2 N` ends the transaction. -/
theorem ctrl_busy {N t : Nat} (ht : t < 2 ^ 32) (hL : clog2 N < 2 ^ 32) :
    nbaFold "done" (ctrlQ N (knownBit false) (knownBit false) (knownBit false) (.ofBitVec (BitVec.ofNat 32 t))
        (knownBit true)) (knownBit false) = knownBit (decide (t = clog2 N)) ∧
    nbaFold "busy" (ctrlQ N (knownBit false) (knownBit false) (knownBit false) (.ofBitVec (BitVec.ofNat 32 t))
        (knownBit true)) (knownBit true) = knownBit (decide (t ≠ clog2 N)) ∧
    nbaFold "t" (ctrlQ N (knownBit false) (knownBit false) (knownBit false) (.ofBitVec (BitVec.ofNat 32 t))
        (knownBit true)) (.ofBitVec (BitVec.ofNat 32 t)) = .ofBitVec (BitVec.ofNat 32 (t + 1)) := by
  simp only [ctrlQ, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
    BitVec.ofInt_natCast, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq,
    ofNat32_inj ht hL, LVec.add_ofBitVec, LVec.width_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  by_cases hf : t = clog2 N <;>
    simp [hf, nbaFold, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
      BitVec.ofNat_add_ofNat]

theorem ctrl_start (N : Nat) (dn t bz : LVec) (h1 : dn.width = 1) (h3 : t.width = 32) (h4 : bz.width = 1) :
    nbaFold "done" (ctrlQ N (knownBit false) (knownBit true) dn t bz) dn = knownBit false ∧
    nbaFold "busy" (ctrlQ N (knownBit false) (knownBit true) dn t bz) bz = knownBit true ∧
    nbaFold "t" (ctrlQ N (knownBit false) (knownBit true) dn t bz) t = .ofBitVec (BitVec.ofNat 32 0) := by
  simp [ctrlQ, wr, nbaFold, h1, h3, h4, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
    LVec.replicate_l0, LVec.resizeU_ofBitVec]

theorem ctrl_idle (N : Nat) (dn t : LVec) (n : String) (x : LVec) :
    nbaFold n (ctrlQ N (knownBit false) (knownBit false) dn t (knownBit false)) x = x := by
  simp [ctrlQ, nbaFold]

theorem ctrl_reset (N : Nat) (s dn t bz : LVec) (h1 : dn.width = 1) (h4 : bz.width = 1) :
    nbaFold "done" (ctrlQ N (knownBit true) s dn t bz) dn = knownBit false ∧
    nbaFold "busy" (ctrlQ N (knownBit true) s dn t bz) bz = knownBit false := by
  simp [ctrlQ, wr, nbaFold, h1, h4, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0]

/-! ## 6. Shape and termination -/

def Wd (N AccW : Nat) (dn c t bz tr : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ t.width = 32 ∧ bz.width = 1 ∧ tr.width = N * N * (2 * N - 1) * AccW

def I (N AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz tr, st = MS ck r s a b dn c t bz tr ∧ Wd N AccW dn c t bz tr

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c t bz tr : LVec) (hw : Wd N AccW dn c t bz tr) :
    I N AccW (mmNext N W AccW ck r s a b dn c t bz tr) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  rw [mmNext_regs]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, h1, h2, h3, h4, h5]⟩

theorem mm_noq (N W AccW : Nat) : (cbD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [cbD, cbCtrl, cbPEs, cbCell, cbNode, cbLeaf, cbOut, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
    Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec (N * N * (2 * N - 1) * AccW), ?_, by simp [Wd]⟩
  simp [initState2, cbD, cbDecls, MS]

theorem mm_terminates (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Terminates2 (design.sem N W AccW) := by
  refine Terminates2.of_invariant (I N AccW) (mm_init N W AccW hN hW hA) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t bz tr kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c t bz tr hw⟩

/-! ## 7. The protocol: the phases, and the statement -/

theorem MS_inj {ck r s a b dn c t bz tr ck' r' s' a' b' dn' c' t' bz' tr' : LVec}
    (h : MS ck r s a b dn c t bz tr = MS ck' r' s' a' b' dn' c' t' bz' tr') :
    dn = dn' ∧ c = c' ∧ t = t' ∧ bz = bz' ∧ tr = tr' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- `t` busy cycles after a start with operands `A`, `B`: the tree ready to level `t`. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c tr, st = MS ck r s a b (knownBit false) c (.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) tr ∧
    Good N W AccW A B t tr

/-- Finished with `A`, `B`: `done` = 1, `C` the product, every node of the tree ready. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b t tr, st = MS ck r s a b (knownBit true) (.ofBitVec (Tasks.Matmul.product N W AccW A B)) t
    (knownBit false) tr ∧ Good N W AccW A B (clog2 N) tr

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz tr, prev = MS ck r s a b dn c t bz tr ∧ Wd N AccW dn c t bz tr ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c t bz tr

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

theorem bounds {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N * N * W < 2 ^ 31) : clog2 N < 2 ^ 31 := by
  have h1 : N ≤ N * N * W := by
    rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hN hW)
  have := clog2_le_self N; omega

/-- **The phase model** at `(N, W, AccW)`, latency `clog2 N + 1`. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (clog2 N + 1) (design.sem N W AccW) where
  Shape := I N AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t bz tr k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, tr, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c t bz tr hw
  Ready st := ∃ ck r s a b c t tr, st = MS ck r s a b (knownBit false) c t (knownBit false) tr
  Busy x m st := ∃ t, t + m = clog2 N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, t, tr, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, c, tr, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, t, tr, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, tr, -, hw, rfl⟩ hr
    obtain ⟨h1, -, -, h4, -⟩ := hw
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r, mmNext_regs,
      (ctrl_reset N _ dn t bz h1 h4).1, (ctrl_reset N _ dn t bz h1 h4).2]
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, tr, -, hw, rfl⟩ - hr hs hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    obtain ⟨d1, d2, d3⟩ := ctrl_start N dn t bz h1 h3 h4
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb, mmNext_regs, d1, d2, d3]
    exact .inr ⟨clog2 N, by omega, 0, by omega, _, _, _, _, _, _, _, rfl, T_start hN hW x.1 x.2.1 h5⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, hw, rfl⟩
      ⟨t', ht', ck', r', s', a', b', c', tr', hb', hg⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb'
    obtain ⟨-, h2, -, -, -⟩ := hw
    have hL := bounds hN hW hNW
    obtain ⟨d1, d2, d3⟩ := ctrl_busy (N := N) (t := t') (by omega) (by omega)
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmNext_regs, d1, d2, d3]
    by_cases hf : t' = clog2 N
    · left
      subst hf
      rw [C_root hN x.1 x.2.1 _ _ _ hg (le_pow_clog2 N) h2]
      simp only [decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, rfl, good_down (T_step hN x.1 x.2.1 _ _ hg)⟩
    · right
      simp only [hf, decide_false, ne_eq, not_false_eq_true, decide_true]
      exact ⟨m - 1, by omega, t' + 1, by omega, _, _, _, _, _, _, _, rfl, T_step hN x.1 x.2.1 _ _ hg⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, -, rfl⟩ ⟨ck', r', s', a', b', c', t', tr', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmNext_regs, ctrl_idle, ctrl_idle,
      ctrl_idle]
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, -, rfl⟩ ⟨ck', r', s', a', b', t', tr', hb, hg⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmNext_regs, ctrl_idle, ctrl_idle,
      ctrl_idle, C_root hN x.1 x.2.1 _ _ _ hg (le_pow_clog2 N) (by simp)]
    exact ⟨_, _, _, _, _, _, _, rfl, good_down (T_step hN x.1 x.2.1 _ _ hg)⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "T"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨by simp [Tasks.Matmul.task, cbD, cbDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ cbCtrl N :: cbPEs N W AccW := by simpa [cbD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · simp [Tasks.Matmul.task, cbCtrl, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · rcases pe_cases hm with ⟨i, j, x, -, -, -, rfl⟩ | ⟨i, j, k, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
      simp [Tasks.Matmul.task, cbNode, cbLeaf, cbOut, sext, edgeClock, asyncReset, processDataNames, stmtNames,
        stmtOptNames, lhsNames, exprNames, exprListNames]

/-! ## 8. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3) -/

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW)))
    (by simp [cbD, cbDecls, Design2.outputNames, Design2.inputNames])

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨t, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨tr, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain rfl := powerUp_nil.mp h10
  exact ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, w6, w7, w8, w9, w10⟩

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N AccW) (mm_powerUp N W AccW hN hW hA) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, t, bz, tr, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t bz tr kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c t bz tr hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem ctrl_xsafe (N W AccW : Nat) : xsProc (cbD N W AccW) (cbCtrl N) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, cbCtrl, nb, c32, cbD, cbDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem node_xsafe {N W AccW i j x : Nat} (hi : i < N) (hj : j < N) (hx : x + 1 < N) :
    xsProc (cbD N W AccW) (cbNode N AccW i j x) = true := by
  have h0 := nd_le (AccW := AccW) hi hj (x := x) (by omega)
  have h1 := nd_le (AccW := AccW) hi hj (x := 2 * x + 1) (by omega)
  have h2 := nd_le (AccW := AccW) hi hj (x := 2 * x + 2) (by omega)
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, cbNode, cbD, cbDecls, h0, h1, h2]

theorem leaf_xsafe {N W AccW i j k : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) (hk : k < N) :
    xsProc (cbD N W AccW) (cbLeaf N W AccW i j k) = true := by
  have h0 := nd_le (AccW := AccW) hi hj (x := N - 1 + k) (by omega)
  have ha : (i * N + k) * W + W ≤ N * N * W := Lib.rowMajor_window_le hi hk
  have hb : (k * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le hk hj
  have ha1 : (i * N + k) * W + W - 1 + 1 ≤ N * N * W := by omega
  have hb1 : (k * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, cbLeaf, sext, cbD, cbDecls,
    h0, ha, hb, ha1, hb1]

theorem out_xsafe {N W AccW i j : Nat} (hi : i < N) (hj : j < N) :
    xsProc (cbD N W AccW) (cbOut N AccW i j) = true := by
  have h0 := nd_le (AccW := AccW) hi hj (x := 0) (by omega)
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, cbOut, cbD, cbDecls, h0, hC]

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ cbCtrl N :: cbPEs N W AccW := by simpa [cbD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ctrl_xsafe N W AccW
  · rcases pe_cases hm with ⟨i, j, x, hi, hj, hx, rfl⟩ | ⟨i, j, k, hi, hj, hk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
    · exact node_xsafe hi hj hx
    · exact leaf_xsafe hW hi hj hk
    · exact out_xsafe hi hj

/-- **The cube satisfies the matmul statement (txtask-v2) at latency `clog2 N + 1`** (`3` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA)
    (mm_disciplined N W AccW hN hW hA) (mm_terminatesPU N W AccW hN hW hA) (by show 1 ≤ clog2 N + 1; omega)
    (model N W AccW hN hW hA hNW) (mm_powerUp N W AccW hN hW hA) (mm_moore N W AccW hN hW hA)
    (mm_xsafe N W AccW hN hW hA)

end Submission
