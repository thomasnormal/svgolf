-- svgolf-latency: 26
import Submission.Design
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.BitVecArith
import LeanModels.Sv.CombViewArith
import LeanModels.Sv.Mono2
import LeanModels.Sv.NbaCommit
import SvGolf.SeqV2

/-!
# A processing-in-memory matmul: N banks with one multiply-accumulate unit each

`solution.sv`: bank `r` holds row `r` of `A` (sign-extended to `AccW` bits) in array row 0; one
sequencer issues one command per cycle to all banks: `ACT0`, then per column `j` of `B` a `FILL`
(the column broadcast into every unit's `grfa`) and `N` reads `RD` (each one multiply-accumulate of
the open row's column 0 with `grfa`'s entry 0, both rotating), then `LAST`, `ACT1`, `WR`, `PRE`,
`READ`. Latency `N² + N + 6`.

1. Agreement (`mm_sem_eq`): the loaded family is the hand-built `mmD`.
2. The clock step (`mm_cycle`) and the commit, register by register (`nbaFold`).
3. The program positions and the register values at each (`AtAct0` … `AtRead`), one step each.
4. The phase model and txtask-v2's rules.
-/

namespace Submission

open LeanModels.Sv SvGolf

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The latency: `1 + N·(N+1) + 5` busy cycles. -/
def lat (N _W _AccW : Nat) : Nat := N * N + N + 6

/-! ## 1. Agreement -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `n == v` against a 32-bit constant. -/
abbrev eqE (n : String) (v : Int) : Expr2 := .binary .eq (.ident n) (c32 v)

/-- A nonblocking write of a constant to a whole signal. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `w` zero bits. -/
abbrev zv (w : Nat) : LVec := LVec.replicate w .l0

/-- One known bit. -/
abbrev b1 (b : Bool) : LVec := ⟨#[if b then .l1 else .l0]⟩

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- A copy of window `src[lo' +: w]` into `dst[lo +: w]`. -/
abbrev mv (dst : String) (lo : Nat) (src : String) (lo' w : Nat) : Stmt2 :=
  .nbaAssign (.slice dst lo w) (.slice (.ident src) lo' w)

/-- The sequencer. -/
def ctrlP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" (b1 false), nb "done" (b1 false), nb "ph" (LVec.ofInt 32 0), nb "j" (zv 32), nb "k" (zv 32)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" (b1 true), nb "done" (b1 false), nb "ph" (LVec.ofInt 32 0), nb "j" (zv 32), nb "k" (zv 32)])
      (some (.ifStmt (.ident "busy")
        (.block #[.ifStmt (eqE "ph" 2)
          (.block #[.ifStmt (.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1)))
            (.block #[nb "k" (zv 32),
              .ifStmt (.binary .eq (.ident "j") (.binary .sub (c32 N) (c32 1)))
                (nb "ph" (LVec.ofInt 32 3))
                (some (.block #[.nbaAssign (.ident "j") (.binary .add (.ident "j") (c32 1)),
                  nb "ph" (LVec.ofInt 32 1)]))])
            (some (.nbaAssign (.ident "k") (.binary .add (.ident "k") (c32 1))))])
          (some (.ifStmt (eqE "ph" 7)
            (.block #[nb "busy" (b1 false), nb "done" (b1 true)])
            (some (.nbaAssign (.ident "ph") (.binary .add (.ident "ph") (c32 1))))))])
        none)))))

/-- The host's copy of `B`. -/
def bfP (W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "bf") (.ident "B"))
    (some (.ifStmt (.ident "busy")
      (.block #[.ifStmt (eqE "ph" 1) (.nbaAssign (.ident "bf") (.binary (.shr false) (.ident "bf") (c32 W))) none])
      none)))

/-- Unit `r`'s multiply-accumulate. -/
def macP (N W AccW r : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.block #[.ifStmt (eqE "ph" 1)
      (.nbaAssign (.slice "grfb" (r * AccW) AccW) (.lit (zv AccW)))
      (some (.ifStmt (eqE "ph" 2)
        (.nbaAssign (.slice "grfb" (r * AccW) AccW)
          (.resize AccW (.binary .sub
            (.binary .add (.resize (AccW + W) (.slice (.ident "grfb") (r * AccW) AccW))
              (.binary .mul (.resize (AccW + W) (.slice (.ident "rb") (r * N * AccW) AccW))
                (.concat #[.repl AccW (.concat #[.lit (b1 false)]), .slice (.ident "grfa") (r * N * W) W])))
            (.binary (.shl false)
              (.binary .and (.resize (AccW + W) (.repl AccW (.concat #[.slice (.ident "grfa") (r * N * W + W - 1) 1])))
                (.resize (AccW + W) (.slice (.ident "rb") (r * N * AccW) AccW)))
              (c32 W)))))
        none))])
    none)

/-- Column slot `u` (`= r·N + c`) of a bank: the host's write of `A`, then the commands. `gl` is the gather
source in `bf`, `rl` the slot the rotations read, `gs[gsl +: AccW]` what the result register shifts in. -/
def slotP (W AccW u gl rl : Nat) (gs : String) (gsl : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .ifStmt (.ident "start")
      (.nbaAssign (.slice "arr0" (u * AccW) AccW) (.resize AccW (sext "A" AccW (u * W) W))) none,
    .ifStmt (.ident "busy") (.block #[
      .ifStmt (eqE "ph" 0) (mv "rb" (u * AccW) "arr0" (u * AccW) AccW)
      (some (.ifStmt (eqE "ph" 1)
        (.block #[mv "grfa" (u * W) "bf" gl W,
          .ifStmt (eqE "j" 0) (.nbaAssign (.slice "grfc" (u * AccW) AccW) (.lit (zv AccW)))
            (some (mv "grfc" (u * AccW) gs gsl AccW))])
      (some (.ifStmt (eqE "ph" 2)
        (.block #[mv "rb" (u * AccW) "rb" (rl * AccW) AccW, mv "grfa" (u * W) "grfa" (rl * W) W])
      (some (.ifStmt (eqE "ph" 3) (mv "grfc" (u * AccW) gs gsl AccW)
      (some (.ifStmt (eqE "ph" 4) (mv "rb" (u * AccW) "arr1" (u * AccW) AccW)
      (some (.ifStmt (eqE "ph" 5) (mv "rb" (u * AccW) "grfc" (u * AccW) AccW)
      (some (.ifStmt (eqE "ph" 6) (mv "arr1" (u * AccW) "rb" (u * AccW) AccW)
      (some (.ifStmt (eqE "ph" 7) (mv "C" (u * AccW) "arr1" (u * AccW) AccW) none))))))))))))))]) none])

/-- Column `c < N - 1` of bank `r`. -/
abbrev cellP (N W AccW r c : Nat) : Process2 :=
  slotP W AccW (r * N + c) (c * N * W) (r * N + c + 1) "grfc" ((r * N + c + 1) * AccW)

/-- Column `N - 1` of bank `r`: the rotations wrap to column 0, the results enter from `grfb`. -/
abbrev topP (N W AccW r : Nat) : Process2 :=
  slotP W AccW (r * N + N - 1) ((N - 1) * N * W) (r * N) "grfb" (r * AccW)

/-- The declarations: `A`/`B`/`bf`/`grfa` at `wa`, `C`/`arr0`/`arr1`/`rb`/`grfc` at `wc`, `grfb` at `wb` bits. -/
def mmDecls (wa wc wb : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "busy", width := 1 }, { name := "ph", width := 32 },
   { name := "j", width := 32 }, { name := "k", width := 32 }, { name := "bf", width := wa },
   { name := "arr0", width := wc }, { name := "arr1", width := wc }, { name := "rb", width := wc },
   { name := "grfa", width := wa }, { name := "grfb", width := wb }, { name := "grfc", width := wc }]

/-- Bank `r`'s processes, in source order. -/
def bankPs (N W AccW r : Nat) : List Process2 :=
  macP N W AccW r :: ((List.range (N - 1)).map (cellP N W AccW r) ++ [topP N W AccW r])

/-- The generated processes. -/
def genPs (N W AccW : Nat) : List Process2 := (List.range N).flatMap (bankPs N W AccW)

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * N * AccW) (N * AccW)).toArray
  processes := (ctrlP N :: bfP W :: genPs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("READ", 7), ("PRE", 6), ("WR", 5), ("ACT1", 4), ("LAST", 3), ("RD", 2), ("FILL", 1), ("ACT0", 0),
      ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("ACT0", 32), ("FILL", 32), ("RD", 32), ("LAST", 32),
      ("ACT1", 32), ("WR", 32), ("PRE", 32), ("READ", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "busy", "ph", "j", "k", "bf", "arr0", "arr1", "rb", "grfa",
    "grfb", "grfc"].map (·, 1)

theorem mm_decls (N W AccW : Int) :
    buildDecls (mmEnv N W AccW) design.pdesign.decls =
      .ok (mmDecls ((N * N * W - 1).natAbs + 1) ((N * N * AccW - 1).natAbs + 1) ((N * AccW - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, mmDecls, Gen2.except_ok_bind]

theorem mm_elems (N W AccW : Int) : buildElems (mmEnv N W AccW) design.pdesign.decls = .ok mmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, mmElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev mmE (N W AccW : Nat) : IEnv :=
  (mmEnv N W AccW).withDecls (mmDecls (N * N * W) (N * N * AccW) (N * AccW))

/-- The static processes' templates. -/
def ctrlT : PProcess := match design.pdesign.processes with
  | [p, _] => p
  | _ => .alwaysFF "" (.block [])
def bfT : PProcess := match design.pdesign.processes with
  | [_, p] => p
  | _ => .alwaysFF "" (.block [])

/-- The generate templates. -/
def macT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p, _, _]] => p
  | _ => .alwaysFF "" (.block [])
def cellT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [_, .genFor _ _ _ _ _ _ [.process p], _]] => p
  | _ => .alwaysFF "" (.block [])
def topT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [_, _, .process p]] => p
  | _ => .alwaysFF "" (.block [])

macro "mm_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, mmEnv, mmScope, mmDecls, mmElems, ctrlT, bfT, macT, cellT, topT, ctrlP, bfP, macP, slotP, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  divOperandWidthSum2, instDivOperand2, instDivParts2, fitDivOperand2, *])

theorem mm_static (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [ctrlP N, bfP W] := by
  have h1 : (0 : Int) < W := by omega
  have h2 : 0 < W := hW
  mm_simp
  try and_intros
  all_goals first | rfl | decide | omega | skip

/-- The facts every template instantiation needs. -/
theorem inst_facts {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    ((0 : Int) < W ∧ (0 : Int) < AccW ∧ 0 < W ∧ 0 < AccW ∧ ¬ W = 0 ∧ ¬ AccW = 0) ∧
    ((N : Int) * N * W - 1).natAbs + 1 = N * N * W ∧ ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW ∧
    ((N : Int) * AccW - 1).natAbs + 1 = N * AccW ∧ (PartMode.up == PartMode.range) = false ∧
    ¬ AccW + W < AccW ∧ ¬ AccW + W ≤ AccW ∧ (1 : Int) ≤ N * N * W ∧ (1 : Int) ≤ N * N * AccW ∧ (1 : Int) ≤ N * AccW := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have pB := Nat.mul_pos hN hA
  refine ⟨⟨by omega, by omega, hW, hA, by omega, by omega⟩, ?_, ?_, ?_, rfl, by omega, by omega, ?_, ?_, ?_⟩
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pA
  · rw [← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pB
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; omega
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; omega
  · rw [← Int.natCast_mul]; omega

theorem mac_inst (N W AccW r : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) :
    instProcess2 ((mmE N W AccW).bindVal "r" r) mmElems macT = macP N W AccW r := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := inst_facts hN hW hA
  have hb := Lib.window_bounds_of_natCast ((r : Int) * AccW) (N * AccW)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr) hA (by simp) (by simp)
  have hrb := Lib.window_bounds_of_natCast ((r : Int) * N * AccW) (N * N * AccW)
    (Lib.rowMajor_window_le (N := N) (w := AccW) (j := 0) hr (by omega)) hA (by simp) (by simp)
  have hg := Lib.window_bounds_of_natCast ((r : Int) * N * W) (N * N * W)
    (Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hr (by omega)) hW (by simp) (by simp)
  mm_simp
  repeat (unfold instExpr2; mm_simp)
  all_goals (try and_intros) <;> first | rfl | decide

/-- Window facts for unit `u` of the `AccW`-entry and `W`-entry registers, in `instantiate2`'s `Int` form. -/
theorem uwin {N K u : Nat} (X : Int) (hK : 1 ≤ K) (hu : u < N * N) (hx : ((u * K : Nat) : Int) = X) :
    0 ≤ X ∧ X.toNat = u * K ∧ X + K - 1 < N * N * K ∧ 1 ≤ X + K ∧ (X + K).toNat = u * K + K :=
  Lib.window_bounds_of_natCast X _ (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu) hK hx (by simp)

theorem cell_inst (N W AccW r c : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) (hc : c + 1 < N) :
    instProcess2 (((mmE N W AccW).bindVal "r" r).bindVal "c" c) mmElems cellT = cellP N W AccW r c := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := inst_facts hN hW hA
  have hu : r * N + c < N * N := by have := Lib.rowMajor_window_le (w := 1) hr (show c < N by omega); simp at this; omega
  have hu1 : r * N + c + 1 < N * N := by have := Lib.rowMajor_window_le (w := 1) hr (show c + 1 < N by omega); simp at this; omega
  have w1 := uwin (((r : Int) * N + c) * AccW) hA hu (by simp)
  have w2 := uwin (((r : Int) * N + c) * W) hW hu (by simp)
  have w3 := uwin (((r : Int) * N + c + 1) * AccW) hA hu1 (by simp)
  have w4 := uwin (((r : Int) * N + c + 1) * W) hW hu1 (by simp)
  have hbf := Lib.window_bounds_of_natCast ((c : Int) * N * W) (N * N * W)
    (Lib.rowMajor_window_le (N := N) (w := W) (j := 0) (show c < N by omega) (by omega)) hW (by simp) (by simp)
  mm_simp
  repeat (unfold instExpr2; mm_simp)
  all_goals (try and_intros) <;> first | rfl | decide

theorem cast_sub1 {x : Nat} (h : 1 ≤ x) : ((x - 1 : Nat) : Int) = (x : Int) - 1 := by omega

theorem top_inst (N W AccW r : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) :
    instProcess2 ((mmE N W AccW).bindVal "r" r) mmElems topT = topP N W AccW r := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := inst_facts hN hW hA
  have hu : r * N + N - 1 < N * N := by
    have := Lib.rowMajor_window_le (w := 1) hr (show N - 1 < N by omega); simp at this; omega
  have hu0 : r * N < N * N := by
    have := Lib.rowMajor_window_le (w := 1) hr (show 0 < N by omega); simp at this; omega
  have hs : 1 ≤ r * N + N := by omega
  have w1 := uwin (((r : Int) * N + N - 1) * AccW) hA hu (by simp [cast_sub1 hs])
  have w2 := uwin (((r : Int) * N + N - 1) * W) hW hu (by simp [cast_sub1 hs])
  have w3 := uwin ((r : Int) * N * AccW) hA hu0 (by simp)
  have w4 := uwin ((r : Int) * N * W) hW hu0 (by simp)
  have hb := Lib.window_bounds_of_natCast ((r : Int) * AccW) (N * AccW)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr) hA (by simp) (by simp)
  have hbf := Lib.window_bounds_of_natCast (((N : Int) - 1) * N * W) (N * N * W)
    (Lib.rowMajor_window_le (N := N) (w := W) (j := 0) (show N - 1 < N by omega) (by omega)) hW
    (by simp [cast_sub1 hN]) (by simp)
  mm_simp
  repeat (unfold instExpr2; mm_simp)
  all_goals (try and_intros) <;> first | rfl | decide

theorem mm_gens_src : design.pdesign.generates =
    [.genFor (some "g_bank") "r" (.int 0) (.binary .slt (.genvarRef "r") (.paramRef "N" none))
      (.unary .inc (.genvarRef "r")) (some 4)
      [.process macT,
       .genFor (some "g_col") "c" (.int 0)
         (.binary .slt (.genvarRef "c") (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)))
         (.unary .inc (.genvarRef "c")) (some 3) ([cellT].map .process),
       .process topT]] := rfl

/-- **The generates expand to the banks' processes.** -/
theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  rw [mm_gens_src]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => [instProcess2 ((mmE N W AccW).bindVal "r" v) mmElems macT] ++
        (((intRange 0 ((N : Int) - 1 - 0).toNat).flatMap fun w =>
          [cellT].map (instProcess2 (((mmE N W AccW).bindVal "r" v).bindVal "c" w) mmElems)) ++
        [instProcess2 ((mmE N W AccW).bindVal "r" v) mmElems topT]))
      (evalInt_int 0) (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv]))
      (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv])) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map, genPs, List.singleton_append]
    congr 1
    refine CombView.flatMap_congr' fun r hr => ?_
    have hr' := List.mem_range.mp hr
    have ht' : ((N : Int) - 1).toNat = N - 1 := by omega
    rw [mac_inst N W AccW r hN hW hA hr', top_inst N W AccW r hN hW hA hr', ht', bankPs]
    congr 2
    exact List.map_congr_left fun c hc => cell_inst N W AccW r c hN hW hA hr' (by have := List.mem_range.mp hc; omega)
  · intro v _ _
    have hv : ∀ i : Int, (((mmE N W AccW).bindVal "r" v).bindVal "c" i).vals.lookup "N" = some (N : Int) := by
      intro i; simp [IEnv.bindVal, List.lookup, hNv]
    refine expandList2_cons_ok (GenItem.expand2_process macT)
      (expandList2_cons_ok ?_ (expandList2_singleton_ok (GenItem.expand2_process topT)))
    rw [GenItem.expand2_genFor_ascending_processes (N := (N : Int) - 1) (evalInt_int 0)
      (fun i => isInt_binary_of rfl (isInt_paramRef_of (hv i)) rfl)
      (fun i => evalInt_sub_of (isInt_paramRef_of (hv i)) rfl (evalInt_paramRef_of (hv i)) rfl) (by omega)]

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (mmDecls (N * N * W) (N * N * AccW) (N * AccW)) mmElems
        (genPs N W AccW)) := by
  have hd := mm_decls N W AccW
  rw [← Int.natCast_mul N N, ← Int.natCast_mul (N * N) W,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hW), ← Int.natCast_mul (N * N) AccW,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hA), ← Int.natCast_mul N AccW,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos hN hA)] at hd
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv _ _ _) hd (mm_elems _ _ _)
    (mm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      ctrlP N :: bfP W :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_static N W AccW hN hW hA]
  simp [design.pdesign]

/-! ### Disjoint windows -/

/-- Two processes write disjoint windows. -/
abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

/-- The windows of slot `u`: entry `u` of `grfa`, or of one of the `AccW`-entry registers. -/
def SlotWin (W AccW u : Nat) (a : DrvWin) : Prop :=
  (a.1 = "grfa" ∧ a.2 = some (u * W, W)) ∨
    ((a.1 = "arr0" ∨ a.1 = "rb" ∨ a.1 = "grfc" ∨ a.1 = "arr1" ∨ a.1 = "C") ∧ a.2 = some (u * AccW, AccW))

theorem slot_wins {W AccW u gl rl gsl : Nat} {gs : String} :
    ∀ a ∈ (slotP W AccW u gl rl gs gsl).procWins, SlotWin W AccW u a := by
  simp [slotP, mv, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, SlotWin]

theorem slot_disj {W AccW u u' : Nat} (h : u < u') {a b : DrvWin}
    (ha : SlotWin W AccW u a) (hb : SlotWin W AccW u' b) : a.overlaps b = false := by
  have h1 := rowMajor_le (K := W) h
  have h2 := rowMajor_le (K := AccW) h
  obtain ⟨n, w⟩ := a
  obtain ⟨n', w'⟩ := b
  simp only [SlotWin] at ha hb
  rcases ha with ⟨rfl, rfl⟩ | ⟨hn | hn | hn | hn | hn, rfl⟩ <;>
    rcases hb with ⟨rfl, rfl⟩ | ⟨hn' | hn' | hn' | hn' | hn', rfl⟩ <;>
    (try subst hn) <;> (try subst hn') <;> simp [DrvWin.overlaps] <;> omega

theorem overlaps_comm (a b : DrvWin) : a.overlaps b = b.overlaps a := by
  obtain ⟨n, w⟩ := a
  obtain ⟨n', w'⟩ := b
  by_cases hn : n = n'
  · subst hn; cases w <;> cases w' <;> simp [DrvWin.overlaps, Bool.and_comm]
  · simp only [DrvWin.overlaps, beq_eq_false_iff_ne.mpr hn, beq_eq_false_iff_ne.mpr (Ne.symm hn), Bool.false_and]

theorem slot_disj' {W AccW u u' : Nat} (h : u ≠ u') {a b : DrvWin}
    (ha : SlotWin W AccW u a) (hb : SlotWin W AccW u' b) : a.overlaps b = false := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact slot_disj h ha hb
  · rw [overlaps_comm]; exact slot_disj h hb ha

/-- The windows of a slot process are at its unit. -/
abbrev IsSlot (W AccW u : Nat) (p : Process2) : Prop := ∀ a ∈ p.procWins, SlotWin W AccW u a

theorem slots_disj {W AccW u u' : Nat} (h : u ≠ u') {p q : Process2}
    (hp : IsSlot W AccW u p) (hq : IsSlot W AccW u' q) : Disj p q :=
  fun a ha b hb => slot_disj' h (hp a ha) (hq b hb)

theorem mac_wins {N W AccW r : Nat} : ∀ a ∈ (macP N W AccW r).procWins, a = ("grfb", some (r * AccW, AccW)) := by
  simp [macP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]

theorem mac_slot_disj {N W AccW r u : Nat} {p : Process2} (hp : IsSlot W AccW u p) : Disj (macP N W AccW r) p := by
  intro a ha b hb
  rw [mac_wins a ha]
  rcases hp b hb with ⟨h, -⟩ | ⟨h, -⟩
  · simp [DrvWin.overlaps, h]
  · rcases h with h | h | h | h | h <;> simp [DrvWin.overlaps, h]

theorem slot_mac_disj {N W AccW r u : Nat} {p : Process2} (hp : IsSlot W AccW u p) : Disj p (macP N W AccW r) := by
  intro a ha b hb
  rw [mac_wins b hb]
  rcases hp a ha with ⟨h, -⟩ | ⟨h, -⟩
  · simp [DrvWin.overlaps, h]
  · rcases h with h | h | h | h | h <;> simp [DrvWin.overlaps, h]

theorem cell_isSlot (N W AccW r c : Nat) : IsSlot W AccW (r * N + c) (cellP N W AccW r c) := slot_wins
theorem top_isSlot (N W AccW r : Nat) : IsSlot W AccW (r * N + N - 1) (topP N W AccW r) := slot_wins

/-- The slots of bank `r`, with their units in `[r·N, r·N + N)`. -/
theorem bank_slot {N W AccW r : Nat} (hN : 1 ≤ N) {p : Process2} (hp : p ∈ bankPs N W AccW r) :
    p = macP N W AccW r ∨ ∃ u, r * N ≤ u ∧ u < r * N + N ∧ IsSlot W AccW u p := by
  simp only [bankPs, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | ⟨c, hc, rfl⟩ | rfl
  · exact .inl rfl
  · exact .inr ⟨r * N + c, by omega, by omega, cell_isSlot N W AccW r c⟩
  · exact .inr ⟨r * N + N - 1, by omega, by omega, top_isSlot N W AccW r⟩

theorem bank_pairwise {N W AccW r : Nat} (hN : 1 ≤ N) :
    (bankPs N W AccW r).Pairwise Disj := by
  refine List.Pairwise.cons (fun p hp => ?_) ?_
  · rcases bank_slot hN (List.mem_cons_of_mem _ hp) with h | ⟨u, -, -, hu⟩
    · -- the mac process is not in the tail
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    List.mem_nil_iff, or_false] at hp
      rcases hp with ⟨c, -, rfl⟩ | rfl
      · exact mac_slot_disj (cell_isSlot N W AccW r c)
      · exact mac_slot_disj (top_isSlot N W AccW r)
    · exact mac_slot_disj hu
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun hc hc' h =>
      slots_disj (by omega) (cell_isSlot N W AccW r _) (cell_isSlot N W AccW r _)),
      List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
    simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    rw [List.mem_singleton] at hq
    subst hq
    exact slots_disj (by omega) (cell_isSlot N W AccW r c) (top_isSlot N W AccW r)

theorem ctrl_names (N : Nat) : ∀ a ∈ (ctrlP N).procWins,
    a.1 = "busy" ∨ a.1 = "done" ∨ a.1 = "ph" ∨ a.1 = "j" ∨ a.1 = "k" := by
  simp [ctrlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]

theorem bf_names (W : Nat) : ∀ a ∈ (bfP W).procWins, a.1 = "bf" := by
  simp [bfP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]

/-- Every generated process writes only `grfb` or a slot register. -/
theorem gen_names {N W AccW : Nat} (hN : 1 ≤ N) {p : Process2} (hp : p ∈ genPs N W AccW) :
    ∀ a ∈ p.procWins, a.1 = "grfb" ∨ a.1 = "grfa" ∨ a.1 = "arr0" ∨ a.1 = "rb" ∨ a.1 = "grfc" ∨ a.1 = "arr1" ∨
      a.1 = "C" := by
  simp only [genPs, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨r, -, hp⟩ := hp
  intro a ha
  rcases bank_slot hN hp with rfl | ⟨u, -, -, hu⟩
  · rw [mac_wins a ha]; simp
  · rcases hu a ha with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inr (.inl h)
    · rcases h with h | h | h | h | h <;> simp [h]

theorem mm_pairwise (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (ctrlP N :: bfP W :: genPs N W AccW).Pairwise Disj := by
  refine List.Pairwise.cons (fun p hp a ha b hb => ?_) (List.Pairwise.cons (fun p hp a ha b hb => ?_) ?_)
  · have h1 := ctrl_names N a ha
    rcases List.mem_cons.mp hp with rfl | hp
    · have h2 := bf_names W b hb; rcases h1 with h | h | h | h | h <;> simp [DrvWin.overlaps, h, h2]
    · rcases gen_names hN hp b hb with h | h | h | h | h | h | h <;>
        rcases h1 with h' | h' | h' | h' | h' <;> simp [DrvWin.overlaps, h, h']
  · have h2 := bf_names W a ha
    rcases gen_names hN hp b hb with h | h | h | h | h | h | h <;> simp [DrvWin.overlaps, h, h2]
  · refine pairwise_flatMap_range (fun r _ => bank_pairwise hN) fun r r' hrr _ p hp q hq => ?_
    have hle := Nat.mul_le_mul_right N (show r + 1 ≤ r' by omega)
    rw [Nat.add_mul, Nat.one_mul] at hle
    rcases bank_slot hN hp with rfl | ⟨u, hu1, hu2, hu⟩ <;> rcases bank_slot hN hq with rfl | ⟨u', hu1', hu2', hu'⟩
    · intro a ha b hb
      rw [mac_wins a ha, mac_wins b hb]
      have := rowMajor_le (K := AccW) hrr
      simp [DrvWin.overlaps]; omega
    · exact mac_slot_disj hu'
    · exact slot_mac_disj hu
    · exact slots_disj (by omega) hu hu'

theorem mm_driversOk (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (ctrlP N :: bfP W :: genPs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW hN hW hA)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    simp only [genPs, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨r, -, hp⟩ := hp
    simp only [bankPs, List.mem_cons, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton,
    List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | ⟨c, -, rfl⟩ | rfl <;> exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, Process2.procWrites, List.mem_map]
    rintro n ⟨p, hp, a, ha, rfl⟩
    have hin : design.pdesign.inputNames = ["clk", "rst", "start", "A", "B"] := rfl
    rw [hin]
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases ctrl_names N a ha with h | h | h | h | h <;> simp [h]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [bf_names W a ha]
    · rcases gen_names hN hp a ha with h | h | h | h | h | h | h <;> simp [h]

/-- **The loaded family is `mmD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.sem N W AccW = mmD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA]; exact mm_driversOk N W AccW hN hW hA)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, mm_static N W AccW hN hW hA, mmD]
  simp [design.pdesign]

/-! ## 2. The clock step -/

/-- **`mmD` is in G0's FF-only profile.** -/
theorem mm_profile (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simp only [mmD, List.toList_toArray]; exact mm_pairwise N W AccW hN hW hA)⟩
  simp [mmD, ctrlP, bfP, genPs, bankPs, macP, slotP, mv, nb, sext, List.all_flatMap, List.all_map,
    Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB,
    Stmt2.listNbaStaticB, Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins, mmDecls]

/-- The 18 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("busy", bz), ("ph", ph),
   ("j", j), ("k", k), ("bf", bf), ("arr0", a0), ("arr1", a1), ("rb", rb), ("grfa", ga), ("grfb", gb), ("grfc", gc)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c bz ph j k bf a0 a1 rb ga gb gc := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The test `x == v` against a 32-bit constant, as evaluated. -/
abbrev phB (x : LVec) (v : Int) : Bool := (LVec.ofLogic (x.eqLogical (LVec.ofInt 32 v))).condTrue

/-- The test `x == N - 1`, as evaluated. -/
abbrev lastB (N : Nat) (x : LVec) : Bool :=
  (LVec.ofLogic (x.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue

def ctrlQ (N : Nat) (r s dn bz ph j k : LVec) : NbaQueue2 :=
  if r.condTrue then
    [wr "busy" bz (b1 false), wr "done" dn (b1 false), wr "ph" ph (LVec.ofInt 32 0), wr "j" j (zv 32), wr "k" k (zv 32)]
  else if s.condTrue then
    [wr "busy" bz (b1 true), wr "done" dn (b1 false), wr "ph" ph (LVec.ofInt 32 0), wr "j" j (zv 32), wr "k" k (zv 32)]
  else if bz.condTrue then
    if phB ph 2 then
      if lastB N k then
        if lastB N j then [wr "k" k (zv 32), wr "ph" ph (LVec.ofInt 32 3)]
        else [wr "k" k (zv 32), wr "j" j (j.add (LVec.ofInt 32 1)), wr "ph" ph (LVec.ofInt 32 1)]
      else [wr "k" k (k.add (LVec.ofInt 32 1))]
    else if phB ph 7 then [wr "busy" bz (b1 false), wr "done" dn (b1 true)]
    else [wr "ph" ph (ph.add (LVec.ofInt 32 1))]
  else []

def bfQ (W : Nat) (s b bz ph bf : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "bf" bf b]
  else if bz.condTrue then (if phB ph 1 then [wr "bf" bf (bf.shr (LVec.ofInt 32 W))] else [])
  else []

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- Unit `r`'s new accumulator in a read, evaluated. -/
def macV (N W AccW r : Nat) (rb ga gb : LVec) : LVec :=
  ((((gb.extract (r * AccW) AccW).resizeU (AccW + W)).add
    (((rb.extract (r * N * AccW) AccW).resizeU (AccW + W)).mul
      (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[b1 false]), ga.extract (r * N * W) W]))).sub
    ((((LVec.replVec AccW (LVec.concatMany #[ga.extract (r * N * W + W - 1) 1])).resizeU (AccW + W)).and
      ((rb.extract (r * N * AccW) AccW).resizeU (AccW + W))).shl (LVec.ofInt 32 W))).resizeU AccW

def macQ (N W AccW r : Nat) (bz ph rb ga gb : LVec) : NbaQueue2 :=
  if bz.condTrue then
    if phB ph 1 then [("grfb", r * AccW, (zv AccW).resizeU AccW)]
    else if phB ph 2 then [("grfb", r * AccW, (macV N W AccW r rb ga gb).resizeU AccW)]
    else []
  else []

def slotQ (W AccW u gl rl gsl : Nat) (s bz ph j a bf a0 a1 rb ga gc gs : LVec) : NbaQueue2 :=
  (if s.condTrue then [("arr0", u * AccW, ((sxv a AccW (u * W) W).resizeU AccW).resizeU AccW)] else []) ++
  (if bz.condTrue then
    if phB ph 0 then [("rb", u * AccW, (a0.extract (u * AccW) AccW).resizeU AccW)]
    else if phB ph 1 then
      ("grfa", u * W, (bf.extract gl W).resizeU W) ::
        (if phB j 0 then [("grfc", u * AccW, (zv AccW).resizeU AccW)]
         else [("grfc", u * AccW, (gs.extract gsl AccW).resizeU AccW)])
    else if phB ph 2 then
      [("rb", u * AccW, (rb.extract (rl * AccW) AccW).resizeU AccW), ("grfa", u * W, (ga.extract (rl * W) W).resizeU W)]
    else if phB ph 3 then [("grfc", u * AccW, (gs.extract gsl AccW).resizeU AccW)]
    else if phB ph 4 then [("rb", u * AccW, (a1.extract (u * AccW) AccW).resizeU AccW)]
    else if phB ph 5 then [("rb", u * AccW, (gc.extract (u * AccW) AccW).resizeU AccW)]
    else if phB ph 6 then [("arr1", u * AccW, (rb.extract (u * AccW) AccW).resizeU AccW)]
    else if phB ph 7 then [("C", u * AccW, (a1.extract (u * AccW) AccW).resizeU AccW)]
    else []
  else [])

macro "run_simp" : tactic => `(tactic| simp [ctrlP, bfP, macP, slotP, mv, nb, c32, eqE, sext, sxv, macV,
  runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, MS, SvState.lookup,
  evalBinOp, wr, *])

set_option hygiene false in
macro "slot_tac" : tactic => `(tactic| (
  by_cases hs : s.condTrue = true <;> by_cases hb : bz.condTrue = false <;>
  first
  | (run_simp; done)
  | (by_cases p0 : phB ph 0 = true
     · run_simp
     by_cases p1 : phB ph 1 = true
     · by_cases pj : phB j 0 = true <;> run_simp
     by_cases p2 : phB ph 2 = true
     · run_simp
     by_cases p3 : phB ph 3 = true
     · run_simp
     by_cases p4 : phB ph 4 = true
     · run_simp
     by_cases p5 : phB ph 5 = true
     · run_simp
     by_cases p6 : phB ph 6 = true
     · run_simp
     by_cases p7 : phB ph 7 = true <;> run_simp)))

section run
variable (F : Nat) (hF : 40 ≤ F) (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec)
include hF

theorem ctrl_run (N : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) [] (ctrlP N) =
      .ok (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, ctrlQ N r s dn bz ph j k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true
  · run_simp
  by_cases h2 : s.condTrue = true
  · run_simp
  by_cases h3 : bz.condTrue = false
  · run_simp
  by_cases h4 : phB ph 2 = true
  · by_cases h5 : lastB N k = true
    · by_cases h6 : lastB N j = true <;> run_simp
    · run_simp
  · by_cases h7 : phB ph 7 = true <;> run_simp

theorem bf_run (W : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) [] (bfP W) =
      .ok (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, bfQ W s b bz ph bf) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold bfQ
  by_cases h1 : s.condTrue = true <;> by_cases h2 : bz.condTrue = true <;> by_cases h3 : phB ph 1 = true <;> run_simp

theorem mac_run (N W AccW i : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) [] (macP N W AccW i) =
      .ok (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, macQ N W AccW i bz ph rb ga gb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold macQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : phB ph 1 = true <;> by_cases h3 : phB ph 2 = true <;> run_simp

theorem cell_run (N W AccW i c0 : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) [] (cellP N W AccW i c0) =
      .ok (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, slotQ W AccW (i * N + c0) (c0 * N * W) (i * N + c0 + 1)
        ((i * N + c0 + 1) * AccW) s bz ph j a bf a0 a1 rb ga gc gc) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold slotQ
  slot_tac

theorem top_run (N W AccW i : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) [] (topP N W AccW i) =
      .ok (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, slotQ W AccW (i * N + N - 1) ((N - 1) * N * W) (i * N)
        (i * AccW) s bz ph j a bf a0 a1 rb ga gc gb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold slotQ
  slot_tac

end run

/-- The generated processes' updates. -/
def genQ (N W AccW : Nat) (s bz ph j a bf a0 a1 rb ga gb gc : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i =>
    macQ N W AccW i bz ph rb ga gb ++
      ((List.range (N - 1)).flatMap (fun c0 => slotQ W AccW (i * N + c0) (c0 * N * W) (i * N + c0 + 1)
          ((i * N + c0 + 1) * AccW) s bz ph j a bf a0 a1 rb ga gc gc) ++
        slotQ W AccW (i * N + N - 1) ((N - 1) * N * W) (i * N) (i * AccW) s bz ph j a bf a0 a1 rb ga gc gb)

/-- One cycle's updates, in process order. -/
def mmQ (N W AccW : Nat) (r s b dn bz ph j k a bf a0 a1 rb ga gb gc : LVec) : NbaQueue2 :=
  ctrlQ N r s dn bz ph j k ++ (bfQ W s b bz ph bf ++ genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc)

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) (mmQ N W AccW r s b dn bz ph j k a bf a0 a1 rb ga gb gc)

theorem mm_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmD N W AccW).processes.toList) :
    p = ctrlP N ∨ p = bfP W ∨ (∃ i, p = macP N W AccW i) ∨ (∃ i c0, p = cellP N W AccW i c0) ∨
      ∃ i, p = topP N W AccW i := by
  simp only [mmD, List.toList_toArray, List.mem_cons, genPs, List.mem_flatMap, List.mem_range, bankPs,
    List.mem_append, List.mem_map, List.mem_singleton, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | ⟨i, -, rfl | ⟨c0, -, rfl⟩ | rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl ⟨i, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨i, c0, rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨i, rfl⟩)))

/-- **One cycle of the loaded design is G0's clock step**, evaluated. -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) (kk F : Nat) (hF : 40 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c bz ph j k bf a0 a1 rb ga gb gc, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    rcases mm_mem hp with rfl | rfl | ⟨i, rfl⟩ | ⟨i, c0, rfl⟩ | ⟨i, rfl⟩ <;> rfl
  rw [mm_sem_eq N W AccW hN hW hA, cycleStep2_profile (mm_profile N W AccW hN hW hA) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD, List.toList_toArray, List.flatMap_cons, ctrl_run F hF, bf_run F hF, genPs, List.flatMap_assoc,
      bankPs, List.flatMap_append, List.flatMap_map, mac_run F hF, cell_run F hF, top_run F hF, List.flatMap_nil,
      List.append_nil, mmNext, mmQ, genQ]
  · intro i p hp
    rw [apply_mm]
    rcases mm_mem (List.mem_of_getElem? (by simpa using hp)) with rfl | rfl | ⟨i, rfl⟩ | ⟨i, c0, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N⟩
    · exact ⟨_, bf_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W⟩
    · exact ⟨_, mac_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW i⟩
    · exact ⟨_, cell_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW i c0⟩
    · exact ⟨_, top_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW i⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The commit, register by register -/

section commit
variable {ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec} {lo : Nat} {v : LVec}
theorem nb_dn : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c bz ph j k bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) bz ph j k bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bz : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("busy", lo, v) =
    MS ck r s a b dn c (bz.insertAt lo v) ph j k bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ph : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("ph", lo, v) =
    MS ck r s a b dn c bz (ph.insertAt lo v) j k bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_j : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("j", lo, v) =
    MS ck r s a b dn c bz ph (j.insertAt lo v) k bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_k : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("k", lo, v) =
    MS ck r s a b dn c bz ph j (k.insertAt lo v) bf a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bf : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("bf", lo, v) =
    MS ck r s a b dn c bz ph j k (bf.insertAt lo v) a0 a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_a0 : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("arr0", lo, v) =
    MS ck r s a b dn c bz ph j k bf (a0.insertAt lo v) a1 rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_a1 : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("arr1", lo, v) =
    MS ck r s a b dn c bz ph j k bf a0 (a1.insertAt lo v) rb ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_rb : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("rb", lo, v) =
    MS ck r s a b dn c bz ph j k bf a0 a1 (rb.insertAt lo v) ga gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ga : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("grfa", lo, v) =
    MS ck r s a b dn c bz ph j k bf a0 a1 rb (ga.insertAt lo v) gb gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_gb : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("grfb", lo, v) =
    MS ck r s a b dn c bz ph j k bf a0 a1 rb ga (gb.insertAt lo v) gc := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_gc : nbaStep (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) ("grfc", lo, v) =
    MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb (gc.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- The thirteen registers. -/
abbrev RegName (n : String) : Prop :=
  n = "done" ∨ n = "C" ∨ n = "busy" ∨ n = "ph" ∨ n = "j" ∨ n = "k" ∨ n = "bf" ∨ n = "arr0" ∨ n = "arr1" ∨
    n = "rb" ∨ n = "grfa" ∨ n = "grfb" ∨ n = "grfc"

/-- Committing a queue of writes to the thirteen registers. -/
theorem commit_MS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c bz ph j k bf a0 a1 rb ga gb gc : LVec),
    (∀ u ∈ q, RegName u.1) →
    commitNba2 (MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) q =
      MS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "busy" q bz) (nbaFold "ph" q ph)
        (nbaFold "j" q j) (nbaFold "k" q k) (nbaFold "bf" q bf) (nbaFold "arr0" q a0) (nbaFold "arr1" q a1)
        (nbaFold "rb" q rb) (nbaFold "grfa" q ga) (nbaFold "grfb" q gb) (nbaFold "grfc" q gc)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, h => by
    have hq := @commit_MS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;>
      simp only at h1 <;> subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_bz, nb_ph, nb_j, nb_k, nb_bf, nb_a0, nb_a1, nb_rb, nb_ga, nb_gb, nb_gc,
        hq _ _ _ _ _ _ _ _ _ _ _ _ _ h', nbaFold]

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 := h u List.mem_cons_self
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

/-- The slot registers. -/
abbrev SlotName (n : String) : Prop :=
  n = "arr0" ∨ n = "rb" ∨ n = "grfa" ∨ n = "grfc" ∨ n = "arr1" ∨ n = "C"

section names
variable {N W AccW : Nat} {r s b dn bz ph j k a bf a0 a1 rb ga gb gc gs : LVec}

theorem ctrlQ_names : ∀ u ∈ ctrlQ N r s dn bz ph j k,
    u.1 = "busy" ∨ u.1 = "done" ∨ u.1 = "ph" ∨ u.1 = "j" ∨ u.1 = "k" := by
  intro u hu; unfold ctrlQ at hu; (repeat' split at hu) <;> simp at hu <;>
    (try rcases hu with rfl | rfl | rfl | rfl | rfl) <;> (try rcases hu with rfl | rfl | rfl) <;>
    (try rcases hu with rfl | rfl) <;> (try subst hu) <;> simp
theorem bfQ_names : ∀ u ∈ bfQ W s b bz ph bf, u.1 = "bf" := by
  intro u hu; unfold bfQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem macQ_names (i : Nat) : ∀ u ∈ macQ N W AccW i bz ph rb ga gb, u.1 = "grfb" := by
  intro u hu
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : phB ph 1 = true <;> by_cases h3 : phB ph 2 = true <;>
    simp [macQ, h1, h2, h3] at hu <;> subst hu <;> rfl
theorem slotQ_names {u0 gl rl gsl : Nat} : ∀ u ∈ slotQ W AccW u0 gl rl gsl s bz ph j a bf a0 a1 rb ga gc gs,
    SlotName u.1 := by
  intro u hu; unfold slotQ at hu; rw [List.mem_append] at hu
  rcases hu with hu | hu <;> (repeat' split at hu) <;> simp at hu <;>
    (try rcases hu with rfl | rfl) <;> (try subst hu) <;> simp [SlotName]

theorem genQ_names : ∀ u ∈ genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc, u.1 = "grfb" ∨ SlotName u.1 := by
  intro u hu
  simp only [genQ, List.mem_flatMap, List.mem_range, List.mem_append] at hu
  obtain ⟨i, -, hu | ⟨c0, -, hu⟩ | hu⟩ := hu
  · exact .inl (macQ_names i u hu)
  · exact .inr (slotQ_names u hu)
  · exact .inr (slotQ_names u hu)

theorem mmQ_names : ∀ u ∈ mmQ N W AccW r s b dn bz ph j k a bf a0 a1 rb ga gb gc, RegName u.1 := by
  intro u hu
  simp only [mmQ, List.mem_append] at hu
  rcases hu with hu | hu | hu
  · rcases ctrlQ_names u hu with h | h | h | h | h <;> rw [h] <;> simp [RegName]
  · rw [bfQ_names u hu]; simp [RegName]
  · rcases genQ_names u hu with h | h
    · rw [h]; simp [RegName]
    · rcases h with h | h | h | h | h | h <;> rw [h] <;> simp [RegName]

theorem skip_ctrl {n : String} (h1 : n ≠ "busy") (h2 : n ≠ "done") (h3 : n ≠ "ph") (h4 : n ≠ "j")
    (h5 : n ≠ "k") (x : LVec) : nbaFold n (ctrlQ N r s dn bz ph j k) x = x :=
  nbaFold_of_forall_ne (fun u hu h => by
    rcases ctrlQ_names u hu with h' | h' | h' | h' | h' <;> rw [h'] at h <;> subst h <;> contradiction) x

theorem skip_bf {n : String} (h : n ≠ "bf") (x : LVec) : nbaFold n (bfQ W s b bz ph bf) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => h (h'.symm.trans (bfQ_names u hu))) x

theorem skip_mac {n : String} (h : n ≠ "grfb") (i : Nat) (x : LVec) : nbaFold n (macQ N W AccW i bz ph rb ga gb) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => h (h'.symm.trans (macQ_names i u hu))) x

theorem skip_slot {n : String} (h : ¬ SlotName n) {u0 gl rl gsl : Nat} (x : LVec) :
    nbaFold n (slotQ W AccW u0 gl rl gsl s bz ph j a bf a0 a1 rb ga gc gs) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => h (by rw [← h']; exact slotQ_names u hu)) x

theorem skip_gen {n : String} (h1 : n ≠ "grfb") (h2 : ¬ SlotName n) (x : LVec) :
    nbaFold n (genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    rcases genQ_names u hu with h | h
    · exact h1 (h'.symm.trans h)
    · exact h2 (by rw [← h']; exact h)) x

/-- The control's registers: only `ctrlQ` writes them. -/
theorem fold_ctrl (n : String) (h1 : n ≠ "bf") (h2 : n ≠ "grfb") (h3 : ¬ SlotName n) (x : LVec) :
    nbaFold n (mmQ N W AccW r s b dn bz ph j k a bf a0 a1 rb ga gb gc) x = nbaFold n (ctrlQ N r s dn bz ph j k) x := by
  simp only [mmQ, nbaFold_append, skip_bf h1, skip_gen h2 h3]

theorem fold_bf (x : LVec) :
    nbaFold "bf" (mmQ N W AccW r s b dn bz ph j k a bf a0 a1 rb ga gb gc) x = nbaFold "bf" (bfQ W s b bz ph bf) x := by
  simp only [mmQ, nbaFold_append, skip_ctrl (n := "bf") (by decide) (by decide) (by decide) (by decide) (by decide),
    skip_gen (n := "bf") (by decide) (by simp [SlotName])]

theorem fold_gen (n : String) (h1 : n ≠ "bf") (h2 : n ≠ "busy") (h3 : n ≠ "done") (h4 : n ≠ "ph") (h5 : n ≠ "j")
    (h6 : n ≠ "k") (x : LVec) :
    nbaFold n (mmQ N W AccW r s b dn bz ph j k a bf a0 a1 rb ga gb gc) x =
      nbaFold n (genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc) x := by
  simp only [mmQ, nbaFold_append, skip_ctrl h2 h3 h4 h5 h6, skip_bf h1]

theorem foldl_skip {α : Type} (l : List α) (f : α → NbaQueue2) (n : String) (h : ∀ x y, nbaFold n (f x) y = y)
    (y : LVec) : l.foldl (fun acc x => nbaFold n (f x) acc) y = y := by
  induction l generalizing y with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, h, ih]

theorem fold_grfb (x : LVec) :
    nbaFold "grfb" (genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc) x =
      (List.range N).foldl (fun acc i => nbaFold "grfb" (macQ N W AccW i bz ph rb ga gb) acc) x := by
  rw [genQ, nbaFold_flatMap]
  congr 1; funext acc i
  rw [nbaFold_append, nbaFold_append, nbaFold_flatMap,
    foldl_skip _ _ _ (fun _ _ => skip_slot (n := "grfb") (by simp [SlotName]) _),
    skip_slot (n := "grfb") (by simp [SlotName])]

theorem fold_slots (n : String) (h : n ≠ "grfb") (x : LVec) :
    nbaFold n (genQ N W AccW s bz ph j a bf a0 a1 rb ga gb gc) x =
      (List.range N).foldl (fun acc i =>
        nbaFold n (slotQ W AccW (i * N + N - 1) ((N - 1) * N * W) (i * N) (i * AccW) s bz ph j a bf a0 a1 rb ga gc gb)
          ((List.range (N - 1)).foldl (fun acc c0 => nbaFold n (slotQ W AccW (i * N + c0) (c0 * N * W) (i * N + c0 + 1)
            ((i * N + c0 + 1) * AccW) s bz ph j a bf a0 a1 rb ga gc gc) acc) acc)) x := by
  rw [genQ, nbaFold_flatMap]
  congr 1; funext acc i
  rw [nbaFold_append, nbaFold_append, nbaFold_flatMap, skip_mac h]

end names

/-! ## 4. The register values -/

attribute [local simp] condTrue_knownBit

/-- A known 32-bit counter value. -/
abbrev n32 (v : Nat) : LVec := .ofBitVec (BitVec.ofNat 32 v)

/-- `(i, e) ↦ g i e` over `i, e < N`, packed row-major (entry `i·N + e`). -/
abbrev P2 (K N : Nat) (g : Nat → Nat → BitVec K) : BitVec (N * N * K) := packBV K (N * N) fun u => g (u / N) (u % N)

/-- Column `e` of a row rotated by `k` columns (`e, k < N`, or `k = N`). -/
def rot (N e k : Nat) : Nat := if e + k < N then e + k else e + k - N

section vals
variable (N W AccW : Nat)

/-- Entry `u` of `A`, sign-extended to `AccW` bits (the host's write into array row 0). -/
def sA (A : BitVec (N * N * W)) (u : Nat) : BitVec AccW := (A.extractLsb' (u * W) W).signExtend AccW

/-- `B[kk][j]`. -/
def bE (B : BitVec (N * N * W)) (kk j : Nat) : BitVec W := B.extractLsb' ((kk * N + j) * W) W

/-- `Σ_{k' < k} A[i][k']·B[k'][j]` in the integers. -/
def psum (A B : BitVec (N * N * W)) (k i j : Nat) : Int :=
  (List.range k).foldl (fun acc k' => acc + Tasks.Matmul.entry W A (i * N + k') * Tasks.Matmul.entry W B (k' * N + j)) 0

/-- `C[i][j]` mod `2^AccW`. -/
def cv (A B : BitVec (N * N * W)) (i j : Nat) : BitVec AccW := BitVec.ofInt AccW (psum N W A B N i j)

/-- Array row 0 of every bank. -/
def a0V (A : BitVec (N * N * W)) : BitVec (N * N * AccW) := P2 AccW N fun i e => sA N W AccW A (i * N + e)
/-- The row buffers after `k` rotations. -/
def rbV (A : BitVec (N * N * W)) (k : Nat) : BitVec (N * N * AccW) :=
  P2 AccW N fun i e => sA N W AccW A (i * N + rot N e k)
/-- The units' `grfa`: column `j` of `B`, rotated by `k`. -/
def gaV (B : BitVec (N * N * W)) (j k : Nat) : BitVec (N * N * W) := P2 W N fun _ e => bE N W B (rot N e k) j
/-- The accumulators after `k` reads of column `j`. -/
def gbV (A B : BitVec (N * N * W)) (j k : Nat) : BitVec (N * AccW) :=
  packBV AccW N fun i => BitVec.ofInt AccW (psum N W A B k i j)
/-- The result registers after `s` shift-ins (`C[i][0 .. s-1]` in the top `s` entries, zeros below). -/
def gcV (A B : BitVec (N * N * W)) (s : Nat) : BitVec (N * N * AccW) :=
  P2 AccW N fun i e => if N ≤ e + s then cv N W AccW A B i (e + s - N) else 0
/-- The host's copy of `B` after `j` columns. -/
def bfV (B : BitVec (N * N * W)) (j : Nat) : BitVec (N * N * W) := B >>> (j * W)

end vals

theorem rm_div {N i c : Nat} (hc : c < N) : (i * N + c) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem rm_mod {N i c : Nat} (hc : c < N) : (i * N + c) % N = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem rm_lt {N i c : Nat} (hi : i < N) (hc : c < N) : i * N + c < N * N := by
  have := Lib.rowMajor_window_le (w := 1) hi hc; simp at this; omega

/-- Reading entry `(i, c)` of a known packed family. -/
theorem extract_P2 {K N i c : Nat} (g : Nat → Nat → BitVec K) (hi : i < N) (hc : c < N) :
    (LVec.ofBitVec (P2 K N g)).extract ((i * N + c) * K) K = .ofBitVec (g i c) := by
  rw [extract_ofBitVec_packBV _ (rm_lt hi hc) rfl, rm_div hc, rm_mod hc]

theorem P2_congr {K N : Nat} {g g' : Nat → Nat → BitVec K} (h : ∀ i e, i < N → e < N → g i e = g' i e) :
    P2 K N g = P2 K N g' :=
  packBV_congr fun u hu => h _ _ (Nat.div_lt_of_lt_mul hu) (Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp at hu
    · exact h0))

/-- `insertEntries` of `a + b` windows: the first `a`, then `b` more. -/
theorem insertEntries_add (K : Nat) (g : Nat → LVec) (x : LVec) (a : Nat) : ∀ b,
    LVec.insertEntries K g (a + b) x =
      (List.range b).foldl (fun acc c => acc.insertAt ((a + c) * K) (g (a + c))) (LVec.insertEntries K g a x)
  | 0 => rfl
  | b + 1 => by
    rw [← Nat.add_assoc, LVec.insertEntries_succ, insertEntries_add K g x a b, List.range_succ, List.foldl_append]
    rfl

theorem foldl_congr_range {α : Type} {f f' : α → Nat → α} {n : Nat} (h : ∀ acc c, c < n → f acc c = f' acc c)
    (x : α) : (List.range n).foldl f x = (List.range n).foldl f' x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (fun acc c hc => h acc c (by omega)),
      List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil, h _ _ (by omega)]

/-- **A slot family writing every entry**: cell `(i, c)` writes `g i c`, the top cell of bank `i` writes
`g i (N-1)`; over any old value of the register's width the result is the packed family. -/
theorem fold_fam {N K : Nat} (hN : 1 ≤ N) (n : String) (cq : Nat → Nat → NbaQueue2) (tq : Nat → NbaQueue2)
    (g : Nat → Nat → BitVec K) (x : LVec) (hx : x.width = N * N * K)
    (hc : ∀ i c y, i < N → c + 1 < N → nbaFold n (cq i c) y = y.insertAt ((i * N + c) * K) (.ofBitVec (g i c)))
    (ht : ∀ i y, i < N → nbaFold n (tq i) y = y.insertAt ((i * N + N - 1) * K) (.ofBitVec (g i (N - 1)))) :
    (List.range N).foldl (fun acc i => nbaFold n (tq i) ((List.range (N - 1)).foldl (fun acc c => nbaFold n (cq i c) acc) acc)) x =
      .ofBitVec (P2 K N g) := by
  have key : ∀ m, m ≤ N → (List.range m).foldl (fun acc i => nbaFold n (tq i)
      ((List.range (N - 1)).foldl (fun acc c => nbaFold n (cq i c) acc) acc)) x =
      LVec.insertEntries K (fun u => .ofBitVec (g (u / N) (u % N))) (m * N) x := by
    intro m
    induction m with
    | zero => intro _; rw [Nat.zero_mul]; rfl
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil,
        foldl_congr_range (fun acc c hc' => hc m c acc (by omega) (by omega)), ht m _ (by omega),
        Nat.succ_mul, show N = N - 1 + 1 by omega, insertEntries_add, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      have e1 : ∀ c, c < N - 1 + 1 → (m * (N - 1 + 1) + c) / (N - 1 + 1) = m := fun c hc => rm_div hc
      have e2 : ∀ c, c < N - 1 + 1 → (m * (N - 1 + 1) + c) % (N - 1 + 1) = c := fun c hc => rm_mod hc
      rw [e1 _ (by omega), e2 _ (by omega), show m * (N - 1 + 1) + (N - 1 + 1) - 1 = m * (N - 1 + 1) + (N - 1) by omega]
      congr 1
      exact foldl_congr_range (fun acc c hc' => by rw [e1 c (by omega), e2 c (by omega)]) _
  rw [key N (Nat.le_refl _), LVec.insertEntries_ofBitVec _ _ hx]

/-- **The units' accumulators**: unit `i` writes `g i`. -/
theorem fold_macs {N K : Nat} (n : String) (q : Nat → NbaQueue2) (g : Nat → BitVec K) (x : LVec)
    (hx : x.width = N * K) (h : ∀ i y, i < N → nbaFold n (q i) y = y.insertAt (i * K) (.ofBitVec (g i))) :
    (List.range N).foldl (fun acc i => nbaFold n (q i) acc) x = .ofBitVec (packBV K N g) := by
  rw [foldl_congr_range (fun acc i hi => h i acc hi), ← LVec.insertEntries_ofBitVec _ _ hx]
  rfl

/-- A family writing nothing to `n`. -/
theorem fold_fam_skip {N : Nat} (n : String) (cq : Nat → Nat → NbaQueue2) (tq : Nat → NbaQueue2) (x : LVec)
    (hc : ∀ i c y, nbaFold n (cq i c) y = y) (ht : ∀ i y, nbaFold n (tq i) y = y) :
    (List.range N).foldl (fun acc i => nbaFold n (tq i) ((List.range (N - 1)).foldl (fun acc c => nbaFold n (cq i c) acc) acc)) x = x := by
  generalize List.range N = l
  induction l generalizing x with
  | nil => rfl
  | cons i l ih => rw [List.foldl_cons, foldl_skip _ _ _ (fun c z => hc i c z), ht, ih]

/-! ### Known control values -/

theorem ofNat32_inj {p q : Nat} (hp : p < 2 ^ 32) (hq : q < 2 ^ 32) : BitVec.ofNat 32 p = BitVec.ofNat 32 q ↔ p = q :=
  ⟨fun h => by have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt hq] at this; exact this, fun h => h ▸ rfl⟩

theorem phB_n32 {p : Nat} {v : Int} (hp : p < 2 ^ 31) (hv0 : 0 ≤ v) (hv : v < 2 ^ 31) :
    phB (n32 p) v = decide ((p : Int) = v) := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat, v = q := ⟨v.toNat, by omega⟩
  simp only [phB, n32, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    LVec.condTrue_ofBitVec, ofNat32_inj (by omega : p < 2 ^ 32) (by omega : q < 2 ^ 32), Int.natCast_inj]
  by_cases h : p = q <;> simp [h]

theorem lastB_n32 {N k : Nat} (hk : k < N) (hN : N < 2 ^ 31) : lastB N (n32 k) = decide (k + 1 = N) := by
  have h1 : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [lastB, n32, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.sub_ofBitVec, h1,
    LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec]
  rw [show (1#32 : BitVec 32) = 1#32 from rfl] at *
  have := Lib.ofNat_eq_ofNat_sub_one_iff (w := 32) hk (by omega)
  by_cases h : k + 1 = N
  · simp [h] at this ⊢; simp [this]
  · simp [h] at this ⊢; simp [this]

theorem add_n32 (k : Nat) : (n32 k).add (LVec.ofInt 32 1) = n32 (k + 1) := by
  have h1 : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  rw [h1, n32, LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]

theorem ofInt_n32 (v : Nat) (hv : v < 2 ^ 31) : LVec.ofInt 32 (v : Int) = n32 v := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem zv_n32 : zv 32 = n32 0 := LVec.replicate_l0 32

theorem wr_width {old v : LVec} (h : v.width = old.width) : old.insertAt 0 (v.resizeU old.width) = v := by
  rw [LVec.insertAt_zero_of_width_eq (by simp [h])]
  have : v = LVec.resizeU v v.width := by
    apply LVec.ext_bits (by simp)
    intro i h1 h2
    simp only [LVec.resizeU, Array.getElem_ofFn]
    have h3 : i < v.bits.size := h1
    rw [Array.getElem?_eq_getElem h3, Option.getD_some]
    rfl
  rw [← h, ← this]

theorem rot_zero {N e : Nat} (he : e < N) : rot N e 0 = e := by simp [rot, he]
theorem rot_succ (N c k : Nat) : rot N (c + 1) k = rot N c (k + 1) := by
  unfold rot; rw [show c + 1 + k = c + (k + 1) by omega]
theorem rot_zero_left {N k : Nat} (hk : k < N) : rot N 0 k = k := by simp [rot, hk]
theorem rot_top {N k : Nat} (hN : 1 ≤ N) (hk : k < N) : rot N (N - 1) (k + 1) = k := by
  unfold rot; rw [if_neg (by omega)]; omega
theorem rot_N {N e : Nat} (he : e < N) : rot N e N = e := by unfold rot; rw [if_neg (by omega)]; omega

/-! ### The queues at a known command -/

section evalq
variable {W AccW u gl rl gsl : Nat} {a bf a0 a1 rb ga gc gs : LVec}

theorem slotQ_idle (ph j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit false) ph j a bf a0 a1 rb ga gc gs = [] := by
  simp [slotQ]
theorem slotQ_start (bz ph j : LVec) (hbz : bz.condTrue = false) :
    slotQ W AccW u gl rl gsl (knownBit true) bz ph j a bf a0 a1 rb ga gc gs =
      [("arr0", u * AccW, ((sxv a AccW (u * W) W).resizeU AccW).resizeU AccW)] := by
  simp [slotQ, hbz]
theorem slotQ_0 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 0) j a bf a0 a1 rb ga gc gs =
      [("rb", u * AccW, (a0.extract (u * AccW) AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_1 (j : Nat) (hj : j < 2 ^ 31) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 1) (n32 j) a bf a0 a1 rb ga gc gs =
      ("grfa", u * W, (bf.extract gl W).resizeU W) ::
        (if j = 0 then [("grfc", u * AccW, (zv AccW).resizeU AccW)]
         else [("grfc", u * AccW, (gs.extract gsl AccW).resizeU AccW)]) := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_2 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 2) j a bf a0 a1 rb ga gc gs =
      [("rb", u * AccW, (rb.extract (rl * AccW) AccW).resizeU AccW), ("grfa", u * W, (ga.extract (rl * W) W).resizeU W)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_3 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 3) j a bf a0 a1 rb ga gc gs =
      [("grfc", u * AccW, (gs.extract gsl AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_4 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 4) j a bf a0 a1 rb ga gc gs =
      [("rb", u * AccW, (a1.extract (u * AccW) AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_5 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 5) j a bf a0 a1 rb ga gc gs =
      [("rb", u * AccW, (gc.extract (u * AccW) AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_6 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 6) j a bf a0 a1 rb ga gc gs =
      [("arr1", u * AccW, (rb.extract (u * AccW) AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
theorem slotQ_7 (j : LVec) :
    slotQ W AccW u gl rl gsl (knownBit false) (knownBit true) (n32 7) j a bf a0 a1 rb ga gc gs =
      [("C", u * AccW, (a1.extract (u * AccW) AccW).resizeU AccW)] := by
  simp (disch := omega) [slotQ, phB_n32]
end evalq

section evalm
variable {N W AccW i : Nat} {rb ga gb : LVec}
theorem macQ_idle (ph : LVec) : macQ N W AccW i (knownBit false) ph rb ga gb = [] := by simp [macQ]
theorem macQ_1 : macQ N W AccW i (knownBit true) (n32 1) rb ga gb = [("grfb", i * AccW, (zv AccW).resizeU AccW)] := by
  simp (disch := omega) [macQ, phB_n32]
theorem macQ_2 : macQ N W AccW i (knownBit true) (n32 2) rb ga gb =
    [("grfb", i * AccW, (macV N W AccW i rb ga gb).resizeU AccW)] := by
  simp (disch := omega) [macQ, phB_n32]
theorem macQ_other {p : Nat} (hp : p < 2 ^ 31) (h1 : p ≠ 1) (h2 : p ≠ 2) :
    macQ N W AccW i (knownBit true) (n32 p) rb ga gb = [] := by
  have h1' : ¬ (p : Int) = 1 := by omega
  have h2' : ¬ (p : Int) = 2 := by omega
  simp (disch := omega) [macQ, phB_n32, h1', h2']
end evalm

/-! ### Values read by one slot -/

theorem ext_u {K N i c : Nat} (g : Nat → Nat → BitVec K) (hi : i < N) (hc : c < N) :
    (LVec.ofBitVec (P2 K N g)).extract ((i * N + c) * K) K = .ofBitVec (g i c) := extract_P2 g hi hc
theorem ext_u1 {K N i c : Nat} (g : Nat → Nat → BitVec K) (hi : i < N) (hc : c + 1 < N) :
    (LVec.ofBitVec (P2 K N g)).extract ((i * N + c + 1) * K) K = .ofBitVec (g i (c + 1)) := by
  rw [show i * N + c + 1 = i * N + (c + 1) by omega]; exact extract_P2 g hi hc
theorem ext_u0 {K N i : Nat} (g : Nat → Nat → BitVec K) (hi : i < N) :
    (LVec.ofBitVec (P2 K N g)).extract (i * N * K) K = .ofBitVec (g i 0) := by
  have := extract_P2 (c := 0) g hi (by omega); rwa [Nat.add_zero] at this
theorem ext_top {K N i : Nat} (g : Nat → Nat → BitVec K) (hN : 1 ≤ N) (hi : i < N) :
    (LVec.ofBitVec (P2 K N g)).extract ((i * N + N - 1) * K) K = .ofBitVec (g i (N - 1)) := by
  rw [show i * N + N - 1 = i * N + (N - 1) by omega]; exact extract_P2 g hi (by omega)
theorem ext_gb {K N i : Nat} (g : Nat → BitVec K) (hi : i < N) :
    (LVec.ofBitVec (packBV K N g)).extract (i * K) K = .ofBitVec (g i) := extract_ofBitVec_packBV g hi rfl

theorem rs_same {w : Nat} (x : BitVec w) : (LVec.ofBitVec x).resizeU w = .ofBitVec x := by
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem nbaFold_hit (n : String) (lo : Nat) (v y : LVec) : nbaFold n [(n, lo, v)] y = y.insertAt lo v := by
  simp [nbaFold]
theorem nbaFold_miss {n n' : String} (h : n' ≠ n) (lo : Nat) (v y : LVec) : nbaFold n [(n', lo, v)] y = y := by
  simp [nbaFold, h]

/-- The host's copy of `B` at column `j`: entry `c·N` is `B[c][j]`. -/
theorem bf_tap {N W : Nat} (B : BitVec (N * N * W)) (j c : Nat) (hc : c < N) :
    (LVec.ofBitVec (bfV N W B j)).extract (c * N * W) W = .ofBitVec (bE N W B c j) := by
  have hb : c * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hc (show 0 < N by omega); simpa using this
  rw [LVec.extract_ofBitVec _ hb, bfV, Lib.extractLsb'_ushiftRight, bE,
    show j * W + c * N * W = (c * N + j) * W by rw [Nat.add_mul, Nat.add_comm]]

theorem bf_shift {N W : Nat} (hW : W < 2 ^ 32) (B : BitVec (N * N * W)) (j : Nat) :
    (LVec.ofBitVec (bfV N W B j)).shr (LVec.ofInt 32 (W : Int)) = .ofBitVec (bfV N W B (j + 1)) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.shr_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW,
    bfV, bfV, ← BitVec.shiftRight_add, Nat.succ_mul]

/-- The host's write of entry `u` of `A`, sign-extended. -/
theorem sx_A {N W AccW u : Nat} (hW : 1 ≤ W) (hu : u < N * N) (A : BitVec (N * N * W)) :
    ((sxv (.ofBitVec A) AccW (u * W) W).resizeU AccW).resizeU AccW = .ofBitVec (sA N W AccW A u) := by
  have h2 : u * W + W ≤ N * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h1 : u * W + W - 1 + 1 ≤ N * N * W := by omega
  simp only [sxv, LVec.extract_ofBitVec _ h1, LVec.extract_ofBitVec _ h2, LVec.concatMany_singleton,
    LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  rw [LVec.ofBitVec_replicate_append_eq_signExtend hW _ _ rfl, LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec,
    BitVec.setWidth_setWidth_of_le _ (Nat.le_refl _), Lib.setWidth_signExtend_of_le _ (by omega), sA]

theorem mac_arith {m n w : Nat} (h : m ≤ n) (g a : BitVec m) (b : BitVec w) :
    (g.setWidth n + a.setWidth n * b.signExtend n).setWidth m = g + a * b.signExtend m := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_mul _ _ h, BitVec.setWidth_setWidth_of_le _ h,
    BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq, BitVec.setWidth_eq, Lib.setWidth_signExtend_of_le _ h]

theorem psum_succ (N W : Nat) (A B : BitVec (N * N * W)) (k i j : Nat) : psum N W A B (k + 1) i j =
    psum N W A B k i j + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem setWidth_neg' {n m : Nat} (h : m ≤ n) (y : BitVec n) : (-y).setWidth m = -(y.setWidth m) := by
  have h1 : (-y).setWidth m + y.setWidth m = 0#m := by
    rw [← BitVec.setWidth_add _ _ h, BitVec.add_left_neg, BitVec.setWidth_zero]
  rw [← BitVec.add_sub_cancel ((-y).setWidth m) (y.setWidth m), h1, BitVec.sub_eq_add_neg, BitVec.zero_add]

theorem setWidth_sub' {n m : Nat} (h : m ≤ n) (x y : BitVec n) :
    (x - y).setWidth m = x.setWidth m - y.setWidth m := by
  rw [BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ h, setWidth_neg' h, ← BitVec.sub_eq_add_neg]

theorem ofInt_sub' {w : Nat} (x y : Int) : BitVec.ofInt w (x - y) = BitVec.ofInt w x - BitVec.ofInt w y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ← BitVec.sub_eq_add_neg]

/-- A negative `b`, sign-extended: its unsigned value minus `2^w`. -/
theorem signExtend_neg_msb {m w : Nat} (b : BitVec w) (hb : b.msb = true) :
    b.signExtend m = b.setWidth m - BitVec.twoPow m w := by
  have ht : BitVec.ofNat m (2 ^ w) = BitVec.twoPow m w := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
  rw [BitVec.signExtend, BitVec.toInt_eq_msb_cond, hb, if_pos rfl, ofInt_sub', BitVec.ofInt_natCast,
    BitVec.ofInt_natCast, BitVec.ofNat_toNat, ht]

/-- **The unit's signed product**: `a·b` with `b` read unsigned, minus `a·2^w` when `b` is negative, computed at
`m + w` bits and truncated to `m`, is the accumulate of `a` times `b` sign-extended. -/
theorem mac_corr {m w : Nat} (g a : BitVec m) (b : BitVec w) (s : BitVec 1) (hs : s = BitVec.ofBool b.msb) :
    ((g.setWidth (m + w) + a.setWidth (m + w) * b.setWidth (m + w)) -
      (((s.replicate m).setWidth (m + w) &&& a.setWidth (m + w)) <<< w)).setWidth m = g + a * b.signExtend m := by
  have h : m ≤ m + w := Nat.le_add_right _ _
  rw [setWidth_sub' h, BitVec.setWidth_add _ _ h, BitVec.setWidth_mul _ _ h, BitVec.setWidth_shiftLeft_of_le h]
  simp only [BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]
  have hand : ((s.replicate m).setWidth (m + w) &&& a.setWidth (m + w)).setWidth m =
      if b.msb then a else 0#m := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    subst hs
    cases hb : b.msb <;> simp [BitVec.getLsbD_replicate, hi, Nat.mod_one, show i < m + w by omega]
  rw [hand]
  cases hb : b.msb
  · simp [BitVec.signExtend_eq_setWidth_of_msb_false hb]
  · simp only [if_true]
    rw [signExtend_neg_msb b hb, BitVec.mul_sub, BitVec.shiftLeft_eq_mul_twoPow, BitVec.sub_eq_add_neg,
      BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- `{{m{1'b0}}, y}` of a known `y` is `y` zero-extended to `m + W` bits. -/
theorem ofBitVec_zeros_append {W : Nat} (y : BitVec W) (m : Nat) :
    LVec.ofBitVec ((0#1).replicate m ++ y) = LVec.ofBitVec (y.setWidth (m + W)) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [Nat.add_comm], fun i hi => ?_⟩
  rw [LVec.getElem?_ofBitVec, if_pos (by simp; omega)]
  congr 2
  rw [BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h : i < W
  · simp [h, show i < m + W by omega]
  · simp [h, BitVec.getLsbD_replicate, BitVec.getLsbD_of_ge y i (by omega)]

/-- `<<` of known vectors (a known shift amount) is `BitVec`'s left shift by the amount's value. -/
theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft]
  by_cases h : i < y.toNat
  · simp [h, hi]
  · simp [h, hi, LVec.getElem?_ofBitVec, show i - y.toNat < w by omega]

theorem b1_false_eq : b1 false = LVec.ofBitVec 0#1 := by decide

/-- **Unit `i`'s multiply-accumulate in read `k` of column `j`.** -/
theorem mac_val {N W AccW : Nat} (hW : 1 ≤ W) (hW32 : W < 2 ^ 32) (A B : BitVec (N * N * W)) {j k i : Nat}
    (hi : i < N) (hk : k < N) :
    (macV N W AccW i (.ofBitVec (rbV N W AccW A k)) (.ofBitVec (gaV N W B j k)) (.ofBitVec (gbV N W AccW A B j k))).resizeU AccW =
      .ofBitVec (BitVec.ofInt AccW (psum N W A B (k + 1) i j)) := by
  have hu : i * N < N * N := by have := rm_lt (c := 0) hi (show 0 < N by omega); simpa using this
  have h2 : i * N * W + W ≤ N * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
  have hga : (gaV N W B j k).extractLsb' (i * N * W) W = bE N W B k j := by
    have := ext_u0 (K := W) (fun _ e => bE N W B (rot N e k) j) hi
    rw [LVec.extract_ofBitVec _ h2] at this
    rw [gaV, LVec.ofBitVec_inj.mp this, rot_zero_left hk]
  have hs : (gaV N W B j k).extractLsb' (i * N * W + W - 1) 1 = BitVec.ofBool (bE N W B k j).msb := by
    rw [extractLsb'_one_eq_ofBool, BitVec.msb_eq_getLsbD_last, ← hga, BitVec.getLsbD_extractLsb',
      show i * N * W + (W - 1) = i * N * W + W - 1 by omega]
    simp [show W - 1 < W by omega]
  unfold macV
  rw [gbV, ext_gb _ hi, rbV, ext_u0 _ hi, rot_zero_left hk]
  simp only [LVec.extract_ofBitVec _ h1, LVec.extract_ofBitVec _ h2, LVec.concatMany_singleton,
    LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec, b1_false_eq]
  rw [ofBitVec_zeros_append, hga, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]
  simp only [LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec, LVec.and_ofBitVec, shl_ofBitVec,
    LVec.sub_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW32]
  rw [mac_corr _ _ _ _ hs, BitVec.setWidth_eq, psum_succ, BitVec.ofInt_add, BitVec.ofInt_mul]
  rfl

/-! ### Value identities -/

theorem rbV_N {N W AccW : Nat} (A : BitVec (N * N * W)) : rbV N W AccW A N = rbV N W AccW A 0 := by
  unfold rbV
  apply P2_congr
  intro _ e _ he
  rw [rot_N he, rot_zero he]

theorem rbV_zero {N W AccW : Nat} (A : BitVec (N * N * W)) : rbV N W AccW A 0 = a0V N W AccW A := by
  unfold rbV a0V
  apply P2_congr
  intro _ e _ he
  rw [rot_zero he]

theorem gbV_zero {N W AccW : Nat} (A B : BitVec (N * N * W)) (j : Nat) :
    gbV N W AccW A B j 0 = packBV AccW N fun _ => 0#AccW := by
  simp [gbV, psum]

theorem product_gcV {N W AccW : Nat} (A B : BitVec (N * N * W)) :
    Tasks.Matmul.product N W AccW A B = gcV N W AccW A B N := by
  rw [show Tasks.Matmul.product N W AccW A B = packBV AccW (N * N) (fun r =>
    BitVec.ofInt AccW (Tasks.Matmul.dot N W A B (r / N) (r % N))) from (packBV_eq_ofNat ..).symm]
  unfold gcV
  apply packBV_congr
  intro u _
  simp [cv, psum, Tasks.Matmul.dot]

/-! ### One busy cycle per command -/

theorem ofInt32_0 : LVec.ofInt 32 0 = n32 0 := by decide
theorem ofInt32_1 : LVec.ofInt 32 1 = n32 1 := by decide
theorem ofInt32_3 : LVec.ofInt 32 3 = n32 3 := by decide
theorem b1_kb (b : Bool) : b1 b = knownBit b := by cases b <;> decide
theorem bvIns_zero {w : Nat} (x y : BitVec w) : bvInsertAt x 0 y = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; rw [getLsbD_bvInsertAt _ _ _ hi]; simp [hi]
theorem add_n32' (k : Nat) : (n32 k).add (n32 1) = n32 (k + 1) := by
  rw [n32, n32, LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]

theorem width_fam {N : Nat} (n : String) (cq : Nat → Nat → NbaQueue2) (tq : Nat → NbaQueue2) (x : LVec) :
    ((List.range N).foldl (fun acc i => nbaFold n (tq i) ((List.range (N - 1)).foldl (fun acc c => nbaFold n (cq i c) acc) acc)) x).width =
      x.width := by
  generalize List.range N = l
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, width_nbaFold]
    generalize List.range (N - 1) = l'
    induction l' generalizing x with
    | nil => rfl
    | cons c l' ih' => rw [List.foldl_cons, ih', width_nbaFold]

set_option hygiene false in
macro "skp" : tactic => `(tactic| (refine fold_fam_skip _ _ _ _ ?_ ?_ <;> intros <;>
  simp (disch := first | omega | simp) [slotQ_0, slotQ_1, slotQ_2, slotQ_3, slotQ_4, slotQ_5, slotQ_6, slotQ_7,
    slotQ_idle, slotQ_start, nbaFold]))

set_option hygiene false in
macro "mskp" : tactic => `(tactic| (refine foldl_skip _ _ _ ?_ _ <;> intros <;>
  simp [macQ_1, macQ_2, macQ_other, macQ_idle, nbaFold]))

set_option hygiene false in
macro "ctl" : tactic => `(tactic| (simp (disch := first | omega | simp [*]) [ctrlQ, bfQ, phB_n32, lastB_n32, nbaFold,
  add_n32, add_n32', bvIns_zero, wr_width, LVec.insertAt_zero_of_width_eq, BitVec.ofNat_add_ofNat, ofInt32_0, ofInt32_1, ofInt32_3, zv_n32, b1_kb, *]))

theorem MS_congr {ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc dn' c' bz' ph' j' k' bf' a0' a1' rb' ga' gb' gc' : LVec}
    (h1 : dn = dn') (h2 : c = c') (h3 : bz = bz') (h4 : ph = ph') (h5 : j = j') (h6 : k = k') (h7 : bf = bf')
    (h8 : a0 = a0') (h9 : a1 = a1') (h10 : rb = rb') (h11 : ga = ga') (h12 : gb = gb') (h13 : gc = gc') :
    MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc = MS ck r s a b dn' c' bz' ph' j' k' bf' a0' a1' rb' ga' gb' gc' := by
  subst_vars; rfl

set_option hygiene false in
macro "step_init" : tactic => `(tactic| (
  rw [mmNext, commit_MS _ _ _ _ _ _ _ _ _ _ _ _ _ _ mmQ_names]
  simp (disch := decide) only [fold_ctrl, fold_bf, fold_gen, fold_grfb, fold_slots]
  refine MS_congr ?e_dn ?e_c ?e_bz ?e_ph ?e_j ?e_k ?e_bf ?e_a0 ?e_a1 ?e_rb ?e_ga ?e_gb ?e_gc))

/-- The range facts the steps use. -/
structure Rng (N W AccW : Nat) : Prop where
  hN : 1 ≤ N
  hW : 1 ≤ W
  hA : 1 ≤ AccW
  hN31 : N < 2 ^ 31
  hW31 : W < 2 ^ 31

/-- `ACT0`: the row buffers open array row 0. -/
theorem step_act0 {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c a1 rb ga gb gc : LVec) (hrb : rb.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 0) (n32 0)
      (n32 0) (.ofBitVec (bfV N W B 0)) (.ofBitVec (a0V N W AccW A)) a1 rb ga gb gc =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 1) (n32 0) (n32 0)
      (.ofBitVec (bfV N W B 0)) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0)) ga gb gc := by
  have hN := h.hN
  have hN31 := h.hN31
  step_init
  all_goals first | (ctl; done) | (skp; done) | (mskp; done) | skip
  refine (fold_fam hN "rb" _ _ (fun i e => sA N W AccW A (i * N + rot N e 0)) rb hrb (fun i c y hi hc => ?_)
    (fun i y hi => ?_)).trans rfl
  · rw [slotQ_0, nbaFold_hit, a0V, ext_u _ hi (by omega), rs_same, rot_zero (by omega)]
  · rw [slotQ_0, nbaFold_hit, a0V, ext_top _ hN hi, rs_same, rot_zero (by omega),
      show i * N + (N - 1) = i * N + N - 1 by omega]

/-- `FILL` of column 0: `grfa` takes column 0 of `B`, `grfb` and `grfc` are cleared. -/
theorem step_fill0 {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c a1 ga gb gc : LVec) (hga : ga.width = N * N * W) (hgb : gb.width = N * AccW)
    (hgc : gc.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 1) (n32 0)
      (n32 0) (.ofBitVec (bfV N W B 0)) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0)) ga gb gc =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 0) (n32 0)
      (.ofBitVec (bfV N W B 1)) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0))
      (.ofBitVec (gaV N W B 0 0)) (.ofBitVec (gbV N W AccW A B 0 0)) (.ofBitVec (gcV N W AccW A B 0)) := by
  have hN := h.hN
  have hN31 := h.hN31
  have hW32 : W < 2 ^ 32 := by have := h.hW31; omega
  have hsh := bf_shift hW32 B 0
  step_init
  case e_ga =>
    refine (fold_fam hN "grfa" _ _ (fun _ e => bE N W B (rot N e 0) 0) ga hga (fun i c y hi hc => ?_)
      (fun i y hi => ?_)).trans rfl
    · rw [slotQ_1 0 (by omega), if_pos rfl]
      simp [nbaFold, bf_tap B 0 c (by omega), rs_same, rot_zero (show c < N by omega)]
    · rw [slotQ_1 0 (by omega), if_pos rfl]
      simp [nbaFold, bf_tap B 0 (N - 1) (by omega), rs_same, rot_zero (show N - 1 < N by omega)]
  case e_gb =>
    refine (fold_macs "grfb" _ (fun _ => 0#AccW) gb hgb (fun i y hi => ?_)).trans (by rw [gbV_zero])
    rw [macQ_1, nbaFold_hit, zv, LVec.replicate_l0, rs_same]
  case e_gc =>
    refine (fold_fam hN "grfc" _ _ (fun i e => if N ≤ e + 0 then cv N W AccW A B i (e + 0 - N) else 0) gc hgc
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_1 0 (by omega), if_pos rfl]
      simp [nbaFold, zv, LVec.replicate_l0, rs_same, show ¬ N ≤ c by omega]
    · rw [slotQ_1 0 (by omega), if_pos rfl]
      simp [nbaFold, zv, LVec.replicate_l0, rs_same, show ¬ N ≤ N - 1 by omega]
  case e_bf => simp [bfQ, nbaFold, hsh, bvIns_zero, phB_n32]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-- `FILL` of column `j + 1`: `grfa` takes the column, `grfb` is cleared, `grfc` shifts the last result in. -/
theorem step_fillS {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {j : Nat} (hj : j + 1 < N)
    (ck a b c a1 ga : LVec) (hga : ga.width = N * N * W) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 1) (n32 (j + 1))
      (n32 0) (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0)) ga
      (.ofBitVec (gbV N W AccW A B j N)) (.ofBitVec (gcV N W AccW A B j)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 (j + 1)) (n32 0)
      (.ofBitVec (bfV N W B (j + 1 + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0))
      (.ofBitVec (gaV N W B (j + 1) 0)) (.ofBitVec (gbV N W AccW A B (j + 1) 0))
      (.ofBitVec (gcV N W AccW A B (j + 1))) := by
  have hN := h.hN
  have hN31 := h.hN31
  have hW32 : W < 2 ^ 32 := by have := h.hW31; omega
  have hsh := bf_shift hW32 B (j + 1)
  have hj0 : ¬ j + 1 = 0 := by omega
  step_init
  case e_ga =>
    refine (fold_fam hN "grfa" _ _ (fun _ e => bE N W B (rot N e 0) (j + 1)) ga hga (fun i c y hi hc => ?_)
      (fun i y hi => ?_)).trans rfl
    · rw [slotQ_1 (j + 1) (by omega), if_neg hj0]
      simp [nbaFold, bf_tap B (j + 1) c (by omega), rs_same, rot_zero (show c < N by omega)]
    · rw [slotQ_1 (j + 1) (by omega), if_neg hj0]
      simp [nbaFold, bf_tap B (j + 1) (N - 1) (by omega), rs_same, rot_zero (show N - 1 < N by omega)]
  case e_gb =>
    refine (fold_macs "grfb" _ (fun _ => 0#AccW) _ (by simp) (fun i y hi => ?_)).trans (by rw [gbV_zero])
    rw [macQ_1, nbaFold_hit, zv, LVec.replicate_l0, rs_same]
  case e_gc =>
    refine (fold_fam hN "grfc" _ _ (fun i e => if N ≤ e + (j + 1) then cv N W AccW A B i (e + (j + 1) - N) else 0) _
      (by simp) (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_1 (j + 1) (by omega), if_neg hj0]
      simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [gcV, ext_u1 _ hi hc, rs_same]
      simp [show c + 1 + j = c + (j + 1) by omega]
    · rw [slotQ_1 (j + 1) (by omega), if_neg hj0]
      simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [gbV, ext_gb _ hi, rs_same]
      simp [cv, show N ≤ N - 1 + (j + 1) by omega, show N - 1 + (j + 1) - N = j by omega]
  case e_bf => simp [bfQ, nbaFold, hsh, bvIns_zero, phB_n32]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

set_option hygiene false in
macro "rd_dp" : tactic => `(tactic| (
  case e_rb =>
    refine (fold_fam hN "rb" _ _ (fun i e => sA N W AccW A (i * N + rot N e (k + 1))) _ (by simp)
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_2]; simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [rbV, ext_u1 _ hi hc, rs_same, rot_succ]; simp
    · rw [slotQ_2]; simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [rbV, ext_u0 _ hi, rs_same, rot_zero_left hk, show i * N + N - 1 = i * N + (N - 1) by omega,
        rot_top hN hk]; simp
  case e_ga =>
    refine (fold_fam hN "grfa" _ _ (fun _ e => bE N W B (rot N e (k + 1)) j) _ (by simp)
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_2]; simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [gaV, ext_u1 _ hi hc, rs_same, rot_succ]; simp
    · rw [slotQ_2]; simp only [nbaFold, List.foldl_cons, List.foldl_nil]
      rw [gaV, ext_u0 _ hi, rs_same, rot_zero_left hk, rot_top hN hk]; simp
  case e_gb =>
    refine (fold_macs "grfb" _ (fun i => BitVec.ofInt AccW (psum N W A B (k + 1) i j)) _ (by simp)
      (fun i y hi => ?_)).trans rfl
    rw [macQ_2, nbaFold_hit, mac_val h.hW (by have := h.hW31; omega) A B hi hk]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)))

/-- A read `RD` with more reads of the column to come. -/
theorem step_rd_mid {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {j k : Nat} (hj : j < N)
    (hk1 : k + 1 < N) (ck a b c a1 : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 j)
      (n32 k) (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A k))
      (.ofBitVec (gaV N W B j k)) (.ofBitVec (gbV N W AccW A B j k)) (.ofBitVec (gcV N W AccW A B j)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 j) (n32 (k + 1))
      (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A (k + 1)))
      (.ofBitVec (gaV N W B j (k + 1))) (.ofBitVec (gbV N W AccW A B j (k + 1))) (.ofBitVec (gcV N W AccW A B j)) := by
  have hN := h.hN
  have hN31 := h.hN31
  have hk : k < N := by omega
  have hne : ¬ k + 1 = N := by omega
  step_init
  rd_dp

/-- The last read of column `j < N - 1`: on to the next `FILL`. -/
theorem step_rd_wrap {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {j k : Nat} (hj1 : j + 1 < N)
    (hk1 : k + 1 = N) (ck a b c a1 : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 j)
      (n32 k) (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A k))
      (.ofBitVec (gaV N W B j k)) (.ofBitVec (gbV N W AccW A B j k)) (.ofBitVec (gcV N W AccW A B j)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 1) (n32 (j + 1)) (n32 0)
      (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A (k + 1)))
      (.ofBitVec (gaV N W B j (k + 1))) (.ofBitVec (gbV N W AccW A B j (k + 1))) (.ofBitVec (gcV N W AccW A B j)) := by
  have hN := h.hN
  have hN31 := h.hN31
  have hk : k < N := by omega
  have hj : j < N := by omega
  have hne : ¬ j + 1 = N := by omega
  step_init
  rd_dp

/-- The last read of the last column: on to `LAST`. -/
theorem step_rd_end {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {j k : Nat} (hj1 : j + 1 = N)
    (hk1 : k + 1 = N) (ck a b c a1 : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 2) (n32 j)
      (n32 k) (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A k))
      (.ofBitVec (gaV N W B j k)) (.ofBitVec (gbV N W AccW A B j k)) (.ofBitVec (gcV N W AccW A B j)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 3) (n32 j) (n32 0)
      (.ofBitVec (bfV N W B (j + 1))) (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A (k + 1)))
      (.ofBitVec (gaV N W B j (k + 1))) (.ofBitVec (gbV N W AccW A B j (k + 1))) (.ofBitVec (gcV N W AccW A B j)) := by
  have hN := h.hN
  have hN31 := h.hN31
  have hk : k < N := by omega
  have hj : j < N := by omega
  step_init
  rd_dp

/-- `LAST`: the last result enters the result registers. -/
theorem step_last {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c bf a1 rb ga : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 3) (n32 (N - 1))
      (n32 0) bf (.ofBitVec (a0V N W AccW A)) a1 rb ga (.ofBitVec (gbV N W AccW A B (N - 1) N))
      (.ofBitVec (gcV N W AccW A B (N - 1))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 4) (n32 (N - 1)) (n32 0)
      bf (.ofBitVec (a0V N W AccW A)) a1 rb ga (.ofBitVec (gbV N W AccW A B (N - 1) N))
      (.ofBitVec (gcV N W AccW A B N)) := by
  have hN := h.hN
  have hN31 := h.hN31
  step_init
  case e_gc =>
    refine (fold_fam hN "grfc" _ _ (fun i e => if N ≤ e + N then cv N W AccW A B i (e + N - N) else 0) _
      (by simp) (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_3, nbaFold_hit, gcV, ext_u1 _ hi hc, rs_same, show c + 1 + (N - 1) = c + N by omega]
    · rw [slotQ_3, nbaFold_hit, gbV, ext_gb _ hi, rs_same]
      simp [cv, show N ≤ N - 1 + N by omega, show N - 1 + N - N = N - 1 by omega]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-- `ACT1`: the row buffers open array row 1 (whose old contents are not used). -/
theorem step_act1 {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c bf a1 rb ga gb : LVec) (hrb : rb.width = N * N * AccW) : ∃ rb', rb'.width = N * N * AccW ∧
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 4) (n32 (N - 1))
      (n32 0) bf (.ofBitVec (a0V N W AccW A)) a1 rb ga gb (.ofBitVec (gcV N W AccW A B N)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 5) (n32 (N - 1)) (n32 0)
      bf (.ofBitVec (a0V N W AccW A)) a1 rb' ga gb (.ofBitVec (gcV N W AccW A B N)) := by
  have hN := h.hN
  have hN31 := h.hN31
  refine ⟨?rb', ?hw, ?heq⟩
  case heq =>
    step_init
    case e_rb => rfl
    all_goals first | (ctl; done) | (skp; done) | (mskp; done)
  case hw => rw [width_fam, hrb]

/-- `WR`: the results are written into the open row. -/
theorem step_wr {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c bf a1 rb ga gb : LVec) (hrb : rb.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 5) (n32 (N - 1))
      (n32 0) bf (.ofBitVec (a0V N W AccW A)) a1 rb ga gb (.ofBitVec (gcV N W AccW A B N)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 6) (n32 (N - 1)) (n32 0)
      bf (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (gcV N W AccW A B N)) ga gb (.ofBitVec (gcV N W AccW A B N)) := by
  have hN := h.hN
  have hN31 := h.hN31
  step_init
  case e_rb =>
    refine (fold_fam hN "rb" _ _ (fun i e => if N ≤ e + N then cv N W AccW A B i (e + N - N) else 0) rb hrb
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_5, nbaFold_hit, gcV, ext_u _ hi (by omega), rs_same]
    · rw [slotQ_5, nbaFold_hit, gcV, ext_top _ hN hi, rs_same]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-- `PRE`: the open row is written back into array row 1. -/
theorem step_pre {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c bf a1 ga gb : LVec) (ha1 : a1.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 6) (n32 (N - 1))
      (n32 0) bf (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (gcV N W AccW A B N)) ga gb (.ofBitVec (gcV N W AccW A B N)) =
    MS ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 7) (n32 (N - 1)) (n32 0)
      bf (.ofBitVec (a0V N W AccW A)) (.ofBitVec (gcV N W AccW A B N)) (.ofBitVec (gcV N W AccW A B N)) ga gb
      (.ofBitVec (gcV N W AccW A B N)) := by
  have hN := h.hN
  have hN31 := h.hN31
  step_init
  case e_a1 =>
    refine (fold_fam hN "arr1" _ _ (fun i e => if N ≤ e + N then cv N W AccW A B i (e + N - N) else 0) a1 ha1
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_6, nbaFold_hit, gcV, ext_u _ hi (by omega), rs_same]
    · rw [slotQ_6, nbaFold_hit, gcV, ext_top _ hN hi, rs_same]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-- `READ`: the host reads array row 1 of every bank into `C`; `done`. -/
theorem step_read {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck a b c bf rb ga gb gc : LVec) (hc : c.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (knownBit true) (n32 7) (n32 (N - 1))
      (n32 0) bf (.ofBitVec (a0V N W AccW A)) (.ofBitVec (gcV N W AccW A B N)) rb ga gb gc =
    MS ck (knownBit false) (knownBit false) a b (knownBit true) (.ofBitVec (gcV N W AccW A B N)) (knownBit false)
      (n32 7) (n32 (N - 1)) (n32 0) bf (.ofBitVec (a0V N W AccW A)) (.ofBitVec (gcV N W AccW A B N)) rb ga gb gc := by
  have hN := h.hN
  have hN31 := h.hN31
  step_init
  case e_c =>
    refine (fold_fam hN "C" _ _ (fun i e => if N ≤ e + N then cv N W AccW A B i (e + N - N) else 0) c hc
      (fun i c y hi hc => ?_) (fun i y hi => ?_)).trans rfl
    · rw [slotQ_7, nbaFold_hit, gcV, ext_u _ hi (by omega), rs_same]
    · rw [slotQ_7, nbaFold_hit, gcV, ext_top _ hN hi, rs_same]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-! ### Start, reset, idle -/

/-- A start from an idle state (`busy` = 0): the host writes `A` into array row 0 and `B` into `bf`. -/
theorem next_start {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W))
    (ck dn c ph j k bf a0 a1 rb ga gb gc : LVec) (hdn : dn.width = 1) (hph : ph.width = 32) (hj : j.width = 32)
    (hk : k.width = 32) (hbf : bf.width = N * N * W) (ha0 : a0.width = N * N * AccW) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c (knownBit false) ph j k bf a0
      a1 rb ga gb gc =
    MS ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) (knownBit false) c (knownBit true) (n32 0)
      (n32 0) (n32 0) (.ofBitVec (bfV N W B 0)) (.ofBitVec (a0V N W AccW A)) a1 rb ga gb gc := by
  have hN := h.hN
  have hN31 := h.hN31
  have hb0 : bfV N W B 0 = B := by simp [bfV]
  step_init
  case e_a0 =>
    refine (fold_fam hN "arr0" _ _ (fun i e => sA N W AccW A (i * N + e)) a0 ha0 (fun i c y hi hc => ?_)
      (fun i y hi => ?_)).trans rfl
    · rw [slotQ_start _ _ _ (by simp), nbaFold_hit, sx_A h.hW (rm_lt hi (by omega))]
    · rw [slotQ_start _ _ _ (by simp), nbaFold_hit, sx_A h.hW (by have := rm_lt hi (show N - 1 < N by omega); omega),
        show i * N + (N - 1) = i * N + N - 1 by omega]
  case e_bf => simp [bfQ, nbaFold, hb0, LVec.insertAt_zero_of_width_eq, hbf]
  all_goals first | (ctl; done) | (skp; done) | (mskp; done)

/-- A reset cycle clears `busy` and `done`. -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) (hdn : dn.width = 1)
    (hbz : bz.width = 1) : ∃ c' ph' j' k' bf' a0' a1' rb' ga' gb' gc',
    mmNext N W AccW ck (knownBit true) s a b dn c bz ph j k bf a0 a1 rb ga gb gc =
      MS ck (knownBit true) s a b (knownBit false) c' (knownBit false) ph' j' k' bf' a0' a1' rb' ga' gb' gc' := by
  rw [mmNext, commit_MS _ _ _ _ _ _ _ _ _ _ _ _ _ _ mmQ_names]
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, MS_congr ?_ rfl ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩
  · rw [fold_ctrl "done" (by decide) (by decide) (by decide)]
    simp [ctrlQ, nbaFold, b1_kb, LVec.insertAt_zero_of_width_eq, hdn]
  · rw [fold_ctrl "busy" (by decide) (by decide) (by decide)]
    simp [ctrlQ, nbaFold, b1_kb, LVec.insertAt_zero_of_width_eq, hbz]

/-- A cycle without `rst` and `start` from an idle state changes no register. -/
theorem next_idle {N W AccW : Nat} (ck a b dn c ph j k bf a0 a1 rb ga gb gc : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c (knownBit false) ph j k bf a0 a1 rb ga gb gc =
      MS ck (knownBit false) (knownBit false) a b dn c (knownBit false) ph j k bf a0 a1 rb ga gb gc := by
  have : mmQ N W AccW (knownBit false) (knownBit false) b dn (knownBit false) ph j k a bf a0 a1 rb ga gb gc = [] := by
    simp [mmQ, ctrlQ, bfQ, genQ, macQ_idle, slotQ_idle]
  rw [mmNext, this, commitNba2_nil]

/-! ## 5. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c bz ph j k bf a0 a1 rb ga gb gc : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ bz.width = 1 ∧ ph.width = 32 ∧ j.width = 32 ∧ k.width = 32 ∧
    bf.width = N * N * W ∧ a0.width = N * N * AccW ∧ a1.width = N * N * AccW ∧ rb.width = N * N * AccW ∧
    ga.width = N * N * W ∧ gb.width = N * AccW ∧ gc.width = N * N * AccW

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, st = MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc ∧
    Wd N W AccW dn c bz ph j k bf a0 a1 rb ga gb gc

/-- **Every cycle keeps the design's shape.** -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc : LVec)
    (hw : Wd N W AccW dn c bz ph j k bf a0 a1 rb ga gb gc) :
    I N W AccW (mmNext N W AccW ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc) := by
  rw [mmNext, commit_MS _ _ _ _ _ _ _ _ _ _ _ _ _ _ mmQ_names]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, width_nbaFold, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, ctrlP, bfP, genPs, bankPs, macP, slotP, mv, nb, sext, List.any_flatMap, List.any_map,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 1, .xVec 32, .xVec 32, .xVec 32, .xVec (N * N * W), .xVec (N * N * AccW), .xVec (N * N * AccW),
    .xVec (N * N * AccW), .xVec (N * N * W), .xVec (N * AccW), .xVec (N * N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

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
  obtain ⟨bz, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨ph, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨j, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨k, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨bf, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨a0, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨a1, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨rb, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain ⟨ga, r16, rfl, w16, -, h16⟩ := powerUp_cons.mp h15
  obtain ⟨gb, r17, rfl, w17, -, h17⟩ := powerUp_cons.mp h16
  obtain ⟨gc, r18, rfl, w18, -, h18⟩ := powerUp_cons.mp h17
  obtain rfl := powerUp_nil.mp h18
  exact ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18⟩

/-- **Termination from every power-up.** -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA) (fun σ => ⟨40, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc kk 40 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c bz ph j k bf a0 a1 rb ga gb gc hw⟩

/-! ## 6. The protocol: the phases -/

theorem MS_inj {ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc ck' r' s' a' b' dn' c' bz' ph' j' k' bf' a0' a1' rb' ga' gb'
    gc' : LVec}
    (h : MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc = MS ck' r' s' a' b' dn' c' bz' ph' j' k' bf' a0' a1' rb' ga' gb' gc') :
    dn = dn' ∧ c = c' ∧ bz = bz' ∧ ph = ph' ∧ j = j' ∧ k = k' ∧ bf = bf' ∧ a0 = a0' ∧ a1 = a1' ∧ rb = rb' ∧ ga = ga' ∧
      gb = gb' ∧ gc = gc' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

section phases
variable (N W AccW : Nat) (A B : BitVec (N * N * W))

def AtAct0 (st : SvState) : Prop := ∃ ck r s a b c a1 rb ga gb gc, c.width = N * N * AccW ∧ a1.width = N * N * AccW ∧
  rb.width = N * N * AccW ∧ ga.width = N * N * W ∧ gb.width = N * AccW ∧ gc.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 0) (n32 0) (n32 0) (.ofBitVec (bfV N W B 0))
    (.ofBitVec (a0V N W AccW A)) a1 rb ga gb gc

def AtFill (j : Nat) (st : SvState) : Prop := ∃ ck r s a b c a1 ga gb gc, c.width = N * N * AccW ∧
  a1.width = N * N * AccW ∧ ga.width = N * N * W ∧ gb.width = N * AccW ∧ gc.width = N * N * AccW ∧
  (0 < j → gb = .ofBitVec (gbV N W AccW A B (j - 1) N) ∧ gc = .ofBitVec (gcV N W AccW A B (j - 1))) ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 1) (n32 j) (n32 0) (.ofBitVec (bfV N W B j))
    (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A 0)) ga gb gc

def AtRd (j k : Nat) (st : SvState) : Prop := ∃ ck r s a b c a1, c.width = N * N * AccW ∧ a1.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 2) (n32 j) (n32 k) (.ofBitVec (bfV N W B (j + 1)))
    (.ofBitVec (a0V N W AccW A)) a1 (.ofBitVec (rbV N W AccW A k)) (.ofBitVec (gaV N W B j k))
    (.ofBitVec (gbV N W AccW A B j k)) (.ofBitVec (gcV N W AccW A B j))

def AtLast (st : SvState) : Prop := ∃ ck r s a b c bf a1 rb ga, c.width = N * N * AccW ∧ a1.width = N * N * AccW ∧
  rb.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 3) (n32 (N - 1)) (n32 0) bf (.ofBitVec (a0V N W AccW A))
    a1 rb ga (.ofBitVec (gbV N W AccW A B (N - 1) N)) (.ofBitVec (gcV N W AccW A B (N - 1)))

def AtTail (p : Nat) (st : SvState) : Prop := ∃ ck r s a b c bf a1 rb ga gb, c.width = N * N * AccW ∧
  a1.width = N * N * AccW ∧ rb.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 p) (n32 (N - 1)) (n32 0) bf (.ofBitVec (a0V N W AccW A))
    a1 rb ga gb (.ofBitVec (gcV N W AccW A B N))

def AtPre (st : SvState) : Prop := ∃ ck r s a b c bf a1 ga gb, c.width = N * N * AccW ∧ a1.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 6) (n32 (N - 1)) (n32 0) bf (.ofBitVec (a0V N W AccW A))
    a1 (.ofBitVec (gcV N W AccW A B N)) ga gb (.ofBitVec (gcV N W AccW A B N))

def AtRead (st : SvState) : Prop := ∃ ck r s a b c bf rb ga gb gc, c.width = N * N * AccW ∧
  st = MS ck r s a b (knownBit false) c (knownBit true) (n32 7) (n32 (N - 1)) (n32 0) bf (.ofBitVec (a0V N W AccW A))
    (.ofBitVec (gcV N W AccW A B N)) rb ga gb gc

/-- The busy states, `m` cycles before `done` shows at the latest. -/
def BusyAt (m : Nat) (st : SvState) : Prop :=
  (m + 1 = lat N W AccW ∧ AtAct0 N W AccW A B st) ∨
  (∃ j, j < N ∧ m + 2 + j * (N + 1) = lat N W AccW ∧ AtFill N W AccW A B j st) ∨
  (∃ j k, j < N ∧ k < N ∧ m + 3 + j * (N + 1) + k = lat N W AccW ∧ AtRd N W AccW A B j k st) ∨
  (m + 2 + N * (N + 1) = lat N W AccW ∧ AtLast N W AccW A B st) ∨
  (m + 3 + N * (N + 1) = lat N W AccW ∧ AtTail N W AccW A B 4 st) ∨
  (m + 4 + N * (N + 1) = lat N W AccW ∧ AtTail N W AccW A B 5 st) ∨
  (m + 5 + N * (N + 1) = lat N W AccW ∧ AtPre N W AccW A B st) ∨
  (m + 6 + N * (N + 1) = lat N W AccW ∧ AtRead N W AccW A B st)

/-- Finished: `done` = 1 and `C` the product. -/
def FinAt (st : SvState) : Prop := ∃ ck r s a b bz ph j k bf a0 a1 rb ga gb gc, bz = knownBit false ∧
  st = MS ck r s a b (knownBit true) (.ofBitVec (Tasks.Matmul.product N W AccW A B)) bz ph j k bf a0 a1 rb ga gb gc

end phases

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc, prev = MS ck r s a b dn c bz ph j k bf a0 a1 rb ga gb gc ∧
    Wd N W AccW dn c bz ph j k bf a0 a1 rb ga gb gc ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
      dn c bz ph j k bf a0 a1 rb ga gb gc

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

theorem lat_eq (N W AccW : Nat) : lat N W AccW = N * (N + 1) + 6 := by
  rw [lat, Nat.mul_succ]

/-- **One busy cycle**: from `BusyAt m`, the next state is finished or `BusyAt m'` with `m' < m`. -/
theorem busy_step {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {m : Nat} {ck a b ck0 r0 s0 aa bb : LVec}
    {dn c bz ph j k bf a0 a1 rb ga gb gc : LVec}
    (hB : BusyAt N W AccW A B m (MS ck0 r0 s0 aa bb dn c bz ph j k bf a0 a1 rb ga gb gc)) :
    FinAt N W AccW A B (mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c bz ph j k bf a0 a1 rb ga gb gc) ∨
    ∃ m', m' < m ∧ BusyAt N W AccW A B m'
      (mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c bz ph j k bf a0 a1 rb ga gb gc) := by
  have hN := h.hN
  have hl := lat_eq N W AccW
  rcases hB with ⟨hm, ck', r', s', a', b', c', a1', rb', ga', gb', gc', w1, w2, w3, w4, w5, w6, hs⟩ |
    ⟨jj, hjj, hm, ck', r', s', a', b', c', a1', ga', gb', gc', w1, w2, w4, w5, w6, hjg, hs⟩ |
    ⟨jj, kk, hjj, hkk, hm, ck', r', s', a', b', c', a1', w1, w2, hs⟩ |
    ⟨hm, ck', r', s', a', b', c', bf', a1', rb', ga', w1, w2, w3, hs⟩ |
    ⟨hm, ck', r', s', a', b', c', bf', a1', rb', ga', gb', w1, w2, w3, hs⟩ |
    ⟨hm, ck', r', s', a', b', c', bf', a1', rb', ga', gb', w1, w2, w3, hs⟩ |
    ⟨hm, ck', r', s', a', b', c', bf', a1', ga', gb', w1, w2, hs⟩ |
    ⟨hm, ck', r', s', a', b', c', bf', rb', ga', gb', gc', w1, hs⟩ <;>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hs
  · -- ACT0
    rw [step_act0 h A B _ _ _ _ _ _ _ _ _ w3]
    exact .inr ⟨m - 1, by omega, .inr (.inl ⟨0, by omega, by omega, _, _, _, _, _, _, _, _, _, _, w1, w2, w4, w5,
      w6, by simp, rfl⟩)⟩
  · -- FILL
    have hle : jj * (N + 1) + (N + 1) ≤ N * (N + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hjj
    rcases Nat.eq_zero_or_pos jj with rfl | hpos
    · rw [step_fill0 h A B _ _ _ _ _ _ _ _ w4 w5 w6]
      exact .inr ⟨m - 1, by omega, .inr (.inr (.inl ⟨0, 0, by omega, by omega, by simp at hm ⊢; omega, _, _, _, _, _,
        _, _, w1, w2, rfl⟩))⟩
    · obtain ⟨j', rfl⟩ : ∃ j', jj = j' + 1 := ⟨jj - 1, by omega⟩
      obtain ⟨rfl, rfl⟩ := hjg hpos
      simp only [Nat.add_sub_cancel] 
      rw [step_fillS h A B hjj _ _ _ _ _ _ w4]
      exact .inr ⟨m - 1, by omega, .inr (.inr (.inl ⟨j' + 1, 0, hjj, by omega, by omega, _, _, _, _, _, _, _, w1, w2,
        rfl⟩))⟩
  · -- RD
    have hle : jj * (N + 1) + (N + 1) ≤ N * (N + 1) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hjj
    rcases Nat.lt_or_ge (kk + 1) N with hk1 | hk1
    · rw [step_rd_mid h A B hjj hk1]
      exact .inr ⟨m - 1, by omega, .inr (.inr (.inl ⟨jj, kk + 1, hjj, hk1, by omega, _, _, _, _, _, _, _, w1, w2,
        rfl⟩))⟩
    · have hk1 : kk + 1 = N := by omega
      rcases Nat.lt_or_ge (jj + 1) N with hj1 | hj1
      · rw [step_rd_wrap h A B hj1 hk1]
        have hs1 : (jj + 1) * (N + 1) = jj * (N + 1) + (N + 1) := Nat.succ_mul _ _
        refine .inr ⟨m - 1, by omega, .inr (.inl ⟨jj + 1, hj1, by omega, ck, knownBit false, knownBit false, a, b, c, a1,
          .ofBitVec (gaV N W B jj (kk + 1)), .ofBitVec (gbV N W AccW A B jj (kk + 1)), .ofBitVec (gcV N W AccW A B jj),
          w1, w2, by simp, by simp, by simp, fun _ => ⟨by simp [hk1], by simp⟩, ?_⟩)⟩
        rw [hk1, rbV_N]
      · have hj1 : jj + 1 = N := by omega
        rw [step_rd_end h A B hj1 hk1]
        have hs1 : (jj + 1) * (N + 1) = jj * (N + 1) + (N + 1) := Nat.succ_mul _ _
        have hjN : jj = N - 1 := by omega
        subst hjN
        refine .inr ⟨m - 1, by rw [hj1] at hs1; omega, .inr (.inr (.inr (.inl ⟨by rw [hj1] at hs1; omega, ck, knownBit false,
          knownBit false, a, b, c, .ofBitVec (bfV N W B (N - 1 + 1)), a1, .ofBitVec (rbV N W AccW A (kk + 1)), .ofBitVec (gaV N W B (N - 1) (kk + 1)), w1, w2,
          by simp, ?_⟩)))⟩
        rw [hk1]
  · -- LAST
    rw [step_last h A B]
    exact .inr ⟨m - 1, by omega, .inr (.inr (.inr (.inr (.inl ⟨by omega, _, _, _, _, _, _, _, _, _, _, _, w1, w2, w3,
      rfl⟩))))⟩
  · -- ACT1
    obtain ⟨rb'', hw, he⟩ := step_act1 h A B ck a b c bf a1 rb ga gb w3
    rw [he]
    exact .inr ⟨m - 1, by omega, .inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, _, _, _, _, _, _, _, _, _, _, _, w1, w2,
      hw, rfl⟩)))))⟩
  · -- WR
    rw [step_wr h A B _ _ _ _ _ _ _ _ _ w3]
    exact .inr ⟨m - 1, by omega, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, _, _, _, _, _, _, _, _, _, _, w1,
      w2, rfl⟩))))))⟩
  · -- PRE
    rw [step_pre h A B _ _ _ _ _ _ _ _ w2]
    exact .inr ⟨m - 1, by omega, .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, _, _, _, _, _, _, _, _, _, _, _,
      w1, rfl⟩))))))⟩
  · -- READ
    rw [step_read h A B _ _ _ _ _ _ _ _ _ w1]
    exact .inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by rw [product_gcV]⟩

/-- **The phase model** at `(N, W, AccW)`, latency `N² + N + 6`. -/
def model (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (lat N W AccW) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW h.hN h.hW h.hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, bz, ph, j, kk, bf, a0, a1, rb, ga, gb, gc, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, bz, ph, j, kk, bf, a0, a1, rb, ga, gb, gc, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW h.hN h.hW h.hA σ e ck r s a b dn c bz ph j kk bf a0 a1 rb ga gb gc k 40 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c bz ph j k bf a0 a1 rb ga gb gc hw
  Ready st := ∃ ck r s a b c ph j k bf a0 a1 rb ga gb gc,
    st = MS ck r s a b (knownBit false) c (knownBit false) ph j k bf a0 a1 rb ga gb gc
  Busy x m st := BusyAt N W AccW x.1 x.2.1 m st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st (⟨-, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, rfl⟩ |
      ⟨_, -, -, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, rfl⟩ | ⟨_, _, -, -, -, _, _, _, _, _, _, _, -, -, rfl⟩ |
      ⟨-, _, _, _, _, _, _, _, _, _, _, -, -, -, rfl⟩ | ⟨-, _, _, _, _, _, _, _, _, _, _, _, -, -, -, rfl⟩ |
      ⟨-, _, _, _, _, _, _, _, _, _, _, _, -, -, -, rfl⟩ | ⟨-, _, _, _, _, _, _, _, _, _, _, -, -, rfl⟩ |
      ⟨-, _, _, _, _, _, _, _, _, _, _, _, -, rfl⟩) <;>
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, -, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', ph', j', k', bf', a0', a1', rb', ga', gb', gc', he⟩ := next_reset (N := N) (W := W) (AccW := AccW)
      (appIn e "clk" ck) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn c bz ph j k bf a0 a1 rb ga gb gc
      hw.1 hw.2.2.1
    rw [he]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, hw, rfl⟩ hprev hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    have hbz : bz = knownBit false := by
      rcases hprev with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, he⟩
      · exact (MS_inj he).2.2.1
      · rw [(MS_inj he).2.2.1, hb0]
    subst hbz
    obtain ⟨w1, w2, -, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ := hw
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb,
      next_start h x.1 x.2.1 _ dn c ph j k bf a0 a1 rb ga gb gc w1 w4 w5 w6 w7 w8]
    refine .inr ⟨lat N W AccW - 1, by simp [lat], .inl ⟨by simp [lat], _, _, _, _, _, _, _, _, _, _, _, w2, w9, w10, w11,
      w12, w13, rfl⟩⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, -, rfl⟩ hB hr hs -
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    exact busy_step h x.1 x.2.1 hB
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, -, rfl⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, he⟩ hr hs
    obtain ⟨rfl, -, rfl, -⟩ := MS_inj he
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, bz, ph, j, k, bf, a0, a1, rb, ga, gb, gc, rfl, -, rfl⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb0, he⟩ hr hs
    obtain ⟨rfl, rfl, rfl, -⟩ := MS_inj he
    subst hb0
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl⟩

/-! ## 7. txtask-v2's rules, and the statement -/

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "busy", "ph", "j", "k", "bf", "arr0", "arr1", "rb", "grfa",
      "grfb", "grfc"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_mem hp with rfl | rfl | ⟨i, rfl⟩ | ⟨i, c0, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, bfP, macP, slotP, mv, nb, c32, eqE, sext, edgeClock, asyncReset, processDataNames,
      stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-- **Rule 1.** -/
theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW hN hW hA)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem ctrl_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (ctrlP N) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ctrlP, nb, c32, eqE, b1, mmD, mmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem bf_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (bfP W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, bfP, c32, eqE, mmD, mmDecls, LVec.ofInt]

theorem b1_width (b : Bool) : (b1 b).width = 1 := rfl
theorem b1_known (b : Bool) : (b1 b).allKnown = true := by
  cases b
  · exact lvec_l0_known
  · exact lvec_l1_known

theorem mac_xsafe {N W AccW i : Nat} (hW : 1 ≤ W) (hi : i < N) : xsProc (mmD N W AccW) (macP N W AccW i) = true := by
  have hu : i * N < N * N := by have := rm_lt (c := 0) hi (show 0 < N by omega); simpa using this
  have h1 : i * AccW + AccW ≤ N * AccW := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
  have h2 : i * N * AccW + AccW ≤ N * N * AccW := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h3 : i * N * W + W ≤ N * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h4 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, macP, sext, c32, eqE, mmD,
    mmDecls, LVec.replicate_l0, LVec.ofInt, b1_width, b1_known, h1, h2, h3, h4]

theorem slot_xsafe {N W AccW u gl rl gsl : Nat} {gs : String} (hW : 1 ≤ W) (hu : u < N * N) (hrl : rl < N * N)
    (hgl : gl + W ≤ N * N * W)
    (hgs : (gs = "grfc" ∧ gsl + AccW ≤ N * N * AccW) ∨ (gs = "grfb" ∧ gsl + AccW ≤ N * AccW)) :
    xsProc (mmD N W AccW) (slotP W AccW u gl rl gs gsl) = true := by
  have h1 : u * AccW + AccW ≤ N * N * AccW := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h2 : u * W + W ≤ N * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hu
  have h3 : u * W + W - 1 + 1 ≤ N * N * W := by omega
  have h4 : rl * AccW + AccW ≤ N * N * AccW := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hrl
  have h5 : rl * W + W ≤ N * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hrl
  rcases hgs with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ <;>
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, slotP, mv, sext, c32, eqE, mmD,
    mmDecls, LVec.replicate_l0, LVec.ofInt, h1, h2, h3, h4, h5, hgl, hg]

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hp' : p ∈ ctrlP N :: bfP W :: genPs N W AccW := by simpa [mmD] using hp
  rcases List.mem_cons.mp hp' with rfl | hp'
  · exact ctrl_xsafe N W AccW
  rcases List.mem_cons.mp hp' with rfl | hp'
  · exact bf_xsafe N W AccW
  simp only [genPs, List.mem_flatMap, List.mem_range, bankPs, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_singleton, List.mem_nil_iff, or_false] at hp'
  obtain ⟨i, hi, rfl | ⟨c0, hc0, rfl⟩ | rfl⟩ := hp'
  · exact mac_xsafe hW hi
  · exact slot_xsafe hW (rm_lt hi (by omega)) (by rw [Nat.add_assoc]; exact rm_lt hi (by omega))
      (by have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) (show c0 < N by omega) (show 0 < N by omega)
          simpa using this)
      (.inl ⟨rfl, by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by rw [Nat.add_assoc]; exact rm_lt hi (by omega))⟩)
  · exact slot_xsafe hW (by have := rm_lt hi (show N - 1 < N by omega); omega)
      (by have := rm_lt (c := 0) hi (show 0 < N by omega); simpa using this)
      (by have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) (show N - 1 < N by omega) (show 0 < N by omega)
          simpa using this)
      (.inr ⟨rfl, by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi⟩)

/-- **The design satisfies the matmul statement (txtask-v2) at latency `N² + N + 6`** (`26` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  have hN : 1 ≤ N := hN
  have hW : 1 ≤ W := hW
  have hA : 1 ≤ AccW := hA
  have hNW' : N * N * W < 2 ^ 31 := hNW
  have h : Rng N W AccW := ⟨hN, hW, hA, by
      have := Nat.le_mul_of_pos_right N (Nat.mul_pos hN hW)
      have : N ≤ N * N * W := by rw [Nat.mul_assoc]; exact this
      omega, by
      have := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
      omega⟩
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA)
    (mm_disciplined N W AccW hN hW hA) (mm_terminatesPU N W AccW hN hW hA) (by simp [lat])
    (model N W AccW h) (mm_powerUp N W AccW hN hW hA) (mm_moore N W AccW hN hW hA)
    (mm_xsafe N W AccW hN hW hA)

end Submission
