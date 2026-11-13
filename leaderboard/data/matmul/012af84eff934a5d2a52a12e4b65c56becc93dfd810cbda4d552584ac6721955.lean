-- svgolf-latency: 16
import Submission.Design
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.NbaCommit
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.BitVecArith
import LeanModels.Sv.CombViewArith
import LeanModels.Sv.Mono2
import SvGolf.SeqV2

/-!
# A weight-stationary systolic matrix unit (task `matmul`), proved for every `(N, W, AccW)`

`solution.sv`: a weight FIFO `wf`, shadow weights `wsh` loaded by shifting them down the array, a swap
into the active weights `wac` at step `N` (sign-extended to `AccW` bits), a unified buffer `ub` feeding a
triangle of data rows `dat` (entries sign-extended to `AccW` bits)
(row `k` has `k` delay stages and the `N` PE data registers), partial sums `ps` moving down the columns,
and per-column rotating accumulators `C` below the array. `done` shows `4N` snapshots after the start's.

1. **Agreement** (`tp_sem_eq`): the loaded family is the hand-built `tpD`.
2. **The clock step** (`tp_cycle`): one cycle is the evaluated commit `tpNext`.
3. **The registers through a cycle**, register by register (`nbaFold`), and their closed forms `t` steps
   after a start (`wfV`, `ubV`, `datV`, `cV`). The PE registers are not cleared at a start, so their
   invariants say which entries are known `t` steps on (`shOK`, `waOK`, `psOK`, over `PEnt`).
4. **The phase model** and txtask-v2's three rules, then `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The latency: `done` shows `4N` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := 4 * N

/-! ## 1. The hand-built design -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `w` zero bits. -/
abbrev zv (w : Nat) : LVec := LVec.replicate w .l0

/-- A nonblocking write of a constant to a whole signal. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: the entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The first entry of data row `k` (row `k'` has `N + k'` entries). -/
def base (N k : Nat) : Nat := k * N + k * (k - 1) / 2

/-- The entries of all data rows. -/
def DW (N : Nat) : Nat := N * (3 * N - 1) / 2

/-- The control: `busy`, `done` and the step counter `t`. -/
def ctrlP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (zv 32)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (zv 32)])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "t") (.binary .add (.ident "t") (c32 1)),
          .ifStmt (.binary .eq (.ident "t") (c32 ((4 * N - 1 : Nat) : Int)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The weight FIFO. -/
def wfP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "wf") (.ident "B"))
    (some (.ifStmt (.binary .lt (.ident "t") (c32 N))
      (.nbaAssign (.ident "wf") (.binary (.shl false) (.ident "wf") (.binary .mul (c32 N) (c32 W))))
      none)))

/-- The unified buffer. -/
def ubP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "ub") (.ident "A"))
    (some (.ifStmt (.binary .ge (.ident "t") (c32 N))
      (.nbaAssign (.ident "ub") (.binary (.shr false) (.ident "ub") (.binary .mul (c32 N) (c32 W))))
      none)))

/-- Entry `e < N + k - 1` of data row `k`: the entry above it. -/
def dsP (N AccW k e : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "dat" ((base N k + e) * AccW) AccW) (.lit (zv AccW)))
    (some (.nbaAssign (.slice "dat" ((base N k + e) * AccW) AccW)
      (.slice (.ident "dat") ((base N k + e + 1) * AccW) AccW))))

/-- The top entry of data row `k`: the setup unit's input. -/
def dtP (N W AccW k : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "dat" ((base N k + N + k - 1) * AccW) AccW) (.lit (zv AccW)))
    (some (.ifStmt (.binary .ge (.ident "t") (c32 N))
      (.nbaAssign (.slice "dat" ((base N k + N + k - 1) * AccW) AccW) (.resize AccW (sext "ub" AccW (k * W) W)))
      (some (.nbaAssign (.slice "dat" ((base N k + N + k - 1) * AccW) AccW) (.lit (zv AccW)))))))

/-- PE `(0, j)`. -/
def p0P (N W AccW j : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
      .ifStmt (.binary .lt (.ident "t") (c32 N))
        (.nbaAssign (.slice "wsh" (j * W) W) (.slice (.ident "wf") (((N - 1) * N + j) * W) W)) none,
      .ifStmt (.binary .eq (.ident "t") (c32 N))
        (.nbaAssign (.slice "wac" (j * AccW) AccW) (.resize AccW (sext "wsh" AccW (j * W) W))) none,
      .nbaAssign (.slice "ps" (j * AccW) AccW)
        (.binary .mul (.slice (.ident "dat") ((N - 1 - j) * AccW) AccW) (.slice (.ident "wac") (j * AccW) AccW))])

/-- PE `(k + 1, j)`. -/
def pkP (N W AccW k j : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
      .ifStmt (.binary .lt (.ident "t") (c32 N))
        (.nbaAssign (.slice "wsh" (((k + 1) * N + j) * W) W) (.slice (.ident "wsh") ((k * N + j) * W) W)) none,
      .ifStmt (.binary .eq (.ident "t") (c32 N))
        (.nbaAssign (.slice "wac" (((k + 1) * N + j) * AccW) AccW)
          (.resize AccW (sext "wsh" AccW (((k + 1) * N + j) * W) W))) none,
      .nbaAssign (.slice "ps" (((k + 1) * N + j) * AccW) AccW)
        (.binary .add (.slice (.ident "ps") ((k * N + j) * AccW) AccW)
          (.binary .mul (.slice (.ident "dat") ((base N (k + 1) + N - 1 - j) * AccW) AccW)
            (.slice (.ident "wac") (((k + 1) * N + j) * AccW) AccW)))])

/-- Accumulator word `i < N - 1` of column `j`. -/
def arP (N AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (zv AccW)))
    (some (.ifStmt (.ident "busy")
      (.ifStmt (.binary .ge (.ident "t") (.binary .add (c32 (2 * (N : Int) + 1)) (c32 j)))
        (.ifStmt (.binary .le (.ident "t") (.binary .add (c32 (3 * (N : Int))) (c32 j)))
          (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.slice (.ident "C") (((i + 1) * N + j) * AccW) AccW))
          none)
        none)
      none)))

/-- Accumulator word `N - 1` of column `j`: word `0` plus the column's bottom partial sum. -/
def alP (N AccW j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "C" (((N - 1) * N + j) * AccW) AccW) (.lit (zv AccW)))
    (some (.ifStmt (.ident "busy")
      (.ifStmt (.binary .ge (.ident "t") (.binary .add (c32 (2 * (N : Int) + 1)) (c32 j)))
        (.ifStmt (.binary .le (.ident "t") (.binary .add (c32 (3 * (N : Int))) (c32 j)))
          (.nbaAssign (.slice "C" (((N - 1) * N + j) * AccW) AccW)
            (.binary .add (.slice (.ident "C") (j * AccW) AccW) (.slice (.ident "ps") (((N - 1) * N + j) * AccW) AccW)))
          none)
        none)
      none)))

/-- The declarations. -/
def tpDecls (N W AccW : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true }, { name := "busy", width := 1 },
   { name := "t", width := 32 }, { name := "wf", width := N * N * W }, { name := "wsh", width := N * N * W },
   { name := "wac", width := N * N * AccW }, { name := "ub", width := N * N * W }, { name := "dat", width := DW N * AccW },
   { name := "ps", width := N * N * AccW }]

def dsPs (N AccW : Nat) : List Process2 := (List.range N).flatMap fun k => (List.range (N + k - 1)).map (dsP N AccW k)
def dtPs (N W AccW : Nat) : List Process2 := (List.range N).map (dtP N W AccW)
def p0Ps (N W AccW : Nat) : List Process2 := (List.range N).map (p0P N W AccW)
def pkPs (N W AccW : Nat) : List Process2 := (List.range (N - 1)).flatMap fun k => (List.range N).map (pkP N W AccW k)
def arPs (N AccW : Nat) : List Process2 := (List.range (N - 1)).flatMap fun i => (List.range N).map (arP N AccW i)
def alPs (N AccW : Nat) : List Process2 := (List.range N).map (alP N AccW)

/-- The generated processes, in source order. -/
def genPs (N W AccW : Nat) : List Process2 :=
  dsPs N AccW ++ dtPs N W AccW ++ p0Ps N W AccW ++ pkPs N W AccW ++ arPs N AccW ++ alPs N AccW

/-- **The hand-built design.** -/
def tpD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (tpDecls N W AccW).toArray
  processes := (ctrlP N :: wfP N W :: ubP N W :: genPs N W AccW).toArray

/-! ### The instantiation environment -/

def tpScopeRaw (N W AccW : Nat) : IEnv :=
  { vals := [("LAST", 4 * (N : Int) - 1), ("HI", 3 * (N : Int)), ("LO", 2 * (N : Int) + 1), ("N", N), ("W", W),
      ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("LO", 32), ("HI", 32), ("LAST", 32)] }

def tpScope (N W AccW : Nat) : IEnv :=
  { vals := [("LAST", ((4 * N - 1 : Nat) : Int)), ("HI", ((3 * N : Nat) : Int)), ("LO", ((2 * N + 1 : Nat) : Int)),
      ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("LO", 32), ("HI", 32), ("LAST", 32)] }

def tpEnvRaw (N W AccW : Nat) : IEnv := { tpScopeRaw N W AccW with dims := dimTable (tpScopeRaw N W AccW) design.pdesign.decls }

def tpEnv (N W AccW : Nat) : IEnv := { tpScope N W AccW with dims := dimTable (tpScope N W AccW) design.pdesign.decls }

def tpElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "busy", "t", "wf", "wsh", "wac", "ub", "dat", "ps"].map (·, 1)

abbrev tpE (N W AccW : Nat) : IEnv := (tpEnv N W AccW).withDecls (tpDecls N W AccW)

theorem declTy (env : IEnv) :
    declConstType env (some (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32))) none = .ok none := rfl

theorem tyW (env : IEnv) : (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32)).width env = .ok 32 :=
  rfl

theorem tp_paramEnv_raw (N W AccW : Nat) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (tpEnvRaw N W AccW) := by
  simp [PDesign.paramEnv2, design.pdesign, bindPackageParams, bindPackageEnums, bindParamsRes, bindParams,
    bindLocals, bindLocal, evalIntTarget, evalInt, bindEnums, IEnv.bindVal, declTy, tyW, tpEnvRaw, tpScopeRaw,
    Gen2.except_ok_bind, Except.mapError, List.lookup, List.filterMapM, List.filterMapM.loop]

theorem tp_env_eq (N W AccW : Nat) (hN : 1 ≤ N) : tpEnvRaw N W AccW = tpEnv N W AccW := by
  have e1 : 4 * (N : Int) - 1 = ((4 * N - 1 : Nat) : Int) := by omega
  have e2 : 3 * (N : Int) = ((3 * N : Nat) : Int) := by omega
  have e3 : 2 * (N : Int) + 1 = ((2 * N + 1 : Nat) : Int) := by omega
  simp only [tpEnvRaw, tpEnv, tpScopeRaw, tpScope, e1, e2, e3]

theorem tp_paramEnv (N W AccW : Nat) (hN : 1 ≤ N) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (tpEnv N W AccW) := by
  rw [tp_paramEnv_raw, tp_env_eq N W AccW hN]

/-! ### Declarations and elements -/

theorem natAbs_cast {x : Nat} {X : Int} (h : (x : Int) = X) (hx : 0 < x) : (X - 1).natAbs + 1 = x := by
  subst h; omega

theorem DW_pos {N : Nat} (hN : 1 ≤ N) : 0 < DW N := by
  unfold DW
  have : 1 * 2 ≤ N * (3 * N - 1) := Nat.mul_le_mul hN (by omega)
  omega

theorem tdiv_two_cast (n : Nat) : ((n : Int)).tdiv 2 = ((n / 2 : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega

theorem DW_cast (N : Nat) (hN : 1 ≤ N) : ((N : Int) * (3 * (N : Int) - 1)).tdiv 2 = ((DW N : Nat) : Int) := by
  have h : ((N : Int) * (3 * (N : Int) - 1)) = ((N * (3 * N - 1) : Nat) : Int) := by
    rw [Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl
  rw [h, tdiv_two_cast]; rfl

theorem tp_decls (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    buildDecls (tpEnv N W AccW) design.pdesign.decls = .ok (tpDecls N W AccW) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have h1 : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hW)
  have h2 : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hA)
  have h3 : (((N : Int) * (3 * (N : Int) - 1)).tdiv 2 * AccW - 1).natAbs + 1 = DW N * AccW :=
    natAbs_cast (by rw [DW_cast N hN]; push_cast; rfl) (Nat.mul_pos (DW_pos hN) hA)
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    tpEnv, tpScope, List.lookup, Gen2.except_ok_bind, tpDecls, h1, h2, h3]

theorem tp_elems (N W AccW : Nat) : buildElems (tpEnv N W AccW) design.pdesign.decls = .ok tpElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, tpEnv,
    tpScope, List.lookup, Gen2.except_ok_bind, tpElems]

/-! ### The static processes -/

def ctrlT : PProcess := match design.pdesign.processes with
  | [p, _, _] => p
  | _ => .alwaysFF "" (.block [])
def wfT : PProcess := match design.pdesign.processes with
  | [_, p, _] => p
  | _ => .alwaysFF "" (.block [])
def ubT : PProcess := match design.pdesign.processes with
  | [_, _, p] => p
  | _ => .alwaysFF "" (.block [])

macro "tp_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, tpEnv, tpScope, tpDecls, tpElems, ctrlT, wfT, ubT,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, *])

theorem ctrl_inst (N W AccW : Nat) (hN : 1 ≤ N) : instProcess2 (tpE N W AccW) tpElems ctrlT = ctrlP N := by
  tp_simp
  all_goals first | rfl | decide | skip

theorem wf_inst (N W AccW : Nat) (hN : 1 ≤ N) : instProcess2 (tpE N W AccW) tpElems wfT = wfP N W := by
  tp_simp
  all_goals first | rfl | decide | skip

theorem ub_inst (N W AccW : Nat) (hN : 1 ≤ N) : instProcess2 (tpE N W AccW) tpElems ubT = ubP N W := by
  tp_simp
  all_goals first | rfl | decide | skip

/-! ### The generate templates -/

def dsT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _, _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def dtT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.process p], _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def p0T : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.process p], _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def pkT : PProcess := match design.pdesign.generates with
  | [_, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _, _] => p
  | _ => .alwaysFF "" (.block [])
def arT : PProcess := match design.pdesign.generates with
  | [_, _, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])
def alT : PProcess := match design.pdesign.generates with
  | [_, _, _, _, _, .genFor _ _ _ _ _ _ [.process p]] => p
  | _ => .alwaysFF "" (.block [])

macro "tp_tsimp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, tpEnv, tpScope, tpDecls, tpElems, dsT, dtT, p0T, pkT, arT, alT, dsP, dtP, p0P, pkP, arP, alP, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, divOperandWidthSum2, arraySelWidth, instDivParts2, *])

theorem tdiv_kk (k : Nat) : ((k : Int) * ((k : Int) - 1)).tdiv 2 = ((k * (k - 1) / 2 : Nat) : Int) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rfl
  · have h : ((k : Int) * ((k : Int) - 1)) = ((k * (k - 1) : Nat) : Int) := by
      rw [Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl
    rw [h, tdiv_two_cast]

theorem tdiv_kk1 (k : Nat) : (((k : Int) + 1) * (k : Int)).tdiv 2 = (((k + 1) * k / 2 : Nat) : Int) := by
  have h : (((k : Int) + 1) * (k : Int)) = (((k + 1) * k : Nat) : Int) := by push_cast; rfl
  rw [h, tdiv_two_cast]

/-! ### The triangle's offsets -/

theorem tri_succ (k : Nat) : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
  cases k with
  | zero => rfl
  | succ m =>
    have h : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by
      rw [Nat.succ_mul, Nat.mul_succ]; omega
    rw [h, Nat.add_sub_cancel]; omega

theorem base_succ (N k : Nat) : base N (k + 1) = base N k + N + k := by
  unfold base; rw [Nat.add_sub_cancel, tri_succ, Nat.succ_mul]; omega

theorem base_mono (N : Nat) {k k' : Nat} (h : k ≤ k') : base N k ≤ base N k' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [base_succ]; omega

theorem base_N (N : Nat) (hN : 1 ≤ N) : base N N = DW N := by
  unfold base DW
  have h : N * (3 * N - 1) = 2 * (N * N) + N * (N - 1) := by
    rw [show 3 * N - 1 = 2 * N + (N - 1) by omega, Nat.mul_add, Nat.mul_left_comm]
  rw [h]; omega

/-- Row `k`'s entries end where row `k + 1` begins, and every row is inside the triangle. -/
theorem base_row_le (N : Nat) (hN : 1 ≤ N) {k : Nat} (hk : k < N) : base N k + N + k ≤ DW N := by
  rw [← base_succ, ← base_N N hN]; exact base_mono N hk

theorem base_cast (N k e W : Nat) :
    (((base N k + e) * W : Nat) : Int) = ((k : Int) * N + (k : Int) * ((k - 1 : Nat) : Int) / 2 + e) * W := by
  simp [base]

/-- The window facts of a select `x[lo +: w]` of a `c`-bit signal, the offset `X` and the width `C` as the
loader computes them. -/
theorem winF (X C : Int) {lo w c : Nat} (hx : (lo : Int) = X) (hC : (c : Int) = C) (hw : 0 < w) (h : lo + w ≤ c) :
    0 ≤ X ∧ X.toNat = lo ∧ X + (w : Int) - 1 < C ∧ ¬ (X + (w : Int) - 1 < 0) ∧ ¬ X < 0 ∧
      (X + (w : Int) - 1 - X + 1).toNat = w ∧ ¬ (C ≤ X) ∧ X ≤ X + (w : Int) - 1 ∧ 1 ≤ X + (w : Int) := by
  subst hx hC; omega

/-- The facts of a bit select `x[i]` of a `c`-bit signal. -/
theorem bitF (X C : Int) {i c : Nat} (hx : (i : Int) = X) (hC : (c : Int) = C) (h : i < c) :
    0 ≤ X ∧ X.toNat = i ∧ X < C ∧ ¬ X < 0 ∧ ¬ C ≤ X := by
  subst hx hC; omega

theorem cDW (N W : Nat) : ((DW N * W : Nat) : Int) = ((DW N : Nat) : Int) * (W : Int) := by push_cast; rfl
theorem cNNW (N W : Nat) : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl

theorem ds_inst (N W AccW k e : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N) (he : e < N + k - 1) :
    instProcess2 (((tpE N W AccW).bindVal "k" k).bindVal "e" e) tpElems dsT = dsP N AccW k e := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hDW := DW_cast N hN
  have hkk := tdiv_kk k
  have hc : (((DW N : Nat) : Int) * (AccW : Int) - 1).natAbs + 1 = DW N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (DW_pos hN) hA)
  have d1 : (1 : Int) ≤ ((DW N : Nat) : Int) * (AccW : Int) := by
    have := Nat.mul_pos (DW_pos hN) hA
    have h' := cDW N AccW
    omega
  have hrow := base_row_le N hN hk
  have w1 := winF (((k : Int) * N + (k : Int) * ((k - 1 : Nat) : Int) / 2 + e) * AccW)
    (((DW N : Nat) : Int) * (AccW : Int))
    (lo := (base N k + e) * AccW) (w := AccW) (c := DW N * AccW) (base_cast N k e AccW) (cDW N AccW) hA
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega))
  have w2 := winF (((k : Int) * N + (k : Int) * ((k - 1 : Nat) : Int) / 2 + e + 1) * AccW)
    (((DW N : Nat) : Int) * (AccW : Int))
    (lo := (base N k + e + 1) * AccW) (w := AccW) (c := DW N * AccW) (by simp [base])
    (cDW N AccW) hA (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega))
  tp_tsimp

/-- The declared widths as the instantiation computes them. -/
theorem decl_facts (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    ((N : Int) * N * W - 1).natAbs + 1 = N * N * W ∧ ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW ∧
      (((DW N : Nat) : Int) * (AccW : Int) - 1).natAbs + 1 = DW N * AccW ∧ (1 : Int) ≤ (N : Int) * N * W ∧
      (1 : Int) ≤ (N : Int) * N * AccW ∧ (1 : Int) ≤ ((DW N : Nat) : Int) * (AccW : Int) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have p1 := Nat.mul_pos hNN hW
  have p2 := Nat.mul_pos hNN hA
  have p3 := Nat.mul_pos (DW_pos hN) hA
  have c1 := cNNW N W
  have c2 := cNNW N AccW
  have c3 := cDW N AccW
  refine ⟨natAbs_cast c1 p1, natAbs_cast c2 p2, natAbs_cast c3 p3, by omega, by omega, by omega⟩

theorem winle {i M : Nat} (w : Nat) (h : i < M) : i * w + w ≤ M * w := by
  have := Nat.mul_le_mul_right w (Nat.succ_le_of_lt h); rwa [Nat.succ_mul] at this

theorem castW {x : Nat} {X : Int} (h : (x : Int) = X) (W : Nat) : ((x * W : Nat) : Int) = X * W := by
  rw [Int.natCast_mul, h]

theorem cast_base (N k : Nat) : ((base N k : Nat) : Int) = (k : Int) * N + (k : Int) * ((k - 1 : Nat) : Int) / 2 := by
  simp [base]

theorem dt_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N) :
    instProcess2 ((tpE N W AccW).bindVal "k" k) tpElems dtT = dtP N W AccW k := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hW0 : 0 < W := hW
  have hWi : (0 : Int) < W := by omega
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hWne : ¬ W = 0 := by omega
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  have hDW := DW_cast N hN
  have hkk := tdiv_kk k
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := decl_facts N W AccW hN hW hA
  have hrow := base_row_le N hN hk
  have hb := cast_base N k
  have w1 := winF (((k : Int) * N + (k : Int) * ((k - 1 : Nat) : Int) / 2 + N + k - 1) * AccW)
    (((DW N : Nat) : Int) * (AccW : Int))
    (lo := (base N k + N + k - 1) * AccW) (w := AccW) (c := DW N * AccW) (castW (by omega) AccW) (cDW N AccW) hA
    (winle AccW (by omega))
  have hkNN : k < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
  have w2 := winF ((k : Int) * W) ((N : Int) * N * W) (lo := k * W) (w := W) (c := N * N * W) (castW rfl W)
    (cNNW N W) hW (winle W hkNN)
  have b1 := bitF ((k : Int) * W + W - 1) ((N : Int) * N * W) (i := k * W + W - 1) (c := N * N * W)
    (by rw [Int.ofNat_sub (by omega), Int.natCast_add, castW rfl W]; simp) (cNNW N W)
    (by have : k * W + W ≤ N * N * W := winle W hkNN
        omega)
  tp_tsimp
  repeat (unfold instExpr2; tp_tsimp)
  all_goals first | rfl | decide | skip

theorem p0_inst (N W AccW j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hj : j < N) :
    instProcess2 ((tpE N W AccW).bindVal "j" j) tpElems p0T = p0P N W AccW j := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hW0 : 0 < W := hW
  have hWi : (0 : Int) < W := by omega
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hWne : ¬ W = 0 := by omega
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  have hDW := DW_cast N hN
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := decl_facts N W AccW hN hW hA
  have hjNN : j < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
  have hDWN : N ≤ DW N := by have := base_row_le N hN (show 0 < N by omega); simp [base] at this; omega
  have w1 := winF ((j : Int) * W) ((N : Int) * N * W) (lo := j * W) (w := W) (c := N * N * W) (castW rfl W)
    (cNNW N W) hW (winle W hjNN)
  have w2 := winF ((j : Int) * AccW) ((N : Int) * N * AccW) (lo := j * AccW) (w := AccW) (c := N * N * AccW)
    (castW rfl AccW) (cNNW N AccW) hA (winle AccW hjNN)
  have w3 := winF ((((N : Int) - 1) * N + j) * W) ((N : Int) * N * W) (lo := ((N - 1) * N + j) * W) (w := W)
    (c := N * N * W) (castW (by rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hN]; rfl) W) (cNNW N W) hW
    (winle W (by have := Nat.mul_le_mul_right N (show N - 1 + 1 ≤ N by omega); rw [Nat.succ_mul] at this; omega))
  have w4 := winF (((N : Int) - 1 - j) * AccW) (((DW N : Nat) : Int) * (AccW : Int)) (lo := (N - 1 - j) * AccW)
    (w := AccW) (c := DW N * AccW) (castW (by omega) AccW) (cDW N AccW) hA (winle AccW (by omega))
  have b2 := bitF ((j : Int) * W + W - 1) ((N : Int) * N * W) (i := j * W + W - 1) (c := N * N * W)
    (by rw [Int.ofNat_sub (by omega), Int.natCast_add, castW rfl W]; simp) (cNNW N W)
    (by have : j * W + W ≤ N * N * W := winle W hjNN
        omega)
  tp_tsimp
  repeat (unfold instExpr2; tp_tsimp)
  all_goals first | rfl | decide | skip

theorem rm_lt {N i j : Nat} (hi : i < N) (hj : j < N) : i * N + j < N * N := by
  have := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hi); rw [Nat.succ_mul] at this; omega

theorem pk_inst (N W AccW k j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N - 1) (hj : j < N) :
    instProcess2 (((tpE N W AccW).bindVal "k" k).bindVal "j" j) tpElems pkT = pkP N W AccW k j := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hW0 : 0 < W := hW
  have hWi : (0 : Int) < W := by omega
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hWne : ¬ W = 0 := by omega
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  have hDW := DW_cast N hN
  have hkk := tdiv_kk1 k
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := decl_facts N W AccW hN hW hA
  have r1 := rm_lt (show k + 1 < N by omega) hj
  have r2 := rm_lt (show k < N by omega) hj
  have hrow := base_row_le N hN (show k + 1 < N by omega)
  have hb1 : ((base N (k + 1) : Nat) : Int) = ((k : Int) + 1) * N + ((k : Int) + 1) * k / 2 := by simp [base]
  have w1 := winF ((((k : Int) + 1) * N + j) * W) ((N : Int) * N * W) (lo := ((k + 1) * N + j) * W) (w := W)
    (c := N * N * W) (castW (by push_cast; rfl) W) (cNNW N W) hW (winle W r1)
  have w2 := winF ((((k : Int) + 1) * N + j) * AccW) ((N : Int) * N * AccW) (lo := ((k + 1) * N + j) * AccW) (w := AccW)
    (c := N * N * AccW) (castW (by push_cast; rfl) AccW) (cNNW N AccW) hA (winle AccW r1)
  have w3 := winF (((k : Int) * N + j) * W) ((N : Int) * N * W) (lo := (k * N + j) * W) (w := W)
    (c := N * N * W) (castW (by push_cast; rfl) W) (cNNW N W) hW (winle W r2)
  have w4 := winF (((k : Int) * N + j) * AccW) ((N : Int) * N * AccW) (lo := (k * N + j) * AccW) (w := AccW)
    (c := N * N * AccW) (castW (by push_cast; rfl) AccW) (cNNW N AccW) hA (winle AccW r2)
  have w5 := winF ((((k : Int) + 1) * N + ((k : Int) + 1) * k / 2 + N - 1 - j) * AccW)
    (((DW N : Nat) : Int) * (AccW : Int))
    (lo := (base N (k + 1) + N - 1 - j) * AccW) (w := AccW) (c := DW N * AccW) (castW (by omega) AccW) (cDW N AccW) hA
    (winle AccW (by omega))
  have b2 := bitF ((((k : Int) + 1) * N + j) * W + W - 1) ((N : Int) * N * W) (i := ((k + 1) * N + j) * W + W - 1)
    (c := N * N * W) (by rw [Int.ofNat_sub (by omega), Int.natCast_add, castW (by push_cast; rfl) W]; simp) (cNNW N W)
    (by have : ((k + 1) * N + j) * W + W ≤ N * N * W := winle W r1
        omega)
  tp_tsimp
  repeat (unfold instExpr2; tp_tsimp)
  all_goals first | rfl | decide | skip

theorem ar_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N - 1) (hj : j < N) :
    instProcess2 (((tpE N W AccW).bindVal "i" i).bindVal "j" j) tpElems arT = arP N AccW i j := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hDW := DW_cast N hN
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := decl_facts N W AccW hN hW hA
  have r1 := rm_lt (show i + 1 < N by omega) hj
  have r2 := rm_lt (show i < N by omega) hj
  have w1 := winF ((((i : Int) + 1) * N + j) * AccW) ((N : Int) * N * AccW) (lo := ((i + 1) * N + j) * AccW) (w := AccW)
    (c := N * N * AccW) (castW (by push_cast; rfl) AccW) (cNNW N AccW) hA (winle AccW r1)
  have w2 := winF (((i : Int) * N + j) * AccW) ((N : Int) * N * AccW) (lo := (i * N + j) * AccW) (w := AccW)
    (c := N * N * AccW) (castW (by push_cast; rfl) AccW) (cNNW N AccW) hA (winle AccW r2)
  tp_tsimp
  exact ⟨if_pos (by decide), if_pos (by decide)⟩

theorem al_inst (N W AccW j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hj : j < N) :
    instProcess2 ((tpE N W AccW).bindVal "j" j) tpElems alT = alP N AccW j := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hA0 : 0 < AccW := hA
  have hAi : (0 : Int) < AccW := by omega
  have hDW := DW_cast N hN
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := decl_facts N W AccW hN hW hA
  have r1 := rm_lt (show N - 1 < N by omega) hj
  have r2 : j < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
  have w1 := winF ((((N : Int) - 1) * N + j) * AccW) ((N : Int) * N * AccW) (lo := ((N - 1) * N + j) * AccW) (w := AccW)
    (c := N * N * AccW) (castW (by rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hN]; rfl) AccW) (cNNW N AccW) hA
    (winle AccW r1)
  have w2 := winF ((j : Int) * AccW) ((N : Int) * N * AccW) (lo := j * AccW) (w := AccW)
    (c := N * N * AccW) (castW rfl AccW) (cNNW N AccW) hA (winle AccW r2)
  tp_tsimp
  exact ⟨if_pos (by decide), if_pos (by decide)⟩

/-! ### The generates -/

/-- `for (g = 0; g < bound; g++) body`. -/
def genL (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

def nE : PExpr := .paramRef "N" none
def nm1E : PExpr := .binary (.m0 .sub) (.paramRef "N" none) (.int 1)
def nkE : PExpr := .binary (.m0 .sub) (.binary (.m0 .add) (.paramRef "N" none) (.genvarRef "k")) (.int 1)

theorem tp_gens_src : design.pdesign.generates =
    [genL "g_dk" "k" nE 4 [genL "g_de" "e" nkE 3 ([dsT].map .process)], genL "g_dt" "k" nE 4 ([dtT].map .process),
     genL "g_p0" "j" nE 4 ([p0T].map .process), genL "g_pr" "k" nm1E 3 [genL "g_pc" "j" nE 4 ([pkT].map .process)],
     genL "g_ar" "i" nm1E 3 [genL "g_ac" "j" nE 4 ([arT].map .process)], genL "g_al" "j" nE 4 ([alT].map .process)] :=
  rfl

theorem toNat_sub_zero (n : Nat) : ((n : Int) - 0).toNat = n := by omega

/-- A loop over `[0, n)` whose body is one process template, instantiated by `inst`. -/
theorem gen_one {env : IEnv} {F : Nat} {lbl g : String} {bound : PExpr} {rc : Nat} {T : PProcess} {n : Nat}
    {P : Nat → Process2} (hb : ∀ i : Int, bound.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) bound = .ok (n : Int)) (hF : n < F)
    (hinst : ∀ v, v < n → instProcess2 (env.bindVal g (v : Int)) tpElems T = P v) :
    (genL lbl g bound rc ([T].map .process)).expand2 env tpElems F = .ok ((List.range n).map P) := by
  rw [genL, GenItem.expand2_genFor_ascending_processes (N := (n : Int)) (evalInt_int 0) hb he
    (by rw [toNat_sub_zero]; exact hF), toNat_sub_zero, intRange_zero]
  simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map]
  congr 1
  exact List.map_congr_left fun v hv => hinst v (List.mem_range.mp hv)

/-- Two nested loops, the inner over `[0, m v)`. -/
theorem gen_two {env : IEnv} {F : Nat} {lbl g lbl' g' : String} {bound bound' : PExpr} {rc rc' : Nat} {T : PProcess}
    {n : Nat} {m : Nat → Nat} {P : Nat → Nat → Process2}
    (hb : ∀ i : Int, bound.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) bound = .ok (n : Int)) (hF : n < F)
    (hb' : ∀ v, v < n → ∀ i : Int, bound'.isInt ((env.bindVal g (v : Int)).bindVal g' i) = true)
    (he' : ∀ v, v < n → ∀ i : Int, evalInt ((env.bindVal g (v : Int)).bindVal g' i) bound' = .ok ((m v : Nat) : Int))
    (hF' : ∀ v, v < n → m v < F)
    (hinst : ∀ v w, v < n → w < m v → instProcess2 ((env.bindVal g (v : Int)).bindVal g' (w : Int)) tpElems T = P v w) :
    (genL lbl g bound rc [genL lbl' g' bound' rc' ([T].map .process)]).expand2 env tpElems F =
      .ok ((List.range n).flatMap fun v => (List.range (m v)).map (P v)) := by
  rw [genL, GenItem.expand2_genFor_ascending_flatMap (N := (n : Int))
      (f := fun v => (List.range (m v.toNat)).map (P v.toNat)) (evalInt_int 0) hb he
      (by rw [toNat_sub_zero]; exact hF)]
  · simp only [toNat_sub_zero, intRange_zero, List.flatMap_map, Int.toNat_natCast]
  · intro v hv0 hvn
    obtain ⟨u, rfl⟩ : ∃ u : Nat, v = (u : Int) := ⟨v.toNat, by omega⟩
    have hu : u < n := by omega
    apply expandList2_singleton_ok
    rw [Int.toNat_natCast]
    exact gen_one (hb' u hu) (he' u hu) (hF' u hu) (fun w hw => hinst u w hu hw)

theorem lookN {env : IEnv} {g : String} (v : Int) (hg : g ≠ "N") (h : env.vals.lookup "N" = some (N : Int)) :
    (env.bindVal g v).vals.lookup "N" = some (N : Int) := by rw [vals_lookup_bindVal_ne _ hg.symm, h]

theorem tp_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : 2 * N < F) :
    expandList2 (tpE N W AccW) tpElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have hNv : (tpE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  have hNF : N < F := by omega
  rw [tp_gens_src, genPs, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_cons_ok ?_
    (expandList2_cons_ok ?_ (expandList2_singleton_ok ?_)))))
  · -- the data rows' shifting entries
    refine gen_two (m := fun k => N + k - 1) (fun _ => rfl)
      (fun i => evalInt_paramRef_of (lookN (g := "k") i (by decide) hNv)) hNF
      (fun _ _ _ => rfl) (fun v _ i => ?_) (fun v hv => by omega) (fun v w hv hw => ds_inst N W AccW v w hN hW hA hv hw)
    have h1 : ((((tpE N W AccW).bindVal "k" (v : Int)).bindVal "e" i).vals.lookup "N") = some (N : Int) :=
      lookN (g := "e") i (by decide) (lookN (g := "k") _ (by decide) hNv)
    have h2 : ((((tpE N W AccW).bindVal "k" (v : Int)).bindVal "e" i).vals.lookup "k") = some (v : Int) := by
      rw [vals_lookup_bindVal_ne _ (by decide), vals_lookup_bindVal_self]
    rw [nkE, evalInt_sub_of rfl rfl (evalInt_add_of rfl rfl (evalInt_paramRef_of h1) (evalInt_genvarRef_of h2))
      (evalInt_int 1)]
    congr 1; omega
  · exact gen_one (fun _ => rfl) (fun i => evalInt_paramRef_of (lookN (g := "k") i (by decide) hNv)) hNF
      (fun v hv => dt_inst N W AccW v hN hW hA hv)
  · exact gen_one (fun _ => rfl) (fun i => evalInt_paramRef_of (lookN (g := "j") i (by decide) hNv)) hNF
      (fun v hv => p0_inst N W AccW v hN hW hA hv)
  · refine gen_two (n := N - 1) (m := fun _ => N) (fun i => isInt_binary_of rfl (isInt_paramRef_of (lookN (g := "k") i (by decide) hNv)) rfl)
      (fun i => ?_) (by omega)
      (fun v _ i => isInt_paramRef_of (lookN (g := "j") i (by decide) (lookN (g := "k") _ (by decide) hNv)))
      (fun v _ i => evalInt_paramRef_of (lookN (g := "j") i (by decide) (lookN (g := "k") _ (by decide) hNv)))
      (fun _ _ => hNF) (fun v w hv hw => pk_inst N W AccW v w hN hW hA hv hw)
    rw [nm1E, evalInt_sub_of (isInt_paramRef_of (lookN (g := "k") i (by decide) hNv)) rfl
      (evalInt_paramRef_of (lookN (g := "k") i (by decide) hNv)) (evalInt_int 1)]
    congr 1; omega
  · refine gen_two (n := N - 1) (m := fun _ => N) (fun i => isInt_binary_of rfl (isInt_paramRef_of (lookN (g := "i") i (by decide) hNv)) rfl)
      (fun i => ?_) (by omega)
      (fun v _ i => isInt_paramRef_of (lookN (g := "j") i (by decide) (lookN (g := "i") _ (by decide) hNv)))
      (fun v _ i => evalInt_paramRef_of (lookN (g := "j") i (by decide) (lookN (g := "i") _ (by decide) hNv)))
      (fun _ _ => hNF) (fun v w hv hw => ar_inst N W AccW v w hN hW hA hv hw)
    rw [nm1E, evalInt_sub_of (isInt_paramRef_of (lookN (g := "i") i (by decide) hNv)) rfl
      (evalInt_paramRef_of (lookN (g := "i") i (by decide) hNv)) (evalInt_int 1)]
    congr 1; omega
  · exact gen_one (fun _ => rfl) (fun i => evalInt_paramRef_of (lookN (g := "j") i (by decide) hNv)) hNF
      (fun v hv => al_inst N W AccW v hN hW hA hv)

theorem tp_static (N W AccW : Nat) (hN : 1 ≤ N) :
    design.pdesign.processes.map (instProcess2 (tpE N W AccW) tpElems) = [ctrlP N, wfP N W, ubP N W] := by
  rw [show design.pdesign.processes = [ctrlT, wfT, ubT] from rfl]
  simp only [List.map_cons, List.map_nil, ctrl_inst N W AccW hN, wf_inst N W AccW hN, ub_inst N W AccW hN]

theorem tp_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (tpEnv N W AccW) (tpDecls N W AccW) tpElems (genPs N W AccW)) := by
  refine PDesign.instantiate2_of_ok rfl (tp_paramEnv N W AccW hN) (tp_decls N W AccW hN hW hA) (tp_elems N W AccW)
    (tp_gens N W AccW _ hN hW hA ?_)
  have key : ∀ s : Nat, N ≤ s → 2 * N < (s + 2) * (s + 2) + 64 := fun s hs => by
    have := Nat.mul_le_mul (show 2 ≤ s + 2 by omega) (show N ≤ s + 2 by omega); omega
  exact key _ (by simp only [List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]; omega)

theorem tp_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      ctrlP N :: wfP N W :: ubP N W :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (tp_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    tp_static N W AccW hN]
  simp [design.pdesign]

/-! ### The windows: pairwise disjoint -/

abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

/-- Every window of `p` is of a name in `ns`. -/
def Names (p : Process2) (ns : List String) : Prop := ∀ a ∈ p.procWins, a.1 ∈ ns

/-- Every window of `p` is one of the slots `(name, lo, width)` in `L`. -/
def Slots (p : Process2) (L : List (String × Nat × Nat)) : Prop :=
  ∀ a ∈ p.procWins, ∃ s ∈ L, a = (s.1, some (s.2.1, s.2.2))

/-- Unit `r` of the registers `ns` (name, entry width). -/
def sl (ns : List (String × Nat)) (r : Nat) : List (String × Nat × Nat) := ns.map fun n => (n.1, r * n.2, n.2)

theorem disj_of_names {p q : Process2} {ns ms : List String} (hp : Names p ns) (hq : Names q ms)
    (h : ∀ n ∈ ns, n ∉ ms) : Disj p q := by
  intro a ha b hb
  have h1 := hp a ha; have h2 := hq b hb
  simp only [DrvWin.overlaps, Bool.and_eq_false_iff]
  left
  rw [beq_eq_false_iff_ne]
  intro he; rw [he] at h1; exact h _ h1 h2

theorem names_of_slots {p : Process2} {L : List (String × Nat × Nat)} (h : Slots p L) : Names p (L.map Prod.fst) := by
  intro a ha
  obtain ⟨s, hs, rfl⟩ := h a ha
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

theorem disj_sl {p q : Process2} {ns : List (String × Nat)} {r r' : Nat}
    (hns : ∀ a ∈ ns, ∀ b ∈ ns, a.1 = b.1 → a.2 = b.2) (hp : Slots p (sl ns r)) (hq : Slots q (sl ns r'))
    (h : r ≠ r') : Disj p q := by
  intro a ha b hb
  obtain ⟨s, hs, rfl⟩ := hp a ha
  obtain ⟨s', hs', rfl⟩ := hq b hb
  simp only [sl, List.mem_map] at hs hs'
  obtain ⟨n, hn, rfl⟩ := hs
  obtain ⟨n', hn', rfl⟩ := hs'
  simp only [DrvWin.overlaps, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  by_cases hnn : n.1 = n'.1
  · right
    have hw := hns n hn n' hn' hnn
    rw [← hw]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
    rcases Nat.lt_or_gt_of_ne h with h | h
    · right; exact rowMajor_le h
    · left; exact rowMajor_le h
  · left; exact hnn

def datN (W : Nat) : List (String × Nat) := [("dat", W)]
def peN (W AccW : Nat) : List (String × Nat) := [("wsh", W), ("wac", AccW), ("ps", AccW)]
def cN (AccW : Nat) : List (String × Nat) := [("C", AccW)]

theorem datN_ok (W : Nat) : ∀ a ∈ datN W, ∀ b ∈ datN W, a.1 = b.1 → a.2 = b.2 := by simp [datN]
theorem peN_ok (W AccW : Nat) : ∀ a ∈ peN W AccW, ∀ b ∈ peN W AccW, a.1 = b.1 → a.2 = b.2 := by simp [peN]
theorem cN_ok (AccW : Nat) : ∀ a ∈ cN AccW, ∀ b ∈ cN AccW, a.1 = b.1 → a.2 = b.2 := by simp [cN]

section windows
variable (N W AccW : Nat)

theorem ctrl_names : Names (ctrlP N) ["busy", "done", "t"] := by
  intro a ha
  simp only [ctrlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    List.append_nil, List.cons_append, List.nil_append] at ha
  revert ha a
  decide

theorem wf_names : Names (wfP N W) ["wf"] := by
  intro a ha
  simp only [wfP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    List.append_nil, List.cons_append, List.nil_append] at ha
  revert ha a
  decide

theorem ub_names : Names (ubP N W) ["ub"] := by
  intro a ha
  simp only [ubP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    List.append_nil, List.cons_append, List.nil_append] at ha
  revert ha a
  decide

theorem ds_slots (k e : Nat) : Slots (dsP N AccW k e) (sl (datN AccW) (base N k + e)) := by
  intro a ha
  simp [dsP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  subst ha; simp [sl, datN]

theorem dt_slots (k : Nat) : Slots (dtP N W AccW k) (sl (datN AccW) (base N k + N + k - 1)) := by
  intro a ha
  simp [dtP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl <;> simp [sl, datN]

theorem p0_slots (j : Nat) : Slots (p0P N W AccW j) (sl (peN W AccW) j) := by
  intro a ha
  simp [p0P, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl <;> simp [sl, peN]

theorem pk_slots (k j : Nat) : Slots (pkP N W AccW k j) (sl (peN W AccW) ((k + 1) * N + j)) := by
  intro a ha
  simp [pkP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl <;> simp [sl, peN]

theorem ar_slots (i j : Nat) : Slots (arP N AccW i j) (sl (cN AccW) (i * N + j)) := by
  intro a ha
  simp [arP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl <;> simp [sl, cN]

theorem al_slots (j : Nat) : Slots (alP N AccW j) (sl (cN AccW) ((N - 1) * N + j)) := by
  intro a ha
  simp [alP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl <;> simp [sl, cN]

end windows

section members
variable {N W AccW : Nat} {p : Process2}

theorem mem_ds (h : p ∈ dsPs N AccW) : ∃ k e, k < N ∧ e < N + k - 1 ∧ p = dsP N AccW k e := by
  simp only [dsPs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, e, he, rfl⟩ := h; exact ⟨k, e, hk, he, rfl⟩
theorem mem_dt (h : p ∈ dtPs N W AccW) : ∃ k, k < N ∧ p = dtP N W AccW k := by
  simp only [dtPs, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩
theorem mem_p0 (h : p ∈ p0Ps N W AccW) : ∃ j, j < N ∧ p = p0P N W AccW j := by
  simp only [p0Ps, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, hj, rfl⟩
theorem mem_pk (h : p ∈ pkPs N W AccW) : ∃ k j, k < N - 1 ∧ j < N ∧ p = pkP N W AccW k j := by
  simp only [pkPs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨k, hk, j, hj, rfl⟩ := h; exact ⟨k, j, hk, hj, rfl⟩
theorem mem_ar (h : p ∈ arPs N AccW) : ∃ i j, i < N - 1 ∧ j < N ∧ p = arP N AccW i j := by
  simp only [arPs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h; exact ⟨i, j, hi, hj, rfl⟩
theorem mem_al (h : p ∈ alPs N AccW) : ∃ j, j < N ∧ p = alP N AccW j := by
  simp only [alPs, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, hj, rfl⟩

end members

theorem genPs_eq (N W AccW : Nat) : genPs N W AccW =
    (dsPs N AccW ++ dtPs N W AccW) ++ ((p0Ps N W AccW ++ pkPs N W AccW) ++ (arPs N AccW ++ alPs N AccW)) := by
  simp only [genPs, List.append_assoc]

theorem dat_names {N W AccW : Nat} {p : Process2} (h : p ∈ dsPs N AccW ++ dtPs N W AccW) : Names p ["dat"] := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨k, e, -, -, rfl⟩ := mem_ds h; exact names_of_slots (ds_slots N AccW k e)
  · obtain ⟨k, -, rfl⟩ := mem_dt h; exact names_of_slots (dt_slots N W AccW k)

theorem pe_names {N W AccW : Nat} {p : Process2} (h : p ∈ p0Ps N W AccW ++ pkPs N W AccW) :
    Names p ["wsh", "wac", "ps"] := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨j, -, rfl⟩ := mem_p0 h; exact names_of_slots (p0_slots N W AccW j)
  · obtain ⟨k, j, -, -, rfl⟩ := mem_pk h; exact names_of_slots (pk_slots N W AccW k j)

theorem c_names {N AccW : Nat} {p : Process2} (h : p ∈ arPs N AccW ++ alPs N AccW) : Names p ["C"] := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i, j, -, -, rfl⟩ := mem_ar h; exact names_of_slots (ar_slots N AccW i j)
  · obtain ⟨j, -, rfl⟩ := mem_al h; exact names_of_slots (al_slots N AccW j)

theorem names_mono {p : Process2} {ns ms : List String} (h : Names p ns) (hm : ∀ n ∈ ns, n ∈ ms) : Names p ms :=
  fun a ha => hm _ (h a ha)

theorem gen_names {N W AccW : Nat} {p : Process2} (h : p ∈ genPs N W AccW) :
    Names p ["dat", "wsh", "wac", "ps", "C"] := by
  rw [genPs_eq] at h
  rcases List.mem_append.mp h with h | h
  · exact names_mono (dat_names h) (by decide)
  · rcases List.mem_append.mp h with h | h
    · exact names_mono (pe_names h) (by decide)
    · exact names_mono (c_names h) (by decide)

theorem dat_pairwise (N W AccW : Nat) (hN : 1 ≤ N) : (dsPs N AccW ++ dtPs N W AccW).Pairwise Disj := by
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine pairwise_flatMap_range (fun k _ => ?_) (fun k k' hkk _ a ha b hb => ?_)
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hee => ?_)
      exact disj_sl (datN_ok AccW) (ds_slots N AccW k _) (ds_slots N AccW k _) (by omega)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      obtain ⟨e', -, rfl⟩ := List.mem_map.mp hb
      have := List.mem_range.mp he
      have h1 := base_succ N k
      have h2 := base_mono N (show k + 1 ≤ k' by omega)
      exact disj_sl (datN_ok AccW) (ds_slots N AccW k e) (ds_slots N AccW k' e') (by omega)
  · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hkk => ?_)
    have := base_mono N (Nat.le_of_lt hkk)
    exact disj_sl (datN_ok AccW) (dt_slots N W AccW _) (dt_slots N W AccW _) (by omega)
  · intro a ha b hb
    obtain ⟨k, e, hk, he, rfl⟩ := mem_ds ha
    obtain ⟨k', hk', rfl⟩ := mem_dt hb
    refine disj_sl (datN_ok AccW) (ds_slots N AccW k e) (dt_slots N W AccW k') ?_
    rcases Nat.lt_trichotomy k k' with h | rfl | h
    · have h1 := base_succ N k
      have h2 := base_mono N (show k + 1 ≤ k' by omega)
      omega
    · omega
    · have h1 := base_succ N k'
      have h2 := base_mono N (show k' + 1 ≤ k by omega)
      omega

theorem pe_pairwise (N W AccW : Nat) : (p0Ps N W AccW ++ pkPs N W AccW).Pairwise Disj := by
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hjj => ?_)
    exact disj_sl (peN_ok W AccW) (p0_slots N W AccW _) (p0_slots N W AccW _) (by omega)
  · refine pairwise_flatMap_range (fun k _ => ?_) (fun k k' hkk _ a ha b hb => ?_)
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hjj => ?_)
      exact disj_sl (peN_ok W AccW) (pk_slots N W AccW k _) (pk_slots N W AccW k _) (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j', -, rfl⟩ := List.mem_map.mp hb
      have := List.mem_range.mp hj
      have := rowMajor_le (K := N) (show k + 1 < k' + 1 by omega)
      exact disj_sl (peN_ok W AccW) (pk_slots N W AccW k j) (pk_slots N W AccW k' j') (by omega)
  · intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := mem_p0 ha
    obtain ⟨k, j', -, -, rfl⟩ := mem_pk hb
    have := Nat.le_mul_of_pos_left N (show 0 < k + 1 by omega)
    exact disj_sl (peN_ok W AccW) (p0_slots N W AccW j) (pk_slots N W AccW k j') (by omega)

theorem c_pairwise (N W AccW : Nat) : (arPs N AccW ++ alPs N AccW).Pairwise Disj := by
  refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
  · refine pairwise_flatMap_range (fun i _ => ?_) (fun i i' hii _ a ha b hb => ?_)
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hjj => ?_)
      exact disj_sl (cN_ok AccW) (ar_slots N AccW i _) (ar_slots N AccW i _) (by omega)
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j', -, rfl⟩ := List.mem_map.mp hb
      have := List.mem_range.mp hj
      have := rowMajor_le (K := N) hii
      exact disj_sl (cN_ok AccW) (ar_slots N AccW i j) (ar_slots N AccW i' j') (by omega)
  · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hjj => ?_)
    exact disj_sl (cN_ok AccW) (al_slots N AccW _) (al_slots N AccW _) (by omega)
  · intro a ha b hb
    obtain ⟨i, j, hi, hj, rfl⟩ := mem_ar ha
    obtain ⟨j', -, rfl⟩ := mem_al hb
    have := rowMajor_le (K := N) hi
    exact disj_sl (cN_ok AccW) (ar_slots N AccW i j) (al_slots N AccW j') (by omega)

theorem tp_pairwise (N W AccW : Nat) (hN : 1 ≤ N) :
    (ctrlP N :: wfP N W :: ubP N W :: genPs N W AccW).Pairwise Disj := by
  refine .cons (fun q hq => ?_) (.cons (fun q hq => ?_) (.cons (fun q hq => ?_) ?_))
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (ctrl_names N) (wf_names N W) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (ctrl_names N) (ub_names N W) (by decide)
    · exact disj_of_names (ctrl_names N) (gen_names hq) (by decide)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (wf_names N W) (ub_names N W) (by decide)
    · exact disj_of_names (wf_names N W) (gen_names hq) (by decide)
  · exact disj_of_names (ub_names N W) (gen_names hq) (by decide)
  · rw [genPs_eq]
    refine List.pairwise_append.mpr ⟨dat_pairwise N W AccW hN, List.pairwise_append.mpr
      ⟨pe_pairwise N W AccW, c_pairwise N W AccW, ?_⟩, ?_⟩
    · intro a ha b hb; exact disj_of_names (pe_names ha) (c_names hb) (by decide)
    · intro a ha b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact disj_of_names (dat_names ha) (pe_names hb) (by decide)
      · exact disj_of_names (dat_names ha) (c_names hb) (by decide)

theorem tp_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ ctrlP N :: wfP N W :: ubP N W :: genPs N W AccW) :
    p = ctrlP N ∨ p = wfP N W ∨ p = ubP N W ∨ (∃ k e, k < N ∧ e < N + k - 1 ∧ p = dsP N AccW k e) ∨
      (∃ k, k < N ∧ p = dtP N W AccW k) ∨ (∃ j, j < N ∧ p = p0P N W AccW j) ∨
      (∃ k j, k < N - 1 ∧ j < N ∧ p = pkP N W AccW k j) ∨ (∃ i j, i < N - 1 ∧ j < N ∧ p = arP N AccW i j) ∨
      (∃ j, j < N ∧ p = alP N AccW j) := by
  simp only [List.mem_cons, genPs, List.mem_append] at hp
  rcases hp with rfl | rfl | rfl | ((((hp | hp) | hp) | hp) | hp) | hp
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl (mem_ds hp))))
  · exact .inr (.inr (.inr (.inr (.inl (mem_dt hp)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (mem_p0 hp))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl (mem_pk hp)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (mem_ar hp))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (mem_al hp))))))))

theorem tp_driversOk (N W AccW : Nat) (hN : 1 ≤ N) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (ctrlP N :: wfP N W :: ubP N W :: genPs N W AccW) =
      true := by
  apply driversOk_of_ff ?_ ?_ (tp_pairwise N W AccW hN)
  · intro p hp
    rcases tp_mem hp with rfl | rfl | rfl | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact ⟨_, _, rfl⟩
  · intro n hn
    simp only [List.mem_flatMap] at hn
    obtain ⟨p, hp, hn⟩ := hn
    rcases tp_mem hp with rfl | rfl | rfl | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
    revert n <;> simp [ctrlP, wfP, ubP, dsP, dtP, p0P, pkP, arP, alP, nb, Process2.procWrites, Process2.procWins,
      Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] <;> decide

/-- **The loaded family is `tpD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem tp_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.sem N W AccW = tpD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [tp_processes N W AccW hN hW hA]; exact tp_driversOk N W AccW hN)
  rw [h1, PDesign.instantiateD2_of_ok (tp_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, tp_static N W AccW hN, tpD]
  simp [design.pdesign]

/-- **`tpD` is in G0's FF-only profile.** -/
theorem tp_profile (N W AccW : Nat) (hN : 1 ≤ N) : (tpD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by exact tp_pairwise N W AccW hN)⟩
  simp [tpD, genPs, dsPs, dtPs, p0Ps, pkPs, arPs, alPs, ctrlP, wfP, ubP, dsP, dtP, p0P, pkP, arP, alP, nb,
    List.all_flatMap, List.all_map, List.all_append,
    Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB,
    Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, tpDecls]

/-! ## 2. One cycle: the processes' updates and the clock step -/

/-- The fifteen signals of `tpD`, in declaration order. -/
def SS (ck r s a b dn c bz t wf sh wa ub dt ps : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("busy", bz), ("t", t),
   ("wf", wf), ("wsh", sh), ("wac", wa), ("ub", ub), ("dat", dt), ("ps", ps)]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The step tests, as the processes evaluate them. -/
abbrev ltB (N : Nat) (t : LVec) : Bool := (LVec.ofLogic (t.lt (LVec.ofInt 32 N))).condTrue
abbrev eqB (N : Nat) (t : LVec) : Bool := (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 N))).condTrue
abbrev geB (N : Nat) (t : LVec) : Bool := (LVec.ofLogic (t.ge (LVec.ofInt 32 N))).condTrue
abbrev lastB (N : Nat) (t : LVec) : Bool :=
  (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 ((4 * N - 1 : Nat) : Int)))).condTrue
abbrev loB (N j : Nat) (t : LVec) : Bool :=
  (LVec.ofLogic (t.ge ((LVec.ofInt 32 (2 * (N : Int) + 1)).add (LVec.ofInt 32 j)))).condTrue
abbrev hiB (N j : Nat) (t : LVec) : Bool :=
  (LVec.ofLogic (t.le ((LVec.ofInt 32 (3 * (N : Int))).add (LVec.ofInt 32 j)))).condTrue

def ctrlQ (N : Nat) (r s dn bz t : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (zv 32)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (zv 32)]
  else if bz.condTrue then
    wr "t" t (t.add (LVec.ofInt 32 1)) ::
      (if lastB N t then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩] else [])
  else []

def wfQ (N W : Nat) (s b t wf : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "wf" wf b]
  else if ltB N t then [wr "wf" wf (wf.shl ((LVec.ofInt 32 N).mul (LVec.ofInt 32 W)))] else []

def ubQ (N W : Nat) (s a t ub : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "ub" ub a]
  else if geB N t then [wr "ub" ub (ub.shr ((LVec.ofInt 32 N).mul (LVec.ofInt 32 W)))] else []

def dsQ (N W : Nat) (s dt : LVec) (k e : Nat) : NbaQueue2 :=
  if s.condTrue then [("dat", (base N k + e) * W, (zv W).resizeU W)]
  else [("dat", (base N k + e) * W, (dt.extract ((base N k + e + 1) * W) W).resizeU W)]

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

def dtQ (N W AccW : Nat) (s t ub : LVec) (k : Nat) : NbaQueue2 :=
  if s.condTrue then [("dat", (base N k + N + k - 1) * AccW, (zv AccW).resizeU AccW)]
  else if geB N t then
    [("dat", (base N k + N + k - 1) * AccW, ((sxv ub AccW (k * W) W).resizeU AccW).resizeU AccW)]
  else [("dat", (base N k + N + k - 1) * AccW, (zv AccW).resizeU AccW)]

def p0Q (N W AccW : Nat) (_s t wf sh wa dt : LVec) (j : Nat) : NbaQueue2 :=
    (if ltB N t then [("wsh", j * W, (wf.extract (((N - 1) * N + j) * W) W).resizeU W)] else []) ++
    (if eqB N t then [("wac", j * AccW, ((sxv sh AccW (j * W) W).resizeU AccW).resizeU AccW)] else []) ++
    [("ps", j * AccW, ((dt.extract ((N - 1 - j) * AccW) AccW).mul (wa.extract (j * AccW) AccW)).resizeU AccW)]

def pkQ (N W AccW : Nat) (_s t sh wa dt ps : LVec) (k j : Nat) : NbaQueue2 :=
    (if ltB N t then [("wsh", ((k + 1) * N + j) * W, (sh.extract ((k * N + j) * W) W).resizeU W)] else []) ++
    (if eqB N t then [("wac", ((k + 1) * N + j) * AccW, ((sxv sh AccW (((k + 1) * N + j) * W) W).resizeU AccW).resizeU AccW)]
      else []) ++
    [("ps", ((k + 1) * N + j) * AccW,
      ((ps.extract ((k * N + j) * AccW) AccW).add
        ((dt.extract ((base N (k + 1) + N - 1 - j) * AccW) AccW).mul (wa.extract (((k + 1) * N + j) * AccW) AccW))).resizeU
          AccW)]

def arQ (N AccW : Nat) (s bz t c : LVec) (i j : Nat) : NbaQueue2 :=
  if s.condTrue then [("C", (i * N + j) * AccW, (zv AccW).resizeU AccW)]
  else if bz.condTrue then
    if loB N j t then
      if hiB N j t then [("C", (i * N + j) * AccW, (c.extract (((i + 1) * N + j) * AccW) AccW).resizeU AccW)]
      else []
    else []
  else []

def alQ (N AccW : Nat) (s bz t c ps : LVec) (j : Nat) : NbaQueue2 :=
  if s.condTrue then [("C", ((N - 1) * N + j) * AccW, (zv AccW).resizeU AccW)]
  else if bz.condTrue then
    if loB N j t then
      if hiB N j t then
        [("C", ((N - 1) * N + j) * AccW,
          ((c.extract (j * AccW) AccW).add (ps.extract (((N - 1) * N + j) * AccW) AccW)).resizeU AccW)]
      else []
    else []
  else []

section run
variable (F : Nat) (hF : 30 ≤ F) (ck r s a b dn c bz t wf sh wa ub dt ps : LVec)
include hF

theorem ctrl_run (N : Nat) : runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (ctrlP N) =
    .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, ctrlQ N r s dn bz t) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : lastB N t = true <;>
    simp [ctrlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem wf_run (N W : Nat) : runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (wfP N W) =
    .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, wfQ N W s b t wf) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold wfQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : ltB N t = true <;>
    simp [wfP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, wr, h2, h3]

theorem ub_run (N W : Nat) : runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (ubP N W) =
    .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, ubQ N W s a t ub) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ubQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : geB N t = true <;>
    simp [ubP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, wr, h2, h3]

theorem ds_run (N AccW k e : Nat) : runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (dsP N AccW k e) =
    .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, dsQ N AccW s dt k e) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold dsQ
  by_cases h2 : s.condTrue = true <;>
    simp [dsP, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h2]

theorem dt_run (N W AccW k : Nat) : runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (dtP N W AccW k) =
    .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, dtQ N W AccW s t ub k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold dtQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : geB N t = true <;>
    simp [dtP, sext, sxv, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, h2, h3]

theorem p0_run (N W AccW j : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (p0P N W AccW j) =
      .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, p0Q N W AccW s t wf sh wa dt j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold p0Q
  by_cases h3 : ltB N t = true <;> by_cases h4 : eqB N t = true <;>
    simp [p0P, sext, sxv, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, SS, SvState.lookup, evalBinOp, h3, h4]

theorem pk_run (N W AccW k j : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (pkP N W AccW k j) =
      .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, pkQ N W AccW s t sh wa dt ps k j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold pkQ
  by_cases h3 : ltB N t = true <;> by_cases h4 : eqB N t = true <;>
    simp [pkP, sext, sxv, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, SS, SvState.lookup, evalBinOp, h3, h4]

theorem ar_run (N AccW i j : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (arP N AccW i j) =
      .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, arQ N AccW s bz t c i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold arQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;> by_cases h4 : loB N j t = true <;>
    by_cases h5 : hiB N j t = true <;>
    simp [arP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h2, h3, h4, h5]

theorem al_run (N AccW j : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c bz t wf sh wa ub dt ps) [] (alP N AccW j) =
      .ok (SS ck r s a b dn c bz t wf sh wa ub dt ps, alQ N AccW s bz t c ps j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold alQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;> by_cases h4 : loB N j t = true <;>
    by_cases h5 : hiB N j t = true <;>
    simp [alP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, h2, h3, h4, h5]

end run

def dsQs (N AccW : Nat) (s dt : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun k => (List.range (N + k - 1)).flatMap (dsQ N AccW s dt k)
def dtQs (N W AccW : Nat) (s t ub : LVec) : NbaQueue2 := (List.range N).flatMap (dtQ N W AccW s t ub)
def p0Qs (N W AccW : Nat) (s t wf sh wa dt : LVec) : NbaQueue2 := (List.range N).flatMap (p0Q N W AccW s t wf sh wa dt)
def pkQs (N W AccW : Nat) (s t sh wa dt ps : LVec) : NbaQueue2 :=
  (List.range (N - 1)).flatMap fun k => (List.range N).flatMap (pkQ N W AccW s t sh wa dt ps k)
def arQs (N AccW : Nat) (s bz t c : LVec) : NbaQueue2 :=
  (List.range (N - 1)).flatMap fun i => (List.range N).flatMap (arQ N AccW s bz t c i)
def alQs (N AccW : Nat) (s bz t c ps : LVec) : NbaQueue2 := (List.range N).flatMap (alQ N AccW s bz t c ps)

/-- The cycle's updates, in process order. -/
def Q (N W AccW : Nat) (r s a b dn c bz t wf sh wa ub dt ps : LVec) : NbaQueue2 :=
  ctrlQ N r s dn bz t ++ wfQ N W s b t wf ++ ubQ N W s a t ub ++
    (dsQs N AccW s dt ++ dtQs N W AccW s t ub ++ p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps ++
      arQs N AccW s bz t c ++ alQs N AccW s bz t c ps)

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def tpNext (N W AccW : Nat) (ck r s a b dn c bz t wf sh wa ub dt ps : LVec) : SvState :=
  commitNba2 (SS ck r s a b dn c bz t wf sh wa ub dt ps) (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps)

theorem apply_tp (N W AccW : Nat) (e : SvState) (ck r s a b dn c bz t wf sh wa ub dt ps : LVec) :
    applyInputs2 (tpD N W AccW) e (SS ck r s a b dn c bz t wf sh wa ub dt ps) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c bz t wf sh wa ub dt ps := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [tpD, tpDecls, SS, appIn, h1, h2, h3, h4, h5, SvState.set]

theorem tp_mem' {N W AccW : Nat} {p : Process2} (hp : p ∈ (tpD N W AccW).processes.toList) :
    p = ctrlP N ∨ p = wfP N W ∨ p = ubP N W ∨ (∃ k e, k < N ∧ e < N + k - 1 ∧ p = dsP N AccW k e) ∨
      (∃ k, k < N ∧ p = dtP N W AccW k) ∨ (∃ j, j < N ∧ p = p0P N W AccW j) ∨
      (∃ k j, k < N - 1 ∧ j < N ∧ p = pkP N W AccW k j) ∨ (∃ i j, i < N - 1 ∧ j < N ∧ p = arP N AccW i j) ∨
      (∃ j, j < N ∧ p = alP N AccW j) := tp_mem (by simpa [tpD] using hp)

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus, any state of
the design's shape, every fuel from 30). -/
theorem tp_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle) (e : SvState)
    (ck r s a b dn c bz t wf sh wa ub dt ps : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (SS ck r s a b dn c bz t wf sh wa ub dt ps) kk =
      .ok (tpNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c bz t wf sh wa ub dt ps, kk + 3) := by
  have hedge : ∀ p ∈ (tpD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    rcases tp_mem' hp with rfl | rfl | rfl | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  rw [tp_sem_eq N W AccW hN hW hA, cycleStep2_profile (tp_profile N W AccW hN) σ e _ kk ?_ ?_ (by omega), apply_tp,
    clockStep, flatMap_ffUpd F _ hedge]
  · simp only [tpD, genPs, dsPs, dtPs, p0Ps, pkPs, arPs, alPs, List.toList_toArray, List.flatMap_cons,
      List.flatMap_append, ctrl_run F hF, wf_run F hF, ub_run F hF, List.flatMap_map, ds_run F hF, dt_run F hF,
      p0_run F hF, pk_run F hF, ar_run F hF, al_run F hF, List.flatMap_assoc, tpNext, Q, dsQs, dtQs, p0Qs, pkQs,
      arQs, alQs, List.append_assoc]
  · intro i p hp
    rw [apply_tp]
    rcases tp_mem' (List.mem_of_getElem? (by simpa using hp)) with rfl | rfl | rfl | ⟨k, e, _, _, rfl⟩ |
      ⟨k, _, rfl⟩ | ⟨j, _, rfl⟩ | ⟨k, j, _, _, rfl⟩ | ⟨i, j, _, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N⟩
    · exact ⟨_, wf_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, ub_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, ds_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW k e⟩
    · exact ⟨_, dt_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW k⟩
    · exact ⟨_, p0_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW j⟩
    · exact ⟨_, pk_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW k j⟩
    · exact ⟨_, ar_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW i j⟩
    · exact ⟨_, al_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW j⟩
  · rw [apply_tp]; simp [SS]

/-! ## 3. The commit, register by register -/

section commit
variable {ck r s a b dn c bz t wf sh wa ub dt ps : LVec} {lo : Nat} {v : LVec}
theorem nb_dn : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("done", lo, v) =
    SS ck r s a b (dn.insertAt lo v) c bz t wf sh wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("C", lo, v) =
    SS ck r s a b dn (c.insertAt lo v) bz t wf sh wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_bz : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("busy", lo, v) =
    SS ck r s a b dn c (bz.insertAt lo v) t wf sh wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_t : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("t", lo, v) =
    SS ck r s a b dn c bz (t.insertAt lo v) wf sh wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_wf : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("wf", lo, v) =
    SS ck r s a b dn c bz t (wf.insertAt lo v) sh wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_sh : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("wsh", lo, v) =
    SS ck r s a b dn c bz t wf (sh.insertAt lo v) wa ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_wa : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("wac", lo, v) =
    SS ck r s a b dn c bz t wf sh (wa.insertAt lo v) ub dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_ub : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("ub", lo, v) =
    SS ck r s a b dn c bz t wf sh wa (ub.insertAt lo v) dt ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_dt : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("dat", lo, v) =
    SS ck r s a b dn c bz t wf sh wa ub (dt.insertAt lo v) ps := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_ps : nbaStep (SS ck r s a b dn c bz t wf sh wa ub dt ps) ("ps", lo, v) =
    SS ck r s a b dn c bz t wf sh wa ub dt (ps.insertAt lo v) := by simp [nbaStep, SS, SvState.lookup, SvState.set]
end commit

/-- The ten registers. -/
abbrev RegName (n : String) : Prop :=
  n = "done" ∨ n = "C" ∨ n = "busy" ∨ n = "t" ∨ n = "wf" ∨ n = "wsh" ∨ n = "wac" ∨ n = "ub" ∨ n = "dat" ∨ n = "ps"

/-- Committing a queue of writes to the ten registers. -/
theorem commit_SS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c bz t wf sh wa ub dt ps : LVec),
    (∀ u ∈ q, RegName u.1) →
    commitNba2 (SS ck r s a b dn c bz t wf sh wa ub dt ps) q =
      SS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "busy" q bz) (nbaFold "t" q t)
        (nbaFold "wf" q wf) (nbaFold "wsh" q sh) (nbaFold "wac" q wa) (nbaFold "ub" q ub) (nbaFold "dat" q dt)
        (nbaFold "ps" q ps)
  | [], _, _, _, _, _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, bz, t, wf, sh, wa, ub, dt, ps, h => by
    have hq := @commit_SS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;>
      subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_bz, nb_t, nb_wf, nb_sh, nb_wa, nb_ub, nb_dt, nb_ps,
        hq _ _ _ _ _ _ _ _ _ _ h', nbaFold]

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 := h u List.mem_cons_self
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

section names
variable {N W AccW : Nat} {r s a b dn c bz t wf sh wa ub dt ps : LVec}

theorem ctrlQ_names : ∀ u ∈ ctrlQ N r s dn bz t, u.1 = "busy" ∨ u.1 = "done" ∨ u.1 = "t" := by
  intro u hu; unfold ctrlQ at hu; (repeat' split at hu) <;> simp at hu <;>
    (try rcases hu with rfl | rfl | rfl) <;> (try rcases hu with rfl | rfl) <;> simp
theorem wfQ_names : ∀ u ∈ wfQ N W s b t wf, u.1 = "wf" := by
  intro u hu; unfold wfQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem ubQ_names : ∀ u ∈ ubQ N W s a t ub, u.1 = "ub" := by
  intro u hu; unfold ubQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem datQ_names : ∀ u ∈ dsQs N AccW s dt ++ dtQs N W AccW s t ub, u.1 = "dat" := by
  intro u hu
  simp only [dsQs, dtQs, List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨k, -, e, -, hu⟩ | ⟨k, -, hu⟩
  · unfold dsQ at hu; split at hu <;> simp at hu <;> subst hu <;> rfl
  · unfold dtQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem peQ_names : ∀ u ∈ p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps,
    u.1 = "wsh" ∨ u.1 = "wac" ∨ u.1 = "ps" := by
  intro u hu
  simp only [p0Qs, pkQs, List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨j, -, hu⟩ | ⟨k, -, j, -, hu⟩
  · unfold p0Q at hu; (repeat' split at hu) <;> simp at hu <;> (repeat' rcases hu with rfl | hu) <;>
      (try subst hu) <;> simp
  · unfold pkQ at hu; (repeat' split at hu) <;> simp at hu <;> (repeat' rcases hu with rfl | hu) <;>
      (try subst hu) <;> simp
theorem cQ_names : ∀ u ∈ arQs N AccW s bz t c ++ alQs N AccW s bz t c ps, u.1 = "C" := by
  intro u hu
  simp only [arQs, alQs, List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨i, -, j, -, hu⟩ | ⟨j, -, hu⟩
  · unfold arQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
  · unfold alQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl

theorem Q_names : ∀ u ∈ Q N W AccW r s a b dn c bz t wf sh wa ub dt ps, RegName u.1 := by
  intro u hu
  have e : Q N W AccW r s a b dn c bz t wf sh wa ub dt ps =
      ctrlQ N r s dn bz t ++ wfQ N W s b t wf ++ ubQ N W s a t ub ++
        ((dsQs N AccW s dt ++ dtQs N W AccW s t ub) ++ (p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps) ++
          (arQs N AccW s bz t c ++ alQs N AccW s bz t c ps)) := by simp only [Q, List.append_assoc]
  rw [e] at hu
  simp only [List.mem_append] at hu
  rcases hu with ((hu | hu) | hu) | ((hu | hu) | hu)
  · rcases ctrlQ_names u hu with h | h | h <;> rw [h] <;> simp [RegName]
  · rw [wfQ_names u hu]; simp [RegName]
  · rw [ubQ_names u hu]; simp [RegName]
  · rw [datQ_names u (List.mem_append.mpr hu)]; simp [RegName]
  · rcases peQ_names u (List.mem_append.mpr hu) with h | h | h <;> rw [h] <;> simp [RegName]
  · rw [cQ_names u (List.mem_append.mpr hu)]; simp [RegName]

theorem skip_of {q : NbaQueue2} {ns : List String} {n : String} (hq : ∀ u ∈ q, u.1 ∈ ns) (hn : n ∉ ns) (x : LVec) :
    nbaFold n q x = x :=
  nbaFold_of_forall_ne (fun u hu h => hn (by rw [← h]; exact hq u hu)) x

theorem skip_ctrl {n : String} (h1 : n ≠ "busy") (h2 : n ≠ "done") (h3 : n ≠ "t") (x : LVec) :
    nbaFold n (ctrlQ N r s dn bz t) x = x :=
  skip_of (ns := ["busy", "done", "t"]) (fun u hu => by rcases ctrlQ_names u hu with h | h | h <;> simp [h])
    (by simp [h1, h2, h3]) x
theorem skip_wf {n : String} (h : n ≠ "wf") (x : LVec) : nbaFold n (wfQ N W s b t wf) x = x :=
  skip_of (ns := ["wf"]) (fun u hu => by simp [wfQ_names u hu]) (by simp [h]) x
theorem skip_ub {n : String} (h : n ≠ "ub") (x : LVec) : nbaFold n (ubQ N W s a t ub) x = x :=
  skip_of (ns := ["ub"]) (fun u hu => by simp [ubQ_names u hu]) (by simp [h]) x
theorem skip_dat {n : String} (h : n ≠ "dat") (x : LVec) : nbaFold n (dsQs N AccW s dt ++ dtQs N W AccW s t ub) x = x :=
  skip_of (ns := ["dat"]) (fun u hu => by simp [datQ_names u hu]) (by simp [h]) x
theorem skip_pe {n : String} (h1 : n ≠ "wsh") (h2 : n ≠ "wac") (h3 : n ≠ "ps") (x : LVec) :
    nbaFold n (p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps) x = x :=
  skip_of (ns := ["wsh", "wac", "ps"]) (fun u hu => by rcases peQ_names u hu with h | h | h <;> simp [h])
    (by simp [h1, h2, h3]) x
theorem skip_C {n : String} (h : n ≠ "C") (x : LVec) : nbaFold n (arQs N AccW s bz t c ++ alQs N AccW s bz t c ps) x = x :=
  skip_of (ns := ["C"]) (fun u hu => by simp [cQ_names u hu]) (by simp [h]) x

/-- The registers of each group, and which part of the queue writes them. -/
theorem fold_Q (n : String) (x : LVec) : nbaFold n (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x =
    nbaFold n (arQs N AccW s bz t c ++ alQs N AccW s bz t c ps)
      (nbaFold n (p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps)
        (nbaFold n (dsQs N AccW s dt ++ dtQs N W AccW s t ub)
          (nbaFold n (ubQ N W s a t ub) (nbaFold n (wfQ N W s b t wf) (nbaFold n (ctrlQ N r s dn bz t) x))))) := by
  simp only [Q, nbaFold_append, List.append_assoc]

theorem fold_ctrl (n : String) (h1 : n ≠ "wf" := by decide) (h2 : n ≠ "ub" := by decide) (h3 : n ≠ "dat" := by decide)
    (h4 : n ≠ "wsh" := by decide) (h5 : n ≠ "wac" := by decide) (h6 : n ≠ "ps" := by decide)
    (h7 : n ≠ "C" := by decide) (x : LVec) :
    nbaFold n (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x = nbaFold n (ctrlQ N r s dn bz t) x := by
  rw [fold_Q, skip_C h7, skip_pe h4 h5 h6, skip_dat h3, skip_ub h2, skip_wf h1]

theorem fold_wf (x : LVec) :
    nbaFold "wf" (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x = nbaFold "wf" (wfQ N W s b t wf) x := by
  rw [fold_Q, skip_C (by decide), skip_pe (by decide) (by decide) (by decide), skip_dat (by decide),
    skip_ub (by decide), skip_ctrl (by decide) (by decide) (by decide)]

theorem fold_ub (x : LVec) :
    nbaFold "ub" (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x = nbaFold "ub" (ubQ N W s a t ub) x := by
  rw [fold_Q, skip_C (by decide), skip_pe (by decide) (by decide) (by decide), skip_dat (by decide),
    skip_wf (by decide), skip_ctrl (by decide) (by decide) (by decide)]

theorem fold_dat (x : LVec) :
    nbaFold "dat" (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x =
      nbaFold "dat" (dsQs N AccW s dt ++ dtQs N W AccW s t ub) x := by
  rw [fold_Q, skip_C (by decide), skip_pe (by decide) (by decide) (by decide), skip_ub (by decide),
    skip_wf (by decide), skip_ctrl (by decide) (by decide) (by decide)]

theorem fold_pe (n : String) (h1 : n ≠ "C" := by decide) (h2 : n ≠ "dat" := by decide)
    (h3 : n ≠ "ub" := by decide) (h4 : n ≠ "wf" := by decide) (h5 : n ≠ "busy" := by decide)
    (h6 : n ≠ "done" := by decide) (h7 : n ≠ "t" := by decide) (x : LVec) :
    nbaFold n (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x =
      nbaFold n (p0Qs N W AccW s t wf sh wa dt ++ pkQs N W AccW s t sh wa dt ps) x := by
  rw [fold_Q, skip_C h1, skip_dat h2, skip_ub h3, skip_wf h4, skip_ctrl h5 h6 h7]

theorem fold_C (x : LVec) :
    nbaFold "C" (Q N W AccW r s a b dn c bz t wf sh wa ub dt ps) x =
      nbaFold "C" (arQs N AccW s bz t c ++ alQs N AccW s bz t c ps) x := by
  rw [fold_Q, skip_pe (by decide) (by decide) (by decide), skip_dat (by decide), skip_ub (by decide),
    skip_wf (by decide), skip_ctrl (by decide) (by decide) (by decide)]

end names

/-! ## 4. Register families entry by entry -/

/-- A queue's writes to `n` are entries `r < M` of width `w`, entry `r` written with the value `g r`. -/
def EntW (n : String) (w M : Nat) (g : Nat → BitVec w) (q : NbaQueue2) : Prop :=
  ∀ u ∈ q, u.1 = n → ∃ r, r < M ∧ u.2.1 = r * w ∧ u.2.2 = LVec.ofBitVec (g r)

theorem EntW.tail {n : String} {w M : Nat} {g : Nat → BitVec w} {u : String × Nat × LVec} {q : NbaQueue2}
    (h : EntW n w M g (u :: q)) : EntW n w M g q := fun u' hu' => h u' (List.mem_cons_of_mem _ hu')

theorem EntW.append {n : String} {w M : Nat} {g : Nat → BitVec w} {q q' : NbaQueue2} (h : EntW n w M g q)
    (h' : EntW n w M g q') : EntW n w M g (q ++ q') := by
  intro u hu; rcases List.mem_append.mp hu with hu | hu
  · exact h u hu
  · exact h' u hu

/-- An entry no write of the queue reaches keeps its value. -/
theorem fold_unwritten {n : String} {w M : Nat} {g : Nat → BitVec w} {r : Nat} :
    ∀ {q : NbaQueue2}, EntW n w M g q → (∀ u ∈ q, u.1 = n → u.2.1 ≠ r * w) → ∀ x : LVec,
      (nbaFold n q x).extract (r * w) w = x.extract (r * w) w
  | [], _, _, _ => rfl
  | u :: q, hq, hn, x => by
    have hn' := fun u' hu' => hn u' (List.mem_cons_of_mem _ hu')
    show (nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x)).extract _ _ = _
    rw [fold_unwritten hq.tail hn']
    split
    · rename_i h
      obtain ⟨r', -, h1, h2⟩ := hq u List.mem_cons_self h
      have hne : r' ≠ r := fun e => hn u List.mem_cons_self h (by rw [h1, e])
      rw [h1, h2]
      apply LVec.extract_insertAt_of_disjoint
      simp only [LVec.width_ofBitVec]
      rcases Nat.lt_or_gt_of_ne hne with h3 | h3
      · right; exact rowMajor_le h3
      · left; exact rowMajor_le h3
    · rfl

/-- An entry the queue writes holds the written value. -/
theorem fold_written {n : String} {w M : Nat} {g : Nat → BitVec w} {r : Nat} (hw : 0 < w) (hr : r < M) :
    ∀ {q : NbaQueue2}, EntW n w M g q → (∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w) → ∀ x : LVec, x.width = M * w →
      (nbaFold n q x).extract (r * w) w = LVec.ofBitVec (g r)
  | [], _, ⟨_, h, _⟩, _, _ => absurd h List.not_mem_nil
  | u :: q, hq, hex, x, hx => by
    show (nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x)).extract _ _ = _
    by_cases hin : ∃ u' ∈ q, u'.1 = n ∧ u'.2.1 = r * w
    · exact fold_written hw hr hq.tail hin _ (by split <;> simp [hx])
    · have hn' : ∀ u' ∈ q, u'.1 = n → u'.2.1 ≠ r * w := fun u' hu' h1 h2 => hin ⟨u', hu', h1, h2⟩
      rw [fold_unwritten hq.tail hn']
      obtain ⟨u0, hu0, h1, h2⟩ := hex
      rcases List.mem_cons.mp hu0 with rfl | hu0
      · obtain ⟨r', -, h3, h4⟩ := hq u0 List.mem_cons_self h1
        have hrr : r' = r := Nat.eq_of_mul_eq_mul_right hw (h3.symm.trans h2)
        subst hrr
        rw [if_pos h1, h3, h4]
        exact LVec.extract_insertAt_self (by simp) (by rw [hx]; exact winle w hr)
      · exact absurd ⟨u0, hu0, h1, h2⟩ hin

/-- A vector whose every entry is known is the packed family of the entries. -/
theorem ent_eq {w M : Nat} {v : LVec} (f : Nat → BitVec w) (hv : v.width = M * w)
    (h : ∀ r, r < M → v.extract (r * w) w = LVec.ofBitVec (f r)) : v = LVec.ofBitVec (packBV w M f) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨hv, fun i hi => ?_⟩
  have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hr : i / w < M := (Nat.div_lt_iff_lt_mul hw).mpr hi
  have hd : i / w * w + i % w = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i w
  have hj : i % w < w := Nat.mod_lt i hw
  have h1 := congrArg (fun x : LVec => x.bits[i % w]?) (h (i / w) hr)
  simp only [LVec.getElem?_extract, if_pos hj, LVec.getElem?_ofBitVec] at h1
  rw [hd] at h1
  have hlt : i < v.bits.size := by show i < v.width; rw [hv]; exact hi
  have hp := getLsbD_bvInsertEntries f (0#(M * w)) M (Nat.le_refl _) (i / w) (i % w) hr hj
  rw [hd] at hp
  rw [Array.getElem?_eq_getElem hlt] at h1 ⊢
  simp only [Option.getD_some, Option.some.injEq] at h1
  rw [h1, packBV, hp]

/-- Entry `r` of a known packed family. -/
theorem ext_pack {w M r : Nat} (f : Nat → BitVec w) (hr : r < M) :
    (LVec.ofBitVec (packBV w M f)).extract (r * w) w = LVec.ofBitVec (f r) :=
  extract_ofBitVec_packBV f hr rfl

/-! ## 5. The closed forms, `t` steps after a start -/

attribute [local simp] condTrue_knownBit

/-- `Σ_{k' < m} A[i][k']·B[k'][j]` in the integers (`Tasks.Matmul.dot` at `m = N`). -/
def psum (N W : Nat) {n : Nat} (A B : BitVec n) (m i j : Nat) : Int :=
  (List.range m).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (m i j : Nat) : psum N W A B (m + 1) i j =
    psum N W A B m i j + Tasks.Matmul.entry W A (i * N + m) * Tasks.Matmul.entry W B (m * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem psum_zero (N W : Nat) {n : Nat} (A B : BitVec n) (i j : Nat) : psum N W A B 0 i j = 0 := rfl

/-- The row of the data triangle that holds offset `r`, among rows `< m`. -/
def rowOf (N : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, r => if base N m ≤ r then m else rowOf N m r

theorem rowOf_base (N : Nat) {k e : Nat} (he : e < N + k) : ∀ m, k < m → rowOf N m (base N k + e) = k
  | 0, h => absurd h (Nat.not_lt_zero _)
  | m + 1, h => by
    simp only [rowOf]
    by_cases hm : base N m ≤ base N k + e
    · rw [if_pos hm]
      refine Nat.le_antisymm ?_ (by omega)
      refine Nat.le_of_not_lt fun hlt => ?_
      have h1 := base_mono N (show k + 1 ≤ m by omega)
      rw [base_succ] at h1
      omega
    · rw [if_neg hm]
      refine rowOf_base N he m ?_
      refine Nat.lt_of_le_of_ne (by omega) fun hkm => ?_
      subst hkm; omega

theorem tri_cover (N : Nat) : ∀ m r, r < base N m → ∃ k e, k < m ∧ e < N + k ∧ r = base N k + e
  | 0, r, h => by simp [base] at h
  | m + 1, r, h => by
    rw [base_succ] at h
    by_cases hr : r < base N m
    · obtain ⟨k, e, hk, he, rfl⟩ := tri_cover N m r hr; exact ⟨k, e, by omega, he, rfl⟩
    · exact ⟨m, r - base N m, by omega, by omega, by omega⟩

section vals
variable (N W AccW : Nat) (A B : BitVec (N * N * W))

/-- `A[x - v][k]` as an entry, `0` outside the matrix. -/
def aPat (k x v : Nat) : BitVec W :=
  if v ≤ x ∧ x - v < N then A.extractLsb' (((x - v) * N + k) * W) W else 0

/-- Offset `r` of the data rows `t` steps on: entry `e` of row `k` holds `A[t + e - 2N - k][k]`. -/
def datE (t r : Nat) : BitVec AccW :=
  (aPat N W A (rowOf N N r) (t + (r - base N (rowOf N N r))) (2 * N + rowOf N N r)).signExtend AccW

def wfV (t : Nat) : BitVec (N * N * W) := B <<< (min t N * (N * W))
def ubV (t : Nat) : BitVec (N * N * W) := A >>> ((t - N) * (N * W))
def datV (t : Nat) : BitVec (DW N * AccW) := packBV AccW (DW N) (datE N W AccW A t)
def shV (t : Nat) : BitVec (N * N * W) := B >>> ((N - min t N) * (N * W))
def waV (t : Nat) : BitVec (N * N * W) := if t ≤ N then 0 else B

/-- PE `(k, j)`'s partial sum `t` steps on: row `t - (N + 2 + k + j)` of `A` up to `k`, `0` outside. -/
def psI (t k j : Nat) : Int :=
  if N + 2 + k + j ≤ t ∧ t - (N + 2 + k + j) < N then psum N W A B (k + 1) (t - (N + 2 + k + j)) j else 0

def psV (t : Nat) : BitVec (N * N * AccW) :=
  packBV AccW (N * N) fun r => BitVec.ofInt AccW (psI N W A B t (r / N) (r % N))

/-- The rows column `j`'s accumulators hold `t` steps on. -/
def nC (t j : Nat) : Nat := min N (t - (2 * N + 1 + j))

def cE (t i j : Nat) : BitVec AccW :=
  if N - nC N t j ≤ i then BitVec.ofInt AccW (psum N W A B N (i - (N - nC N t j)) j) else 0

def cV (t : Nat) : BitVec (N * N * AccW) := packBV AccW (N * N) fun r => cE N W AccW A B t (r / N) (r % N)

end vals

theorem datE_at (N W AccW : Nat) (A : BitVec (N * N * W)) (t : Nat) {k e : Nat} (hk : k < N) (he : e < N + k) :
    datE N W AccW A t (base N k + e) = (aPat N W A k (t + e) (2 * N + k)).signExtend AccW := by
  rw [datE, rowOf_base N he N hk, Nat.add_sub_cancel_left]

/-! ### `BitVec` and `LVec` facts -/

theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft, LVec.getElem?_ofBitVec]
  by_cases h : i < y.toNat
  · simp [h, Logic.ofBool]
  · simp [h, show i - y.toNat < w by omega]

theorem extractLsb'_shiftLeft {n : Nat} (x : BitVec n) {s lo m : Nat} (h : s ≤ lo) (hm : lo + m ≤ n) :
    (x <<< s).extractLsb' lo m = x.extractLsb' (lo - s) m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rw [show lo - s + i = lo + i - s by omega]
  simp [show lo + i < n by omega, show ¬ lo + i < s by omega]

theorem extractLsb'_of_ge {n : Nat} (x : BitVec n) {lo m : Nat} (h : n ≤ lo) : x.extractLsb' lo m = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_of_ge x _ (by omega)]; simp

theorem sxv_known {n : Nat} (X : BitVec n) {AccW lo W : Nat} (hW : 1 ≤ W) (h : lo + W ≤ n) :
    sxv (LVec.ofBitVec X) AccW lo W = LVec.ofBitVec ((X.extractLsb' lo W).signExtend (AccW + W)) := by
  unfold sxv
  simp only [LVec.extract_ofBitVec _ (show lo + W - 1 + 1 ≤ n by omega), LVec.extract_ofBitVec _ h,
    LVec.concatMany_singleton, LVec.replVec_ofBitVec, LVec.concatMany_cons_cons, LVec.concat_ofBitVec]
  exact LVec.ofBitVec_replicate_append_eq_signExtend hW X AccW rfl

theorem setWidth_mul_signExtend {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := Lib.setWidth_add_mul_signExtend h 0#m a b
  simpa using this

theorem sext_mul {w m : Nat} (a b : BitVec w) :
    a.signExtend m * b.signExtend m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := setWidth_mul_signExtend (Nat.le_refl m) a b
  simpa using this

theorem zv_eq (w : Nat) : zv w = LVec.ofBitVec 0#w := LVec.replicate_l0 w

theorem ofInt32 {v : Nat} (h : v < 2 ^ 31) : LVec.ofInt 32 (v : Int) = LVec.ofBitVec (BitVec.ofNat 32 v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

/-- A vector is the packed family of its own entries. -/
theorem pack_self {w M : Nat} (X : BitVec (M * w)) : packBV w M (fun r => X.extractLsb' (r * w) w) = X := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hr : i / w < M := (Nat.div_lt_iff_lt_mul hw).mpr hi
  have hd : i / w * w + i % w = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i w
  have hp := getLsbD_bvInsertEntries (fun r => X.extractLsb' (r * w) w) (0#(M * w)) M (Nat.le_refl _) (i / w) (i % w)
    hr (Nat.mod_lt i hw)
  rw [hd] at hp
  rw [packBV, hp, BitVec.getLsbD_extractLsb', decide_eq_true (Nat.mod_lt i hw), Bool.true_and, hd]

/-- **A family's commit**: every write to `n` is an entry of the target `X`, and every entry is written or already
holds `X`'s value. -/
theorem fold_family {n : String} {w M : Nat} (hw : 0 < w) (X : BitVec (M * w)) {q : NbaQueue2} {x : LVec}
    (hx : x.width = M * w)
    (hq : ∀ u ∈ q, u.1 = n → ∃ r, r < M ∧ u.2.1 = r * w ∧ u.2.2 = LVec.ofBitVec (X.extractLsb' (r * w) w))
    (hcov : ∀ r, r < M → (∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w) ∨
      x.extract (r * w) w = LVec.ofBitVec (X.extractLsb' (r * w) w)) :
    nbaFold n q x = LVec.ofBitVec X := by
  have hE : EntW n w M (fun r => X.extractLsb' (r * w) w) q := hq
  rw [← pack_self X]
  refine ent_eq _ (by rw [width_nbaFold, hx]) fun r hr => ?_
  by_cases hex : ∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w
  · exact fold_written hw hr hE hex x hx
  · have hn : ∀ u ∈ q, u.1 = n → u.2.1 ≠ r * w := fun u hu h1 h2 => hex ⟨u, hu, h1, h2⟩
    rw [fold_unwritten hE hn x]
    exact (hcov r hr).resolve_left hex

/-- A write of a whole register with a known value of its width. -/
theorem fold_whole {n : String} {w : Nat} (old : LVec) (y : BitVec w) (h : old.width = w) :
    nbaFold n [(n, 0, (LVec.ofBitVec y).resizeU old.width)] old = LVec.ofBitVec y := by
  simp only [nbaFold, List.foldl_cons, List.foldl_nil, if_true, h, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  exact LVec.insertAt_zero_of_width_eq (by simp [h])

/-- Entry `q` of an `N × N` matrix, `0` past its end. -/
def ent (N W : Nat) (X : BitVec (N * N * W)) (q : Nat) : BitVec W :=
  if q < N * N then X.extractLsb' (q * W) W else 0

theorem ent_shr (N W : Nat) (X : BitVec (N * N * W)) (m r : Nat) :
    (X >>> (m * (N * W))).extractLsb' (r * W) W = ent N W X (m * N + r) := by
  rw [Lib.extractLsb'_ushiftRight, show m * (N * W) + r * W = (m * N + r) * W by
    rw [Nat.add_mul, Nat.mul_assoc]]
  unfold ent
  split
  · rfl
  · exact extractLsb'_of_ge X (Nat.mul_le_mul_right W (by omega))

theorem ent_shl (N W : Nat) (X : BitVec (N * N * W)) {s r : Nat} (hs : s * N ≤ r) (hr : r < N * N) :
    (X <<< (s * (N * W))).extractLsb' (r * W) W = ent N W X (r - s * N) := by
  rw [extractLsb'_shiftLeft X (by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right W hs) (winle W hr)]
  unfold ent
  rw [if_pos (by omega), show r * W - s * (N * W) = (r - s * N) * W by rw [Nat.sub_mul, Nat.mul_assoc]]

theorem ent_self (N W : Nat) (X : BitVec (N * N * W)) {r : Nat} (hr : r < N * N) :
    X.extractLsb' (r * W) W = ent N W X r := by
  unfold ent; rw [if_pos hr]

/-! ### Range facts -/

structure Rng (N W AccW : Nat) : Prop where
  hN : 1 ≤ N
  hW : 1 ≤ W
  hA : 1 ≤ AccW
  hNW : N * N * W < 2 ^ 31
  hNA : N * N * AccW < 2 ^ 31

theorem Rng.hNN {N W AccW : Nat} (h : Rng N W AccW) : N * N < 2 ^ 31 := by
  have := Nat.le_mul_of_pos_right (N * N) h.hW; have := h.hNW; omega

theorem Rng.hN16 {N W AccW : Nat} (h : Rng N W AccW) : N < 2 ^ 16 := by
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.mul_le_mul hc hc; have := h.hNN; omega

theorem Rng.hNW' {N W AccW : Nat} (h : Rng N W AccW) : N * W < 2 ^ 31 := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ h.hN
  have := h.hNW; omega

theorem Rng.hW31 {N W AccW : Nat} (h : Rng N W AccW) : W < 2 ^ 31 := by
  have h1 : W ≤ N * W := Nat.le_mul_of_pos_left _ h.hN
  have := h.hNW'; omega

/-! ### The step tests on a known counter -/

abbrev tv (t : Nat) : LVec := LVec.ofBitVec (BitVec.ofNat 32 t)

theorem ofInt_cast32 (v : Nat) : LVec.ofInt 32 (v : Int) = LVec.ofBitVec (BitVec.ofNat 32 v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem cmp_lt {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (LVec.ofLogic ((tv a).lt (tv b))).condTrue = decide (a < b) := by
  simp [LVec.ofLogic_ofBool, BitVec.lt_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a < b <;> simp [hab]

theorem cmp_le {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (LVec.ofLogic ((tv a).le (tv b))).condTrue = decide (a ≤ b) := by
  simp [LVec.ofLogic_ofBool, BitVec.le_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : a ≤ b <;> simp [hab]

theorem cmp_ge {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (LVec.ofLogic ((tv a).ge (tv b))).condTrue = decide (b ≤ a) := by
  simp [LVec.ofLogic_ofBool, BitVec.le_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases hab : b ≤ a <;> simp [hab]

theorem cmp_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (LVec.ofLogic ((tv a).eqLogical (tv b))).condTrue = decide (a = b) := by
  simp only [LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit]
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 32 a ≠ BitVec.ofNat 32 b := by
      intro he; apply h
      have := congrArg BitVec.toNat he
      simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    simp [h, this]

section tests
variable {N W AccW : Nat} (h : Rng N W AccW) {t : Nat} (ht : t ≤ 4 * N)
include h ht

theorem ltB_tv : ltB N (tv t) = decide (t < N) := by
  have := h.hN16; unfold ltB; rw [ofInt_cast32]; exact cmp_lt (by omega) (by omega)
theorem eqB_tv : eqB N (tv t) = decide (t = N) := by
  have := h.hN16; unfold eqB; rw [ofInt_cast32]; exact cmp_eq (by omega) (by omega)
theorem geB_tv : geB N (tv t) = decide (N ≤ t) := by
  have := h.hN16; unfold geB; rw [ofInt_cast32]; exact cmp_ge (by omega) (by omega)
theorem lastB_tv : lastB N (tv t) = decide (t = 4 * N - 1) := by
  have := h.hN16; unfold lastB; rw [ofInt_cast32]; exact cmp_eq (by omega) (by omega)
theorem loB_tv {j : Nat} (hj : j < N) : loB N j (tv t) = decide (2 * N + 1 + j ≤ t) := by
  have := h.hN16; unfold loB
  rw [show (2 * (N : Int) + 1) = ((2 * N + 1 : Nat) : Int) by push_cast; rfl, ofInt_cast32, ofInt_cast32,
    LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]
  exact cmp_ge (by omega) (by omega)
theorem hiB_tv {j : Nat} (hj : j < N) : hiB N j (tv t) = decide (t ≤ 3 * N + j) := by
  have := h.hN16; unfold hiB
  rw [show (3 * (N : Int)) = ((3 * N : Nat) : Int) by push_cast; rfl, ofInt_cast32, ofInt_cast32,
    LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]
  exact cmp_le (by omega) (by omega)

end tests

/-! ## 6. The registers through a busy cycle -/

abbrev kb (b : Bool) : LVec := knownBit b

theorem mulNW {N W AccW : Nat} (h : Rng N W AccW) :
    (LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)) = LVec.ofBitVec (BitVec.ofNat 32 (N * W)) := by
  have h1 := h.hNW'; have h2 := h.hW31; have h3 := h.hN16
  rw [ofInt_cast32, ofInt_cast32, LVec.mul_ofBitVec]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mod_eq_of_lt (show N < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show W < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show N * W < 2 ^ 32 by omega)]

theorem toNat_NW {N W AccW : Nat} (h : Rng N W AccW) : (BitVec.ofNat 32 (N * W)).toNat = N * W := by
  have := h.hNW'; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

section busy
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

theorem ctrl_busy :
    nbaFold "done" (ctrlQ N (kb false) (kb false) (kb false) (kb true) (tv t)) (kb false) =
        kb (decide (t + 1 = 4 * N)) ∧
      nbaFold "busy" (ctrlQ N (kb false) (kb false) (kb false) (kb true) (tv t)) (kb true) =
        kb (decide (t + 1 ≠ 4 * N)) ∧
      nbaFold "t" (ctrlQ N (kb false) (kb false) (kb false) (kb true) (tv t)) (tv t) = tv (t + 1) := by
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  unfold ctrlQ
  simp only [condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, lastB_tv h (Nat.le_of_lt ht), h1', LVec.add_ofBitVec,
    BitVec.ofNat_add_ofNat, decide_eq_true_eq]
  by_cases hf : t = 4 * N - 1
  · have hf' : 4 * N - 1 + 1 = 4 * N := by omega
    simp [hf, hf', nbaFold, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1]
  · have hf' : ¬ t + 1 = 4 * N := by omega
    simp [hf, hf', nbaFold, LVec.insertAt_zero_of_width_eq, BitVec.ofNat_add_ofNat]

theorem wf_busy (b : LVec) :
    nbaFold "wf" (wfQ N W (kb false) b (tv t) (.ofBitVec (wfV N W B t))) (.ofBitVec (wfV N W B t)) =
      .ofBitVec (wfV N W B (t + 1)) := by
  unfold wfQ
  rw [condTrue_knownBit, if_neg (by simp), ltB_tv h (Nat.le_of_lt ht)]
  by_cases hl : t < N
  · rw [if_pos (by simpa using hl), mulNW h, shl_ofBitVec, toNat_NW h]
    rw [fold_whole _ _ (by simp)]
    congr 1
    unfold wfV
    rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), ← BitVec.shiftLeft_add, Nat.succ_mul]
  · rw [if_neg (by simpa using hl)]
    show _ = _
    unfold wfV
    rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    rfl

theorem ub_busy (a : LVec) :
    nbaFold "ub" (ubQ N W (kb false) a (tv t) (.ofBitVec (ubV N W A t))) (.ofBitVec (ubV N W A t)) =
      .ofBitVec (ubV N W A (t + 1)) := by
  unfold ubQ
  rw [condTrue_knownBit, if_neg (by simp), geB_tv h (Nat.le_of_lt ht)]
  by_cases hl : N ≤ t
  · rw [if_pos (by simpa using hl), mulNW h, LVec.shr_ofBitVec, toNat_NW h]
    rw [fold_whole _ _ (by simp)]
    congr 1
    unfold ubV
    rw [← BitVec.shiftRight_add, show t + 1 - N = t - N + 1 by omega, Nat.succ_mul]
  · rw [if_neg (by simpa using hl)]
    unfold ubV
    rw [show t + 1 - N = t - N by omega]
    rfl

theorem mem_p0Q_busy {s wf sh wa dt : LVec} {j : Nat} {u : String × Nat × LVec} :
    u ∈ p0Q N W AccW s (tv t) wf sh wa dt j ↔
      (t < N ∧ u = ("wsh", j * W, (wf.extract (((N - 1) * N + j) * W) W).resizeU W)) ∨
      (t = N ∧ u = ("wac", j * AccW, ((sxv sh AccW (j * W) W).resizeU AccW).resizeU AccW)) ∨
      u = ("ps", j * AccW, ((dt.extract ((N - 1 - j) * AccW) AccW).mul (wa.extract (j * AccW) AccW)).resizeU AccW) := by
  unfold p0Q
  rw [ltB_tv h (Nat.le_of_lt ht), eqB_tv h (Nat.le_of_lt ht)]
  by_cases h1 : t < N <;> by_cases h2 : t = N <;> simp [h1, h2]

theorem mem_pkQ_busy {s sh wa dt ps : LVec} {k j : Nat} {u : String × Nat × LVec} :
    u ∈ pkQ N W AccW s (tv t) sh wa dt ps k j ↔
      (t < N ∧ u = ("wsh", ((k + 1) * N + j) * W, (sh.extract ((k * N + j) * W) W).resizeU W)) ∨
      (t = N ∧ u = ("wac", ((k + 1) * N + j) * AccW,
        ((sxv sh AccW (((k + 1) * N + j) * W) W).resizeU AccW).resizeU AccW)) ∨
      u = ("ps", ((k + 1) * N + j) * AccW,
        ((ps.extract ((k * N + j) * AccW) AccW).add
          ((dt.extract ((base N (k + 1) + N - 1 - j) * AccW) AccW).mul
            (wa.extract (((k + 1) * N + j) * AccW) AccW))).resizeU AccW) := by
  unfold pkQ
  rw [ltB_tv h (Nat.le_of_lt ht), eqB_tv h (Nat.le_of_lt ht)]
  by_cases h1 : t < N <;> by_cases h2 : t = N <;> simp [h1, h2]

end busy

/-! ### The PE registers through a busy cycle -/

theorem rm_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
theorem rm_mod {N i j : Nat} (hj : j < N) : (i * N + j) % N = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- Every unit `r < N·N` of a PE family is row `0`'s or row `k + 1`'s. -/
theorem pe_cover {N r : Nat} (hr : r < N * N) : r < N ∨ ∃ k j, k < N - 1 ∧ j < N ∧ r = (k + 1) * N + j := by
  by_cases h0 : r < N
  · exact .inl h0
  · right
    have hN : 0 < N := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hr
    have hd := Nat.div_add_mod r N
    have h1 : 1 ≤ r / N := (Nat.le_div_iff_mul_le hN).mpr (by omega)
    have h2 : r / N < N := (Nat.div_lt_iff_lt_mul hN).mpr hr
    refine ⟨r / N - 1, r % N, by omega, Nat.mod_lt _ hN, ?_⟩
    rw [Nat.sub_add_cancel h1, Nat.mul_comm]; omega

/-! ### Partially known register families (registers the start does not clear) -/

/-- `v` holds `f r` at every entry `r < M` with `cond r`, and any value elsewhere. -/
def PEnt (w M : Nat) (cond : Nat → Prop) (f : Nat → BitVec w) (v : LVec) : Prop :=
  v.width = M * w ∧ ∀ r, r < M → cond r → v.extract (r * w) w = LVec.ofBitVec (f r)

/-- A queue's writes to `n` are entries `r < M` of width `w`, the value `g r` wherever `cond r`. -/
def EntP (n : String) (w M : Nat) (cond : Nat → Prop) (g : Nat → BitVec w) (q : NbaQueue2) : Prop :=
  ∀ u ∈ q, u.1 = n → ∃ r, r < M ∧ u.2.1 = r * w ∧ u.2.2.width = w ∧ (cond r → u.2.2 = LVec.ofBitVec (g r))

theorem EntP.tail {n : String} {w M : Nat} {cond : Nat → Prop} {g : Nat → BitVec w} {u : String × Nat × LVec}
    {q : NbaQueue2} (h : EntP n w M cond g (u :: q)) : EntP n w M cond g q :=
  fun u' hu' => h u' (List.mem_cons_of_mem _ hu')

theorem foldP_unwritten {n : String} {w M : Nat} {cond : Nat → Prop} {g : Nat → BitVec w} {r : Nat} :
    ∀ {q : NbaQueue2}, EntP n w M cond g q → (∀ u ∈ q, u.1 = n → u.2.1 ≠ r * w) → ∀ x : LVec,
      (nbaFold n q x).extract (r * w) w = x.extract (r * w) w
  | [], _, _, _ => rfl
  | u :: q, hq, hn, x => by
    have hn' := fun u' hu' => hn u' (List.mem_cons_of_mem _ hu')
    show (nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x)).extract _ _ = _
    rw [foldP_unwritten hq.tail hn']
    split
    · rename_i h
      obtain ⟨r', -, h1, h2, -⟩ := hq u List.mem_cons_self h
      have hne : r' ≠ r := fun e => hn u List.mem_cons_self h (by rw [h1, e])
      rw [h1]
      apply LVec.extract_insertAt_of_disjoint
      rw [h2]
      rcases Nat.lt_or_gt_of_ne hne with h3 | h3
      · right; exact rowMajor_le h3
      · left; exact rowMajor_le h3
    · rfl

theorem foldP_written {n : String} {w M : Nat} {cond : Nat → Prop} {g : Nat → BitVec w} {r : Nat} (hw : 0 < w)
    (hr : r < M) (hc : cond r) :
    ∀ {q : NbaQueue2}, EntP n w M cond g q → (∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w) → ∀ x : LVec, x.width = M * w →
      (nbaFold n q x).extract (r * w) w = LVec.ofBitVec (g r)
  | [], _, ⟨_, h, _⟩, _, _ => absurd h List.not_mem_nil
  | u :: q, hq, hex, x, hx => by
    show (nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x)).extract _ _ = _
    by_cases hin : ∃ u' ∈ q, u'.1 = n ∧ u'.2.1 = r * w
    · exact foldP_written hw hr hc hq.tail hin _ (by split <;> simp [hx])
    · have hn' : ∀ u' ∈ q, u'.1 = n → u'.2.1 ≠ r * w := fun u' hu' h1 h2 => hin ⟨u', hu', h1, h2⟩
      rw [foldP_unwritten hq.tail hn']
      obtain ⟨u0, hu0, h1, h2⟩ := hex
      rcases List.mem_cons.mp hu0 with rfl | hu0
      · obtain ⟨r', -, h3, -, h4⟩ := hq u0 List.mem_cons_self h1
        have hrr : r' = r := Nat.eq_of_mul_eq_mul_right hw (h3.symm.trans h2)
        subst hrr
        rw [if_pos h1, h3, h4 hc]
        exact LVec.extract_insertAt_self (by simp) (by rw [hx]; exact winle w hr)
      · exact absurd ⟨u0, hu0, h1, h2⟩ hin

theorem fold_familyP {n : String} {w M : Nat} (hw : 0 < w) {cond : Nat → Prop} (g : Nat → BitVec w)
    {q : NbaQueue2} {x : LVec} (hx : x.width = M * w) (hq : EntP n w M cond g q)
    (hcov : ∀ r, r < M → cond r → (∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w) ∨ x.extract (r * w) w = LVec.ofBitVec (g r)) :
    PEnt w M cond g (nbaFold n q x) := by
  refine ⟨by rw [width_nbaFold, hx], fun r hr hc => ?_⟩
  by_cases hex : ∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w
  · exact foldP_written hw hr hc hq hex x hx
  · have hn : ∀ u ∈ q, u.1 = n → u.2.1 ≠ r * w := fun u hu h1 h2 => hex ⟨u, hu, h1, h2⟩
    rw [foldP_unwritten hq hn x]
    exact (hcov r hr hc).resolve_left hex

theorem PEnt.eq {w M : Nat} {cond : Nat → Prop} {f : Nat → BitVec w} {v : LVec} (h : PEnt w M cond f v)
    (hall : ∀ r, r < M → cond r) : v = LVec.ofBitVec (packBV w M f) :=
  ent_eq f h.1 fun r hr => h.2 r hr (hall r hr)

theorem sxv_of_extract {v : LVec} {AccW lo W : Nat} {y : BitVec W} (hW : 1 ≤ W) (hv : v.extract lo W = .ofBitVec y) :
    sxv v AccW lo W = LVec.ofBitVec (y.signExtend (AccW + W)) := by
  have h1 : v.extract (lo + W - 1) 1 = (v.extract lo W).extract (W - 1) 1 := by
    rw [LVec.extract_extract _ (by omega : W - 1 + 1 ≤ W)]; congr 1; omega
  have hy : y.extractLsb' 0 W = y := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_extractLsb', hi]
  have := sxv_known y (AccW := AccW) (lo := 0) hW (by omega)
  unfold sxv at this ⊢
  rw [LVec.extract_ofBitVec _ (show 0 + W ≤ W by omega), hy, Nat.zero_add] at this
  rw [h1, hv]
  exact this

section pe
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

/-- The PE queues of a busy cycle. -/
abbrev peQB (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (sh wa ps : LVec) : NbaQueue2 :=
  p0Qs N W AccW (kb false) (tv t) (.ofBitVec (wfV N W B t)) sh wa (.ofBitVec (datV N W AccW A t)) ++
    pkQs N W AccW (kb false) (tv t) sh wa (.ofBitVec (datV N W AccW A t)) ps

theorem mem_peQB {sh wa ps : LVec} {u : String × Nat × LVec} (hu : u ∈ peQB N W AccW A B t sh wa ps) :
    (∃ j, j < N ∧ u ∈ p0Q N W AccW (kb false) (tv t) (.ofBitVec (wfV N W B t)) sh wa (.ofBitVec (datV N W AccW A t)) j) ∨
    (∃ k j, k < N - 1 ∧ j < N ∧ u ∈ pkQ N W AccW (kb false) (tv t) sh wa (.ofBitVec (datV N W AccW A t)) ps k j) := by
  simp only [peQB, p0Qs, pkQs, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with ⟨j, hj, hu⟩ | ⟨k, hk, j, hj, hu⟩
  · exact .inl ⟨j, hj, hu⟩
  · exact .inr ⟨k, j, hk, hj, hu⟩

end pe

/-- The shadow weights `t` steps on: the rows below `min t N` hold `B`'s shifted rows, the rest anything. -/
def shOK (N W : Nat) (B : BitVec (N * N * W)) (t : Nat) (sh : LVec) : Prop :=
  PEnt W (N * N) (fun r => r / N < t) (fun r => (shV N W B t).extractLsb' (r * W) W) sh

/-- The active weights `t` steps on: `B` after the swap, anything before. -/
def waOK (N W AccW : Nat) (B : BitVec (N * N * W)) (t : Nat) (wa : LVec) : Prop :=
  PEnt AccW (N * N) (fun _ => N + 1 ≤ t) (fun r => (B.extractLsb' (r * W) W).signExtend AccW) wa

/-- The partial sums `t` steps on: PE `(k, j)`'s is known from step `N + 2 + k`. -/
def psOK (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (ps : LVec) : Prop :=
  PEnt AccW (N * N) (fun r => N + 2 + r / N ≤ t) (fun r => BitVec.ofInt AccW (psI N W A B t (r / N) (r % N))) ps

section pe2
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

theorem sh_busy {sh wa ps : LVec} (hsh : shOK N W B t sh) :
    shOK N W B (t + 1) (nbaFold "wsh" (peQB N W AccW A B t sh wa ps) sh) := by
  have hN := h.hN
  by_cases hl : t < N
  · refine fold_familyP h.hW _ hsh.1 (fun u hu hn => ?_) (fun r hr _ => .inl ?_)
    · rcases mem_peQB h A B ht hu with ⟨j, hj, hu⟩ | ⟨k, j, hk, hj, hu⟩
      · rcases (mem_p0Q_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
        · have hjN : j < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
          have hb : (N - 1) * N + j < N * N := rm_lt (show N - 1 < N by omega) hj
          refine ⟨j, hjN, rfl, by simp, fun _ => ?_⟩
          rw [LVec.extract_ofBitVec _ (winle W hb), LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
          congr 1
          unfold wfV shV
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega),
            ent_shl N W B (show t * N ≤ (N - 1) * N + j from Nat.le_trans (Nat.mul_le_mul_right N (by omega))
              (Nat.le_add_right _ _)) hb, ent_shr]
          dsimp only; congr 2
          have e1 : (N - 1) * N = (N - (t + 1)) * N + t * N := by
            rw [← Nat.add_mul]; congr 1; omega
          omega
        · simp at hn
        · simp at hn
      · rcases (mem_pkQ_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
        · have hb := rm_lt (show k + 1 < N by omega) hj
          have hb' := rm_lt (show k < N by omega) hj
          refine ⟨(k + 1) * N + j, hb, rfl, by simp, fun hc => ?_⟩
          rw [rm_div hj] at hc
          rw [hsh.2 _ hb' (by show (k * N + j) / N < t; rw [rm_div hj]; omega), LVec.resizeU_ofBitVec,
            BitVec.setWidth_eq]
          try dsimp only
          congr 1
          unfold shV
          rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), ent_shr, ent_shr]
          congr 1
          have e2 : (N - t) * N = (N - (t + 1)) * N + N := by
            rw [← Nat.succ_mul]; congr 1; omega
          have e3 : (k + 1) * N = k * N + N := Nat.succ_mul k N
          omega
        · simp at hn
        · simp at hn
    · rcases pe_cover hr with h0 | ⟨k, j, hk, hj, rfl⟩
      · refine ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr h0,
          (mem_p0Q_busy h ht).mpr (.inl ⟨hl, rfl⟩)⟩)), rfl, rfl⟩
      · refine ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
          List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, (mem_pkQ_busy h ht).mpr (.inl ⟨hl, rfl⟩)⟩⟩)), rfl, rfl⟩
  · rw [nbaFold_of_forall_ne (fun u hu hn => ?_)]
    · refine ⟨hsh.1, fun r hr _ => ?_⟩
      have hN0 : 0 < N := by omega
      rw [hsh.2 r hr (by show r / N < t; have := (Nat.div_lt_iff_lt_mul hN0).mpr hr; omega)]
      congr 2; unfold shV; rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    · rcases mem_peQB h A B ht hu with ⟨j, hj, hu⟩ | ⟨k, j, hk, hj, hu⟩
      · rcases (mem_p0Q_busy h ht).mp hu with ⟨h1, -⟩ | ⟨-, rfl⟩ | rfl
        · exact hl h1
        · simp at hn
        · simp at hn
      · rcases (mem_pkQ_busy h ht).mp hu with ⟨h1, -⟩ | ⟨-, rfl⟩ | rfl
        · exact hl h1
        · simp at hn
        · simp at hn

theorem wa_busy {sh wa ps : LVec} (hsh : shOK N W B t sh) (hwa : waOK N W AccW B t wa) :
    waOK N W AccW B (t + 1) (nbaFold "wac" (peQB N W AccW A B t sh wa ps) wa) := by
  have hN := h.hN; have hW := h.hW
  by_cases hl : t = N
  · subst hl
    have hshB : shV t W B t = B := by
      unfold shV; rw [Nat.min_self, Nat.sub_self, Nat.zero_mul, BitVec.ushiftRight_zero]
    have hN0 : 0 < t := by omega
    refine fold_familyP h.hA _ hwa.1 (fun u hu hn => ?_) (fun r hr _ => .inl ?_)
    · rcases mem_peQB h A B ht hu with ⟨j, hj, hu⟩ | ⟨k, j, hk, hj, hu⟩
      · rcases (mem_p0Q_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
        · simp at hn
        · have hjN : j < t * t := by have := Nat.le_mul_of_pos_left t hN; omega
          refine ⟨j, hjN, rfl, by simp, fun _ => ?_⟩
          rw [sxv_of_extract hW (hsh.2 j hjN (by show j / t < t; have := (Nat.div_lt_iff_lt_mul hN0).mpr hjN; omega)),
            hshB,
            LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
            Lib.setWidth_signExtend_of_le _ (Nat.le_add_right _ _)]
        · simp at hn
      · rcases (mem_pkQ_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
        · simp at hn
        · have hb := rm_lt (show k + 1 < t by omega) hj
          refine ⟨(k + 1) * t + j, hb, rfl, by simp, fun _ => ?_⟩
          rw [sxv_of_extract hW (hsh.2 _ hb (by show ((k + 1) * t + j) / t < t; have := (Nat.div_lt_iff_lt_mul hN0).mpr hb; omega)), hshB,
            LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
            Lib.setWidth_signExtend_of_le _ (Nat.le_add_right _ _)]
        · simp at hn
    · rcases pe_cover hr with h0 | ⟨k, j, hk, hj, rfl⟩
      · refine ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr h0,
          (mem_p0Q_busy h ht).mpr (.inr (.inl ⟨rfl, rfl⟩))⟩)), rfl, rfl⟩
      · refine ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
          List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, (mem_pkQ_busy h ht).mpr (.inr (.inl ⟨rfl, rfl⟩))⟩⟩)), rfl, rfl⟩
  · rw [nbaFold_of_forall_ne (fun u hu hn => ?_)]
    · exact ⟨hwa.1, fun r hr hc => hwa.2 r hr (by have : N + 1 ≤ t + 1 := hc; show N + 1 ≤ t; omega)⟩
    · rcases mem_peQB h A B ht hu with ⟨j, hj, hu⟩ | ⟨k, j, hk, hj, hu⟩
      · rcases (mem_p0Q_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨h1, -⟩ | rfl
        · simp at hn
        · exact hl h1
        · simp at hn
      · rcases (mem_pkQ_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨h1, -⟩ | rfl
        · simp at hn
        · exact hl h1
        · simp at hn

end pe2

theorem base_zero (N : Nat) : base N 0 = 0 := by simp [base]

theorem datE_at0 (N W AccW : Nat) (A : BitVec (N * N * W)) (t : Nat) {e : Nat} (he : e < N) :
    datE N W AccW A t e = (aPat N W A 0 (t + e) (2 * N)).signExtend AccW := by
  have := datE_at N W AccW A t (k := 0) (e := e) (by omega) (by omega)
  rwa [base_zero, Nat.zero_add, Nat.add_zero] at this

/-- **PE `(0, j)` in a step**: the product of its data register and its active weight. -/
theorem psI_step0 (N W : Nat) (A B : BitVec (N * N * W)) (t : Nat) {j : Nat} (hj : j < N) :
    psI N W A B (t + 1) 0 j =
      (aPat N W A 0 (t + (N - 1 - j)) (2 * N)).toInt * ((waV N W B t).extractLsb' (j * W) W).toInt := by
  unfold psI aPat waV
  by_cases hv : N + 1 + j ≤ t ∧ t - (N + 1 + j) < N
  · rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), psum_succ, psum_zero]
    unfold Tasks.Matmul.entry
    rw [show t + 1 - (N + 2 + 0 + j) = t + (N - 1 - j) - 2 * N by omega]
    simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

/-- **PE `(k + 1, j)` in a step**: the partial sum from above plus the product. -/
theorem psI_step (N W : Nat) (A B : BitVec (N * N * W)) (t : Nat) {k j : Nat} (hj : j < N) :
    psI N W A B (t + 1) (k + 1) j = psI N W A B t k j +
      (aPat N W A (k + 1) (t + (N - 1 - j)) (2 * N + (k + 1))).toInt *
        ((waV N W B t).extractLsb' (((k + 1) * N + j) * W) W).toInt := by
  unfold psI aPat waV
  by_cases hv : N + 2 + k + j ≤ t ∧ t - (N + 2 + k + j) < N
  · rw [if_pos (by omega), if_pos hv, if_pos (by omega), if_neg (by omega), psum_succ]
    unfold Tasks.Matmul.entry
    rw [show t + 1 - (N + 2 + (k + 1) + j) = t - (N + 2 + k + j) by omega,
      show t + (N - 1 - j) - (2 * N + (k + 1)) = t - (N + 2 + k + j) by omega]
  · rw [if_neg (by omega), if_neg hv, if_neg (by omega)]
    simp

section ps
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

theorem ps_busy {sh wa ps : LVec} (hwa : waOK N W AccW B t wa) (hps : psOK N W AccW A B t ps) :
    psOK N W AccW A B (t + 1) (nbaFold "ps" (peQB N W AccW A B t sh wa ps) ps) := by
  have hN := h.hN; have hW := h.hW; have hA := h.hA
  have hNN : N ≤ N * N := Nat.le_mul_of_pos_left N hN
  have hDN : N ≤ DW N := by have := base_row_le N hN (show 0 < N by omega); simp [base] at this; omega
  refine fold_familyP hA _ hps.1 (fun u hu hn => ?_) (fun r hr _ => .inl ?_)
  · rcases mem_peQB h A B ht hu with ⟨j, hj, hu⟩ | ⟨k, j, hk, hj, hu⟩
    · rcases (mem_p0Q_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
      · simp at hn
      · simp at hn
      · refine ⟨j, by omega, rfl, by simp, fun hc => ?_⟩
        simp only [Nat.div_eq_of_lt hj] at hc
        have hwv : waV N W B t = B := by unfold waV; rw [if_neg (by omega)]
        unfold datV
        rw [ext_pack _ (show N - 1 - j < DW N by omega), hwa.2 j (by omega) (by show N + 1 ≤ t; omega),
          datE_at0 N W AccW A t (show N - 1 - j < N by omega),
          LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, sext_mul, Nat.div_eq_of_lt hj,
          Nat.mod_eq_of_lt hj, psI_step0 N W A B t hj, hwv]
    · rcases (mem_pkQ_busy h ht).mp hu with ⟨-, rfl⟩ | ⟨-, rfl⟩ | rfl
      · simp at hn
      · simp at hn
      · have hb := rm_lt (show k + 1 < N by omega) hj
        have hb' := rm_lt (show k < N by omega) hj
        have hrow := base_row_le N hN (show k + 1 < N by omega)
        have hd : base N (k + 1) + N - 1 - j = base N (k + 1) + (N - 1 - j) := by omega
        refine ⟨(k + 1) * N + j, hb, rfl, by simp, fun hc => ?_⟩
        simp only [rm_div hj] at hc
        have hwv : waV N W B t = B := by unfold waV; rw [if_neg (by omega)]
        unfold datV
        rw [hps.2 _ hb' (by show N + 2 + (k * N + j) / N ≤ t; rw [rm_div hj]; omega)]
        dsimp only
        rw [rm_div hj, rm_mod hj, hd,
          ext_pack _ (show base N (k + 1) + (N - 1 - j) < DW N by omega), hwa.2 _ hb (by show N + 1 ≤ t; omega),
          datE_at N W AccW A t (show k + 1 < N by omega) (show N - 1 - j < N + (k + 1) by omega),
          LVec.mul_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, sext_mul,
          ← BitVec.ofInt_add, rm_div hj, rm_mod hj, psI_step N W A B t hj, hwv]
  · rcases pe_cover hr with h0 | ⟨k, j, hk, hj, rfl⟩
    · refine ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr h0,
        (mem_p0Q_busy h ht).mpr (.inr (.inr rfl))⟩)), rfl, rfl⟩
    · refine ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
        List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, (mem_pkQ_busy h ht).mpr (.inr (.inr rfl))⟩⟩)), rfl, rfl⟩

end ps

/-! ### The data rows through a busy cycle -/

theorem rm_lt_iff {N q k : Nat} (hk : k < N) : q * N + k < N * N ↔ q < N := by
  constructor
  · intro h'; refine Nat.lt_of_not_le fun hc => ?_
    have := Nat.mul_le_mul_right N hc; omega
  · intro h'; exact rm_lt h' hk

/-- The setup unit's input: entry `k` of the buffer's row, `0` outside the wavefront phase. -/
theorem tap_ub (N W : Nat) (A : BitVec (N * N * W)) (t : Nat) {k : Nat} (hk : k < N) (hNt : N ≤ t) :
    (ubV N W A t).extractLsb' (k * W) W = aPat N W A k (t + 1 + (N + k - 1)) (2 * N + k) := by
  unfold ubV aPat
  rw [ent_shr]
  unfold ent
  by_cases hv : t - N < N
  · rw [if_pos ((rm_lt_iff hk).mpr hv), if_pos (by omega),
      show t + 1 + (N + k - 1) - (2 * N + k) = t - N by omega]
  · rw [if_neg (fun hc => hv ((rm_lt_iff hk).mp hc)), if_neg (by omega)]

theorem tap_zero (N W : Nat) (A : BitVec (N * N * W)) (t : Nat) {k : Nat} (hNt : ¬ N ≤ t) :
    0#W = aPat N W A k (t + 1 + (N + k - 1)) (2 * N + k) := by
  unfold aPat; rw [if_neg (by omega)]; rfl

theorem sext_zero (w m : Nat) : (0#w).signExtend m = 0#m := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_signExtend]

theorem mem_dsQ_busy {N AccW : Nat} {dt : LVec} {k e : Nat} {u : String × Nat × LVec} :
    u ∈ dsQ N AccW (kb false) dt k e ↔
      u = ("dat", (base N k + e) * AccW, (dt.extract ((base N k + e + 1) * AccW) AccW).resizeU AccW) := by
  unfold dsQ; rw [condTrue_knownBit, if_neg (by simp)]; simp

section dat
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

abbrev datQB (N W AccW : Nat) (A : BitVec (N * N * W)) (t : Nat) : NbaQueue2 :=
  dsQs N AccW (kb false) (.ofBitVec (datV N W AccW A t)) ++ dtQs N W AccW (kb false) (tv t) (.ofBitVec (ubV N W A t))

theorem mem_dtQ_busy {ub : LVec} {k : Nat} {u : String × Nat × LVec} :
    u ∈ dtQ N W AccW (kb false) (tv t) ub k ↔
      (N ≤ t ∧ u = ("dat", (base N k + N + k - 1) * AccW, ((sxv ub AccW (k * W) W).resizeU AccW).resizeU AccW)) ∨
      (¬ N ≤ t ∧ u = ("dat", (base N k + N + k - 1) * AccW, (zv AccW).resizeU AccW)) := by
  unfold dtQ; rw [condTrue_knownBit, if_neg (by simp), geB_tv h (Nat.le_of_lt ht)]
  by_cases h1 : N ≤ t <;> simp [h1]

theorem dat_busy : nbaFold "dat" (datQB N W AccW A t) (.ofBitVec (datV N W AccW A t)) =
    .ofBitVec (datV N W AccW A (t + 1)) := by
  have hN := h.hN; have hW := h.hW; have hA := h.hA
  refine fold_family hA (datV N W AccW A (t + 1)) (by simp) (fun u hu hn => ?_) (fun r hr => .inl ?_)
  · simp only [datQB, dsQs, dtQs, List.mem_append, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨k, hk, e, he, hu⟩ | ⟨k, hk, hu⟩
    · rw [mem_dsQ_busy] at hu; subst hu
      have hrow := base_row_le N hN hk
      refine ⟨base N k + e, by omega, rfl, ?_⟩
      unfold datV
      rw [ext_pack _ (show base N k + e + 1 < DW N by omega), LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
        extractLsb'_packBV _ (show base N k + e < DW N by omega), show base N k + e + 1 = base N k + (e + 1) by omega,
        datE_at N W AccW A t hk (show e + 1 < N + k by omega), datE_at N W AccW A (t + 1) hk (show e < N + k by omega),
        show t + (e + 1) = t + 1 + e by omega]
    · have hrow := base_row_le N hN hk
      have hidx : base N k + N + k - 1 = base N k + (N + k - 1) := by omega
      rcases (mem_dtQ_busy h ht).mp hu with ⟨hNt, rfl⟩ | ⟨hNt, rfl⟩
      · refine ⟨base N k + N + k - 1, by omega, rfl, ?_⟩
        have hkNN : k < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
        unfold datV
        rw [sxv_known _ hW (winle W hkNN), LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
          Lib.setWidth_signExtend_of_le _ (Nat.le_add_right _ _),
          extractLsb'_packBV _ (show base N k + N + k - 1 < DW N by omega), hidx,
          datE_at N W AccW A (t + 1) hk (show N + k - 1 < N + k by omega), tap_ub N W A t hk hNt]
      · refine ⟨base N k + N + k - 1, by omega, rfl, ?_⟩
        unfold datV
        rw [zv_eq, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
          extractLsb'_packBV _ (show base N k + N + k - 1 < DW N by omega), hidx,
          datE_at N W AccW A (t + 1) hk (show N + k - 1 < N + k by omega), ← tap_zero N W A t hNt, sext_zero]
  · obtain ⟨k, e, hk, he, rfl⟩ := tri_cover N N r (by rw [base_N N hN]; exact hr)
    by_cases he' : e < N + k - 1
    · exact ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
        List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he', mem_dsQ_busy.mpr rfl⟩⟩)), rfl, rfl⟩
    · have hidx : base N k + e = base N k + N + k - 1 := by omega
      by_cases hNt : N ≤ t
      · exact ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
          (mem_dtQ_busy h ht).mpr (.inl ⟨hNt, rfl⟩)⟩)), rfl, by rw [hidx]⟩
      · exact ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
          (mem_dtQ_busy h ht).mpr (.inr ⟨hNt, rfl⟩)⟩)), rfl, by rw [hidx]⟩

end dat

/-! ### The accumulators through a busy cycle -/

section acc
variable (N W AccW : Nat) (A B : BitVec (N * N * W)) {t i j : Nat}

/-- In column `j`'s window every word takes the next one. -/
theorem cE_in (hlo : 2 * N + 1 + j ≤ t) (hhi : t ≤ 3 * N + j) (hi : i + 1 < N) :
    cE N W AccW A B (t + 1) i j = cE N W AccW A B t (i + 1) j := by
  unfold cE nC
  rw [show min N (t + 1 - (2 * N + 1 + j)) = t - (2 * N + 1 + j) + 1 by omega,
    show min N (t - (2 * N + 1 + j)) = t - (2 * N + 1 + j) by omega]
  by_cases hc : N - (t - (2 * N + 1 + j) + 1) ≤ i
  · rw [if_pos hc, if_pos (by omega),
      show i - (N - (t - (2 * N + 1 + j) + 1)) = i + 1 - (N - (t - (2 * N + 1 + j))) by omega]
  · rw [if_neg hc, if_neg (by omega)]

/-- In column `j`'s window the last word takes the first (still `0`) plus the bottom partial sum. -/
theorem cE_last (hN : 1 ≤ N) (hlo : 2 * N + 1 + j ≤ t) (hhi : t ≤ 3 * N + j) :
    cE N W AccW A B (t + 1) (N - 1) j = cE N W AccW A B t 0 j + BitVec.ofInt AccW (psI N W A B t (N - 1) j) := by
  unfold cE nC psI
  rw [show min N (t + 1 - (2 * N + 1 + j)) = t - (2 * N + 1 + j) + 1 by omega,
    show min N (t - (2 * N + 1 + j)) = t - (2 * N + 1 + j) by omega, if_pos (by omega), if_neg (by omega),
    if_pos (by omega), show N - 1 + 1 = N by omega,
    show N - 1 - (N - (t - (2 * N + 1 + j) + 1)) = t - (N + 2 + (N - 1) + j) by omega]
  simp

/-- Outside column `j`'s window nothing changes. -/
theorem cE_out (hout : ¬ (2 * N + 1 + j ≤ t ∧ t ≤ 3 * N + j)) :
    cE N W AccW A B (t + 1) i j = cE N W AccW A B t i j := by
  unfold cE nC
  rw [show min N (t + 1 - (2 * N + 1 + j)) = min N (t - (2 * N + 1 + j)) by omega]

end acc

section accb
variable {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
include h ht

theorem mem_arQ_busy {c : LVec} {i j : Nat} (hj : j < N) {u : String × Nat × LVec} :
    u ∈ arQ N AccW (kb false) (kb true) (tv t) c i j ↔ (2 * N + 1 + j ≤ t ∧ t ≤ 3 * N + j) ∧
      u = ("C", (i * N + j) * AccW, (c.extract (((i + 1) * N + j) * AccW) AccW).resizeU AccW) := by
  unfold arQ
  rw [condTrue_knownBit, condTrue_knownBit, if_neg (by simp), if_pos rfl, loB_tv h (Nat.le_of_lt ht) hj,
    hiB_tv h (Nat.le_of_lt ht) hj]
  by_cases h1 : 2 * N + 1 + j ≤ t <;> by_cases h2 : t ≤ 3 * N + j <;> simp [h1, h2]

theorem mem_alQ_busy {c ps : LVec} {j : Nat} (hj : j < N) {u : String × Nat × LVec} :
    u ∈ alQ N AccW (kb false) (kb true) (tv t) c ps j ↔ (2 * N + 1 + j ≤ t ∧ t ≤ 3 * N + j) ∧
      u = ("C", ((N - 1) * N + j) * AccW,
        ((c.extract (j * AccW) AccW).add (ps.extract (((N - 1) * N + j) * AccW) AccW)).resizeU AccW) := by
  unfold alQ
  rw [condTrue_knownBit, condTrue_knownBit, if_neg (by simp), if_pos rfl, loB_tv h (Nat.le_of_lt ht) hj,
    hiB_tv h (Nat.le_of_lt ht) hj]
  by_cases h1 : 2 * N + 1 + j ≤ t <;> by_cases h2 : t ≤ 3 * N + j <;> simp [h1, h2]

abbrev cQB (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (ps : LVec) : NbaQueue2 :=
  arQs N AccW (kb false) (kb true) (tv t) (.ofBitVec (cV N W AccW A B t)) ++
    alQs N AccW (kb false) (kb true) (tv t) (.ofBitVec (cV N W AccW A B t)) ps

theorem C_busy {ps : LVec} (hps : psOK N W AccW A B t ps) : nbaFold "C" (cQB N W AccW A B t ps) (.ofBitVec (cV N W AccW A B t)) =
    .ofBitVec (cV N W AccW A B (t + 1)) := by
  have hN := h.hN; have hA := h.hA
  have hNN : N ≤ N * N := Nat.le_mul_of_pos_left N hN
  refine fold_family hA (cV N W AccW A B (t + 1)) (by simp) (fun u hu hn => ?_) (fun r hr => ?_)
  · simp only [cQB, arQs, alQs, List.mem_append, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨i, hi, j, hj, hu⟩ | ⟨j, hj, hu⟩
    · obtain ⟨⟨hlo, hhi⟩, rfl⟩ := (mem_arQ_busy h ht hj).mp hu
      have hb := rm_lt (show i < N by omega) hj
      have hb' := rm_lt (show i + 1 < N by omega) hj
      refine ⟨i * N + j, hb, rfl, ?_⟩
      unfold cV
      rw [ext_pack _ hb', LVec.resizeU_ofBitVec, BitVec.setWidth_eq, extractLsb'_packBV _ hb, rm_div hj, rm_mod hj,
        rm_div hj, rm_mod hj, cE_in N W AccW A B hlo hhi (by omega)]
    · obtain ⟨⟨hlo, hhi⟩, rfl⟩ := (mem_alQ_busy h ht hj).mp hu
      have hb := rm_lt (show N - 1 < N by omega) hj
      refine ⟨(N - 1) * N + j, hb, rfl, ?_⟩
      unfold cV
      rw [ext_pack _ (show j < N * N by omega), hps.2 _ hb (by show N + 2 + ((N - 1) * N + j) / N ≤ t; rw [rm_div hj]; omega)]
      dsimp only
      rw [LVec.add_ofBitVec,
        LVec.resizeU_ofBitVec, BitVec.setWidth_eq, extractLsb'_packBV _ hb, rm_div hj, rm_mod hj, Nat.div_eq_of_lt hj,
        Nat.mod_eq_of_lt hj, cE_last N W AccW A B hN hlo hhi]
  · have hN0 : 0 < N := by omega
    have hr' : r = r / N * N + r % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod r N).symm
    have hi : r / N < N := (Nat.div_lt_iff_lt_mul hN0).mpr hr
    have hj : r % N < N := Nat.mod_lt r hN0
    by_cases hw : 2 * N + 1 + r % N ≤ t ∧ t ≤ 3 * N + r % N
    · left
      by_cases hiN : r / N < N - 1
      · refine ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨r / N, List.mem_range.mpr hiN,
          List.mem_flatMap.mpr ⟨r % N, List.mem_range.mpr hj, (mem_arQ_busy h ht hj).mpr ⟨hw, rfl⟩⟩⟩)), rfl, ?_⟩
        show (r / N * N + r % N) * AccW = r * AccW
        rw [← hr']
      · refine ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨r % N, List.mem_range.mpr hj,
          (mem_alQ_busy h ht hj).mpr ⟨hw, rfl⟩⟩)), rfl, ?_⟩
        show ((N - 1) * N + r % N) * AccW = r * AccW
        rw [show N - 1 = r / N by omega, ← hr']
    · right
      unfold cV
      rw [ext_pack _ hr, extractLsb'_packBV _ hr, cE_out N W AccW A B hw]

end accb

/-! ### The whole busy cycle -/

/-- The state `t` busy steps after a start with operands `A`, `B` (the PE registers `sh`, `wa`, `ps` as given). -/
def BS (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (ck r s a b sh wa ps : LVec) : SvState :=
  SS ck r s a b (kb false) (.ofBitVec (cV N W AccW A B t)) (kb true) (tv t) (.ofBitVec (wfV N W B t)) sh wa
    (.ofBitVec (ubV N W A t)) (.ofBitVec (datV N W AccW A t)) ps

/-- **One busy cycle**: from the state at `t < 4N`, without reset and start, the state at `t + 1`; `done` rises and
`busy` falls exactly when `t + 1 = 4N`. -/
theorem next_busy {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 4 * N)
    (ck a b sh wa ps : LVec) (hsh : shOK N W B t sh) (hwa : waOK N W AccW B t wa) (hps : psOK N W AccW A B t ps) :
    ∃ sh' wa' ps', tpNext N W AccW ck (kb false) (kb false) a b (kb false) (.ofBitVec (cV N W AccW A B t)) (kb true)
        (tv t) (.ofBitVec (wfV N W B t)) sh wa (.ofBitVec (ubV N W A t)) (.ofBitVec (datV N W AccW A t)) ps =
      SS ck (kb false) (kb false) a b (kb (decide (t + 1 = 4 * N))) (.ofBitVec (cV N W AccW A B (t + 1)))
        (kb (decide (t + 1 ≠ 4 * N))) (tv (t + 1)) (.ofBitVec (wfV N W B (t + 1))) sh' wa'
        (.ofBitVec (ubV N W A (t + 1))) (.ofBitVec (datV N W AccW A (t + 1))) ps' ∧
      shOK N W B (t + 1) sh' ∧ waOK N W AccW B (t + 1) wa' ∧ psOK N W AccW A B (t + 1) ps' := by
  obtain ⟨hd, hb, htt⟩ := ctrl_busy (N := N) h ht
  unfold tpNext
  rw [commit_SS _ _ _ _ _ _ _ _ _ _ _ (fun u hu => Q_names u hu), fold_ctrl "done", fold_C, fold_ctrl "busy",
    fold_ctrl "t", fold_wf, fold_pe "wsh", fold_pe "wac", fold_ub, fold_dat, fold_pe "ps", hd, hb, htt,
    wf_busy h B ht, ub_busy h A ht]
  have e1 := sh_busy (AccW := AccW) h A B ht (wa := wa) (ps := ps) hsh
  have e2 := wa_busy (AccW := AccW) h A B ht (ps := ps) hsh hwa
  have e3 := ps_busy h A B ht (sh := sh) hwa hps
  have e4 := dat_busy (AccW := AccW) h A ht
  have e5 := C_busy h A B ht hps
  simp only [peQB, datQB, cQB] at e1 e2 e3 e4 e5
  rw [e4, e5]
  exact ⟨_, _, _, rfl, e1, e2, e3⟩

/-! ## 7. The start, the reset and the idle cycles -/

theorem zero_of_entries {w M : Nat} (X : BitVec (M * w)) (h : ∀ r, r < M → X.extractLsb' (r * w) w = 0#w) :
    X = 0#(M * w) := by
  rw [← pack_self X, ← pack_self (0#(M * w))]
  exact packBV_congr fun r hr => by rw [h r hr]; simp

/-- A queue that writes `0` into every entry. -/
theorem fold_zero {n : String} {w M : Nat} (hw : 0 < w) {q : NbaQueue2} {x : LVec} (hx : x.width = M * w)
    (hq : ∀ u ∈ q, u.1 = n → ∃ r, r < M ∧ u.2.1 = r * w ∧ u.2.2 = LVec.ofBitVec 0#w)
    (hcov : ∀ r, r < M → ∃ u ∈ q, u.1 = n ∧ u.2.1 = r * w) : nbaFold n q x = LVec.ofBitVec 0#(M * w) :=
  fold_family hw 0#(M * w) hx (fun u hu hn => by
      obtain ⟨r, hr, h1, h2⟩ := hq u hu hn; exact ⟨r, hr, h1, by rw [h2]; simp⟩)
    (fun r hr => .inl (hcov r hr))

theorem zres (w : Nat) : (zv w).resizeU w = LVec.ofBitVec 0#w := by
  rw [zv_eq, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

section start
variable (N W AccW : Nat) (A B : BitVec (N * N * W))

theorem wfV_zero : wfV N W B 0 = B := by
  unfold wfV; rw [Nat.min_eq_left (Nat.zero_le _), Nat.zero_mul, BitVec.shiftLeft_zero]
theorem ubV_zero : ubV N W A 0 = A := by
  unfold ubV; rw [Nat.zero_sub, Nat.zero_mul, BitVec.ushiftRight_zero]
theorem datV_zero : datV N W AccW A 0 = 0#(DW N * AccW) := by
  unfold datV
  rw [← pack_self (0#(DW N * AccW))]
  refine packBV_congr fun r hr => ?_
  rw [BitVec.extractLsb'_zero]
  unfold datE aPat
  refine (congrArg (BitVec.signExtend AccW) (if_neg ?_)).trans (sext_zero W AccW)
  intro hc
  -- the entry `r` of row `k` has `e < N + k < 2N + k`
  obtain ⟨k, e, hk, he, rfl⟩ := tri_cover N N r (by
    by_cases hN : 1 ≤ N
    · rw [base_N N hN]; exact hr
    · have : N = 0 := by omega
      subst this; simp [DW] at hr)
  rw [rowOf_base N he N hk, Nat.add_sub_cancel_left] at hc
  omega
theorem shV_zero : shV N W B 0 = 0#(N * N * W) := by
  refine zero_of_entries (M := N * N) _ fun r hr => ?_
  unfold shV
  rw [Nat.min_eq_left (Nat.zero_le _), Nat.sub_zero, ent_shr]
  unfold ent; rw [if_neg (by omega)]; rfl
theorem waV_zero : waV N W B 0 = 0 := by unfold waV; rw [if_pos (Nat.zero_le _)]
theorem psV_zero : psV N W AccW A B 0 = 0#(N * N * AccW) := by
  rw [← pack_self (0#(N * N * AccW))]
  unfold psV
  refine packBV_congr fun r hr => ?_
  rw [BitVec.extractLsb'_zero]
  simp [psI]
theorem cV_zero : cV N W AccW A B 0 = 0#(N * N * AccW) := by
  rw [← pack_self (0#(N * N * AccW))]
  unfold cV
  refine packBV_congr fun r hr => ?_
  rw [BitVec.extractLsb'_zero]
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hr
  have hi : r / N < N := (Nat.div_lt_iff_lt_mul hN0).mpr hr
  unfold cE nC
  rw [if_neg (by omega)]; rfl

end start

section startq
variable {N W AccW : Nat} {t wf sh wa dt ps ub c bz : LVec} {u : String × Nat × LVec}

theorem mem_dsQ_start {k e : Nat} :
    u ∈ dsQ N AccW (kb true) dt k e ↔ u = ("dat", (base N k + e) * AccW, (zv AccW).resizeU AccW) := by
  unfold dsQ; simp
theorem mem_dtQ_start {k : Nat} :
    u ∈ dtQ N W AccW (kb true) t ub k ↔ u = ("dat", (base N k + N + k - 1) * AccW, (zv AccW).resizeU AccW) := by
  unfold dtQ; simp
theorem mem_arQ_start {i j : Nat} : u ∈ arQ N AccW (kb true) bz t c i j ↔
    u = ("C", (i * N + j) * AccW, (zv AccW).resizeU AccW) := by
  unfold arQ; simp
theorem mem_alQ_start {j : Nat} : u ∈ alQ N AccW (kb true) bz t c ps j ↔
    u = ("C", ((N - 1) * N + j) * AccW, (zv AccW).resizeU AccW) := by
  unfold alQ; simp

theorem dat_start (hN : 1 ≤ N) (hA : 1 ≤ AccW) {x : LVec} (hx : x.width = DW N * AccW) :
    nbaFold "dat" (dsQs N AccW (kb true) dt ++ dtQs N W AccW (kb true) t ub) x = LVec.ofBitVec 0#(DW N * AccW) := by
  refine fold_zero hA hx (fun u hu hn => ?_) (fun r hr => ?_)
  · simp only [dsQs, dtQs, List.mem_append, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨k, hk, e, he, hu⟩ | ⟨k, hk, hu⟩
    · rw [mem_dsQ_start] at hu; subst hu
      have := base_row_le N hN hk
      exact ⟨base N k + e, by omega, rfl, zres AccW⟩
    · rw [mem_dtQ_start] at hu; subst hu
      have := base_row_le N hN hk
      exact ⟨base N k + N + k - 1, by omega, rfl, zres AccW⟩
  · obtain ⟨k, e, hk, he, rfl⟩ := tri_cover N N r (by rw [base_N N hN]; exact hr)
    by_cases he' : e < N + k - 1
    · exact ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
        List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he', mem_dsQ_start.mpr rfl⟩⟩)), rfl, rfl⟩
    · exact ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
        mem_dtQ_start.mpr rfl⟩)), rfl, by show (base N k + N + k - 1) * AccW = _; congr 1; omega⟩

theorem C_start (hN : 1 ≤ N) (hA : 1 ≤ AccW) {x : LVec} (hx : x.width = N * N * AccW) :
    nbaFold "C" (arQs N AccW (kb true) bz t c ++ alQs N AccW (kb true) bz t c ps) x = LVec.ofBitVec 0#(N * N * AccW) := by
  refine fold_zero hA hx (fun u hu hn => ?_) (fun r hr => ?_)
  · simp only [arQs, alQs, List.mem_append, List.mem_flatMap, List.mem_range] at hu
    rcases hu with ⟨i, hi, j, hj, hu⟩ | ⟨j, hj, hu⟩
    · rw [mem_arQ_start] at hu; subst hu
      exact ⟨i * N + j, rm_lt (by omega) hj, rfl, zres _⟩
    · rw [mem_alQ_start] at hu; subst hu
      exact ⟨(N - 1) * N + j, rm_lt (by omega) hj, rfl, zres _⟩
  · have hN0 : 0 < N := by omega
    have hr' : r = r / N * N + r % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod r N).symm
    have hi : r / N < N := (Nat.div_lt_iff_lt_mul hN0).mpr hr
    have hj : r % N < N := Nat.mod_lt r hN0
    by_cases hiN : r / N < N - 1
    · refine ⟨_, List.mem_append.mpr (.inl (List.mem_flatMap.mpr ⟨r / N, List.mem_range.mpr hiN,
        List.mem_flatMap.mpr ⟨r % N, List.mem_range.mpr hj, mem_arQ_start.mpr rfl⟩⟩)), rfl, ?_⟩
      show (r / N * N + r % N) * AccW = r * AccW
      rw [← hr']
    · refine ⟨_, List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨r % N, List.mem_range.mpr hj,
        mem_alQ_start.mpr rfl⟩)), rfl, ?_⟩
      show ((N - 1) * N + r % N) * AccW = r * AccW
      rw [show N - 1 = r / N by omega, ← hr']

end startq

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c bz t wf sh wa ub dt ps : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ bz.width = 1 ∧ t.width = 32 ∧ wf.width = N * N * W ∧ sh.width = N * N * W ∧
    wa.width = N * N * AccW ∧ ub.width = N * N * W ∧ dt.width = DW N * AccW ∧ ps.width = N * N * AccW

theorem ctrl_start {N : Nat} {dn bz t : LVec} (h1 : dn.width = 1) (h2 : bz.width = 1) (h3 : t.width = 32) :
    nbaFold "done" (ctrlQ N (kb false) (kb true) dn bz t) dn = kb false ∧
      nbaFold "busy" (ctrlQ N (kb false) (kb true) dn bz t) bz = kb true ∧
      nbaFold "t" (ctrlQ N (kb false) (kb true) dn bz t) t = tv 0 := by
  unfold ctrlQ
  simp only [condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, wr, h1, h2, h3, LVec.resizeU_one_l0,
    LVec.resizeU_one_l1, zres]
  refine ⟨?_, ?_, ?_⟩ <;> simp [nbaFold] <;> exact LVec.insertAt_zero_of_width_eq (by simp [h1, h2, h3])

/-- **A start cycle** clears and loads: the state `0` steps after a start with operands `A`, `B`. -/
theorem next_start {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (ck dn c bz t wf sh wa ub dt ps : LVec)
    (hw : Wd N W AccW dn c bz t wf sh wa ub dt ps) :
    ∃ sh' wa' ps', tpNext N W AccW ck (kb false) (kb true) (.ofBitVec A) (.ofBitVec B) dn c bz t wf sh wa ub dt ps =
      BS N W AccW A B 0 ck (kb false) (kb true) (.ofBitVec A) (.ofBitVec B) sh' wa' ps' ∧
      shOK N W B 0 sh' ∧ waOK N W AccW B 0 wa' ∧ psOK N W AccW A B 0 ps' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
  obtain ⟨cd, cb, ct⟩ := ctrl_start (N := N) h1 h3 h4
  refine ⟨nbaFold "wsh" (Q N W AccW (kb false) (kb true) (.ofBitVec A) (.ofBitVec B) dn c bz t wf sh wa ub dt ps) sh,
    nbaFold "wac" (Q N W AccW (kb false) (kb true) (.ofBitVec A) (.ofBitVec B) dn c bz t wf sh wa ub dt ps) wa,
    nbaFold "ps" (Q N W AccW (kb false) (kb true) (.ofBitVec A) (.ofBitVec B) dn c bz t wf sh wa ub dt ps) ps, ?_,
    ⟨by simp [h6], fun r _ hc => absurd (show r / N < 0 from hc) (Nat.not_lt_zero _)⟩,
    ⟨by simp [h7], fun r _ hc => False.elim (by have : N + 1 ≤ 0 := hc; omega)⟩,
    ⟨by simp [h10], fun r _ hc => False.elim (by
      have h' : N + 2 + r / N ≤ 0 := hc
      have := Nat.le_trans (Nat.le_add_right (N + 2) (r / N)) h'
      omega)⟩⟩
  unfold tpNext BS
  rw [commit_SS _ _ _ _ _ _ _ _ _ _ _ (fun u hu => Q_names u hu), fold_ctrl "done", fold_C, fold_ctrl "busy",
    fold_ctrl "t", fold_wf, fold_ub, fold_dat, cd, cb, ct, C_start h.hN h.hA h2, dat_start h.hN h.hA h9,
    cV_zero, datV_zero, wfV_zero, ubV_zero]
  unfold wfQ ubQ
  simp only [condTrue_knownBit, ↓reduceIte]
  rw [fold_whole _ _ h5, fold_whole _ _ h8]
  try rfl

theorem ctrl_reset {N : Nat} {s dn bz t : LVec} (h1 : dn.width = 1) (h3 : bz.width = 1) :
    nbaFold "done" (ctrlQ N (kb true) s dn bz t) dn = kb false ∧ nbaFold "busy" (ctrlQ N (kb true) s dn bz t) bz = kb false := by
  unfold ctrlQ
  simp only [condTrue_knownBit, ↓reduceIte, wr, h1, h3, LVec.resizeU_one_l0]
  refine ⟨?_, ?_⟩ <;> simp [nbaFold] <;> exact LVec.insertAt_zero_of_width_eq (by simp [h1, h3])

/-- A reset cycle clears `busy` and `done`. -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c bz t wf sh wa ub dt ps : LVec)
    (hw : Wd N W AccW dn c bz t wf sh wa ub dt ps) :
    ∃ c' t' wf' sh' wa' ub' dt' ps', tpNext N W AccW ck (kb true) s a b dn c bz t wf sh wa ub dt ps =
      SS ck (kb true) s a b (kb false) c' (kb false) t' wf' sh' wa' ub' dt' ps' := by
  obtain ⟨h1, -, h3, -⟩ := hw
  obtain ⟨cd, cb⟩ := ctrl_reset (N := N) (s := s) (t := t) h1 h3
  unfold tpNext
  rw [commit_SS _ _ _ _ _ _ _ _ _ _ _ (fun u hu => Q_names u hu), fold_ctrl "done", fold_ctrl "busy", cd, cb]
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- An idle cycle (no reset, no start, `busy` = 0) changes neither `done` nor `C`. -/
theorem next_idle {N W AccW : Nat} (ck a b dn c t wf sh wa ub dt ps : LVec) :
    ∃ t' wf' sh' wa' ub' dt' ps', tpNext N W AccW ck (kb false) (kb false) a b dn c (kb false) t wf sh wa ub dt ps =
      SS ck (kb false) (kb false) a b dn c (kb false) t' wf' sh' wa' ub' dt' ps' := by
  unfold tpNext
  rw [commit_SS _ _ _ _ _ _ _ _ _ _ _ (fun u hu => Q_names u hu), fold_ctrl "done", fold_ctrl "busy", fold_C]
  have hc : arQs N AccW (kb false) (kb false) t c ++ alQs N AccW (kb false) (kb false) t c ps = [] := by
    simp [arQs, alQs, arQ, alQ]
  have hq : ctrlQ N (kb false) (kb false) dn (kb false) t = [] := by simp [ctrlQ]
  rw [hc, hq]
  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-! ## 8. Shape, termination and the phase model -/

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c bz t wf sh wa ub dt ps, st = SS ck r s a b dn c bz t wf sh wa ub dt ps ∧
    Wd N W AccW dn c bz t wf sh wa ub dt ps

theorem tpNext_I (N W AccW : Nat) (ck r s a b dn c bz t wf sh wa ub dt ps : LVec)
    (hw : Wd N W AccW dn c bz t wf sh wa ub dt ps) :
    I N W AccW (tpNext N W AccW ck r s a b dn c bz t wf sh wa ub dt ps) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
  unfold tpNext
  rw [commit_SS _ _ _ _ _ _ _ _ _ _ _ (fun u hu => Q_names u hu)]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, *]⟩

theorem tp_noq (N W AccW : Nat) : (tpD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [tpD, genPs, dsPs, dtPs, p0Ps, pkPs, arPs, alPs, ctrlP, wfP, ubP, dsP, dtP, p0P, pkP, arP, alP, nb,
    List.any_flatMap, List.any_map, List.any_append, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
    Stmt2.listHasQualifiedCase]

theorem SS_inj {ck r s a b dn c bz t wf sh wa ub dt ps ck' r' s' a' b' dn' c' bz' t' wf' sh' wa' ub' dt' ps' : LVec}
    (h : SS ck r s a b dn c bz t wf sh wa ub dt ps = SS ck' r' s' a' b' dn' c' bz' t' wf' sh' wa' ub' dt' ps') :
    dn = dn' ∧ c = c' ∧ bz = bz' ∧ t = t' ∧ wf = wf' ∧ sh = sh' ∧ wa = wa' ∧ ub = ub' ∧ dt = dt' ∧ ps = ps' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- After `4N` steps the accumulators hold the product. -/
theorem cV_fin (N W AccW : Nat) (A B : BitVec (N * N * W)) :
    cV N W AccW A B (4 * N) = Tasks.Matmul.product N W AccW A B := by
  rw [product_eq]
  unfold cV
  refine packBV_congr fun r hr => ?_
  have hN0 : 0 < N := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hr
  have hj : r % N < N := Nat.mod_lt r hN0
  unfold cE nC
  rw [show min N (4 * N - (2 * N + 1 + r % N)) = N by omega, Nat.sub_self, if_pos (Nat.zero_le _), Nat.sub_zero]
  rfl

theorem tp_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [tp_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW), .xVec 1,
    .xVec 32, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * AccW), .xVec (N * N * W), .xVec (DW N * AccW),
    .xVec (N * N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, tpD, tpDecls, SS]

/-- **Termination**: every schedule and every stimulus completes. -/
theorem tp_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hpu : ∀ st, PowerUp (design.sem N W AccW) st → I N W AccW st) : TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) hpu (fun σ => ⟨30, ?_⟩)
    (by rw [tp_sem_eq N W AccW hN hW hA]; exact tp_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, hw⟩
  exact ⟨_, _, tp_cycle N W AccW hN hW hA σ e ck r s a b dn c bz t wf sh wa ub dt ps kk 30 (Nat.le_refl _),
    tpNext_I N W AccW _ _ _ _ _ dn c bz t wf sh wa ub dt ps hw⟩

/-! ### The phase model -/

/-- The state `t` busy cycles after a start with operands `A`, `B`. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b sh wa ps, st = BS N W AccW A B t ck r s a b sh wa ps ∧ shOK N W B t sh ∧ waOK N W AccW B t wa ∧
    psOK N W AccW A B t ps

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b t wf sh wa ub dt ps, st = SS ck r s a b (kb true) (.ofBitVec (Tasks.Matmul.product N W AccW A B))
    (kb false) t wf sh wa ub dt ps

/-- One cycle from a state of the shape, evaluated (`tp_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c bz t wf sh wa ub dt ps, prev = SS ck r s a b dn c bz t wf sh wa ub dt ps ∧
    Wd N W AccW dn c bz t wf sh wa ub dt ps ∧
    st = tpNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
      dn c bz t wf sh wa ub dt ps

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- **The phase model** at `(N, W, AccW)`, latency `4N`: `Ready` after a reset, `Busy x m` the state
`t = 4N - 1 - m` busy cycles after a start, `Fin x` the product shown. -/
def model (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (4 * N) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := tp_init N W AccW h.hN h.hW h.hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (tp_cycle N W AccW h.hN h.hW h.hA σ e ck r s a b dn c bz t wf sh wa ub dt ps k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, -, hw, rfl⟩
    exact tpNext_I N W AccW _ _ _ _ _ dn c bz t wf sh wa ub dt ps hw
  Ready st := ∃ ck r s a b c t wf sh wa ub dt ps, st = SS ck r s a b (kb false) c (kb false) t wf sh wa ub dt ps
  Busy x m st := ∃ t, t + m + 1 = 4 * N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, t, wf, sh, wa, ub, dt, ps, rfl⟩
    simp [BitIs, Tasks.Matmul.task, SS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, sh, wa, ps, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, BS, SS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, t, wf, sh, wa, ub, dt, ps, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, SS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', t', wf', sh', wa', ub', dt', ps', hn⟩ := next_reset (appIn e "clk" ck) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c bz t wf sh wa ub dt ps hw
    rw [hn]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    obtain ⟨sh', wa', ps', he, h1, h2, h3⟩ := next_start h x.1 x.2.1 (appIn e "clk" ck) dn c bz t wf sh wa ub dt ps hw
    rw [he]
    exact .inr ⟨4 * N - 1, by have := h.hN; omega, 0, by have := h.hN; omega, _, _, _, _, _, _, _, _, rfl, h1, h2, h3⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, bz, t', wf, sh, wa, ub, dt, ps, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', sh0, wa0, ps0, hb, hsh, hwa, hps⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := SS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨sh', wa', ps', he, h1, h2, h3⟩ := next_busy h _ _ (show t < 4 * N by omega) (appIn e "clk" ck)
      (appIn e "A" a) (appIn e "B" b) _ _ _ hsh hwa hps
    rw [he]
    by_cases hf : t + 1 = 4 * N
    · left
      rw [hf, cV_fin]
      simp only [decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, _, _, rfl, h1, h2, h3⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', t', wf', sh', wa', ub', dt', ps', hb⟩ hr hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := SS_inj hb
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨t'', wf'', sh'', wa'', ub'', dt'', ps'', hn⟩ := next_idle (N := N) (W := W) (AccW := AccW)
      (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) (kb false) c' t' wf' sh' wa' ub' dt' ps'
    rw [hn]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', t', wf', sh', wa', ub', dt', ps', hb⟩ hr hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := SS_inj hb
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨t'', wf'', sh'', wa'', ub'', dt'', ps'', hn⟩ := next_idle (N := N) (W := W) (AccW := AccW)
      (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) (kb true)
      (.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) t' wf' sh' wa' ub' dt' ps'
    rw [hn]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ## 9. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3) -/

theorem tp_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [tp_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "busy", "t", "wf", "wsh", "wac", "ub", "dat", "ps"] :
      List String).Nodup
    decide⟩

theorem tp_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [tp_sem_eq N W AccW hN hW hA]
  refine ⟨by simp [Tasks.Matmul.task, tpD, tpDecls, Design2.inputNames], fun p hp => ?_⟩
  rcases tp_mem' hp with rfl | rfl | rfl | ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, wfP, ubP, dsP, dtP, p0P, pkP, arP, alP, nb, c32, sext, edgeClock, asyncReset,
      processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-- **Rule 1.** -/
theorem tp_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [tp_sem_eq N W AccW hN hW hA]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (tp_profile N W AccW hN)))
    (by simp [tpD, tpDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem tp_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [tp_sem_eq N W AccW hN hW hA] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨bz, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨t, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨wf, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨sh, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨wa, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨ub, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨dt, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨ps, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain rfl := powerUp_nil.mp h15
  exact ⟨ck, r, s, a, b, dn, c, bz, t, wf, sh, wa, ub, dt, ps, rfl, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

section xs
variable {N W AccW : Nat}

theorem ctrl_xsafe : xsProc (tpD N W AccW) (ctrlP N) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ctrlP, nb, c32, tpD, tpDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem wf_xsafe : xsProc (tpD N W AccW) (wfP N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, wfP, c32, tpD, tpDecls, LVec.ofInt]

theorem ub_xsafe : xsProc (tpD N W AccW) (ubP N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ubP, c32, tpD, tpDecls, LVec.ofInt]

theorem ds_xsafe (hN : 1 ≤ N) {k e : Nat} (hk : k < N) (he : e < N + k - 1) :
    xsProc (tpD N W AccW) (dsP N AccW k e) = true := by
  have hrow := base_row_le N hN hk
  have h1 : (base N k + e) * AccW + AccW ≤ DW N * AccW := winle AccW (by omega)
  have h2 : (base N k + e + 1) * AccW + AccW ≤ DW N * AccW := winle AccW (by omega)
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, dsP, tpD, tpDecls, LVec.replicate_l0,
    h1, h2]

theorem dt_xsafe (hN : 1 ≤ N) (hW : 1 ≤ W) {k : Nat} (hk : k < N) :
    xsProc (tpD N W AccW) (dtP N W AccW k) = true := by
  have hrow := base_row_le N hN hk
  have h1 : (base N k + N + k - 1) * AccW + AccW ≤ DW N * AccW := winle AccW (by omega)
  have h2 : k * W + W ≤ N * N * W := winle W (by have := Nat.le_mul_of_pos_left N hN; omega)
  have h3 : k * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, dtP, sext, c32, tpD, tpDecls,
    LVec.replicate_l0, LVec.ofInt, h1, h2, h3]

theorem p0_xsafe (hN : 1 ≤ N) (hW : 1 ≤ W) {j : Nat} (hj : j < N) : xsProc (tpD N W AccW) (p0P N W AccW j) = true := by
  have hDN : N ≤ DW N := by have := base_row_le N hN (show 0 < N by omega); simp [base] at this; omega
  have hjN : j < N * N := by have := Nat.le_mul_of_pos_left N hN; omega
  have h1 : j * W + W ≤ N * N * W := winle W hjN
  have h2 : j * AccW + AccW ≤ N * N * AccW := winle AccW hjN
  have h3 : ((N - 1) * N + j) * W + W ≤ N * N * W := winle W (rm_lt (by omega) hj)
  have h4 : (N - 1 - j) * AccW + AccW ≤ DW N * AccW := winle AccW (by omega)
  have h6 : j * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, p0P, sext, c32, tpD, tpDecls,
    LVec.replicate_l0, LVec.ofInt, h1, h2, h3, h4, h6]

theorem pk_xsafe (hN : 1 ≤ N) (hW : 1 ≤ W) {k j : Nat} (hk : k < N - 1) (hj : j < N) :
    xsProc (tpD N W AccW) (pkP N W AccW k j) = true := by
  have hrow := base_row_le N hN (show k + 1 < N by omega)
  have r1 := rm_lt (show k + 1 < N by omega) hj
  have r2 := rm_lt (show k < N by omega) hj
  have h1 : ((k + 1) * N + j) * W + W ≤ N * N * W := winle W r1
  have h2 : ((k + 1) * N + j) * AccW + AccW ≤ N * N * AccW := winle AccW r1
  have h3 : (k * N + j) * W + W ≤ N * N * W := winle W r2
  have h4 : (k * N + j) * AccW + AccW ≤ N * N * AccW := winle AccW r2
  have h5 : (base N (k + 1) + N - 1 - j) * AccW + AccW ≤ DW N * AccW := winle AccW (by omega)
  have h7 : ((k + 1) * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pkP, sext, c32, tpD, tpDecls,
    LVec.replicate_l0, LVec.ofInt, h1, h2, h3, h4, h5, h7]

theorem ar_xsafe {i j : Nat} (hi : i < N - 1) (hj : j < N) : xsProc (tpD N W AccW) (arP N AccW i j) = true := by
  have h1 : (i * N + j) * AccW + AccW ≤ N * N * AccW := winle AccW (rm_lt (by omega) hj)
  have h2 : ((i + 1) * N + j) * AccW + AccW ≤ N * N * AccW := winle AccW (rm_lt (by omega) hj)
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, arP, c32, tpD, tpDecls,
    LVec.replicate_l0, LVec.ofInt, h1, h2]

theorem al_xsafe (hN : 1 ≤ N) {j : Nat} (hj : j < N) : xsProc (tpD N W AccW) (alP N AccW j) = true := by
  have h1 : ((N - 1) * N + j) * AccW + AccW ≤ N * N * AccW := winle AccW (rm_lt (by omega) hj)
  have h2 : j * AccW + AccW ≤ N * N * AccW := winle AccW (by have := Nat.le_mul_of_pos_left N hN; omega)
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, alP, c32, tpD, tpDecls,
    LVec.replicate_l0, LVec.ofInt, h1, h2]

end xs

/-- **Rule 3.** -/
theorem tp_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) : XSafe (design.sem N W AccW) := by
  rw [tp_sem_eq N W AccW hN hW hA]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases tp_mem' hp with rfl | rfl | rfl | ⟨k, e, hk, he, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, j, hk, hj, rfl⟩ |
      ⟨i, j, hi, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ctrl_xsafe
  · exact wf_xsafe
  · exact ub_xsafe
  · exact ds_xsafe hN hk he
  · exact dt_xsafe hN hW hk
  · exact p0_xsafe hN hW hj
  · exact pk_xsafe hN hW hk hj
  · exact ar_xsafe hi hj
  · exact al_xsafe hN hj

/-- **The design satisfies the matmul statement (txtask-v2) at latency `4N`** (`16` at the scoring point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, hNA⟩ := hp
  have h : Rng N W AccW := ⟨hN, hW, hA, hNW, hNA⟩
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (tp_interface N W AccW hN hW hA)
    (tp_disciplined N W AccW hN hW hA) (tp_terminatesPU N W AccW hN hW hA (tp_powerUp N W AccW hN hW hA))
    (show 1 ≤ 4 * N by omega) (model N W AccW h) (tp_powerUp N W AccW hN hW hA) (tp_moore N W AccW hN hW hA)
    (tp_xsafe N W AccW hN hW hA)

end Submission
