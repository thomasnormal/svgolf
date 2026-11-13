-- svgolf-latency: 17
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
# Gemmini's weight-stationary array (translated), task `matmul`, latency `4N + 1`

Proof plan (the matmul reference's eight steps): agreement with a hand-built design, the FF-only
clock step, an invariant over the row schedule of the preload and compute passes, the phase model.
-/

namespace Submission

open LeanModels.Sv SvGolf

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- The latency: `done` shows `4N + 1` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := 4 * N + 1

/-- The triangle number `j (j + 1) / 2`: the offset of lane `j` in a packed triangle of lanes. -/
def tri (j : Nat) : Nat := j * (j + 1) / 2

theorem tri_succ (j : Nat) : tri (j + 1) = tri j + (j + 1) := by
  unfold tri
  have : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ (by decide)]

theorem tri_mono {i j : Nat} (h : i < j) : tri i + i + 1 ≤ tri j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [tri_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := ih h; omega
    · omega

theorem tri_le {i N : Nat} (h : i < N) : tri i + i + 1 ≤ tri N := tri_mono h

/-! ## 1. The hand-built design -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- A nonblocking write of a constant to a whole signal. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The MAC of PE `(r, c)`: `m_b + sext(m_a) * (wp[r+c] ? sext(c2) : sext(c1))`, at `AccW` bits. -/
def macE (N W AccW r c : Nat) : Expr2 :=
  .resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "m_b") ((r * N + c) * AccW) AccW))
    (.binary .mul (sext "m_a" AccW ((r * N + c) * W) W)
      (.ternary (.slice (.ident "wp") (r + c) 1) (sext "c2" AccW ((r * N + c) * W) W)
        (sext "c1" AccW ((r * N + c) * W) W))))

/-- The controller. -/
def ctrlP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "step" (LVec.replicate 32 .l0), nb "in_prop" ⟨#[.l0]⟩])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "step" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "in_prop") (.unary .bnot (.ident "in_prop")),
        .nbaAssign (.ident "a_rows") (.ident "A"), .nbaAssign (.ident "w_rows") (.ident "B")])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "step") (.binary .add (.ident "step") (c32 1)),
          .ifStmt (.binary .eq (.ident "step") (.binary .sub (c32 N) (c32 1)))
            (.nbaAssign (.ident "in_prop") (.unary .bnot (.ident "in_prop"))) none,
          .ifStmt (.binary .lt (.ident "step") (c32 N))
            (.nbaAssign (.ident "w_rows") (.binary (.shl false) (.ident "w_rows") (.binary .mul (c32 N) (c32 W))))
            none,
          .ifStmt (.binary .ge (.ident "step") (c32 N))
            (.nbaAssign (.ident "a_rows") (.binary (.shr false) (.ident "a_rows") (.binary .mul (c32 N) (c32 W))))
            none,
          .ifStmt (.binary .eq (.ident "step") (c32 ((4 * N : Nat) : Int)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The valid wavefront's head and shift, the propagate beside the buffers, Tile (0, 0)'s propagate. -/
def waveP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .nbaAssign (.ident "wv") (.binary (.shl false) (.ident "wv") (c32 1)),
    .nbaAssign (.slice "wv" 0 1) (.binary .and (.ident "busy") (.binary .lt (.ident "step") (c32 ((2 * N : Nat) : Int)))),
    .nbaAssign (.ident "pb") (.ident "in_prop"),
    .ifStmt (.slice (.ident "wv") 0 1) (.nbaAssign (.slice "wp" 0 1) (.ident "pb")) none])

/-- The propagate wavefront, stage `k + 1`. -/
def propP (k : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.slice (.ident "wv") (k + 1) 1)
    (.nbaAssign (.slice "wp" (k + 1) 1) (.slice (.ident "wp") k 1)) none)

/-- Row lane `r` of `a` and Mesh row `r`'s `a` registers. -/
def rowP (N W r : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .nbaAssign (.slice "sk_a" (tri r * W) ((r + 1) * W))
      (.binary (.shl false) (.slice (.ident "sk_a") (tri r * W) ((r + 1) * W)) (c32 W)),
    .nbaAssign (.slice "sk_a" (tri r * W) W) (.slice (.ident "a_rows") (r * W) W),
    .nbaAssign (.slice "m_a" (r * N * W) (N * W))
      (.binary (.shl false) (.slice (.ident "m_a") (r * N * W) (N * W)) (c32 W)),
    .nbaAssign (.slice "m_a" (r * N * W) W) (.slice (.ident "sk_a") ((tri r + r) * W) W)])

/-- Column lane `c` of `d`, Tile `(0, c)`'s `b` and `d` registers, the output register and lane of column `c`. -/
def colP (N W AccW c : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .nbaAssign (.slice "sk_d" (tri c * W) ((c + 1) * W))
      (.binary (.shl false) (.slice (.ident "sk_d") (tri c * W) ((c + 1) * W)) (c32 W)),
    .nbaAssign (.slice "sk_d" (tri c * W) W) (.slice (.ident "w_rows") (((N - 1) * N + c) * W) W),
    .ifStmt (.slice (.ident "wv") c 1)
      (.block #[.nbaAssign (.slice "m_b" (c * AccW) AccW) (.lit (LVec.replicate AccW .l0)),
        .nbaAssign (.slice "m_d" (c * W) W) (.slice (.ident "sk_d") ((tri c + c) * W) W)]) none,
    .nbaAssign (.slice "sk_o" (tri (N - 1 - c) * AccW) ((N - c) * AccW))
      (.binary (.shl false) (.slice (.ident "sk_o") (tri (N - 1 - c) * AccW) ((N - c) * AccW)) (c32 AccW)),
    .ifStmt (.slice (.ident "wv") (N + c) 1)
      (.nbaAssign (.slice "sk_o" (tri (N - 1 - c) * AccW) AccW) (macE N W AccW (N - 1) c)) none])

/-- Tile `(r + 1, c)`'s `b` and `d` registers, fed by PE `(r, c)`. -/
def pipeP (N W AccW r c : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.slice (.ident "wv") (r + c + 1) 1)
    (.block #[.nbaAssign (.slice "m_b" (((r + 1) * N + c) * AccW) AccW) (macE N W AccW r c),
      .nbaAssign (.slice "m_d" (((r + 1) * N + c) * W) W)
        (.ternary (.slice (.ident "wp") (r + c) 1) (.slice (.ident "c1") ((r * N + c) * W) W)
          (.slice (.ident "c2") ((r * N + c) * W) W))]) none)

/-- PE `(r, c)`'s weight registers. -/
def tileP (N W r c : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.slice (.ident "wv") (r + c + 1) 1)
    (.block #[.ifStmt (.slice (.ident "wp") (r + c) 1)
      (.nbaAssign (.slice "c1" ((r * N + c) * W) W) (.slice (.ident "m_d") ((r * N + c) * W) W))
      (some (.nbaAssign (.slice "c2" ((r * N + c) * W) W) (.slice (.ident "m_d") ((r * N + c) * W) W)))]) none)

/-- The capture of `C(u, c)`. -/
def outP (N AccW u c : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.binary .and (.ident "busy")
      (.binary .eq (.ident "step") (.binary .add (c32 ((3 * N + 1 : Nat) : Int)) (c32 u))))
    (.nbaAssign (.slice "C" ((u * N + c) * AccW) AccW)
      (.slice (.ident "sk_o") ((tri (N - 1 - c) + (N - 1 - c)) * AccW) AccW)) none)

/-- The declarations. -/
def gmDecls (N W AccW : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true }, { name := "busy", width := 1 },
   { name := "in_prop", width := 1 }, { name := "step", width := 32 }, { name := "a_rows", width := N * N * W },
   { name := "w_rows", width := N * N * W }, { name := "sk_a", width := tri N * W },
   { name := "sk_d", width := tri N * W }, { name := "sk_o", width := tri N * AccW },
   { name := "wv", width := 2 * N }, { name := "pb", width := 1 }, { name := "wp", width := 2 * N - 1 },
   { name := "m_a", width := N * N * W }, { name := "m_d", width := N * N * W },
   { name := "m_b", width := N * N * AccW }, { name := "c1", width := N * N * W }, { name := "c2", width := N * N * W }]

def propPs (N : Nat) : List Process2 := (List.range (2 * N - 2)).map propP
def rowPs (N W : Nat) : List Process2 := (List.range N).map (rowP N W)
def colPs (N W AccW : Nat) : List Process2 := (List.range N).map (colP N W AccW)
def pipePs (N W AccW : Nat) : List Process2 :=
  (List.range (N - 1)).flatMap fun r => (List.range N).map (pipeP N W AccW r)
def tilePs (N W : Nat) : List Process2 := (List.range N).flatMap fun r => (List.range N).map (tileP N W r)
def outPs (N AccW : Nat) : List Process2 := (List.range N).flatMap fun u => (List.range N).map (outP N AccW u)

/-- The generated processes, in source order. -/
def genPs (N W AccW : Nat) : List Process2 :=
  propPs N ++ (rowPs N W ++ (colPs N W AccW ++ (pipePs N W AccW ++ (tilePs N W ++ outPs N AccW))))

def gmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (gmDecls N W AccW).toArray
  processes := (ctrlP N W :: waveP N :: genPs N W AccW).toArray

/-! ## 2. Agreement: the stages of `instantiate2` -/

def gmScopeRaw (N W AccW : Nat) : IEnv :=
  { vals := [("OUT0", 3 * (N : Int) + 1), ("FOUR_N", 4 * (N : Int)),
      ("TWO_N", 2 * (N : Int)), ("T", canonInt 32 true (((N : Int) * ((N : Int) + 1)).tdiv 2)),
      ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("T", 32), ("TWO_N", 32), ("FOUR_N", 32), ("OUT0", 32)] }

def gmScope (N W AccW : Nat) : IEnv :=
  { vals := [("OUT0", ((3 * N + 1 : Nat) : Int)), ("FOUR_N", ((4 * N : Nat) : Int)), ("TWO_N", ((2 * N : Nat) : Int)),
      ("T", ((tri N : Nat) : Int)), ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("T", 32), ("TWO_N", 32), ("FOUR_N", 32), ("OUT0", 32)] }

def gmEnvRaw (N W AccW : Nat) : IEnv :=
  { gmScopeRaw N W AccW with dims := dimTable (gmScopeRaw N W AccW) design.pdesign.decls }

def gmEnv (N W AccW : Nat) : IEnv :=
  { gmScope N W AccW with dims := dimTable (gmScope N W AccW) design.pdesign.decls }

theorem declTy (env : IEnv) :
    declConstType env (some (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32))) none =
      .ok none := rfl

theorem tyW (env : IEnv) :
    (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32)).width env = .ok 32 := rfl

theorem gm_paramEnv_raw (N W AccW : Nat) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (gmEnvRaw N W AccW) := by
  have h2 : ¬ ((N : Int) < 0) := by omega
  simp [PDesign.paramEnv2, design.pdesign, bindPackageParams, bindPackageEnums, bindParamsRes, bindParams,
    bindLocals, bindLocal, evalIntTarget, evalInt, bindEnums, IEnv.bindVal, declTy, tyW, gmEnvRaw, gmScopeRaw,
    h2, Gen2.except_ok_bind, Except.mapError, List.lookup, List.filterMapM, List.filterMapM.loop]

theorem tri_cast (N : Nat) : ((N : Int) * ((N : Int) + 1)).tdiv 2 = ((tri N : Nat) : Int) := by
  unfold tri
  have : ((N : Int) * ((N : Int) + 1)) = ((N * (N + 1) : Nat) : Int) := by push_cast; rfl
  rw [this]; rfl

theorem canonInt_small {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) : canonInt 32 true v = v := by
  have e : Int.emod v (2 ^ 32) = v := Int.emod_eq_of_lt h0 (by omega)
  unfold canonInt
  simp only [e]
  split
  · rename_i hc
    simp at hc
    omega
  · rfl

/-- `tri N ≤ N * N` (for `N ≥ 1`), so `T` is in the 32-bit range. -/
theorem tri_le_sq (N : Nat) : tri N ≤ N * N := by
  unfold tri
  have : N * (N + 1) ≤ 2 * (N * N) + 0 := by
    rcases N with _ | N
    · simp
    · have := Nat.mul_le_mul_left (N + 1) (show N + 1 + 1 ≤ 2 * (N + 1) by omega)
      rw [Nat.mul_comm (N + 1) (2 * (N + 1)), Nat.mul_assoc] at this; omega
  have := Nat.div_le_of_le_mul (m := N * (N + 1)) (n := N * N) (k := 2) (by omega)
  exact this

theorem gm_env_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) :
    gmEnvRaw N W AccW = gmEnv N W AccW := by
  have hsq : N * N ≤ N * N * W := Nat.le_mul_of_pos_right _ hW
  have ht := tri_le_sq N
  have ht' : tri N < 2 ^ 31 := by omega
  have e1 : canonInt 32 true (((N : Int) * ((N : Int) + 1)).tdiv 2) = ((tri N : Nat) : Int) := by
    rw [tri_cast, canonInt_small (by omega) (by omega)]
  have e2 : 2 * (N : Int) = ((2 * N : Nat) : Int) := by push_cast; rfl
  have e3 : 4 * (N : Int) = ((4 * N : Nat) : Int) := by push_cast; rfl
  have e4 : 3 * (N : Int) + 1 = ((3 * N + 1 : Nat) : Int) := by push_cast; rfl
  simp only [gmEnvRaw, gmEnv, gmScopeRaw, gmScope, e1, e2, e3, e4]

theorem gm_paramEnv (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (gmEnv N W AccW) := by
  rw [gm_paramEnv_raw, gm_env_eq N W AccW hN hW hr]

theorem natAbs_cast {x : Nat} {X : Int} (h : (x : Int) = X) (hx : 0 < x) : (X - 1).natAbs + 1 = x := by
  subst h; omega

theorem tri_pos {N : Nat} (hN : 1 ≤ N) : 0 < tri N := by
  have := tri_le (show 0 < N by omega); unfold tri at this ⊢; omega

theorem gm_decls (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    buildDecls (gmEnv N W AccW) design.pdesign.decls = .ok (gmDecls N W AccW) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have ht := tri_pos hN
  have h1 : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hW)
  have h2 : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hA)
  have h3 : (((tri N : Nat) : Int) * W - 1).natAbs + 1 = tri N * W := natAbs_cast (by push_cast; rfl) (Nat.mul_pos ht hW)
  have h4 : (((tri N : Nat) : Int) * AccW - 1).natAbs + 1 = tri N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos ht hA)
  have h5 : (2 * (N : Int) - 1).natAbs + 1 = 2 * N := natAbs_cast (by push_cast; rfl) (by omega)
  have h6 : (2 * (N : Int) - 1 - 1).natAbs + 1 = 2 * N - 1 := by omega
  have h7 : (2 * (N : Int) - 2).natAbs + 1 = 2 * N - 1 := by omega
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    gmEnv, gmScope, List.lookup, Gen2.except_ok_bind, gmDecls, h1, h2, h3, h4, h5, h6, h7]

def gmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "busy", "in_prop", "step", "a_rows", "w_rows", "sk_a", "sk_d",
    "sk_o", "wv", "pb", "wp", "m_a", "m_d", "m_b", "c1", "c2"].map (·, 1)

theorem gm_elems (N W AccW : Nat) : buildElems (gmEnv N W AccW) design.pdesign.decls = .ok gmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, gmEnv,
    gmScope, List.lookup, Gen2.except_ok_bind, gmElems]

/-- The instantiation environment. -/
abbrev gmE (N W AccW : Nat) : IEnv := (gmEnv N W AccW).withDecls (gmDecls N W AccW)

/-- The templates. -/
def ctrlT : PProcess := match design.pdesign.processes with
  | [p, _] => p
  | _ => .alwaysFF "" (.block [])
def waveT : PProcess := match design.pdesign.processes with
  | [_, p] => p
  | _ => .alwaysFF "" (.block [])
def propT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def rowT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.process p], _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def colT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.process p], _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def pipeT : PProcess := match design.pdesign.generates with
  | [_, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _, _] => p
  | _ => .alwaysFF "" (.block [])
def tileT : PProcess := match design.pdesign.generates with
  | [_, _, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])
def outT : PProcess := match design.pdesign.generates with
  | [_, _, _, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

macro "gm_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, gmEnv, gmScope, gmDecls, gmElems, ctrlT, waveT, propT, rowT, colT, pipeT, tileT, outT,
  ctrlP, waveP, propP, rowP, colP, pipeP, tileP, outP, macE, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, divOperandWidthSum2, arraySelWidth, instDivParts2, *])

/-- The window facts of a select `x[lo +: w]` of a `c`-bit signal, in the forms the instantiation writes. -/
theorem winF (X W C : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = X) (hW : (w : Int) = W)
    (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = lo ∧ X + W - 1 < C ∧ 1 ≤ X + W ∧ (X + W).toNat = lo + w ∧ 0 < W ∧ W.toNat = w ∧ X ≤ X + W - 1 := by
  subst hx hW hy; omega

/-- The window facts of a bit select `x[i]` of a `c`-bit signal. -/
theorem bitF (X C : Int) {i c : Nat} (h : i < c) (hx : (i : Int) = X) (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = i ∧ X < C ∧ ¬ X < 0 ∧ ¬ C ≤ X := by
  subst hx hy; omega


theorem tri_cast_sub {N c : Nat} (hc : c < N) :
    (((N : Int) - 1 - c) * ((N : Int) - c)).tdiv 2 = ((tri (N - 1 - c) : Nat) : Int) := by
  have h1 : ((N - 1 - c : Nat) : Int) = (N : Int) - 1 - c := by omega
  have h2 : (N : Int) - c = ((N - 1 - c : Nat) : Int) + 1 := by omega
  rw [h2, ← h1, tri_cast]

/-- The facts every instantiation `simp` here needs. -/
theorem inst_facts {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    ((1 : Int) ≤ N * N * W ∧ (1 : Int) ≤ N * N * AccW ∧ (1 : Int) ≤ ((tri N : Nat) : Int) * W ∧
      (1 : Int) ≤ ((tri N : Nat) : Int) * AccW ∧ (1 : Int) ≤ 2 * (N : Int) ∧ (1 : Int) ≤ 2 * (N : Int) - 1) ∧
    (0 < W ∧ 0 < AccW ∧ (0 : Int) < W ∧ (0 : Int) < AccW) ∧ (PartMode.up == PartMode.range) = false ∧
    ((((N : Int) * N * W - 1).natAbs : Int) + 1 = (N : Int) * N * W ∧
      (((N : Int) * N * AccW - 1).natAbs : Int) + 1 = (N : Int) * N * AccW ∧
      (((((tri N : Nat) : Int) * W - 1).natAbs : Nat) : Int) + 1 = ((tri N : Nat) : Int) * W ∧
      (((((tri N : Nat) : Int) * AccW - 1).natAbs : Nat) : Int) + 1 = ((tri N : Nat) : Int) * AccW ∧
      (((2 * (N : Int) - 1).natAbs : Nat) : Int) + 1 = 2 * (N : Int) ∧
      (((2 * (N : Int) - 2).natAbs : Nat) : Int) + 1 = 2 * (N : Int) - 1) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have ht := tri_pos hN
  have a1 : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl
  have a2 : ((N * N * AccW : Nat) : Int) = (N : Int) * N * AccW := by push_cast; rfl
  have a3 : ((tri N * W : Nat) : Int) = ((tri N : Nat) : Int) * W := by push_cast; rfl
  have a4 : ((tri N * AccW : Nat) : Int) = ((tri N : Nat) : Int) * AccW := by push_cast; rfl
  have := Nat.mul_pos hNN hW; have := Nat.mul_pos hNN hA; have := Nat.mul_pos ht hW; have := Nat.mul_pos ht hA
  exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, ⟨hW, hA, by omega, by omega⟩, rfl,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩⟩

theorem ctrl_inst (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    instProcess2 (gmE N W AccW) gmElems ctrlT = ctrlP N W := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem wave_inst (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    instProcess2 (gmE N W AccW) gmElems waveT = waveP N := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have b1 := bitF 0 (2 * (N : Int)) (i := 0) (c := 2 * N) (by omega) rfl (by push_cast; rfl)
  have b2 := bitF 0 (2 * (N : Int) - 1) (i := 0) (c := 2 * N - 1) (by omega) rfl (by omega)
  have b3 : (1 : Int) < 2 * N := by omega
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem prop_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hk : k < 2 * N - 2) :
    instProcess2 ((gmE N W AccW).bindVal "k" k) gmElems propT = propP k := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have b1 := bitF ((k : Int) + 1) (2 * (N : Int)) (i := k + 1) (c := 2 * N) (by omega) (by push_cast; rfl)
    (by push_cast; rfl)
  have b2 := bitF ((k : Int) + 1) (2 * (N : Int) - 1) (i := k + 1) (c := 2 * N - 1) (by omega) (by push_cast; rfl)
    (by omega)
  have b3 := bitF (k : Int) (2 * (N : Int) - 1) (i := k) (c := 2 * N - 1) (by omega) rfl (by omega)
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem row_inst (N W AccW r : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) :
    instProcess2 ((gmE N W AccW).bindVal "r" r) gmElems rowT = rowP N W r := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have hT := tri_cast r
  have htl := tri_le hr
  have hl1 : tri r * W + (r + 1) * W ≤ tri N * W := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hl2 : (tri r + r) * W + W ≤ tri N * W := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hl3 : r * N * W + N * W ≤ N * N * W := by
    rw [Nat.mul_assoc r, Nat.mul_assoc N N W, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
  have hl4 : r * W + W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show r + 1 ≤ N * N by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega)
    rw [Nat.succ_mul] at this; exact this
  have w1 := winF (((tri r : Nat) : Int) * W) (((r : Int) + 1) * W) (((tri N : Nat) : Int) * W)
    (lo := tri r * W) (w := (r + 1) * W) (c := tri N * W) hl1 (Nat.mul_pos (by omega) hW) (by push_cast; rfl)
    (by push_cast; rfl) (by push_cast; rfl)
  have hrW : W ≤ (r + 1) * W := Nat.le_mul_of_pos_left W (by omega)
  have w2 := winF (((tri r : Nat) : Int) * W) W (((tri N : Nat) : Int) * W) (lo := tri r * W) (w := W)
    (c := tri N * W) (by omega) hW (by push_cast; rfl) rfl (by push_cast; rfl)
  have w3 := winF ((r : Int) * W) W ((N : Int) * N * W) (lo := r * W) (w := W) (c := N * N * W) hl4 hW
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have w4 := winF ((r : Int) * N * W) ((N : Int) * W) ((N : Int) * N * W) (lo := r * N * W) (w := N * W)
    (c := N * N * W) hl3 (Nat.mul_pos (by omega) hW) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  have w5 := winF ((r : Int) * N * W) W ((N : Int) * N * W) (lo := r * N * W) (w := W)
    (c := N * N * W) (by have := Nat.le_mul_of_pos_left W (show 0 < N by omega); omega) hW (by push_cast; rfl) rfl
    (by push_cast; rfl)
  have w6 := winF ((((tri r : Nat) : Int) + r) * W) W (((tri N : Nat) : Int) * W) (lo := (tri r + r) * W) (w := W)
    (c := tri N * W) hl2 hW (by push_cast; rfl) rfl (by push_cast; rfl)
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

/-- Window facts of PE `(r, c)`'s MAC reads (`m_b`, `m_a`, `wp`, `c1`, `c2`), with `X = r * N + c` as `Int`. -/
theorem mac_facts {N W AccW r c : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) (hc : c < N)
    (X : Int) (hX : ((r * N + c : Nat) : Int) = X) :
    (0 ≤ X * AccW ∧ (X * AccW).toNat = (r * N + c) * AccW ∧ X * AccW + AccW - 1 < (N : Int) * N * AccW ∧
      1 ≤ X * AccW + AccW ∧ (X * AccW + AccW).toNat = (r * N + c) * AccW + AccW ∧ X * AccW ≤ X * AccW + AccW - 1) ∧
    (0 ≤ X * W ∧ (X * W).toNat = (r * N + c) * W ∧ X * W + W - 1 < (N : Int) * N * W ∧
      1 ≤ X * W + W ∧ (X * W + W).toNat = (r * N + c) * W + W ∧ X * W ≤ X * W + W - 1) ∧
    (0 ≤ X * W + W - 1 ∧ (X * W + W - 1).toNat = (r * N + c) * W + W - 1 ∧ X * W + W - 1 < (N : Int) * N * W ∧
      ¬ X * W + W - 1 < 0 ∧ ¬ (N : Int) * N * W ≤ X * W + W - 1) := by
  have h1 := Lib.rowMajor_window_le (w := AccW) hr hc
  have h2 := Lib.rowMajor_window_le (w := W) hr hc
  have e1 : (((r * N + c) * AccW : Nat) : Int) = X * AccW := by rw [← hX]; push_cast; rfl
  have e2 : (((r * N + c) * W : Nat) : Int) = X * W := by rw [← hX]; push_cast; rfl
  have e3 : ((N * N * AccW : Nat) : Int) = (N : Int) * N * AccW := by push_cast; rfl
  have e4 : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega,
    by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega, by omega⟩⟩

theorem col_inst (N W AccW c : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hc : c < N) :
    instProcess2 ((gmE N W AccW).bindVal "c" c) gmElems colT = colP N W AccW c := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have hT := tri_cast c
  have hT' := tri_cast_sub hc
  have htl := tri_le hc
  have hto := tri_le (show N - 1 - c < N by omega)
  have ho : N - 1 - (N - 1 - c) = c := by omega
  have hl1 : tri c * W + (c + 1) * W ≤ tri N * W := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hl2 : (tri c + c) * W + W ≤ tri N * W := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hl3 : tri (N - 1 - c) * AccW + (N - c) * AccW ≤ tri N * AccW := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hcN : c < N * N := by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega
  have hlast : (N - 1) * N + c < N * N := by
    have : (N - 1) * N + N = N * N := by rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hN]
    omega
  have cN1 : ((N - 1 : Nat) : Int) = (N : Int) - 1 := by omega
  have w1 := winF (((tri c : Nat) : Int) * W) (((c : Int) + 1) * W) (((tri N : Nat) : Int) * W)
    (lo := tri c * W) (w := (c + 1) * W) (c := tri N * W) hl1 (Nat.mul_pos (by omega) hW) (by push_cast; rfl)
    (by push_cast; rfl) (by push_cast; rfl)
  have hcW : W ≤ (c + 1) * W := Nat.le_mul_of_pos_left W (by omega)
  have w2 := winF (((tri c : Nat) : Int) * W) W (((tri N : Nat) : Int) * W) (lo := tri c * W) (w := W)
    (c := tri N * W) (by omega) hW (by push_cast; rfl) rfl (by push_cast; rfl)
  have hl5 : ((N - 1) * N + c) * W + W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show (N - 1) * N + c + 1 ≤ N * N by omega)
    rw [Nat.succ_mul] at this; exact this
  have w3 := winF ((((N : Int) - 1) * N + c) * W) W ((N : Int) * N * W) (lo := ((N - 1) * N + c) * W) (w := W)
    (c := N * N * W) hl5 hW (by push_cast [Int.ofNat_sub hN]; rfl) rfl (by push_cast; rfl)
  have b1 := bitF (c : Int) (2 * (N : Int)) (i := c) (c := 2 * N) (by omega) rfl (by push_cast; rfl)
  have w4 := winF ((c : Int) * AccW) AccW ((N : Int) * N * AccW) (lo := c * AccW) (w := AccW) (c := N * N * AccW)
    (by have := Nat.mul_le_mul_right AccW (show c + 1 ≤ N * N by omega); rw [Nat.succ_mul] at this; exact this) hA
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have w5 := winF ((c : Int) * W) W ((N : Int) * N * W) (lo := c * W) (w := W) (c := N * N * W)
    (by have := Nat.mul_le_mul_right W (show c + 1 ≤ N * N by omega); rw [Nat.succ_mul] at this; exact this) hW
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have w6 := winF ((((tri c : Nat) : Int) + c) * W) W (((tri N : Nat) : Int) * W) (lo := (tri c + c) * W) (w := W)
    (c := tri N * W) hl2 hW (by push_cast; rfl) rfl (by push_cast; rfl)
  have w7 := winF (((tri (N - 1 - c) : Nat) : Int) * AccW) (((N : Int) - c) * AccW) (((tri N : Nat) : Int) * AccW)
    (lo := tri (N - 1 - c) * AccW) (w := (N - c) * AccW) (c := tri N * AccW) hl3 (Nat.mul_pos (by omega) hA)
    (by push_cast; rfl) (by push_cast [Int.ofNat_sub (show c ≤ N by omega)]; rfl) (by push_cast; rfl)
  have hl6 : tri (N - 1 - c) * AccW + AccW ≤ tri N * AccW := by
    have := Nat.mul_le_mul_right AccW (show tri (N - 1 - c) + 1 ≤ tri N by omega)
    rw [Nat.succ_mul] at this; exact this
  have w8 := winF (((tri (N - 1 - c) : Nat) : Int) * AccW) AccW (((tri N : Nat) : Int) * AccW)
    (lo := tri (N - 1 - c) * AccW) (w := AccW) (c := tri N * AccW) hl6 hA (by push_cast; rfl) rfl (by push_cast; rfl)
  have b2 := bitF ((N : Int) + c) (2 * (N : Int)) (i := N + c) (c := 2 * N) (by omega) (by push_cast; rfl)
    (by push_cast; rfl)
  have b3 := bitF ((N : Int) - 1 + c) (2 * (N : Int) - 1) (i := N - 1 + c) (c := 2 * N - 1) (by omega) (by omega)
    (by omega)
  have mf := mac_facts hN hW hA (show N - 1 < N by omega) hc (((N : Int) - 1) * N + c)
    (by push_cast [Int.ofNat_sub hN]; rfl)
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨m7, m8, m9, m10, m11, m12⟩, ⟨m13, m14, m15, m16, m17⟩⟩ := mf
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem pipe_inst (N W AccW r c : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r + 1 < N) (hc : c < N) :
    instProcess2 (((gmE N W AccW).bindVal "r" r).bindVal "c" c) gmElems pipeT = pipeP N W AccW r c := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have b1 := bitF ((r : Int) + c + 1) (2 * (N : Int)) (i := r + c + 1) (c := 2 * N) (by omega) (by push_cast; rfl)
    (by push_cast; rfl)
  have b2 := bitF ((r : Int) + c) (2 * (N : Int) - 1) (i := r + c) (c := 2 * N - 1) (by omega) (by push_cast; rfl)
    (by omega)
  have mf := mac_facts hN hW hA (show r < N by omega) hc ((r : Int) * N + c) (by push_cast; rfl)
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, ⟨m7, m8, m9, m10, m11, m12⟩, ⟨m13, m14, m15, m16, m17⟩⟩ := mf
  have nf := mac_facts hN hW hA hr hc (((r : Int) + 1) * N + c) (by push_cast; rfl)
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, ⟨n7, n8, n9, n10, n11, n12⟩, -⟩ := nf
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem tile_inst (N W AccW r c : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : r < N) (hc : c < N) :
    instProcess2 (((gmE N W AccW).bindVal "r" r).bindVal "c" c) gmElems tileT = tileP N W r c := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have b1 := bitF ((r : Int) + c + 1) (2 * (N : Int)) (i := r + c + 1) (c := 2 * N) (by omega) (by push_cast; rfl)
    (by push_cast; rfl)
  have b2 := bitF ((r : Int) + c) (2 * (N : Int) - 1) (i := r + c) (c := 2 * N - 1) (by omega) (by push_cast; rfl)
    (by omega)
  have mf := mac_facts hN hW hA hr hc ((r : Int) * N + c) (by push_cast; rfl)
  obtain ⟨-, ⟨m7, m8, m9, m10, m11, m12⟩, -⟩ := mf
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem out_inst (N W AccW u c : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hu : u < N) (hc : c < N) :
    instProcess2 (((gmE N W AccW).bindVal "u" u).bindVal "c" c) gmElems outT = outP N AccW u c := by
  obtain ⟨⟨d1, d2, d3, d4, d5, d6⟩, ⟨p1, p2, p3, p4⟩, hmode, ⟨a1, a2, a3, a4, a5, a6⟩⟩ := inst_facts hN hW hA
  have hT' := tri_cast_sub hc
  have hto := tri_le (show N - 1 - c < N by omega)
  have mf := mac_facts hN hW hA hu hc ((u : Int) * N + c) (by push_cast; rfl)
  obtain ⟨⟨m1, m2, m3, m4, m5, m6⟩, -, -⟩ := mf
  have w1 := winF ((((tri (N - 1 - c) : Nat) : Int) + N - 1 - c) * AccW) AccW (((tri N : Nat) : Int) * AccW)
    (lo := (tri (N - 1 - c) + (N - 1 - c)) * AccW) (w := AccW) (c := tri N * AccW)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)) hA
    (by push_cast [Int.ofNat_sub (show c ≤ N - 1 by omega), Int.ofNat_sub hN]; congr 1; omega) rfl
    (by push_cast; rfl)
  gm_simp
  try and_intros
  all_goals first | rfl | decide | skip


/-! ### The generates, the instantiation, the processes -/

def genG (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

def nP : PExpr := .paramRef "N" none

theorem gm_gens_src : design.pdesign.generates =
    [genG "Mesh_prop" "k" (.binary (.m0 .sub) (.binary .mul (.int 2) nP) (.int 2)) 6 ([propT].map .process),
     genG "MeshWithDelays_row" "r" nP 4 ([rowT].map .process),
     genG "MeshWithDelays_col" "c" nP 4 ([colT].map .process),
     genG "Mesh_pipe" "r" (.binary (.m0 .sub) nP (.int 1)) 3 [genG "Tile_in" "c" nP 4 ([pipeT].map .process)],
     genG "Mesh" "r" nP 4 [genG "Tile" "c" nP 4 ([tileT].map .process)],
     genG "Out_row" "u" nP 4 [genG "Out_col" "c" nP 4 ([outT].map .process)]] := rfl

theorem toNat_sub_zero (n : Nat) : ((n : Int) - 0).toNat = n := by omega

theorem gm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : 2 * N < F) :
    expandList2 (gmE N W AccW) gmElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have hNF : N < F := by omega
  have hNv : (gmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  have hv : ∀ (g : String) (v : Int), g ≠ "N" → ((gmE N W AccW).bindVal g v).vals.lookup "N" = some (N : Int) :=
    fun g v hg => by rw [vals_lookup_bindVal_ne _ hg.symm, hNv]
  have hK : ∀ v : Int, ((gmE N W AccW).bindVal "k" v).vals.lookup "N" = some (N : Int) := fun v => hv "k" v (by decide)
  have hR : ∀ v : Int, ((gmE N W AccW).bindVal "r" v).vals.lookup "N" = some (N : Int) := fun v => hv "r" v (by decide)
  have hC : ∀ v : Int, ((gmE N W AccW).bindVal "c" v).vals.lookup "N" = some (N : Int) := fun v => hv "c" v (by decide)
  have hU : ∀ v : Int, ((gmE N W AccW).bindVal "u" v).vals.lookup "N" = some (N : Int) := fun v => hv "u" v (by decide)
  have hRC : ∀ v w : Int, (((gmE N W AccW).bindVal "r" v).bindVal "c" w).vals.lookup "N" = some (N : Int) :=
    fun v w => by rw [vals_lookup_bindVal_ne _ (by decide), hR v]
  have hUC : ∀ v w : Int, (((gmE N W AccW).bindVal "u" v).bindVal "c" w).vals.lookup "N" = some (N : Int) :=
    fun v w => by rw [vals_lookup_bindVal_ne _ (by decide), hU v]
  have h2N : (2 * (N : Int) - 2 - 0).toNat = 2 * N - 2 := by omega
  have hN1 : ((N : Int) - 1 - 0).toNat = N - 1 := by omega
  rw [gm_gens_src, genPs]
  refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_cons_ok ?_
    (expandList2_cons_ok ?_ (expandList2_singleton_ok ?_)))))
  · rw [genG, nP, GenItem.expand2_genFor_ascending_processes (N := 2 * (N : Int) - 2) (evalInt_int 0)
      (fun v => isInt_binary_of rfl (isInt_binary_of rfl rfl (isInt_paramRef_of (hK v))) rfl)
      (fun v => evalInt_sub_of (isInt_binary_of rfl rfl (isInt_paramRef_of (hK v))) rfl
        (evalInt_mul_of rfl (isInt_paramRef_of (hK v)) (evalInt_int 2) (evalInt_paramRef_of (hK v))) (evalInt_int 2))
      (by rw [h2N]; omega), h2N, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, propPs]
    refine congrArg Res.ok ?_
    refine List.map_congr_left fun k hk => ?_
    exact prop_inst N W AccW k hN (List.mem_range.mp hk)
  · rw [genG, nP, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun v => isInt_paramRef_of (hR v)) (fun v => evalInt_paramRef_of (hR v))
      (by rw [toNat_sub_zero]; exact hNF), toNat_sub_zero, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, rowPs]
    refine congrArg Res.ok ?_
    refine List.map_congr_left fun r hr => ?_
    exact row_inst N W AccW r hN hW hA (List.mem_range.mp hr)
  · rw [genG, nP, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun v => isInt_paramRef_of (hC v)) (fun v => evalInt_paramRef_of (hC v))
      (by rw [toNat_sub_zero]; exact hNF), toNat_sub_zero, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, colPs]
    refine congrArg Res.ok ?_
    refine List.map_congr_left fun c hc => ?_
    exact col_inst N W AccW c hN hW hA (List.mem_range.mp hc)
  · rw [genG, nP, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int) - 1)
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [pipeT].map (instProcess2 (((gmE N W AccW).bindVal "r" v).bindVal "c" w) gmElems))
      (evalInt_int 0) (fun v => isInt_binary_of rfl (isInt_paramRef_of (hR v)) rfl)
      (fun v => evalInt_sub_of (isInt_paramRef_of (hR v)) rfl (evalInt_paramRef_of (hR v)) (evalInt_int 1))
      (by rw [hN1]; omega)]
    · simp only [intRange_zero, List.flatMap_map, hN1, List.map_cons, List.map_nil,
        Gen2.flatMap_singleton_map, pipePs]
      refine congrArg Res.ok ?_
      simp only [List.flatMap_def]
      refine congrArg List.flatten ?_
      refine List.map_congr_left fun r hr => List.map_congr_left fun c hc => ?_
      exact pipe_inst N W AccW r c hN hW hA (by have := List.mem_range.mp hr; omega) (List.mem_range.mp hc)
    · intro v _ _
      apply expandList2_singleton_ok
      rw [genG, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
        (fun w => isInt_paramRef_of (hRC v w)) (fun w => evalInt_paramRef_of (hRC v w))
        (by rw [toNat_sub_zero]; exact hNF), toNat_sub_zero]
  · rw [genG, nP, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [tileT].map (instProcess2 (((gmE N W AccW).bindVal "r" v).bindVal "c" w) gmElems))
      (evalInt_int 0) (fun v => isInt_paramRef_of (hR v))
      (fun v => evalInt_paramRef_of (hR v)) (by rw [toNat_sub_zero]; exact hNF)]
    · simp only [intRange_zero, List.flatMap_map, toNat_sub_zero, List.map_cons, List.map_nil,
        Gen2.flatMap_singleton_map, tilePs]
      refine congrArg Res.ok ?_
      simp only [List.flatMap_def]
      refine congrArg List.flatten ?_
      refine List.map_congr_left fun r hr => List.map_congr_left fun c hc => ?_
      exact tile_inst N W AccW r c hN hW hA (List.mem_range.mp hr) (List.mem_range.mp hc)
    · intro v _ _
      apply expandList2_singleton_ok
      rw [genG, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
        (fun w => isInt_paramRef_of (hRC v w)) (fun w => evalInt_paramRef_of (hRC v w))
        (by rw [toNat_sub_zero]; exact hNF), toNat_sub_zero]
  · rw [genG, nP, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [outT].map (instProcess2 (((gmE N W AccW).bindVal "u" v).bindVal "c" w) gmElems))
      (evalInt_int 0) (fun v => isInt_paramRef_of (hU v))
      (fun v => evalInt_paramRef_of (hU v)) (by rw [toNat_sub_zero]; exact hNF)]
    · simp only [intRange_zero, List.flatMap_map, toNat_sub_zero, List.map_cons, List.map_nil,
        Gen2.flatMap_singleton_map, outPs]
      refine congrArg Res.ok ?_
      simp only [List.flatMap_def]
      refine congrArg List.flatten ?_
      refine List.map_congr_left fun u hu => List.map_congr_left fun c hc => ?_
      exact out_inst N W AccW u c hN hW hA (List.mem_range.mp hu) (List.mem_range.mp hc)
    · intro v _ _
      apply expandList2_singleton_ok
      rw [genG, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
        (fun w => isInt_paramRef_of (hUC v w)) (fun w => evalInt_paramRef_of (hUC v w))
        (by rw [toNat_sub_zero]; exact hNF), toNat_sub_zero]

theorem gm_static (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.processes.map (instProcess2 (gmE N W AccW) gmElems) = [ctrlP N W, waveP N] := by
  rw [show design.pdesign.processes = [ctrlT, waveT] from rfl]
  simp only [List.map_cons, List.map_nil, ctrl_inst N W AccW hN hW hA, wave_inst N W AccW hN hW hA]

theorem gm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (gmEnv N W AccW) (gmDecls N W AccW) gmElems (genPs N W AccW)) := by
  refine PDesign.instantiate2_of_ok rfl (gm_paramEnv N W AccW hN hW hr) (gm_decls N W AccW hN hW hA)
    (gm_elems N W AccW) (gm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  have := Nat.mul_le_mul_right (N + (W + (AccW + 0)) + 2) (show 2 ≤ N + (W + (AccW + 0)) + 2 by omega)
  omega

theorem gm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList = ctrlP N W :: waveP N :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (gm_instantiate2 N W AccW hN hW hA hr), PDesign.assemble2_processes,
    gm_static N W AccW hN hW hA]
  simp [design.pdesign]

/-! ### Disjoint windows -/

abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

macro "wins_simp" : tactic => `(tactic| simp [ctrlP, waveP, propP, rowP, colP, pipeP, tileP, outP, nb,
  Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins])

theorem prop_wins (k : Nat) : (propP k).procWins = [("wp", some (k + 1, 1))] := by wins_simp
theorem row_wins (N W r : Nat) : (rowP N W r).procWins = [("sk_a", some (tri r * W, (r + 1) * W)),
    ("sk_a", some (tri r * W, W)), ("m_a", some (r * N * W, N * W)), ("m_a", some (r * N * W, W))] := by wins_simp
theorem col_wins (N W AccW c : Nat) : (colP N W AccW c).procWins = [("sk_d", some (tri c * W, (c + 1) * W)),
    ("sk_d", some (tri c * W, W)), ("m_b", some (c * AccW, AccW)), ("m_d", some (c * W, W)),
    ("sk_o", some (tri (N - 1 - c) * AccW, (N - c) * AccW)), ("sk_o", some (tri (N - 1 - c) * AccW, AccW))] := by
  wins_simp
theorem pipe_wins (N W AccW r c : Nat) : (pipeP N W AccW r c).procWins =
    [("m_b", some (((r + 1) * N + c) * AccW, AccW)), ("m_d", some (((r + 1) * N + c) * W, W))] := by wins_simp
theorem tile_wins (N W r c : Nat) : (tileP N W r c).procWins =
    [("c1", some ((r * N + c) * W, W)), ("c2", some ((r * N + c) * W, W))] := by wins_simp
theorem out_wins (N AccW u c : Nat) : (outP N AccW u c).procWins = [("C", some ((u * N + c) * AccW, AccW))] := by
  wins_simp

theorem mem_propPs {N : Nat} {p : Process2} (h : p ∈ propPs N) : ∃ k, k < 2 * N - 2 ∧ p = propP k := by
  simp only [propPs, List.mem_map, List.mem_range] at h; obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩
theorem mem_rowPs {N W : Nat} {p : Process2} (h : p ∈ rowPs N W) : ∃ r, r < N ∧ p = rowP N W r := by
  simp only [rowPs, List.mem_map, List.mem_range] at h; obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩
theorem mem_colPs {N W AccW : Nat} {p : Process2} (h : p ∈ colPs N W AccW) : ∃ c, c < N ∧ p = colP N W AccW c := by
  simp only [colPs, List.mem_map, List.mem_range] at h; obtain ⟨k, hk, rfl⟩ := h; exact ⟨k, hk, rfl⟩
theorem mem_pipePs {N W AccW : Nat} {p : Process2} (h : p ∈ pipePs N W AccW) :
    ∃ r c, r + 1 < N ∧ c < N ∧ p = pipeP N W AccW r c := by
  simp only [pipePs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨r, hr, c, hc, rfl⟩ := h; exact ⟨r, c, by omega, hc, rfl⟩
theorem mem_tilePs {N W : Nat} {p : Process2} (h : p ∈ tilePs N W) :
    ∃ r c, r < N ∧ c < N ∧ p = tileP N W r c := by
  simp only [tilePs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨r, hr, c, hc, rfl⟩ := h; exact ⟨r, c, hr, hc, rfl⟩
theorem mem_outPs {N AccW : Nat} {p : Process2} (h : p ∈ outPs N AccW) :
    ∃ u c, u < N ∧ c < N ∧ p = outP N AccW u c := by
  simp only [outPs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨r, hr, c, hc, rfl⟩ := h; exact ⟨r, c, hr, hc, rfl⟩

/-- The generated processes, case by case. -/
theorem gen_cases {N W AccW : Nat} {p : Process2} (hp : p ∈ genPs N W AccW) :
    (∃ k, p = propP k) ∨ (∃ r, p = rowP N W r) ∨
      (∃ c, p = colP N W AccW c) ∨ (∃ r c, p = pipeP N W AccW r c) ∨ (∃ r c, p = tileP N W r c) ∨
      (∃ u c, p = outP N AccW u c) := by
  simp only [genPs, List.mem_append] at hp
  rcases hp with hp | hp | hp | hp | hp | hp
  · obtain ⟨k, -, rfl⟩ := mem_propPs hp; exact .inl ⟨k, rfl⟩
  · obtain ⟨k, -, rfl⟩ := mem_rowPs hp; exact .inr (.inl ⟨k, rfl⟩)
  · obtain ⟨k, -, rfl⟩ := mem_colPs hp; exact .inr (.inr (.inl ⟨k, rfl⟩))
  · obtain ⟨r, c, -, -, rfl⟩ := mem_pipePs hp; exact .inr (.inr (.inr (.inl ⟨r, c, rfl⟩)))
  · obtain ⟨r, c, -, -, rfl⟩ := mem_tilePs hp; exact .inr (.inr (.inr (.inr (.inl ⟨r, c, rfl⟩))))
  · obtain ⟨r, c, -, -, rfl⟩ := mem_outPs hp; exact .inr (.inr (.inr (.inr (.inr ⟨r, c, rfl⟩))))

macro "disj_simp" : tactic => `(tactic| simp [Disj, prop_wins, row_wins, col_wins, pipe_wins, tile_wins, out_wins,
  DrvWin.overlaps])

theorem gm_pairwise (N W AccW : Nat) (hN : 1 ≤ N) :
    (ctrlP N W :: waveP N :: genPs N W AccW).Pairwise Disj := by
  -- the families
  have hprop : (propPs N).Pairwise Disj := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ _ h => ?_)
    disj_simp; omega
  have hrow : (rowPs N W).Pairwise Disj := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ _ h => ?_)
    have h1 : tri a * W + (a + 1) * W ≤ tri b * W := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono h; omega)
    have h2 : W ≤ (a + 1) * W := Nat.le_mul_of_pos_left W (by omega)
    have h3 := rowMajor_le (K := N * W) h
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h3
    have h4 : W ≤ N * W := Nat.le_mul_of_pos_left W (by omega)
    disj_simp; omega
  have hcol : (colPs N W AccW).Pairwise Disj := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ hb h => ?_)
    have hb' := List.mem_range.mp hb
    have h1 : tri a * W + (a + 1) * W ≤ tri b * W := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono h; omega)
    have h2 : W ≤ (a + 1) * W := Nat.le_mul_of_pos_left W (by omega)
    have h3 := rowMajor_le (K := AccW) h
    have h4 := rowMajor_le (K := W) h
    have h5 : tri (N - 1 - b) * AccW + (N - b) * AccW ≤ tri (N - 1 - a) * AccW := by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by have := tri_mono (show N - 1 - b < N - 1 - a by omega); omega)
    have h6 : AccW ≤ (N - b) * AccW := Nat.le_mul_of_pos_left AccW (by omega)
    disj_simp
    omega
  have hpipe : (pipePs N W AccW).Pairwise Disj := by
    refine pairwise_flatMap_range (fun r _ => ?_) ?_
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ _ h => ?_)
      have := rowMajor_le (K := AccW) (show (r + 1) * N + a < (r + 1) * N + b by omega)
      have := rowMajor_le (K := W) (show (r + 1) * N + a < (r + 1) * N + b by omega)
      disj_simp; omega
    · intro r r' hrr _ a ha b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
      have hlt : (r + 1) * N + c < (r' + 1) * N + c' := by
        have := rowMajor_le (K := N) (show r + 1 < r' + 1 by omega); have := List.mem_range.mp hc; omega
      have := rowMajor_le (K := AccW) hlt
      have := rowMajor_le (K := W) hlt
      disj_simp; omega
  have htile : (tilePs N W).Pairwise Disj := by
    refine pairwise_flatMap_range (fun r _ => ?_) ?_
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ _ h => ?_)
      have := rowMajor_le (K := W) (show r * N + a < r * N + b by omega)
      disj_simp; omega
    · intro r r' hrr _ a ha b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
      have hlt : r * N + c < r' * N + c' := by
        have := rowMajor_le (K := N) hrr; have := List.mem_range.mp hc; omega
      have := rowMajor_le (K := W) hlt
      disj_simp; omega
  have hout : (outPs N AccW).Pairwise Disj := by
    refine pairwise_flatMap_range (fun r _ => ?_) ?_
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {a b} _ _ h => ?_)
      have := rowMajor_le (K := AccW) (show r * N + a < r * N + b by omega)
      disj_simp; omega
    · intro r r' hrr _ a ha b hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hb
      have hlt : r * N + c < r' * N + c' := by
        have := rowMajor_le (K := N) hrr; have := List.mem_range.mp hc; omega
      have := rowMajor_le (K := AccW) hlt
      disj_simp; omega
  -- across families
  have xpr : ∀ a ∈ propPs N, ∀ b ∈ rowPs N W ++ (colPs N W AccW ++ (pipePs N W AccW ++ (tilePs N W ++ outPs N AccW))),
      Disj a b := by
    intro a ha b hb
    obtain ⟨k, -, rfl⟩ := mem_propPs ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb | hb | hb
    · obtain ⟨r, -, rfl⟩ := mem_rowPs hb; disj_simp
    · obtain ⟨c, -, rfl⟩ := mem_colPs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_pipePs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_tilePs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_outPs hb; disj_simp
  have xrc : ∀ a ∈ rowPs N W, ∀ b ∈ colPs N W AccW ++ (pipePs N W AccW ++ (tilePs N W ++ outPs N AccW)),
      Disj a b := by
    intro a ha b hb
    obtain ⟨k, -, rfl⟩ := mem_rowPs ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb | hb
    · obtain ⟨c, -, rfl⟩ := mem_colPs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_pipePs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_tilePs hb; disj_simp
    · obtain ⟨r, c, -, -, rfl⟩ := mem_outPs hb; disj_simp
  have xcp : ∀ a ∈ colPs N W AccW, ∀ b ∈ pipePs N W AccW ++ (tilePs N W ++ outPs N AccW), Disj a b := by
    intro a ha b hb
    obtain ⟨c, hc, rfl⟩ := mem_colPs ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · obtain ⟨r, c', -, -, rfl⟩ := mem_pipePs hb
      have hlt : c < (r + 1) * N + c' := by have := Nat.le_mul_of_pos_left N (show 0 < r + 1 by omega); omega
      have := rowMajor_le (K := AccW) hlt
      have := rowMajor_le (K := W) hlt
      disj_simp; omega
    · obtain ⟨r, c', -, -, rfl⟩ := mem_tilePs hb; disj_simp
    · obtain ⟨r, c', -, -, rfl⟩ := mem_outPs hb; disj_simp
  have xpt : ∀ a ∈ pipePs N W AccW, ∀ b ∈ tilePs N W ++ outPs N AccW, Disj a b := by
    intro a ha b hb
    obtain ⟨r, c, -, -, rfl⟩ := mem_pipePs ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · obtain ⟨r', c', -, -, rfl⟩ := mem_tilePs hb; disj_simp
    · obtain ⟨r', c', -, -, rfl⟩ := mem_outPs hb; disj_simp
  have xto : ∀ a ∈ tilePs N W, ∀ b ∈ outPs N AccW, Disj a b := by
    intro a ha b hb
    obtain ⟨r, c, -, -, rfl⟩ := mem_tilePs ha
    obtain ⟨r', c', -, -, rfl⟩ := mem_outPs hb; disj_simp
  have hgen : (genPs N W AccW).Pairwise Disj := by
    unfold genPs
    exact List.pairwise_append.mpr ⟨hprop, List.pairwise_append.mpr ⟨hrow, List.pairwise_append.mpr ⟨hcol,
      List.pairwise_append.mpr ⟨hpipe, List.pairwise_append.mpr ⟨htile, hout, xto⟩, xpt⟩, xcp⟩, xrc⟩, xpr⟩
  have hgm := @gen_cases N W AccW
  refine .cons (fun q hq => ?_) (.cons (fun q hq => ?_) hgen)
  · rcases List.mem_cons.mp hq with rfl | hq
    · simp [Disj, ctrlP, waveP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps]
    · rcases hgm hq with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;>
        (simp only [Disj, prop_wins, row_wins, col_wins, pipe_wins, tile_wins, out_wins]
         simp [ctrlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
          Lhs2.drvWins, DrvWin.overlaps])
  · rcases hgm hq with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;>
      (simp only [Disj, prop_wins, row_wins, col_wins, pipe_wins, tile_wins, out_wins]
       simp [waveP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])


theorem all_cases {N W AccW : Nat} {p : Process2} (hp : p ∈ ctrlP N W :: waveP N :: genPs N W AccW) :
    p = ctrlP N W ∨ p = waveP N ∨ (∃ k, p = propP k) ∨ (∃ r, p = rowP N W r) ∨
      (∃ c, p = colP N W AccW c) ∨ (∃ r c, p = pipeP N W AccW r c) ∨ (∃ r c, p = tileP N W r c) ∨
      (∃ u c, p = outP N AccW u c) := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact .inl rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · exact .inr (.inl rfl)
  exact .inr (.inr (gen_cases hp))

theorem gm_driversOk (N W AccW : Nat) (hN : 1 ≤ N) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (ctrlP N W :: waveP N :: genPs N W AccW) =
      true := by
  apply driversOk_of_ff ?_ ?_ (gm_pairwise N W AccW hN)
  · intro p hp
    rcases all_cases hp with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;>
      exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap]
    rintro n ⟨p, hp, hn⟩
    rcases all_cases hp with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩
    all_goals revert n
    all_goals simp only [Process2.procWrites, prop_wins, row_wins, col_wins, pipe_wins, tile_wins, out_wins]
    all_goals (try simp [ctrlP, waveP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins])
    all_goals (try decide)

/-- **The loaded family is `gmD`**, at every in-range `(N, W, AccW)`. -/
theorem gm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    design.sem N W AccW = gmD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [gm_processes N W AccW hN hW hA hr]; exact gm_driversOk N W AccW hN)
  rw [h1, PDesign.instantiateD2_of_ok (gm_instantiate2 N W AccW hN hW hA hr)]
  simp only [PDesign.assemble2, gm_static N W AccW hN hW hA, gmD]
  simp [design.pdesign]

/-! ## 3. G0's clock step for the loaded family -/

theorem gm_profile (N W AccW : Nat) (hN : 1 ≤ N) : (gmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (gm_pairwise N W AccW hN)⟩
  simp [gmD, genPs, propPs, rowPs, colPs, pipePs, tilePs, outPs, ctrlP, waveP, propP, rowP, colP, pipeP, tileP,
    outP, nb, List.all_append, List.all_flatMap, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, gmDecls]

/-- The eighteen registers. -/
structure Regs where
  dn : LVec
  c : LVec
  bz : LVec
  ip : LVec
  st : LVec
  ar : LVec
  wr : LVec
  ska : LVec
  skd : LVec
  sko : LVec
  wv : LVec
  pb : LVec
  wp : LVec
  ma : LVec
  md : LVec
  mb : LVec
  c1 : LVec
  c2 : LVec

/-- The 23 signals of `gmD`, in declaration order. -/
def GS (ck r s a b : LVec) (g : Regs) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", g.dn), ("C", g.c), ("busy", g.bz),
   ("in_prop", g.ip), ("step", g.st), ("a_rows", g.ar), ("w_rows", g.wr), ("sk_a", g.ska), ("sk_d", g.skd),
   ("sk_o", g.sko), ("wv", g.wv), ("pb", g.pb), ("wp", g.wp), ("m_a", g.ma), ("m_d", g.md), ("m_b", g.mb),
   ("c1", g.c1), ("c2", g.c2)]

theorem apply_gm (N W AccW : Nat) (e : SvState) (ck r s a b : LVec) (g : Regs) :
    applyInputs2 (gmD N W AccW) e (GS ck r s a b g) =
      GS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) g := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [gmD, gmDecls, GS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- PE `(r, c)`'s MAC, evaluated. -/
def macV (N W AccW r c : Nat) (g : Regs) : LVec :=
  (((g.mb.extract ((r * N + c) * AccW) AccW).resizeU (AccW + W)).add
    ((sxv g.ma AccW ((r * N + c) * W) W).mul
      (LVec.ternary (g.wp.extract (r + c) 1) (sxv g.c2 AccW ((r * N + c) * W) W)
        (sxv g.c1 AccW ((r * N + c) * W) W)))).resizeU AccW

def ctrlQ (N W : Nat) (r s a b : LVec) (g : Regs) : NbaQueue2 :=
  if r.condTrue then
    [wr "busy" g.bz ⟨#[.l0]⟩, wr "done" g.dn ⟨#[.l0]⟩, wr "step" g.st (LVec.replicate 32 .l0),
      wr "in_prop" g.ip ⟨#[.l0]⟩]
  else if s.condTrue then
    [wr "busy" g.bz ⟨#[.l1]⟩, wr "done" g.dn ⟨#[.l0]⟩, wr "step" g.st (LVec.replicate 32 .l0),
      wr "in_prop" g.ip g.ip.not, wr "a_rows" g.ar a, wr "w_rows" g.wr b]
  else if g.bz.condTrue then
    wr "step" g.st (g.st.add (LVec.ofInt 32 1)) ::
      ((if (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue then
          [wr "in_prop" g.ip g.ip.not] else []) ++
       ((if (LVec.ofLogic (g.st.lt (LVec.ofInt 32 (N : Int)))).condTrue then
          [wr "w_rows" g.wr (g.wr.shl ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))] else []) ++
       ((if (LVec.ofLogic (g.st.ge (LVec.ofInt 32 (N : Int)))).condTrue then
          [wr "a_rows" g.ar (g.ar.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))] else []) ++
       (if (LVec.ofLogic (g.st.eqLogical (LVec.ofInt 32 ((4 * N : Nat) : Int)))).condTrue then
          [wr "busy" g.bz ⟨#[.l0]⟩, wr "done" g.dn ⟨#[.l1]⟩] else []))))
  else []

def waveQ (N : Nat) (g : Regs) : NbaQueue2 :=
  [wr "wv" g.wv (g.wv.shl (LVec.ofInt 32 1)),
    ("wv", 0, (g.bz.and (LVec.ofLogic (g.st.lt (LVec.ofInt 32 ((2 * N : Nat) : Int))))).resizeU 1),
    wr "pb" g.pb g.ip] ++
  (if (g.wv.extract 0 1).condTrue then [("wp", 0, g.pb.resizeU 1)] else [])

def propQ (g : Regs) (k : Nat) : NbaQueue2 :=
  if (g.wv.extract (k + 1) 1).condTrue then [("wp", k + 1, (g.wp.extract k 1).resizeU 1)] else []

def rowQ (N W : Nat) (g : Regs) (r : Nat) : NbaQueue2 :=
  [("sk_a", tri r * W, ((g.ska.extract (tri r * W) ((r + 1) * W)).shl (LVec.ofInt 32 (W : Int))).resizeU ((r + 1) * W)),
   ("sk_a", tri r * W, (g.ar.extract (r * W) W).resizeU W),
   ("m_a", r * N * W, ((g.ma.extract (r * N * W) (N * W)).shl (LVec.ofInt 32 (W : Int))).resizeU (N * W)),
   ("m_a", r * N * W, (g.ska.extract ((tri r + r) * W) W).resizeU W)]

def colQ (N W AccW : Nat) (g : Regs) (c : Nat) : NbaQueue2 :=
  [("sk_d", tri c * W, ((g.skd.extract (tri c * W) ((c + 1) * W)).shl (LVec.ofInt 32 (W : Int))).resizeU ((c + 1) * W)),
   ("sk_d", tri c * W, (g.wr.extract (((N - 1) * N + c) * W) W).resizeU W)] ++
  ((if (g.wv.extract c 1).condTrue then
      [("m_b", c * AccW, (LVec.replicate AccW .l0).resizeU AccW),
       ("m_d", c * W, (g.skd.extract ((tri c + c) * W) W).resizeU W)] else []) ++
   (("sk_o", tri (N - 1 - c) * AccW,
      ((g.sko.extract (tri (N - 1 - c) * AccW) ((N - c) * AccW)).shl (LVec.ofInt 32 (AccW : Int))).resizeU
        ((N - c) * AccW)) ::
    (if (g.wv.extract (N + c) 1).condTrue then
      [("sk_o", tri (N - 1 - c) * AccW, (macV N W AccW (N - 1) c g).resizeU AccW)] else [])))

def pipeQ (N W AccW : Nat) (g : Regs) (r c : Nat) : NbaQueue2 :=
  if (g.wv.extract (r + c + 1) 1).condTrue then
    [("m_b", ((r + 1) * N + c) * AccW, (macV N W AccW r c g).resizeU AccW),
     ("m_d", ((r + 1) * N + c) * W, (LVec.ternary (g.wp.extract (r + c) 1) (g.c1.extract ((r * N + c) * W) W)
        (g.c2.extract ((r * N + c) * W) W)).resizeU W)]
  else []

def tileQ (N W : Nat) (g : Regs) (r c : Nat) : NbaQueue2 :=
  if (g.wv.extract (r + c + 1) 1).condTrue then
    (if (g.wp.extract (r + c) 1).condTrue then [("c1", (r * N + c) * W, (g.md.extract ((r * N + c) * W) W).resizeU W)]
     else [("c2", (r * N + c) * W, (g.md.extract ((r * N + c) * W) W).resizeU W)])
  else []

def outQ (N AccW : Nat) (g : Regs) (u c : Nat) : NbaQueue2 :=
  if (g.bz.and (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 ((3 * N + 1 : Nat) : Int)).add
      (LVec.ofInt 32 (u : Int)))))).condTrue then
    [("C", (u * N + c) * AccW, (g.sko.extract ((tri (N - 1 - c) + (N - 1 - c)) * AccW) AccW).resizeU AccW)]
  else []

section run
variable (F : Nat) (hF : 50 ≤ F) (ck r s a b : LVec) (g : Regs)
include hF

macro "run_simp" : tactic => `(tactic| simp [ctrlP, waveP, propP, rowP, colP, pipeP, tileP, outP, nb, c32, macE,
  sext, macV, sxv, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal, GS,
  SvState.lookup, evalBinOp, evalUnaryOp, wr, *])

theorem prop_run (k : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (propP k) = .ok (GS ck r s a b g, propQ g k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold propQ
  by_cases h1 : (g.wv.extract (k + 1) 1).condTrue = true <;> run_simp

theorem wave_run (N : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (waveP N) = .ok (GS ck r s a b g, waveQ N g) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold waveQ
  by_cases h1 : (g.wv.extract 0 1).condTrue = true <;> run_simp

theorem row_run (N W rr : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (rowP N W rr) =
    .ok (GS ck r s a b g, rowQ N W g rr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold rowQ
  run_simp

theorem col_run (N W AccW c : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (colP N W AccW c) =
    .ok (GS ck r s a b g, colQ N W AccW g c) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold colQ
  by_cases h1 : (g.wv.extract c 1).condTrue = true <;> by_cases h2 : (g.wv.extract (N + c) 1).condTrue = true <;>
    run_simp

theorem pipe_run (N W AccW rr c : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (pipeP N W AccW rr c) =
    .ok (GS ck r s a b g, pipeQ N W AccW g rr c) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold pipeQ
  by_cases h1 : (g.wv.extract (rr + c + 1) 1).condTrue = true <;> run_simp

theorem tile_run (N W rr c : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (tileP N W rr c) =
    .ok (GS ck r s a b g, tileQ N W g rr c) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold tileQ
  by_cases h1 : (g.wv.extract (rr + c + 1) 1).condTrue = true <;>
    by_cases h2 : (g.wp.extract (rr + c) 1).condTrue = true <;> run_simp

theorem out_run (N AccW u c : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (outP N AccW u c) =
    .ok (GS ck r s a b g, outQ N AccW g u c) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold outQ
  by_cases h1 : (g.bz.and (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 (3 * (N : Int) + 1)).add
      (LVec.ofInt 32 (u : Int)))))).condTrue = true <;> run_simp

theorem ctrl_run (N W : Nat) : runEdgeProcess2 F (GS ck r s a b g) [] (ctrlP N W) =
    .ok (GS ck r s a b g, ctrlQ N W r s a b g) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 50 := ⟨F - 50, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true
  · run_simp
  by_cases h2 : s.condTrue = true
  · run_simp
  by_cases h3 : g.bz.condTrue = true
  · by_cases h4 : (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    by_cases h5 : (LVec.ofLogic (g.st.lt (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    by_cases h6 : (LVec.ofLogic (g.st.ge (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    by_cases h7 : (LVec.ofLogic (g.st.eqLogical (LVec.ofInt 32 (4 * (N : Int))))).condTrue = true <;>
    run_simp
  · run_simp

end run

/-- The cycle's updates, in process order. -/
def gmQ (N W AccW : Nat) (r s a b : LVec) (g : Regs) : NbaQueue2 :=
  ctrlQ N W r s a b g ++ (waveQ N g ++ ((List.range (2 * N - 2)).flatMap (propQ g) ++
    ((List.range N).flatMap (rowQ N W g) ++ ((List.range N).flatMap (colQ N W AccW g) ++
    (((List.range (N - 1)).flatMap fun r => (List.range N).flatMap (pipeQ N W AccW g r)) ++
    (((List.range N).flatMap fun r => (List.range N).flatMap (tileQ N W g r)) ++
    ((List.range N).flatMap fun u => (List.range N).flatMap (outQ N AccW g u))))))))

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def gmNext (N W AccW : Nat) (ck r s a b : LVec) (g : Regs) : SvState :=
  commitNba2 (GS ck r s a b g) (gmQ N W AccW r s a b g)

/-- **One cycle of the loaded design is G0's clock step**, evaluated. -/
theorem gm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31)
    (σ : ScheduleOracle) (e : SvState) (ck r s a b : LVec) (g : Regs) (kk F : Nat) (hF : 50 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (GS ck r s a b g) kk =
      .ok (gmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) g, kk + 3) := by
  have hedge : ∀ p ∈ (gmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ ctrlP N W :: waveP N :: genPs N W AccW := by simpa [gmD] using hp
    rcases all_cases hm with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;> rfl
  rw [gm_sem_eq N W AccW hN hW hA hr, cycleStep2_profile (gm_profile N W AccW hN) σ e _ kk ?_ ?_ (by omega),
    apply_gm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [gmD, List.toList_toArray, List.flatMap_cons, ctrl_run F hF, wave_run F hF, genPs, List.flatMap_append,
      propPs, rowPs, colPs, pipePs, tilePs, outPs, List.flatMap_map, List.flatMap_assoc, prop_run F hF, row_run F hF,
      col_run F hF, pipe_run F hF, tile_run F hF, out_run F hF, gmNext, gmQ]
  · intro i p hp
    rw [apply_gm]
    have hm : p ∈ ctrlP N W :: waveP N :: genPs N W AccW :=
      List.mem_of_getElem? (by simpa [gmD] using hp : (ctrlP N W :: waveP N :: genPs N W AccW)[i]? = some p)
    rcases all_cases hm with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨rr, c, rfl⟩ | ⟨rr, c, rfl⟩ | ⟨rr, c, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ N W⟩
    · exact ⟨_, wave_run F hF _ _ _ _ _ _ N⟩
    · exact ⟨_, prop_run F hF _ _ _ _ _ _ k⟩
    · exact ⟨_, row_run F hF _ _ _ _ _ _ N W k⟩
    · exact ⟨_, col_run F hF _ _ _ _ _ _ N W AccW k⟩
    · exact ⟨_, pipe_run F hF _ _ _ _ _ _ N W AccW rr c⟩
    · exact ⟨_, tile_run F hF _ _ _ _ _ _ N W rr c⟩
    · exact ⟨_, out_run F hF _ _ _ _ _ _ N AccW rr c⟩
  · rw [apply_gm]; simp [GS]

/-! ## 4. The commit, register by register -/

theorem lookup_none_not_mem : ∀ {st : SvState} {n : String}, SvState.lookup st n = none → n ∉ st.map Prod.fst
  | [], _, _ => by simp
  | (k, v) :: rest, n, h => by
    simp only [SvState.lookup] at h
    by_cases hk : k = n
    · subst hk; simp at h
    · have : (k == n) = false := by simp [hk]
      rw [this] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have := lookup_none_not_mem h
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h' => hk h'.symm, this⟩

theorem map_ite_eq_self {n : String} (f : LVec → LVec) :
    ∀ (rest : SvState), n ∉ rest.map Prod.fst →
      (rest.map fun p => (p.1, if n = p.1 then f p.2 else p.2)) = rest
  | [], _ => rfl
  | (k, v) :: rest, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.map_cons, if_neg h.1, map_ite_eq_self f rest h.2]

theorem nbaStep_eq_map : ∀ (st : SvState) (u : String × Nat × LVec), (st.map Prod.fst).Nodup →
    nbaStep st u = st.map fun p => (p.1, if u.1 = p.1 then p.2.insertAt u.2.1 u.2.2 else p.2)
  | [], u, _ => by simp [nbaStep, SvState.lookup]
  | (k, v) :: rest, u, hnd => by
    have hk : k ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    have hr : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    by_cases h : k = u.1
    · subst h
      have hrest := map_ite_eq_self (n := u.1) (fun x => x.insertAt u.2.1 u.2.2) rest hk
      simp [nbaStep, SvState.lookup, SvState.set, hrest]
    · have ih := nbaStep_eq_map rest u hr
      have hb : (k == u.1) = false := by simp [h]
      have h' : ¬ u.1 = k := fun e => h e.symm
      unfold nbaStep at ih ⊢
      simp only [SvState.lookup, hb, Bool.false_eq_true, ↓reduceIte]
      cases hl : SvState.lookup rest u.1 with
      | none =>
        simp only [hl] at ih
        simp only [List.map_cons, if_neg h']
        exact congrArg _ ih
      | some old =>
        simp only [hl] at ih
        simp only [SvState.set, hb, Bool.false_eq_true, ↓reduceIte, List.map_cons, if_neg h']
        exact congrArg _ ih

theorem commit_eq_map : ∀ (q : NbaQueue2) (st : SvState), (st.map Prod.fst).Nodup →
    commitNba2 st q = st.map fun p => (p.1, nbaFold p.1 q p.2)
  | [], st, _ => by
    simp only [commitNba2_nil]
    conv => lhs; rw [← List.map_id st]
    rfl
  | u :: q, st, hnd => by
    have hk : ((st.map fun p => (p.1, if u.1 = p.1 then p.2.insertAt u.2.1 u.2.2 else p.2)).map Prod.fst) =
        st.map Prod.fst := by simp [List.map_map, Function.comp_def]
    rw [commitNba2_cons, nbaStep_eq_map st u hnd, commit_eq_map q _ (by rw [hk]; exact hnd), List.map_map]
    rfl

/-- The registers after a commit. -/
def Regs.fold (q : NbaQueue2) (g : Regs) : Regs :=
  ⟨nbaFold "done" q g.dn, nbaFold "C" q g.c, nbaFold "busy" q g.bz, nbaFold "in_prop" q g.ip,
    nbaFold "step" q g.st, nbaFold "a_rows" q g.ar, nbaFold "w_rows" q g.wr, nbaFold "sk_a" q g.ska,
    nbaFold "sk_d" q g.skd, nbaFold "sk_o" q g.sko, nbaFold "wv" q g.wv, nbaFold "pb" q g.pb, nbaFold "wp" q g.wp,
    nbaFold "m_a" q g.ma, nbaFold "m_d" q g.md, nbaFold "m_b" q g.mb, nbaFold "c1" q g.c1, nbaFold "c2" q g.c2⟩

theorem commit_GS (q : NbaQueue2) (ck r s a b : LVec) (g : Regs) :
    commitNba2 (GS ck r s a b g) q =
      GS (nbaFold "clk" q ck) (nbaFold "rst" q r) (nbaFold "start" q s) (nbaFold "A" q a) (nbaFold "B" q b)
        (g.fold q) := by
  rw [commit_eq_map q _ (by simp only [GS, List.map]; decide)]
  rfl

/-! ## 5. Windows of a committed register -/

theorem extract_insertAt_cover {v p : LVec} {lo a w : Nat} (h1 : lo ≤ a) (h2 : a + w ≤ lo + p.width)
    (h3 : a + w ≤ v.width) : (v.insertAt lo p).extract a w = p.extract (a - lo) w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, LVec.getD_extract, if_pos hi, if_pos hi, LVec.getD_insertAt, if_pos ⟨by omega, by omega⟩,
    if_pos (by omega)]
  congr 2; omega

theorem extract_resizeU {p : LVec} {n a w : Nat} (h1 : a + w ≤ n) (h2 : a + w ≤ p.width) :
    (p.resizeU n).extract a w = p.extract a w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, LVec.getD_extract, if_pos hi, if_pos hi]
  have hp : a + i < p.bits.size := by simp [LVec.width] at h2; omega
  simp [LVec.resizeU, Array.getElem?_ofFn, show a + i < n by omega, Array.getElem?_eq_getElem hp]

theorem toNat?_ofInt32 {v : Nat} (h : v < 2 ^ 32) : (LVec.ofInt 32 (v : Int)).toNat? = some v := by
  rw [LVec.ofInt_eq_ofBitVec, LVec.toNat?_ofBitVec, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem extract_shl {p : LVec} {K a w : Nat} (hK : K < 2 ^ 32) (h1 : K ≤ a) (h2 : a + w ≤ p.width) :
    (p.shl (LVec.ofInt 32 (K : Int))).extract a w = p.extract (a - K) w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, LVec.getD_extract, if_pos hi, if_pos hi]
  have hp : a - K + i < p.bits.size := by simp [LVec.width] at h2; omega
  have hq : a + i < p.bits.size := by simp [LVec.width] at h2; omega
  simp [LVec.shl, LVec.shiftAmount?, toNat?_ofInt32 hK, Array.getElem?_ofFn, LVec.width, hq,
    show ¬ a + i < K by omega, show a + i - K = a - K + i by omega, Array.getElem?_eq_getElem hp]

theorem extract_zero_self {p : LVec} {w : Nat} (h : p.width = w) : p.extract 0 w = p := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, Nat.zero_add]

/-- Writes to `n` disjoint from the window `[a, a + w)` leave it. -/
theorem extract_nbaFold_disj {n : String} {a w : Nat} : ∀ (q : NbaQueue2) (x : LVec),
    (∀ u ∈ q, u.1 = n → u.2.1 + u.2.2.width ≤ a ∨ a + w ≤ u.2.1) →
    (nbaFold n q x).extract a w = x.extract a w
  | [], _, _ => rfl
  | u :: q, x, h => by
    simp only [nbaFold, List.foldl_cons]
    rw [← nbaFold, extract_nbaFold_disj q _ fun u' hu' => h u' (List.mem_cons_of_mem _ hu')]
    split
    · rename_i hn
      exact LVec.extract_insertAt_of_disjoint ((h u List.mem_cons_self hn).symm)
    · rfl

/-- The window after a queue depends only on the window before it (equal widths). -/
theorem extract_nbaFold_congr {n : String} {a w : Nat} : ∀ (q : NbaQueue2) (x y : LVec), x.width = y.width →
    x.extract a w = y.extract a w → (nbaFold n q x).extract a w = (nbaFold n q y).extract a w
  | [], _, _, _, h => h
  | u :: q, x, y, hw, h => by
    simp only [nbaFold, List.foldl_cons]
    rw [← nbaFold, ← nbaFold]
    split
    · refine extract_nbaFold_congr q _ _ (by simp [hw]) ?_
      apply LVec.ext_getD (by simp)
      intro i hi
      simp only [LVec.width_extract] at hi
      have hb := congrArg (fun z : LVec => z.bits[i]?.getD .lx) h
      simp only [LVec.getD_extract, if_pos hi] at hb
      rw [LVec.getD_extract, LVec.getD_extract, if_pos hi, if_pos hi, LVec.getD_insertAt, LVec.getD_insertAt, hb, hw]
    · exact extract_nbaFold_congr q _ _ hw h

/-- **A family's writes to one window**: only member `k0` touches `[a, a + w)`. -/
theorem extract_fold_family {n : String} {a w : Nat} (f : Nat → NbaQueue2) (k0 : Nat) :
    ∀ (l : List Nat), l.Nodup → (∀ k ∈ l, k ≠ k0 → ∀ u ∈ f k, u.1 = n → u.2.1 + u.2.2.width ≤ a ∨ a + w ≤ u.2.1) →
    ∀ x : LVec, (nbaFold n (l.flatMap f) x).extract a w =
      if k0 ∈ l then (nbaFold n (f k0) x).extract a w else x.extract a w
  | [], _, _, x => by simp [nbaFold]
  | k :: l, hnd, h, x => by
    have hk : k ∉ l := (List.nodup_cons.mp hnd).1
    have hl : l.Nodup := (List.nodup_cons.mp hnd).2
    have ih := extract_fold_family f k0 l hl (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))
    rw [List.flatMap_cons, nbaFold_append, ih]
    by_cases hkk : k = k0
    · subst hkk
      simp [hk]
    · have hd := extract_nbaFold_disj (n := n) (a := a) (w := w) (f k) x (h k List.mem_cons_self hkk)
      by_cases hm : k0 ∈ l
      · simp only [hm, ↓reduceIte, List.mem_cons, or_true]
        exact extract_nbaFold_congr _ _ _ (by simp) hd
      · simp only [hm, ↓reduceIte, List.mem_cons, Ne.symm hkk, or_false]
        exact hd


/-! ### Which queues write which registers -/

theorem nbaFold_of_names {n : String} {ns : List String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ∈ ns) → n ∉ ns →
    ∀ x : LVec, nbaFold n q x = x
  | [], _, _, _ => rfl
  | u :: q, hq, hn, x => by
    have h1 : u.1 ≠ n := fun h => hn (h ▸ hq u List.mem_cons_self)
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_names (fun u' hu' => hq u' (List.mem_cons_of_mem _ hu')) hn x

theorem names_flatMap {ns : List String} {f : Nat → NbaQueue2} (h : ∀ k, ∀ u ∈ f k, u.1 ∈ ns) (l : List Nat) :
    ∀ u ∈ l.flatMap f, u.1 ∈ ns := by
  intro u hu
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hu
  exact h k u hk

macro "names_tac" : tactic => `(tactic| (intro u hu; (repeat' split at hu) <;> simp at hu <;>
  (repeat' rcases hu with rfl | hu) <;> simp_all))

section names
variable (N W AccW : Nat) (r s a b : LVec) (g : Regs)
theorem ctrlQ_names : ∀ u ∈ ctrlQ N W r s a b g, u.1 ∈ ["busy", "done", "step", "in_prop", "a_rows", "w_rows"] := by
  unfold ctrlQ; names_tac
theorem waveQ_names : ∀ u ∈ waveQ N g, u.1 ∈ ["wv", "pb", "wp"] := by unfold waveQ; names_tac
theorem propQ_names (k : Nat) : ∀ u ∈ propQ g k, u.1 ∈ ["wp"] := by unfold propQ; names_tac
theorem rowQ_names (k : Nat) : ∀ u ∈ rowQ N W g k, u.1 ∈ ["sk_a", "m_a"] := by unfold rowQ; names_tac
theorem colQ_names (k : Nat) : ∀ u ∈ colQ N W AccW g k, u.1 ∈ ["sk_d", "m_b", "m_d", "sk_o"] := by
  unfold colQ; names_tac
theorem pipeQ_names (k j : Nat) : ∀ u ∈ pipeQ N W AccW g k j, u.1 ∈ ["m_b", "m_d"] := by unfold pipeQ; names_tac
theorem tileQ_names (k j : Nat) : ∀ u ∈ tileQ N W g k j, u.1 ∈ ["c1", "c2"] := by unfold tileQ; names_tac
theorem outQ_names (k j : Nat) : ∀ u ∈ outQ N AccW g k j, u.1 ∈ ["C"] := by unfold outQ; names_tac

abbrev Props := (List.range (2 * N - 2)).flatMap (propQ g)
abbrev Rows := (List.range N).flatMap (rowQ N W g)
abbrev Cols := (List.range N).flatMap (colQ N W AccW g)
abbrev Pipes := (List.range (N - 1)).flatMap fun k => (List.range N).flatMap (pipeQ N W AccW g k)
abbrev Tiles := (List.range N).flatMap fun k => (List.range N).flatMap (tileQ N W g k)
abbrev Outs := (List.range N).flatMap fun k => (List.range N).flatMap (outQ N AccW g k)

theorem props_names : ∀ u ∈ Props N g, u.1 ∈ ["wp"] := names_flatMap (propQ_names g) _
theorem rows_names : ∀ u ∈ Rows N W g, u.1 ∈ ["sk_a", "m_a"] := names_flatMap (rowQ_names N W g) _
theorem cols_names : ∀ u ∈ Cols N W AccW g, u.1 ∈ ["sk_d", "m_b", "m_d", "sk_o"] := names_flatMap (colQ_names N W AccW g) _
theorem pipes_names : ∀ u ∈ Pipes N W AccW g, u.1 ∈ ["m_b", "m_d"] :=
  names_flatMap (fun k => names_flatMap (pipeQ_names N W AccW g k) _) _
theorem tiles_names : ∀ u ∈ Tiles N W g, u.1 ∈ ["c1", "c2"] :=
  names_flatMap (fun k => names_flatMap (tileQ_names N W g k) _) _
theorem outs_names : ∀ u ∈ Outs N AccW g, u.1 ∈ ["C"] :=
  names_flatMap (fun k => names_flatMap (outQ_names N AccW g k) _) _

theorem gmQ_split (n : String) (x : LVec) : nbaFold n (gmQ N W AccW r s a b g) x =
    nbaFold n (Outs N AccW g) (nbaFold n (Tiles N W g) (nbaFold n (Pipes N W AccW g) (nbaFold n (Cols N W AccW g)
      (nbaFold n (Rows N W g) (nbaFold n (Props N g) (nbaFold n (waveQ N g) (nbaFold n (ctrlQ N W r s a b g) x))))))) := by
  simp only [gmQ, nbaFold_append]

theorem skipOuts {n : String} (hn : n ∉ ["C"]) (x : LVec) : nbaFold n (Outs N AccW g) x = x :=
  nbaFold_of_names (outs_names N AccW g) hn x
theorem skipTiles {n : String} (hn : n ∉ ["c1", "c2"]) (x : LVec) : nbaFold n (Tiles N W g) x = x :=
  nbaFold_of_names (tiles_names N W g) hn x
theorem skipPipes {n : String} (hn : n ∉ ["m_b", "m_d"]) (x : LVec) : nbaFold n (Pipes N W AccW g) x = x :=
  nbaFold_of_names (pipes_names N W AccW g) hn x
theorem skipCols {n : String} (hn : n ∉ ["sk_d", "m_b", "m_d", "sk_o"]) (x : LVec) : nbaFold n (Cols N W AccW g) x = x :=
  nbaFold_of_names (cols_names N W AccW g) hn x
theorem skipRows {n : String} (hn : n ∉ ["sk_a", "m_a"]) (x : LVec) : nbaFold n (Rows N W g) x = x :=
  nbaFold_of_names (rows_names N W g) hn x
theorem skipProps {n : String} (hn : n ∉ ["wp"]) (x : LVec) : nbaFold n (Props N g) x = x :=
  nbaFold_of_names (props_names N g) hn x
theorem skipWave {n : String} (hn : n ∉ ["wv", "pb", "wp"]) (x : LVec) : nbaFold n (waveQ N g) x = x :=
  nbaFold_of_names (waveQ_names N g) hn x
theorem skipCtrl {n : String} (hn : n ∉ ["busy", "done", "step", "in_prop", "a_rows", "w_rows"]) (x : LVec) : nbaFold n (ctrlQ N W r s a b g) x = x :=
  nbaFold_of_names (ctrlQ_names N W r s a b g) hn x
theorem fold_wv (x : LVec) : nbaFold "wv" (gmQ N W AccW r s a b g) x =
    nbaFold "wv" (waveQ N g) x := by
  simp only [gmQ_split, skipOuts (n := "wv") (hn := by decide), skipTiles (n := "wv") (hn := by decide), skipPipes (n := "wv") (hn := by decide), skipCols (n := "wv") (hn := by decide), skipRows (n := "wv") (hn := by decide), skipProps (n := "wv") (hn := by decide), skipCtrl (n := "wv") (hn := by decide)]
theorem fold_pb (x : LVec) : nbaFold "pb" (gmQ N W AccW r s a b g) x =
    nbaFold "pb" (waveQ N g) x := by
  simp only [gmQ_split, skipOuts (n := "pb") (hn := by decide), skipTiles (n := "pb") (hn := by decide), skipPipes (n := "pb") (hn := by decide), skipCols (n := "pb") (hn := by decide), skipRows (n := "pb") (hn := by decide), skipProps (n := "pb") (hn := by decide), skipCtrl (n := "pb") (hn := by decide)]
theorem fold_wp (x : LVec) : nbaFold "wp" (gmQ N W AccW r s a b g) x =
    nbaFold "wp" (Props N g) (nbaFold "wp" (waveQ N g) x) := by
  simp only [gmQ_split, skipOuts (n := "wp") (hn := by decide), skipTiles (n := "wp") (hn := by decide), skipPipes (n := "wp") (hn := by decide), skipCols (n := "wp") (hn := by decide), skipRows (n := "wp") (hn := by decide), skipCtrl (n := "wp") (hn := by decide)]
theorem fold_ska (x : LVec) : nbaFold "sk_a" (gmQ N W AccW r s a b g) x =
    nbaFold "sk_a" (Rows N W g) x := by
  simp only [gmQ_split, skipOuts (n := "sk_a") (hn := by decide), skipTiles (n := "sk_a") (hn := by decide), skipPipes (n := "sk_a") (hn := by decide), skipCols (n := "sk_a") (hn := by decide), skipProps (n := "sk_a") (hn := by decide), skipWave (n := "sk_a") (hn := by decide), skipCtrl (n := "sk_a") (hn := by decide)]
theorem fold_ma (x : LVec) : nbaFold "m_a" (gmQ N W AccW r s a b g) x =
    nbaFold "m_a" (Rows N W g) x := by
  simp only [gmQ_split, skipOuts (n := "m_a") (hn := by decide), skipTiles (n := "m_a") (hn := by decide), skipPipes (n := "m_a") (hn := by decide), skipCols (n := "m_a") (hn := by decide), skipProps (n := "m_a") (hn := by decide), skipWave (n := "m_a") (hn := by decide), skipCtrl (n := "m_a") (hn := by decide)]
theorem fold_skd (x : LVec) : nbaFold "sk_d" (gmQ N W AccW r s a b g) x =
    nbaFold "sk_d" (Cols N W AccW g) x := by
  simp only [gmQ_split, skipOuts (n := "sk_d") (hn := by decide), skipTiles (n := "sk_d") (hn := by decide), skipPipes (n := "sk_d") (hn := by decide), skipRows (n := "sk_d") (hn := by decide), skipProps (n := "sk_d") (hn := by decide), skipWave (n := "sk_d") (hn := by decide), skipCtrl (n := "sk_d") (hn := by decide)]
theorem fold_sko (x : LVec) : nbaFold "sk_o" (gmQ N W AccW r s a b g) x =
    nbaFold "sk_o" (Cols N W AccW g) x := by
  simp only [gmQ_split, skipOuts (n := "sk_o") (hn := by decide), skipTiles (n := "sk_o") (hn := by decide), skipPipes (n := "sk_o") (hn := by decide), skipRows (n := "sk_o") (hn := by decide), skipProps (n := "sk_o") (hn := by decide), skipWave (n := "sk_o") (hn := by decide), skipCtrl (n := "sk_o") (hn := by decide)]
theorem fold_mb (x : LVec) : nbaFold "m_b" (gmQ N W AccW r s a b g) x =
    nbaFold "m_b" (Pipes N W AccW g) (nbaFold "m_b" (Cols N W AccW g) x) := by
  simp only [gmQ_split, skipOuts (n := "m_b") (hn := by decide), skipTiles (n := "m_b") (hn := by decide), skipRows (n := "m_b") (hn := by decide), skipProps (n := "m_b") (hn := by decide), skipWave (n := "m_b") (hn := by decide), skipCtrl (n := "m_b") (hn := by decide)]
theorem fold_md (x : LVec) : nbaFold "m_d" (gmQ N W AccW r s a b g) x =
    nbaFold "m_d" (Pipes N W AccW g) (nbaFold "m_d" (Cols N W AccW g) x) := by
  simp only [gmQ_split, skipOuts (n := "m_d") (hn := by decide), skipTiles (n := "m_d") (hn := by decide), skipRows (n := "m_d") (hn := by decide), skipProps (n := "m_d") (hn := by decide), skipWave (n := "m_d") (hn := by decide), skipCtrl (n := "m_d") (hn := by decide)]
theorem fold_c1 (x : LVec) : nbaFold "c1" (gmQ N W AccW r s a b g) x =
    nbaFold "c1" (Tiles N W g) x := by
  simp only [gmQ_split, skipOuts (n := "c1") (hn := by decide), skipPipes (n := "c1") (hn := by decide), skipCols (n := "c1") (hn := by decide), skipRows (n := "c1") (hn := by decide), skipProps (n := "c1") (hn := by decide), skipWave (n := "c1") (hn := by decide), skipCtrl (n := "c1") (hn := by decide)]
theorem fold_C (x : LVec) : nbaFold "C" (gmQ N W AccW r s a b g) x =
    nbaFold "C" (Outs N AccW g) x := by
  simp only [gmQ_split, skipTiles (n := "C") (hn := by decide), skipPipes (n := "C") (hn := by decide), skipCols (n := "C") (hn := by decide), skipRows (n := "C") (hn := by decide), skipProps (n := "C") (hn := by decide), skipWave (n := "C") (hn := by decide), skipCtrl (n := "C") (hn := by decide)]
theorem fold_ctrl {n : String} (h1 : n ∉ ["C"]) (h2 : n ∉ ["c1", "c2"]) (h3 : n ∉ ["m_b", "m_d"])
    (h4 : n ∉ ["sk_d", "m_b", "m_d", "sk_o"]) (h5 : n ∉ ["sk_a", "m_a"]) (h6 : n ∉ ["wp"]) (h7 : n ∉ ["wv", "pb", "wp"])
    (x : LVec) : nbaFold n (gmQ N W AccW r s a b g) x = nbaFold n (ctrlQ N W r s a b g) x := by
  simp only [gmQ_split, skipOuts (hn := h1), skipTiles (hn := h2), skipPipes (hn := h3), skipCols (hn := h4),
    skipRows (hn := h5), skipProps (hn := h6), skipWave (hn := h7)]
end names

set_option hygiene false in
macro "region_tac" : tactic => `(tactic| ((repeat' split at hu) <;>
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hu <;>
  (repeat' rcases hu with rfl | hu) <;> (try simp only [LVec.width_resizeU, LVec.width_ofBitVec] at hn ⊢) <;>
  first | omega | exact absurd hn (by decide) | simp at hn))

/-! ### Lanes and windows -/

theorem width_shl (p k : LVec) : (p.shl k).width = p.width := by
  unfold LVec.shl
  split <;> simp [LVec.width, LVec.xVec, LVec.replicate]

theorem resizeU_self {p : LVec} {w : Nat} (h : p.width = w) : p.resizeU w = p := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_resizeU] at hi
  have hp : i < p.bits.size := by simp [LVec.width] at h; omega
  simp [LVec.resizeU, Array.getElem?_ofFn, hi, Array.getElem?_eq_getElem hp]

/-- Entry `m ≥ 1` of a lane after its shift: the old entry `m - 1`. -/
theorem lane_succ {x : LVec} {L0 E len m : Nat} (hE : E < 2 ^ 32) (hm1 : 1 ≤ m) (hlen : m * E + E ≤ len)
    (hx : L0 + len ≤ x.width) :
    (x.insertAt L0 (((x.extract L0 len).shl (LVec.ofInt 32 (E : Int))).resizeU len)).extract (L0 + m * E) E =
      x.extract (L0 + (m * E - E)) E := by
  have h1 : E ≤ m * E := Nat.le_mul_of_pos_left E (by omega)
  rw [extract_insertAt_cover (by omega) (by simp; omega) (by omega), show L0 + m * E - L0 = m * E by omega,
    extract_resizeU (by omega) (by simp [width_shl]; omega), extract_shl hE h1 (by simp; omega),
    LVec.extract_extract _ (by omega)]

/-- Entry `0` of a lane after its head write. -/
theorem lane_zero {y src : LVec} {L0 E : Nat} (hs : src.width = E) (hy : L0 + E ≤ y.width) :
    (y.insertAt L0 (src.resizeU E)).extract L0 E = src := by
  rw [LVec.extract_insertAt_self (by simp) hy, resizeU_self hs]

theorem lane_zero' {y src : LVec} {L0 E a : Nat} (ha : a = L0) (hs : src.width = E) (hy : L0 + E ≤ y.width) :
    (y.insertAt L0 (src.resizeU E)).extract a E = src := by
  subst ha; exact lane_zero hs hy

/-- A write that ends before the window, or starts after it. -/
theorem skip_win {y p : LVec} {lo a w : Nat} (h : lo + p.width ≤ a ∨ a + w ≤ lo) :
    (y.insertAt lo p).extract a w = y.extract a w :=
  LVec.extract_insertAt_of_disjoint (Or.symm h)


theorem nbaFold_cons_self (n : String) (lo : Nat) (v : LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold n ((n, lo, v) :: q) x = nbaFold n q (x.insertAt lo v) := by
  simp [nbaFold]
theorem nbaFold_cons_ne {n m : String} (h : m ≠ n) (lo : Nat) (v : LVec) (q : NbaQueue2) (x : LVec) :
    nbaFold n ((m, lo, v) :: q) x = nbaFold n q x := by
  simp [nbaFold, h]
theorem nbaFold_nil' (n : String) (x : LVec) : nbaFold n [] x = x := rfl
theorem nbaFold_cons_app (n : String) (u : String × Nat × LVec) (q q' : NbaQueue2) (x : LVec) :
    nbaFold n ((u :: q) ++ q') x = nbaFold n (u :: (q ++ q')) x := rfl

/-! ### The registers through a cycle, window by window -/

/-- The widths of the registers. -/
structure Wd (N W AccW : Nat) (g : Regs) : Prop where
  dn : g.dn.width = 1
  c : g.c.width = N * N * AccW
  bz : g.bz.width = 1
  ip : g.ip.width = 1
  st : g.st.width = 32
  ar : g.ar.width = N * N * W
  wr : g.wr.width = N * N * W
  ska : g.ska.width = tri N * W
  skd : g.skd.width = tri N * W
  sko : g.sko.width = tri N * AccW
  wv : g.wv.width = 2 * N
  pb : g.pb.width = 1
  wp : g.wp.width = 2 * N - 1
  ma : g.ma.width = N * N * W
  md : g.md.width = N * N * W
  mb : g.mb.width = N * N * AccW
  c1 : g.c1.width = N * N * W
  c2 : g.c2.width = N * N * W

theorem Wd.fold {N W AccW : Nat} {g : Regs} (h : Wd N W AccW g) (q : NbaQueue2) : Wd N W AccW (g.fold q) :=
  ⟨by simp [Regs.fold, h.dn], by simp [Regs.fold, h.c], by simp [Regs.fold, h.bz], by simp [Regs.fold, h.ip],
    by simp [Regs.fold, h.st], by simp [Regs.fold, h.ar], by simp [Regs.fold, h.wr], by simp [Regs.fold, h.ska],
    by simp [Regs.fold, h.skd], by simp [Regs.fold, h.sko], by simp [Regs.fold, h.wv], by simp [Regs.fold, h.pb],
    by simp [Regs.fold, h.wp], by simp [Regs.fold, h.ma], by simp [Regs.fold, h.md], by simp [Regs.fold, h.mb],
    by simp [Regs.fold, h.c1], by simp [Regs.fold, h.c2]⟩

section nexts
variable {N W AccW : Nat} {g : Regs}

theorem ska_next (hwd : Wd N W AccW g) (hW : W < 2 ^ 32) {r m : Nat} (hr : r < N) (hm : m ≤ r) :
    (nbaFold "sk_a" (Rows N W g) g.ska).extract ((tri r + m) * W) W =
      if m = 0 then g.ar.extract (r * W) W else g.ska.extract ((tri r + (m - 1)) * W) W := by
  have hw := hwd.ska
  have htl := tri_le hr
  have hL : tri r * W + (r + 1) * W ≤ g.ska.width := by
    rw [hw, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hmW : m * W + W ≤ (r + 1) * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  rw [extract_fold_family (rowQ N W g) r (List.range N) List.nodup_range ?_ g.ska, if_pos (List.mem_range.mpr hr)]
  · simp only [rowQ, nbaFold_cons_self, nbaFold_cons_ne (show "m_a" ≠ "sk_a" by decide), nbaFold_nil']
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos rfl, lane_zero' (by simp) (by simp) (by simp; omega)]
    · have hWm : W ≤ m * W := Nat.le_mul_of_pos_left W (show 0 < m by omega)
      rw [if_neg hm0, Nat.add_mul (tri _) m W, skip_win (Or.inl (by simp only [LVec.width_resizeU]; omega)),
        lane_succ hW (by omega) hmW (by omega), Nat.add_mul (tri _) (m - 1), Nat.sub_mul, Nat.one_mul]
  · intro k hk hkr u hu hn
    have hk' := List.mem_range.mp hk
    simp only [rowQ, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases Nat.lt_or_gt_of_ne hkr with hlt | hgt
    · have h1 : tri k * W + (k + 1) * W ≤ tri r * W := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono hlt; omega)
      have h2 : W ≤ (k + 1) * W := Nat.le_mul_of_pos_left W (by omega)
      have h3 : tri r * W ≤ (tri r + m) * W := Nat.mul_le_mul_right _ (by omega)
      rcases hu with rfl | rfl | rfl | rfl <;> simp only [LVec.width_resizeU] at hn ⊢ <;>
        first | omega | exact absurd hn (by decide)
    · have h1 : (tri r + m) * W + W ≤ tri k * W := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono hgt; omega)
      rcases hu with rfl | rfl | rfl | rfl <;> simp only [LVec.width_resizeU] at hn ⊢ <;>
        first | omega | exact absurd hn (by decide)

theorem ma_next (hwd : Wd N W AccW g) (hW : W < 2 ^ 32) {r c : Nat} (hr : r < N) (hc : c < N) :
    (nbaFold "m_a" (Rows N W g) g.ma).extract ((r * N + c) * W) W =
      if c = 0 then g.ska.extract ((tri r + r) * W) W else g.ma.extract ((r * N + (c - 1)) * W) W := by
  have hw := hwd.ma
  have hL : r * N * W + N * W ≤ g.ma.width := by
    rw [hw, Nat.mul_assoc r, Nat.mul_assoc N N W, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
  have hcW : c * W + W ≤ N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have e1 : (r * N + c) * W = r * N * W + c * W := Nat.add_mul _ _ _
  rw [extract_fold_family (rowQ N W g) r (List.range N) List.nodup_range ?_ g.ma, if_pos (List.mem_range.mpr hr)]
  · simp only [rowQ, nbaFold_cons_self, nbaFold_cons_ne (show "sk_a" ≠ "m_a" by decide), nbaFold_nil']
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl, lane_zero' (by simp) (by simp) (by simp; omega)]
    · have hWc : W ≤ c * W := Nat.le_mul_of_pos_left W (show 0 < c by omega)
      rw [if_neg hc0, e1, skip_win (Or.inl (by simp only [LVec.width_resizeU]; omega)),
        lane_succ hW (by omega) hcW (by omega), Nat.add_mul (r * N) (c - 1), Nat.sub_mul, Nat.one_mul]
  · intro k hk hkr u hu hn
    have hk' := List.mem_range.mp hk
    simp only [rowQ, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases Nat.lt_or_gt_of_ne hkr with hlt | hgt
    · have h1 : k * N * W + N * W ≤ r * N * W := by
        rw [Nat.mul_assoc k, Nat.mul_assoc r, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      have h2 : W ≤ N * W := Nat.le_mul_of_pos_left W (by omega)
      rcases hu with rfl | rfl | rfl | rfl <;> simp only [LVec.width_resizeU] at hn ⊢ <;>
        first | omega | exact absurd hn (by decide)
    · have h1 : r * N * W + N * W ≤ k * N * W := by
        rw [Nat.mul_assoc k, Nat.mul_assoc r, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hgt
      rcases hu with rfl | rfl | rfl | rfl <;> simp only [LVec.width_resizeU] at hn ⊢ <;>
        first | omega | exact absurd hn (by decide)

theorem nbaFold_ite (n : String) (c : Prop) [Decidable c] (l1 l2 : NbaQueue2) (x : LVec) :
    nbaFold n (if c then l1 else l2) x = if c then nbaFold n l1 x else nbaFold n l2 x := by
  split <;> rfl

theorem skd_next (hwd : Wd N W AccW g) (hW : W < 2 ^ 32) {c m : Nat} (hc : c < N) (hm : m ≤ c) :
    (nbaFold "sk_d" (Cols N W AccW g) g.skd).extract ((tri c + m) * W) W =
      if m = 0 then g.wr.extract (((N - 1) * N + c) * W) W else g.skd.extract ((tri c + (m - 1)) * W) W := by
  have hw := hwd.skd
  have htl := tri_le hc
  have hL : tri c * W + (c + 1) * W ≤ g.skd.width := by
    rw [hw, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have hmW : m * W + W ≤ (c + 1) * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  rw [extract_fold_family (colQ N W AccW g) c (List.range N) List.nodup_range ?_ g.skd, if_pos (List.mem_range.mpr hc)]
  · simp only [colQ, List.cons_append, List.nil_append, nbaFold_cons_self, nbaFold_append, nbaFold_ite,
      nbaFold_cons_ne (show "m_b" ≠ "sk_d" by decide), nbaFold_cons_ne (show "m_d" ≠ "sk_d" by decide),
      nbaFold_cons_ne (show "sk_o" ≠ "sk_d" by decide), nbaFold_nil', ite_self]
    by_cases hm0 : m = 0
    · subst hm0
      rw [if_pos rfl, lane_zero' (by simp) (by simp) (by simp; omega)]
    · have hWm : W ≤ m * W := Nat.le_mul_of_pos_left W (show 0 < m by omega)
      rw [if_neg hm0, Nat.add_mul (tri _) m W, skip_win (Or.inl (by simp only [LVec.width_resizeU]; omega)),
        lane_succ hW (by omega) hmW (by omega), Nat.add_mul (tri _) (m - 1), Nat.sub_mul, Nat.one_mul]
  · intro k hk hkr u hu hn
    have hk' := List.mem_range.mp hk
    simp only [colQ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases Nat.lt_or_gt_of_ne hkr with hlt | hgt
    · have h1 : tri k * W + (k + 1) * W ≤ tri c * W := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono hlt; omega)
      have h2 : W ≤ (k + 1) * W := Nat.le_mul_of_pos_left W (by omega)
      have h3 : tri c * W ≤ (tri c + m) * W := Nat.mul_le_mul_right _ (by omega)
      region_tac
    · have h1 : (tri c + m) * W + W ≤ tri k * W := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono hgt; omega)
      region_tac

/-- Two row-major entries of distinct coordinates have disjoint `K`-bit windows. -/
theorem rm_disj {N K i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : ¬ (i = i' ∧ j = j')) :
    (i * N + j) * K + K ≤ (i' * N + j') * K ∨ (i' * N + j') * K + K ≤ (i * N + j) * K := by
  have hne : i * N + j ≠ i' * N + j' := by
    intro he
    have d1 : (i * N + j) / N = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
    have d2 : (i' * N + j') / N = i' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj', Nat.zero_add]
    have m1 : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have m2 : (i' * N + j') % N = j' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj']
    exact h ⟨by rw [← d1, ← d2, he], by rw [← m1, ← m2, he]⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact .inl (rowMajor_le hlt)
  · exact .inr (rowMajor_le hgt)

theorem sko_win (hwd : Wd N W AccW g) {c : Nat} (hc : c < N) :
    tri (N - 1 - c) * AccW + (N - c) * AccW ≤ g.sko.width := by
  rw [hwd.sko, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_le (show N - 1 - c < N by omega); omega)

theorem sko_region {c k m : Nat} (hc : c < N) (hk : k < N) (hkc : k ≠ c) (hm : m + c < N) (u : String × Nat × LVec)
    (hu : u ∈ colQ N W AccW g k) (hn : u.1 = "sk_o") :
    u.2.1 + u.2.2.width ≤ (tri (N - 1 - c) + m) * AccW ∨ (tri (N - 1 - c) + m) * AccW + AccW ≤ u.2.1 := by
  simp only [colQ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases Nat.lt_or_gt_of_ne hkc with hlt | hgt
  · have h1 : (tri (N - 1 - c) + m) * AccW + AccW ≤ tri (N - 1 - k) * AccW := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono (show N - 1 - c < N - 1 - k by omega); omega)
    region_tac
  · have h1 : tri (N - 1 - k) * AccW + (N - k) * AccW ≤ tri (N - 1 - c) * AccW := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by have := tri_mono (show N - 1 - k < N - 1 - c by omega); omega)
    have h2 : AccW ≤ (N - k) * AccW := Nat.le_mul_of_pos_left AccW (by omega)
    have h3 : tri (N - 1 - c) * AccW ≤ (tri (N - 1 - c) + m) * AccW := Nat.mul_le_mul_right _ (by omega)
    region_tac

theorem colQ_sko (c : Nat) (x : LVec) : nbaFold "sk_o" (colQ N W AccW g c) x =
    if (g.wv.extract (N + c) 1).condTrue then
      (x.insertAt (tri (N - 1 - c) * AccW) (((g.sko.extract (tri (N - 1 - c) * AccW) ((N - c) * AccW)).shl
        (LVec.ofInt 32 (AccW : Int))).resizeU ((N - c) * AccW))).insertAt (tri (N - 1 - c) * AccW)
          ((macV N W AccW (N - 1) c g).resizeU AccW)
    else x.insertAt (tri (N - 1 - c) * AccW) (((g.sko.extract (tri (N - 1 - c) * AccW) ((N - c) * AccW)).shl
        (LVec.ofInt 32 (AccW : Int))).resizeU ((N - c) * AccW)) := by
  by_cases h1 : (g.wv.extract c 1).condTrue = true <;> by_cases h2 : (g.wv.extract (N + c) 1).condTrue = true <;>
    simp [colQ, nbaFold, h1, h2]

theorem sko_next_zero (hwd : Wd N W AccW g) {c : Nat} (hc : c < N) (hv : (g.wv.extract (N + c) 1).condTrue = true) :
    (nbaFold "sk_o" (Cols N W AccW g) g.sko).extract ((tri (N - 1 - c) + 0) * AccW) AccW = macV N W AccW (N - 1) c g := by
  have hL := sko_win hwd hc
  have h2 : AccW ≤ (N - c) * AccW := Nat.le_mul_of_pos_left AccW (by omega)
  rw [extract_fold_family (colQ N W AccW g) c (List.range N) List.nodup_range
    (fun k hk hkc u hu hn => sko_region hc (List.mem_range.mp hk) hkc (by omega) u hu hn) g.sko,
    if_pos (List.mem_range.mpr hc), colQ_sko, if_pos hv,
    lane_zero' (by simp) (by simp [macV]) (by simp; omega)]

theorem sko_next_succ (hwd : Wd N W AccW g) (hA : AccW < 2 ^ 32) {c m : Nat} (hc : c < N) (hm : m + c < N)
    (hm1 : 1 ≤ m) :
    (nbaFold "sk_o" (Cols N W AccW g) g.sko).extract ((tri (N - 1 - c) + m) * AccW) AccW =
      g.sko.extract ((tri (N - 1 - c) + (m - 1)) * AccW) AccW := by
  have hL := sko_win hwd hc
  have hmW : m * AccW + AccW ≤ (N - c) * AccW := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h1 : AccW ≤ m * AccW := Nat.le_mul_of_pos_left AccW (by omega)
  rw [extract_fold_family (colQ N W AccW g) c (List.range N) List.nodup_range
    (fun k hk hkc u hu hn => sko_region hc (List.mem_range.mp hk) hkc hm u hu hn) g.sko,
    if_pos (List.mem_range.mpr hc), colQ_sko, Nat.add_mul (tri _) m AccW]
  split
  · rw [skip_win (Or.inl (by simp only [LVec.width_resizeU]; omega)), lane_succ hA hm1 hmW (by omega),
      Nat.add_mul (tri _) (m - 1), Nat.sub_mul, Nat.one_mul]
  · rw [lane_succ hA hm1 hmW (by omega), Nat.add_mul (tri _) (m - 1), Nat.sub_mul, Nat.one_mul]

/-- The `m_b`/`m_d` writes of `colQ k` and `pipeQ k j` are at their tile's window. -/
theorem colQ_mbd {k : Nat} (u : String × Nat × LVec) (hu : u ∈ colQ N W AccW g k) :
    (u.1 = "m_b" → u.2.1 = k * AccW ∧ u.2.2.width = AccW) ∧ (u.1 = "m_d" → u.2.1 = k * W ∧ u.2.2.width = W) := by
  simp only [colQ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  (repeat' split at hu) <;>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc] at hu <;>
    (repeat' rcases hu with rfl | hu) <;> simp_all

theorem pipeQ_mbd {k j : Nat} (u : String × Nat × LVec) (hu : u ∈ pipeQ N W AccW g k j) :
    (u.1 = "m_b" → u.2.1 = ((k + 1) * N + j) * AccW ∧ u.2.2.width = AccW) ∧
      (u.1 = "m_d" → u.2.1 = ((k + 1) * N + j) * W ∧ u.2.2.width = W) := by
  unfold pipeQ at hu
  split at hu
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> simp
  · simp at hu

/-- The pipes leave the windows of tile row 0, and the columns those of rows `≥ 1`. -/
theorem pipes_skip0 {n : String} {K c : Nat} (hc : c < N) (hn : ∀ u ∈ Pipes N W AccW g, u.1 = n →
    ∃ k j, j < N ∧ u.2.1 = ((k + 1) * N + j) * K ∧ u.2.2.width = K) (x : LVec) :
    (nbaFold n (Pipes N W AccW g) x).extract (c * K) K = x.extract (c * K) K := by
  refine extract_nbaFold_disj _ _ fun u hu h => ?_
  obtain ⟨k, j, hj, h1, h2⟩ := hn u hu h
  rw [h1, h2]
  have := rm_disj (N := N) (K := K) (i := 0) (j := c) (i' := k + 1) (j' := j) hc hj (by omega)
  simp only [Nat.zero_mul, Nat.zero_add] at this
  omega

theorem pipes_mb (u : String × Nat × LVec) (hu : u ∈ Pipes N W AccW g) (h : u.1 = "m_b") :
    ∃ k j, j < N ∧ u.2.1 = ((k + 1) * N + j) * AccW ∧ u.2.2.width = AccW := by
  simp only [Pipes, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨k, -, j, hj, hu⟩ := hu
  exact ⟨k, j, hj, (pipeQ_mbd u hu).1 h⟩

theorem pipes_md (u : String × Nat × LVec) (hu : u ∈ Pipes N W AccW g) (h : u.1 = "m_d") :
    ∃ k j, j < N ∧ u.2.1 = ((k + 1) * N + j) * W ∧ u.2.2.width = W := by
  simp only [Pipes, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨k, -, j, hj, hu⟩ := hu
  exact ⟨k, j, hj, (pipeQ_mbd u hu).2 h⟩

theorem mb_next_top (hwd : Wd N W AccW g) {c : Nat} (hc : c < N) (hv : (g.wv.extract c 1).condTrue = true) :
    (nbaFold "m_b" (Pipes N W AccW g) (nbaFold "m_b" (Cols N W AccW g) g.mb)).extract ((0 * N + c) * AccW) AccW =
      LVec.ofBitVec 0#AccW := by
  rw [Nat.zero_mul, Nat.zero_add, pipes_skip0 hc pipes_mb]
  have hcN : c * AccW + AccW ≤ g.mb.width := by
    rw [hwd.mb, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega)
  rw [extract_fold_family (colQ N W AccW g) c (List.range N) List.nodup_range ?_ g.mb, if_pos (List.mem_range.mpr hc)]
  · simp only [colQ, nbaFold_append, nbaFold_ite, hv, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne (show "sk_d" ≠ "m_b" by decide), nbaFold_cons_ne (show "m_d" ≠ "m_b" by decide),
      nbaFold_cons_ne (show "sk_o" ≠ "m_b" by decide), nbaFold_nil', ite_self, List.cons_append, List.nil_append]
    rw [LVec.extract_insertAt_self (by simp) hcN, LVec.replicate_l0, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  · intro k hk hkc u hu hn
    obtain ⟨h1, h2⟩ := (colQ_mbd u hu).1 hn
    rw [h1, h2]
    have := rm_disj (N := N) (K := AccW) (i := 0) (j := c) (i' := 0) (j' := k) hc (List.mem_range.mp hk) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at this
    omega

theorem mb_next_pipe (hwd : Wd N W AccW g) {r c : Nat} (hr : r + 1 < N) (hc : c < N)
    (hv : (g.wv.extract (r + c + 1) 1).condTrue = true) :
    (nbaFold "m_b" (Pipes N W AccW g) (nbaFold "m_b" (Cols N W AccW g) g.mb)).extract (((r + 1) * N + c) * AccW) AccW =
      macV N W AccW r c g := by
  have hwin : ((r + 1) * N + c) * AccW + AccW ≤ (nbaFold "m_b" (Cols N W AccW g) g.mb).width := by
    rw [width_nbaFold, hwd.mb]; exact Lib.rowMajor_window_le hr hc
  rw [Pipes, extract_fold_family (fun k => (List.range N).flatMap (pipeQ N W AccW g k)) r (List.range (N - 1))
      List.nodup_range ?_ _, if_pos (List.mem_range.mpr (by omega)),
    extract_fold_family (pipeQ N W AccW g r) c (List.range N) List.nodup_range ?_ _, if_pos (List.mem_range.mpr hc)]
  · simp only [pipeQ, hv, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne (show "m_d" ≠ "m_b" by decide), nbaFold_nil']
    rw [LVec.extract_insertAt_self (by simp) hwin, resizeU_self (by simp [macV])]
  · intro j hj hjc u hu hn
    obtain ⟨h1, h2⟩ := (pipeQ_mbd u hu).1 hn
    rw [h1, h2]
    exact rm_disj (List.mem_range.mp hj) hc (by omega)
  · intro k hk hkr u hu hn
    simp only [List.mem_flatMap, List.mem_range] at hu
    obtain ⟨j, hj, hu⟩ := hu
    obtain ⟨h1, h2⟩ := (pipeQ_mbd u hu).1 hn
    rw [h1, h2]
    exact rm_disj hj hc (by omega)

theorem md_next_top (hwd : Wd N W AccW g) {c : Nat} (hc : c < N) (hv : (g.wv.extract c 1).condTrue = true) :
    (nbaFold "m_d" (Pipes N W AccW g) (nbaFold "m_d" (Cols N W AccW g) g.md)).extract ((0 * N + c) * W) W =
      g.skd.extract ((tri c + c) * W) W := by
  rw [Nat.zero_mul, Nat.zero_add, pipes_skip0 hc pipes_md]
  have hcN : c * W + W ≤ g.md.width := by
    rw [hwd.md, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega)
  rw [extract_fold_family (colQ N W AccW g) c (List.range N) List.nodup_range ?_ g.md, if_pos (List.mem_range.mpr hc)]
  · simp only [colQ, nbaFold_append, nbaFold_ite, hv, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne (show "sk_d" ≠ "m_d" by decide), nbaFold_cons_ne (show "m_b" ≠ "m_d" by decide),
      nbaFold_cons_ne (show "sk_o" ≠ "m_d" by decide), nbaFold_nil', ite_self, List.cons_append, List.nil_append]
    rw [LVec.extract_insertAt_self (by simp) hcN, resizeU_self (by simp)]
  · intro k hk hkc u hu hn
    obtain ⟨h1, h2⟩ := (colQ_mbd u hu).2 hn
    rw [h1, h2]
    have := rm_disj (N := N) (K := W) (i := 0) (j := c) (i' := 0) (j' := k) hc (List.mem_range.mp hk) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at this
    omega

theorem md_next_pipe (hwd : Wd N W AccW g) {r c : Nat} (hr : r + 1 < N) (hc : c < N)
    (hv : (g.wv.extract (r + c + 1) 1).condTrue = true) (hp : g.wp.extract (r + c) 1 = knownBit true) :
    (nbaFold "m_d" (Pipes N W AccW g) (nbaFold "m_d" (Cols N W AccW g) g.md)).extract (((r + 1) * N + c) * W) W =
      g.c1.extract ((r * N + c) * W) W := by
  have hwin : ((r + 1) * N + c) * W + W ≤ (nbaFold "m_d" (Cols N W AccW g) g.md).width := by
    rw [width_nbaFold, hwd.md]; exact Lib.rowMajor_window_le hr hc
  rw [Pipes, extract_fold_family (fun k => (List.range N).flatMap (pipeQ N W AccW g k)) r (List.range (N - 1))
      List.nodup_range ?_ _, if_pos (List.mem_range.mpr (by omega)),
    extract_fold_family (pipeQ N W AccW g r) c (List.range N) List.nodup_range ?_ _, if_pos (List.mem_range.mpr hc)]
  · simp only [pipeQ, hv, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne (show "m_b" ≠ "m_d" by decide), nbaFold_nil']
    rw [LVec.extract_insertAt_self (by simp) hwin, hp, knownBit, LVec.ternary_ofBitVec_ofBool, if_pos rfl,
      resizeU_self (by simp)]
  · intro j hj hjc u hu hn
    obtain ⟨h1, h2⟩ := (pipeQ_mbd u hu).2 hn
    rw [h1, h2]
    exact rm_disj (List.mem_range.mp hj) hc (by omega)
  · intro k hk hkr u hu hn
    simp only [List.mem_flatMap, List.mem_range] at hu
    obtain ⟨j, hj, hu⟩ := hu
    obtain ⟨h1, h2⟩ := (pipeQ_mbd u hu).2 hn
    rw [h1, h2]
    exact rm_disj hj hc (by omega)

theorem tileQ_c1 {k j : Nat} (u : String × Nat × LVec) (hu : u ∈ tileQ N W g k j) (h : u.1 = "c1") :
    u.2.1 = (k * N + j) * W ∧ u.2.2.width = W := by
  unfold tileQ at hu
  (repeat' split at hu) <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hu <;>
    (try subst hu) <;> simp_all

theorem c1_next (hwd : Wd N W AccW g) {r c : Nat} (hr : r < N) (hc : c < N) :
    (nbaFold "c1" (Tiles N W g) g.c1).extract ((r * N + c) * W) W =
      if (g.wv.extract (r + c + 1) 1).condTrue ∧ (g.wp.extract (r + c) 1).condTrue then g.md.extract ((r * N + c) * W) W
      else g.c1.extract ((r * N + c) * W) W := by
  have hwin : (r * N + c) * W + W ≤ g.c1.width := by rw [hwd.c1]; exact Lib.rowMajor_window_le hr hc
  rw [Tiles, extract_fold_family (fun k => (List.range N).flatMap (tileQ N W g k)) r (List.range N)
      List.nodup_range ?_ _, if_pos (List.mem_range.mpr hr),
    extract_fold_family (tileQ N W g r) c (List.range N) List.nodup_range ?_ _, if_pos (List.mem_range.mpr hc)]
  · by_cases hv : (g.wv.extract (r + c + 1) 1).condTrue = true <;>
      by_cases hp : (g.wp.extract (r + c) 1).condTrue = true <;>
      simp only [tileQ, hv, hp, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne (show "c2" ≠ "c1" by decide),
        nbaFold_nil', and_self, and_true, true_and, Bool.false_eq_true, and_false, false_and]
    rw [LVec.extract_insertAt_self (by simp) hwin, resizeU_self (by simp)]
  · intro j hj hjc u hu hn
    obtain ⟨h1, h2⟩ := tileQ_c1 u hu hn
    rw [h1, h2]
    exact rm_disj (List.mem_range.mp hj) hc (by omega)
  · intro k hk hkr u hu hn
    simp only [List.mem_flatMap, List.mem_range] at hu
    obtain ⟨j, hj, hu⟩ := hu
    obtain ⟨h1, h2⟩ := tileQ_c1 u hu hn
    rw [h1, h2]
    exact rm_disj hj hc (by omega)

/-- The capture condition of `C(u, c)`. -/
abbrev outC (u : Nat) (g : Regs) (N : Nat) : Bool :=
  (g.bz.and (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 ((3 * N + 1 : Nat) : Int)).add
    (LVec.ofInt 32 (u : Int)))))).condTrue

theorem C_next (hwd : Wd N W AccW g) {u c : Nat} (hu : u < N) (hc : c < N) :
    (nbaFold "C" (Outs N AccW g) g.c).extract ((u * N + c) * AccW) AccW =
      if outC u g N then g.sko.extract ((tri (N - 1 - c) + (N - 1 - c)) * AccW) AccW
      else g.c.extract ((u * N + c) * AccW) AccW := by
  have hwin : (u * N + c) * AccW + AccW ≤ g.c.width := by rw [hwd.c]; exact Lib.rowMajor_window_le hu hc
  rw [Outs, extract_fold_family (fun k => (List.range N).flatMap (outQ N AccW g k)) u (List.range N)
      List.nodup_range ?_ _, if_pos (List.mem_range.mpr hu),
    extract_fold_family (outQ N AccW g u) c (List.range N) List.nodup_range ?_ _, if_pos (List.mem_range.mpr hc)]
  · unfold outQ outC
    split
    · simp only [nbaFold_cons_self, nbaFold_nil']
      rw [LVec.extract_insertAt_self (by simp) hwin, resizeU_self (by simp)]
    · rfl
  · intro j hj hjc v hv hn
    unfold outQ at hv
    split at hv
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      simp only [LVec.width_resizeU]
      exact rm_disj (List.mem_range.mp hj) hc (by omega)
    · simp at hv
  · intro k hk hkr v hv hn
    simp only [List.mem_flatMap, List.mem_range] at hv
    obtain ⟨j, hj, hv⟩ := hv
    unfold outQ at hv
    split at hv
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      subst hv
      simp only [LVec.width_resizeU]
      exact rm_disj hj hc (by omega)
    · simp at hv

theorem waveQ_fold_wv (x : LVec) : nbaFold "wv" (waveQ N g) x =
    (x.insertAt 0 ((g.wv.shl (LVec.ofInt 32 1)).resizeU g.wv.width)).insertAt 0
      ((g.bz.and (LVec.ofLogic (g.st.lt (LVec.ofInt 32 ((2 * N : Nat) : Int))))).resizeU 1) := by
  by_cases h : (g.wv.extract 0 1).condTrue = true <;> simp [waveQ, nbaFold, h]

theorem wv_next_zero (hwd : Wd N W AccW g) (hN : 1 ≤ N) :
    (nbaFold "wv" (waveQ N g) g.wv).extract 0 1 =
      (g.bz.and (LVec.ofLogic (g.st.lt (LVec.ofInt 32 ((2 * N : Nat) : Int))))).resizeU 1 := by
  rw [waveQ_fold_wv, LVec.extract_insertAt_self (by simp) (by simp [hwd.wv]; omega)]

theorem wv_next_succ (hwd : Wd N W AccW g) {k : Nat} (hk : k + 1 < 2 * N) :
    (nbaFold "wv" (waveQ N g) g.wv).extract (k + 1) 1 = g.wv.extract k 1 := by
  have hs := extract_shl (p := g.wv) (K := 1) (a := k + 1) (w := 1) (by decide) (by omega) (by rw [hwd.wv]; omega)
  have h1 : ((1 : Nat) : Int) = 1 := rfl
  rw [h1] at hs
  rw [waveQ_fold_wv, skip_win (Or.inl (by simp)), extract_insertAt_cover (by omega) (by simp [hwd.wv]; omega) (by simp [hwd.wv]; omega),
    Nat.sub_zero, extract_resizeU (by rw [hwd.wv]; omega) (by simp [width_shl, hwd.wv]; omega), hs, Nat.add_sub_cancel]

theorem pb_next (hwd : Wd N W AccW g) : nbaFold "pb" (waveQ N g) g.pb = g.ip := by
  have e : nbaFold "pb" (waveQ N g) g.pb = g.pb.insertAt 0 (g.ip.resizeU g.pb.width) := by
    by_cases h : (g.wv.extract 0 1).condTrue = true <;> simp [waveQ, nbaFold, h]
  rw [e, LVec.insertAt_zero_of_width_eq (by simp), hwd.pb, resizeU_self hwd.ip]

theorem waveQ_fold_wp (x : LVec) : nbaFold "wp" (waveQ N g) x =
    if (g.wv.extract 0 1).condTrue then x.insertAt 0 (g.pb.resizeU 1) else x := by
  by_cases h : (g.wv.extract 0 1).condTrue = true <;> simp [waveQ, nbaFold, h]

theorem props_wp (u : String × Nat × LVec) (hu : u ∈ Props N g) : ∃ k, u.2.1 = k + 1 ∧ u.2.2.width = 1 := by
  simp only [Props, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨k, -, hu⟩ := hu
  unfold propQ at hu
  split at hu
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; subst hu; exact ⟨k, rfl, by simp⟩
  · simp at hu

theorem wp_next_zero (hwd : Wd N W AccW g) (hN : 1 ≤ N) :
    (nbaFold "wp" (Props N g) (nbaFold "wp" (waveQ N g) g.wp)).extract 0 1 =
      if (g.wv.extract 0 1).condTrue then g.pb else g.wp.extract 0 1 := by
  rw [extract_nbaFold_disj _ _ fun u hu _ => by obtain ⟨k, h1, -⟩ := props_wp u hu; omega, waveQ_fold_wp]
  split
  · rw [LVec.extract_insertAt_self (by simp) (by rw [hwd.wp]; omega), resizeU_self hwd.pb]
  · rfl

theorem wp_next_succ (hwd : Wd N W AccW g) {k : Nat} (hk : k + 1 < 2 * N - 1) :
    (nbaFold "wp" (Props N g) (nbaFold "wp" (waveQ N g) g.wp)).extract (k + 1) 1 =
      if (g.wv.extract (k + 1) 1).condTrue then g.wp.extract k 1 else g.wp.extract (k + 1) 1 := by
  have hwx : k + 1 + 1 ≤ (nbaFold "wp" (waveQ N g) g.wp).width := by rw [width_nbaFold, hwd.wp]; omega
  rw [Props, extract_fold_family (propQ g) k (List.range (2 * N - 2)) List.nodup_range ?_ _,
    if_pos (List.mem_range.mpr (by omega))]
  · unfold propQ
    split
    · simp only [nbaFold_cons_self, nbaFold_nil']
      rw [LVec.extract_insertAt_self (by simp) hwx, resizeU_self (by simp)]
    · simp only [nbaFold_nil']
      rw [waveQ_fold_wp]
      split
      · rw [skip_win (Or.inl (by simp))]
      · rfl
  · intro j _ hjk u hu _
    unfold propQ at hu
    split at hu
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu; subst hu; simp; omega
    · simp at hu

end nexts

/-! ## 6. Known values: the BitVec side -/

attribute [local simp] condTrue_knownBit

/-- Entry `(u, k)` of a flat `N × N` matrix of `W`-bit entries. -/
def aE (N W : Nat) (A : BitVec (N * N * W)) (u k : Nat) : BitVec W := A.extractLsb' ((u * N + k) * W) W

/-- `Σ_{k < r} A[u][k]·B[k][c]` in the integers. -/
def ps (N W : Nat) (A B : BitVec (N * N * W)) (u r c : Nat) : Int :=
  (List.range r).foldl (fun acc k => acc + (aE N W A u k).toInt * (aE N W B k c).toInt) 0

theorem ps_succ (N W : Nat) (A B : BitVec (N * N * W)) (u r c : Nat) :
    ps N W A B u (r + 1) c = ps N W A B u r c + (aE N W A u r).toInt * (aE N W B r c).toInt := by
  simp [ps, List.range_succ, List.foldl_append]

theorem ps_zero (N W : Nat) (A B : BitVec (N * N * W)) (u c : Nat) : ps N W A B u 0 c = 0 := rfl

theorem ps_dot (N W : Nat) (A B : BitVec (N * N * W)) (u c : Nat) :
    ps N W A B u N c = Tasks.Matmul.dot N W A B u c := rfl

theorem extractLsb'_zero_self {w : Nat} (x : BitVec w) : x.extractLsb' 0 w = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem sxv_window {v : LVec} {AccW lo W : Nat} {x : BitVec W} (hW : 1 ≤ W) (h : v.extract lo W = .ofBitVec x) :
    sxv v AccW lo W = .ofBitVec (x.signExtend (AccW + W)) := by
  have h1 : v.extract (lo + W - 1) 1 = .ofBitVec (x.extractLsb' (W - 1) 1) := by
    rw [show lo + W - 1 = lo + (W - 1) by omega, ← LVec.extract_extract v (show W - 1 + 1 ≤ W by omega), h,
      LVec.extract_ofBitVec _ (by omega)]
  rw [sxv, h1, h]
  have := LVec.ofBitVec_replicate_append_eq_signExtend hW x AccW (lo := 0) (p := W - 1) (by omega)
  rw [extractLsb'_zero_self] at this
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  exact this

/-- **The MAC of a compute row**: `m_b + A[u][r]·B[r][c]`, wrapped. -/
theorem mac_compute {N W AccW r c : Nat} (g : Regs) (hW : 1 ≤ W) {p : Int} {x y : BitVec W}
    (hb : g.mb.extract ((r * N + c) * AccW) AccW = .ofBitVec (BitVec.ofInt AccW p))
    (ha : g.ma.extract ((r * N + c) * W) W = .ofBitVec x)
    (hp : g.wp.extract (r + c) 1 = knownBit false)
    (hc : g.c1.extract ((r * N + c) * W) W = .ofBitVec y) :
    macV N W AccW r c g = .ofBitVec (BitVec.ofInt AccW (p + x.toInt * y.toInt)) := by
  unfold macV
  rw [hb, hp, sxv_window hW ha, sxv_window hW hc, knownBit, LVec.ternary_ofBitVec_ofBool]
  simp only [Bool.false_eq_true, ↓reduceIte, LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec]
  rw [Lib.setWidth_add_mul_signExtend (by omega), BitVec.ofInt_add]

theorem ar_entry {N W : Nat} (A : BitVec (N * N * W)) {u r : Nat} (hu : u < N) (hr : r < N) :
    (LVec.ofBitVec (A >>> (u * (N * W)))).extract (r * W) W = LVec.ofBitVec (aE N W A u r) := by
  have h1 : r * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (j := r) (by omega) hr
    simpa using this
  rw [LVec.extract_ofBitVec _ h1, Lib.extractLsb'_ushiftRight, aE,
    show u * (N * W) + r * W = (u * N + r) * W by rw [Nat.add_mul, Nat.mul_assoc]]

theorem extractLsb'_shiftLeft {n : Nat} (x : BitVec n) {s lo w : Nat} (h1 : s ≤ lo) (h2 : lo + w ≤ n) :
    (x <<< s).extractLsb' lo w = x.extractLsb' (lo - s) w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hi, show lo + i < n by omega,
    show ¬ lo + i < s by omega, show lo + i - s = lo - s + i by omega]
  all_goals exact (BitVec.getLsbD_eq_getElem (by omega)).symm

theorem wr_entry {N W : Nat} (B : BitVec (N * N * W)) {ρ c : Nat} (hρ : ρ < N) (hc : c < N) :
    (LVec.ofBitVec (B <<< (ρ * (N * W)))).extract (((N - 1) * N + c) * W) W =
      LVec.ofBitVec (aE N W B (N - 1 - ρ) c) := by
  have hl : ((N - 1) * N + c) * W + W ≤ N * N * W := Lib.rowMajor_window_le (by omega) hc
  have e0 : (N - 1) * N = ρ * N + (N - 1 - ρ) * N := by rw [← Nat.add_mul]; congr 1; omega
  have e : ((N - 1) * N + c) * W = ρ * (N * W) + ((N - 1 - ρ) * N + c) * W := by
    rw [e0, Nat.add_assoc, Nat.add_mul (ρ * N), Nat.mul_assoc]
  rw [LVec.extract_ofBitVec _ hl, extractLsb'_shiftLeft _ (by rw [e]; omega) hl, aE, e, Nat.add_sub_cancel_left]

theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft, LVec.getElem?_ofBitVec]
  by_cases h : i < y.toNat
  · simp [h, Logic.ofBool]
  · simp [h, show i - y.toNat < w by omega, hi]

theorem cond_eq32 {t v : Nat} (ht : t < 2 ^ 32) (hv : v < 2 ^ 32) :
    (LVec.ofLogic ((LVec.ofBitVec (BitVec.ofNat 32 t)).eqLogical (LVec.ofInt 32 (v : Int)))).condTrue = decide (t = v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit]
  by_cases h : t = v
  · subst h; simp
  · have : BitVec.ofNat 32 t ≠ BitVec.ofNat 32 v := by
      intro he; have := congrArg BitVec.toNat he
      simp [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hv] at this; exact h this
    simp [h, this]

theorem cond_lt32 {t v : Nat} (ht : t < 2 ^ 32) (hv : v < 2 ^ 32) :
    (LVec.ofLogic ((LVec.ofBitVec (BitVec.ofNat 32 t)).lt (LVec.ofInt 32 (v : Int)))).condTrue = decide (t < v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit]
  simp [BitVec.lt_def, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hv]

theorem cond_ge32 {t v : Nat} (ht : t < 2 ^ 32) (hv : v < 2 ^ 32) :
    (LVec.ofLogic ((LVec.ofBitVec (BitVec.ofNat 32 t)).ge (LVec.ofInt 32 (v : Int)))).condTrue = decide (v ≤ t) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.ge_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit]
  simp [BitVec.le_def, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hv]

theorem sub_one32 {N : Nat} (hN : 1 ≤ N) (hN' : N < 2 ^ 32) :
    (LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1) = LVec.ofInt 32 ((N - 1 : Nat) : Int) := by
  rw [LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.sub_ofBitVec]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  rw [show (1 : Int) = ((1 : Nat) : Int) from rfl, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

theorem add32 {a b : Nat} (h : a + b < 2 ^ 32) :
    (LVec.ofInt 32 (a : Int)).add (LVec.ofInt 32 (b : Int)) = LVec.ofInt 32 ((a + b : Nat) : Int) := by
  rw [LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.add_ofBitVec,
    BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofInt_natCast, BitVec.ofNat_add_ofNat]

theorem and_kb (a b : Bool) : (knownBit a).and (knownBit b) = knownBit (a && b) := by
  simp only [knownBit, LVec.and_ofBitVec]
  exact congrArg _ (by cases a <;> cases b <;> decide)

theorem ofLogic_kb (b : Bool) : LVec.ofLogic (Logic.ofBool b) = knownBit b := LVec.ofLogic_ofBool b

theorem ushr_ushr {w : Nat} (x : BitVec w) (a b : Nat) : x >>> a >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

theorem lt32_kb {t v : Nat} (ht : t < 2 ^ 32) (hv : v < 2 ^ 32) :
    LVec.ofLogic ((LVec.ofBitVec (BitVec.ofNat 32 t)).lt (LVec.ofInt 32 (v : Int))) = knownBit (decide (t < v)) := by
  have e := cond_lt32 ht hv
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit] at e
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, e]

theorem eq32_kb {t v : Nat} (ht : t < 2 ^ 32) (hv : v < 2 ^ 32) :
    LVec.ofLogic ((LVec.ofBitVec (BitVec.ofNat 32 t)).eqLogical (LVec.ofInt 32 (v : Int))) =
      knownBit (decide (t = v)) := by
  have e := cond_eq32 ht hv
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    condTrue_knownBit] at e
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, e]

theorem kb_w0 (b : Bool) : (knownBit b).insertAt 0 ((⟨#[Logic.l0]⟩ : LVec).resizeU (knownBit b).width) = knownBit false := by
  cases b <;> first | rfl | decide

theorem kb_w1 (b : Bool) : (knownBit b).insertAt 0 ((⟨#[Logic.l1]⟩ : LVec).resizeU (knownBit b).width) = knownBit true := by
  cases b <;> first | rfl | decide

theorem resizeU_kb (b : Bool) : (knownBit b).resizeU 1 = knownBit b := by
  cases b <;> first | rfl | decide

theorem bounds {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) :
    N * W < 2 ^ 31 ∧ N < 2 ^ 31 ∧ W < 2 ^ 31 ∧ 5 * N < 2 ^ 31 + 25 ∧ N * N < 2 ^ 31 := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
  have h2 : N ≤ N * W := Nat.le_mul_of_pos_right _ hW
  have h3 : W ≤ N * W := Nat.le_mul_of_pos_left _ hN
  have h4 : N * N ≤ N * N * W := Nat.le_mul_of_pos_right _ hW
  have h5 : 5 * N ≤ N * N + 25 := by
    rcases Nat.lt_or_ge N 5 with h | h
    · omega
    · have := Nat.mul_le_mul_right N h; omega
  omega

theorem wr_whole {x v : LVec} (h : v.width = x.width) : x.insertAt 0 (v.resizeU x.width) = v := by
  rw [LVec.insertAt_zero_of_width_eq (by simp), resizeU_self h]

theorem kb_not (b : Bool) : (knownBit b).not = knownBit (!b) := by
  simp only [knownBit, LVec.not_ofBitVec]; congr 1; cases b <;> decide

theorem kb_width (b : Bool) : (knownBit b).width = 1 := by
  cases b <;> first | rfl | simp [knownBit]

theorem kb_not_w (b : Bool) : (knownBit b).insertAt 0 ((knownBit b).not.resizeU (knownBit b).width) = knownBit (!b) := by
  rw [kb_not, wr_whole (by rw [kb_width, kb_width])]

theorem l0_kb : (⟨#[Logic.l0]⟩ : LVec) = knownBit false := by first | rfl | decide
theorem l1_kb : (⟨#[Logic.l1]⟩ : LVec) = knownBit true := by first | rfl | decide

theorem wr1 {x v : LVec} (hx : x.width = 1) (hv : v.width = 1) : x.insertAt 0 (v.resizeU x.width) = v :=
  wr_whole (by rw [hx, hv])

theorem rep0 : LVec.replicate 32 Logic.l0 = LVec.ofBitVec (BitVec.ofNat 32 0) := by
  first | decide | rfl | simp [LVec.replicate_l0]

/-! ## 7. The invariant: the state `t` busy steps after a start -/

structure Inv (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (g : Regs) : Prop where
  wd : Wd N W AccW g
  dn : g.dn = knownBit (decide (t = 4 * N + 1))
  bz : g.bz = knownBit (decide (t ≤ 4 * N))
  st : g.st = .ofBitVec (BitVec.ofNat 32 t)
  ip : g.ip = knownBit (decide (t < N))
  ar : g.ar = .ofBitVec (A >>> ((t - N) * (N * W)))
  wr : g.wr = .ofBitVec (B <<< (min t N * (N * W)))
  pb : ∀ ρ, t = ρ + 1 → g.pb = knownBit (decide (ρ < N))
  wv : ∀ k ρ, k < 2 * N → t = ρ + 1 + k → g.wv.extract k 1 = knownBit (decide (ρ < 2 * N))
  wp : ∀ k ρ, k + 1 < 2 * N → t = ρ + 2 + k → g.wp.extract k 1 = knownBit (decide (ρ < N))
  ska : ∀ r m u, r < N → m ≤ r → u < N → t = N + u + 1 + m →
    g.ska.extract ((tri r + m) * W) W = .ofBitVec (aE N W A u r)
  skd : ∀ c m ρ, c < N → m ≤ c → ρ < N → t = ρ + 1 + m →
    g.skd.extract ((tri c + m) * W) W = .ofBitVec (aE N W B (N - 1 - ρ) c)
  ma : ∀ r c u, r < N → c < N → u < N → t = N + u + 2 + r + c →
    g.ma.extract ((r * N + c) * W) W = .ofBitVec (aE N W A u r)
  md : ∀ r c j, r < N → c < N → r + j < N → t = r + j + 2 + r + c →
    g.md.extract ((r * N + c) * W) W = .ofBitVec (aE N W B (N - 1 - j) c)
  mb : ∀ r c u, r < N → c < N → u < N → t = N + u + 2 + r + c →
    g.mb.extract ((r * N + c) * AccW) AccW = .ofBitVec (BitVec.ofInt AccW (ps N W A B u r c))
  c1 : ∀ r c ρ, r < N → c < N → r + 1 ≤ ρ → t = ρ + 2 + r + c →
    g.c1.extract ((r * N + c) * W) W = .ofBitVec (aE N W B (N + r - min ρ N) c)
  sko : ∀ c m u, c < N → m + c < N → u < N → t = N + u + N + 2 + c + m →
    g.sko.extract ((tri (N - 1 - c) + m) * AccW) AccW = .ofBitVec (BitVec.ofInt AccW (ps N W A B u N c))
  cc : ∀ u c, u < N → c < N → 3 * N + 2 + u ≤ t →
    g.c.extract ((u * N + c) * AccW) AccW = .ofBitVec (BitVec.ofInt AccW (ps N W A B u N c))

/-- The control in a busy step. -/
theorem ctrl_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t ≤ 4 * N) {g : Regs} (h : Inv N W AccW A B t g) (a b : LVec) :
    nbaFold "busy" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.bz = knownBit (decide (t + 1 ≤ 4 * N)) ∧
    nbaFold "done" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.dn =
      knownBit (decide (t + 1 = 4 * N + 1)) ∧
    nbaFold "step" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.st = .ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
    nbaFold "in_prop" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.ip = knownBit (decide (t + 1 < N)) ∧
    nbaFold "a_rows" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.ar =
      .ofBitVec (A >>> ((t + 1 - N) * (N * W))) ∧
    nbaFold "w_rows" (ctrlQ N W (knownBit false) (knownBit false) a b g) g.wr =
      .ofBitVec (B <<< (min (t + 1) N * (N * W))) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := bounds hN hW hr
  have hbz : g.bz = knownBit true := by rw [h.bz, decide_eq_true ht]
  have hdn : g.dn = knownBit false := by rw [h.dn, decide_eq_false (show ¬ t = 4 * N + 1 by omega)]
  have c1 : (LVec.ofLogic (g.st.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue =
      decide (t = N - 1) := by rw [h.st, sub_one32 hN (by omega), cond_eq32 (by omega) (by omega)]
  have c2 : (LVec.ofLogic (g.st.lt (LVec.ofInt 32 (N : Int)))).condTrue = decide (t < N) := by
    rw [h.st, cond_lt32 (by omega) (by omega)]
  have c3 : (LVec.ofLogic (g.st.ge (LVec.ofInt 32 (N : Int)))).condTrue = decide (N ≤ t) := by
    rw [h.st, cond_ge32 (by omega) (by omega)]
  have c4 : (LVec.ofLogic (g.st.eqLogical (LVec.ofInt 32 ((4 * N : Nat) : Int)))).condTrue = decide (t = 4 * N) := by
    rw [h.st, cond_eq32 (by omega) (by omega)]
  have hNW : (LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)) = LVec.ofBitVec (BitVec.ofNat 32 (N * W)) := by
    rw [LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.mul_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_natCast,
      BitVec.ofNat_mul_ofNat]
  have hNWv : (BitVec.ofNat 32 (N * W)).toNat = N * W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hs1 : g.st.add (LVec.ofInt 32 1) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) := by
    rw [h.st, show (1 : Int) = ((1 : Nat) : Int) from rfl, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast,
      LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]
  have hw1 := h.wd.st
  simp (disch := decide) only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, hbz, c1, c2, c3, c4,
    decide_eq_true_eq, List.cons_append, List.nil_append, nbaFold_append, nbaFold_ite, nbaFold_cons_self,
    nbaFold_cons_ne, nbaFold_nil', ite_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases e : t = 4 * N
    · rw [if_pos e, decide_eq_false (show ¬ t + 1 ≤ 4 * N by omega), kb_w0]
    · rw [if_neg e, decide_eq_true (show t + 1 ≤ 4 * N by omega)]
  · rw [hdn]
    by_cases e : t = 4 * N
    · rw [if_pos e, decide_eq_true (show t + 1 = 4 * N + 1 by omega), kb_w1]
    · rw [if_neg e, decide_eq_false (show ¬ t + 1 = 4 * N + 1 by omega)]
  · rw [hs1, wr_whole (by simp [hw1])]
  · rw [h.ip]
    by_cases e : t = N - 1
    · rw [if_pos e, kb_not_w, decide_eq_true (show t < N by omega), decide_eq_false (show ¬ t + 1 < N by omega),
        Bool.not_true]
    · rw [if_neg e]
      by_cases e2 : t < N
      · rw [decide_eq_true e2, decide_eq_true (show t + 1 < N by omega)]
      · rw [decide_eq_false e2, decide_eq_false (show ¬ t + 1 < N by omega)]
  · by_cases e : N ≤ t
    · rw [if_pos e, hNW, h.ar, LVec.shr_ofBitVec, hNWv, wr_whole (by simp), ushr_ushr,
        show t + 1 - N = (t - N) + 1 by omega, Nat.add_mul, Nat.one_mul]
    · rw [if_neg e, h.ar, show t - N = 0 by omega, show t + 1 - N = 0 by omega]
  · by_cases e : t < N
    · rw [if_pos e, hNW, h.wr, shl_ofBitVec, hNWv, wr_whole (by simp), ← BitVec.shiftLeft_add,
        Nat.min_eq_left (show t ≤ N by omega), Nat.min_eq_left (show t + 1 ≤ N by omega), Nat.add_mul, Nat.one_mul]
    · rw [if_neg e, h.wr, Nat.min_eq_right (show N ≤ t by omega), Nat.min_eq_right (show N ≤ t + 1 by omega)]

theorem kb_cond {b : Bool} {v : LVec} (h : v = knownBit b) : v.condTrue = b := by rw [h, condTrue_knownBit]

theorem outC_eval {N : Nat} {g : Regs} {t u : Nat} (hbz : g.bz = knownBit true)
    (hst : g.st = .ofBitVec (BitVec.ofNat 32 t)) (ht : t < 2 ^ 32) (hu : 3 * N + 1 + u < 2 ^ 32) :
    outC u g N = decide (t = 3 * N + 1 + u) := by
  unfold outC
  rw [hbz, hst, add32 hu, eq32_kb ht hu, and_kb, condTrue_knownBit, Bool.true_and]

/-- **One busy step of the invariant.** -/
theorem inv_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31)
    (hrA : N * N * AccW < 2 ^ 31) (A B : BitVec (N * N * W)) {t : Nat} (ht : t ≤ 4 * N) {g : Regs}
    (h : Inv N W AccW A B t g) (a b : LVec) :
    Inv N W AccW A B (t + 1) (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := bounds hN hW hr
  obtain ⟨b6, -, b7, -, -⟩ := bounds hN hA hrA
  obtain ⟨hcb, hcd, hcs, hci, hca, hcw⟩ := ctrl_step hN hW hr A B ht h a b
  have hwd := h.wd
  have hbz : g.bz = knownBit true := by rw [h.bz, decide_eq_true ht]
  have hW32 : W < 2 ^ 32 := by omega
  have hA32 : AccW < 2 ^ 32 := by omega
  refine ⟨hwd.fold _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show nbaFold "done" _ g.dn = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "done" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hcd
  · show nbaFold "busy" _ g.bz = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "busy" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hcb
  · show nbaFold "step" _ g.st = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "step" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hcs
  · show nbaFold "in_prop" _ g.ip = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "in_prop" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hci
  · show nbaFold "a_rows" _ g.ar = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "a_rows" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hca
  · show nbaFold "w_rows" _ g.wr = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "w_rows" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]; exact hcw
  · -- pb
    intro ρ hρ
    show nbaFold "pb" _ g.pb = _
    obtain rfl : ρ = t := by omega
    rw [fold_pb, pb_next hwd, h.ip]
  · -- wv
    intro k ρ hk hkt
    show (nbaFold "wv" _ g.wv).extract k 1 = _
    rw [fold_wv]
    rcases k with _ | k
    · obtain rfl : ρ = t := by omega
      rw [wv_next_zero hwd hN, hbz, h.st, lt32_kb (by omega) (by omega), and_kb, Bool.true_and, resizeU_kb]
    · rw [wv_next_succ hwd hk]; exact h.wv k ρ (by omega) (by omega)
  · -- wp
    intro k ρ hk hkt
    show (nbaFold "wp" _ g.wp).extract k 1 = _
    rw [fold_wp]
    rcases k with _ | k
    · rw [wp_next_zero hwd hN, kb_cond (h.wv 0 ρ (by omega) (by omega))]
      by_cases hv : ρ < 2 * N
      · rw [decide_eq_true hv, if_pos rfl]; exact h.pb ρ (by omega)
      · rw [decide_eq_false hv, if_neg (by simp), h.wp 0 (ρ - 1) (by omega) (by omega),
          decide_eq_false (show ¬ ρ - 1 < N by omega), decide_eq_false (show ¬ ρ < N by omega)]
    · rw [wp_next_succ hwd (by omega), kb_cond (h.wv (k + 1) ρ (by omega) (by omega))]
      by_cases hv : ρ < 2 * N
      · rw [decide_eq_true hv, if_pos rfl]; exact h.wp k ρ (by omega) (by omega)
      · rw [decide_eq_false hv, if_neg (by simp), h.wp (k + 1) (ρ - 1) (by omega) (by omega),
          decide_eq_false (show ¬ ρ - 1 < N by omega), decide_eq_false (show ¬ ρ < N by omega)]
  · -- sk_a
    intro r m u hr hm hu htm
    show (nbaFold "sk_a" _ g.ska).extract _ _ = _
    rw [fold_ska, ska_next hwd hW32 hr hm]
    split
    · rename_i hm0; subst hm0
      rw [h.ar, show t - N = u by omega]; exact ar_entry A hu hr
    · exact h.ska r (m - 1) u hr (by omega) hu (by omega)
  · -- sk_d
    intro c m ρ hc hm hρ htm
    show (nbaFold "sk_d" _ g.skd).extract _ _ = _
    rw [fold_skd, skd_next hwd hW32 hc hm]
    split
    · rename_i hm0; subst hm0
      rw [h.wr, show min t N = ρ by omega]; exact wr_entry B hρ hc
    · exact h.skd c (m - 1) ρ hc (by omega) hρ (by omega)
  · -- m_a
    intro r c u hr hc hu htm
    show (nbaFold "m_a" _ g.ma).extract _ _ = _
    rw [fold_ma, ma_next hwd hW32 hr hc]
    split
    · exact h.ska r r u hr (Nat.le_refl _) hu (by omega)
    · exact h.ma r (c - 1) u hr (by omega) hu (by omega)
  · -- m_d
    intro r c j hr hc hj htm
    show (nbaFold "m_d" _ g.md).extract _ _ = _
    rw [fold_md]
    rcases r with _ | r
    · have hv : (g.wv.extract c 1).condTrue = true := by
        rw [kb_cond (h.wv c j (by omega) (by omega))]; exact decide_eq_true (by omega)
      rw [md_next_top hwd hc hv]
      exact h.skd c c j hc (Nat.le_refl _) (by omega) (by omega)
    · have hv : (g.wv.extract (r + c + 1) 1).condTrue = true := by
        rw [kb_cond (h.wv (r + c + 1) (r + j + 1) (by omega) (by omega))]; exact decide_eq_true (by omega)
      have hp : g.wp.extract (r + c) 1 = knownBit true := by
        rw [h.wp (r + c) (r + j + 1) (by omega) (by omega), decide_eq_true (show r + j + 1 < N by omega)]
      rw [md_next_pipe hwd hr hc hv hp, h.c1 r c (r + j + 1) (by omega) hc (by omega) (by omega),
        Nat.min_eq_left (show r + j + 1 ≤ N by omega), show N + r - (r + j + 1) = N - 1 - j by omega]
  · -- m_b
    intro r c u hr hc hu htm
    show (nbaFold "m_b" _ g.mb).extract _ _ = _
    rw [fold_mb]
    rcases r with _ | r
    · have hv : (g.wv.extract c 1).condTrue = true := by
        rw [kb_cond (h.wv c (N + u) (by omega) (by omega))]; exact decide_eq_true (by omega)
      rw [mb_next_top hwd hc hv, ps_zero]; congr 1
    · have hv : (g.wv.extract (r + c + 1) 1).condTrue = true := by
        rw [kb_cond (h.wv (r + c + 1) (N + u) (by omega) (by omega))]; exact decide_eq_true (by omega)
      have hp : g.wp.extract (r + c) 1 = knownBit false := by
        rw [h.wp (r + c) (N + u) (by omega) (by omega), decide_eq_false (show ¬ N + u < N by omega)]
      have hc1 := h.c1 r c (N + u) (by omega) hc (by omega) (by omega)
      rw [Nat.min_eq_right (by omega), show N + r - N = r by omega] at hc1
      rw [mb_next_pipe hwd hr hc hv, mac_compute g hW (h.mb r c u (by omega) hc hu (by omega))
        (h.ma r c u (by omega) hc hu (by omega)) hp hc1, ps_succ]
  · -- c1
    intro r c ρ hr hc hρ htm
    show (nbaFold "c1" _ g.c1).extract _ _ = _
    rw [fold_c1, c1_next hwd hr hc, kb_cond (h.wv (r + c + 1) (ρ - 1) (by omega) (by omega)),
      kb_cond (h.wp (r + c) (ρ - 1) (by omega) (by omega))]
    by_cases hv : ρ - 1 < N
    · rw [if_pos (by simp; omega), h.md r c (ρ - 1 - r) hr hc (by omega) (by omega)]
      congr 2; rw [Nat.min_eq_left (by omega)]; omega
    · rw [if_neg (by simp; omega), h.c1 r c (ρ - 1) hr hc (by omega) (by omega)]
      congr 2; rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
  · -- sk_o
    intro c m u hc hm hu htm
    show (nbaFold "sk_o" _ g.sko).extract _ _ = _
    rw [fold_sko]
    rcases m with _ | m
    · have hv : (g.wv.extract (N + c) 1).condTrue = true := by
        rw [kb_cond (h.wv (N + c) (N + u) (by omega) (by omega))]; exact decide_eq_true (by omega)
      have hp : g.wp.extract (N - 1 + c) 1 = knownBit false := by
        rw [h.wp (N - 1 + c) (N + u) (by omega) (by omega), decide_eq_false (show ¬ N + u < N by omega)]
      have hc1 := h.c1 (N - 1) c (N + u) (by omega) hc (by omega) (by omega)
      rw [Nat.min_eq_right (by omega), show N + (N - 1) - N = N - 1 by omega] at hc1
      have hps : ps N W A B u N c = ps N W A B u (N - 1) c + (aE N W A u (N - 1)).toInt * (aE N W B (N - 1) c).toInt := by
        rw [← ps_succ, Nat.sub_add_cancel hN]
      rw [sko_next_zero hwd hc hv, mac_compute g hW (h.mb (N - 1) c u (by omega) hc hu (by omega))
        (h.ma (N - 1) c u (by omega) hc hu (by omega)) hp hc1, hps]
    · rw [sko_next_succ hwd hA32 hc hm (by omega)]
      exact h.sko c m u hc (by omega) hu (by omega)
  · -- C
    intro u c hu hc htu
    show (nbaFold "C" _ g.c).extract _ _ = _
    rw [fold_C, C_next hwd hu hc, outC_eval hbz h.st (by omega) (by omega)]
    by_cases hcap : t = 3 * N + 1 + u
    · rw [if_pos (by simp [hcap])]
      exact h.sko c (N - 1 - c) u hc (by omega) hu (by omega)
    · rw [if_neg (by simp [hcap])]
      exact h.cc u c hu hc (by omega)

/-! ## 8. The spec's product, window by window -/

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem product_win {N W AccW : Nat} (A B : BitVec (N * N * W)) {u c : Nat} (hu : u < N) (hc : c < N) :
    (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)).extract ((u * N + c) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (ps N W A B u N c)) := by
  have hd : (u * N + c) / N = u := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]
  have hm : (u * N + c) % N = c := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hr : u * N + c < N * N := by have := Lib.rowMajor_window_le (w := 1) hu hc; simp at this; omega
  have hl : (u * N + c) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le (w := AccW) hu hc
  rw [product_eq, LVec.extract_ofBitVec _ hl]
  simp (disch := omega) only [extractLsb'_packBV, hd, hm]
  rw [ps_dot]

/-- A vector of `n` windows of `w` bits is equal to another one window by window. -/
theorem eq_of_windows {c d : LVec} {n w : Nat} (hc : c.width = n * w) (hd : d.width = n * w)
    (h : ∀ k, k < n → c.extract (k * w) w = d.extract (k * w) w) : c = d := by
  apply LVec.ext_getD (by rw [hc, hd])
  intro i hi
  rw [hc] at hi
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hk : i / w < n := by rw [Nat.div_lt_iff_lt_mul hw]; exact hi
  have hb := congrArg (fun z : LVec => z.bits[i % w]?.getD .lx) (h (i / w) hk)
  simp only [LVec.getD_extract, if_pos (Nat.mod_lt i hw)] at hb
  have e : i / w * w + i % w = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i w
  rwa [e] at hb

theorem C_product {N W AccW : Nat} (A B : BitVec (N * N * W)) {c : LVec} (hc : c.width = N * N * AccW)
    (h : ∀ u j, u < N → j < N → c.extract ((u * N + j) * AccW) AccW = .ofBitVec (BitVec.ofInt AccW (ps N W A B u N j))) :
    c = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  refine eq_of_windows (n := N * N) (w := AccW) hc (by simp) fun k hk => ?_
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hu : k / N < N := by rw [Nat.div_lt_iff_lt_mul hN]; exact hk
  have hj : k % N < N := Nat.mod_lt k hN
  have e : k = k / N * N + k % N := by rw [Nat.mul_comm]; exact (Nat.div_add_mod k N).symm
  rw [e, h _ _ hu hj, product_win A B hu hj]

/-! ## 9. The control outside a busy step: reset, start, idle -/

theorem ctrl_reset {N W AccW : Nat} {g : Regs} (hwd : Wd N W AccW g) (s a b : LVec) :
    (g.fold (gmQ N W AccW (knownBit true) s a b g)).dn = knownBit false ∧
    (g.fold (gmQ N W AccW (knownBit true) s a b g)).bz = knownBit false ∧
    (g.fold (gmQ N W AccW (knownBit true) s a b g)).ip = knownBit false ∧
    ∃ n : BitVec 32, (g.fold (gmQ N W AccW (knownBit true) s a b g)).st = .ofBitVec n := by
  refine ⟨?_, ?_, ?_, ⟨BitVec.ofNat 32 0, ?_⟩⟩
  · show nbaFold "done" _ g.dn = _
    rw [@fold_ctrl N W AccW (knownBit true) s a b g "done" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    simp (disch := decide) only [ctrlQ, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil']
    rw [wr1 hwd.dn (by rfl), l0_kb]
  · show nbaFold "busy" _ g.bz = _
    rw [@fold_ctrl N W AccW (knownBit true) s a b g "busy" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    simp (disch := decide) only [ctrlQ, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil']
    rw [wr1 hwd.bz (by rfl), l0_kb]
  · show nbaFold "in_prop" _ g.ip = _
    rw [@fold_ctrl N W AccW (knownBit true) s a b g "in_prop" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    simp (disch := decide) only [ctrlQ, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil']
    rw [wr1 hwd.ip (by rfl), l0_kb]
  · show nbaFold "step" _ g.st = _
    rw [@fold_ctrl N W AccW (knownBit true) s a b g "step" (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    simp (disch := decide) only [ctrlQ, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil']
    rw [rep0, wr_whole (by simp [hwd.st])]

theorem ctrl_start {N W AccW : Nat} {g : Regs} (hwd : Wd N W AccW g) (hip : g.ip = knownBit false)
    (A B : BitVec (N * N * W)) :
    nbaFold "done" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.dn = knownBit false ∧
    nbaFold "busy" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.bz = knownBit true ∧
    nbaFold "step" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.st =
      .ofBitVec (BitVec.ofNat 32 0) ∧
    nbaFold "in_prop" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.ip = knownBit true ∧
    nbaFold "a_rows" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.ar = .ofBitVec A ∧
    nbaFold "w_rows" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g) g.wr = .ofBitVec B := by
  simp (disch := decide) only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, nbaFold_cons_self,
    nbaFold_cons_ne, nbaFold_nil']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wr1 hwd.dn (by rfl), l0_kb]
  · rw [wr1 hwd.bz (by rfl), l1_kb]
  · rw [rep0, wr_whole (by simp [hwd.st])]
  · rw [hip, kb_not_w, Bool.not_false]
  · exact wr_whole (by simp [hwd.ar])
  · exact wr_whole (by simp [hwd.wr])

/-- **The start**: from `in_prop` = 0, a start cycle reaches the invariant at `t = 0` (every array claim is
vacuous there: the every-power-up argument). -/
theorem inv_start {N W AccW : Nat} (hN : 1 ≤ N) (A B : BitVec (N * N * W)) {g : Regs} (hwd : Wd N W AccW g)
    (hip : g.ip = knownBit false) :
    Inv N W AccW A B 0 (g.fold (gmQ N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g)) := by
  obtain ⟨hcd, hcb, hcs, hci, hca, hcw⟩ := ctrl_start hwd hip A B
  refine ⟨hwd.fold _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show nbaFold "done" _ g.dn = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "done" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcd,
      decide_eq_false (show ¬ (0 = 4 * N + 1) by omega)]
  · show nbaFold "busy" _ g.bz = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "busy" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcb,
      decide_eq_true (show 0 ≤ 4 * N by omega)]
  · show nbaFold "step" _ g.st = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "step" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcs]
  · show nbaFold "in_prop" _ g.ip = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "in_prop" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hci,
      decide_eq_true (show 0 < N by omega)]
  · show nbaFold "a_rows" _ g.ar = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "a_rows" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hca]
    simp
  · show nbaFold "w_rows" _ g.wr = _
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) g "w_rows" (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcw]
    simp
  all_goals intros; omega

theorem outQ_idle {N AccW : Nat} {g : Regs} (hbz : g.bz = knownBit false) {n : BitVec 32}
    (hst : g.st = .ofBitVec n) (u c : Nat) : outQ N AccW g u c = [] := by
  unfold outQ
  rw [hbz, hst, LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, LVec.add_ofBitVec, LVec.eqLogical_ofBitVec,
    LVec.ofLogic_ofBool, and_kb, condTrue_knownBit, Bool.false_and]
  try rfl

theorem outs_idle {N AccW : Nat} {g : Regs} (hbz : g.bz = knownBit false) {n : BitVec 32}
    (hst : g.st = .ofBitVec n) : Outs N AccW g = [] := by
  simp [Outs, List.flatMap_eq_nil_iff, outQ_idle hbz hst]

/-- An idle cycle (`busy` = 0, no `rst`, no `start`) keeps `done`, `busy`, `in_prop`, `step` and `C`. -/
theorem idle_step {N W AccW : Nat} {g : Regs} (hbz : g.bz = knownBit false) {n : BitVec 32}
    (hst : g.st = .ofBitVec n) (a b : LVec) :
    (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)).dn = g.dn ∧
    (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)).bz = g.bz ∧
    (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)).ip = g.ip ∧
    (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)).st = g.st ∧
    (g.fold (gmQ N W AccW (knownBit false) (knownBit false) a b g)).c = g.c := by
  have hq : ctrlQ N W (knownBit false) (knownBit false) a b g = [] := by
    simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, hbz]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show nbaFold "done" _ g.dn = g.dn
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "done" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hq, nbaFold_nil']
  · show nbaFold "busy" _ g.bz = g.bz
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "busy" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hq, nbaFold_nil']
  · show nbaFold "in_prop" _ g.ip = g.ip
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "in_prop" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hq, nbaFold_nil']
  · show nbaFold "step" _ g.st = g.st
    rw [@fold_ctrl N W AccW (knownBit false) (knownBit false) a b g "step" (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hq, nbaFold_nil']
  · show nbaFold "C" _ g.c = g.c
    rw [fold_C, outs_idle hbz hst, nbaFold_nil']

/-- The end of a run: the invariant at `t = 4N + 1` shows `done` = 1 and the product. -/
theorem fin_of_inv {N W AccW : Nat} {A B : BitVec (N * N * W)} {t : Nat} {g : Regs} (ht : t = 4 * N + 1)
    (h : Inv N W AccW A B t g) :
    Wd N W AccW g ∧ g.dn = knownBit true ∧ g.bz = knownBit false ∧ g.ip = knownBit false ∧
      (∃ n : BitVec 32, g.st = .ofBitVec n) ∧ g.c = .ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  subst ht
  refine ⟨h.wd, ?_, ?_, ?_, ⟨_, h.st⟩, C_product A B h.wd.c fun u j hu hj => h.cc u j hu hj (by omega)⟩
  · rw [h.dn, decide_eq_true rfl]
  · rw [h.bz, decide_eq_false (show ¬ (4 * N + 1 ≤ 4 * N) by omega)]
  · rw [h.ip, decide_eq_false (show ¬ (4 * N + 1 < N) by omega)]

/-! ## 10. Shape, the phase model and the rules -/

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop := ∃ ck r s a b g, st = GS ck r s a b g ∧ Wd N W AccW g

/-- One cycle from a state of the shape, evaluated (`gm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b g, prev = GS ck r s a b g ∧ Wd N W AccW g ∧
    st = gmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) g

theorem gmNext_eq (N W AccW : Nat) (ck r s a b : LVec) (g : Regs) :
    gmNext N W AccW ck r s a b g = GS (nbaFold "clk" (gmQ N W AccW r s a b g) ck)
      (nbaFold "rst" (gmQ N W AccW r s a b g) r) (nbaFold "start" (gmQ N W AccW r s a b g) s)
      (nbaFold "A" (gmQ N W AccW r s a b g) a) (nbaFold "B" (gmQ N W AccW r s a b g) b)
      (g.fold (gmQ N W AccW r s a b g)) := commit_GS _ _ _ _ _ _ _

theorem gmNext_I {N W AccW : Nat} (ck r s a b : LVec) {g : Regs} (hw : Wd N W AccW g) :
    I N W AccW (gmNext N W AccW ck r s a b g) :=
  ⟨_, _, _, _, _, _, gmNext_eq N W AccW ck r s a b g, hw.fold _⟩

theorem GS_inj {ck r s a b ck' r' s' a' b' : LVec} {g g' : Regs} (h : GS ck r s a b g = GS ck' r' s' a' b' g') :
    g = g' := by
  cases g; cases g'
  simp only [GS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  simp only [Regs.mk.injEq]
  first | exact h.2.2.2.2.2 | simp_all

theorem gm_noq (N W AccW : Nat) : (gmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  refine List.any_eq_false.mpr fun p hp => ?_
  have hm : p ∈ ctrlP N W :: waveP N :: genPs N W AccW := by simpa [gmD] using hp
  rcases all_cases hm with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;>
    simp [ctrlP, waveP, propP, rowP, colP, pipeP, tileP, outP, nb, Process2.hasQualifiedCase,
      Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem gm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [gm_sem_eq N W AccW hN hW hA hr]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W),
    ⟨.xVec 1, .xVec (N * N * AccW), .xVec 1, .xVec 1, .xVec 32, .xVec (N * N * W), .xVec (N * N * W),
      .xVec (tri N * W), .xVec (tri N * W), .xVec (tri N * AccW), .xVec (2 * N), .xVec 1, .xVec (2 * N - 1),
      .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * AccW), .xVec (N * N * W), .xVec (N * N * W)⟩, ?_,
    ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp⟩⟩
  simp [initState2, gmD, gmDecls, GS]

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- `Ready`: idle with nothing shown. -/
def ReadyS (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b g, st = GS ck r s a b g ∧ Wd N W AccW g ∧ g.dn = knownBit false ∧ g.bz = knownBit false ∧
    g.ip = knownBit false ∧ ∃ n : BitVec 32, g.st = .ofBitVec n

/-- The state `t` busy cycles after a start with operands `A`, `B`: the invariant. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b g, st = GS ck r s a b g ∧ Inv N W AccW A B t g

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b g, st = GS ck r s a b g ∧ Wd N W AccW g ∧ g.dn = knownBit true ∧ g.bz = knownBit false ∧
    g.ip = knownBit false ∧ (∃ n : BitVec 32, g.st = .ofBitVec n) ∧ g.c = .ofBitVec (Tasks.Matmul.product N W AccW A B)

/-- **The phase model** at `(N, W, AccW)`, latency `4N + 1`. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31)
    (hNA : N * N * AccW < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (4 * N + 1) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := gm_init N W AccW hN hW hA hNW
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, g, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, g, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (gm_cycle N W AccW hN hW hA hNW σ e ck r s a b g k 50 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, g, -, hw, rfl⟩
    exact gmNext_I _ _ _ _ _ hw
  Ready := ReadyS N W AccW
  Busy x m st := ∃ t, t + m + 1 = 4 * N + 1 ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, g, rfl, -, hdn, -⟩
    simp [BitIs, Tasks.Matmul.task, GS, SvState.lookup, hdn]
  busy_done := by
    rintro x m st ⟨t, ht, ck, r, s, a, b, g, rfl, hi⟩
    have hdn : g.dn = knownBit false := by rw [hi.dn, decide_eq_false (show ¬ (t = 4 * N + 1) by omega)]
    simp [BitIs, Tasks.Matmul.task, GS, SvState.lookup, hdn]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, g, rfl, -, hdn, -, -, -, hc⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, GS, SvState.lookup, hdn, hc]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, g, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r, gmNext_eq]
    obtain ⟨h1, h2, h3, h4⟩ := ctrl_reset hw (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
    exact ⟨_, _, _, _, _, _, rfl, hw.fold _, h1, h2, h3, h4⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, g, hp, hw, rfl⟩ hprev hr hs hx
    have hip : g.ip = knownBit false := by
      rcases hprev with ⟨ck', r', s', a', b', g', hb, -, -, -, h3, -⟩ | ⟨y, ck', r', s', a', b', g', hb, -, -, -, h3, -⟩
      · rw [GS_inj (hp.symm.trans hb)]; exact h3
      · rw [GS_inj (hp.symm.trans hb)]; exact h3
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb, gmNext_eq]
    exact .inr ⟨4 * N, by omega, 0, by omega, _, _, _, _, _, _, rfl, inv_start hN x.1 x.2.1 hw hip⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, g, rfl, -, rfl⟩ ⟨t, ht, ck', r', s', a', b', g', hb, hinv⟩ hr hs -
    obtain rfl := GS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, gmNext_eq]
    have hi := inv_step hN hW hA hNW hNA x.1 x.2.1 (show t ≤ 4 * N by omega) hinv (appIn e "A" a) (appIn e "B" b)
    by_cases hf : t + 1 = 4 * N + 1
    · exact .inl ⟨_, _, _, _, _, _, rfl, fin_of_inv hf hi⟩
    · exact .inr ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, rfl, hi⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, g, rfl, -, rfl⟩ ⟨ck', r', s', a', b', g', hb, hw, hdn, hbz, hip, n, hst⟩ hr hs
    obtain rfl := GS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, gmNext_eq]
    obtain ⟨h1, h2, h3, h4, -⟩ := idle_step (N := N) (W := W) (AccW := AccW) hbz hst (appIn e "A" a) (appIn e "B" b)
    exact ⟨_, _, _, _, _, _, rfl, hw.fold _, h1.trans hdn, h2.trans hbz, h3.trans hip, n, h4.trans hst⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, g, rfl, -, rfl⟩ ⟨ck', r', s', a', b', g', hb, hw, hdn, hbz, hip, ⟨n, hst⟩, hc⟩
      hr hs
    obtain rfl := GS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, gmNext_eq]
    obtain ⟨h1, h2, h3, h4, h5⟩ := idle_step (N := N) (W := W) (AccW := AccW) hbz hst (appIn e "A" a) (appIn e "B" b)
    exact ⟨_, _, _, _, _, _, rfl, hw.fold _, h1.trans hdn, h2.trans hbz, h3.trans hip, ⟨n, h4.trans hst⟩, h5.trans hc⟩

theorem gm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [gm_sem_eq N W AccW hN hW hA hr]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "busy", "in_prop", "step", "a_rows", "w_rows", "sk_a",
      "sk_d", "sk_o", "wv", "pb", "wp", "m_a", "m_d", "m_b", "c1", "c2"] : List String).Nodup
    decide⟩

theorem gm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [gm_sem_eq N W AccW hN hW hA hr]
  refine ⟨by simp [Tasks.Matmul.task, gmD, gmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ ctrlP N W :: waveP N :: genPs N W AccW := by simpa [gmD] using hp
  rcases all_cases hm with rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ | ⟨r, c, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, waveP, propP, rowP, colP, pipeP, tileP, outP, macE, sext, nb, c32, edgeClock,
      asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-- **Rule 1.** -/
theorem gm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [gm_sem_eq N W AccW hN hW hA hr]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (gm_profile N W AccW hN)))
    (by simp [gmD, gmDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem gm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [gm_sem_eq N W AccW hN hW hA hr] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨bz, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨ip, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨st', r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨ar, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨wr', r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨ska, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨skd, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨sko, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain ⟨wv, r16, rfl, w16, -, h16⟩ := powerUp_cons.mp h15
  obtain ⟨pb, r17, rfl, w17, -, h17⟩ := powerUp_cons.mp h16
  obtain ⟨wp, r18, rfl, w18, -, h18⟩ := powerUp_cons.mp h17
  obtain ⟨ma, r19, rfl, w19, -, h19⟩ := powerUp_cons.mp h18
  obtain ⟨md, r20, rfl, w20, -, h20⟩ := powerUp_cons.mp h19
  obtain ⟨mb, r21, rfl, w21, -, h21⟩ := powerUp_cons.mp h20
  obtain ⟨c1, r22, rfl, w22, -, h22⟩ := powerUp_cons.mp h21
  obtain ⟨c2, r23, rfl, w23, -, h23⟩ := powerUp_cons.mp h22
  obtain rfl := powerUp_nil.mp h23
  exact ⟨ck, r, s, a, b, ⟨dn, c, bz, ip, st', ar, wr', ska, skd, sko, wv, pb, wp, ma, md, mb, c1, c2⟩, rfl,
    ⟨w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23⟩⟩

/-- **Termination from every power-up**. -/
theorem gm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (gm_powerUp N W AccW hN hW hA hr) (fun σ => ⟨50, ?_⟩)
    (by rw [gm_sem_eq N W AccW hN hW hA hr]; exact gm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, g, rfl, hw⟩
  exact ⟨_, _, gm_cycle N W AccW hN hW hA hr σ e ck r s a b g kk 50 (Nat.le_refl _), gmNext_I _ _ _ _ _ hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem tri_le_of_le {i j : Nat} (h : i ≤ j) : tri i ≤ tri j := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · have := tri_mono h; omega
  · exact Nat.le_refl _

theorem lane_fit {r N W : Nat} (hr : r < N) : tri r * W + (r + 1) * W ≤ tri N * W := by
  have := Nat.mul_le_mul_right W (tri_le hr); rwa [Nat.add_assoc, Nat.add_mul] at this

theorem tap_fit {r N W : Nat} (hr : r < N) : (tri r + r) * W + W ≤ tri N * W := by
  have := Nat.mul_le_mul_right W (tri_le hr); rwa [Nat.add_mul, Nat.one_mul] at this

theorem olane_fit {c N AccW : Nat} (hc : c < N) :
    tri (N - 1 - c) * AccW + (N - c) * AccW ≤ tri N * AccW := by
  have e : tri (N - 1 - c) + (N - c) = tri (N - c) := by rw [show N - c = N - 1 - c + 1 by omega, tri_succ]
  have := Nat.mul_le_mul_right AccW (tri_le_of_le (show N - c ≤ N by omega))
  rwa [← e, Nat.add_mul] at this

theorem row_fit {r N W : Nat} (hr : r < N) : r * N * W + N * W ≤ N * N * W := by
  have := Nat.mul_le_mul_right W (Nat.mul_le_mul_right N (show r + 1 ≤ N by omega))
  rwa [Nat.add_mul, Nat.add_mul, Nat.one_mul] at this

theorem ent_fit {r N W : Nat} (hN : 1 ≤ N) (hr : r < N) : r * W + W ≤ N * N * W := by
  have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hr; simpa using this

theorem ctrl_xsafe (N W AccW : Nat) : xsProc (gmD N W AccW) (ctrlP N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ctrlP, nb, c32, gmD, gmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem wave_xsafe {N W AccW : Nat} (hN : 1 ≤ N) : xsProc (gmD N W AccW) (waveP N) = true := by
  have h1 : 1 ≤ 2 * N := by omega
  have h2 : 0 < N := by omega
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, waveP, nb, c32, gmD,
    gmDecls, LVec.ofInt, h1, h2, Nat.pos_iff_ne_zero.mp h2, if_pos]

theorem prop_xsafe {N W AccW k : Nat} (hk : k < 2 * N - 2) : xsProc (gmD N W AccW) (propP k) = true := by
  have h1 : k + 1 + 1 ≤ 2 * N := by omega
  have h2 : k + 1 ≤ 2 * N - 1 := by omega
  have h3 : k + 2 ≤ 2 * N := by omega
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, propP, gmD, gmDecls,
    h1, h2, h3, if_pos]

theorem row_xsafe {N W AccW r : Nat} (hN : 1 ≤ N) (hr : r < N) : xsProc (gmD N W AccW) (rowP N W r) = true := by
  have h1 := lane_fit (W := W) hr
  have h2 := ent_fit (W := W) hN hr
  have h3 := row_fit (W := W) hr
  have h4 := tap_fit (W := W) hr
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, rowP, c32, gmD, gmDecls,
    LVec.ofInt, h1, h2, h3, h4, if_pos]

theorem mac_win {N W AccW r c : Nat} (hW : 1 ≤ W) (hr : r < N) (hc : c < N) :
    (r * N + c) * AccW + AccW ≤ N * N * AccW ∧ (r * N + c) * W + W ≤ N * N * W ∧
      (r * N + c) * W + W - 1 + 1 ≤ N * N * W := by
  have h1 := Lib.rowMajor_window_le (w := AccW) hr hc
  have h2 := Lib.rowMajor_window_le (w := W) hr hc
  exact ⟨h1, h2, by omega⟩

theorem col_xsafe {N W AccW c : Nat} (hW : 1 ≤ W) (hc : c < N) :
    xsProc (gmD N W AccW) (colP N W AccW c) = true := by
  have hN : 1 ≤ N := by omega
  have h1 := lane_fit (W := W) hc
  have h2 := tap_fit (W := W) hc
  have h3 := olane_fit (AccW := AccW) hc
  obtain ⟨h4, h5, h6⟩ := mac_win (AccW := AccW) hW (show N - 1 < N by omega) hc
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, colP, macE,
    sext, c32, gmD, gmDecls, LVec.ofInt, LVec.replicate_l0, h1, h2, h3, h4, h5, h6, if_pos]

theorem pipe_xsafe {N W AccW r c : Nat} (hW : 1 ≤ W) (hr : r + 1 < N) (hc : c < N) :
    xsProc (gmD N W AccW) (pipeP N W AccW r c) = true := by
  obtain ⟨h4, h5, h6⟩ := mac_win (AccW := AccW) hW (show r < N by omega) hc
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pipeP, macE,
    sext, gmD, gmDecls, h4, h5, h6, if_pos]

theorem tile_xsafe {N W AccW r c : Nat} (hW : 1 ≤ W) (hr : r < N) (hc : c < N) :
    xsProc (gmD N W AccW) (tileP N W r c) = true := by
  obtain ⟨-, h5, -⟩ := mac_win (AccW := AccW) hW hr hc
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, tileP,
    gmD, gmDecls, h5, if_pos]

theorem out_xsafe {N W AccW u c : Nat} (hc : c < N) : xsProc (gmD N W AccW) (outP N AccW u c) = true := by
  have h1 : (tri (N - 1 - c) + (N - 1 - c)) * AccW + AccW ≤ tri N * AccW := tap_fit (show N - 1 - c < N by omega)
  simp (disch := first | (simp [*]; done) | omega) [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, outP, c32, gmD, gmDecls,
    LVec.ofInt, h1, if_pos]

/-- **Rule 3.** -/
theorem gm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    XSafe (design.sem N W AccW) := by
  rw [gm_sem_eq N W AccW hN hW hA hr]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ ctrlP N W :: waveP N :: genPs N W AccW := by simpa [gmD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ctrl_xsafe N W AccW
  rcases List.mem_cons.mp hm with rfl | hm
  · exact wave_xsafe hN
  simp only [genPs, List.mem_append] at hm
  rcases hm with hm | hm | hm | hm | hm | hm
  · obtain ⟨k, hk, rfl⟩ := mem_propPs hm; exact prop_xsafe hk
  · obtain ⟨k, hk, rfl⟩ := mem_rowPs hm; exact row_xsafe hN hk
  · obtain ⟨k, hk, rfl⟩ := mem_colPs hm; exact col_xsafe hW hk
  · obtain ⟨r, c, hr', hc, rfl⟩ := mem_pipePs hm; exact pipe_xsafe hW hr' hc
  · obtain ⟨r, c, hr', hc, rfl⟩ := mem_tilePs hm; exact tile_xsafe hW hr' hc
  · obtain ⟨u, c, hu, hc, rfl⟩ := mem_outPs hm; exact out_xsafe hc

/-- **The design satisfies the matmul statement (txtask-v2) at latency `4N + 1`** (`17` at the scoring point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, hNA⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (gm_interface N W AccW hN hW hA hNW)
    (gm_disciplined N W AccW hN hW hA hNW) (gm_terminatesPU N W AccW hN hW hA hNW)
    (by first | omega | (unfold lat; omega) | (simp only [lat]; omega))
    (model N W AccW hN hW hA hNW hNA) (gm_powerUp N W AccW hN hW hA hNW) (gm_moore N W AccW hN hW hA hNW)
    (gm_xsafe N W AccW hN hW hA hNW)

end Submission
