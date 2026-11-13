-- svgolf-latency: 8
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
# A weight-stationary array for task `matmul`: `N²` PEs, the weights held, the partial sums down the columns

`solution.sv`: on `start` the weights `B` are latched into `w` (PE `(k, j)` holds `B[k][j]`), input delay line `k`
gets `A[0][k]` at its entry `k`, and `ash` holds the rows of `A` still to come. In each busy cycle every line shifts
one entry towards its head while `A[t+1][k]` enters at entry `k`, so the head of line `k` is `A[t-k][k]` (row `k` of
the array sees column `k` of `A` `k` cycles late); every PE of array row `k` multiplies that head by its weight and
adds the partial sum of the PE above; and from `t = N` on the bottom row of PEs, output row `t - N`, enters `C`'s
last row while the collected rows move one row on. `done` shows `2N` snapshots after the start's (`lat = 2N`).

Proved at every in-range `(N, W, AccW)`, following the reference proof's steps:
1. **Agreement** (`mm_sem_eq`): the loaded family is the hand-built `mmD` (one control process, the delay lines,
   the two PE families, the two collection families).
2. **The clock step** (`mm_cycle`): one cycle is the commit `mmNext` of the process queues, register by register
   (`nbaFold`).
3. **The invariant** (`BusyAt`): the control and `ash` exactly; the delay lines, the partial sums and `C` window by
   window (`DlOk`, `PsOk`, `COk`); a vector all of whose windows are known is the packed vector (`eq_ofBitVec_of_win`).
4. **The protocol** (`model`) and txtask-v2's rules 1 to 3, then `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The latency: `done` shows `2N` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := 2 * N

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- `e` (of width `we`) widened to the context width `n`: the loader writes no `resize` when the widths agree. -/
def rz (n we : Nat) (e : Expr2) : Expr2 := if n = we then e else .resize n e

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- The control: `busy`, `done`, the step counter `t`, the weight load and the row feeder `ash`. -/
def ctrlP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "w") (.ident "B"),
        .nbaAssign (.ident "ash") (.binary (.shr false) (.ident "A") (.binary .mul (c32 N) (c32 W)))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "t") (.binary .add (.ident "t") (c32 1)),
          .nbaAssign (.ident "ash") (.binary (.shr false) (.ident "ash") (.binary .mul (c32 N) (c32 W))),
          .ifStmt (.binary .eq (.ident "t") (.binary .sub (.binary .add (c32 N) (c32 N)) (c32 1)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- Delay line `k`: loaded with `A[0][k]` at entry `k` on start, shifted with `ash`'s entry `k` OR-ed in while busy. -/
def lineP (N W k : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "dl" (k * N * W) (N * W))
      (.binary (.shl false) (rz (N * W) W (.slice (.ident "A") (k * W) W)) (.binary .mul (c32 k) (c32 W))))
    (some (.ifStmt (.ident "busy")
      (.nbaAssign (.slice "dl" (k * N * W) (N * W))
        (.binary .or (.binary (.shr false) (.slice (.ident "dl") (k * N * W) (N * W)) (c32 W))
          (.binary (.shl false) (rz (N * W) W (.slice (.ident "ash") (k * W) W)) (.binary .mul (c32 k) (c32 W)))))
      none)))

/-- PE `(0, j)`: the head of line `0` times the weight. -/
def topP (W AccW j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.nbaAssign (.slice "ps" (j * AccW) AccW)
      (.resize AccW (.binary .mul (sext "dl" AccW 0 W) (sext "w" AccW (j * W) W))))
    none)

/-- PE `(k+1, j)`: the partial sum of PE `(k, j)` plus the head of line `k+1` times the weight. -/
def rowP (N W AccW k j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.nbaAssign (.slice "ps" (((k + 1) * N + j) * AccW) AccW)
      (.resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "ps") ((k * N + j) * AccW) AccW))
        (.binary .mul (sext "dl" AccW ((k + 1) * N * W) W) (sext "w" AccW (((k + 1) * N + j) * W) W)))))
    none)

/-- `C[i][j]` takes `C[i+1][j]` in a collecting cycle. -/
def crowP (N AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.ifStmt (.binary .ge (.ident "t") (c32 N))
      (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.slice (.ident "C") (((i + 1) * N + j) * AccW) AccW))
      none)
    none)

/-- `C[N-1][j]` takes the bottom PE's partial sum in a collecting cycle. -/
def coutP (N AccW j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.ifStmt (.binary .ge (.ident "t") (c32 N))
      (.nbaAssign (.slice "C" (((N - 1) * N + j) * AccW) AccW) (.slice (.ident "ps") (((N - 1) * N + j) * AccW) AccW))
      none)
    none)

/-- The declarations, `A`/`B`/`w`/`ash`/`dl` at `wa` bits and `C`/`ps` at `wc`. -/
def mmDecls (wa wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "t", width := 32 },
   { name := "busy", width := 1 }, { name := "w", width := wa }, { name := "ash", width := wa },
   { name := "dl", width := wa }, { name := "ps", width := wc }]

def linePs (N W : Nat) : List Process2 := (List.range N).map (lineP N W)
def topPs (N W AccW : Nat) : List Process2 := (List.range N).map (topP W AccW)
def rowPs (N W AccW : Nat) : List Process2 := (List.range (N - 1)).flatMap fun k => (List.range N).map (rowP N W AccW k)
def crowPs (N AccW : Nat) : List Process2 := (List.range (N - 1)).flatMap fun i => (List.range N).map (crowP N AccW i)
def coutPs (N AccW : Nat) : List Process2 := (List.range N).map (coutP N AccW)

/-- The generated processes, in source order. -/
def genPs (N W AccW : Nat) : List Process2 :=
  linePs N W ++ topPs N W AccW ++ rowPs N W AccW ++ crowPs N AccW ++ coutPs N AccW

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * N * AccW)).toArray
  processes := (ctrlP N W :: genPs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("N", N), ("W", W), ("AccW", AccW)], pwidths := [("N", 32), ("W", 32), ("AccW", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "w", "ash", "dl", "ps"].map (·, 1)

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
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [ctrlP N W] := by
  sv2_inst_simp [instStmt2, instStmts2, design.pdesign, mmEnv, mmScope, mmDecls, mmElems, ctrlP,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2]
  try and_intros
  all_goals first | rfl | decide

/-- The generate templates. -/
def lineT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def topT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.process p], _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def rowT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _, _] => p
  | _ => .alwaysFF "" (.block [])
def crowT : PProcess := match design.pdesign.generates with
  | [_, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])
def coutT : PProcess := match design.pdesign.generates with
  | [_, _, _, _, .genFor _ _ _ _ _ _ [.process p]] => p
  | _ => .alwaysFF "" (.block [])

/-- The `sv2_inst_simp` set of the templates (with the window facts in scope). -/
macro "t_simp" : tactic => `(tactic| sv2_inst_simp [lineT, topT, rowT, crowT, coutT, evalSized, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, design.pdesign,
  mmEnv, mmScope, mmDecls, mmElems, lineP, topP, rowP, crowP, coutP, sext, rz,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2, instDivOperand2, fitDivOperand2, *])

/-- The facts every instantiation needs. -/
theorem inst_facts {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    ((0 : Int) < W ∧ (0 : Int) < AccW ∧ (1 : Int) ≤ N * N * W ∧ (1 : Int) ≤ N * N * AccW) ∧
    ((N : Int) * N * W - 1).natAbs + 1 = N * N * W ∧ ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW ∧
    (PartMode.up == PartMode.range) = false ∧ 0 < AccW ∧ 0 < W ∧ ¬ W = 0 ∧ ¬ AccW + W < AccW ∧ ¬ AccW + W ≤ AccW ∧
    0 < N * W ∧ (0 : Int) < N * W := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have pNW := Nat.mul_pos hN hW
  refine ⟨⟨by omega, by omega, by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega,
    by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega⟩, ?_, ?_, rfl, by omega, by omega, by omega, by omega,
    by omega, pNW, by rw [← Int.natCast_mul]; omega⟩
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  · rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pA

/-- Window facts of `x[lo +: w]` inside `c` bits, for the instantiation `simp`. -/
theorem win {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (x : Int) (hx : (lo : Int) = x) :
    0 ≤ x ∧ x.toNat = lo ∧ x + w - 1 < c ∧ 1 ≤ x + w ∧ (x + w).toNat = lo + w :=
  Lib.window_bounds_of_natCast x c h hw hx (by simp)

theorem line_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N) :
    instProcess2 ((mmE N W AccW).bindVal "k" k) mmElems lineT = lineP N W k := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := inst_facts hN hW hA
  have e1 : k * N * W + N * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (show k + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have e2 : k * W + W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show k + 1 ≤ N * N by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hd := win e1 h13 ((k : Int) * N * W) (by simp)
  have ha := win e2 hW ((k : Int) * W) (by simp)
  push_cast at hd ha
  have hNW : ((N : Int) * W).toNat = N * W := by rw [← Int.natCast_mul]; rfl
  have hmx : max (N * W) W = N * W := Nat.max_eq_left (Nat.le_mul_of_pos_left W (by omega))
  t_simp
  try and_intros
  all_goals first | rfl | decide

/-- Row-major window facts: entry `(i, j)` of an `M × N` matrix of `w`-bit entries. -/
theorem rm_le {M N w i j : Nat} (hi : i < M) (hj : j < N) : (i * N + j) * w + w ≤ M * N * w :=
  Lib.rowMajor_window_le hi hj

theorem top_inst (N W AccW j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hj : j < N) :
    instProcess2 ((mmE N W AccW).bindVal "j" j) mmElems topT = topP W AccW j := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := inst_facts hN hW hA
  have hc := win (by simpa using rm_le (M := N) (N := N) (w := AccW) (i := 0) (by omega) hj) hA ((j : Int) * AccW)
    (by simp)
  have hNNW : W ≤ N * N * W := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ : (W : Int) - 1 < N * N * W ∧ max ((W : Int) - 1) 0 = W - 1 ∧
      min ((W : Int) - 1) 0 = 0 ∧ ((W : Int) - 1 - 0 + 1).toNat = W ∧ ((W : Int) - 1).toNat = W - 1 ∧
      (0 : Int) ≤ W - 1 ∧ (1 : Int) ≤ W := by
    refine ⟨?_, by omega, by omega, by omega, by omega, by omega, by omega⟩
    have : ((W : Nat) : Int) ≤ ((N * N * W : Nat) : Int) := by exact_mod_cast hNNW
    push_cast at this; omega
  have hb := win (by simpa using rm_le (M := N) (N := N) (w := W) (i := 0) (by omega) hj) hW ((j : Int) * W)
    (by simp)
  push_cast at hc hb
  t_simp
  -- `simp` cannot use `instExpr2`'s `resize` equation (measured in the reference): unfold it by hand.
  repeat (unfold instExpr2; t_simp)

theorem row_inst (N W AccW k j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N - 1) (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "k" k).bindVal "j" j) mmElems rowT = rowP N W AccW k j := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := inst_facts hN hW hA
  have hc1 := win (rm_le (M := N) (N := N) (w := AccW) (i := k + 1) (by omega) hj) hA ((((k : Int) + 1) * N + j) * AccW)
    (by simp)
  have hc0 := win (rm_le (M := N) (N := N) (w := AccW) (i := k) (by omega) hj) hA (((k : Int) * N + j) * AccW)
    (by simp)
  have hd := win (by simpa using rm_le (M := N) (N := N) (w := W) (i := k + 1) (j := 0) (by omega) (by omega)) hW
    (((k : Int) + 1) * N * W) (by simp)
  have hb := win (rm_le (M := N) (N := N) (w := W) (i := k + 1) (by omega) hj) hW ((((k : Int) + 1) * N + j) * W)
    (by simp)
  push_cast at hc1 hc0 hd hb
  t_simp
  repeat (unfold instExpr2; t_simp)

theorem crow_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N - 1) (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems crowT = crowP N AccW i j := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := inst_facts hN hW hA
  have hc1 := win (rm_le (M := N) (N := N) (w := AccW) (i := i + 1) (by omega) hj) hA ((((i : Int) + 1) * N + j) * AccW)
    (by simp)
  have hc0 := win (rm_le (M := N) (N := N) (w := AccW) (i := i) (by omega) hj) hA (((i : Int) * N + j) * AccW)
    (by simp)
  push_cast at hc1 hc0
  t_simp
  try and_intros
  all_goals first | rfl | decide

theorem cout_inst (N W AccW j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hj : j < N) :
    instProcess2 ((mmE N W AccW).bindVal "j" j) mmElems coutT = coutP N AccW j := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := inst_facts hN hW hA
  have hc := win (rm_le (M := N) (N := N) (w := AccW) (i := N - 1) (by omega) hj) hA ((((N : Int) - 1) * N + j) * AccW)
    (by push_cast [Int.ofNat_sub hN]; rfl)
  push_cast at hc
  t_simp
  try and_intros
  all_goals first | rfl | decide

/-- `for (g = 0; g < N; g++) body`. -/
def genN (lbl g : String) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) (.paramRef "N" none))
    (.unary .inc (.genvarRef g)) (some rc) body

/-- `for (g = 0; g < N - 1; g++) body`. -/
def genM (lbl g : String) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)))
    (.unary .inc (.genvarRef g)) (some rc) body

theorem mm_gens_src : design.pdesign.generates =
    [genN "g_line" "k" 4 ([lineT].map .process), genN "g_top" "j" 4 ([topT].map .process),
     genM "g_row" "k" 3 [genN "g_col" "j" 4 ([rowT].map .process)],
     genM "g_crow" "i" 3 [genN "g_ccol" "j" 4 ([crowT].map .process)],
     genN "g_cout" "j" 4 ([coutT].map .process)] := rfl

/-- A loop `g < N` over one template, from its instantiation lemma. -/
theorem gen_one {env : IEnv} {lbl g : String} {rc N F : Nat} {p : PProcess} {f : Nat → Process2}
    (hNv : ∀ v : Int, (env.bindVal g v).vals.lookup "N" = some (N : Int)) (hF : N < F)
    (hf : ∀ v, v < N → instProcess2 (env.bindVal g v) mmElems p = f v) :
    (genN lbl g rc ([p].map .process)).expand2 env mmElems F = .ok ((List.range N).map f) := by
  rw [genN, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun i => isInt_paramRef_of (hNv i)) (fun i => evalInt_paramRef_of (hNv i)) (by simpa using hF)]
  simp only [intRange_zero, Int.sub_zero, Int.toNat_natCast, List.flatMap_map, List.map_cons, List.map_nil,
    Gen2.flatMap_singleton_map]
  congr 1
  exact List.map_congr_left fun v hv => hf v (List.mem_range.mp hv)

/-- A loop `g < N - 1` over a loop `j < N` over one template. -/
theorem gen_two {env : IEnv} {lbl g lbl' : String} {rc rc' N F : Nat} {p : PProcess} {f : Nat → Nat → Process2}
    (hN : 1 ≤ N) (hNv : ∀ v : Int, (env.bindVal g v).vals.lookup "N" = some (N : Int))
    (hNv' : ∀ v w : Int, ((env.bindVal g v).bindVal "j" w).vals.lookup "N" = some (N : Int)) (hF : N < F)
    (hf : ∀ v w, v < N - 1 → w < N → instProcess2 ((env.bindVal g v).bindVal "j" w) mmElems p = f v w) :
    (genM lbl g rc [genN lbl' "j" rc' ([p].map .process)]).expand2 env mmElems F =
      .ok ((List.range (N - 1)).flatMap fun v => (List.range N).map (f v)) := by
  rw [genM, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int) - 1)
    (f := fun v => (List.range N).map (fun w : Nat => instProcess2 ((env.bindVal g v).bindVal "j" (w : Int)) mmElems p))
    (evalInt_int 0) (fun i => isInt_binary_of rfl (isInt_paramRef_of (hNv i)) rfl)
    (fun i => evalInt_sub_of (isInt_paramRef_of (hNv i)) rfl (evalInt_paramRef_of (hNv i)) rfl) (by omega)]
  · have ht : ((N : Int) - 1 - 0).toNat = N - 1 := by omega
    simp only [ht, intRange_zero, List.flatMap_map]
    congr 1
    exact CombView.flatMap_congr' fun v hv => List.map_congr_left fun w hw =>
      hf v w (List.mem_range.mp hv) (List.mem_range.mp hw)
  · intro v _ _
    apply expandList2_singleton_ok
    exact gen_one (hNv' v) hF (fun w _ => rfl)

theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have h1 := gen_one (env := mmE N W AccW) (lbl := "g_line") (g := "k") (rc := 4) (fun _ => rfl) hF
    (fun k hk => line_inst N W AccW k hN hW hA hk)
  have h2 := gen_one (env := mmE N W AccW) (lbl := "g_top") (g := "j") (rc := 4) (fun _ => rfl) hF
    (fun j hj => top_inst N W AccW j hN hW hA hj)
  have h3 := gen_two (env := mmE N W AccW) (lbl := "g_row") (g := "k") (lbl' := "g_col") (rc := 3) (rc' := 4) hN
    (fun _ => rfl) (fun _ _ => rfl) hF (fun k j hk hj => row_inst N W AccW k j hN hW hA hk hj)
  have h4 := gen_two (env := mmE N W AccW) (lbl := "g_crow") (g := "i") (lbl' := "g_ccol") (rc := 3) (rc' := 4) hN
    (fun _ => rfl) (fun _ _ => rfl) hF (fun i j hi hj => crow_inst N W AccW i j hN hW hA hi hj)
  have h5 := gen_one (env := mmE N W AccW) (lbl := "g_cout") (g := "j") (rc := 4) (fun _ => rfl) hF
    (fun j hj => cout_inst N W AccW j hN hW hA hj)
  rw [mm_gens_src, genPs, List.append_assoc, List.append_assoc, List.append_assoc]
  exact expandList2_cons_ok h1 (expandList2_cons_ok h2 (expandList2_cons_ok h3 (expandList2_cons_ok h4
    (expandList2_singleton_ok h5))))

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (mmDecls (N * N * W) (N * N * AccW)) mmElems
        (genPs N W AccW)) := by
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
      ctrlP N W :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_ctrl]
  simp [design.pdesign]

/-! ### Disjoint windows -/

/-- The kinds of process, with their indices in range. -/
theorem genPs_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ genPs N W AccW) :
    (∃ k, k < N ∧ p = lineP N W k) ∨ (∃ j, j < N ∧ p = topP W AccW j) ∨
      (∃ k j, k < N - 1 ∧ j < N ∧ p = rowP N W AccW k j) ∨ (∃ i j, i < N - 1 ∧ j < N ∧ p = crowP N AccW i j) ∨
      (∃ j, j < N ∧ p = coutP N AccW j) := by
  simp only [genPs, linePs, topPs, rowPs, crowPs, coutPs, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_range] at hp
  rcases hp with (((⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨k, hk, j, hj, rfl⟩) | ⟨i, hi, j, hj, rfl⟩) | ⟨j, hj, rfl⟩
  · exact .inl ⟨k, hk, rfl⟩
  · exact .inr (.inl ⟨j, hj, rfl⟩)
  · exact .inr (.inr (.inl ⟨k, j, hk, hj, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨i, j, hi, hj, rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨j, hj, rfl⟩)))

/-- The windows each process drives. -/
theorem wins_line (N W k : Nat) : (lineP N W k).procWins = [("dl", some (k * N * W, N * W)), ("dl", some (k * N * W, N * W))] := rfl
theorem wins_top (W AccW j : Nat) : (topP W AccW j).procWins = [("ps", some (j * AccW, AccW))] := rfl
theorem wins_row (N W AccW k j : Nat) :
    (rowP N W AccW k j).procWins = [("ps", some (((k + 1) * N + j) * AccW, AccW))] := rfl
theorem wins_crow (N AccW i j : Nat) : (crowP N AccW i j).procWins = [("C", some ((i * N + j) * AccW, AccW))] := rfl
theorem wins_cout (N AccW j : Nat) : (coutP N AccW j).procWins = [("C", some (((N - 1) * N + j) * AccW, AccW))] := rfl
theorem wins_ctrl (N W : Nat) : (ctrlP N W).procWins =
    [("busy", none), ("done", none), ("t", none), ("busy", none), ("done", none), ("t", none), ("w", none),
     ("ash", none), ("t", none), ("ash", none), ("busy", none), ("done", none)] := rfl

/-- Two windows of one signal at row-major units `r < r'` of width `E` are disjoint. -/
theorem unit_disj {n : String} {E r r' : Nat} (h : r < r') :
    DrvWin.overlaps (n, some (r * E, E)) (n, some (r' * E, E)) = false := by
  have := rowMajor_le (K := E) h
  simp [DrvWin.overlaps]; omega

theorem unit_disj' {n : String} {E r r' : Nat} (h : r < r') :
    DrvWin.overlaps (n, some (r' * E, E)) (n, some (r * E, E)) = false := by
  have := rowMajor_le (K := E) h
  simp [DrvWin.overlaps]; omega

theorem name_disj {n n' : String} (h : n ≠ n') (a b : Option (Nat × Nat)) :
    DrvWin.overlaps (n, a) (n', b) = false := by
  simp [DrvWin.overlaps, h]

/-- The relation `driversOk` and the profile need. -/
abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

theorem disj_of_names {p q : Process2} {n n' : String} (h : n ≠ n') (hp : ∀ a ∈ p.procWins, a.1 = n)
    (hq : ∀ b ∈ q.procWins, b.1 = n') : Disj p q := by
  intro a ha b hb
  obtain ⟨x, u⟩ := a; obtain ⟨y, v⟩ := b
  have h1 := hp _ ha; have h2 := hq _ hb
  simp only at h1 h2; subst h1; subst h2
  exact name_disj h u v

theorem names_line (N W k : Nat) : ∀ a ∈ (lineP N W k).procWins, a.1 = "dl" := by simp [wins_line]
theorem names_top (W AccW j : Nat) : ∀ a ∈ (topP W AccW j).procWins, a.1 = "ps" := by simp [wins_top]
theorem names_row (N W AccW k j : Nat) : ∀ a ∈ (rowP N W AccW k j).procWins, a.1 = "ps" := by simp [wins_row]
theorem names_crow (N AccW i j : Nat) : ∀ a ∈ (crowP N AccW i j).procWins, a.1 = "C" := by simp [wins_crow]
theorem names_cout (N AccW j : Nat) : ∀ a ∈ (coutP N AccW j).procWins, a.1 = "C" := by simp [wins_cout]

/-- Unit index of a process of one of the two `ps` families, and of the two `C` families. -/
theorem disj_unit {p q : Process2} {n : String} {E r r' : Nat} (h : r ≠ r')
    (hp : p.procWins = [(n, some (r * E, E))]) (hq : q.procWins = [(n, some (r' * E, E))]) : Disj p q := by
  intro a ha b hb
  rw [hp] at ha; rw [hq] at hb
  simp only [List.mem_singleton] at ha hb; subst ha; subst hb
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact unit_disj h
  · exact unit_disj' h

theorem rm_lt {N i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : i < i') : i * N + j < i' * N + j' := by
  have := rowMajor_le (K := N) h; omega

theorem rm_ne {N i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : i ≠ i' ∨ j ≠ j') : i * N + j ≠ i' * N + j' := by
  intro he
  rcases Nat.lt_or_ge i i' with hi | hi
  · exact absurd he (Nat.ne_of_lt (rm_lt hj hj' hi))
  · rcases Nat.lt_or_ge i' i with hi' | hi'
    · exact absurd he.symm (Nat.ne_of_lt (rm_lt hj' hj hi'))
    · have : i = i' := by omega
      subst this; rcases h with h | h
      · exact h rfl
      · omega

theorem disj_lists {l1 l2 : List Process2} {n n' : String} (h : n ≠ n')
    (h1 : ∀ p ∈ l1, ∀ a ∈ p.procWins, a.1 = n) (h2 : ∀ q ∈ l2, ∀ b ∈ q.procWins, b.1 = n') :
    ∀ p ∈ l1, ∀ q ∈ l2, Disj p q := fun p hp q hq => disj_of_names h (h1 p hp) (h2 q hq)

theorem L_names (N W : Nat) : ∀ p ∈ linePs N W, ∀ a ∈ p.procWins, a.1 = "dl" := by
  intro p hp; simp only [linePs, List.mem_map] at hp; obtain ⟨k, -, rfl⟩ := hp; exact names_line N W k
theorem T_names (N W AccW : Nat) : ∀ p ∈ topPs N W AccW, ∀ a ∈ p.procWins, a.1 = "ps" := by
  intro p hp; simp only [topPs, List.mem_map] at hp; obtain ⟨k, -, rfl⟩ := hp; exact names_top W AccW k
theorem R_names (N W AccW : Nat) : ∀ p ∈ rowPs N W AccW, ∀ a ∈ p.procWins, a.1 = "ps" := by
  intro p hp; simp only [rowPs, List.mem_flatMap, List.mem_map] at hp; obtain ⟨k, -, j, -, rfl⟩ := hp
  exact names_row N W AccW k j
theorem CR_names (N AccW : Nat) : ∀ p ∈ crowPs N AccW, ∀ a ∈ p.procWins, a.1 = "C" := by
  intro p hp; simp only [crowPs, List.mem_flatMap, List.mem_map] at hp; obtain ⟨k, -, j, -, rfl⟩ := hp
  exact names_crow N AccW k j
theorem CO_names (N AccW : Nat) : ∀ p ∈ coutPs N AccW, ∀ a ∈ p.procWins, a.1 = "C" := by
  intro p hp; simp only [coutPs, List.mem_map] at hp; obtain ⟨k, -, rfl⟩ := hp; exact names_cout N AccW k

theorem line_disj {N W k k' : Nat} (h : k < k') : Disj (lineP N W k) (lineP N W k') := by
  intro a ha b hb
  rw [wins_line] at ha hb
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at ha hb
  subst ha; subst hb
  have := rowMajor_le (K := N * W) h
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at this
  simp [DrvWin.overlaps]; omega

/-- A map over `range n` of processes pairwise disjoint in index order. -/
theorem pw_map {n : Nat} {f : Nat → Process2} (h : ∀ a b, a < b → b < n → Disj (f a) (f b)) :
    ((List.range n).map f).Pairwise Disj :=
  List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ hb hab => h _ _ hab (List.mem_range.mp hb))

/-- A double family `(k, j) ↦ f k j`, `k < m`, `j < n`, pairwise disjoint in row-major order. -/
theorem pw_flat {m n : Nat} {f : Nat → Nat → Process2}
    (h : ∀ k j k' j', k < m → k' < m → j < n → j' < n → k * n + j < k' * n + j' → Disj (f k j) (f k' j')) :
    ((List.range m).flatMap fun k => (List.range n).map (f k)).Pairwise Disj := by
  refine pairwise_flatMap_range (fun k hk => pw_map fun a b hab hb => h k a k b hk hk (by omega) hb (by omega)) ?_
  intro k k' hkk' hk' a ha b hb
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨j, hj, rfl⟩ := ha; obtain ⟨j', hj', rfl⟩ := hb
  exact h k j k' j' (by omega) hk' hj hj' (rm_lt hj hj' hkk')

theorem mm_gen_pairwise (N W AccW : Nat) : (genPs N W AccW).Pairwise Disj := by
  simp only [genPs, List.pairwise_append, List.mem_append]
  refine ⟨⟨⟨⟨pw_map fun a b hab _ => line_disj hab, pw_map fun a b hab _ =>
      disj_unit (Nat.ne_of_lt hab) (wins_top W AccW a) (wins_top W AccW b),
      disj_lists (by decide) (L_names N W) (T_names N W AccW)⟩,
    pw_flat fun k j k' j' _ _ _ _ hlt => disj_unit (by simp only [Nat.add_mul, Nat.one_mul]; omega)
      (wins_row N W AccW k j) (wins_row N W AccW k' j'), ?_⟩,
    pw_flat fun i j i' j' _ _ _ _ hlt => disj_unit (Nat.ne_of_lt hlt) (wins_crow N AccW i j) (wins_crow N AccW i' j'),
      ?_⟩, pw_map fun a b hab _ => disj_unit (by omega) (wins_cout N AccW a) (wins_cout N AccW b), ?_⟩
  · rintro p (hp | hp) q hq
    · exact disj_lists (by decide) (L_names N W) (R_names N W AccW) p hp q hq
    · simp only [topPs, List.mem_map, List.mem_range] at hp
      simp only [rowPs, List.mem_flatMap, List.mem_map, List.mem_range] at hq
      obtain ⟨j, hj, rfl⟩ := hp; obtain ⟨k, hk, j', hj', rfl⟩ := hq
      exact disj_unit (by have := Nat.le_mul_of_pos_left N (show 0 < k + 1 by omega); omega)
        (wins_top W AccW j) (wins_row N W AccW k j')
  · rintro p ((hp | hp) | hp) q hq
    · exact disj_lists (by decide) (L_names N W) (CR_names N AccW) p hp q hq
    · exact disj_lists (by decide) (T_names N W AccW) (CR_names N AccW) p hp q hq
    · exact disj_lists (by decide) (R_names N W AccW) (CR_names N AccW) p hp q hq
  · rintro p (((hp | hp) | hp) | hp) q hq
    · exact disj_lists (by decide) (L_names N W) (CO_names N AccW) p hp q hq
    · exact disj_lists (by decide) (T_names N W AccW) (CO_names N AccW) p hp q hq
    · exact disj_lists (by decide) (R_names N W AccW) (CO_names N AccW) p hp q hq
    · simp only [crowPs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
      simp only [coutPs, List.mem_map, List.mem_range] at hq
      obtain ⟨i, hi, j, hj, rfl⟩ := hp; obtain ⟨j', hj', rfl⟩ := hq
      exact disj_unit (rm_ne hj hj' (.inl (by omega))) (wins_crow N AccW i j) (wins_cout N AccW j')

/-- The control and the generated processes drive pairwise disjoint windows. -/
theorem mm_pairwise (N W AccW : Nat) : (ctrlP N W :: genPs N W AccW).Pairwise Disj := by
  refine List.Pairwise.cons (fun p hp => ?_) (mm_gen_pairwise N W AccW)
  intro a ha b hb
  rw [wins_ctrl] at ha
  rcases genPs_mem hp with ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, j, hk, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;>
    simp only [wins_line, wins_top, wins_row, wins_crow, wins_cout, List.mem_cons,
      List.not_mem_nil, or_false, or_self] at hb <;>
    subst hb <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mm_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ ctrlP N W :: genPs N W AccW) :
    p = ctrlP N W ∨ (∃ k, k < N ∧ p = lineP N W k) ∨ (∃ j, j < N ∧ p = topP W AccW j) ∨
      (∃ k j, k < N - 1 ∧ j < N ∧ p = rowP N W AccW k j) ∨ (∃ i j, i < N - 1 ∧ j < N ∧ p = crowP N AccW i j) ∨
      (∃ j, j < N ∧ p = coutP N AccW j) := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact .inl rfl
  · exact .inr (genPs_mem hp)

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (ctrlP N W :: genPs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW)
  · intro p hp
    rcases mm_mem hp with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
      exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap]
    rintro n ⟨p, hp, hn⟩
    rcases mm_mem hp with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
      revert n <;>
      simp [Process2.procWrites, wins_ctrl, wins_line, wins_top, wins_row, wins_crow, wins_cout] <;> decide

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
  refine ⟨List.all_eq_true.mpr fun p hp => ?_, ffDisjB_of_pairwise (by simp only [mmD, List.toList_toArray]; exact mm_pairwise N W AccW)⟩
  have hm : p ∈ ctrlP N W :: genPs N W AccW := by simpa [mmD] using hp
  rcases mm_mem hm with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
    simp [mmD, ctrlP, lineP, topP, rowP, crowP, coutP, nb, Stmt2.nbaOnly, Stmt2.optNbaOnly,
      Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
      Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins, mmDecls]

/-- The 13 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c t bz w ash dl ps : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("t", t), ("busy", bz),
   ("w", w), ("ash", ash), ("dl", dl), ("ps", ps)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c t bz w ash dl ps : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c t bz w ash dl ps) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c t bz w ash dl ps := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- `N·W` at 32 bits. -/
abbrev nwV (N W : Nat) : LVec := (LVec.ofInt 32 N).mul (LVec.ofInt 32 W)

/-- The last-step test `t == N + N - 1`. -/
abbrev lastB (N : Nat) (t : LVec) : Bool :=
  (LVec.ofLogic (t.eqLogical (((LVec.ofInt 32 N).add (LVec.ofInt 32 N)).sub (LVec.ofInt 32 1)))).condTrue

/-- The collection test `t >= N`. -/
abbrev geB (N : Nat) (t : LVec) : Bool := (LVec.ofLogic (t.ge (LVec.ofInt 32 N))).condTrue

/-- `rz`, evaluated. -/
def rzV (n we : Nat) (v : LVec) : LVec := if n = we then v else v.resizeU n

/-- The control's updates, from the pre-edge values. -/
def ctrlQ (N W : Nat) (r s a b dn t bz w ash : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0),
    wr "w" w b, wr "ash" ash (a.shr (nwV N W))]
  else if bz.condTrue then
    if lastB N t then
      [wr "t" t (t.add (LVec.ofInt 32 1)), wr "ash" ash (ash.shr (nwV N W)), wr "busy" bz ⟨#[.l0]⟩,
        wr "done" dn ⟨#[.l1]⟩]
    else [wr "t" t (t.add (LVec.ofInt 32 1)), wr "ash" ash (ash.shr (nwV N W))]
  else []

/-- The new value of delay line `k` on a start. -/
def lineGo (N W k : Nat) (a : LVec) : LVec :=
  (rzV (N * W) W (a.extract (k * W) W)).shl ((LVec.ofInt 32 k).mul (LVec.ofInt 32 W))

/-- The new value of delay line `k` in a busy cycle. -/
def lineStep (N W k : Nat) (ash dl : LVec) : LVec :=
  ((dl.extract (k * N * W) (N * W)).shr (LVec.ofInt 32 W)).or
    ((rzV (N * W) W (ash.extract (k * W) W)).shl ((LVec.ofInt 32 k).mul (LVec.ofInt 32 W)))

def lineQ (N W : Nat) (s a bz ash dl : LVec) (k : Nat) : NbaQueue2 :=
  if s.condTrue then [("dl", k * N * W, (lineGo N W k a).resizeU (N * W))]
  else if bz.condTrue then [("dl", k * N * W, (lineStep N W k ash dl).resizeU (N * W))]
  else []

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- The new partial sum of PE `(0, j)`, evaluated. -/
def topV (W AccW j : Nat) (w dl : LVec) : LVec := ((sxv dl AccW 0 W).mul (sxv w AccW (j * W) W)).resizeU AccW

/-- The new partial sum of PE `(k+1, j)`, evaluated. -/
def rowV (N W AccW k j : Nat) (w dl ps : LVec) : LVec :=
  (((ps.extract ((k * N + j) * AccW) AccW).resizeU (AccW + W)).add
    ((sxv dl AccW ((k + 1) * N * W) W).mul (sxv w AccW (((k + 1) * N + j) * W) W))).resizeU AccW

def topQ (W AccW : Nat) (bz w dl : LVec) (j : Nat) : NbaQueue2 :=
  if bz.condTrue then [("ps", j * AccW, (topV W AccW j w dl).resizeU AccW)] else []

def rowQ (N W AccW : Nat) (bz w dl ps : LVec) (k j : Nat) : NbaQueue2 :=
  if bz.condTrue then [("ps", ((k + 1) * N + j) * AccW, (rowV N W AccW k j w dl ps).resizeU AccW)] else []

def crowQ (N AccW : Nat) (t bz c : LVec) (i j : Nat) : NbaQueue2 :=
  if bz.condTrue then
    if geB N t then [("C", (i * N + j) * AccW, (c.extract (((i + 1) * N + j) * AccW) AccW).resizeU AccW)] else []
  else []

def coutQ (N AccW : Nat) (t bz ps : LVec) (j : Nat) : NbaQueue2 :=
  if bz.condTrue then
    if geB N t then [("C", ((N - 1) * N + j) * AccW, (ps.extract (((N - 1) * N + j) * AccW) AccW).resizeU AccW)]
    else []
  else []

section run
variable (F : Nat) (hF : 40 ≤ F) (ck r s a b dn c t bz w ash dl ps : LVec)
include hF

theorem ctrl_run (N W : Nat) : runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (ctrlP N W) =
    .ok (MS ck r s a b dn c t bz w ash dl ps, ctrlQ N W r s a b dn t bz w ash) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : lastB N t = true <;>
    simp [ctrlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem line_run (N W k : Nat) : runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (lineP N W k) =
    .ok (MS ck r s a b dn c t bz w ash dl ps, lineQ N W s a bz ash dl k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold lineQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;> by_cases hz : N * W = W <;>
    simp [lineP, lineGo, lineStep, rz, rzV, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h2, h3, hz]

theorem top_run (W AccW j : Nat) : runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (topP W AccW j) =
    .ok (MS ck r s a b dn c t bz w ash dl ps, topQ W AccW bz w dl j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold topQ
  by_cases h3 : bz.condTrue = true <;>
    simp [topP, topV, sext, sxv, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h3]

theorem row_run (N W AccW k j : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (rowP N W AccW k j) =
      .ok (MS ck r s a b dn c t bz w ash dl ps, rowQ N W AccW bz w dl ps k j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold rowQ
  by_cases h3 : bz.condTrue = true <;>
    simp [rowP, rowV, sext, sxv, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h3]

theorem crow_run (N AccW i j : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (crowP N AccW i j) =
      .ok (MS ck r s a b dn c t bz w ash dl ps, crowQ N AccW t bz c i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold crowQ
  by_cases h3 : bz.condTrue = true <;> by_cases h4 : geB N t = true <;>
    simp [crowP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h3, h4]

theorem cout_run (N AccW j : Nat) :
    runEdgeProcess2 F (MS ck r s a b dn c t bz w ash dl ps) [] (coutP N AccW j) =
      .ok (MS ck r s a b dn c t bz w ash dl ps, coutQ N AccW t bz ps j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold coutQ
  by_cases h3 : bz.condTrue = true <;> by_cases h4 : geB N t = true <;>
    simp [coutP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h3, h4]

end run

/-- The cycle's updates, in process order. -/
def Q (N W AccW : Nat) (r s a b dn c t bz w ash dl ps : LVec) : NbaQueue2 :=
  ctrlQ N W r s a b dn t bz w ash ++
    ((List.range N).flatMap (lineQ N W s a bz ash dl) ++ (List.range N).flatMap (topQ W AccW bz w dl) ++
      ((List.range (N - 1)).flatMap fun k => (List.range N).flatMap (rowQ N W AccW bz w dl ps k)) ++
      ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap (crowQ N AccW t bz c i)) ++
      (List.range N).flatMap (coutQ N AccW t bz ps))

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c t bz w ash dl ps : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c t bz w ash dl ps) (Q N W AccW r s a b dn c t bz w ash dl ps)

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus
entry, any state of the design's shape, every fuel from 40). -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c t bz w ash dl ps : LVec) (kk F : Nat) (hF : 40 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c t bz w ash dl ps) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c t bz w ash dl ps, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ ctrlP N W :: genPs N W AccW := by simpa [mmD] using hp
    rcases mm_mem hm with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;> rfl
  rw [mm_sem_eq N W AccW hN hW hA, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD, genPs, linePs, topPs, rowPs, crowPs, coutPs, List.toList_toArray, List.flatMap_cons,
      List.flatMap_append, ctrl_run F hF, List.flatMap_map, line_run F hF, top_run F hF, row_run F hF,
      crow_run F hF, cout_run F hF, List.flatMap_assoc, mmNext, Q, List.append_assoc]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ ctrlP N W :: genPs N W AccW := List.mem_of_getElem? (by simpa [mmD] using hp)
    rcases mm_mem hm with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, line_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ N W k⟩
    · exact ⟨_, top_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ W AccW j⟩
    · exact ⟨_, row_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW k j⟩
    · exact ⟨_, crow_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW i j⟩
    · exact ⟨_, cout_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW j⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The commit, register by register -/

section commit
variable {ck r s a b dn c t bz w ash dl ps : LVec} {lo : Nat} {v : LVec}
theorem nb_dn : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c t bz w ash dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) t bz w ash dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_t : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("t", lo, v) =
    MS ck r s a b dn c (t.insertAt lo v) bz w ash dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bz : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("busy", lo, v) =
    MS ck r s a b dn c t (bz.insertAt lo v) w ash dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_w : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("w", lo, v) =
    MS ck r s a b dn c t bz (w.insertAt lo v) ash dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ash : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("ash", lo, v) =
    MS ck r s a b dn c t bz w (ash.insertAt lo v) dl ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_dl : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("dl", lo, v) =
    MS ck r s a b dn c t bz w ash (dl.insertAt lo v) ps := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ps : nbaStep (MS ck r s a b dn c t bz w ash dl ps) ("ps", lo, v) =
    MS ck r s a b dn c t bz w ash dl (ps.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- The eight registers. -/
abbrev RegName (n : String) : Prop :=
  n = "done" ∨ n = "C" ∨ n = "t" ∨ n = "busy" ∨ n = "w" ∨ n = "ash" ∨ n = "dl" ∨ n = "ps"

/-- Committing a queue of writes to the eight registers. -/
theorem commit_MS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c t bz w ash dl ps : LVec),
    (∀ u ∈ q, RegName u.1) →
    commitNba2 (MS ck r s a b dn c t bz w ash dl ps) q =
      MS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "t" q t) (nbaFold "busy" q bz)
        (nbaFold "w" q w) (nbaFold "ash" q ash) (nbaFold "dl" q dl) (nbaFold "ps" q ps)
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, t, bz, w, ash, dl, ps, h => by
    have hq := @commit_MS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;>
      subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_t, nb_bz, nb_w, nb_ash, nb_dl, nb_ps,
        hq _ _ _ _ _ _ _ _ h', nbaFold]

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 := h u List.mem_cons_self
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

section names
variable {N W AccW : Nat} {r s a b dn c t bz w ash dl ps : LVec}

theorem ctrlQ_names : ∀ u ∈ ctrlQ N W r s a b dn t bz w ash,
    u.1 = "busy" ∨ u.1 = "done" ∨ u.1 = "t" ∨ u.1 = "w" ∨ u.1 = "ash" := by
  intro u hu; unfold ctrlQ at hu; (repeat' split at hu) <;> simp at hu <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
theorem lineQ_names (k : Nat) : ∀ u ∈ lineQ N W s a bz ash dl k, u.1 = "dl" := by
  intro u hu; unfold lineQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem topQ_names (j : Nat) : ∀ u ∈ topQ W AccW bz w dl j, u.1 = "ps" := by
  intro u hu; unfold topQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem rowQ_names (k j : Nat) : ∀ u ∈ rowQ N W AccW bz w dl ps k j, u.1 = "ps" := by
  intro u hu; unfold rowQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem crowQ_names (i j : Nat) : ∀ u ∈ crowQ N AccW t bz c i j, u.1 = "C" := by
  intro u hu; unfold crowQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem coutQ_names (j : Nat) : ∀ u ∈ coutQ N AccW t bz ps j, u.1 = "C" := by
  intro u hu; unfold coutQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl

def linesQ (N W : Nat) (s a bz ash dl : LVec) : NbaQueue2 := (List.range N).flatMap (lineQ N W s a bz ash dl)
def psQ (N W AccW : Nat) (bz w dl ps : LVec) : NbaQueue2 :=
  (List.range N).flatMap (topQ W AccW bz w dl) ++ (List.range (N - 1)).flatMap fun k => (List.range N).flatMap (rowQ N W AccW bz w dl ps k)
def cQ (N AccW : Nat) (t bz c ps : LVec) : NbaQueue2 :=
  ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap (crowQ N AccW t bz c i)) ++
    (List.range N).flatMap (coutQ N AccW t bz ps)

theorem linesQ_names : ∀ u ∈ linesQ N W s a bz ash dl, u.1 = "dl" := by
  intro u hu; simp only [linesQ, List.mem_flatMap] at hu; obtain ⟨k, -, hu⟩ := hu; exact lineQ_names k u hu
theorem psQ_names : ∀ u ∈ psQ N W AccW bz w dl ps, u.1 = "ps" := by
  intro u hu; simp only [psQ, List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨j, -, hu⟩ | ⟨k, -, j, -, hu⟩
  · exact topQ_names j u hu
  · exact rowQ_names k j u hu
theorem cQ_names : ∀ u ∈ cQ N AccW t bz c ps, u.1 = "C" := by
  intro u hu; simp only [cQ, List.mem_append, List.mem_flatMap] at hu
  rcases hu with ⟨i, -, j, -, hu⟩ | ⟨j, -, hu⟩
  · exact crowQ_names i j u hu
  · exact coutQ_names j u hu

theorem Q_eq : Q N W AccW r s a b dn c t bz w ash dl ps =
    ctrlQ N W r s a b dn t bz w ash ++ (linesQ N W s a bz ash dl ++ psQ N W AccW bz w dl ps ++ cQ N AccW t bz c ps) := by
  simp only [Q, linesQ, psQ, cQ, List.append_assoc]

/-- **The commit of a cycle, register by register.** -/
theorem next_eq (ck : LVec) : mmNext N W AccW ck r s a b dn c t bz w ash dl ps =
    MS ck r s a b (nbaFold "done" (ctrlQ N W r s a b dn t bz w ash) dn) (nbaFold "C" (cQ N AccW t bz c ps) c)
      (nbaFold "t" (ctrlQ N W r s a b dn t bz w ash) t) (nbaFold "busy" (ctrlQ N W r s a b dn t bz w ash) bz)
      (nbaFold "w" (ctrlQ N W r s a b dn t bz w ash) w) (nbaFold "ash" (ctrlQ N W r s a b dn t bz w ash) ash)
      (nbaFold "dl" (linesQ N W s a bz ash dl) dl) (nbaFold "ps" (psQ N W AccW bz w dl ps) ps) := by
  have hc : ∀ {n : String}, n ≠ "busy" → n ≠ "done" → n ≠ "t" → n ≠ "w" → n ≠ "ash" → ∀ x,
      nbaFold n (ctrlQ N W r s a b dn t bz w ash) x = x := fun h1 h2 h3 h4 h5 x =>
    nbaFold_of_forall_ne (fun u hu h => by
      rcases ctrlQ_names u hu with h' | h' | h' | h' | h' <;> rw [h'] at h <;> subst h <;> contradiction) x
  have hl : ∀ {n : String}, n ≠ "dl" → ∀ x, nbaFold n (linesQ N W s a bz ash dl) x = x := fun h x =>
    nbaFold_of_forall_ne (fun u hu h' => h (h'.symm.trans (linesQ_names u hu))) x
  have hp : ∀ {n : String}, n ≠ "ps" → ∀ x, nbaFold n (psQ N W AccW bz w dl ps) x = x := fun h x =>
    nbaFold_of_forall_ne (fun u hu h' => h (h'.symm.trans (psQ_names u hu))) x
  have hC : ∀ {n : String}, n ≠ "C" → ∀ x, nbaFold n (cQ N AccW t bz c ps) x = x := fun h x =>
    nbaFold_of_forall_ne (fun u hu h' => h (h'.symm.trans (cQ_names u hu))) x
  rw [mmNext, Q_eq, commit_MS]
  · simp (disch := decide) only [nbaFold_append, hl, hp, hC, hc]
  · intro u hu
    simp only [List.mem_append] at hu
    rcases hu with hu | ((hu | hu) | hu)
    · rcases ctrlQ_names u hu with h | h | h | h | h <;> rw [h] <;> simp [RegName]
    · rw [linesQ_names u hu]; simp [RegName]
    · rw [psQ_names u hu]; simp [RegName]
    · rw [cQ_names u hu]; simp [RegName]

end names

/-! ## 4. Windows: a family of window writes, and a vector known window by window -/

/-- `insertEntries` reads only the written values below `n`. -/
theorem ie_congr {E : Nat} {g g' : Nat → LVec} (c : LVec) : ∀ n, (∀ r, r < n → g r = g' r) →
    LVec.insertEntries E g n c = LVec.insertEntries E g' n c
  | 0, _ => rfl
  | n + 1, h => by
    rw [LVec.insertEntries_succ, LVec.insertEntries_succ, ie_congr c n (fun r hr => h r (by omega)), h n (by omega)]

/-- **Window `r` of a written family** is the value written there. -/
theorem extract_ie {E : Nat} {g : Nat → LVec} (hg : ∀ k, (g k).width = E) (c : LVec) :
    ∀ n, n * E ≤ c.width → ∀ r, r < n → (LVec.insertEntries E g n c).extract (r * E) E = g r
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, hn, r, hr => by
    have hn' : n * E + E ≤ c.width := by simpa [Nat.succ_mul] using hn
    rw [LVec.insertEntries_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := rowMajor_le (K := E) hr
      rw [LVec.extract_insertAt_of_disjoint (.inl this)]
      exact extract_ie hg c n (by omega) r hr
    · exact LVec.extract_insertAt_self (hg r) (by rw [LVec.width_insertEntries]; exact hn')

/-- Writing every window's own content back changes nothing. -/
theorem ie_self (E : Nat) (v : LVec) : ∀ n, LVec.insertEntries E (fun r => v.extract (r * E) E) n v = v
  | 0 => rfl
  | n + 1 => by rw [LVec.insertEntries_succ, ie_self E v n, LVec.insertAt_extract_self]

/-- **A vector known window by window** is the packed vector of its windows. -/
theorem eq_ofBitVec_of_win {E n : Nat} {v : LVec} {f : Nat → BitVec E} (hw : v.width = n * E)
    (h : ∀ r, r < n → v.extract (r * E) E = LVec.ofBitVec (f r)) : v = LVec.ofBitVec (packBV E n f) := by
  rw [← LVec.insertEntries_ofBitVec f v hw, ← ie_congr v n h, ie_self]

/-- Committing a queue that writes window `r` of `n` with `g r`, in order, is `insertEntries`. -/
theorem nbaFold_map (n : String) (E : Nat) (g : Nat → LVec) (m : Nat) (x : LVec) :
    nbaFold n ((List.range m).map fun r => (n, r * E, g r)) x = LVec.insertEntries E g m x := by
  simp only [nbaFold, List.foldl_map, if_pos rfl]; rfl

/-- A single loop of one-window writes, as a `map`. -/
theorem rmap1 {M : Nat} {q : Nat → NbaQueue2} {f : Nat → String × Nat × LVec} (h : ∀ j, j < M → q j = [f j]) :
    (List.range M).flatMap q = (List.range M).map f := by
  rw [CombView.flatMap_congr' fun j hj => h j (List.mem_range.mp hj)]
  induction (List.range M) with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, ih]; rfl

/-- A double loop of one-window writes in row-major order, as one `map` (the reference's `rowMajor_map`). -/
theorem rmap2 {R M : Nat} {q : Nat → Nat → NbaQueue2} (f : Nat → String × Nat × LVec)
    (h : ∀ i j, i < R → j < M → q i j = [f (i * M + j)]) :
    ((List.range R).flatMap fun i => (List.range M).flatMap (q i)) = (List.range (R * M)).map f := by
  suffices ∀ K, K ≤ R → ((List.range K).flatMap fun i => (List.range M).flatMap (q i)) =
      (List.range (K * M)).map f from this R (Nat.le_refl _)
  intro K; induction K with
  | zero => intro _; simp
  | succ K ih =>
    intro hK
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add, List.map_append,
      List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [rmap1 (f := fun j => f (K * M + j)) fun j hj => h K j (by omega) hj]
    rfl

/-- Two consecutive index ranges, mapped. -/
theorem map_range_append (f : Nat → String × Nat × LVec) (a b : Nat) :
    (List.range a).map f ++ (List.range b).map (fun r => f (a + r)) = (List.range (a + b)).map f := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-! ### `BitVec` facts -/

theorem extractLsb'_or {n : Nat} (x y : BitVec n) (lo w : Nat) :
    (x ||| y).extractLsb' lo w = x.extractLsb' lo w ||| y.extractLsb' lo w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem extractLsb'_of_ge {n : Nat} (x : BitVec n) {lo w : Nat} (h : n ≤ lo) : x.extractLsb' lo w = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', hi, BitVec.getLsbD_of_ge x (lo + i) (by omega)]

theorem extractLsb'_self {W : Nat} (x : BitVec W) : x.extractLsb' 0 W = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem bor0 {n : Nat} (x : BitVec n) : x ||| (0 : BitVec n) = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

theorem b0or {n : Nat} (x : BitVec n) : (0 : BitVec n) ||| x = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

/-- Entry `e` of a shift down by one entry. -/
theorem shr_entry {W N : Nat} (f : Nat → BitVec W) {e : Nat} :
    ((packBV W N f) >>> W).extractLsb' (e * W) W = if e + 1 < N then f (e + 1) else 0 := by
  rw [Lib.extractLsb'_ushiftRight, show W + e * W = (e + 1) * W by rw [Nat.succ_mul, Nat.add_comm]]
  split
  · exact extractLsb'_packBV f ‹_›
  · exact extractLsb'_of_ge _ (Nat.mul_le_mul_right W (by omega))

/-- Entry `e` of an entry placed at `k`. -/
theorem shl_entry {W N : Nat} (y : BitVec W) {k e : Nat} (hk : k < N) (he : e < N) :
    ((y.setWidth (N * W)) <<< (k * W)).extractLsb' (e * W) W = if e = k then y else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have h1 : e * W + b < N * W := by have := rowMajor_le (K := W) he; omega
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, BitVec.getLsbD_shiftLeft, h1,
    BitVec.getLsbD_setWidth]
  split
  · subst e; simp [hb, show k * W + b - k * W = b by omega, show ¬ (k * W + b < k * W) by omega]; omega
  · rename_i hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := rowMajor_le (K := W) hlt; simp [show e * W + b < k * W by omega]
    · have := rowMajor_le (K := W) hgt
      simp [BitVec.getLsbD_of_ge y (e * W + b - k * W) (by omega)]

/-- The sign-extended product truncated to `m ≤ n` bits. -/
theorem setWidth_mul_signExtend {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := Lib.setWidth_add_mul_signExtend h (0#m) a b
  simpa using this

/-! ### Known values -/

theorem ofInt32 {v : Nat} (h : v < 2 ^ 31) : LVec.ofInt 32 (v : Int) = LVec.ofBitVec (BitVec.ofNat 32 v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem toNat_ofNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `<<` of known vectors (a known shift amount). -/
theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft, LVec.getElem?_ofBitVec]
  by_cases h : i < y.toNat
  · simp [h]
  · simp [h, show i - y.toNat < w by omega]

theorem rzV_ofBitVec {n W : Nat} (x : BitVec W) : rzV n W (LVec.ofBitVec x) = LVec.ofBitVec (x.setWidth n) := by
  unfold rzV
  split
  · subst n; rw [BitVec.setWidth_eq]
  · rw [LVec.resizeU_ofBitVec]

/-- `{{m{x[W-1]}}, x}` of a known window is the sign extension. -/
theorem sxv_of_win {v : LVec} {AccW lo W : Nat} (hW : 1 ≤ W) {x : BitVec W} (h : v.extract lo W = LVec.ofBitVec x) :
    sxv v AccW lo W = LVec.ofBitVec (x.signExtend (AccW + W)) := by
  have h1 : v.extract (lo + W - 1) 1 = (v.extract lo W).extract (W - 1) 1 := by
    rw [LVec.extract_extract v (show W - 1 + 1 ≤ W by omega), show lo + (W - 1) = lo + W - 1 by omega]
  have h2 := LVec.ofBitVec_replicate_append_eq_signExtend hW x AccW (p := W - 1) (lo := 0) (by omega)
  rw [extractLsb'_self] at h2
  rw [sxv, h1, h, LVec.extract_ofBitVec x (show W - 1 + 1 ≤ W by omega)]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  exact h2

/-! ## 5. The registers of a transaction, `t` busy cycles after its start -/

attribute [local simp] condTrue_knownBit

/-- `Σ_{k' < m} A[i][k']·B[k'][j]` in the integers (`Tasks.Matmul.dot` at `m = N`). -/
def psum (N W : Nat) {n : Nat} (A B : BitVec n) (m i j : Nat) : Int :=
  (List.range m).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (m i j : Nat) : psum N W A B (m + 1) i j =
    psum N W A B m i j + Tasks.Matmul.entry W A (i * N + m) * Tasks.Matmul.entry W B (m * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

/-- Entry `e` of delay line `k`, `t` busy cycles after the start: `A[t+e-k][k]` for `e ≤ k ≤ t + e`. -/
def dlE (N W : Nat) (A : BitVec (N * N * W)) (t k e : Nat) : BitVec W :=
  if e ≤ k ∧ k ≤ t + e then A.extractLsb' (((t + e - k) * N + k) * W) W else 0

/-- The partial sum of PE `(k, j)` after `t ≥ k + 1` busy cycles: output row `t - 1 - k` summed to `k`. -/
abbrev psV (N W AccW : Nat) (A B : BitVec (N * N * W)) (t k j : Nat) : BitVec AccW :=
  BitVec.ofInt AccW (psum N W A B (k + 1) (t - 1 - k) j)

/-- Entry `(i, j)` of the product. -/
abbrev outV (N W AccW : Nat) (A B : BitVec (N * N * W)) (i j : Nat) : BitVec AccW :=
  BitVec.ofInt AccW (psum N W A B N i j)

/-- The delay lines, window by window. -/
def DlOk (N W : Nat) (A : BitVec (N * N * W)) (t : Nat) (dl : LVec) : Prop :=
  ∀ k e, k < N → e < N → dl.extract ((k * N + e) * W) W = LVec.ofBitVec (dlE N W A t k e)

/-- The partial sums of the PEs that have one. -/
def PsOk (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (ps : LVec) : Prop :=
  ∀ k j, k < N → j < N → k + 1 ≤ t → ps.extract ((k * N + j) * AccW) AccW = LVec.ofBitVec (psV N W AccW A B t k j)

/-- The collected rows of `C`. -/
def COk (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (c : LVec) : Prop :=
  ∀ i j, i < N → j < N → 2 * N ≤ i + t →
    c.extract ((i * N + j) * AccW) AccW = LVec.ofBitVec (outV N W AccW A B (i + t - 2 * N) j)

/-- The range facts the steps use. -/
structure Rng (N W AccW : Nat) : Prop where
  hN : 1 ≤ N
  hW : 1 ≤ W
  hA : 1 ≤ AccW
  hNW : N * N * W < 2 ^ 31

theorem Rng.hN31 {N W AccW : Nat} (h : Rng N W AccW) : N * W < 2 ^ 31 := by
  have := Nat.mul_le_mul_right W (Nat.le_mul_of_pos_left N h.hN); have := h.hNW; omega
theorem Rng.hNW1 {N W AccW : Nat} (h : Rng N W AccW) : N ≤ N * W := Nat.le_mul_of_pos_right N h.hW
theorem Rng.hWN {N W AccW : Nat} (h : Rng N W AccW) : W ≤ N * W := Nat.le_mul_of_pos_left W h.hN
theorem Rng.hNN {N W AccW : Nat} (h : Rng N W AccW) : N * W ≤ N * N * W := by
  rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ h.hN

/-! ### The delay lines -/

theorem dlE_go (N W : Nat) (A : BitVec (N * N * W)) {k e : Nat} (hk : k < N) (he : e < N) :
    ((A.extractLsb' (k * W) W).setWidth (N * W) <<< (k * W)).extractLsb' (e * W) W = dlE N W A 0 k e := by
  rw [shl_entry _ hk he, dlE]
  by_cases h : e = k
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]

theorem dlE_step (N W : Nat) (A : BitVec (N * N * W)) (t : Nat) {k e : Nat} (hk : k < N) (he : e < N) :
    (((packBV W N (dlE N W A t k)) >>> W) |||
      ((A >>> ((t + 1) * (N * W))).extractLsb' (k * W) W).setWidth (N * W) <<< (k * W)).extractLsb' (e * W) W =
      dlE N W A (t + 1) k e := by
  rw [extractLsb'_or, shr_entry, shl_entry _ hk he, Lib.extractLsb'_ushiftRight]
  have hix : (t + 1) * (N * W) + k * W = ((t + 1 + k - k) * N + k) * W := by
    rw [Nat.add_sub_cancel, Nat.add_mul ((t + 1) * N) k W, Nat.mul_assoc (t + 1) N W]
  by_cases h1 : e < k
  · rw [if_pos (by omega), if_neg (by omega), bor0]
    unfold dlE
    by_cases h2 : k ≤ t + (e + 1)
    · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨by omega, by omega⟩, show t + (e + 1) - k = t + 1 + e - k by omega]
    · rw [if_neg (by omega), if_neg (by omega)]
  · by_cases h2 : e = k
    · subst h2
      have hz : (if e + 1 < N then dlE N W A t e (e + 1) else 0) = 0 := by
        split
        · unfold dlE; rw [if_neg (by omega)]
        · rfl
      rw [hz, if_pos rfl, b0or, hix]
      unfold dlE; rw [if_pos ⟨Nat.le_refl _, by omega⟩]
    · have hz : (if e + 1 < N then dlE N W A t k (e + 1) else 0) = 0 := by
        split
        · unfold dlE; rw [if_neg (by omega)]
        · rfl
      rw [hz, if_neg h2, bor0]
      unfold dlE; rw [if_neg (by omega)]

theorem lineGo_known {N W AccW : Nat} (h : Rng N W AccW) (A : BitVec (N * N * W)) {k : Nat} (hk : k < N) :
    lineGo N W k (LVec.ofBitVec A) = LVec.ofBitVec ((A.extractLsb' (k * W) W).setWidth (N * W) <<< (k * W)) := by
  have hkW : k * W + W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show k + 1 ≤ N by omega); have := h.hNN; rw [Nat.add_mul, Nat.one_mul] at *; omega
  have hk31 : k < 2 ^ 31 := by have := h.hN31; have := h.hNW1; omega
  have hW31 : W < 2 ^ 31 := by have := h.hN31; have := h.hWN; omega
  have hkw : (BitVec.ofNat 32 k * BitVec.ofNat 32 W).toNat = k * W := by
    have : k * W < 2 ^ 31 := by have := h.hN31; have := Nat.mul_le_mul_right W (show k ≤ N by omega); omega
    rw [BitVec.toNat_mul, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [lineGo, LVec.extract_ofBitVec A hkW, rzV_ofBitVec, ofInt32 hk31, ofInt32 hW31, LVec.mul_ofBitVec,
    shl_ofBitVec, hkw]

theorem lineStep_known {N W AccW : Nat} (h : Rng N W AccW) (X : BitVec (N * N * W)) {L : BitVec (N * W)} {dl : LVec}
    {k : Nat} (hk : k < N) (hl : dl.extract (k * N * W) (N * W) = LVec.ofBitVec L) :
    lineStep N W k (LVec.ofBitVec X) dl =
      LVec.ofBitVec ((L >>> W) ||| ((X.extractLsb' (k * W) W).setWidth (N * W) <<< (k * W))) := by
  have hkW : k * W + W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show k + 1 ≤ N by omega); have := h.hNN; rw [Nat.add_mul, Nat.one_mul] at *; omega
  have hk31 : k < 2 ^ 31 := by have := h.hN31; have := h.hNW1; omega
  have hW31 : W < 2 ^ 31 := by have := h.hN31; have := h.hWN; omega
  have hkw : (BitVec.ofNat 32 k * BitVec.ofNat 32 W).toNat = k * W := by
    have : k * W < 2 ^ 31 := by have := h.hN31; have := Nat.mul_le_mul_right W (show k ≤ N by omega); omega
    rw [BitVec.toNat_mul, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [lineStep, hl, ofInt32 hW31, LVec.shr_ofBitVec, toNat_ofNat32 (by omega), LVec.extract_ofBitVec X hkW,
    rzV_ofBitVec, ofInt32 hk31, LVec.mul_ofBitVec, shl_ofBitVec, hkw, LVec.or_ofBitVec]

/-- A line of the delay lines, from the windows. -/
theorem line_of_win {N W : Nat} {A : BitVec (N * N * W)} {t : Nat} {dl : LVec} (hd : DlOk N W A t dl) {k : Nat}
    (hk : k < N) (hw : dl.width = N * N * W) :
    dl.extract (k * N * W) (N * W) = LVec.ofBitVec (packBV W N (dlE N W A t k)) := by
  apply eq_ofBitVec_of_win (by simp)
  intro e he
  have h1 : e * W + W ≤ N * W := rowMajor_le (K := W) he
  rw [LVec.extract_extract dl h1, ← hd k e hk he]
  congr 1
  rw [Nat.add_mul (k * N) e W]

/-- **The delay lines after a cycle that writes them all**: line `k` holds `g k`. -/
theorem dl_after {N W : Nat} {g : Nat → LVec} (hg : ∀ k, (g k).width = N * W) {dl : LVec}
    (hw : dl.width = N * N * W) {k e : Nat} (hk : k < N) (he : e < N) :
    (nbaFold "dl" ((List.range N).map fun k => ("dl", k * (N * W), g k)) dl).extract ((k * N + e) * W) W =
      (g k).extract (e * W) W := by
  rw [nbaFold_map]
  have h1 : e * W + W ≤ N * W := rowMajor_le (K := W) he
  rw [show (k * N + e) * W = k * (N * W) + e * W by rw [Nat.add_mul, Nat.mul_assoc],
    ← LVec.extract_extract _ h1, extract_ie hg dl N (Nat.le_of_eq (by rw [hw, Nat.mul_assoc])) k hk]

/-! ### The PEs -/

theorem topV_known {N W AccW : Nat} (h : Rng N W AccW) {B : BitVec (N * N * W)} {dl : LVec} {x : BitVec W} {j : Nat}
    (hj : j < N) (hx : dl.extract 0 W = LVec.ofBitVec x) :
    topV W AccW j (LVec.ofBitVec B) dl =
      LVec.ofBitVec (BitVec.ofInt AccW (x.toInt * (B.extractLsb' (j * W) W).toInt)) := by
  have hjW : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (by omega) hj; simpa using this
  rw [topV, sxv_of_win h.hW hx, sxv_of_win h.hW (LVec.extract_ofBitVec B hjW), LVec.mul_ofBitVec,
    LVec.resizeU_ofBitVec, setWidth_mul_signExtend (by omega)]

theorem rowV_known {N W AccW : Nat} (h : Rng N W AccW) {B : BitVec (N * N * W)} {dl ps : LVec} {x : BitVec W}
    {p : BitVec AccW} {k j : Nat} (hk : k + 1 < N) (hj : j < N) (hx : dl.extract ((k + 1) * N * W) W = LVec.ofBitVec x)
    (hp : ps.extract ((k * N + j) * AccW) AccW = LVec.ofBitVec p) :
    rowV N W AccW k j (LVec.ofBitVec B) dl ps =
      LVec.ofBitVec (p + BitVec.ofInt AccW (x.toInt * (B.extractLsb' (((k + 1) * N + j) * W) W).toInt)) := by
  have hjW := Lib.rowMajor_window_le (M := N) (N := N) (w := W) hk hj
  simp only [rowV, hp, sxv_of_win h.hW hx, sxv_of_win h.hW (LVec.extract_ofBitVec B hjW), LVec.mul_ofBitVec,
    LVec.resizeU_ofBitVec, LVec.add_ofBitVec]
  rw [Lib.setWidth_add_mul_signExtend (by omega)]

/-! ### The commits of the delay lines, the partial sums and `C` -/

theorem rm_div {N k j : Nat} (hj : j < N) : (N + (k * N + j)) / N - 1 = k := by
  have e : N + (k * N + j) = j + (k + 1) * N := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]; omega

theorem rm_mod {N k j : Nat} (hj : j < N) : (N + (k * N + j)) % N = j := by
  have e : N + (k * N + j) = j + (k + 1) * N := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- The delay-line queue of a start or busy cycle, as one map. -/
theorem linesQ_map {N W : Nat} {s a bz ash dl : LVec} {g : Nat → LVec}
    (hq : ∀ k, k < N → lineQ N W s a bz ash dl k = [("dl", k * N * W, g k)]) :
    linesQ N W s a bz ash dl = (List.range N).map fun k => ("dl", k * (N * W), g k) := by
  rw [linesQ, rmap1 fun k hk => by rw [hq k hk, Nat.mul_assoc]]

/-- The partial sum written into PE `r` (row-major) in a busy cycle. -/
def gps (N W AccW : Nat) (w dl ps : LVec) (r : Nat) : LVec :=
  if r < N then (topV W AccW r w dl).resizeU AccW else (rowV N W AccW (r / N - 1) (r % N) w dl ps).resizeU AccW

def psF (N W AccW : Nat) (w dl ps : LVec) (r : Nat) : String × Nat × LVec := ("ps", r * AccW, gps N W AccW w dl ps r)

theorem psQ_busy {N W AccW : Nat} (hN : 1 ≤ N) (w dl ps : LVec) :
    psQ N W AccW (knownBit true) w dl ps = (List.range (N * N)).map (psF N W AccW w dl ps) := by
  have h1 : (List.range N).flatMap (topQ W AccW (knownBit true) w dl) = (List.range N).map (psF N W AccW w dl ps) :=
    rmap1 fun j hj => by simp [topQ, psF, gps, hj]
  have h2 : ((List.range (N - 1)).flatMap fun k => (List.range N).flatMap (rowQ N W AccW (knownBit true) w dl ps k)) =
      (List.range ((N - 1) * N)).map fun r => psF N W AccW w dl ps (N + r) :=
    rmap2 (fun r => psF N W AccW w dl ps (N + r)) fun k j _ hj => by
      have e3 : (k + 1) * N + j = N + (k * N + j) := by rw [Nat.add_mul, Nat.one_mul]; omega
      simp [rowQ, psF, gps, rm_div hj, rm_mod hj, show ¬ N + (k * N + j) < N by omega, e3]
  rw [psQ, h1, h2, map_range_append (psF N W AccW w dl ps) N ((N - 1) * N),
    show N + (N - 1) * N = N * N by rw [Nat.sub_mul, Nat.one_mul]; have := Nat.le_mul_self N; omega]

/-- The value `C` window `r` takes in a collecting cycle. -/
def gc (N AccW : Nat) (c ps : LVec) (r : Nat) : LVec :=
  if r < (N - 1) * N then (c.extract ((r + N) * AccW) AccW).resizeU AccW else (ps.extract (r * AccW) AccW).resizeU AccW

def cF (N AccW : Nat) (c ps : LVec) (r : Nat) : String × Nat × LVec := ("C", r * AccW, gc N AccW c ps r)

theorem cQ_collect {N AccW : Nat} (hN : 1 ≤ N) {t : LVec} (hg : geB N t = true) (c ps : LVec) :
    cQ N AccW t (knownBit true) c ps = (List.range (N * N)).map (cF N AccW c ps) := by
  have h1 : ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap (crowQ N AccW t (knownBit true) c i)) =
      (List.range ((N - 1) * N)).map (cF N AccW c ps) :=
    rmap2 (cF N AccW c ps) fun i j hi hj => by
      have e3 : (i + 1) * N + j = i * N + j + N := by rw [Nat.add_mul, Nat.one_mul]; omega
      have e4 : i * N + j < (N - 1) * N := by
        have := rowMajor_le (K := N) hi; omega
      simp only [crowQ, condTrue_knownBit, if_true, hg, cF, gc, if_pos e4, e3]
  have h2 : (List.range N).flatMap (coutQ N AccW t (knownBit true) ps) =
      (List.range N).map fun j => cF N AccW c ps ((N - 1) * N + j) :=
    rmap1 fun j hj => by simp only [coutQ, condTrue_knownBit, if_true, hg, cF, gc, if_neg (show ¬ (N - 1) * N + j < (N - 1) * N by omega)]
  rw [cQ, h1, h2, map_range_append (cF N AccW c ps) ((N - 1) * N) N,
    show (N - 1) * N + N = N * N by rw [Nat.sub_mul, Nat.one_mul]; have := Nat.le_mul_self N; omega]

theorem cQ_nocollect {N AccW : Nat} {t : LVec} (hg : geB N t = false) (c ps : LVec) :
    cQ N AccW t (knownBit true) c ps = [] := by
  simp [cQ, crowQ, coutQ, hg]

theorem queues_idle {N W AccW : Nat} {s a bz ash dl w c ps t : LVec} (hs : s.condTrue = false) (hb : bz.condTrue = false) :
    linesQ N W s a bz ash dl = [] ∧ psQ N W AccW bz w dl ps = [] ∧ cQ N AccW t bz c ps = [] := by
  simp [linesQ, lineQ, psQ, topQ, rowQ, cQ, crowQ, coutQ, hs, hb]

/-! ### The control on known values -/

theorem lastB_known {N W AccW : Nat} (h : Rng N W AccW) {t : Nat} (ht : t < 2 * N) :
    lastB N (LVec.ofBitVec (BitVec.ofNat 32 t)) = decide (t + 1 = 2 * N) := by
  have hN31 : N < 2 ^ 31 := by have := h.hN31; have := h.hNW1; omega
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  have e : BitVec.ofNat 32 N + BitVec.ofNat 32 N = BitVec.ofNat 32 (2 * N) := by
    rw [BitVec.ofNat_add_ofNat, Nat.two_mul]
  simp only [lastB, ofInt32 hN31, h1', LVec.add_ofBitVec, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec,
    LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec, e]
  have := Lib.ofNat_eq_ofNat_sub_one_iff (w := 32) ht (by omega)
  by_cases hc : t + 1 = 2 * N
  · simp [hc] at this ⊢; simp [this]
  · simp [hc] at this ⊢; simp [this]

theorem geB_known {N W AccW : Nat} (h : Rng N W AccW) {t : Nat} (ht : t < 2 ^ 32) :
    geB N (LVec.ofBitVec (BitVec.ofNat 32 t)) = decide (N ≤ t) := by
  have hN31 : N < 2 ^ 31 := by have := h.hN31; have := h.hNW1; omega
  simp only [geB, ofInt32 hN31, LVec.ge_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec, BitVec.le_def,
    toNat_ofNat32 ht, toNat_ofNat32 (show N < 2 ^ 32 by omega)]
  by_cases hc : N ≤ t <;> simp [hc]

theorem nwV_known {N W AccW : Nat} (h : Rng N W AccW) : nwV N W = LVec.ofBitVec (BitVec.ofNat 32 N * BitVec.ofNat 32 W) := by
  have hN31 : N < 2 ^ 31 := by have := h.hN31; have := h.hNW1; omega
  have hW31 : W < 2 ^ 31 := by have := h.hN31; have := h.hWN; omega
  rw [nwV, ofInt32 hN31, ofInt32 hW31, LVec.mul_ofBitVec]

theorem nw_toNat {N W AccW : Nat} (h : Rng N W AccW) : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
  have := h.hN31; have := h.hNW1; have := h.hWN
  rw [BitVec.toNat_mul, toNat_ofNat32 (by omega), toNat_ofNat32 (by omega), Nat.mod_eq_of_lt (by omega)]

theorem t_succ {t : Nat} : (LVec.ofBitVec (BitVec.ofNat 32 t)).add (LVec.ofInt 32 1) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) := by
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  rw [h1', LVec.add_ofBitVec, show (1#32 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]

/-- **The control in a busy cycle `t < 2N`**: `t` and the feeder step; the last one ends. -/
theorem ctrl_busy {N W AccW : Nat} (h : Rng N W AccW) {t : Nat} (ht : t < 2 * N) (a b w : LVec) (X : BitVec (N * N * W)) :
    let q := ctrlQ N W (knownBit false) (knownBit false) a b (knownBit false) (LVec.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) w (LVec.ofBitVec X)
    nbaFold "done" q (knownBit false) = knownBit (decide (t + 1 = 2 * N)) ∧
      nbaFold "t" q (LVec.ofBitVec (BitVec.ofNat 32 t)) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
      nbaFold "busy" q (knownBit true) = knownBit (decide (t + 1 ≠ 2 * N)) ∧ nbaFold "w" q w = w ∧
      nbaFold "ash" q (LVec.ofBitVec X) = LVec.ofBitVec (X >>> (N * W)) := by
  intro q
  have hq : q = (if decide (t + 1 = 2 * N) then
      [wr "t" (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))),
        wr "ash" (LVec.ofBitVec X) (LVec.ofBitVec (X >>> (N * W))), wr "busy" (knownBit true) ⟨#[.l0]⟩,
        wr "done" (knownBit false) ⟨#[.l1]⟩]
    else [wr "t" (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))),
        wr "ash" (LVec.ofBitVec X) (LVec.ofBitVec (X >>> (N * W)))]) := by
    simp only [q, ctrlQ, condTrue_knownBit, Bool.false_eq_true, if_false, if_true, lastB_known h ht, t_succ,
      nwV_known h, LVec.shr_ofBitVec, nw_toNat h]
  rw [hq]
  by_cases hf : t + 1 = 2 * N <;>
    simp [hf, nbaFold, wr, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1]

/-! ## 6. One cycle of each phase -/

theorem rm_lt_sq {N k j : Nat} (hk : k < N) (hj : j < N) : k * N + j < N * N := by
  have := rowMajor_le (K := N) hk; omega

theorem gps_width (N W AccW : Nat) (w dl ps : LVec) : ∀ r, (gps N W AccW w dl ps r).width = AccW := by
  intro r; unfold gps; split <;> simp

theorem gc_width (N AccW : Nat) (c ps : LVec) : ∀ r, (gc N AccW c ps r).width = AccW := by
  intro r; unfold gc; split <;> simp

/-- **A busy cycle `t < 2N`**: every register steps to its value at `t + 1`. -/
theorem next_busy {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 2 * N)
    (ck a b c dl ps : LVec) (hcw : c.width = N * N * AccW) (hdw : dl.width = N * N * W) (hpw : ps.width = N * N * AccW)
    (hd : DlOk N W A t dl) (hp : PsOk N W AccW A B t ps) (hC : COk N W AccW A B t c) :
    ∃ c' dl' ps', mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec B)
        (LVec.ofBitVec (A >>> ((t + 1) * (N * W)))) dl ps =
      MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = 2 * N))) c'
        (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ 2 * N))) (LVec.ofBitVec B)
        (LVec.ofBitVec (A >>> ((t + 1 + 1) * (N * W)))) dl' ps' ∧
      c'.width = N * N * AccW ∧ dl'.width = N * N * W ∧ ps'.width = N * N * AccW ∧
      DlOk N W A (t + 1) dl' ∧ PsOk N W AccW A B (t + 1) ps' ∧ COk N W AccW A B (t + 1) c' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ctrl_busy h ht a b (LVec.ofBitVec B) (A >>> ((t + 1) * (N * W)))
  have hash : A >>> ((t + 1) * (N * W)) >>> (N * W) = A >>> ((t + 1 + 1) * (N * W)) := by
    rw [← BitVec.shiftRight_add, Nat.succ_mul (t + 1)]
  rw [next_eq]
  refine ⟨nbaFold "C" (cQ N AccW (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) c ps) c,
    nbaFold "dl" (linesQ N W (knownBit false) a (knownBit true) (LVec.ofBitVec (A >>> ((t + 1) * (N * W)))) dl) dl,
    nbaFold "ps" (psQ N W AccW (knownBit true) (LVec.ofBitVec B) dl ps) ps, ?_, by simp [hcw], by simp [hdw],
    by simp [hpw], ?_, ?_, ?_⟩
  · rw [h1, h2, h3, h4, h5, hash]
  · -- the delay lines
    intro k e hk he
    rw [linesQ_map (g := fun k => (lineStep N W k (LVec.ofBitVec (A >>> ((t + 1) * (N * W)))) dl).resizeU (N * W))
      (fun k _ => by simp [lineQ])]
    rw [dl_after (fun _ => by simp) hdw hk he, lineStep_known h _ hk (line_of_win hd hk hdw), LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq, LVec.extract_ofBitVec _ (rowMajor_le he), dlE_step N W A t hk he]
  · -- the partial sums
    intro k j hk hj hkt
    rw [psQ_busy h.hN, show psF N W AccW (LVec.ofBitVec B) dl ps =
      fun r => ("ps", r * AccW, gps N W AccW (LVec.ofBitVec B) dl ps r) from rfl, nbaFold_map, extract_ie (gps_width N W AccW _ _ _) ps (N * N) (Nat.le_of_eq (by rw [hpw]))
      (k * N + j) (rm_lt_sq hk hj)]
    unfold gps
    rcases k with _ | k
    · have hx : dl.extract 0 W = LVec.ofBitVec (dlE N W A t 0 0) := by simpa using hd 0 0 h.hN h.hN
      rw [if_pos (by simpa using hj), Nat.zero_mul, Nat.zero_add, topV_known h hj hx, LVec.resizeU_ofBitVec,
        BitVec.setWidth_eq]
      simp [psV, psum, dlE, Tasks.Matmul.entry]
    · have hk' : k + 1 ≤ t := by omega
      have hx : dl.extract ((k + 1) * N * W) W = LVec.ofBitVec (dlE N W A t (k + 1) 0) := by
        simpa using hd (k + 1) 0 hk h.hN
      have hpk := hp k j (by omega) hj hk'
      have e3 : (k + 1) * N + j = N + (k * N + j) := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [if_neg (by omega), e3, rm_div hj, rm_mod hj, rowV_known h hk hj hx hpk, LVec.resizeU_ofBitVec,
        BitVec.setWidth_eq]
      congr 1
      have e4 : t + 1 - 1 - (k + 1) = t - 1 - k := by omega
      have e5 : t + 0 - (k + 1) = t - 1 - k := by omega
      rw [psV, psV, e4, psum_succ N W A B (k + 1) (t - 1 - k) j, BitVec.ofInt_add]
      simp only [dlE, Nat.zero_le, true_and, if_pos (show k + 1 ≤ t + 0 by omega), e5, Tasks.Matmul.entry]
  · -- the collected rows
    by_cases hcol : N ≤ t
    · have hg : geB N (LVec.ofBitVec (BitVec.ofNat 32 t)) = true := by
        rw [geB_known h (by have := h.hN31; have := h.hNW1; omega)]; exact decide_eq_true hcol
      intro i j hi hj hit
      rw [cQ_collect h.hN hg, show cF N AccW c ps = fun r => ("C", r * AccW, gc N AccW c ps r) from rfl, nbaFold_map,
        extract_ie (gc_width N AccW _ _) c (N * N) (Nat.le_of_eq (by rw [hcw]))
        (i * N + j) (rm_lt_sq hi hj)]
      unfold gc
      split
      · rename_i hlt
        have hi' : i + 1 < N := by
          rcases Nat.lt_or_ge (i + 1) N with h' | h'
          · exact h'
          · have := Nat.mul_le_mul_right N (show N - 1 ≤ i by omega); omega
        have e3 : i * N + j + N = (i + 1) * N + j := by rw [Nat.add_mul, Nat.one_mul]; omega
        rw [e3, hC (i + 1) j hi' hj (by omega), LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
          show i + 1 + t - 2 * N = i + (t + 1) - 2 * N by omega]
      · rename_i hge
        have hi' : i = N - 1 := by
          rcases Nat.lt_or_ge i (N - 1) with h' | h'
          · exact absurd (by have := rowMajor_le (K := N) h'; omega) hge
          · omega
        subst hi'
        rw [hp (N - 1) j hi hj (by omega), LVec.resizeU_ofBitVec, BitVec.setWidth_eq, psV, outV,
          show N - 1 + 1 = N by omega, show t - 1 - (N - 1) = N - 1 + (t + 1) - 2 * N by omega]
    · have hg : geB N (LVec.ofBitVec (BitVec.ofNat 32 t)) = false := by
        rw [geB_known h (by have := h.hN31; have := h.hNW1; omega)]; exact decide_eq_false hcol
      rw [cQ_nocollect hg]
      intro i j hi _ hit
      omega

theorem psQ_off {N W AccW : Nat} {bz w dl ps : LVec} (hb : bz.condTrue = false) : psQ N W AccW bz w dl ps = [] := by
  simp [psQ, topQ, rowQ, hb]

theorem cQ_off {N AccW : Nat} {t bz c ps : LVec} (hb : bz.condTrue = false) : cQ N AccW t bz c ps = [] := by
  simp [cQ, crowQ, coutQ, hb]

/-- The control in a start cycle. -/
theorem ctrl_start {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (dn t w ash : LVec)
    (hdn : dn.width = 1) (ht : t.width = 32) (hww : w.width = N * N * W) (haw : ash.width = N * N * W) :
    let q := ctrlQ N W (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn t (knownBit false) w ash
    nbaFold "done" q dn = knownBit false ∧ nbaFold "t" q t = LVec.ofBitVec (BitVec.ofNat 32 0) ∧
      nbaFold "busy" q (knownBit false) = knownBit true ∧ nbaFold "w" q w = LVec.ofBitVec B ∧
      nbaFold "ash" q ash = LVec.ofBitVec (A >>> ((0 + 1) * (N * W))) := by
  intro q
  have hq : q = [wr "busy" (knownBit false) ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0),
      wr "w" w (LVec.ofBitVec B), wr "ash" ash (LVec.ofBitVec (A >>> (N * W)))] := by
    simp only [q, ctrlQ, condTrue_knownBit, Bool.false_eq_true, if_false, if_true, nwV_known h, LVec.shr_ofBitVec,
      nw_toNat h]
  rw [hq]
  simp [nbaFold, wr, hdn, ht, hww, haw, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1]

/-- **A start cycle** from an idle state (`busy` = 0): the state at `t = 0`. -/
theorem next_start {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (ck dn c t w ash dl ps : LVec)
    (hdn : dn.width = 1) (ht : t.width = 32) (hww : w.width = N * N * W) (haw : ash.width = N * N * W)
    (hdw : dl.width = N * N * W) :
    ∃ dl', mmNext N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn c t
        (knownBit false) w ash dl ps =
      MS ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true) (LVec.ofBitVec B)
        (LVec.ofBitVec (A >>> ((0 + 1) * (N * W)))) dl' ps ∧
      dl'.width = N * N * W ∧ DlOk N W A 0 dl' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ctrl_start h A B dn t w ash hdn ht hww haw
  have hb : (knownBit false).condTrue = false := condTrue_knownBit false
  rw [next_eq, psQ_off hb, cQ_off hb]
  refine ⟨nbaFold "dl" (linesQ N W (knownBit true) (LVec.ofBitVec A) (knownBit false) ash dl) dl, ?_, by simp [hdw], ?_⟩
  · rw [h1, h2, h3, h4, h5]; rfl
  · intro k e hk he
    rw [linesQ_map (g := fun k => (lineGo N W k (LVec.ofBitVec A)).resizeU (N * W)) (fun k _ => by simp [lineQ])]
    rw [dl_after (fun _ => by simp) hdw hk he, lineGo_known h A hk, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
      LVec.extract_ofBitVec _ (rowMajor_le he), dlE_go N W A hk he]

/-- **An idle cycle** (no reset, no start, `busy` = 0) changes no register. -/
theorem next_idle (N W AccW : Nat) (ck a b dn c t w ash dl ps : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c t (knownBit false) w ash dl ps =
      MS ck (knownBit false) (knownBit false) a b dn c t (knownBit false) w ash dl ps := by
  have hb : (knownBit false).condTrue = false := condTrue_knownBit false
  have hc : ctrlQ N W (knownBit false) (knownBit false) a b dn t (knownBit false) w ash = [] := by
    simp [ctrlQ]
  rw [next_eq, psQ_off hb, cQ_off hb, hc, show linesQ N W (knownBit false) a (knownBit false) ash dl = [] by
    simp [linesQ, lineQ]]
  rfl

/-- **A reset cycle** clears `busy` and `done`. -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c t bz w ash dl ps : LVec) (hdn : dn.width = 1) (hbz : bz.width = 1) :
    ∃ c' t' w' ash' dl' ps', mmNext N W AccW ck (knownBit true) s a b dn c t bz w ash dl ps =
      MS ck (knownBit true) s a b (knownBit false) c' t' (knownBit false) w' ash' dl' ps' := by
  have hc : ctrlQ N W (knownBit true) s a b dn t bz w ash =
      [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0)] := by
    simp [ctrlQ]
  have hd : nbaFold "done" (ctrlQ N W (knownBit true) s a b dn t bz w ash) dn = knownBit false := by
    rw [hc]; simp [nbaFold, wr, hdn, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0]
  have hb : nbaFold "busy" (ctrlQ N W (knownBit true) s a b dn t bz w ash) bz = knownBit false := by
    rw [hc]; simp [nbaFold, wr, hbz, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0]
  rw [next_eq, hd, hb]
  exact ⟨_, _, _, _, _, _, rfl⟩

/-! ## 7. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c t bz w ash dl ps : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ t.width = 32 ∧ bz.width = 1 ∧ w.width = N * N * W ∧
    ash.width = N * N * W ∧ dl.width = N * N * W ∧ ps.width = N * N * AccW

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz w ash dl ps, st = MS ck r s a b dn c t bz w ash dl ps ∧ Wd N W AccW dn c t bz w ash dl ps

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c t bz w ash dl ps : LVec) (hw : Wd N W AccW dn c t bz w ash dl ps) :
    I N W AccW (mmNext N W AccW ck r s a b dn c t bz w ash dl ps) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  rw [next_eq]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  have hm : p ∈ ctrlP N W :: genPs N W AccW := by simpa [mmD] using hp
  rcases mm_mem hm with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
    simp [ctrlP, lineP, topP, rowP, crowP, coutP, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * W), .xVec (N * N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-! ## 8. The protocol: the phases of `TxTask.satisfiedAtV2_of_phases` -/

/-- The state `t` busy cycles after a start with operands `A`, `B` (the invariant). -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c dl ps, st = MS ck r s a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec B) (LVec.ofBitVec (A >>> ((t + 1) * (N * W)))) dl ps ∧
    c.width = N * N * AccW ∧ dl.width = N * N * W ∧ ps.width = N * N * AccW ∧
    DlOk N W A t dl ∧ PsOk N W AccW A B t ps ∧ COk N W AccW A B t c

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b t w ash dl ps, st = MS ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) t
    (knownBit false) w ash dl ps

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz w ash dl ps, prev = MS ck r s a b dn c t bz w ash dl ps ∧
    Wd N W AccW dn c t bz w ash dl ps ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c t bz w ash dl ps

theorem MS_inj {ck r s a b dn c t bz w ash dl ps ck' r' s' a' b' dn' c' t' bz' w' ash' dl' ps' : LVec}
    (h : MS ck r s a b dn c t bz w ash dl ps = MS ck' r' s' a' b' dn' c' t' bz' w' ash' dl' ps') :
    dn = dn' ∧ c = c' ∧ t = t' ∧ bz = bz' ∧ w = w' ∧ ash = ash' ∧ dl = dl' ∧ ps = ps' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- **All rows collected**: `C` is the product. -/
theorem c_final {N W AccW : Nat} (hN : 1 ≤ N) (A B : BitVec (N * N * W)) {c : LVec} (hcw : c.width = N * N * AccW)
    (hC : COk N W AccW A B (2 * N) c) : c = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]
  apply eq_ofBitVec_of_win hcw
  intro r hr
  have hNp : 0 < N := by omega
  have hj : r % N < N := Nat.mod_lt _ hNp
  have hi : r / N < N := (Nat.div_lt_iff_lt_mul hNp).mpr hr
  have hij : r / N * N + r % N = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r N
  have hc := hC (r / N) (r % N) hi hj (Nat.le_add_left _ _)
  rw [hij, Nat.add_sub_cancel] at hc
  rw [hc]; rfl

/-- **The phase model** at `(N, W, AccW)`, latency `2N`: `Ready` after a reset, `Busy x m` the state
`t = 2N - 1 - m` busy cycles after a start, `Fin x` the product shown. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (2 * N) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t bz w ash dl ps k 40 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c t bz w ash dl ps hw
  Ready st := ∃ ck r s a b c t w ash dl ps, st = MS ck r s a b (knownBit false) c t (knownBit false) w ash dl ps
  Busy x m st := ∃ t, t + m + 1 = 2 * N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, t, w, ash, dl, ps, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, c, dl, ps, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, t, w, ash, dl, ps, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', t', w', ash', dl', ps', h⟩ := next_reset (N := N) (W := W) (AccW := AccW) (appIn e "clk" ck)
      (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn c t bz w ash dl ps hw.1 hw.2.2.2.1
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, hw, rfl⟩ hprev hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    have hbz : bz = knownBit false := by
      rcases hprev with ⟨ck', r', s', a', b', c', t', w', ash', dl', ps', hp⟩ | ⟨y, ck', r', s', a', b', t', w', ash', dl',
        ps', hp⟩
      · exact (MS_inj hp).2.2.2.1
      · exact (MS_inj hp).2.2.2.1
    subst hbz
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    obtain ⟨dl', hn, hdw', hd'⟩ := next_start ⟨hN, hW, hA, hNW⟩ x.1 x.2.1 (appIn e "clk" ck) dn c t w ash dl ps
      h1 h3 h5 h6 h7
    rw [hn]
    refine .inr ⟨2 * N - 1, by omega, 0, by omega, _, _, _, _, _, c, dl', ps, rfl, h2, hdw', h8, hd', ?_, ?_⟩
    · intro k j _ _ hk; omega
    · intro i j hi _ hit; omega
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, -, rfl⟩
      ⟨t', ht', ck', r', s', a', b', c', dl', ps', hb, hcw, hdw, hpw, hd, hp, hC⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨c'', dl'', ps'', hn, hcw', hdw', hpw', hd', hp', hC'⟩ :=
      next_busy (t := t') ⟨hN, hW, hA, hNW⟩ x.1 x.2.1 (by omega) (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
        _ _ _ hcw hdw hpw hd hp hC
    rw [hn]
    by_cases hf : t' + 1 = 2 * N
    · left
      have hc := c_final hN x.1 x.2.1 hcw' (by rw [← hf]; exact hC')
      subst hc
      simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t' + 1, by omega, _, _, _, _, _, c'', dl'', ps'', rfl, hcw', hdw', hpw', hd', hp', hC'⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', t', w', ash', dl', ps', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', t', w', ash', dl', ps', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩


theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "w", "ash", "dl", "ps"] : List String).Nodup
    decide⟩

theorem exprNames_rz (n we : Nat) (e : Expr2) : exprNames (rz n we e) = exprNames e := by
  unfold rz; split <;> simp [exprNames]

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ ctrlP N W :: genPs N W AccW := by simpa [mmD] using hp
  rcases mm_mem hm with rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨k, j, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, lineP, topP, rowP, crowP, coutP, nb, c32, sext, exprNames_rz, edgeClock,
      asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-! ## 9. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3) -/

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
  obtain ⟨t, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨w, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨ash, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨dl, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨ps, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain rfl := powerUp_nil.mp h13
  exact ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, w6, w7, w8, w9, w10, w11, w12, w13⟩

/-- **Termination from every power-up** (the cycle of `mm_cycle`). -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA) (fun σ => ⟨40, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, t, bz, w, ash, dl, ps, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t bz w ash dl ps kk 40 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c t bz w ash dl ps hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem xs_rz {d : Design2} {n we : Nat} {e : Expr2} (h : xsWidth d e = some we) : xsWidth d (rz n we e) = some n := by
  unfold rz; split
  · subst_vars; exact h
  · simp [xsWidth, h]

/-- The control passes rule 3. -/
theorem ctrl_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (ctrlP N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ctrlP, nb, c32, mmD, mmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem line_xsafe {N W AccW k : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hk : k < N) :
    xsProc (mmD N W AccW) (lineP N W k) = true := by
  have h1 : k * N * W + N * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (show k + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have h2 : k * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (by omega) hk; simpa using this
  have hA : xsWidth (mmD N W AccW) (.slice (.ident "A") (k * W) W) = some W := by
    simp [xsWidth, sigWidth, mmD, mmDecls, h2]
  have hS : xsWidth (mmD N W AccW) (.slice (.ident "ash") (k * W) W) = some W := by
    simp [xsWidth, sigWidth, mmD, mmDecls, h2]
  simp only [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, lineP, xs_rz hA, xs_rz hS]
  simp [binW, sigWidth, c32, mmD, mmDecls, LVec.ofInt, h1]

theorem top_xsafe {N W AccW j : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hj : j < N) :
    xsProc (mmD N W AccW) (topP W AccW j) = true := by
  have hB : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (by omega) hj; simpa using this
  have hB1 : j * W + W - 1 + 1 ≤ N * N * W := by omega
  have hC : j * AccW + AccW ≤ N * N * AccW := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) (i := 0) (by omega) hj; simpa using this
  have hD : W ≤ N * N * W := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  have hD1 : W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, topP, sext, mmD, mmDecls, hB, hB1,
    hC, hD, hD1]

theorem row_xsafe {N W AccW k j : Nat} (hW : 1 ≤ W) (hk : k + 1 < N) (hj : j < N) :
    xsProc (mmD N W AccW) (rowP N W AccW k j) = true := by
  have hC1 := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hk hj
  have hC0 := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) (show k < N by omega) hj
  have hB := Lib.rowMajor_window_le (M := N) (N := N) (w := W) hk hj
  have hB1 : ((k + 1) * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
  have hD : (k + 1) * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (j := 0) hk (by omega); simpa using this
  have hD1 : (k + 1) * N * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, rowP, sext, mmD, mmDecls, hB, hB1,
    hC1, hC0, hD, hD1]

theorem crow_xsafe {N W AccW i j : Nat} (hi : i + 1 < N) (hj : j < N) :
    xsProc (mmD N W AccW) (crowP N AccW i j) = true := by
  have hC1 := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have hC0 := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) (show i < N by omega) hj
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, binW, sigWidth, crowP, c32, mmD, mmDecls, LVec.ofInt, hC1, hC0]

theorem cout_xsafe {N W AccW j : Nat} (hN : 1 ≤ N) (hj : j < N) :
    xsProc (mmD N W AccW) (coutP N AccW j) = true := by
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) (show N - 1 < N by omega) hj
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, binW, sigWidth, coutP, c32, mmD, mmDecls, LVec.ofInt, hC]

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ ctrlP N W :: genPs N W AccW := by simpa [mmD] using hp
  rcases mm_mem hm with rfl | ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, j, hk, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ctrl_xsafe N W AccW
  · exact line_xsafe hN hW hk
  · exact top_xsafe hN hW hj
  · exact row_xsafe hW (by omega) hj
  · exact crow_xsafe (by omega) hj
  · exact cout_xsafe hN hj

/-- **The weight-stationary array satisfies the matmul statement (txtask-v2) at latency `2N`** (`8` at the
scoring point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA)
    (mm_disciplined N W AccW hN hW hA) (mm_terminatesPU N W AccW hN hW hA) (show 1 ≤ 2 * N by omega)
    (model N W AccW hN hW hA hNW) (mm_powerUp N W AccW hN hW hA) (mm_moore N W AccW hN hW hA)
    (mm_xsafe N W AccW hN hW hA)


end Submission
