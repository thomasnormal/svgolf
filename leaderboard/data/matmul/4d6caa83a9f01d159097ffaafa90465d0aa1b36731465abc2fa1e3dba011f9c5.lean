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
# A statically scheduled matrix multiplier (a timetable), latency `N + 4`

`solution.sv` has one time counter `t` (reset to the idle value `N + 4`, `0` on `start`, counting up to the
idle value and resting there) and slices that talk through stream registers loaded every cycle:
`ma`/`mb` (memory, shifted by a Read at `t < N`), the operand streams `sa`/`sb`, the product stream `sp`
(exact `2W`-bit products), the accumulator `acc` (load at `t = 2`, add at `2 < t ≤ N + 1`), the result stream
`sc`, and `C`, written from `sc` at `t = N + 3` together with `done`.

1. Agreement (`mm_sem_eq`): the loaded family is the hand-built `mmD`.
2. The clock step (`mm_profile`, `mm_cycle`) and the commit register by register (`commit_MS`).
3. The registers after one cycle (`next_*`), the values `t` cycles after a start (`BusyAt`).
4. The spec's arithmetic (`product_eq`, `accC_N`).
5. The phase model (`model`) and txtask-v2's rules.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `N + 4` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := N + 4

/-! ## 1. Agreement -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{n{x[lo+w-1]}}, x[lo +: w]}`: entry `x[lo +: w]` sign-extended by `n` bits. -/
def sext (x : String) (n lo w : Nat) : Expr2 :=
  .concat #[.repl n (.concat #[.slice (.ident x) (lo + w - 1) 1]), .slice (.ident x) lo w]

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- The time counter and `done`. -/
def ctrlP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "t" (LVec.ofInt 32 ((N : Int) + 4)), nb "done" ⟨#[.l0]⟩])
    (some (.ifStmt (.ident "start")
      (.block #[nb "t" (LVec.replicate 32 .l0), nb "done" ⟨#[.l0]⟩])
      (some (.block #[
        .ifStmt (.binary .lt (.ident "t") (c32 ((N : Int) + 4)))
          (.nbaAssign (.ident "t") (.binary .add (.ident "t") (c32 1))) none,
        .ifStmt (.binary .eq (.ident "t") (c32 ((N : Int) + 3))) (nb "done" ⟨#[.l1]⟩) none])))))

/-- MEM_A: load on `start`, Read (shift by one entry) at `t < N`. -/
def memAP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "ma") (.ident "A"))
    (some (.ifStmt (.binary .lt (.ident "t") (c32 N))
      (.nbaAssign (.ident "ma") (.binary (.shr false) (.ident "ma") (c32 W))) none)))

/-- MEM_B: load on `start`, Read (shift by one row) at `t < N`. -/
def memBP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "mb") (.ident "B"))
    (some (.ifStmt (.binary .lt (.ident "t") (c32 N))
      (.nbaAssign (.ident "mb") (.binary (.shr false) (.ident "mb") (.binary .mul (c32 N) (c32 W)))) none)))

/-- The stream `sb`: row 0 of MEM_B. -/
def sbP (N W : Nat) : Process2 := .alwaysFF "clk" (.nbaAssign (.ident "sb") (.slice (.ident "mb") 0 (N * W)))

/-- The result stream `sc`. -/
def scP : Process2 := .alwaysFF "clk" (.nbaAssign (.ident "sc") (.ident "acc"))

/-- MEM_C: the Write of `sc` at `t = N + 3`. -/
def wrP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.binary .eq (.ident "t") (c32 ((N : Int) + 3))) (.nbaAssign (.ident "C") (.ident "sc")) none)

/-- Lane `i` of the stream `sa`: entry 0 of row `i` of MEM_A. -/
def saP (N W i : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "sa" (i * W) W) (.slice (.ident "ma") (i * N * W) W))

/-- MXM lane `(i, j)`: the exact `2W`-bit product of `sa` lane `i` and `sb` lane `j`. -/
def spP (N W i j : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "sp" ((i * N + j) * (2 * W)) (2 * W))
    (.binary .mul (sext "sa" W (i * W) W) (sext "sb" W (j * W) W)))

/-- VXM lane `(i, j)`: load at `t = 2`, add at `2 < t ≤ N + 1`. -/
def accP (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.binary .eq (.ident "t") (c32 2))
    (.nbaAssign (.slice "acc" ((i * N + j) * AccW) AccW)
      (.resize AccW (sext "sp" AccW ((i * N + j) * (2 * W)) (2 * W))))
    (some (.ifStmt (.binary .gt (.ident "t") (c32 2))
      (.ifStmt (.binary .le (.ident "t") (c32 ((N : Int) + 1)))
        (.nbaAssign (.slice "acc" ((i * N + j) * AccW) AccW)
          (.resize AccW (.binary .add (.resize (AccW + 2 * W) (.slice (.ident "acc") ((i * N + j) * AccW) AccW))
            (sext "sp" AccW ((i * N + j) * (2 * W)) (2 * W))))) none) none)))

/-- The declarations: `A`, `B`, `ma`, `mb` at `wa` bits, `sa`, `sb` at `wn`, `sp` at `wp`, `C`, `acc`, `sc` at
`wc`. -/
def mmDecls (wa wn wp wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "t", width := 32 },
   { name := "ma", width := wa }, { name := "mb", width := wa }, { name := "sa", width := wn },
   { name := "sb", width := wn }, { name := "sp", width := wp }, { name := "acc", width := wc },
   { name := "sc", width := wc }]

/-- The module-level processes, in source order. -/
def mmTop (N W : Nat) : List Process2 := [ctrlP N, memAP N W, memBP N W, sbP N W, scP, wrP N]

def saPs (N W : Nat) : List Process2 := (List.range N).map (saP N W)

def spPs (N W : Nat) : List Process2 := (List.range N).flatMap fun i => (List.range N).map fun j => spP N W i j

def accPs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => accP N W AccW i j

/-- All processes. -/
def mmPs (N W AccW : Nat) : List Process2 := mmTop N W ++ saPs N W ++ spPs N W ++ accPs N W AccW

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * W) (N * N * (2 * W)) (N * N * AccW)).toArray
  processes := (mmPs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("T_IDLE", N + 4), ("T_WRITE", N + 3), ("T_ACC_LAST", N + 1), ("T_ACC_FIRST", 2), ("T_READ_END", N),
      ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("T_READ_END", 32), ("T_ACC_FIRST", 32), ("T_ACC_LAST", 32),
      ("T_WRITE", 32), ("T_IDLE", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "t", "ma", "mb", "sa", "sb", "sp", "acc", "sc"].map (·, 1)

theorem mm_decls (N W AccW : Int) :
    buildDecls (mmEnv N W AccW) design.pdesign.decls =
      .ok (mmDecls ((N * N * W - 1).natAbs + 1) ((N * W - 1).natAbs + 1) ((N * N * 2 * W - 1).natAbs + 1)
        ((N * N * AccW - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, mmDecls, Gen2.except_ok_bind]

theorem mm_elems (N W AccW : Int) : buildElems (mmEnv N W AccW) design.pdesign.decls = .ok mmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, mmElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev mmE (N W AccW : Nat) : IEnv :=
  (mmEnv N W AccW).withDecls (mmDecls (N * N * W) (N * W) (N * N * (2 * W)) (N * N * AccW))

theorem mm_top (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = mmTop N W := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pNW := Nat.mul_pos hN hW
  have hNNW : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
  have h1 : (1 : Int) ≤ N * N * W := by rw [← Int.natCast_mul, ← Int.natCast_mul]; omega
  have h2 : ¬ ((N : Int) * W - 1 < 0) := by rw [← Int.natCast_mul]; omega
  have h3 : min ((N : Int) * W - 1) 0 = 0 := by rw [← Int.natCast_mul]; omega
  have h4 : max ((N : Int) * W - 1) 0 = N * W - 1 := by rw [← Int.natCast_mul]; omega
  have h5 : ((N : Int) * W - 1 - 0 + 1).toNat = N * W := by rw [← Int.natCast_mul]; omega
  have hcA : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  have h6 : (N : Int) * W - 1 < ((N * N * W : Nat) : Int) := by rw [← Int.natCast_mul]; omega
  have h7 : ((N : Int) * W).toNat = N * W := by rw [← Int.natCast_mul]; rfl
  have h8 : (N : Int) * W - 1 < (N : Int) * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul, ← Int.natCast_mul]; omega
  have hmode : (PartMode.range == PartMode.range) = true := rfl
  sv2_inst_simp [instStmt2, instStmts2, design.pdesign, mmEnv, mmScope, mmDecls, mmElems, mmTop, ctrlP, memAP,
    memBP, sbP, scP, wrP,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2, *]
  try and_intros
  all_goals first | rfl | decide

/-- The templates of the three generate loops. -/
def saT : PProcess :=
  match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _] => p
  | _ => .alwaysFF "" (.block [])

def spT : PProcess :=
  match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])

def accT : PProcess :=
  match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

macro "pe_simp" : tactic => `(tactic| sv2_inst_simp [saT, spT, accT, evalSized, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2, design.pdesign,
  mmEnv, mmScope, mmDecls, mmElems, saP, spP, accP, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, *])

theorem sa_inst (N W AccW i : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N) :
    instProcess2 ((mmE N W AccW).bindVal "i" i) mmElems saT = saP N W i := by
  have f1 : (1 : Int) ≤ N * W := by rw [← Int.natCast_mul]; have := Nat.mul_pos hN hW; omega
  have f2 : (1 : Int) ≤ N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hW; omega
  have f3 : (1 : Int) ≤ N * N * 2 * W := by
    have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
    rw [e]; have := Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega); omega
  have f4 : (1 : Int) ≤ N * N * AccW := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hA; omega
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pNW := Nat.mul_pos hN hW
  have hW0 : (0 : Int) < W := by omega
  have hcA : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pW
  have hcN : ((N : Int) * W - 1).natAbs + 1 = N * W := by
    rw [← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pNW
  have hs := Lib.window_bounds_of_natCast ((i : Int) * W) (N * W)
    (by have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this)
    hW (by simp) (by simp)
  have ha := Lib.window_bounds_of_natCast ((i : Int) * N * W) (N * N * W)
    (Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega)) hW (by simp) (by simp)
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  pe_simp
  repeat (unfold instExpr2; pe_simp)

theorem sp_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N) (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems spT = spP N W i j := by
  have f1 : (1 : Int) ≤ N * W := by rw [← Int.natCast_mul]; have := Nat.mul_pos hN hW; omega
  have f2 : (1 : Int) ≤ N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hW; omega
  have f3 : (1 : Int) ≤ N * N * 2 * W := by
    have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
    rw [e]; have := Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega); omega
  have f4 : (1 : Int) ≤ N * N * AccW := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hA; omega
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pNW := Nat.mul_pos hN hW
  have pP := Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega)
  have hW0 : (0 : Int) < W := by omega
  have hcN : ((N : Int) * W - 1).natAbs + 1 = N * W := by
    rw [← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pNW
  have hcP : ((N : Int) * N * 2 * W - 1).natAbs + 1 = N * N * (2 * W) := by
    have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
    rw [e]; exact Lib.natAbs_sub_one_add_one pP
  have hp := Lib.window_bounds_of_natCast (((i : Int) * N + j) * (2 * W)) (N * N * (2 * W))
    (Lib.rowMajor_window_le (w := 2 * W) hi hj) (by omega) (by simp) (by simp)
  push_cast at hp
  have hW2 : (0 : Int) < 2 * W := by omega
  have h2W : (2 * (W : Int)).toNat = 2 * W := by omega
  have hsa := Lib.window_bounds_of_natCast ((i : Int) * W) (N * W)
    (by have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this)
    hW (by simp) (by simp)
  have hsb := Lib.window_bounds_of_natCast ((j : Int) * W) (N * W)
    (by have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this)
    hW (by simp) (by simp)
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hlt1 : ¬ W + W < 2 * W := by omega
  have hle1 : W + W = 2 * W := by omega
  pe_simp
  repeat (unfold instExpr2; pe_simp)
  try and_intros
  all_goals first | rfl | decide

theorem acc_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N) (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems accT = accP N W AccW i j := by
  have f1 : (1 : Int) ≤ N * W := by rw [← Int.natCast_mul]; have := Nat.mul_pos hN hW; omega
  have f2 : (1 : Int) ≤ N * N * W := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hW; omega
  have f3 : (1 : Int) ≤ N * N * 2 * W := by
    have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
    rw [e]; have := Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega); omega
  have f4 : (1 : Int) ≤ N * N * AccW := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; have := Nat.mul_pos (Nat.mul_pos hN hN) hA; omega
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have pP := Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega)
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hcC : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW := by
    rw [← Int.natCast_mul, ← Int.natCast_mul]; exact Lib.natAbs_sub_one_add_one pA
  have hcP : ((N : Int) * N * 2 * W - 1).natAbs + 1 = N * N * (2 * W) := by
    have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
      push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
    rw [e]; exact Lib.natAbs_sub_one_add_one pP
  have hC := Lib.window_bounds_of_natCast (((i : Int) * N + j) * AccW) (N * N * AccW)
    (Lib.rowMajor_window_le (w := AccW) hi hj) hA (by simp) (by simp)
  have hp := Lib.window_bounds_of_natCast (((i : Int) * N + j) * (2 * W)) (N * N * (2 * W))
    (Lib.rowMajor_window_le (w := 2 * W) hi hj) (by omega) (by simp) (by simp)
  push_cast at hp
  have hW2 : (0 : Int) < 2 * W := by omega
  have h2W : (2 * (W : Int)).toNat = 2 * W := by omega
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hlt1 : ¬ AccW + 2 * W < AccW := by omega
  have hle1 : ¬ AccW + 2 * W ≤ AccW := by omega
  pe_simp
  repeat (unfold instExpr2; pe_simp)
  try and_intros
  all_goals first | rfl | decide

/-- `for (g = 0; g < N; g++) body`. -/
def genN (lbl g : String) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) (.paramRef "N" none))
    (.unary .inc (.genvarRef g)) (some 4) body

theorem mm_gens_src : design.pdesign.generates = [genN "g_sa" "i" ([saT].map .process),
    genN "g_mxm_row" "i" [genN "g_mxm_col" "j" ([spT].map .process)],
    genN "g_vxm_row" "i" [genN "g_vxm_col" "j" ([accT].map .process)]] := rfl

/-- One generate loop over `i < N`. -/
theorem gen1_expand (N W AccW F : Nat) (hF : N < F) (lbl : String) (T : PProcess) (P : Nat → Process2)
    (hT : ∀ i, i < N → instProcess2 ((mmE N W AccW).bindVal "i" i) mmElems T = P i) :
    (genN lbl "i" ([T].map .process)).expand2 (mmE N W AccW) mmElems F = .ok ((List.range N).map P) := by
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  rw [genN, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
    (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv]))
    (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv])) (by simpa using hF)]
  simp only [intRange_zero, Int.sub_zero, Int.toNat_natCast, List.flatMap_map, List.map_cons, List.map_nil,
    Gen2.flatMap_singleton_map]
  congr 1
  exact List.map_congr_left fun i hi => hT i (List.mem_range.mp hi)

/-- Two nested generate loops over `i, j < N`, row-major. -/
theorem gen2_expand (N W AccW F : Nat) (hF : N < F) (l1 l2 : String) (T : PProcess) (P : Nat → Nat → Process2)
    (hT : ∀ i j, i < N → j < N → instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems T = P i j) :
    (genN l1 "i" [genN l2 "j" ([T].map .process)]).expand2 (mmE N W AccW) mmElems F =
      .ok ((List.range N).flatMap fun i => (List.range N).map fun j => P i j) := by
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  rw [genN, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [T].map (instProcess2 (((mmE N W AccW).bindVal "i" v).bindVal "j" w) mmElems))
      (evalInt_int 0) (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv]))
      (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hNv])) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map]
    congr 1
    simp only [List.flatMap_def]
    congr 1
    refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
    exact hT i j (List.mem_range.mp hi) (List.mem_range.mp hj)
  · intro v _ _
    apply expandList2_singleton_ok
    have hv : ((mmE N W AccW).bindVal "i" v).vals.lookup "N" = some (N : Int) := by
      simp [IEnv.bindVal, List.lookup, hNv]
    rw [genN, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun _ => isInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hv]))
      (fun _ => evalInt_paramRef_of (by rw [vals_lookup_bindVal_ne _ (by decide), hv]))
      (by simpa using hF)]
    simp

/-- **The three generate loops expand to the lanes**: `sa` lanes, then the MXM lanes, then the VXM lanes. -/
theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates =
      .ok (saPs N W ++ (spPs N W ++ accPs N W AccW)) := by
  rw [mm_gens_src]
  refine expandList2_cons_ok (gen1_expand N W AccW F hF _ saT (saP N W) fun i hi => sa_inst N W AccW i hN hW hA hi)
    (expandList2_cons_ok (gen2_expand N W AccW F hF _ _ spT (spP N W) fun i j hi hj => sp_inst N W AccW i j hN hW hA hi hj)
      (expandList2_singleton_ok
        (gen2_expand N W AccW F hF _ _ accT (accP N W AccW) fun i j hi hj => acc_inst N W AccW i j hN hW hA hi hj)))

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (mmDecls (N * N * W) (N * W) (N * N * (2 * W)) (N * N * AccW))
        mmElems (saPs N W ++ (spPs N W ++ accPs N W AccW))) := by
  have hd := mm_decls N W AccW
  have e : ((N : Int) * N * 2 * W) = ((N * N * (2 * W) : Nat) : Int) := by
    push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W]
  rw [← Int.natCast_mul N N, ← Int.natCast_mul (N * N) W,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hW), ← Int.natCast_mul (N * N) AccW,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) hA), ← Int.natCast_mul N W,
    Lib.natAbs_sub_one_add_one (Nat.mul_pos hN hW)] at hd
  rw [show ((N * N : Nat) : Int) * 2 * W = ((N * N * (2 * W) : Nat) : Int) by push_cast; rw [Int.mul_assoc ((N : Int) * N) 2 W],
    Lib.natAbs_sub_one_add_one (Nat.mul_pos (Nat.mul_pos hN hN) (show 0 < 2 * W by omega))] at hd
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv _ _ _) hd (mm_elems _ _ _)
    (mm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList = mmPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_top N W AccW hN hW]
  simp [design.pdesign, mmPs]

/-- Two processes drive disjoint windows. -/
abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

theorem sa_mem {N W : Nat} {p : Process2} (hp : p ∈ saPs N W) : ∃ i, i < N ∧ p = saP N W i := by
  simp only [saPs, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, hi, rfl⟩

theorem sp_mem {N W : Nat} {p : Process2} (hp : p ∈ spPs N W) : ∃ i j, i < N ∧ j < N ∧ p = spP N W i j := by
  simp only [spPs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp
  exact ⟨i, j, hi, hj, rfl⟩

theorem acc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ accPs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p = accP N W AccW i j := by
  simp only [accPs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp
  exact ⟨i, j, hi, hj, rfl⟩

theorem top_mem {N W : Nat} {p : Process2} (hp : p ∈ mmTop N W) :
    p = ctrlP N ∨ p = memAP N W ∨ p = memBP N W ∨ p = sbP N W ∨ p = scP ∨ p = wrP N := by
  simpa [mmTop] using hp

/-- The window names of each process. -/
theorem names_top {N W : Nat} {p : Process2} (hp : p ∈ mmTop N W) :
    ∀ a ∈ p.procWins, a.1 = "t" ∨ a.1 = "done" ∨ a.1 = "ma" ∨ a.1 = "mb" ∨ a.1 = "sb" ∨ a.1 = "sc" ∨ a.1 = "C" := by
  rcases top_mem hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ctrlP, memAP, memBP, sbP, scP, wrP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
      Stmt2.drvWinsList, Lhs2.drvWins]

theorem names_sa {N W i : Nat} : ∀ a ∈ (saP N W i).procWins, a = ("sa", some (i * W, W)) := by
  simp [saP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]

theorem names_sp {N W i j : Nat} : ∀ a ∈ (spP N W i j).procWins, a = ("sp", some ((i * N + j) * (2 * W), 2 * W)) := by
  simp [spP, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]

theorem names_acc {N W AccW i j : Nat} :
    ∀ a ∈ (accP N W AccW i j).procWins, a = ("acc", some ((i * N + j) * AccW, AccW)) := by
  simp [accP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins]

theorem disj_of_ne {p q : Process2} (h : ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.1 ≠ b.1) : Disj p q := by
  intro a ha b hb
  simp [DrvWin.overlaps, h a ha b hb]

theorem disj_win {n : String} {l w l' w' : Nat} (h : l + w ≤ l' ∨ l' + w' ≤ l) :
    DrvWin.overlaps (n, some (l, w)) (n, some (l', w')) = false := by
  simp [DrvWin.overlaps]; omega

/-- The processes drive pairwise disjoint windows. -/
theorem mm_pairwise (N W AccW : Nat) : (mmPs N W AccW).Pairwise Disj := by
  have htop : (mmTop N W).Pairwise Disj := by
    simp [mmTop, Disj, ctrlP, memAP, memBP, sbP, scP, wrP, nb, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
  have hsa : (saPs N W).Pairwise Disj := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {i i'} _ _ h => ?_)
    intro a ha b hb
    rw [names_sa a ha, names_sa b hb]
    exact disj_win (.inl (rowMajor_le (K := W) h))
  have hsp : (spPs N W).Pairwise Disj := by
    refine pairwise_flatMap_range (fun i _ => ?_) ?_
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {j j'} _ _ h => ?_)
      intro a ha b hb
      rw [names_sp a ha, names_sp b hb]
      exact disj_win (.inl (rowMajor_le (K := 2 * W) (by omega)))
    · intro i i' hii _ p hp q hq
      simp only [List.mem_map, List.mem_range] at hp hq
      obtain ⟨j, hj, rfl⟩ := hp
      obtain ⟨j', -, rfl⟩ := hq
      intro a ha b hb
      rw [names_sp a ha, names_sp b hb]
      exact disj_win (.inl (rowMajor_le (K := 2 * W) (by have := rowMajor_le (K := N) hii; omega)))
  have hacc : (accPs N W AccW).Pairwise Disj := by
    refine pairwise_flatMap_range (fun i _ => ?_) ?_
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun {j j'} _ _ h => ?_)
      intro a ha b hb
      rw [names_acc a ha, names_acc b hb]
      exact disj_win (.inl (rowMajor_le (K := AccW) (by omega)))
    · intro i i' hii _ p hp q hq
      simp only [List.mem_map, List.mem_range] at hp hq
      obtain ⟨j, hj, rfl⟩ := hp
      obtain ⟨j', -, rfl⟩ := hq
      intro a ha b hb
      rw [names_acc a ha, names_acc b hb]
      exact disj_win (.inl (rowMajor_le (K := AccW) (by have := rowMajor_le (K := N) hii; omega)))
  refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨htop, hsa, ?_⟩, hsp, ?_⟩,
    hacc, ?_⟩
  · intro p hp q hq
    obtain ⟨i, -, rfl⟩ := sa_mem hq
    refine disj_of_ne fun a ha b hb => ?_
    rw [names_sa b hb]
    rcases names_top hp a ha with h | h | h | h | h | h | h <;> rw [h] <;> simp
  · intro p hp q hq
    obtain ⟨i, j, -, -, rfl⟩ := sp_mem hq
    refine disj_of_ne fun a ha b hb => ?_
    rw [names_sp b hb]
    rcases List.mem_append.mp hp with hp | hp
    · rcases names_top hp a ha with h | h | h | h | h | h | h <;> rw [h] <;> simp
    · obtain ⟨i', -, rfl⟩ := sa_mem hp; rw [names_sa a ha]; simp
  · intro p hp q hq
    obtain ⟨i, j, -, -, rfl⟩ := acc_mem hq
    refine disj_of_ne fun a ha b hb => ?_
    rw [names_acc b hb]
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · rcases names_top hp a ha with h | h | h | h | h | h | h <;> rw [h] <;> simp
      · obtain ⟨i', -, rfl⟩ := sa_mem hp; rw [names_sa a ha]; simp
    · obtain ⟨i', j', -, -, rfl⟩ := sp_mem hp; rw [names_sp a ha]; simp

theorem mm_ff {N W AccW : Nat} : ∀ p ∈ mmPs N W AccW, ∃ c b, p = .alwaysFF c b := by
  intro p hp
  simp only [mmPs, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases top_mem hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩
  · obtain ⟨i, -, rfl⟩ := sa_mem hp; exact ⟨_, _, rfl⟩
  · obtain ⟨i, j, -, -, rfl⟩ := sp_mem hp; exact ⟨_, _, rfl⟩
  · obtain ⟨i, j, -, -, rfl⟩ := acc_mem hp; exact ⟨_, _, rfl⟩

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mmPs N W AccW) = true := by
  apply driversOk_of_ff mm_ff ?_ (mm_pairwise N W AccW)
  simp only [List.mem_flatMap, mmPs, List.mem_append]
  rintro n ⟨p, hp, hn⟩
  rcases hp with ((hp | hp) | hp) | hp
  · rcases top_mem hp with rfl | rfl | rfl | rfl | rfl | rfl <;> revert n <;>
      simp [ctrlP, memAP, memBP, sbP, scP, wrP, nb, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] <;> decide
  · obtain ⟨i, -, rfl⟩ := sa_mem hp; revert n
    simp [saP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]; decide
  · obtain ⟨i, j, -, -, rfl⟩ := sp_mem hp; revert n
    simp [spP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]; decide
  · obtain ⟨i, j, -, -, rfl⟩ := acc_mem hp; revert n
    simp [accP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins]; decide

/-- **The loaded family is `mmD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    design.sem N W AccW = mmD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA]; exact mm_driversOk N W AccW)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, mm_top N W AccW hN hW, mmD]
  simp [design.pdesign, mmPs]

/-! ## 2. G0's clock step for the loaded family, at every `(N, W, AccW)` -/

/-- **`mmD` is in G0's decidable FF-only profile at every `(N, W, AccW)`**. -/
theorem mm_profile (N W AccW : Nat) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simp only [mmD, List.toList_toArray]; exact mm_pairwise N W AccW)⟩
  simp [mmD, mmPs, mmTop, saPs, spPs, accPs, ctrlP, memAP, memBP, sbP, scP, wrP, saP, spP, accP, nb,
    List.all_flatMap, List.all_map, List.all_append, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, mmDecls]

/-- The 15 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("t", t),
    ("ma", ma), ("mb", mb), ("sa", sa), ("sb", sb), ("sp", sp), ("acc", acc), ("sc", sc)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c t ma mb sa sb sp acc sc) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c t ma mb sa sb sp acc sc := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The counter's updates. -/
def ctrlQ (N : Nat) (r s dn t : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "t" t (LVec.ofInt 32 ((N : Int) + 4)), wr "done" dn ⟨#[.l0]⟩]
  else if s.condTrue then [wr "t" t (LVec.replicate 32 .l0), wr "done" dn ⟨#[.l0]⟩]
  else (if (LVec.ofLogic (t.lt (LVec.ofInt 32 ((N : Int) + 4)))).condTrue then
      [wr "t" t (t.add (LVec.ofInt 32 1))] else []) ++
    (if (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 ((N : Int) + 3)))).condTrue then [wr "done" dn ⟨#[.l1]⟩] else [])

def memAQ (N W : Nat) (s t a ma : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "ma" ma a]
  else if (LVec.ofLogic (t.lt (LVec.ofInt 32 (N : Int)))).condTrue then
    [wr "ma" ma (ma.shr (LVec.ofInt 32 (W : Int)))] else []

def memBQ (N W : Nat) (s t b mb : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "mb" mb b]
  else if (LVec.ofLogic (t.lt (LVec.ofInt 32 (N : Int)))).condTrue then
    [wr "mb" mb (mb.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))] else []

def sbQ (N W : Nat) (mb sb : LVec) : NbaQueue2 := [wr "sb" sb (mb.extract 0 (N * W))]

def scQ (acc sc : LVec) : NbaQueue2 := [wr "sc" sc acc]

def wrQ (N : Nat) (t sc c : LVec) : NbaQueue2 :=
  if (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 ((N : Int) + 3)))).condTrue then [wr "C" c sc] else []

/-- `{{n{v[lo+w-1]}}, v[lo +: w]}`, evaluated. -/
def sxv (v : LVec) (n lo w : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec n (LVec.concatMany #[v.extract (lo + w - 1) 1]), v.extract lo w]

def saQ (N W : Nat) (ma : LVec) (i : Nat) : NbaQueue2 := [("sa", i * W, (ma.extract (i * N * W) W).resizeU W)]

/-- The product of MXM lane `(i, j)`, evaluated. -/
def spV (W : Nat) (sa sb : LVec) (i j : Nat) : LVec := (sxv sa W (i * W) W).mul (sxv sb W (j * W) W)

def spQ (N W : Nat) (sa sb : LVec) (i j : Nat) : NbaQueue2 :=
  [("sp", (i * N + j) * (2 * W), (spV W sa sb i j).resizeU (2 * W))]

/-- The VXM load and add of lane `r`, evaluated. -/
def ldV (W AccW : Nat) (sp : LVec) (r : Nat) : LVec := (sxv sp AccW (r * (2 * W)) (2 * W)).resizeU AccW

def adV (W AccW : Nat) (sp acc : LVec) (r : Nat) : LVec :=
  (((acc.extract (r * AccW) AccW).resizeU (AccW + 2 * W)).add (sxv sp AccW (r * (2 * W)) (2 * W))).resizeU AccW

def accQ (N W AccW : Nat) (t sp acc : LVec) (i j : Nat) : NbaQueue2 :=
  if (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 2))).condTrue then
    [("acc", (i * N + j) * AccW, (ldV W AccW sp (i * N + j)).resizeU AccW)]
  else if (LVec.ofLogic (t.gt (LVec.ofInt 32 2))).condTrue then
    (if (LVec.ofLogic (t.le (LVec.ofInt 32 ((N : Int) + 1)))).condTrue then
      [("acc", (i * N + j) * AccW, (adV W AccW sp acc (i * N + j)).resizeU AccW)] else [])
  else []

theorem ctrl_run (N F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (ctrlP N) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, ctrlQ N r s dn t) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (t.lt (LVec.ofInt 32 ((N : Int) + 4)))).condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 ((N : Int) + 3)))).condTrue = true <;>
    simp [ctrlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem memA_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (memAP N W) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, memAQ N W s t a ma) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold memAQ
  by_cases h2 : s.condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (t.lt (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp [memAP, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h2, h3]

theorem memB_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (memBP N W) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, memBQ N W s t b mb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold memBQ
  by_cases h2 : s.condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (t.lt (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp [memBP, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h2, h3]

theorem sb_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (sbP N W) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, sbQ N W mb sb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [sbP, sbQ, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup, wr]

theorem sc_run (F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] scP =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, scQ acc sc) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [scP, scQ, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup, wr]

theorem wr_run (N F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (wrP N) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, wrQ N t sc c) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold wrQ
  by_cases h4 : (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 ((N : Int) + 3)))).condTrue = true <;>
    simp [wrP, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h4]

theorem sa_run (N W i F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (saP N W i) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, saQ N W ma i) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [saP, saQ, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup]

theorem sp_run (N W i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (spP N W i j) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, spQ N W sa sb i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [spP, spQ, spV, sext, sxv, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2, resolveLhs2,
    readSignal, MS, SvState.lookup, evalBinOp]

theorem acc_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c t ma mb sa sb sp acc sc) [] (accP N W AccW i j) =
      .ok (MS ck r s a b dn c t ma mb sa sb sp acc sc, accQ N W AccW t sp acc i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold accQ
  by_cases h1 : (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 2))).condTrue = true <;>
    by_cases h2 : (LVec.ofLogic (t.gt (LVec.ofInt 32 2))).condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (t.le (LVec.ofInt 32 ((N : Int) + 1)))).condTrue = true <;>
    simp [accP, ldV, adV, sext, sxv, c32, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2,
      resolveLhs2, readSignal, MS, SvState.lookup, evalBinOp, h1, h2, h3]

/-- The MXM and VXM queues, row-major. -/
abbrev saQs (N W : Nat) (ma : LVec) : NbaQueue2 := (List.range N).flatMap (saQ N W ma)
abbrev spQs (N W : Nat) (sa sb : LVec) : NbaQueue2 := (List.range N).flatMap fun i => (List.range N).flatMap (spQ N W sa sb i)
abbrev accQs (N W AccW : Nat) (t sp acc : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap (accQ N W AccW t sp acc i)

/-- One cycle's queue, from the pre-edge (inputs applied) values. -/
def mmQ (N W AccW : Nat) (r s a b dn c t ma mb sa sb sp acc sc : LVec) : NbaQueue2 :=
  ctrlQ N r s dn t ++ (memAQ N W s t a ma ++ (memBQ N W s t b mb ++ (sbQ N W mb sb ++ (scQ acc sc ++
    (wrQ N t sc c ++ (saQs N W ma ++ (spQs N W sa sb ++ accQs N W AccW t sp acc)))))))

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c t ma mb sa sb sp acc sc) (mmQ N W AccW r s a b dn c t ma mb sa sb sp acc sc)

theorem mm_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPs N W AccW) :
    p = ctrlP N ∨ p = memAP N W ∨ p = memBP N W ∨ p = sbP N W ∨ p = scP ∨ p = wrP N ∨
      (∃ i, p = saP N W i) ∨ (∃ i j, p = spP N W i j) ∨ (∃ i j, p = accP N W AccW i j) := by
  simp only [mmPs, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · rcases top_mem hp with h | h | h | h | h | h <;> simp [h]
  · obtain ⟨i, -, rfl⟩ := sa_mem hp; exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, rfl⟩))))))
  · obtain ⟨i, j, -, -, rfl⟩ := sp_mem hp; exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, j, rfl⟩)))))))
  · obtain ⟨i, j, -, -, rfl⟩ := acc_mem hp; exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨i, j, rfl⟩)))))))

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus entry, any
state of the design's shape, every fuel from 30). -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c t ma mb sa sb sp acc sc) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c t ma mb sa sb sp acc sc, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ mmPs N W AccW := by simpa [mmD] using hp
    rcases mm_mem hm with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl
  rw [mm_sem_eq N W AccW hN hW hA, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD, List.toList_toArray, mmPs, mmTop, saPs, spPs, accPs, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc, List.flatMap_assoc, List.flatMap_map,
      ctrl_run N F hF, memA_run N W F hF, memB_run N W F hF, sb_run N W F hF, sc_run F hF, wr_run N F hF,
      sa_run N W _ F hF, sp_run N W _ _ F hF, acc_run N W AccW _ _ F hF, mmNext, mmQ]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ mmPs N W AccW :=
      List.mem_of_getElem? (by simpa [mmD] using hp : (mmPs N W AccW)[i]? = some p)
    rcases mm_mem hm with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
    · exact ⟨_, ctrl_run N F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, memA_run N W F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, memB_run N W F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, sb_run N W F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, sc_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, wr_run N F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, sa_run N W i F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, sp_run N W i j F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨_, acc_run N W AccW i j F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · rw [apply_mm]; simp [MS]

/-! ### The commit, register by register -/

/-- One write's effect on the register `n` (old value `x`). -/
abbrev up (n : String) (u : String × Nat × LVec) (x : LVec) : LVec :=
  if u.1 = n then x.insertAt u.2.1 u.2.2 else x

theorem nbaStep_MS (u : String × Nat × LVec) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    nbaStep (MS ck r s a b dn c t ma mb sa sb sp acc sc) u =
      MS (up "clk" u ck) (up "rst" u r) (up "start" u s) (up "A" u a) (up "B" u b) (up "done" u dn) (up "C" u c)
        (up "t" u t) (up "ma" u ma) (up "mb" u mb) (up "sa" u sa) (up "sb" u sb) (up "sp" u sp) (up "acc" u acc)
        (up "sc" u sc) := by
  obtain ⟨n, lo, v⟩ := u
  by_cases h1 : n = "clk"; · subst h1; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h2 : n = "rst"; · subst h2; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h3 : n = "start"; · subst h3; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h4 : n = "A"; · subst h4; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h5 : n = "B"; · subst h5; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h6 : n = "done"; · subst h6; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h7 : n = "C"; · subst h7; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h8 : n = "t"; · subst h8; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h9 : n = "ma"; · subst h9; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h10 : n = "mb"; · subst h10; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h11 : n = "sa"; · subst h11; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h12 : n = "sb"; · subst h12; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h13 : n = "sp"; · subst h13; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h14 : n = "acc"; · subst h14; simp [nbaStep, MS, SvState.lookup, SvState.set]
  by_cases h15 : n = "sc"; · subst h15; simp [nbaStep, MS, SvState.lookup, SvState.set]
  have k : ∀ m : String, m ≠ n → (m == n) = false := fun m h => by simp [h]
  simp [nbaStep, MS, SvState.lookup, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
    k "clk" (Ne.symm h1), k "rst" (Ne.symm h2), k "start" (Ne.symm h3), k "A" (Ne.symm h4), k "B" (Ne.symm h5),
    k "done" (Ne.symm h6), k "C" (Ne.symm h7), k "t" (Ne.symm h8), k "ma" (Ne.symm h9), k "mb" (Ne.symm h10),
    k "sa" (Ne.symm h11), k "sb" (Ne.symm h12), k "sp" (Ne.symm h13), k "acc" (Ne.symm h14), k "sc" (Ne.symm h15)]

/-- **A commit acts on each register separately**: register `n` gets the writes to `n`, in order. -/
theorem commit_MS : ∀ (q : NbaQueue2) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec),
    commitNba2 (MS ck r s a b dn c t ma mb sa sb sp acc sc) q =
      MS (nbaFold "clk" q ck) (nbaFold "rst" q r) (nbaFold "start" q s) (nbaFold "A" q a) (nbaFold "B" q b)
        (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "t" q t) (nbaFold "ma" q ma) (nbaFold "mb" q mb)
        (nbaFold "sa" q sa) (nbaFold "sb" q sb) (nbaFold "sp" q sp) (nbaFold "acc" q acc) (nbaFold "sc" q sc)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | u :: q, ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc => by
    rw [commitNba2_cons, nbaStep_MS, commit_MS q]; rfl

theorem nbaFold_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 : u.1 ≠ n := h u List.mem_cons_self
    have h2 : ∀ u' ∈ q, u'.1 ≠ n := fun u' hu' => h u' (List.mem_cons_of_mem _ hu')
    show nbaFold n q (if u.1 = n then x.insertAt u.2.1 u.2.2 else x) = x
    rw [if_neg h1, nbaFold_ne h2]

section names
variable {N W AccW : Nat} {r s a b dn c t ma mb sa sb sp acc sc : LVec} {n : String}

theorem fold_ctrlQ (h1 : "t" ≠ n) (h2 : "done" ≠ n) (x : LVec) : nbaFold n (ctrlQ N r s dn t) x = x := by
  unfold ctrlQ
  repeat' split
  all_goals simp [nbaFold, h1, h2]

theorem fold_memAQ (h : "ma" ≠ n) (x : LVec) : nbaFold n (memAQ N W s t a ma) x = x := by
  unfold memAQ
  repeat' split
  all_goals simp [nbaFold, h]

theorem fold_memBQ (h : "mb" ≠ n) (x : LVec) : nbaFold n (memBQ N W s t b mb) x = x := by
  unfold memBQ
  repeat' split
  all_goals simp [nbaFold, h]

theorem fold_sbQ (h : "sb" ≠ n) (x : LVec) : nbaFold n (sbQ N W mb sb) x = x := by
  simp [sbQ, nbaFold, h]

theorem fold_scQ (h : "sc" ≠ n) (x : LVec) : nbaFold n (scQ acc sc) x = x := by
  simp [scQ, nbaFold, h]

theorem fold_wrQ (h : "C" ≠ n) (x : LVec) : nbaFold n (wrQ N t sc c) x = x := by
  unfold wrQ
  repeat' split
  all_goals simp [nbaFold, h]

theorem fold_saQs (h : "sa" ≠ n) (x : LVec) : nbaFold n (saQs N W ma) x = x :=
  nbaFold_flatMap_eq_self (fun _ _ => by simp [saQ, nbaFold, h]) _ x

theorem fold_spQs (h : "sp" ≠ n) (x : LVec) : nbaFold n (spQs N W sa sb) x = x :=
  nbaFold_flatMap_eq_self (fun _ _ => nbaFold_flatMap_eq_self (fun _ _ => by simp [spQ, nbaFold, h]) _ _) _ x

theorem fold_accQs (h : "acc" ≠ n) (x : LVec) : nbaFold n (accQs N W AccW t sp acc) x = x :=
  nbaFold_flatMap_eq_self (fun _ _ => nbaFold_flatMap_eq_self (fun _ _ => by
    unfold accQ
    repeat' split
    all_goals simp [nbaFold, h]) _ _) _ x

end names

/-- **The next state, register by register.** -/
theorem mmNext_eq (N W AccW : Nat) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec) :
    mmNext N W AccW ck r s a b dn c t ma mb sa sb sp acc sc =
      MS ck r s a b (nbaFold "done" (ctrlQ N r s dn t) dn) (nbaFold "C" (wrQ N t sc c) c)
        (nbaFold "t" (ctrlQ N r s dn t) t) (nbaFold "ma" (memAQ N W s t a ma) ma)
        (nbaFold "mb" (memBQ N W s t b mb) mb) (nbaFold "sa" (saQs N W ma) sa) (nbaFold "sb" (sbQ N W mb sb) sb)
        (nbaFold "sp" (spQs N W sa sb) sp) (nbaFold "acc" (accQs N W AccW t sp acc) acc)
        (nbaFold "sc" (scQ acc sc) sc) := by
  rw [mmNext, commit_MS]
  simp (disch := decide) only [mmQ, nbaFold_append, fold_ctrlQ, fold_memAQ, fold_memBQ, fold_sbQ, fold_scQ,
    fold_wrQ, fold_saQs, fold_spQs, fold_accQs]

/-! ## 6. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c t ma mb sa sb sp acc sc : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ t.width = 32 ∧ ma.width = N * N * W ∧ mb.width = N * N * W ∧
    sa.width = N * W ∧ sb.width = N * W ∧ sp.width = N * N * (2 * W) ∧ acc.width = N * N * AccW ∧
    sc.width = N * N * AccW

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c t ma mb sa sb sp acc sc, st = MS ck r s a b dn c t ma mb sa sb sp acc sc ∧
    Wd N W AccW dn c t ma mb sa sb sp acc sc

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c t ma mb sa sb sp acc sc : LVec)
    (hw : Wd N W AccW dn c t ma mb sa sb sp acc sc) :
    I N W AccW (mmNext N W AccW ck r s a b dn c t ma mb sa sb sp acc sc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hw
  rw [mmNext_eq]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmPs, mmTop, saPs, spPs, accPs, ctrlP, memAP, memBP, sbP, scP, wrP, saP, spP, accP, nb,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase, List.any_flatMap, List.any_map,
    List.any_append]

/-! ## 3. The values `t` cycles after a start -/

attribute [local simp] condTrue_knownBit

/-- The counter's value `k`. -/
abbrev tv (k : Nat) : LVec := .ofBitVec (BitVec.ofNat 32 k)

theorem ofInt32 {v : Int} {m : Nat} (hv : v = m) : LVec.ofInt 32 v = LVec.ofBitVec (BitVec.ofNat 32 m) := by
  subst hv; rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem ofNat_eq_iff32 {t N : Nat} (ht : t < 2 ^ 32) (hN : N < 2 ^ 32) :
    BitVec.ofNat 32 t = BitVec.ofNat 32 N ↔ t = N := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hN]

theorem ofBool_eq_zero' (b : Bool) : decide (BitVec.ofBool b = 0#1) = !b := by cases b <;> rfl

theorem c_lt {k m : Nat} (hk : k < 2 ^ 32) (hm : m < 2 ^ 32) :
    (LVec.ofLogic ((tv k).lt (LVec.ofBitVec (BitVec.ofNat 32 m)))).condTrue = decide (k < m) := by
  simp [BitVec.lt_def, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hm, ofBool_eq_zero']

theorem c_le {k m : Nat} (hk : k < 2 ^ 32) (hm : m < 2 ^ 32) :
    (LVec.ofLogic ((tv k).le (LVec.ofBitVec (BitVec.ofNat 32 m)))).condTrue = decide (k ≤ m) := by
  simp [BitVec.le_def, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hm, ofBool_eq_zero']

theorem c_gt {k m : Nat} (hk : k < 2 ^ 32) (hm : m < 2 ^ 32) :
    (LVec.ofLogic ((tv k).gt (LVec.ofBitVec (BitVec.ofNat 32 m)))).condTrue = decide (m < k) := by
  simp [BitVec.lt_def, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hm, ofBool_eq_zero']

theorem c_eq {k m : Nat} (hk : k < 2 ^ 32) (hm : m < 2 ^ 32) :
    (LVec.ofLogic ((tv k).eqLogical (LVec.ofBitVec (BitVec.ofNat 32 m)))).condTrue = decide (k = m) := by
  simp [ofNat_eq_iff32 hk hm, ofBool_eq_zero']

/-- Column `k` of `A`: entry `i` is `A[i][k]`. -/
def colA (N W : Nat) {n : Nat} (A : BitVec n) (k : Nat) : BitVec (N * W) :=
  packBV W N fun i => A.extractLsb' ((i * N + k) * W) W

/-- Row `k` of `B`. -/
def rowB (N W : Nat) {n : Nat} (B : BitVec n) (k : Nat) : BitVec (N * W) := B.extractLsb' (k * (N * W)) (N * W)

/-- The products of step `k`: lane `r = i·N + j` is `A[i][k]·B[k][j]`, exact in `2W` bits. -/
def prodV (N W : Nat) {n : Nat} (A B : BitVec n) (k : Nat) : BitVec (N * N * (2 * W)) :=
  packBV (2 * W) (N * N) fun r =>
    BitVec.ofInt (2 * W) (Tasks.Matmul.entry W A (r / N * N + k) * Tasks.Matmul.entry W B (k * N + r % N))

/-- `Σ_{k' < t} A[i][k']·B[k'][j]` in the integers (`Tasks.Matmul.dot` at `t = N`). -/
def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

/-- The accumulators after `t` steps: entry `(i, j)` is `psum t i j` mod `2^AccW`. -/
def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r => BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 1) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

/-! ### Generic facts -/

theorem insertEntries_congr {W : Nat} {g g' : Nat → LVec} {c : LVec} :
    ∀ {n}, (∀ r, r < n → g r = g' r) → LVec.insertEntries W g n c = LVec.insertEntries W g' n c
  | 0, _ => rfl
  | n + 1, h => by
    rw [LVec.insertEntries_succ, LVec.insertEntries_succ, insertEntries_congr (fun r hr => h r (by omega)),
      h n (by omega)]

theorem nbaFold_map_entries (n : String) (W : Nat) (g : Nat → LVec) :
    ∀ (m : Nat) (x : LVec), nbaFold n ((List.range m).map fun r => (n, r * W, g r)) x = LVec.insertEntries W g m x
  | 0, _ => rfl
  | m + 1, x => by
    rw [List.range_succ, List.map_append, nbaFold_append, nbaFold_map_entries n W g m x, LVec.insertEntries_succ]
    simp [nbaFold]

/-- A row-major family of single writes to `n`, as one map over `r = i·N + j`. -/
theorem rowMajor_map {N K : Nat} {n : String} {q : Nat → Nat → NbaQueue2} (g : Nat → LVec)
    (h : ∀ i j, i < N → j < N → q i j = [(n, (i * N + j) * K, g (i * N + j))]) :
    ((List.range N).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (N * N)).map fun r => (n, r * K, g r) := by
  suffices ∀ M, M ≤ N → ((List.range M).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (M * N)).map (fun r => (n, r * K, g r)) from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [CombView.flatMap_congr' fun j hj => h M j (by omega) (List.mem_range.mp hj)]
    congr 1
    induction (List.range N) with
    | nil => rfl
    | cons a l ih' => rw [List.flatMap_cons, ih']; rfl

theorem extractLsb'_extractLsb'_add {w : Nat} (x : BitVec w) {s L a b : Nat} (h : a + b ≤ L) :
    (x.extractLsb' s L).extractLsb' a b = x.extractLsb' (s + a) b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show a + i < L by omega, Nat.add_assoc]

/-- A signed product at a wider width, truncated: the signed product. -/
theorem setWidth_mul_signExtend' {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  have := Lib.setWidth_add_mul_signExtend h (0#m) a b
  simpa using this

/-- An accumulate of a sign-extended lane at a wider width, truncated. -/
theorem setWidth_add_signExtend {m n w : Nat} (h : m ≤ n) (x : BitVec m) (y : BitVec w) :
    (x.setWidth n + y.signExtend n).setWidth m = x + y.signExtend m := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    Lib.setWidth_signExtend_of_le _ h]

/-- **The product of two `W`-bit entries fits in `2W` bits**: sign-extending its `2W`-bit value is the product. -/
theorem signExtend_ofInt_prod {W : Nat} (hW : 1 ≤ W) (m : Nat) (x y : BitVec W) :
    (BitVec.ofInt (2 * W) (x.toInt * y.toInt)).signExtend m = BitVec.ofInt m (x.toInt * y.toInt) := by
  have h1 := BitVec.le_toInt_mul_toInt (x := x) (y := y)
  have h2 := BitVec.toInt_mul_toInt_le (x := x) (y := y)
  obtain ⟨k, hk⟩ : ∃ k, W * 2 - 2 = k := ⟨_, rfl⟩
  have e : 2 * W = k + 2 := by omega
  rw [hk] at h1 h2
  have hp : (0 : Int) < 2 ^ k := by
    have := Nat.two_pow_pos k; exact_mod_cast this
  have hb : (x.toInt * y.toInt).bmod (2 ^ (2 * W)) = x.toInt * y.toInt := by
    apply Int.bmod_eq_of_le
    · rw [e, Nat.pow_add]; push_cast; omega
    · rw [e, Nat.pow_add]; push_cast; omega
  rw [BitVec.signExtend, BitVec.toInt_ofInt, hb]

/-! ### The registers through a cycle without reset and start -/

section regs
variable {N W AccW : Nat}

theorem sa_next (A : BitVec (N * N * W)) (k : Nat) {sa : LVec} (hsa : sa.width = N * W) :
    nbaFold "sa" (saQs N W (.ofBitVec (A >>> (k * W)))) sa = .ofBitVec (colA N W A k) := by
  rw [saQs, nbaFold_flatMap]
  have h1 : ((List.range N).foldl (fun acc i => nbaFold "sa" (saQ N W (.ofBitVec (A >>> (k * W))) i) acc) sa) =
      LVec.insertEntries W (fun i => ((LVec.ofBitVec (A >>> (k * W))).extract (i * N * W) W).resizeU W) N sa := by
    simp [saQ, nbaFold, LVec.insertEntries]
  rw [h1, insertEntries_congr (g' := fun i => .ofBitVec (A.extractLsb' ((i * N + k) * W) W)),
    LVec.insertEntries_ofBitVec _ _ hsa]
  · rfl
  · intro i hi
    have ha : i * N * W + W ≤ N * N * W := by
      have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
    rw [LVec.extract_ofBitVec _ ha, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, Lib.extractLsb'_ushiftRight,
      Nat.add_mul (i * N) k W, Nat.add_comm (k * W)]

theorem sb_next (hN : 1 ≤ N) (B : BitVec (N * N * W)) (k : Nat) {sb : LVec} (hsb : sb.width = N * W) :
    nbaFold "sb" (sbQ N W (.ofBitVec (B >>> (k * (N * W)))) sb) sb = .ofBitVec (rowB N W B k) := by
  have h : 0 + N * W ≤ N * N * W := by rw [Nat.zero_add, Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
  simp only [sbQ, nbaFold, wr, List.foldl_cons, List.foldl_nil, LVec.extract_ofBitVec _ h, LVec.resizeU_ofBitVec,
    hsb, BitVec.setWidth_eq, ite_true]
  rw [LVec.insertAt_zero_of_width_eq (by simp [hsb]), Lib.extractLsb'_ushiftRight, Nat.add_zero]; rfl

theorem sp_lane (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {k i j : Nat} (hi : i < N) (hj : j < N) :
    spQ N W (.ofBitVec (colA N W A k)) (.ofBitVec (rowB N W B k)) i j =
      [("sp", (i * N + j) * (2 * W), .ofBitVec (BitVec.ofInt (2 * W)
        (Tasks.Matmul.entry W A ((i * N + j) / N * N + k) * Tasks.Matmul.entry W B (k * N + (i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hsa : i * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hsb : j * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have e2 : k * (N * W) + j * W = (k * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  simp only [spQ, spV, sxv]
  simp (disch := omega) only [LVec.extract_ofBitVec, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW, LVec.mul_ofBitVec,
    LVec.resizeU_ofBitVec]
  rw [setWidth_mul_signExtend' (by omega)]
  simp only [colA, rowB, extractLsb'_packBV _ hi, extractLsb'_extractLsb'_add _ hsb, e2, hd, hm, Tasks.Matmul.entry]

theorem sp_next (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (k : Nat) {sp : LVec} (hsp : sp.width = N * N * (2 * W)) :
    nbaFold "sp" (spQs N W (.ofBitVec (colA N W A k)) (.ofBitVec (rowB N W B k))) sp = .ofBitVec (prodV N W A B k) := by
  rw [spQs, rowMajor_map (n := "sp") (K := 2 * W) (fun r => .ofBitVec (BitVec.ofInt (2 * W)
      (Tasks.Matmul.entry W A (r / N * N + k) * Tasks.Matmul.entry W B (k * N + r % N))))
      (fun i j hi hj => sp_lane hW A B hi hj),
    nbaFold_map_entries, LVec.insertEntries_ofBitVec _ _ hsp]
  rfl

theorem two_lt32 : (2 : Nat) < 2 ^ 32 := by decide

theorem acc_load_lane (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (acc : LVec) {i j : Nat} (hi : i < N) (hj : j < N) :
    accQ N W AccW (tv 2) (.ofBitVec (prodV N W A B 0)) acc i j =
      [("acc", (i * N + j) * AccW, .ofBitVec (BitVec.ofInt AccW (psum N W A B 1 ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hp : (i * N + j) * (2 * W) + 2 * W ≤ N * N * (2 * W) := Lib.rowMajor_window_le hi hj
  have e2 : LVec.ofInt 32 2 = .ofBitVec (BitVec.ofNat 32 2) := ofInt32 (m := 2) rfl
  simp only [accQ, e2, c_eq two_lt32 two_lt32, decide_true, ite_true, ldV, sxv]
  simp (disch := omega) only [LVec.extract_ofBitVec, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend (show 1 ≤ 2 * W by omega),
    LVec.resizeU_ofBitVec]
  rw [Lib.setWidth_signExtend_of_le _ (by omega), BitVec.setWidth_eq]
  simp only [prodV, extractLsb'_packBV _ hr, Tasks.Matmul.entry, signExtend_ofInt_prod hW, hd, hm]
  simp [psum, Tasks.Matmul.entry]

theorem acc_add_lane (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {u i j : Nat} (hu : 1 ≤ u) (huN : u + 1 ≤ N)
    (hN4 : N + 4 < 2 ^ 32) (hi : i < N) (hj : j < N) :
    accQ N W AccW (tv (u + 2)) (.ofBitVec (prodV N W A B u)) (accC N W AccW A B u) i j =
      [("acc", (i * N + j) * AccW,
        .ofBitVec (BitVec.ofInt AccW (psum N W A B (u + 1) ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hp : (i * N + j) * (2 * W) + 2 * W ≤ N * N * (2 * W) := Lib.rowMajor_window_le hi hj
  have hc : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
  have e2 : LVec.ofInt 32 2 = .ofBitVec (BitVec.ofNat 32 2) := ofInt32 (m := 2) rfl
  have e1 : LVec.ofInt 32 ((N : Int) + 1) = .ofBitVec (BitVec.ofNat 32 (N + 1)) := ofInt32 (by omega)
  have hu2 : u + 2 < 2 ^ 32 := by omega
  simp only [accQ, e2, e1, c_eq hu2 two_lt32, c_gt hu2 two_lt32, c_le hu2 (show N + 1 < 2 ^ 32 by omega),
    show ¬ (u + 2 = 2) by omega, show 2 < u + 2 by omega, show u + 2 ≤ N + 1 by omega, decide_true, decide_false,
    ite_true, Bool.false_eq_true, ite_false, adV, sxv, accC]
  simp (disch := omega) only [LVec.extract_ofBitVec, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend (show 1 ≤ 2 * W by omega),
    LVec.resizeU_ofBitVec, LVec.add_ofBitVec]
  rw [setWidth_add_signExtend (by omega), BitVec.setWidth_eq]
  simp only [prodV, extractLsb'_packBV _ hr, Tasks.Matmul.entry, signExtend_ofInt_prod hW, hd, hm,
    ← BitVec.ofInt_add, psum_succ]

theorem acc_quiet {t : Nat} (ht : t ≠ 2) (ht' : t ≤ 1 ∨ N + 2 ≤ t) (hN4 : N + 4 < 2 ^ 32) (htN : t ≤ N + 4)
    (sp acc : LVec) : nbaFold "acc" (accQs N W AccW (tv t) sp acc) acc = acc := by
  have e2 : LVec.ofInt 32 2 = .ofBitVec (BitVec.ofNat 32 2) := ofInt32 (m := 2) rfl
  have e1 : LVec.ofInt 32 ((N : Int) + 1) = .ofBitVec (BitVec.ofNat 32 (N + 1)) := ofInt32 (by omega)
  have ht2 : t < 2 ^ 32 := by omega
  refine nbaFold_flatMap_eq_self (fun _ _ => nbaFold_flatMap_eq_self (fun _ _ => ?_) _ _) _ _
  simp only [accQ, e2, e1, c_eq ht2 two_lt32, c_gt ht2 two_lt32, c_le ht2 (show N + 1 < 2 ^ 32 by omega)]
  by_cases h2 : 2 < t
  · simp [ht, h2, show ¬ t ≤ N + 1 by omega, nbaFold]
  · simp [ht, h2, nbaFold]

theorem acc_load (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {acc : LVec}
    (hacc : acc.width = N * N * AccW) :
    nbaFold "acc" (accQs N W AccW (tv 2) (.ofBitVec (prodV N W A B 0)) acc) acc = accC N W AccW A B 1 := by
  rw [accQs, rowMajor_map (n := "acc") (K := AccW)
      (fun r => .ofBitVec (BitVec.ofInt AccW (psum N W A B 1 (r / N) (r % N))))
      (fun i j hi hj => acc_load_lane hW A B acc hi hj),
    nbaFold_map_entries, LVec.insertEntries_ofBitVec _ _ hacc]
  rfl

theorem acc_add (hN4 : N + 4 < 2 ^ 32) (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {u : Nat} (hu : 1 ≤ u)
    (huN : u + 1 ≤ N) :
    nbaFold "acc" (accQs N W AccW (tv (u + 2)) (.ofBitVec (prodV N W A B u)) (accC N W AccW A B u))
      (accC N W AccW A B u) = accC N W AccW A B (u + 1) := by
  rw [accQs, rowMajor_map (n := "acc") (K := AccW)
      (fun r => .ofBitVec (BitVec.ofInt AccW (psum N W A B (u + 1) (r / N) (r % N))))
      (fun i j hi hj => acc_add_lane hW A B hu huN hN4 hi hj),
    nbaFold_map_entries, LVec.insertEntries_ofBitVec _ _ (by simp [accC])]
  rfl

theorem sc_next (x : BitVec (N * N * AccW)) {sc : LVec} (hsc : sc.width = N * N * AccW) :
    nbaFold "sc" (scQ (.ofBitVec x) sc) sc = .ofBitVec x := by
  simp only [scQ, nbaFold, wr, List.foldl_cons, List.foldl_nil, ite_true, hsc, LVec.resizeU_ofBitVec,
    BitVec.setWidth_eq]
  exact LVec.insertAt_zero_of_width_eq (by simp [hsc])

end regs

/-! ### The control, the memories and the write of `C` -/

section ctrl
variable {N W AccW : Nat}

theorem e4 {N : Nat} (hN4 : N + 4 < 2 ^ 32) : LVec.ofInt 32 ((N : Int) + 4) = .ofBitVec (BitVec.ofNat 32 (N + 4)) :=
  ofInt32 (by omega)
theorem e3 {N : Nat} : LVec.ofInt 32 ((N : Int) + 3) = .ofBitVec (BitVec.ofNat 32 (N + 3)) := ofInt32 (by omega)
theorem e1 : LVec.ofInt 32 1 = .ofBitVec (BitVec.ofNat 32 1) := ofInt32 (m := 1) rfl

theorem ctrl_t {k : Nat} (hk : k ≤ N + 4) (hN4 : N + 4 < 2 ^ 32) (dn : LVec) :
    nbaFold "t" (ctrlQ N (knownBit false) (knownBit false) dn (tv k)) (tv k) =
      tv (if k < N + 4 then k + 1 else k) := by
  have hk' : k < 2 ^ 32 := by omega
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ite_false, e4 hN4, e3, e1, c_lt hk' hN4,
    c_eq hk' (show N + 3 < 2 ^ 32 by omega)]
  by_cases h : k < N + 4 <;> by_cases h' : k = N + 3 <;>
    simp [h, h', nbaFold, LVec.add_ofBitVec, BitVec.ofNat_add_ofNat, LVec.insertAt_zero_of_width_eq]

theorem ctrl_done {k : Nat} (hk : k ≤ N + 4) (hN4 : N + 4 < 2 ^ 32) {dn : LVec} (hdn : dn.width = 1) :
    nbaFold "done" (ctrlQ N (knownBit false) (knownBit false) dn (tv k)) dn =
      if k = N + 3 then knownBit true else dn := by
  have hk' : k < 2 ^ 32 := by omega
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ite_false, e4 hN4, e3, e1, c_lt hk' hN4,
    c_eq hk' (show N + 3 < 2 ^ 32 by omega)]
  by_cases h : k < N + 4 <;> by_cases h' : k = N + 3 <;>
    simp [h, h', nbaFold, hdn, LVec.resizeU_one_l1, LVec.insertAt_zero_of_width_eq]

theorem ctrl_reset_t (hN4 : N + 4 < 2 ^ 32) (s dn : LVec) {t : LVec} (ht : t.width = 32) :
    nbaFold "t" (ctrlQ N (knownBit true) s dn t) t = tv (N + 4) := by
  simp [ctrlQ, nbaFold, e4 hN4, ht, LVec.insertAt_zero_of_width_eq]

theorem ctrl_reset_done (s : LVec) {dn : LVec} (t : LVec) (hdn : dn.width = 1) :
    nbaFold "done" (ctrlQ N (knownBit true) s dn t) dn = knownBit false := by
  simp [ctrlQ, nbaFold, hdn, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]

theorem ctrl_start_t (dn : LVec) {t : LVec} (ht : t.width = 32) :
    nbaFold "t" (ctrlQ N (knownBit false) (knownBit true) dn t) t = tv 0 := by
  simp [ctrlQ, nbaFold, ht, LVec.insertAt_zero_of_width_eq]

theorem ctrl_start_done {dn : LVec} (t : LVec) (hdn : dn.width = 1) :
    nbaFold "done" (ctrlQ N (knownBit false) (knownBit true) dn t) dn = knownBit false := by
  simp [ctrlQ, nbaFold, hdn, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]

theorem memA_read {k : Nat} (hk : k < N) (hN4 : N + 4 < 2 ^ 32) (hW32 : W < 2 ^ 32) (A : BitVec (N * N * W))
    (a : LVec) :
    nbaFold "ma" (memAQ N W (knownBit false) (tv k) a (.ofBitVec (A >>> (k * W)))) (.ofBitVec (A >>> (k * W))) =
      .ofBitVec (A >>> ((k + 1) * W)) := by
  have hN32 : N < 2 ^ 32 := by omega
  simp only [memAQ, condTrue_knownBit, Bool.false_eq_true, ite_false, ofInt32 (v := (N : Int)) (m := N) rfl,
    ofInt32 (v := (W : Int)) (m := W) rfl, c_lt (show k < 2 ^ 32 by omega) hN32, decide_eq_true hk, ite_true]
  simp [nbaFold, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW32, LVec.insertAt_zero_of_width_eq, ← BitVec.shiftRight_add,
    Nat.succ_mul]

theorem memB_read {k : Nat} (hk : k < N) (hN4 : N + 4 < 2 ^ 32) (hW32 : W < 2 ^ 32) (hNW32 : N * W < 2 ^ 32)
    (B : BitVec (N * N * W)) (b : LVec) :
    nbaFold "mb" (memBQ N W (knownBit false) (tv k) b (.ofBitVec (B >>> (k * (N * W)))))
      (.ofBitVec (B >>> (k * (N * W)))) = .ofBitVec (B >>> ((k + 1) * (N * W))) := by
  have hN32 : N < 2 ^ 32 := by omega
  have hm : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN32, Nat.mod_eq_of_lt hW32,
      Nat.mod_eq_of_lt hNW32]
  simp only [memBQ, condTrue_knownBit, Bool.false_eq_true, ite_false, ofInt32 (v := (N : Int)) (m := N) rfl,
    ofInt32 (v := (W : Int)) (m := W) rfl, c_lt (show k < 2 ^ 32 by omega) hN32, decide_eq_true hk, ite_true]
  simp [nbaFold, hm, LVec.insertAt_zero_of_width_eq, ← BitVec.shiftRight_add, Nat.succ_mul]

theorem memA_hold {k : Nat} (hk : N ≤ k) (hk32 : k < 2 ^ 32) (a ma : LVec) :
    nbaFold "ma" (memAQ N W (knownBit false) (tv k) a ma) ma = ma := by
  have hN32 : N < 2 ^ 32 := by omega
  simp only [memAQ, ofInt32 (v := (N : Int)) (m := N) rfl, c_lt hk32 hN32]
  simp [show ¬ k < N by omega, nbaFold]

theorem memB_hold {k : Nat} (hk : N ≤ k) (hk32 : k < 2 ^ 32) (b mb : LVec) :
    nbaFold "mb" (memBQ N W (knownBit false) (tv k) b mb) mb = mb := by
  have hN32 : N < 2 ^ 32 := by omega
  simp only [memBQ, ofInt32 (v := (N : Int)) (m := N) rfl, c_lt hk32 hN32]
  simp [show ¬ k < N by omega, nbaFold]

theorem memA_load (t : LVec) (A : BitVec (N * N * W)) {ma : LVec} (hma : ma.width = N * N * W) :
    nbaFold "ma" (memAQ N W (knownBit true) t (.ofBitVec A) ma) ma = .ofBitVec A := by
  simp [memAQ, nbaFold, hma, LVec.insertAt_zero_of_width_eq]

theorem memB_load (t : LVec) (B : BitVec (N * N * W)) {mb : LVec} (hmb : mb.width = N * N * W) :
    nbaFold "mb" (memBQ N W (knownBit true) t (.ofBitVec B) mb) mb = .ofBitVec B := by
  simp [memBQ, nbaFold, hmb, LVec.insertAt_zero_of_width_eq]

theorem wrC_hold {k : Nat} (hk : k ≠ N + 3) (hk32 : k < 2 ^ 32) (hN4 : N + 4 < 2 ^ 32) (sc c : LVec) :
    nbaFold "C" (wrQ N (tv k) sc c) c = c := by
  simp only [wrQ, e3, c_eq hk32 (show N + 3 < 2 ^ 32 by omega)]
  simp [hk, nbaFold]

theorem wrC_fire (hN4 : N + 4 < 2 ^ 32) (x : BitVec (N * N * AccW)) {c : LVec} (hc : c.width = N * N * AccW) :
    nbaFold "C" (wrQ N (tv (N + 3)) (.ofBitVec x) c) c = .ofBitVec x := by
  simp only [wrQ, e3, c_eq (show N + 3 < 2 ^ 32 by omega) (show N + 3 < 2 ^ 32 by omega)]
  simp [nbaFold, hc, LVec.insertAt_zero_of_width_eq]

end ctrl

/-! ## 4. The spec's arithmetic -/

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- After `N` steps the accumulators hold the product (`psum N` is `dot`). -/
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

/-! ## 5. The phases -/

/-- The state `t ≤ N + 3` cycles after a start with operands `A`, `B` (the timetable's invariant). -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c ma mb sa sb sp acc sc, st = MS ck r s a b (knownBit false) c (tv t) ma mb sa sb sp acc sc ∧
    (t ≤ N → ma = .ofBitVec (A >>> (t * W)) ∧ mb = .ofBitVec (B >>> (t * (N * W)))) ∧
    (1 ≤ t → t ≤ N → sa = .ofBitVec (colA N W A (t - 1)) ∧ sb = .ofBitVec (rowB N W B (t - 1))) ∧
    (2 ≤ t → t ≤ N + 1 → sp = .ofBitVec (prodV N W A B (t - 2))) ∧
    (3 ≤ t → acc = accC N W AccW A B (t - 2)) ∧
    (4 ≤ t → sc = accC N W AccW A B (t - 3))

/-- Finished with `A`, `B`: `done` = 1, `C` the product, the counter at rest. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b ma mb sa sb sp acc sc, st = MS ck r s a b (knownBit true)
    (.ofBitVec (Tasks.Matmul.product N W AccW A B)) (tv (N + 4)) ma mb sa sb sp acc sc

/-- Idle after a reset: `done` = 0, the counter at rest. -/
def ReadyAt (N : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c ma mb sa sb sp acc sc, st = MS ck r s a b (knownBit false) c (tv (N + 4)) ma mb sa sb sp acc sc

theorem range_facts {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) :
    N + 4 < 2 ^ 32 ∧ W < 2 ^ 32 ∧ N * W < 2 ^ 32 := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
  have h2 : N ≤ N * W := Nat.le_mul_of_pos_right _ hW
  have h3 : W ≤ N * W := Nat.le_mul_of_pos_left _ hN
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Nat.reducePow] at hr ⊢ <;> omega

/-- **One busy cycle** (`t ≤ N + 2`, reset and `start` low): the state at `t + 1`. -/
theorem next_busy {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t ≤ N + 2) {ck a b c ma mb sa sb sp acc sc : LVec}
    (hw : Wd N W AccW (knownBit false) c (tv t) ma mb sa sb sp acc sc)
    (h1 : t ≤ N → ma = .ofBitVec (A >>> (t * W)) ∧ mb = .ofBitVec (B >>> (t * (N * W))))
    (h2 : 1 ≤ t → t ≤ N → sa = .ofBitVec (colA N W A (t - 1)) ∧ sb = .ofBitVec (rowB N W B (t - 1)))
    (h3 : 2 ≤ t → t ≤ N + 1 → sp = .ofBitVec (prodV N W A B (t - 2)))
    (h4 : 3 ≤ t → acc = accC N W AccW A B (t - 2)) :
    BusyAt N W AccW A B (t + 1)
      (mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (tv t) ma mb sa sb sp acc sc) := by
  obtain ⟨hN4, hW32, hNW32⟩ := range_facts hN hW hr
  obtain ⟨-, hc, -, hma, hmb, hsa, hsb, hsp, hacc, hsc⟩ := hw
  rw [mmNext_eq, ctrl_done (by omega) hN4 (by simp), ctrl_t (by omega) hN4]
  simp only [show ¬ (t = N + 3) by omega, show t < N + 4 by omega, ite_false, ite_true]
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨rfl, rfl⟩ := h1 (by omega)
    exact ⟨memA_read (by omega) hN4 hW32 A a, memB_read (by omega) hN4 hW32 hNW32 B b⟩
  · intro _ h
    obtain ⟨rfl, rfl⟩ := h1 (by omega)
    rw [Nat.add_sub_cancel]
    exact ⟨sa_next A t hsa, sb_next hN B t hsb⟩
  · intro h h'
    obtain ⟨rfl, rfl⟩ := h2 (by omega) (by omega)
    rw [show t + 1 - 2 = t - 1 by omega]
    exact sp_next hW A B (t - 1) hsp
  · intro h
    rcases Nat.lt_or_ge t 3 with h3' | h3'
    · obtain rfl : t = 2 := by omega
      obtain rfl := h3 (by omega) (by omega)
      exact acc_load hW A B hacc
    · obtain rfl := h4 h3'
      rcases Nat.lt_or_ge t (N + 2) with h5 | h5
      · obtain rfl := h3 (by omega) (by omega)
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
        simp only [Nat.add_sub_cancel, show u + 2 + 1 - 2 = u + 1 by omega]
        exact acc_add hN4 hW A B (by omega) (by omega)
      · rw [acc_quiet (by omega) (by omega) hN4 (by omega), accC_ge N W AccW A B (by omega : N ≤ t - 2),
          accC_ge N W AccW A B (by omega : N ≤ t + 1 - 2)]
  · intro h
    obtain rfl := h4 (by omega)
    rw [accC, sc_next _ hsc, show t + 1 - 3 = t - 2 by omega]; rfl

/-- **The last busy cycle** (`t = N + 3`): `C` gets the result stream, `done` rises, the counter rests. -/
theorem next_fin {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {ck a b c ma mb sa sb sp acc sc : LVec}
    (hw : Wd N W AccW (knownBit false) c (tv (N + 3)) ma mb sa sb sp acc sc)
    (h5 : sc = accC N W AccW A B (N + 3 - 3)) :
    FinAt N W AccW A B
      (mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c (tv (N + 3)) ma mb sa sb sp acc sc) := by
  obtain ⟨hN4, -, -⟩ := range_facts hN hW hr
  obtain ⟨-, hc, -, -, -, -, -, -, -, -⟩ := hw
  rw [Nat.add_sub_cancel, accC_N] at h5
  subst h5
  rw [mmNext_eq, ctrl_done (by omega) hN4 (by simp), ctrl_t (by omega) hN4, wrC_fire hN4 _ hc]
  simp only [ite_true, show N + 3 < N + 4 by omega]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- A cycle at rest (reset and `start` low, the counter at `N + 4`) keeps `done`, `C` and the counter. -/
theorem next_rest {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    {ck a b dn c ma mb sa sb sp acc sc : LVec} (hdn : dn.width = 1) :
    ∃ ma' mb' sa' sb' sp' acc' sc',
      mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c (tv (N + 4)) ma mb sa sb sp acc sc =
        MS ck (knownBit false) (knownBit false) a b dn c (tv (N + 4)) ma' mb' sa' sb' sp' acc' sc' := by
  obtain ⟨hN4, -, -⟩ := range_facts hN hW hr
  rw [mmNext_eq, ctrl_done (by omega) hN4 hdn, ctrl_t (by omega) hN4, wrC_hold (by omega) hN4 hN4]
  simp only [show ¬ (N + 4 = N + 3) by omega, show ¬ (N + 4 < N + 4) by omega, ite_false]
  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- A reset cycle: `done` = 0 and the counter at rest. -/
theorem next_reset {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (ck s a b dn c t ma mb sa sb sp acc sc : LVec) (hw : Wd N W AccW dn c t ma mb sa sb sp acc sc) :
    ReadyAt N (mmNext N W AccW ck (knownBit true) s a b dn c t ma mb sa sb sp acc sc) := by
  obtain ⟨hN4, -, -⟩ := range_facts hN hW hr
  obtain ⟨hdn, -, ht, -⟩ := hw
  rw [mmNext_eq, ctrl_reset_done s t hdn, ctrl_reset_t hN4 s dn ht]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- A start cycle: the state at `t = 0`. -/
theorem next_start {N W AccW : Nat} (A B : BitVec (N * N * W)) (ck dn c t ma mb sa sb sp acc sc : LVec)
    (hw : Wd N W AccW dn c t ma mb sa sb sp acc sc) :
    BusyAt N W AccW A B 0
      (mmNext N W AccW ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c t ma mb sa sb sp acc sc) := by
  obtain ⟨hdn, -, ht, hma, hmb, -⟩ := hw
  rw [mmNext_eq, ctrl_start_done t hdn, ctrl_start_t dn ht, memA_load t A hma, memB_load t B hmb]
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, fun _ => ⟨by simp, by simp⟩, by omega, by omega, by omega,
    by omega⟩

/-! ### The model -/

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c t ma mb sa sb sp acc sc, prev = MS ck r s a b dn c t ma mb sa sb sp acc sc ∧
    Wd N W AccW dn c t ma mb sa sb sp acc sc ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c t ma mb sa sb sp acc sc

theorem MS_inj {ck r s a b dn c t ma mb sa sb sp acc sc ck' r' s' a' b' dn' c' t' ma' mb' sa' sb' sp' acc' sc' : LVec}
    (h : MS ck r s a b dn c t ma mb sa sb sp acc sc = MS ck' r' s' a' b' dn' c' t' ma' mb' sa' sb' sp' acc' sc') :
    dn = dn' ∧ c = c' ∧ t = t' ∧ ma = ma' ∧ mb = mb' ∧ sa = sa' ∧ sb = sb' ∧ sp = sp' ∧ acc = acc' ∧ sc = sc' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * W), .xVec (N * W), .xVec (N * N * (2 * W)),
    .xVec (N * N * AccW), .xVec (N * N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-- **The phase model** at `(N, W, AccW)`, latency `N + 4`. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (N + 4) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t ma mb sa sb sp acc sc k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c t ma mb sa sb sp acc sc hw
  Ready st := ReadyAt N st
  Busy x m st := ∃ t, t + m = N + 3 ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, ma, mb, sa, sb, sp, acc, sc, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, c, ma, mb, sa, sb, sp, acc, sc, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, ma, mb, sa, sb, sp, acc, sc, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset hN hW hNW _ _ _ _ dn c t ma mb sa sb sp acc sc hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N + 3, by omega, 0, by omega, next_start _ _ _ dn c t ma mb sa sb sp acc sc hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw, rfl⟩
      ⟨k, hk, ck', r', s', a', b', c', ma', mb', sa', sb', sp', acc', sc', hb, h1, h2, h3, h4, h5⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    by_cases hf : k = N + 3
    · subst hf
      exact .inl (next_fin hN hW hNW _ _ hw (h5 (by omega)))
    · exact .inr ⟨m - 1, by omega, k + 1, by omega, next_busy hN hW hNW _ _ (by omega) hw h1 h2 h3 h4⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw, rfl⟩
      ⟨ck', r', s', a', b', c', ma', mb', sa', sb', sp', acc', sc', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨_, _, _, _, _, _, _, h⟩ := next_rest (W := W) (AccW := AccW) (ck := appIn e "clk" ck)
      (a := appIn e "A" a) (b := appIn e "B" b) (c := c) (ma := ma) (mb := mb) (sa := sa) (sb := sb) (sp := sp)
      (acc := acc) (sc := sc) hN hW hNW (show (knownBit false).width = 1 by simp)
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw, rfl⟩
      ⟨ck', r', s', a', b', ma', mb', sa', sb', sp', acc', sc', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨_, _, _, _, _, _, _, h⟩ := next_rest (W := W) (AccW := AccW) (ck := appIn e "clk" ck)
      (a := appIn e "A" a) (b := appIn e "B" b) (c := .ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      (ma := ma) (mb := mb) (sa := sa) (sb := sb) (sp := sp) (acc := acc) (sc := sc) hN hW hNW
      (show (knownBit true).width = 1 by simp)
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "t", "ma", "mb", "sa", "sb", "sp", "acc", "sc"] :
      List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ mmPs N W AccW := by simpa [mmD] using hp
  rcases mm_mem hm with rfl | rfl | rfl | rfl | rfl | rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, memAP, memBP, sbP, scP, wrP, saP, spP, accP, nb, c32, sext, edgeClock,
      asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-! ## 8. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3) -/

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
  obtain ⟨ma, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨mb, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨sa, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨sb, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨sp, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨acc, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨sc, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain rfl := powerUp_nil.mp h15
  exact ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩

/-- **Termination from every power-up** (the cycle of `mm_cycle`). -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, t, ma, mb, sa, sb, sp, acc, sc, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA σ e ck r s a b dn c t ma mb sa sb sp acc sc kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c t ma mb sa sb sp acc sc hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

/-- The module-level processes pass rule 3. -/
theorem top_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    ∀ p ∈ mmTop N W, xsProc (mmD N W AccW) p = true := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ hN
  intro p hp
  rcases top_mem hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, ctrlP, memAP, memBP, sbP, scP, wrP, nb,
      c32, mmD, mmDecls, lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt, h1]

theorem sa_xsafe {N W AccW i : Nat} (hi : i < N) : xsProc (mmD N W AccW) (saP N W i) = true := by
  have hs : i * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have ha : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
  simp [xsProc, xsStmt, xsLhs, xsWidth, sigWidth, saP, mmD, mmDecls, ha]

theorem sp_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (spP N W i j) = true := by
  have hsa : i * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hsb : j * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hsa1 : i * W + W - 1 + 1 ≤ N * W := by omega
  have hsb1 : j * W + W - 1 + 1 ≤ N * W := by omega
  simp [xsProc, xsStmt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, spP, sext, mmD, mmDecls, hsa, hsb, hsa1, hsb1]

theorem acc_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (accP N W AccW i j) = true := by
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have hp := Lib.rowMajor_window_le (M := N) (N := N) (w := 2 * W) hi hj
  have hp1 : (i * N + j) * (2 * W) + 2 * W - 1 + 1 ≤ N * N * (2 * W) := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, accP, sext, c32, mmD, mmDecls,
    LVec.ofInt, hC, hp, hp1]

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ mmPs N W AccW := by simpa [mmD] using hp
  simp only [mmPs, List.mem_append] at hm
  rcases hm with ((hm | hm) | hm) | hm
  · exact top_xsafe N W AccW hN hW p hm
  · obtain ⟨i, hi, rfl⟩ := sa_mem hm; exact sa_xsafe hi
  · obtain ⟨i, j, hi, hj, rfl⟩ := sp_mem hm; exact sp_xsafe hW hi hj
  · obtain ⟨i, j, hi, hj, rfl⟩ := acc_mem hm; exact acc_xsafe hW hi hj

/-- **The timetable satisfies the matmul statement (txtask-v2) at latency `N + 4`** (`8` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA)
    (mm_disciplined N W AccW hN hW hA) (mm_terminatesPU N W AccW hN hW hA) (by show 1 ≤ N + 4; omega)
    (model N W AccW hN hW hA hNW) (mm_powerUp N W AccW hN hW hA) (mm_moore N W AccW hN hW hA)
    (mm_xsafe N W AccW hN hW hA)

end Submission
