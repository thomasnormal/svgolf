-- svgolf-latency: 10
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
# A mesh of small cores (`solution.sv`), for every `(N, W, AccW)` in range, latency `3N - 2`

The design: an `N × N` mesh of identical cores, each with its own local memory `amem(i, j)` (row `i` of `A`), one
multiply-accumulate unit (its accumulator `C(i, j)`) and one input link `lnk(i, j)` (a wavelet `{valid, last,
payload}`) from its north neighbour; routers forward each wavelet one core south per cycle; the edge I/O streams
column `j` of `B` into the link of core `(0, j)`, starting `j` cycles after the start edge; the far core
`(N-1, N-1)` raises `done` on its last-flagged wavelet.

The proof follows the reference's steps:
1. **Agreement** (`c_sem_eq`): the loaded family is the hand-built `cD`.
2. **One cycle** (`c_profile`, `c_cycle`): G0's clock step; the commit register by register (`nbaFold`).
3. **The invariant** (`AtT`): at time `t` (snapshot `t - 1` after a start), core `(i, j)` has consumed
   `f = min (t - (i + j + 1)) N` wavelets; the links, the edge buffer, the accumulators and the local memories are
   closed forms in `t`.
4. **The phases** (`model`): `Ready`, `Busy x m` (the state at time `t + 1` with `t + m + 2 = 3N - 1`), `Fin x`.
5. **txtask-v2's rules** and `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

/-- The latency: `done` shows `3N - 2` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := 3 * N - 2

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `w` zero bits. -/
abbrev zv (w : Nat) : LVec := LVec.replicate w .l0

/-- A nonblocking write of a constant to a whole signal. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `N + N - 2`, the step counter's idle value. -/
abbrev sMaxE (N : Nat) : Expr2 := .binary .sub (.binary .add (c32 N) (c32 N)) (c32 2)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The edge I/O's step counter `s` and its buffer `bs`. -/
def ctrlP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.ident "s") (sMaxE N))
    (some (.ifStmt (.ident "start")
      (.block #[nb "s" (zv 32), .nbaAssign (.ident "bs") (.resize ((2 * N - 1) * N * W)
        (.binary (.shr false) (.concat #[.ident "B", .repl (N * N * W) (.concat #[.lit ⟨#[.l0]⟩])])
          (.binary .add (.binary .mul (c32 N) (c32 W)) (.binary .mul (c32 N) (c32 W)))))])
      (some (.block #[.nbaAssign (.ident "bs") (.binary (.shr false) (.ident "bs") (.binary .mul (c32 N) (c32 W))),
        .ifStmt (.binary .ne (.ident "s") (sMaxE N))
          (.nbaAssign (.ident "s") (.binary .add (.ident "s") (c32 1))) none])))))

/-- The far core's `done` handler. -/
def doneP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst") (nb "done" ⟨#[.l0]⟩)
    (some (.ifStmt (.ident "start") (nb "done" ⟨#[.l0]⟩)
      (some (.ifStmt (.slice (.ident "lnk") ((N * N - 1) * (W + 2) + W + 1) 1)
        (.ifStmt (.slice (.ident "lnk") ((N * N - 1) * (W + 2) + W) 1) (nb "done" ⟨#[.l1]⟩) none) none)))))

/-- Edge I/O, column `0`: row `0` of `B` at the start edge, row `s + 1` after it. -/
def edge0P (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.slice "lnk" 0 (W + 2)) (.lit (zv (W + 2))))
    (some (.ifStmt (.ident "start")
      (.nbaAssign (.slice "lnk" 0 (W + 2))
        (.concat #[.lit ⟨#[.l1]⟩, .binary .eq (c32 N) (c32 1), .slice (.ident "B") 0 W]))
      (some (.ifStmt (.binary .lt (.ident "s") (.binary .sub (c32 N) (c32 1)))
        (.nbaAssign (.slice "lnk" 0 (W + 2))
          (.concat #[.lit ⟨#[.l1]⟩, .binary .eq (.ident "s") (.binary .sub (c32 N) (c32 2)),
            .slice (.ident "bs") ((N - 1) * N * W) W]))
        (some (.nbaAssign (.slice "lnk" 0 (W + 2)) (.lit (zv (W + 2))))))))))

/-- Edge I/O, column `x + 1`: row `s - x` of `B` into the link of core `(0, x + 1)`. -/
def edgeP (N W x : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.slice "lnk" ((x + 1) * (W + 2)) (W + 2)) (.lit (zv (W + 2))))
    (some (.ifStmt (.binary .lt (.binary .sub (.ident "s") (c32 x)) (c32 N))
      (.nbaAssign (.slice "lnk" ((x + 1) * (W + 2)) (W + 2))
        (.concat #[.lit ⟨#[.l1]⟩, .binary .eq (.ident "s") (.binary .sub (.binary .add (c32 x) (c32 N)) (c32 1)),
          .slice (.ident "bs") (((N - 2 - x) * N + x + 1) * W) W]))
      (some (.nbaAssign (.slice "lnk" ((x + 1) * (W + 2)) (W + 2)) (.lit (zv (W + 2))))))))

/-- The router of core `(i, j)`: the link into `(i+1, j)` takes the link into `(i, j)`. -/
def rtP (N W i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.slice "lnk" (((i + 1) * N + j) * (W + 2)) (W + 2)) (.lit (zv (W + 2))))
    (some (.nbaAssign (.slice "lnk" (((i + 1) * N + j) * (W + 2)) (W + 2))
      (.slice (.ident "lnk") ((i * N + j) * (W + 2)) (W + 2)))))

/-- Core `(i, j)`: load on `start`; a valid wavelet triggers one multiply-accumulate and, unless it is the last,
advances the operand pointer. -/
def coreP (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.block #[.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (zv AccW)),
      .nbaAssign (.slice "amem" ((i * N + j) * N * W) (N * W)) (.slice (.ident "A") (i * N * W) (N * W))])
    (some (.ifStmt (.slice (.ident "lnk") ((i * N + j) * (W + 2) + W + 1) 1)
      (.block #[.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW)
          (.resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "C") ((i * N + j) * AccW) AccW))
            (.binary .mul (sext "amem" AccW ((i * N + j) * N * W) W) (sext "lnk" AccW ((i * N + j) * (W + 2)) W)))),
        .ifStmt (.binary .eq (.slice (.ident "lnk") ((i * N + j) * (W + 2) + W) 1) (.lit ⟨#[.l0]⟩))
          (.nbaAssign (.slice "amem" ((i * N + j) * N * W) (N * W))
            (.binary (.shr false) (.slice (.ident "amem") ((i * N + j) * N * W) (N * W)) (c32 W)))
          none])
      none)))

/-- The declarations. -/
def cDecls (N W AccW : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true }, { name := "s", width := 32 },
   { name := "bs", width := (2 * N - 1) * N * W }, { name := "lnk", width := N * N * (W + 2) },
   { name := "amem", width := N * N * N * W }]

def edgePs (N W : Nat) : List Process2 := (List.range (N - 1)).map (edgeP N W)
def rtPs (N W : Nat) : List Process2 := (List.range (N - 1)).flatMap fun i => (List.range N).map (rtP N W i)
def corePs (N W AccW : Nat) : List Process2 := (List.range N).flatMap fun i => (List.range N).map (coreP N W AccW i)

/-- The generated processes, in source order. -/
def genPs (N W AccW : Nat) : List Process2 := edgePs N W ++ rtPs N W ++ corePs N W AccW

/-- **The hand-built design.** -/
def cD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (cDecls N W AccW).toArray
  processes := (ctrlP N W :: edge0P N W :: doneP N W :: genPs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def cScope (N W AccW : Int) : IEnv :=
  { vals := [("N", N), ("W", W), ("AccW", AccW)], pwidths := [("N", 32), ("W", 32), ("AccW", 32)] }

def cEnv (N W AccW : Int) : IEnv :=
  { cScope N W AccW with dims := dimTable (cScope N W AccW) design.pdesign.decls }

theorem c_paramEnv (N W AccW : Int) :
    design.pdesign.paramEnv2 [N, W, AccW] = .ok (cEnv N W AccW) := rfl

def cElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "s", "bs", "lnk", "amem"].map (·, 1)

theorem natAbs_cast {x : Nat} {X : Int} (h : (x : Int) = X) (hx : 0 < x) : (X - 1).natAbs + 1 = x := by
  subst h; omega

/-- The parameter facts the instantiation `simp`s need. -/
structure Rng (N W AccW : Nat) : Prop where
  hN : 1 ≤ N
  hW : 1 ≤ W
  hA : 1 ≤ AccW

theorem c_decls (N W AccW : Nat) (h : Rng N W AccW) :
    buildDecls (cEnv N W AccW) design.pdesign.decls = .ok (cDecls N W AccW) := by
  have hN := h.hN; have hW := h.hW; have hA := h.hA
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have h1 : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hW)
  have h2 : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hA)
  have h3 : ((2 * (N : Int) - 1) * N * W - 1).natAbs + 1 = (2 * N - 1) * N * W :=
    natAbs_cast (by rw [Int.natCast_mul, Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl)
      (Nat.mul_pos (Nat.mul_pos (by omega) hN) hW)
  have h4 : ((N : Int) * N * ((W : Int) + 2) - 1).natAbs + 1 = N * N * (W + 2) :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN (by omega))
  have h5 : ((N : Int) * N * N * W - 1).natAbs + 1 = N * N * N * W :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (Nat.mul_pos hNN hN) hW)
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    cEnv, cScope, List.lookup, Gen2.except_ok_bind, cDecls, h1, h2, h3, h4, h5]

theorem c_elems (N W AccW : Nat) : buildElems (cEnv N W AccW) design.pdesign.decls = .ok cElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, cEnv,
    cScope, List.lookup, Gen2.except_ok_bind, cElems]

/-- The instantiation environment. -/
abbrev cE (N W AccW : Nat) : IEnv := (cEnv N W AccW).withDecls (cDecls N W AccW)

/-- The static processes' templates. -/
def ctrlT : PProcess := match design.pdesign.processes with
  | [p, _, _] => p
  | _ => .alwaysFF "" (.block [])
def edge0T : PProcess := match design.pdesign.processes with
  | [_, p, _] => p
  | _ => .alwaysFF "" (.block [])
def doneT : PProcess := match design.pdesign.processes with
  | [_, _, p] => p
  | _ => .alwaysFF "" (.block [])

/-- The generate templates. -/
def edgeT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _] => p
  | _ => .alwaysFF "" (.block [])
def rtT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])
def coreT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

macro "c_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, cEnv, cScope, cDecls, cElems, ctrlT, edge0T, doneT, edgeT, rtT, coreT, ctrlP, edge0P, doneP, edgeP, rtP, coreP,
  sext, dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, divOperandWidthSum2, arraySelWidth, instDivParts2, *])

/-- The window facts of a select `x[lo +: w]` of a `c`-bit signal, in the forms the instantiation writes. -/
theorem winF (X Wd C : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = X) (hW : (w : Int) = Wd)
    (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = lo ∧ X + Wd - 1 < C ∧ 1 ≤ X + Wd ∧ (X + Wd).toNat = lo + w ∧ 0 < Wd ∧ Wd.toNat = w ∧
      X ≤ X + Wd - 1 := by
  subst hx hW hy; omega

/-- The window facts of a bit select `x[i]` of a `c`-bit signal. -/
theorem bitF (X C : Int) {i c : Nat} (h : i < c) (hx : (i : Int) = X) (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = i ∧ X < C ∧ ¬ X < 0 ∧ ¬ C ≤ X := by
  subst hx hy; omega

/-- The facts about a declared width `X = n > 0` that the instantiation's range checks use. -/
theorem declF (X : Int) {n : Nat} (hn : 0 < n) (hx : (n : Int) = X) :
    1 ≤ X ∧ (((X - 1).natAbs : Nat) : Int) + 1 = X ∧ (X - 1).natAbs + 1 = n := by
  subst hx; omega

/-- Every declared width of the design, in the `Int` forms the instantiation writes. -/
theorem decl_facts (N W AccW : Nat) (h : Rng N W AccW) :
    (1 ≤ (N : Int) * N * W ∧ ((((N : Int) * N * W - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * W ∧
      ((N : Int) * N * W - 1).natAbs + 1 = N * N * W) ∧
    (1 ≤ (N : Int) * N * AccW ∧ ((((N : Int) * N * AccW - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * AccW ∧
      ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW) ∧
    (1 ≤ (2 * (N : Int) - 1) * N * W ∧
      ((((2 * (N : Int) - 1) * N * W - 1).natAbs : Nat) : Int) + 1 = (2 * (N : Int) - 1) * N * W ∧
      ((2 * (N : Int) - 1) * N * W - 1).natAbs + 1 = (2 * N - 1) * N * W) ∧
    (1 ≤ (N : Int) * N * ((W : Int) + 2) ∧
      ((((N : Int) * N * ((W : Int) + 2) - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * ((W : Int) + 2) ∧
      ((N : Int) * N * ((W : Int) + 2) - 1).natAbs + 1 = N * N * (W + 2)) ∧
    (1 ≤ (N : Int) * N * N * W ∧ ((((N : Int) * N * N * W - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * N * W ∧
      ((N : Int) * N * N * W - 1).natAbs + 1 = N * N * N * W) := by
  have hN := h.hN; have hW := h.hW; have hA := h.hA
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  refine ⟨declF _ (Nat.mul_pos hNN hW) (by push_cast; rfl), declF _ (Nat.mul_pos hNN hA) (by push_cast; rfl),
    declF _ (Nat.mul_pos (Nat.mul_pos (show 0 < 2 * N - 1 by omega) hN) hW)
      (by rw [Int.natCast_mul, Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl),
    declF _ (Nat.mul_pos hNN (by omega)) (by push_cast; rfl),
    declF _ (Nat.mul_pos (Nat.mul_pos hNN hN) hW) (by push_cast; rfl)⟩

theorem ctrl_inst (N W AccW : Nat) (h : Rng N W AccW) : instProcess2 (cE N W AccW) cElems ctrlT = ctrlP N W := by
  have hN := h.hN; have hW := h.hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have hcast : ((2 * N - 1 : Nat) : Int) = 2 * (N : Int) - 1 := by omega
  have hNW : 0 < N * N * W := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hl0 : (⟨#[.l0]⟩ : LVec).width = 1 := rfl
  have hA1 : 0 < N * N * W := hNW
  have htn : ((N : Int) * N * W).toNat = N * N * W := by
    rw [show ((N : Int) * N * W) = ((N * N * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have eX : (2 * N - 1) * N * W + N * W = N * N * W + N * N * W := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.succ_mul, ← Nat.add_mul]; congr 1; omega
  have hX : 0 < N * W := Nat.mul_pos (by omega) (by omega)
  have hlt : ¬ (N * N * W + N * N * W < (2 * N - 1) * N * W) := by omega
  have hle : ¬ (N * N * W + N * N * W ≤ (2 * N - 1) * N * W) := by omega
  have hmx : max ((2 * N - 1) * N * W) (N * N * W + N * N * W) = N * N * W + N * N * W := by omega
  c_simp
  repeat (unfold instExpr2; c_simp)
  try and_intros
  all_goals first | rfl | decide | skip

theorem edge0_inst (N W AccW : Nat) (h : Rng N W AccW) : instProcess2 (cE N W AccW) cElems edge0T = edge0P N W := by
  have hN := h.hN; have hW := h.hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have hW1 : 0 < W := hW
  have hW0 : (0 : Int) < W := by omega
  have hw2 : 1 + (1 + W) = W + 2 := by omega
  have hcast : ((2 * N - 1 : Nat) : Int) = 2 * (N : Int) - 1 := by omega
  have w1 := winF 0 ((W : Int) + 2) ((N : Int) * N * ((W : Int) + 2))
    (lo := 0) (w := W + 2) (c := N * N * (W + 2))
    (by have := Nat.le_mul_of_pos_left (W + 2) (Nat.mul_pos (show 0 < N by omega) (show 0 < N by omega)); omega)
    (by omega) rfl (by push_cast; rfl) (by push_cast; rfl)
  have w2 := winF 0 (W : Int) ((N : Int) * N * W) (lo := 0) (w := W) (c := N * N * W)
    (by have := Nat.le_mul_of_pos_left W (Nat.mul_pos (show 0 < N by omega) (show 0 < N by omega)); omega)
    (by omega) rfl rfl (by push_cast; rfl)
  have e2 : (N - 1) * N * W + W ≤ (2 * N - 1) * N * W := by
    have : (N - 1) * N + 1 ≤ (2 * N - 1) * N := by
      have : (N - 1) * N + N ≤ (2 * N - 1) * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.mul_le_mul_right W this; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have w3 := winF (((N : Int) - 1) * N * W) (W : Int) ((2 * (N : Int) - 1) * N * W)
    (lo := (N - 1) * N * W) (w := W) (c := (2 * N - 1) * N * W) e2 (by omega)
    (by rw [Int.natCast_mul, Int.natCast_mul, Int.ofNat_sub hN]; rfl) rfl
    (by rw [Int.natCast_mul, Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl)
  have g1 : W + 2 ≤ N * N * (W + 2) := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have g2 : W ≤ N * N * W := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have g1' : ((W + 2 : Nat) : Int) ≤ ((N * N * (W + 2) : Nat) : Int) := Int.ofNat_le.mpr g1
  have g2' : ((W : Nat) : Int) ≤ ((N * N * W : Nat) : Int) := Int.ofNat_le.mpr g2
  push_cast at g1' g2'
  have f1 : min ((W : Int) + 2 - 1) 0 = 0 := by omega
  have f2 : max ((W : Int) + 2 - 1) 0 = (W : Int) + 2 - 1 := by omega
  have f3 : (W : Int) + 2 - 1 < (N : Int) * N * ((W : Int) + 2) := by omega
  have f4 : min ((W : Int) - 1) 0 = 0 := by omega
  have f5 : max ((W : Int) - 1) 0 = (W : Int) - 1 := by omega
  have f6 : (W : Int) - 1 < (N : Int) * N * W := by omega
  have f7 : ((W : Int) + 2 - 1 - 0 + 1).toNat = W + 2 := by omega
  have f8 : ((W : Int) - 1 - 0 + 1).toNat = W := by omega
  have f9 : ((W : Int) + 2).toNat = W + 2 := by omega
  have f10 : (W : Int).toNat = W := by omega
  c_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem done_inst (N W AccW : Nat) (h : Rng N W AccW) : instProcess2 (cE N W AccW) cElems doneT = doneP N W := by
  have hN := h.hN; have hW := h.hW
  have hNN : 1 ≤ N * N := Nat.mul_pos hN hN
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have b1 := bitF (((N : Int) * N - 1) * ((W : Int) + 2) + W + 1) ((N : Int) * N * ((W : Int) + 2))
    (i := (N * N - 1) * (W + 2) + W + 1) (c := N * N * (W + 2))
    (by have := Nat.mul_le_mul_right (W + 2) (show N * N - 1 + 1 ≤ N * N by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega)
    (by rw [Int.natCast_add, Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hNN]; push_cast; rfl) (by push_cast; rfl)
  have b2 := bitF (((N : Int) * N - 1) * ((W : Int) + 2) + W) ((N : Int) * N * ((W : Int) + 2))
    (i := (N * N - 1) * (W + 2) + W) (c := N * N * (W + 2))
    (by have := Nat.mul_le_mul_right (W + 2) (show N * N - 1 + 1 ≤ N * N by omega); rw [Nat.add_mul, Nat.one_mul] at this; omega)
    (by rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_sub hNN]; push_cast; rfl) (by push_cast; rfl)
  c_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem c_static (N W AccW : Nat) (h : Rng N W AccW) :
    design.pdesign.processes.map (instProcess2 (cE N W AccW) cElems) = [ctrlP N W, edge0P N W, doneP N W] := by
  rw [show design.pdesign.processes = [ctrlT, edge0T, doneT] from rfl]
  simp only [List.map_cons, List.map_nil, ctrl_inst N W AccW h, edge0_inst N W AccW h, done_inst N W AccW h]

theorem edge_inst (N W AccW x : Nat) (h : Rng N W AccW) (hx : x + 1 < N) :
    instProcess2 ((cE N W AccW).bindVal "x" x) cElems edgeT = edgeP N W x := by
  have hN := h.hN; have hW := h.hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have hjN : x + 1 + 1 ≤ N * N := by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega
  have w1 := winF (((x : Int) + 1) * ((W : Int) + 2)) ((W : Int) + 2) ((N : Int) * N * ((W : Int) + 2))
    (lo := (x + 1) * (W + 2)) (w := W + 2) (c := N * N * (W + 2))
    (by have := Nat.mul_le_mul_right (W + 2) hjN; rw [Nat.add_mul (x + 1) 1, Nat.one_mul] at this; exact this)
    (by omega) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  have hW1 : 0 < W := hW
  have hW0 : (0 : Int) < W := by omega
  have hw2 : 1 + (1 + W) = W + 2 := by omega
  have hcast : ((2 * N - 1 : Nat) : Int) = 2 * (N : Int) - 1 := by omega
  have e1 : ((N - 2 - x : Nat) : Int) = (N : Int) - 2 - x := by omega
  have e2 : (N - 2 - x) * N + x + 1 + 1 ≤ (2 * N - 1) * N := by
    have : (N - 2 - x) * N ≤ (N - 1) * N := Nat.mul_le_mul_right _ (by omega)
    have : (N - 1) * N + N ≤ (2 * N - 1) * N := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have w2 := winF ((((N : Int) - 2 - x) * N + x + 1) * W) (W : Int) ((2 * (N : Int) - 1) * N * W)
    (lo := ((N - 2 - x) * N + x + 1) * W) (w := W) (c := (2 * N - 1) * N * W)
    (by have := Nat.mul_le_mul_right W e2; rw [Nat.add_mul _ 1, Nat.one_mul] at this; exact this)
    (by omega) (by push_cast [e1]; rfl) rfl
    (by rw [Int.natCast_mul, Int.natCast_mul, Int.ofNat_sub (by omega)]; push_cast; rfl)
  c_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem rt_inst (N W AccW i j : Nat) (h : Rng N W AccW) (hi : i + 1 < N) (hj : j < N) :
    instProcess2 (((cE N W AccW).bindVal "i" i).bindVal "j" j) cElems rtT = rtP N W i j := by
  have hN := h.hN; have hW := h.hW
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have w1 := winF ((((i : Int) + 1) * N + j) * ((W : Int) + 2)) ((W : Int) + 2) ((N : Int) * N * ((W : Int) + 2))
    (lo := ((i + 1) * N + j) * (W + 2)) (w := W + 2) (c := N * N * (W + 2))
    (Lib.rowMajor_window_le hi hj) (by omega) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  have w2 := winF (((i : Int) * N + j) * ((W : Int) + 2)) ((W : Int) + 2) ((N : Int) * N * ((W : Int) + 2))
    (lo := (i * N + j) * (W + 2)) (w := W + 2) (c := N * N * (W + 2))
    (Lib.rowMajor_window_le (by omega) hj) (by omega) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  c_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem core_inst (N W AccW i j : Nat) (h : Rng N W AccW) (hi : i < N) (hj : j < N) :
    instProcess2 (((cE N W AccW).bindVal "i" i).bindVal "j" j) cElems coreT = coreP N W AccW i j := by
  have hN := h.hN; have hW := h.hW; have hA := h.hA
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨dA, dC, dB, dL, dM⟩ := decl_facts N W AccW h
  have hr := Lib.rowMajor_window_le (w := 1) hi hj
  simp only [Nat.mul_one] at hr
  have wC := winF (((i : Int) * N + j) * AccW) (AccW : Int) ((N : Int) * N * AccW)
    (lo := (i * N + j) * AccW) (w := AccW) (c := N * N * AccW)
    (Lib.rowMajor_window_le hi hj) (by omega) (by push_cast; rfl) rfl (by push_cast; rfl)
  have hmw : (i * N + j) * N * W + N * W ≤ N * N * N * W := by
    have := Lib.rowMajor_window_le (w := N * W) hi hj
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have wM := winF (((i : Int) * N + j) * N * W) ((N : Int) * W) ((N : Int) * N * N * W)
    (lo := (i * N + j) * N * W) (w := N * W) (c := N * N * N * W)
    hmw (Nat.mul_pos (by omega) (by omega)) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  have hmw1 : (i * N + j) * N * W + W ≤ N * N * N * W := by
    have : W ≤ N * W := Nat.le_mul_of_pos_left W (by omega)
    omega
  have wM1 := winF (((i : Int) * N + j) * N * W) (W : Int) ((N : Int) * N * N * W)
    (lo := (i * N + j) * N * W) (w := W) (c := N * N * N * W)
    hmw1 (by omega) (by push_cast; rfl) rfl (by push_cast; rfl)
  have bM := bitF (((i : Int) * N + j) * N * W + W - 1) ((N : Int) * N * N * W)
    (i := (i * N + j) * N * W + W - 1) (c := N * N * N * W) (by omega) (by omega) (by push_cast; rfl)
  have hla : i * N * W + N * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (show i + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have wA := winF ((i : Int) * N * W) ((N : Int) * W) ((N : Int) * N * W)
    (lo := i * N * W) (w := N * W) (c := N * N * W)
    hla (Nat.mul_pos (by omega) (by omega)) (by push_cast; rfl) (by push_cast; rfl) (by push_cast; rfl)
  have hlw := Lib.rowMajor_window_le (w := W + 2) hi hj
  have wL := winF (((i : Int) * N + j) * ((W : Int) + 2)) (W : Int) ((N : Int) * N * ((W : Int) + 2))
    (lo := (i * N + j) * (W + 2)) (w := W) (c := N * N * (W + 2))
    (by omega) (by omega) (by push_cast; rfl) rfl (by push_cast; rfl)
  have bL1 := bitF (((i : Int) * N + j) * ((W : Int) + 2) + W - 1) ((N : Int) * N * ((W : Int) + 2))
    (i := (i * N + j) * (W + 2) + W - 1) (c := N * N * (W + 2)) (by omega) (by omega) (by push_cast; rfl)
  have bL2 := bitF (((i : Int) * N + j) * ((W : Int) + 2) + W + 1) ((N : Int) * N * ((W : Int) + 2))
    (i := (i * N + j) * (W + 2) + W + 1) (c := N * N * (W + 2)) (by omega) (by push_cast; rfl) (by push_cast; rfl)
  have bL3 := bitF (((i : Int) * N + j) * ((W : Int) + 2) + W) ((N : Int) * N * ((W : Int) + 2))
    (i := (i * N + j) * (W + 2) + W) (c := N * N * (W + 2)) (by omega) (by push_cast; rfl) (by push_cast; rfl)
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  c_simp
  repeat (unfold instExpr2; c_simp)
  try and_intros
  all_goals first | rfl | decide | skip

/-- `for (g = 0; g < bound; g++) body`. -/
def genC (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

theorem c_gens_src : design.pdesign.generates =
    [genC "g_edge" "x" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) 3 ([edgeT].map .process),
     genC "g_rt_row" "i" (.binary (.m0 .sub) (.paramRef "N" none) (.int 1)) 3
       [genC "g_rt_col" "j" (.paramRef "N" none) 4 ([rtT].map .process)],
     genC "g_row" "i" (.paramRef "N" none) 4 [genC "g_col" "j" (.paramRef "N" none) 4 ([coreT].map .process)]] :=
  rfl

theorem toNat_sub_zero (n : Nat) : ((n : Int) - 0).toNat = n := by omega

/-- **The three generates expand to the edge columns, the routers and the cores.** -/
theorem c_gens (N W AccW F : Nat) (h : Rng N W AccW) (hF : N < F) :
    expandList2 (cE N W AccW) cElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have hN := h.hN
  have hNv : (cE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  have hv : ∀ (g : String) (v : Int), g ≠ "N" → ((cE N W AccW).bindVal g v).vals.lookup "N" = some (N : Int) :=
    fun g v hg => by rw [vals_lookup_bindVal_ne _ hg.symm, hNv]
  have hI : ∀ v : Int, ((cE N W AccW).bindVal "i" v).vals.lookup "N" = some (N : Int) := fun v => hv "i" v (by decide)
  have hJ : ∀ v : Int, ((cE N W AccW).bindVal "j" v).vals.lookup "N" = some (N : Int) := fun v => hv "j" v (by decide)
  have hN1 : ((N : Int) - 1 - 0).toNat = N - 1 := by omega
  rw [c_gens_src, genPs, List.append_assoc]
  refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_singleton_ok ?_))
  · have hX : ∀ v : Int, ((cE N W AccW).bindVal "x" v).vals.lookup "N" = some (N : Int) := fun v => hv "x" v (by decide)
    rw [genC, GenItem.expand2_genFor_ascending_processes (N := (N : Int) - 1) (evalInt_int 0)
      (fun v => isInt_binary_of rfl (isInt_paramRef_of (hX v)) rfl)
      (fun v => evalInt_sub_of (isInt_paramRef_of (hX v)) rfl (evalInt_paramRef_of (hX v)) rfl)
      (by rw [hN1]; omega), hN1, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, edgePs]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    exact edge_inst N W AccW x h (by have := List.mem_range.mp hx; omega)
  · rw [genC, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int) - 1)
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [rtT].map (instProcess2 (((cE N W AccW).bindVal "i" v).bindVal "j" w) cElems))
      (evalInt_int 0) (fun v => isInt_binary_of rfl (isInt_paramRef_of (hI v)) rfl)
      (fun v => evalInt_sub_of (isInt_paramRef_of (hI v)) rfl (evalInt_paramRef_of (hI v)) rfl)
      (by rw [hN1]; omega)]
    · simp only [intRange_zero, List.flatMap_map, hN1, List.map_cons, List.map_nil,
        Gen2.flatMap_singleton_map, rtPs]
      congr 1
      simp only [List.flatMap_def]
      congr 1
      refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
      exact rt_inst N W AccW i j h (by have := List.mem_range.mp hi; omega) (List.mem_range.mp hj)
    · intro v _ _
      apply expandList2_singleton_ok
      have hv' : ∀ (w : Int), (((cE N W AccW).bindVal "i" v).bindVal "j" w).vals.lookup "N" = some (N : Int) :=
        fun w => by rw [vals_lookup_bindVal_ne _ (by decide), hI v]
      rw [genC, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
        (fun w => isInt_paramRef_of (hv' w)) (fun w => evalInt_paramRef_of (hv' w))
        (by rw [toNat_sub_zero]; exact hF), toNat_sub_zero]
  · rw [genC, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [coreT].map (instProcess2 (((cE N W AccW).bindVal "i" v).bindVal "j" w) cElems))
      (evalInt_int 0) (fun v => isInt_paramRef_of (hI v))
      (fun v => evalInt_paramRef_of (hI v)) (by rw [toNat_sub_zero]; exact hF)]
    · simp only [intRange_zero, List.flatMap_map, toNat_sub_zero, List.map_cons, List.map_nil,
        Gen2.flatMap_singleton_map, corePs]
      congr 1
      simp only [List.flatMap_def]
      congr 1
      refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
      exact core_inst N W AccW i j h (List.mem_range.mp hi) (List.mem_range.mp hj)
    · intro v _ _
      apply expandList2_singleton_ok
      have hv' : ∀ (w : Int), (((cE N W AccW).bindVal "i" v).bindVal "j" w).vals.lookup "N" = some (N : Int) :=
        fun w => by rw [vals_lookup_bindVal_ne _ (by decide), hI v]
      rw [genC, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
        (fun w => isInt_paramRef_of (hv' w)) (fun w => evalInt_paramRef_of (hv' w))
        (by rw [toNat_sub_zero]; exact hF), toNat_sub_zero]

theorem c_instantiate2 (N W AccW : Nat) (h : Rng N W AccW) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (cEnv N W AccW) (cDecls N W AccW) cElems (genPs N W AccW)) := by
  refine PDesign.instantiate2_of_ok rfl (c_paramEnv _ _ _) (c_decls N W AccW h) (c_elems _ _ _)
    (c_gens N W AccW _ h ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem c_processes (N W AccW : Nat) (h : Rng N W AccW) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      ctrlP N W :: edge0P N W :: doneP N W :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (c_instantiate2 N W AccW h), PDesign.assemble2_processes, c_static N W AccW h]
  simp [design.pdesign]

/-! ### Pairwise disjoint writes -/

/-- Two processes write disjoint windows. -/
abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

/-- Every window of `p` is a window of the name `n`, inside `[lo, lo + w)`. -/
def Within (p : Process2) (n : String) (lo w : Nat) : Prop :=
  ∀ a ∈ p.procWins, a.1 = n ∧ ∃ l v, a.2 = some (l, v) ∧ lo ≤ l ∧ l + v ≤ lo + w

/-- Every window of `p` is of a name in `ns`. -/
def Names (p : Process2) (ns : List String) : Prop := ∀ a ∈ p.procWins, a.1 ∈ ns

theorem disj_of_names {p q : Process2} {ns ms : List String} (hp : Names p ns) (hq : Names q ms)
    (h : ∀ n ∈ ns, n ∉ ms) : Disj p q := by
  intro a ha b hb
  have h1 := hp a ha; have h2 := hq b hb
  simp only [DrvWin.overlaps, Bool.and_eq_false_iff]
  left
  rw [beq_eq_false_iff_ne]
  intro he; rw [he] at h1; exact h _ h1 h2

theorem disj_of_within {p q : Process2} {n : String} {lo w lo' w' : Nat} (hp : Within p n lo w)
    (hq : Within q n lo' w') (h : lo + w ≤ lo') : Disj p q := by
  intro a ha b hb
  obtain ⟨-, l, v, hav, h1, h2⟩ := hp a ha
  obtain ⟨-, l', v', hbv, h1', h2'⟩ := hq b hb
  simp only [DrvWin.overlaps, hav, hbv, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; right; omega

theorem names_of_within {p : Process2} {n : String} {lo w : Nat} (h : Within p n lo w) : Names p [n] :=
  fun a ha => by simp [(h a ha).1]

theorem names_of_all {p : Process2} {ns : List String}
    (h : p.procWins.all (fun a => ns.contains a.1) = true) : Names p ns := fun a ha => by
  have := List.all_eq_true.mp h a ha; simpa using this

theorem ctrl_names (N W : Nat) : Names (ctrlP N W) ["s", "bs"] :=
  names_of_all (by simp [ctrlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

theorem done_names (N W : Nat) : Names (doneP N W) ["done"] :=
  names_of_all (by simp [doneP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

theorem edge_within (N W x : Nat) : Within (edgeP N W x) "lnk" ((x + 1) * (W + 2)) (W + 2) := by
  intro a ha
  simp [edgeP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl <;> exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem edge0_within (N W : Nat) : Within (edge0P N W) "lnk" 0 (W + 2) := by
  intro a ha
  simp [edge0P, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem rt_within (N W i j : Nat) : Within (rtP N W i j) "lnk" (((i + 1) * N + j) * (W + 2)) (W + 2) := by
  intro a ha
  simp [rtP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl <;> exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem core_names (N W AccW i j : Nat) : Names (coreP N W AccW i j) ["C", "amem"] := by
  intro a ha
  simp [coreP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp

/-- Two cores write disjoint windows. -/
theorem core_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    Disj (coreP N W AccW i j) (coreP N W AccW i' j') := by
  have h1 := rowMajor_le (K := AccW) h
  have h2 := rowMajor_le (K := N * W) h
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h2
  intro a ha b hb
  simp [coreP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp [DrvWin.overlaps] <;> omega

theorem edge_mem {N W : Nat} {p : Process2} (hp : p ∈ edgePs N W) : ∃ x, x + 1 < N ∧ p = edgeP N W x := by
  simp only [edgePs, List.mem_map, List.mem_range] at hp
  obtain ⟨x, hx, rfl⟩ := hp; exact ⟨x, by omega, rfl⟩

theorem rt_mem {N W : Nat} {p : Process2} (hp : p ∈ rtPs N W) : ∃ i j, i + 1 < N ∧ j < N ∧ p = rtP N W i j := by
  simp only [rtPs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp; exact ⟨i, j, by omega, hj, rfl⟩

theorem core_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ corePs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p = coreP N W AccW i j := by
  simp only [corePs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp; exact ⟨i, j, hi, hj, rfl⟩

theorem gen_names (N W AccW : Nat) : ∀ p ∈ genPs N W AccW, Names p ["lnk", "C", "amem"] := by
  intro p hp a ha
  simp only [genPs, List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨j, -, rfl⟩ := edge_mem hp; have := (edge_within N W j a ha).1; simp [this]
  · obtain ⟨i, j, -, -, rfl⟩ := rt_mem hp; have := (rt_within N W i j a ha).1; simp [this]
  · obtain ⟨i, j, -, -, rfl⟩ := core_mem hp; have := core_names N W AccW i j a ha; simp_all

/-- Every link writer of the generates writes above unit `0`. -/
theorem gen_lnk_above (N W AccW : Nat) : ∀ q ∈ genPs N W AccW, Disj (edge0P N W) q := by
  intro q hq
  simp only [genPs, List.mem_append] at hq
  rcases hq with (hq | hq) | hq
  · obtain ⟨x, -, rfl⟩ := edge_mem hq
    exact disj_of_within (edge0_within N W) (edge_within N W x) (by
      have := Nat.le_mul_of_pos_left (W + 2) (show 0 < x + 1 by omega); omega)
  · obtain ⟨i, j, hi, -, rfl⟩ := rt_mem hq
    exact disj_of_within (edge0_within N W) (rt_within N W i j) (by
      have : 1 ≤ (i + 1) * N + j := by have := Nat.le_mul_of_pos_left N (show 0 < i + 1 by omega); omega
      have := Nat.mul_le_mul_right (W + 2) this; omega)
  · obtain ⟨i, j, -, -, rfl⟩ := core_mem hq
    exact disj_of_names (names_of_within (edge0_within N W)) (core_names N W AccW i j) (by decide)

theorem edge0_names (N W : Nat) : Names (edge0P N W) ["lnk"] := names_of_within (edge0_within N W)

theorem c_pairwise (N W AccW : Nat) : (ctrlP N W :: edge0P N W :: doneP N W :: genPs N W AccW).Pairwise Disj := by
  have hl : ∀ p ∈ edgePs N W ++ rtPs N W, Names p ["lnk"] := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨j, -, rfl⟩ := edge_mem hp; exact names_of_within (edge_within N W j)
    · obtain ⟨i, j, -, -, rfl⟩ := rt_mem hp; exact names_of_within (rt_within N W i j)
  have hc : ∀ p ∈ corePs N W AccW, Names p ["C", "amem"] := by
    intro p hp; obtain ⟨i, j, -, -, rfl⟩ := core_mem hp; exact core_names N W AccW i j
  refine .cons (fun q hq => ?_) (.cons (fun q hq => ?_) (.cons (fun q hq => ?_) ?_))
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (ctrl_names N W) (edge0_names N W) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (ctrl_names N W) (done_names N W) (by decide)
    · exact disj_of_names (ctrl_names N W) (gen_names N W AccW q hq) (by decide)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (edge0_names N W) (done_names N W) (by decide)
    · exact gen_lnk_above N W AccW q hq
  · exact disj_of_names (done_names N W) (gen_names N W AccW q hq) (by decide)
  · simp only [genPs, List.pairwise_append]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hxy => ?_)
      exact disj_of_within (edge_within N W _) (edge_within N W _) (rowMajor_le (by omega))
    · refine pairwise_flatMap_range (fun i _ => ?_) (fun i i' hii _ a ha b hb => ?_)
      · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hxy => ?_)
        exact disj_of_within (rt_within N W i _) (rt_within N W i _) (rowMajor_le (by omega))
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hb
        have := rowMajor_le (K := N) (show i + 1 < i' + 1 by omega)
        exact disj_of_within (rt_within N W i j) (rt_within N W i' j')
          (rowMajor_le (by have := List.mem_range.mp hj; omega))
    · intro p hp q hq
      obtain ⟨j, hj, rfl⟩ := edge_mem hp
      obtain ⟨i, j', -, -, rfl⟩ := rt_mem hq
      have h1 : (j + 1) * (W + 2) + (W + 2) ≤ ((i + 1) * N + j') * (W + 2) := by
        have := rowMajor_le (K := W + 2) (show j + 1 < (i + 1) * N + j' by
          have := Nat.le_mul_of_pos_left N (show 0 < i + 1 by omega); omega)
        exact this
      exact disj_of_within (edge_within N W j) (rt_within N W i j') h1
    · refine pairwise_flatMap_range (fun i _ => ?_) (fun i i' hii _ a ha b hb => ?_)
      · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hxy => ?_)
        exact core_disj (by omega)
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hb
        have := rowMajor_le (K := N) hii
        exact core_disj (by have := List.mem_range.mp hj; omega)
    · intro p hp q hq
      exact disj_of_names (hl p hp) (hc q hq) (by decide)

theorem c_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames
      (ctrlP N W :: edge0P N W :: doneP N W :: genPs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (c_pairwise N W AccW)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    simp only [genPs, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · obtain ⟨j, -, rfl⟩ := edge_mem hp; exact ⟨_, _, rfl⟩
    · obtain ⟨i, j, -, -, rfl⟩ := rt_mem hp; exact ⟨_, _, rfl⟩
    · obtain ⟨i, j, -, -, rfl⟩ := core_mem hp; exact ⟨_, _, rfl⟩
  · intro n hn
    simp only [List.mem_flatMap] at hn
    obtain ⟨p, hp, hn⟩ := hn
    have hw : n ∈ ["s", "bs", "done", "lnk", "C", "amem"] := by
      rcases List.mem_cons.mp hp with rfl | hp
      · revert n; simp [ctrlP, nb, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
      rcases List.mem_cons.mp hp with rfl | hp
      · revert n; simp [edge0P, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
      rcases List.mem_cons.mp hp with rfl | hp
      · revert n; simp [doneP, nb, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
      simp only [genPs, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · obtain ⟨j, -, rfl⟩ := edge_mem hp
        revert n; simp [edgeP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
      · obtain ⟨i, j, -, -, rfl⟩ := rt_mem hp
        revert n; simp [rtP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
      · obtain ⟨i, j, -, -, rfl⟩ := core_mem hp
        revert n; simp [coreP, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
          Stmt2.drvWinsList, Lhs2.drvWins]
    revert hw; simp only [List.mem_cons, List.mem_nil_iff, or_false]
    rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide

/-- **The loaded family is `cD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem c_sem_eq (N W AccW : Nat) (h : Rng N W AccW) : design.sem N W AccW = cD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [c_processes N W AccW h]; exact c_driversOk N W AccW)
  rw [h1, PDesign.instantiateD2_of_ok (c_instantiate2 N W AccW h)]
  simp only [PDesign.assemble2, c_static N W AccW h, cD]
  simp [design.pdesign]

/-! ## 2. G0's clock step for the loaded family -/

/-- **`cD` is in G0's decidable FF-only profile at every `(N, W, AccW)`.** -/
theorem c_profile (N W AccW : Nat) : (cD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by exact c_pairwise N W AccW)⟩
  simp [cD, genPs, edgePs, rtPs, corePs, ctrlP, edge0P, doneP, edgeP, rtP, coreP, sext, nb, List.all_flatMap, List.all_map,
    List.all_append, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB,
    Stmt2.listNbaStaticB, Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins, cDecls]

/-- The 11 signals of `cD`, in declaration order. -/
def MS (ck r st a b dn c s bs lk am : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", st), ("A", a), ("B", b), ("done", dn), ("C", c), ("s", s), ("bs", bs),
    ("lnk", lk), ("amem", am)]

theorem apply_c (N W AccW : Nat) (e : SvState) (ck r st a b dn c s bs lk am : LVec) :
    applyInputs2 (cD N W AccW) e (MS ck r st a b dn c s bs lk am) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" st) (appIn e "A" a) (appIn e "B" b)
        dn c s bs lk am := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [cD, cDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- `N + N - 1`, evaluated. -/
abbrev sMaxV (N : Nat) : LVec := ((LVec.ofInt 32 N).add (LVec.ofInt 32 N)).sub (LVec.ofInt 32 2)

/-- `N * W`, evaluated. -/
abbrev nwV (N W : Nat) : LVec := (LVec.ofInt 32 N).mul (LVec.ofInt 32 W)

/-- The edge buffer's load `{B, N*N*W zeros} >> 2NW`, evaluated. -/
def bsLoadV (N W : Nat) (b : LVec) : LVec :=
  ((LVec.concatMany #[b, LVec.replVec (N * N * W) (LVec.concatMany #[⟨#[.l0]⟩])]).shr
    ((nwV N W).add (nwV N W))).resizeU ((2 * N - 1) * N * W)

/-- The edge counter's updates. -/
def ctrlQ (N W : Nat) (r st b s bs : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "s" s (sMaxV N)]
  else if st.condTrue then [wr "s" s (zv 32), wr "bs" bs (bsLoadV N W b)]
  else wr "bs" bs (bs.shr ((LVec.ofInt 32 N).mul (LVec.ofInt 32 W))) ::
    (if (LVec.ofLogic (s.neLogical (sMaxV N))).condTrue then [wr "s" s (s.add (LVec.ofInt 32 1))] else [])

/-- The `done` handler's updates. -/
def doneQ (N W : Nat) (r st dn lk : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "done" dn ⟨#[.l0]⟩]
  else if st.condTrue then [wr "done" dn ⟨#[.l0]⟩]
  else if (lk.extract ((N * N - 1) * (W + 2) + W + 1) 1).condTrue then
    (if (lk.extract ((N * N - 1) * (W + 2) + W) 1).condTrue then [wr "done" dn ⟨#[.l1]⟩] else [])
  else []

/-- The wavelet edge column `0` sends at the start edge, evaluated. -/
def edge0SV (N W : Nat) (b : LVec) : LVec :=
  LVec.concatMany #[⟨#[.l1]⟩, LVec.ofLogic ((LVec.ofInt 32 N).eqLogical (LVec.ofInt 32 1)), b.extract 0 W]

/-- The wavelet edge column `0` sends after the start edge, evaluated. -/
def edge0V (N W : Nat) (s bs : LVec) : LVec :=
  LVec.concatMany #[⟨#[.l1]⟩, LVec.ofLogic (s.eqLogical ((LVec.ofInt 32 N).sub (LVec.ofInt 32 2))),
    bs.extract ((N - 1) * N * W) W]

/-- Edge column `0`'s updates. -/
def edge0Q (N W : Nat) (r st b s bs : LVec) : NbaQueue2 :=
  if r.condTrue then [("lnk", 0, (zv (W + 2)).resizeU (W + 2))]
  else if st.condTrue then [("lnk", 0, (edge0SV N W b).resizeU (W + 2))]
  else if (LVec.ofLogic (s.lt ((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)))).condTrue then
    [("lnk", 0, (edge0V N W s bs).resizeU (W + 2))]
  else [("lnk", 0, (zv (W + 2)).resizeU (W + 2))]

/-- The wavelet edge column `x + 1` sends, evaluated. -/
def edgeV (N W x : Nat) (s bs : LVec) : LVec :=
  LVec.concatMany #[⟨#[.l1]⟩,
    LVec.ofLogic (s.eqLogical (((LVec.ofInt 32 x).add (LVec.ofInt 32 N)).sub (LVec.ofInt 32 1))),
    bs.extract (((N - 2 - x) * N + x + 1) * W) W]

/-- Edge column `x + 1`'s updates. -/
def edgeQ (N W : Nat) (r s bs : LVec) (x : Nat) : NbaQueue2 :=
  if r.condTrue then [("lnk", (x + 1) * (W + 2), (zv (W + 2)).resizeU (W + 2))]
  else if (LVec.ofLogic ((s.sub (LVec.ofInt 32 x)).lt (LVec.ofInt 32 N))).condTrue then
    [("lnk", (x + 1) * (W + 2), (edgeV N W x s bs).resizeU (W + 2))]
  else [("lnk", (x + 1) * (W + 2), (zv (W + 2)).resizeU (W + 2))]

/-- Router `(i, j)`'s updates. -/
def rtQ (N W : Nat) (r lk : LVec) (i j : Nat) : NbaQueue2 :=
  if r.condTrue then [("lnk", ((i + 1) * N + j) * (W + 2), (zv (W + 2)).resizeU (W + 2))]
  else [("lnk", ((i + 1) * N + j) * (W + 2), (lk.extract ((i * N + j) * (W + 2)) (W + 2)).resizeU (W + 2))]

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- The new accumulator of core `(i, j)` on a valid wavelet, evaluated. -/
def coreV (N W AccW i j : Nat) (c lk am : LVec) : LVec :=
  (((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
    ((sxv am AccW ((i * N + j) * N * W) W).mul (sxv lk AccW ((i * N + j) * (W + 2)) W))).resizeU AccW

/-- Core `(i, j)`'s updates. -/
def coreQ (N W AccW : Nat) (st a c lk am : LVec) (i j : Nat) : NbaQueue2 :=
  if st.condTrue then
    [("C", (i * N + j) * AccW, (zv AccW).resizeU AccW),
      ("amem", (i * N + j) * N * W, (a.extract (i * N * W) (N * W)).resizeU (N * W))]
  else if (lk.extract ((i * N + j) * (W + 2) + W + 1) 1).condTrue then
    ("C", (i * N + j) * AccW, (coreV N W AccW i j c lk am).resizeU AccW) ::
      (if (LVec.ofLogic ((lk.extract ((i * N + j) * (W + 2) + W) 1).eqLogical ⟨#[.l0]⟩)).condTrue then
        [("amem", (i * N + j) * N * W, ((am.extract ((i * N + j) * N * W) (N * W)).shr (LVec.ofInt 32 W)).resizeU (N * W))]
      else [])
  else []

section run
variable (F : Nat) (hF : 30 ≤ F) (ck r st a b dn c s bs lk am : LVec)
include hF

theorem ctrl_run (N W : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (ctrlP N W) =
    .ok (MS ck r st a b dn c s bs lk am, ctrlQ N W r st b s bs) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : st.condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (s.neLogical (sMaxV N))).condTrue = true <;>
    simp [ctrlP, nb, c32, bsLoadV, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, wr, h1, h2, h3]

theorem edge0_run (N W : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (edge0P N W) =
    .ok (MS ck r st a b dn c s bs lk am, edge0Q N W r st b s bs) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold edge0Q
  by_cases h1 : r.condTrue = true <;> by_cases h2 : st.condTrue = true <;>
    by_cases h3 : (LVec.ofLogic (s.lt ((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [edge0P, edge0SV, edge0V, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h1, h2, h3]

theorem done_run (N W : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (doneP N W) =
    .ok (MS ck r st a b dn c s bs lk am, doneQ N W r st dn lk) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold doneQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : st.condTrue = true <;>
    by_cases h3 : (lk.extract ((N * N - 1) * (W + 2) + W + 1) 1).condTrue = true <;>
    by_cases h4 : (lk.extract ((N * N - 1) * (W + 2) + W) 1).condTrue = true <;>
    simp [doneP, nb, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem edge_run (N W j : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (edgeP N W j) =
    .ok (MS ck r st a b dn c s bs lk am, edgeQ N W r s bs j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold edgeQ
  by_cases h1 : r.condTrue = true <;>
    by_cases h2 : (LVec.ofLogic ((s.sub (LVec.ofInt 32 j)).lt (LVec.ofInt 32 N))).condTrue = true <;>
    simp [edgeP, edgeV, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      MS, SvState.lookup, evalBinOp, h1, h2]

theorem rt_run (N W i j : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (rtP N W i j) =
    .ok (MS ck r st a b dn c s bs lk am, rtQ N W r lk i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold rtQ
  by_cases h1 : r.condTrue = true <;>
    simp [rtP, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS, SvState.lookup, h1]

theorem core_run (N W AccW i j : Nat) : runEdgeProcess2 F (MS ck r st a b dn c s bs lk am) [] (coreP N W AccW i j) =
    .ok (MS ck r st a b dn c s bs lk am, coreQ N W AccW st a c lk am i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold coreQ
  by_cases h1 : st.condTrue = true <;>
    by_cases h2 : (lk.extract ((i * N + j) * (W + 2) + W + 1) 1).condTrue = true <;>
    by_cases h3 : (LVec.ofLogic ((lk.extract ((i * N + j) * (W + 2) + W) 1).eqLogical ⟨#[.l0]⟩)).condTrue = true <;>
    simp [coreP, coreV, sext, sxv, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, h1, h2, h3]

end run

/-- The cycle's updates, in process order. -/
def Q (N W AccW : Nat) (r st a b dn c s bs lk am : LVec) : NbaQueue2 :=
  ctrlQ N W r st b s bs ++ edge0Q N W r st b s bs ++ doneQ N W r st dn lk ++
    (List.range (N - 1)).flatMap (edgeQ N W r s bs) ++
    (List.range (N - 1)).flatMap (fun i => (List.range N).flatMap (rtQ N W r lk i)) ++
    (List.range N).flatMap (fun i => (List.range N).flatMap (coreQ N W AccW st a c lk am i))

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def cNext (N W AccW : Nat) (ck r st a b dn c s bs lk am : LVec) : SvState :=
  commitNba2 (MS ck r st a b dn c s bs lk am) (Q N W AccW r st a b dn c s bs lk am)

theorem c_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (cD N W AccW).processes.toList) :
    p = ctrlP N W ∨ p = edge0P N W ∨ p = doneP N W ∨ (∃ j, p = edgeP N W j) ∨ (∃ i j, p = rtP N W i j) ∨
      ∃ i j, p = coreP N W AccW i j := by
  simp only [cD, List.toList_toArray, List.mem_cons, genPs, List.mem_append] at hp
  rcases hp with rfl | rfl | rfl | (hp | hp) | hp
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · obtain ⟨j, -, rfl⟩ := edge_mem hp; exact .inr (.inr (.inr (.inl ⟨j, rfl⟩)))
  · obtain ⟨i, j, -, -, rfl⟩ := rt_mem hp; exact .inr (.inr (.inr (.inr (.inl ⟨i, j, rfl⟩))))
  · obtain ⟨i, j, -, -, rfl⟩ := core_mem hp; exact .inr (.inr (.inr (.inr (.inr ⟨i, j, rfl⟩))))

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus
entry, any state of the design's shape, every fuel from 30). -/
theorem c_cycle (N W AccW : Nat) (h : Rng N W AccW) (σ : ScheduleOracle) (e : SvState)
    (ck r st a b dn c s bs lk am : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r st a b dn c s bs lk am) kk =
      .ok (cNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" st) (appIn e "A" a)
        (appIn e "B" b) dn c s bs lk am, kk + 3) := by
  have hedge : ∀ p ∈ (cD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    rcases c_mem hp with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩ <;> rfl
  rw [c_sem_eq N W AccW h, cycleStep2_profile (c_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_c, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [cD, List.toList_toArray, List.flatMap_cons, ctrl_run F hF, edge0_run F hF, done_run F hF, genPs, edgePs,
      rtPs, corePs,
      List.flatMap_append, List.flatMap_assoc, List.flatMap_map, edge_run F hF, rt_run F hF, core_run F hF, cNext, Q,
      List.append_assoc]
  · intro i p hp
    rw [apply_c]
    rcases c_mem (List.mem_of_getElem? (by simpa using hp)) with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨i, j, rfl⟩ |
      ⟨i, j, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, edge0_run F hF _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, done_run F hF _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, edge_run F hF _ _ _ _ _ _ _ _ _ _ _ N W j⟩
    · exact ⟨_, rt_run F hF _ _ _ _ _ _ _ _ _ _ _ N W i j⟩
    · exact ⟨_, core_run F hF _ _ _ _ _ _ _ _ _ _ _ N W AccW i j⟩
  · rw [apply_c]; simp [MS]

/-! ## 3. The commit, register by register (`nbaFold`) -/

section commit
variable {ck r st a b dn c s bs lk am : LVec} {lo : Nat} {v : LVec}
theorem nb_dn : nbaStep (MS ck r st a b dn c s bs lk am) ("done", lo, v) =
    MS ck r st a b (dn.insertAt lo v) c s bs lk am := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (MS ck r st a b dn c s bs lk am) ("C", lo, v) =
    MS ck r st a b dn (c.insertAt lo v) s bs lk am := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_s : nbaStep (MS ck r st a b dn c s bs lk am) ("s", lo, v) =
    MS ck r st a b dn c (s.insertAt lo v) bs lk am := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bs : nbaStep (MS ck r st a b dn c s bs lk am) ("bs", lo, v) =
    MS ck r st a b dn c s (bs.insertAt lo v) lk am := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_lk : nbaStep (MS ck r st a b dn c s bs lk am) ("lnk", lo, v) =
    MS ck r st a b dn c s bs (lk.insertAt lo v) am := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_am : nbaStep (MS ck r st a b dn c s bs lk am) ("amem", lo, v) =
    MS ck r st a b dn c s bs lk (am.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- The registers' names. -/
abbrev RegName (n : String) : Prop := n = "done" ∨ n = "C" ∨ n = "s" ∨ n = "bs" ∨ n = "lnk" ∨ n = "amem"

/-- Committing a queue of writes to the six registers. -/
theorem commit_SS {ck r st a b : LVec} : ∀ (q : NbaQueue2) (dn c s bs lk am : LVec), (∀ u ∈ q, RegName u.1) →
    commitNba2 (MS ck r st a b dn c s bs lk am) q =
      MS ck r st a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "s" q s) (nbaFold "bs" q bs)
        (nbaFold "lnk" q lk) (nbaFold "amem" q am)
  | [], _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, s, bs, lk, am, h => by
    have hq := @commit_SS ck r st a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_s, nb_bs, nb_lk, nb_am, hq _ _ _ _ _ _ h', nbaFold]

theorem Q_names (N W AccW : Nat) (r st a b dn c s bs lk am : LVec) :
    ∀ u ∈ Q N W AccW r st a b dn c s bs lk am, RegName u.1 := by
  have h : ∀ q : NbaQueue2, q.all (fun u => u.1 == "done" || u.1 == "C" || u.1 == "s" || u.1 == "bs" ||
      u.1 == "lnk" || u.1 == "amem") = true → ∀ u ∈ q, RegName u.1 :=
    fun q h u hu => by simpa [or_assoc] using List.all_eq_true.mp h u hu
  refine h _ ?_
  simp only [Q, List.all_append, List.all_flatMap, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, List.all_eq_true.mpr fun k _ => ?_⟩, List.all_eq_true.mpr fun i _ =>
    List.all_eq_true.mpr fun j _ => ?_⟩, List.all_eq_true.mpr fun i _ => List.all_eq_true.mpr fun j _ => ?_⟩
  · unfold ctrlQ; (repeat' split) <;> simp
  · unfold edge0Q; (repeat' split) <;> simp
  · unfold doneQ; (repeat' split) <;> simp
  · unfold edgeQ; (repeat' split) <;> simp
  · unfold rtQ; (repeat' split) <;> simp
  · unfold coreQ; (repeat' split) <;> simp

/-- A fold that changes nothing. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    simp only [nbaFold, List.foldl_cons, if_neg (h u List.mem_cons_self)]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

section skip
variable {N W AccW : Nat} {r st a b dn c s bs lk am : LVec} {n : String} (x : LVec)
theorem skip_ctrl (h1 : n ≠ "s") (h2 : n ≠ "bs") : nbaFold n (ctrlQ N W r st b s bs) x = x :=
  nbaFold_of_forall_ne (by unfold ctrlQ; (repeat' split) <;> simp [Ne.symm h1, Ne.symm h2]) x
theorem skip_done (h : n ≠ "done") : nbaFold n (doneQ N W r st dn lk) x = x :=
  nbaFold_of_forall_ne (by unfold doneQ; (repeat' split) <;> simp [Ne.symm h]) x
theorem skip_edge0 (h : n ≠ "lnk") : nbaFold n (edge0Q N W r st b s bs) x = x :=
  nbaFold_of_forall_ne (by unfold edge0Q; (repeat' split) <;> simp [Ne.symm h]) x
theorem skip_edges (h : n ≠ "lnk") : nbaFold n ((List.range (N - 1)).flatMap (edgeQ N W r s bs)) x = x :=
  nbaFold_flatMap_eq_self (fun k y => nbaFold_of_forall_ne (by unfold edgeQ; (repeat' split) <;> simp [Ne.symm h]) y) _ x
theorem skip_rts (h : n ≠ "lnk") :
    nbaFold n ((List.range (N - 1)).flatMap (fun i => (List.range N).flatMap (rtQ N W r lk i))) x = x :=
  nbaFold_flatMap_eq_self (fun i y => nbaFold_flatMap_eq_self
    (fun j z => nbaFold_of_forall_ne (by unfold rtQ; (repeat' split) <;> simp [Ne.symm h]) z) _ y) _ x
theorem skip_cores (h1 : n ≠ "C") (h2 : n ≠ "amem") :
    nbaFold n ((List.range N).flatMap (fun i => (List.range N).flatMap (coreQ N W AccW st a c lk am i))) x = x :=
  nbaFold_flatMap_eq_self (fun i y => nbaFold_flatMap_eq_self
    (fun j z => nbaFold_of_forall_ne (by unfold coreQ; (repeat' split) <;> simp [Ne.symm h1, Ne.symm h2]) z) _ y) _ x
end skip

section fold
variable {N W AccW : Nat} {r st a b dn c s bs lk am : LVec} (x : LVec)
theorem fold_done : nbaFold "done" (Q N W AccW r st a b dn c s bs lk am) x = nbaFold "done" (doneQ N W r st dn lk) x := by
  simp only [Q, nbaFold_append]
  rw [skip_ctrl x (by decide) (by decide), skip_edge0 _ (by decide), skip_edges _ (by decide), skip_rts _ (by decide),
    skip_cores _ (by decide) (by decide)]
theorem fold_s : nbaFold "s" (Q N W AccW r st a b dn c s bs lk am) x = nbaFold "s" (ctrlQ N W r st b s bs) x := by
  simp only [Q, nbaFold_append]
  rw [skip_edge0 _ (by decide), skip_done _ (by decide), skip_edges _ (by decide), skip_rts _ (by decide),
    skip_cores _ (by decide) (by decide)]
theorem fold_bs : nbaFold "bs" (Q N W AccW r st a b dn c s bs lk am) x = nbaFold "bs" (ctrlQ N W r st b s bs) x := by
  simp only [Q, nbaFold_append]
  rw [skip_edge0 _ (by decide), skip_done _ (by decide), skip_edges _ (by decide), skip_rts _ (by decide),
    skip_cores _ (by decide) (by decide)]
theorem fold_lnk : nbaFold "lnk" (Q N W AccW r st a b dn c s bs lk am) x =
    nbaFold "lnk" ((List.range (N - 1)).flatMap (fun i => (List.range N).flatMap (rtQ N W r lk i)))
      (nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W r s bs)) (nbaFold "lnk" (edge0Q N W r st b s bs) x)) := by
  simp only [Q, nbaFold_append]
  rw [skip_ctrl _ (by decide) (by decide), skip_done _ (by decide), skip_cores _ (by decide) (by decide)]
theorem fold_C : nbaFold "C" (Q N W AccW r st a b dn c s bs lk am) x =
    nbaFold "C" ((List.range N).flatMap (fun i => (List.range N).flatMap (coreQ N W AccW st a c lk am i))) x := by
  simp only [Q, nbaFold_append]
  rw [skip_ctrl _ (by decide) (by decide), skip_edge0 _ (by decide), skip_done _ (by decide), skip_edges _ (by decide),
    skip_rts _ (by decide)]
theorem fold_amem : nbaFold "amem" (Q N W AccW r st a b dn c s bs lk am) x =
    nbaFold "amem" ((List.range N).flatMap (fun i => (List.range N).flatMap (coreQ N W AccW st a c lk am i))) x := by
  simp only [Q, nbaFold_append]
  rw [skip_ctrl _ (by decide) (by decide), skip_edge0 _ (by decide), skip_done _ (by decide), skip_edges _ (by decide),
    skip_rts _ (by decide)]
end fold

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem rowMajor_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem rowMajor_mod {N i j : Nat} (hj : j < N) : (i * N + j) % N = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- A row-major double loop is one loop over `r = i·N + j`. -/
theorem flatMap_rowMajor {α : Type} (M N : Nat) (q : Nat → Nat → List α) :
    ((List.range M).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (M * N)).flatMap fun r => q (r / N) (r % N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.flatMap_append, ih, Nat.succ_mul, List.range_add, List.flatMap_append,
      List.flatMap_map]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply flatMap_congr_mem
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp, rowMajor_div hj, rowMajor_mod hj]

/-! ## 4. The values of a transaction, `t` cycles after its start -/

attribute [local simp] condTrue_knownBit

section values
variable (N W AccW : Nat)

/-- `Σ_{k < t} A[i][k]·B[k][j]` in the integers (`Tasks.Matmul.dot` at `t = N`). -/
def psum {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

/-- The wavelets core `(i, j)` has consumed by snapshot `t`. -/
def fc (t i j : Nat) : Nat := min (t - (i + j + 1)) N

/-- The accumulators at snapshot `t`. -/
def accV (A B : BitVec (N * N * W)) (t : Nat) : BitVec (N * N * AccW) :=
  packBV AccW (N * N) fun r => BitVec.ofInt AccW (psum N W A B (fc N t (r / N) (r % N)) (r / N) (r % N))

/-- Row `i` of `A`. -/
def rowA (A : BitVec (N * N * W)) (i : Nat) : BitVec (N * W) := A.extractLsb' (i * N * W) (N * W)

/-- The local memories at snapshot `t`: row `i` of `A` with the consumed entries shifted out (the last one stays). -/
def amV (A : BitVec (N * N * W)) (t : Nat) : BitVec (N * N * (N * W)) :=
  packBV (N * W) (N * N) fun r => rowA N W A (r / N) >>> (min (fc N t (r / N) (r % N)) (N - 1) * W)

/-- Wavelet `k` of column `j`: `{valid = 1, last = (k = N - 1), payload = B[k][j]}`. -/
def wv (B : BitVec (N * N * W)) (k j : Nat) : BitVec (W + 2) :=
  (BitVec.ofBool true ++ (BitVec.ofBool (decide (k = N - 1)) ++ B.extractLsb' ((k * N + j) * W) W)).setWidth (W + 2)

/-- The link into core `(i, j)` at snapshot `t`. -/
def lw (B : BitVec (N * N * W)) (t i j : Nat) : BitVec (W + 2) :=
  if i + j + 1 ≤ t ∧ t < i + j + 1 + N then wv N W B (t - (i + j + 1)) j else 0

/-- All links at snapshot `t`. -/
def lkV (B : BitVec (N * N * W)) (t : Nat) : BitVec (N * N * (W + 2)) :=
  packBV (W + 2) (N * N) fun r => lw N W B t (r / N) (r % N)

/-- The edge buffer as the start edge loads it: row `m` holds row `m + 2 - N` of `B` (`0` outside). -/
def bs0 (B : BitVec (N * N * W)) : BitVec ((2 * N - 1) * N * W) :=
  ((B ++ (BitVec.ofBool false).replicate (N * N * W)) >>> (N * W + N * W)).setWidth ((2 * N - 1) * N * W)

/-- The edge buffer at time `t ≥ 1` (snapshot `t - 1`: shifted down `t - 1` rows). -/
def bsV (B : BitVec (N * N * W)) (t : Nat) : BitVec ((2 * N - 1) * N * W) := bs0 N W B >>> ((t - 1) * (N * W))

/-- The step counter at time `t ≥ 1` (snapshot `t - 1`, saturating at `2N - 2`). -/
def sV (t : Nat) : BitVec 32 := BitVec.ofNat 32 (min (t - 1) (2 * N - 2))

/-- No wavelet anywhere. -/
def lkZ : BitVec (N * N * (W + 2)) := packBV (W + 2) (N * N) fun _ => 0

end values

/-- Reading part of unit `r` of a packed family. -/
theorem extractLsb'_packBV_sub {W' n : Nat} (v : Nat → BitVec W') {r o w : Nat} (hr : r < n) (how : o + w ≤ W') :
    (packBV W' n v).extractLsb' (r * W' + o) w = (v r).extractLsb' o w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and, Bool.true_and,
    Nat.add_assoc, packBV]
  exact getLsbD_bvInsertEntries v _ n (Nat.le_refl _) r (o + i) hr (by omega)

section wavelet
variable {N W : Nat} (B : BitVec (N * N * W)) (k j : Nat)

theorem wv_valid : (wv N W B k j).extractLsb' (W + 1) 1 = BitVec.ofBool true := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain rfl : i = 0 := by omega
  have h1 : ¬ (W + 1 < 1 + W) := by omega
  have h2 : W + 1 < W + 2 := by omega
  have h3 : W + 1 - (1 + W) = 0 := by omega
  simp [wv, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append, h1, h2, h3]

theorem wv_last : (wv N W B k j).extractLsb' W 1 = BitVec.ofBool (decide (k = N - 1)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain rfl : i = 0 := by omega
  have h1 : W < 1 + W := by omega
  have h2 : W < W + 2 := by omega
  simp [wv, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getElem_append, h1, h2]

theorem wv_pay : (wv N W B k j).extractLsb' 0 W = B.extractLsb' ((k * N + j) * W) W := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have h1 : i < 1 + W := by omega
  have h2 : i < W + 2 := by omega
  simp [wv, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getElem_append,
    BitVec.getElem_extractLsb', h1, h2, hi]

end wavelet

theorem zero_extract (w o l : Nat) : (0 : BitVec w).extractLsb' o l = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

theorem ofBool_ne_zero (b : Bool) : decide (BitVec.ofBool b ≠ 0#1) = b := by cases b <;> decide

section links
variable {N W : Nat} (B : BitVec (N * N * W)) (t : Nat) {i j : Nat}

/-- The valid bit of the link into core `(i, j)`. -/
theorem lk_valid (hi : i < N) (hj : j < N) :
    ((LVec.ofBitVec (lkV N W B t)).extract ((i * N + j) * (W + 2) + W + 1) 1).condTrue =
      decide (i + j + 1 ≤ t ∧ t < i + j + 1 + N) := by
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hb : (i * N + j) * (W + 2) + W + 1 + 1 ≤ N * N * (W + 2) := by
    have := Lib.rowMajor_window_le (w := W + 2) hi hj; omega
  rw [LVec.extract_ofBitVec _ hb, Nat.add_assoc, lkV, extractLsb'_packBV_sub _ hr (by omega), rowMajor_div hj,
    rowMajor_mod hj, LVec.condTrue_ofBitVec, lw]
  split
  · rename_i h; rw [wv_valid, ofBool_ne_zero]; simp [h]
  · rename_i h; rw [zero_extract]; simp [h]

/-- The last bit of the link into core `(i, j)`. -/
theorem lk_last (hi : i < N) (hj : j < N) :
    ((LVec.ofBitVec (lkV N W B t)).extract ((i * N + j) * (W + 2) + W) 1) =
      LVec.ofBitVec (BitVec.ofBool (decide ((i + j + 1 ≤ t ∧ t < i + j + 1 + N) ∧ t - (i + j + 1) = N - 1))) := by
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hb : (i * N + j) * (W + 2) + W + 1 ≤ N * N * (W + 2) := by
    have := Lib.rowMajor_window_le (w := W + 2) hi hj; omega
  rw [LVec.extract_ofBitVec _ hb, lkV, extractLsb'_packBV_sub _ hr (by omega), rowMajor_div hj, rowMajor_mod hj, lw]
  split
  · rename_i h; rw [wv_last]; simp [h]
  · rename_i h; rw [zero_extract]; simp [h]

/-- The whole link into core `(i, j)` (the router's read). -/
theorem lk_unit (hi : i < N) (hj : j < N) :
    ((LVec.ofBitVec (lkV N W B t)).extract ((i * N + j) * (W + 2)) (W + 2)) = LVec.ofBitVec (lw N W B t i j) := by
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  rw [LVec.extract_ofBitVec _ (Lib.rowMajor_window_le hi hj), lkV, extractLsb'_packBV _ hr, rowMajor_div hj,
    rowMajor_mod hj]

end links

/-! ### The cores -/

theorem extract_extract {n : Nat} (x : BitVec n) (a b c d : Nat) (h : c + d ≤ b) :
    (x.extractLsb' a b).extractLsb' c d = x.extractLsb' (a + c) d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', hi, show c + i < b by omega, Nat.add_assoc]

/-- `{{AccW{y[lo+W-1]}}, y[lo +: W]}` of a known vector is the entry sign-extended. -/
theorem sxv_ofBitVec {n : Nat} (y : BitVec n) (AccW lo W : Nat) (hW : 1 ≤ W) (h : lo + W ≤ n) :
    sxv (LVec.ofBitVec y) AccW lo W = LVec.ofBitVec ((y.extractLsb' lo W).signExtend (AccW + W)) := by
  unfold sxv
  rw [LVec.extract_ofBitVec _ (show lo + W - 1 + 1 ≤ n by omega), LVec.extract_ofBitVec _ h]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  exact LVec.ofBitVec_replicate_append_eq_signExtend hW y AccW rfl

theorem rowMajor_lt {N i j : Nat} (hi : i < N) (hj : j < N) : i * N + j < N * N := by
  have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega

/-- Entry `0` of core `(i, j)`'s local memory. -/
theorem am_entry {N W : Nat} (A : BitVec (N * N * W)) (t : Nat) {i j : Nat} (hi : i < N) (hj : j < N) :
    (amV N W A t).extractLsb' ((i * N + j) * N * W) W =
      A.extractLsb' ((i * N + min (fc N t i j) (N - 1)) * W) W := by
  have hW : (i * N + j) * N * W = (i * N + j) * (N * W) + 0 := by rw [Nat.mul_assoc]; rfl
  have hm : min (fc N t i j) (N - 1) * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show min (fc N t i j) (N - 1) + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hNW : 0 + W ≤ N * W := by have := Nat.le_mul_of_pos_left W (show 0 < N by omega); omega
  rw [hW, amV, extractLsb'_packBV_sub _ (rowMajor_lt hi hj) hNW, rowMajor_div hj, rowMajor_mod hj,
    Lib.extractLsb'_ushiftRight, rowA, extract_extract _ _ _ _ _ (by omega), Nat.add_zero, Nat.add_mul]

/-- The payload of the link into core `(i, j)`. -/
theorem lk_pay {N W : Nat} (B : BitVec (N * N * W)) (t : Nat) {i j : Nat} (hi : i < N) (hj : j < N) :
    (lkV N W B t).extractLsb' ((i * N + j) * (W + 2)) W = (lw N W B t i j).extractLsb' 0 W := by
  rw [show (i * N + j) * (W + 2) = (i * N + j) * (W + 2) + 0 from rfl, lkV,
    extractLsb'_packBV_sub _ (rowMajor_lt hi hj) (by omega), rowMajor_div hj, rowMajor_mod hj]

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 1) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

/-- **The multiply-accumulate of core `(i, j)` on a valid wavelet.** -/
theorem core_mac {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (t : Nat) {i j : Nat}
    (hi : i < N) (hj : j < N) (hv : i + j + 1 ≤ t ∧ t < i + j + 1 + N) :
    (coreV N W AccW i j (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (lkV N W B t))
        (.ofBitVec (amV N W A t))).resizeU AccW =
      .ofBitVec (BitVec.ofInt AccW (psum N W A B (fc N (t + 1) i j) i j)) := by
  have hW := h.hW
  have hr := rowMajor_lt hi hj
  have hf : fc N t i j = t - (i + j + 1) := by unfold fc; omega
  have hf1 : fc N (t + 1) i j = t - (i + j + 1) + 1 := by unfold fc; omega
  have hmin : min (t - (i + j + 1)) (N - 1) = t - (i + j + 1) := by omega
  have bC : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
  have bM : (i * N + j) * N * W + W ≤ N * N * (N * W) := by
    have h1 := Lib.rowMajor_window_le (w := N * W) hi hj
    have h2 : W ≤ N * W := Nat.le_mul_of_pos_left W (by omega)
    rw [Nat.mul_assoc (i * N + j) N W]; omega
  have bL : (i * N + j) * (W + 2) + W ≤ N * N * (W + 2) := by
    have := Lib.rowMajor_window_le (w := W + 2) hi hj; omega
  unfold coreV
  rw [LVec.extract_ofBitVec _ bC, sxv_ofBitVec _ _ _ _ hW bM, sxv_ofBitVec _ _ _ _ hW bL, am_entry A t hi hj,
    lk_pay B t hi hj, accV, extractLsb'_packBV _ hr, rowMajor_div hj, rowMajor_mod hj, lw, if_pos hv, wv_pay, hf,
    hmin, hf1, psum_succ]
  simp only [LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend (show AccW ≤ AccW + W by omega), BitVec.ofInt_add, Tasks.Matmul.entry]

/-- `x == 1'b0` of a known bit. -/
theorem cond_eq0 (b : Bool) : (LVec.ofLogic ((LVec.ofBitVec (BitVec.ofBool b)).eqLogical ⟨#[.l0]⟩)).condTrue = !b := by
  rw [show (⟨#[.l0]⟩ : LVec) = LVec.ofLogic .l0 from rfl, LVec.ofLogic_l0, LVec.eqLogical_ofBitVec,
    LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec]
  cases b <;> decide

/-- **Core `(i, j)` writes its accumulator**: the sum to `fc (t + 1)` (unchanged when no wavelet arrives). -/
theorem core_C {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (t : Nat) {i j : Nat}
    (hi : i < N) (hj : j < N) (u : Nat → BitVec AccW)
    (hu : u (i * N + j) = BitVec.ofInt AccW (psum N W A B (fc N t i j) i j)) (a : LVec) :
    nbaFold "C" (coreQ N W AccW (knownBit false) a (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (lkV N W B t))
        (.ofBitVec (amV N W A t)) i j) (.ofBitVec (packBV AccW (N * N) u)) =
      .ofBitVec (packBV AccW (N * N) fun k =>
        if k = i * N + j then BitVec.ofInt AccW (psum N W A B (fc N (t + 1) i j) i j) else u k) := by
  have hup := fun x => bvInsertAt_packBV (W := AccW) u x (rowMajor_lt hi hj) rfl
  unfold coreQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, lk_valid B t hi hj]
  by_cases hv : i + j + 1 ≤ t ∧ t < i + j + 1 + N
  · rw [decide_eq_true hv, if_pos rfl, lk_last B t hi hj, cond_eq0, core_mac h A B t hi hj hv]
    split <;> simp [nbaFold, hup]
  · rw [decide_eq_false hv, if_neg Bool.false_ne_true]
    have hs : fc N (t + 1) i j = fc N t i j := by unfold fc; omega
    simp only [nbaFold, List.foldl_nil]
    congr 1
    apply packBV_congr; intro k _
    split
    · rename_i hk; rw [hk, hu, hs]
    · rfl

/-- **Core `(i, j)` writes its local memory**: the pointer advances unless the wavelet is the last. -/
theorem core_M {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    (t : Nat) {i j : Nat} (hi : i < N) (hj : j < N) (u : Nat → BitVec (N * W))
    (hu : u (i * N + j) = rowA N W A i >>> (min (fc N t i j) (N - 1) * W)) (a : LVec) :
    nbaFold "amem" (coreQ N W AccW (knownBit false) a (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (lkV N W B t))
        (.ofBitVec (amV N W A t)) i j) (.ofBitVec (packBV (N * W) (N * N) u)) =
      .ofBitVec (packBV (N * W) (N * N) fun k =>
        if k = i * N + j then rowA N W A i >>> (min (fc N (t + 1) i j) (N - 1) * W) else u k) := by
  have hN := h.hN; have hW := h.hW
  have hr := rowMajor_lt hi hj
  have hup := fun x => bvInsertAt_packBV (W := N * W) u x hr (Nat.mul_assoc _ _ _)
  have hW32 : W < 2 ^ 31 := by
    have : W ≤ N * N * W := Nat.le_mul_of_pos_left W (Nat.mul_pos (by omega) (by omega)); omega
  have hofW : LVec.ofInt 32 (W : Int) = LVec.ofBitVec (BitVec.ofNat 32 W) := by
    rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]
  have hWn : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have bM : (i * N + j) * N * W + N * W ≤ N * N * (N * W) := by
    have := Lib.rowMajor_window_le (w := N * W) hi hj
    rw [← Nat.mul_assoc] at this; exact this
  have hunit : (amV N W A t).extractLsb' ((i * N + j) * N * W) (N * W) =
      rowA N W A i >>> (min (fc N t i j) (N - 1) * W) := by
    rw [show (i * N + j) * N * W = (i * N + j) * (N * W) from Nat.mul_assoc _ _ _, amV, extractLsb'_packBV _ hr,
      rowMajor_div hj, rowMajor_mod hj]
  unfold coreQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, lk_valid B t hi hj]
  by_cases hv : i + j + 1 ≤ t ∧ t < i + j + 1 + N
  · rw [decide_eq_true hv, if_pos rfl, lk_last B t hi hj, cond_eq0]
    have hf : fc N t i j = t - (i + j + 1) := by unfold fc; omega
    have hf1 : fc N (t + 1) i j = t - (i + j + 1) + 1 := by unfold fc; omega
    by_cases hl : t - (i + j + 1) = N - 1
    · simp only [hv, hl, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, nbaFold,
        List.foldl_cons, List.foldl_nil, if_neg (show ("C" : String) ≠ "amem" by decide)]
      congr 1
      apply packBV_congr; intro k _
      split
      · rename_i hk; rw [hk, hu, hf, hf1, hl]; congr 2; omega
      · rfl
    · simp only [hv, hl, and_false, decide_false, Bool.not_false, ↓reduceIte, nbaFold, List.foldl_cons,
        List.foldl_nil, if_neg (show ("C" : String) ≠ "amem" by decide), if_pos rfl]
      rw [LVec.extract_ofBitVec _ bM, hunit, hofW, LVec.shr_ofBitVec, hWn, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
        LVec.insertAt_ofBitVec, hup, ← BitVec.shiftRight_add, hf, hf1]
      congr 1
      apply packBV_congr; intro k _
      split
      · congr 1
        have : min (t - (i + j + 1)) (N - 1) = t - (i + j + 1) := by omega
        have : min (t - (i + j + 1) + 1) (N - 1) = t - (i + j + 1) + 1 := by omega
        simp only [*, Nat.add_mul, Nat.one_mul]
      · rfl
  · rw [decide_eq_false hv, if_neg Bool.false_ne_true]
    have hs : fc N (t + 1) i j = fc N t i j := by unfold fc; omega
    simp only [nbaFold, List.foldl_nil]
    congr 1
    apply packBV_congr; intro k _
    split
    · rename_i hk; rw [hk, hu, hs]
    · rfl

/-- The cores' accumulators through a busy cycle. -/
theorem fold_C_busy {N W AccW : Nat} (h : Rng N W AccW) (A B : BitVec (N * N * W)) (t : Nat) (a : LVec) :
    nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap (coreQ N W AccW (knownBit false) a
        (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (lkV N W B t)) (.ofBitVec (amV N W A t)) i))
      (.ofBitVec (accV N W AccW A B t)) = .ofBitVec (accV N W AccW A B (t + 1)) := by
  have hN := h.hN
  rw [flatMap_rowMajor, nbaFold_flatMap]
  conv => lhs; arg 2; rw [accV]
  rw [foldl_range_ofBitVec_packBV (W := AccW) (N := N * N) _
    (fun r => BitVec.ofInt AccW (psum N W A B (fc N (t + 1) (r / N) (r % N)) (r / N) (r % N))) _ (N * N) ?_, accV]
  · exact congrArg _ (packBV_congr fun k hk => by simp [hk])
  · intro k u' hk hu'
    have hi : k / N < N := Nat.div_lt_of_lt_mul hk
    have hj : k % N < N := Nat.mod_lt _ (by omega)
    have hk' : k / N * N + k % N = k := by rw [Nat.mul_comm]; exact Nat.div_add_mod k N
    have := core_C h A B t hi hj u' (by rw [hk', hu']) a
    rw [hk'] at this; exact this

/-- The cores' local memories through a busy cycle. -/
theorem fold_M_busy {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    (t : Nat) (a : LVec) :
    nbaFold "amem" ((List.range N).flatMap fun i => (List.range N).flatMap (coreQ N W AccW (knownBit false) a
        (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (lkV N W B t)) (.ofBitVec (amV N W A t)) i))
      (.ofBitVec (amV N W A t)) = .ofBitVec (amV N W A (t + 1)) := by
  have hN := h.hN
  rw [flatMap_rowMajor, nbaFold_flatMap]
  conv => lhs; arg 2; rw [amV]
  rw [foldl_range_ofBitVec_packBV (W := N * W) (N := N * N) _
    (fun r => rowA N W A (r / N) >>> (min (fc N (t + 1) (r / N) (r % N)) (N - 1) * W)) _ (N * N) ?_, amV]
  · exact congrArg _ (packBV_congr fun k hk => by simp [hk])
  · intro k u' hk hu'
    have hi : k / N < N := Nat.div_lt_of_lt_mul hk
    have hj : k % N < N := Nat.mod_lt _ (by omega)
    have hk' : k / N * N + k % N = k := by rw [Nat.mul_comm]; exact Nat.div_add_mod k N
    have := core_M h hNW A B t hi hj u' (by rw [hk', hu']) a
    rw [hk'] at this; exact this

/-! ### The edge I/O and the routers -/

/-- A family of unit writes at the units `off, off + 1, …`, each ignoring the old content. -/
theorem foldl_range_packBV_off {W' n : Nat} (off : Nat) (ops : Nat → LVec → LVec) (g u : Nat → BitVec W') :
    ∀ m, (∀ k u', k < m → ops k (.ofBitVec (packBV W' n u')) =
        .ofBitVec (packBV W' n (fun i => if i = k + off then g k else u' i))) →
      (List.range m).foldl (fun acc k => ops k acc) (.ofBitVec (packBV W' n u)) =
        .ofBitVec (packBV W' n (fun i => if off ≤ i ∧ i < off + m then g (i - off) else u i))
  | 0, _ => by
    simp only [List.range_zero, List.foldl_nil]
    exact congrArg _ (packBV_congr fun k _ => by rw [if_neg (by omega)])
  | m + 1, h => by
    rw [List.range_succ, List.foldl_append,
      foldl_range_packBV_off off ops g u m (fun k u' hk => h k u' (by omega)),
      List.foldl_cons, List.foldl_nil, h m _ (by omega)]
    congr 2; funext i
    by_cases h1 : i = m + off
    · subst h1; rw [if_pos rfl, if_pos (by omega), show m + off - off = m by omega]
    · rw [if_neg h1]
      by_cases h2 : off ≤ i ∧ i < off + m
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem ofInt_nat32 {v : Nat} (h : v < 2 ^ 32) : LVec.ofInt 32 (v : Int) = LVec.ofBitVec (BitVec.ofNat 32 v) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem ofNat32_eq {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : BitVec.ofNat 32 x = BitVec.ofNat 32 y ↔ x = y := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]


/-- The edge's window test `s - x < N` (column `x + 1`). -/
theorem edge_lt {N x t : Nat} (hN : N < 2 ^ 30) (hx : x + 1 < N) :
    (BitVec.ofNat 32 (min t (2 * N - 2)) - BitVec.ofNat 32 x < BitVec.ofNat 32 N) ↔ (x ≤ t ∧ t < x + N) := by
  rw [BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

/-- The edge's last test `s == x + N - 1` (column `x + 1`). -/
theorem edge_eq {N x t : Nat} (hN : N < 2 ^ 30) (hx : x + 1 < N) :
    (BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 x + BitVec.ofNat 32 N - 1#32) ↔ (t = x + N - 1) := by
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

/-- Column `0`'s window test `s < N - 1`. -/
theorem edge0_lt {N t : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) :
    (BitVec.ofNat 32 (min t (2 * N - 2)) < BitVec.ofNat 32 N - 1#32) ↔ t + 1 < N := by
  rw [BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

/-- Column `0`'s last test `s == N - 2`, inside its window. -/
theorem edge0_eq {N t : Nat} (hN : N < 2 ^ 30) (ht : t + 1 < N) :
    (BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 N - 2#32) ↔ (t + 1 = N - 1) := by
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

/-- A bit of the loaded edge buffer: bit `idx` is bit `idx - (N - 2)·N·W` of `B`. -/
theorem bs0_bit {N W : Nat} (B : BitVec (N * N * W)) {idx : Nat} (hlo : (N - 2) * (N * W) ≤ idx) (h2 : 2 ≤ N)
    (hhi : idx < (2 * N - 1) * N * W) :
    (bs0 N W B).getLsbD idx = B.getLsbD (idx - (N - 2) * (N * W)) := by
  have e7 : N * N * W = N * (N * W) := Nat.mul_assoc _ _ _
  have eN : N * (N * W) = (N - 2) * (N * W) + (N * W + N * W) := by
    rw [show N * W + N * W = 2 * (N * W) by omega, ← Nat.add_mul]; congr 1; omega
  rw [bs0, BitVec.getLsbD_setWidth, decide_eq_true hhi, Bool.true_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, if_neg (by omega)]
  congr 1; omega

/-- The edge buffer's row `N - 2 - x`, column `x + 1`, at time `t + 1`: row `t - x` of `B`. -/
theorem bs_read {N W : Nat} (B : BitVec (N * N * W)) {t x : Nat} (hx : x + 1 < N) (hv : x ≤ t ∧ t < x + N) :
    (bsV N W B (t + 1)).extractLsb' (((N - 2 - x) * N + x + 1) * W) W =
      B.extractLsb' (((t - x) * N + x + 1) * W) W := by
  apply BitVec.eq_of_getLsbD_eq; intro q hq
  have e1 : ((N - 2 - x) * N + x + 1) * W = (N - 2 - x) * (N * W) + (x + 1) * W := by
    rw [Nat.add_assoc, Nat.add_mul, Nat.mul_assoc]
  have e2 : ((t - x) * N + x + 1) * W = (t - x) * (N * W) + (x + 1) * W := by
    rw [Nat.add_assoc, Nat.add_mul, Nat.mul_assoc]
  have e3 : t * (N * W) + (N - 2 - x) * (N * W) = (t - x) * (N * W) + (N - 2) * (N * W) := by
    rw [← Nat.add_mul, ← Nat.add_mul]; congr 1; omega
  have e5 : (2 * N - 1) * N * W = N * (N * W) + (N - 2) * (N * W) + N * W := by
    rw [Nat.mul_assoc, ← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  have h1 : (t - x) * (N * W) + N * W ≤ N * (N * W) := by
    have := Nat.mul_le_mul_right (N * W) (show t - x + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have h2 : (x + 1) * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show x + 1 + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', decide_eq_true hq, Bool.true_and, Bool.true_and,
    bsV, BitVec.getLsbD_ushiftRight, show t + 1 - 1 = t by omega, e1, e2,
    bs0_bit B (by omega) (by omega) (by omega)]
  congr 1; omega

/-- The edge buffer's row `N - 1`, column `0`, at time `t + 1`: row `t + 1` of `B`. -/
theorem bs_read0 {N W : Nat} (B : BitVec (N * N * W)) {t : Nat} (ht : t + 1 < N) :
    (bsV N W B (t + 1)).extractLsb' ((N - 1) * N * W) W = B.extractLsb' (((t + 1) * N + 0) * W) W := by
  apply BitVec.eq_of_getLsbD_eq; intro q hq
  have e1 : (N - 1) * N * W = (N - 1) * (N * W) := Nat.mul_assoc _ _ _
  have e2 : ((t + 1) * N + 0) * W = (t + 1) * (N * W) := by rw [Nat.add_zero, Nat.mul_assoc]
  have e3 : t * (N * W) + (N - 1) * (N * W) = (t + 1) * (N * W) + (N - 2) * (N * W) := by
    rw [← Nat.add_mul, ← Nat.add_mul]; congr 1; omega
  have e5 : (2 * N - 1) * N * W = N * (N * W) + (N - 2) * (N * W) + N * W := by
    rw [Nat.mul_assoc, ← Nat.add_mul, ← Nat.succ_mul]; congr 1; omega
  have h1 : (t + 1) * (N * W) + N * W ≤ N * (N * W) := by
    have := Nat.mul_le_mul_right (N * W) (show t + 1 + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  have h2 : W ≤ N * W := Nat.le_mul_of_pos_left W (by omega)
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', decide_eq_true hq, Bool.true_and, Bool.true_and,
    bsV, BitVec.getLsbD_ushiftRight, show t + 1 - 1 = t by omega, e1, e2,
    bs0_bit B (by omega) (by omega) (by omega)]
  congr 1; omega

theorem ofInt32_one : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide

theorem zv_resize (w : Nat) : (zv w).resizeU w = LVec.ofBitVec (0#w) := by
  rw [zv, LVec.replicate_l0, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem l1_eq : (⟨#[.l1]⟩ : LVec) = LVec.ofBitVec (BitVec.ofBool true) := by
  rw [show (⟨#[.l1]⟩ : LVec) = LVec.ofLogic .l1 from rfl, LVec.ofLogic_l1]

/-- Edge column `j` outside its window sends nothing (any buffer). -/
theorem edge_idle {N W : Nat} (hN : N < 2 ^ 30) {t x : Nat} (hx : x + 1 < N) (hv : ¬ (x ≤ t ∧ t < x + N))
    (bs : LVec) :
    edgeQ N W (knownBit false) (.ofBitVec (BitVec.ofNat 32 (min t (2 * N - 2)))) bs x =
      [("lnk", (x + 1) * (W + 2), .ofBitVec (0 : BitVec (W + 2)))] := by
  have hj32 : x < 2 ^ 32 := by omega
  have hN32 : N < 2 ^ 32 := by omega
  unfold edgeQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, ofInt_nat32 hj32, ofInt_nat32 hN32, LVec.sub_ofBitVec,
    LVec.lt_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec, ofBool_ne_zero,
    decide_eq_false (fun h => hv ((edge_lt hN hx).mp h)), if_neg Bool.false_ne_true, zv_resize]
  rfl

theorem ofInt32_two : LVec.ofInt 32 2 = LVec.ofBitVec 2#32 := by decide

/-- Column `0` outside its window (and no `start`) sends nothing (any buffer). -/
theorem edge0_idle {N W : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) {t : Nat} (hv : ¬ (t + 1 < N)) (b bs : LVec) :
    edge0Q N W (knownBit false) (knownBit false) b (.ofBitVec (BitVec.ofNat 32 (min t (2 * N - 2)))) bs =
      [("lnk", 0, .ofBitVec (0 : BitVec (W + 2)))] := by
  have hN32 : N < 2 ^ 32 := by omega
  unfold edge0Q
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, ofInt_nat32 hN32, ofInt32_one,
    LVec.sub_ofBitVec, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec, ofBool_ne_zero,
    decide_eq_false (fun h => hv ((edge0_lt hN hN1).mp h)), if_neg Bool.false_ne_true, zv_resize]
  rfl

/-- Column `0` at the start edge sends wavelet `0`. -/
theorem edge0_start {N W : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) (hW : 1 ≤ W) (B : BitVec (N * N * W)) (s bs : LVec) :
    edge0Q N W (knownBit false) (knownBit true) (.ofBitVec B) s bs = [("lnk", 0, .ofBitVec (lw N W B 1 0 0))] := by
  have hN32 : N < 2 ^ 32 := by omega
  have hb : 0 + W ≤ N * N * W := by
    have := Nat.le_mul_of_pos_left W (Nat.mul_pos (show 0 < N by omega) (show 0 < N by omega)); omega
  have hl : decide (BitVec.ofNat 32 N = 1#32) = decide (0 = N - 1) := by
    rw [decide_eq_decide, ofNat32_eq hN32 (show 1 < 2 ^ 32 by omega)]; omega
  have hlw : lw N W B 1 0 0 = wv N W B 0 0 := by
    unfold lw; rw [if_pos (by omega)]
  unfold edge0Q edge0SV
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, condTrue_knownBit, if_pos rfl, ofInt_nat32 hN32, ofInt32_one,
    LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, LVec.extract_ofBitVec _ hb, l1_eq, hl, hlw]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.concat_ofBitVec, LVec.resizeU_ofBitVec, wv,
    Nat.zero_mul, Nat.zero_add]

/-- Column `0` after the start edge sends wavelet `t + 1` while `t + 1 < N`. -/
theorem edge0_busy {N W : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) (B : BitVec (N * N * W)) (b : LVec) (t : Nat) :
    edge0Q N W (knownBit false) (knownBit false) b (.ofBitVec (sV N (t + 1))) (.ofBitVec (bsV N W B (t + 1))) =
      [("lnk", 0, .ofBitVec (lw N W B (t + 2) 0 0))] := by
  by_cases hv : t + 1 < N
  · have hN32 : N < 2 ^ 32 := by omega
    have hb : (N - 1) * N * W + W ≤ (2 * N - 1) * N * W := by
      have : (N - 1) * N + 1 ≤ (2 * N - 1) * N := by
        have : (N - 1) * N + N ≤ (2 * N - 1) * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
        omega
      have := Nat.mul_le_mul_right W this; rw [Nat.add_mul, Nat.one_mul] at this; exact this
    have hl : decide (BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 N - 2#32) = decide (t + 1 = N - 1) := by
      rw [decide_eq_decide]; exact edge0_eq hN hv
    unfold edge0Q edge0V
    rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, sV, show t + 1 - 1 = t by omega,
      ofInt_nat32 hN32, ofInt32_one, LVec.sub_ofBitVec, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec,
      ofBool_ne_zero, decide_eq_true ((edge0_lt hN hN1).mpr hv), if_pos rfl, ofInt32_two, LVec.sub_ofBitVec,
      LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, LVec.extract_ofBitVec _ hb, bs_read0 B hv, l1_eq, hl]
    have hlw : lw N W B (t + 2) 0 0 = wv N W B (t + 1) 0 := by
      unfold lw; rw [if_pos (by omega), show t + 2 - (0 + 0 + 1) = t + 1 by omega]
    rw [hlw]
    simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.concat_ofBitVec, LVec.resizeU_ofBitVec, wv]
  · have := edge0_idle (W := W) hN hN1 hv b (.ofBitVec (bsV N W B (t + 1)))
    rw [sV, show t + 1 - 1 = t by omega, this]
    congr 3
    all_goals (unfold lw; rw [if_neg (by omega)])

/-- Edge column `x + 1` in its window sends wavelet `t - x`. -/
theorem edge_busy {N W : Nat} (hN : N < 2 ^ 30) (B : BitVec (N * N * W)) {t x : Nat} (hx : x + 1 < N)
    (hv : x ≤ t ∧ t < x + N) :
    edgeQ N W (knownBit false) (.ofBitVec (sV N (t + 1))) (.ofBitVec (bsV N W B (t + 1))) x =
      [("lnk", (x + 1) * (W + 2), .ofBitVec (lw N W B (t + 2) 0 (x + 1)))] := by
  have hj32 : x < 2 ^ 32 := by omega
  have hN32 : N < 2 ^ 32 := by omega
  have hb : ((N - 2 - x) * N + x + 1) * W + W ≤ (2 * N - 1) * N * W := by
    have e : (N - 2 - x) * N + x + 1 + 1 ≤ (2 * N - 1) * N := by
      have : (N - 2 - x) * N ≤ (N - 1) * N := Nat.mul_le_mul_right _ (by omega)
      have : (N - 1) * N + N ≤ (2 * N - 1) * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.mul_le_mul_right W e; rw [Nat.add_mul _ 1, Nat.one_mul] at this; exact this
  have hl : decide (BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 x + BitVec.ofNat 32 N - 1#32) =
      decide (t - x = N - 1) := by
    rw [decide_eq_decide]; rw [edge_eq hN hx]; omega
  unfold edgeQ edgeV
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, sV, show t + 1 - 1 = t by omega, ofInt_nat32 hj32,
    ofInt_nat32 hN32, LVec.sub_ofBitVec, LVec.lt_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec, ofBool_ne_zero,
    decide_eq_true ((edge_lt hN hx).mpr hv), if_pos rfl, ofInt32_one, LVec.add_ofBitVec,
    LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, LVec.extract_ofBitVec _ hb, bs_read B hx hv,
    l1_eq, hl]
  have hlw : lw N W B (t + 2) 0 (x + 1) = wv N W B (t - x) (x + 1) := by
    unfold lw; rw [if_pos (by omega), show t + 2 - (0 + (x + 1) + 1) = t - x by omega]
  rw [hlw]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.concat_ofBitVec, LVec.resizeU_ofBitVec, wv]
  rfl

/-- The router of core `(i, j)` copies the link into `(i, j)`. -/
theorem rt_q {N W : Nat} (L : Nat → BitVec (W + 2)) {i j : Nat} (hi : i < N) (hj : j < N) :
    rtQ N W (knownBit false) (.ofBitVec (packBV (W + 2) (N * N) L)) i j =
      [("lnk", ((i + 1) * N + j) * (W + 2), .ofBitVec (L (i * N + j)))] := by
  unfold rtQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, LVec.extract_ofBitVec _ (Lib.rowMajor_window_le hi hj),
    extractLsb'_packBV _ (rowMajor_lt hi hj), LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

/-- **The links through a cycle without reset**: the edge columns' outputs into row 0, row `i` into row `i + 1`. -/
theorem lnk_fold {N W : Nat} (hN : 1 ≤ N) (st b s bs : LVec) (E L : Nat → BitVec (W + 2))
    (hE0 : edge0Q N W (knownBit false) st b s bs = [("lnk", 0, .ofBitVec (E 0))])
    (hE : ∀ x, x + 1 < N → edgeQ N W (knownBit false) s bs x = [("lnk", (x + 1) * (W + 2), .ofBitVec (E (x + 1)))]) :
    nbaFold "lnk" ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap
        (rtQ N W (knownBit false) (.ofBitVec (packBV (W + 2) (N * N) L)) i))
      (nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W (knownBit false) s bs))
        (nbaFold "lnk" (edge0Q N W (knownBit false) st b s bs) (.ofBitVec (packBV (W + 2) (N * N) L)))) =
      .ofBitVec (packBV (W + 2) (N * N) fun k => if k < N then E k else L (k - N)) := by
  have hNN0 : 0 < N * N := Nat.mul_pos (by omega) (by omega)
  have h0 : nbaFold "lnk" (edge0Q N W (knownBit false) st b s bs) (.ofBitVec (packBV (W + 2) (N * N) L)) =
      .ofBitVec (packBV (W + 2) (N * N) fun i => if i = 0 then E 0 else L i) := by
    rw [hE0]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, if_pos rfl, LVec.insertAt_ofBitVec, ite_true, ↓reduceIte]
    rw [bvInsertAt_packBV _ _ hNN0 (by simp)]
  have he : nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W (knownBit false) s bs))
      (.ofBitVec (packBV (W + 2) (N * N) fun i => if i = 0 then E 0 else L i)) =
      .ofBitVec (packBV (W + 2) (N * N) fun i => if 1 ≤ i ∧ i < 1 + (N - 1) then E (i - 1 + 1) else
        (if i = 0 then E 0 else L i)) := by
    rw [nbaFold_flatMap, foldl_range_packBV_off (W' := W + 2) (n := N * N) 1 _ (fun x => E (x + 1)) _ (N - 1) ?_]
    intro k u' hk
    rw [hE k (by omega)]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, if_pos rfl, LVec.insertAt_ofBitVec, ite_true,
      ↓reduceIte]
    rw [bvInsertAt_packBV _ _ (by have := Nat.le_mul_of_pos_left N (show 0 < N by omega); omega) rfl]
  rw [h0, he, flatMap_rowMajor, nbaFold_flatMap,
    foldl_range_packBV_off (W' := W + 2) (n := N * N) N _ (fun r => L (r / N * N + r % N)) _ ((N - 1) * N) ?_]
  · refine congrArg _ (packBV_congr fun k hk => ?_)
    by_cases h1 : k < N
    · rw [if_neg (by omega), if_pos h1]
      by_cases hk0 : k = 0
      · subst hk0; rw [if_neg (by omega), if_pos rfl]
      · rw [if_pos (by omega), show k - 1 + 1 = k by omega]
    · have hNN : N * N = (N - 1) * N + N := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [if_pos (show N ≤ k ∧ k < N + (N - 1) * N by omega), if_neg h1]
      congr 1; rw [Nat.mul_comm]; exact Nat.div_add_mod (k - N) N
  · intro k u' hk
    have hi : k / N < N - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
    have hj : k % N < N := Nat.mod_lt _ (by omega)
    rw [rt_q L (show k / N < N by omega) hj]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, if_pos rfl, LVec.insertAt_ofBitVec, ite_true,
      ↓reduceIte]
    rw [bvInsertAt_packBV _ _ (by have := rowMajor_lt (show k / N + 1 < N by omega) hj; omega) rfl]
    congr 2; funext x
    have : (k / N + 1) * N + k % N = k + N := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_right_comm, Nat.mul_comm, Nat.div_add_mod]
    rw [this]

/-! ### The edge counter, the edge buffer and `done` -/

theorem sMax_eq {N : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) : sMaxV N = LVec.ofBitVec (BitVec.ofNat 32 (2 * N - 2)) := by
  rw [sMaxV, ofInt_nat32 (show N < 2 ^ 32 by omega), ofInt32_two, LVec.add_ofBitVec, LVec.sub_ofBitVec]
  congr 1
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

theorem width_ofBitVec' {w : Nat} (x : BitVec w) : (LVec.ofBitVec x).width = w := LVec.width_ofBitVec x

/-- The step counter through a cycle without reset or start. -/
theorem s_busy {N W : Nat} (hN : N < 2 ^ 30) (hN1 : 1 ≤ N) (b bs : LVec) (t : Nat) :
    nbaFold "s" (ctrlQ N W (knownBit false) (knownBit false) b (.ofBitVec (sV N (t + 1))) bs)
      (.ofBitVec (sV N (t + 1))) = .ofBitVec (sV N (t + 2)) := by
  have h32 : 2 * N - 2 < 2 ^ 32 := by omega
  unfold ctrlQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, sMax_eq hN hN1,
    sV, show t + 1 - 1 = t by omega, LVec.neLogical_ofBitVec, LVec.ofLogic_ofBool, LVec.condTrue_ofBitVec,
    ofBool_ne_zero]
  by_cases ht : 2 * N - 2 ≤ t
  · rw [decide_eq_true (show BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 (2 * N - 2) by
      rw [show min t (2 * N - 2) = 2 * N - 2 by omega])]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, nbaFold, List.foldl_cons, List.foldl_nil,
      if_neg (show ("bs" : String) ≠ "s" by decide)]
    rw [sV, show min (t + 2 - 1) (2 * N - 2) = min t (2 * N - 2) by omega]
  · rw [decide_eq_false (show ¬ BitVec.ofNat 32 (min t (2 * N - 2)) = BitVec.ofNat 32 (2 * N - 2) by
      rw [ofNat32_eq (by omega) h32]; omega)]
    simp only [Bool.not_false, ↓reduceIte, nbaFold, List.foldl_cons, List.foldl_nil,
      if_neg (show ("bs" : String) ≠ "s" by decide), ite_true, wr, ofInt32_one, LVec.add_ofBitVec,
      LVec.resizeU_ofBitVec, width_ofBitVec', BitVec.setWidth_eq]
    rw [LVec.insertAt_zero_of_width_eq (by simp)]
    congr 1
    rw [sV, ← BitVec.toNat_inj, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Nat.reducePow] at hN ⊢
    omega

/-- The edge buffer through a cycle without reset or start: one row down. -/
theorem bs_busy {N W : Nat} (hNW : N * N * W < 2 ^ 31) (hN1 : 1 ≤ N) (hW1 : 1 ≤ W) (B : BitVec (N * N * W)) (b s : LVec) (t : Nat) :
    nbaFold "bs" (ctrlQ N W (knownBit false) (knownBit false) b s (.ofBitVec (bsV N W B (t + 1))))
      (.ofBitVec (bsV N W B (t + 1))) = .ofBitVec (bsV N W B (t + 2)) := by
  have hNW' : N * W < 2 ^ 32 := by
    have : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hW : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W (by omega)) hNW'
  have hN : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW1) hNW'
  have hm : (LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)) = LVec.ofBitVec (BitVec.ofNat 32 (N * W)) := by
    rw [ofInt_nat32 hN, ofInt_nat32 hW, LVec.mul_ofBitVec]
    congr 1
    rw [← BitVec.toNat_inj, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hW]
  unfold ctrlQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hm]
  have hskip : ∀ (q : NbaQueue2) (x : LVec), (∀ u ∈ q, u.1 = "s") → nbaFold "bs" q x = x :=
    fun q x hq => nbaFold_of_forall_ne (fun u hu => by rw [hq u hu]; decide) x
  simp only [nbaFold, List.foldl_cons, ite_true, ↓reduceIte, wr]
  rw [← nbaFold, hskip _ _ (by split <;> simp)]
  rw [LVec.shr_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNW', LVec.resizeU_ofBitVec, width_ofBitVec',
    BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq (by simp), bsV, bsV, ← BitVec.shiftRight_add,
    show t + 2 - 1 = t + 1 by omega, show t + 1 - 1 = t by omega,
    show (t + 1) * (N * W) = t * (N * W) + N * W from by rw [Nat.add_mul, Nat.one_mul]]

/-- `done` through a busy cycle: it rises exactly at the far core's last wavelet. -/
theorem done_busy {N W : Nat} (hN : 1 ≤ N) (B : BitVec (N * N * W)) {t : Nat} (ht : t + 1 ≤ 3 * N - 1) :
    nbaFold "done" (doneQ N W (knownBit false) (knownBit false) (knownBit false) (.ofBitVec (lkV N W B t)))
      (knownBit false) = knownBit (decide (t + 1 = 3 * N - 1)) := by
  have e : N * N - 1 = (N - 1) * N + (N - 1) := by
    have : N * N = (N - 1) * N + N := by rw [← Nat.succ_mul]; congr 1; omega
    omega
  unfold doneQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, e,
    lk_valid B t (show N - 1 < N by omega) (show N - 1 < N by omega),
    lk_last B t (show N - 1 < N by omega) (show N - 1 < N by omega), LVec.condTrue_ofBitVec, ofBool_ne_zero]
  by_cases hd : t + 1 = 3 * N - 1
  · rw [decide_eq_true (show N - 1 + (N - 1) + 1 ≤ t ∧ t < N - 1 + (N - 1) + 1 + N by omega), if_pos rfl,
      decide_eq_true (show (N - 1 + (N - 1) + 1 ≤ t ∧ t < N - 1 + (N - 1) + 1 + N) ∧
        t - (N - 1 + (N - 1) + 1) = N - 1 by omega), if_pos rfl, decide_eq_true hd]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, wr, ↓reduceIte]
    rw [show (knownBit false).width = 1 from rfl, LVec.resizeU_one_l1,
      LVec.insertAt_zero_of_width_eq (by rfl)]
  · rw [decide_eq_false hd]
    by_cases hv : N - 1 + (N - 1) + 1 ≤ t ∧ t < N - 1 + (N - 1) + 1 + N
    · rw [decide_eq_true hv, if_pos rfl,
        decide_eq_false (show ¬ ((N - 1 + (N - 1) + 1 ≤ t ∧ t < N - 1 + (N - 1) + 1 + N) ∧
          t - (N - 1 + (N - 1) + 1) = N - 1) by omega), if_neg Bool.false_ne_true]
      rfl
    · rw [decide_eq_false hv, if_neg Bool.false_ne_true]
      rfl

/-! ## 5. The registers through a cycle -/

/-- The range bound keeps `N` small. -/
theorem N_small {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) : N < 2 ^ 16 := by
  have hW := h.hW
  have h1 : N * N ≤ N * N * W := Nat.le_mul_of_pos_right _ (by omega)
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.mul_le_mul hc hc
  simp only [Nat.reducePow, Nat.reduceMul] at this hNW ⊢
  omega

/-- **One busy cycle**: from the state `t` cycles after a start to the state at `t + 1`; `done` rises exactly at
`t + 1 = 3N - 1`. -/
theorem next_step {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W)) {t : Nat}
    (ht : t + 2 ≤ 3 * N - 1) (ck a b : LVec) :
    cNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) (.ofBitVec (accV N W AccW A B (t + 1)))
        (.ofBitVec (sV N (t + 1))) (.ofBitVec (bsV N W B (t + 1))) (.ofBitVec (lkV N W B (t + 1)))
        (.ofBitVec (amV N W A (t + 1))) =
      MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 2 = 3 * N - 1)))
        (.ofBitVec (accV N W AccW A B (t + 2))) (.ofBitVec (sV N (t + 2))) (.ofBitVec (bsV N W B (t + 2)))
        (.ofBitVec (lkV N W B (t + 2))) (.ofBitVec (amV N W A (t + 2))) := by
  have hN := h.hN; have hW := h.hW
  have hN30 : N < 2 ^ 30 := by have := N_small h hNW; omega
  rw [cNext, commit_SS _ _ _ _ _ _ _ (Q_names _ _ _ _ _ _ _ _ _ _ _ _ _), fold_done, fold_C, fold_s, fold_bs,
    fold_lnk, fold_amem, done_busy (t := t + 1) hN B (by omega), fold_C_busy h A B (t + 1) a, s_busy hN30 hN b _ t,
    bs_busy hNW hN hW B b _ t, fold_M_busy h hNW A B (t + 1) a]
  congr 1
  rw [lkV, lnk_fold hN _ _ _ _ (fun j => lw N W B (t + 2) 0 j) _ (edge0_busy hN30 hN B b t) ?_, lkV]
  · refine congrArg _ (packBV_congr fun k hk => ?_)
    by_cases h1 : k < N
    · rw [if_pos h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1]
      obtain ⟨m, rfl⟩ : ∃ m, k = m + N := ⟨k - N, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_div_right _ (by omega), Nat.add_mod_right, lw, lw]
      rw [show m / N + 1 + m % N + 1 = m / N + m % N + 1 + 1 by omega,
        show t + 2 - (m / N + m % N + 1 + 1) = t + 1 - (m / N + m % N + 1) by omega]
      congr 1
      simp only [eq_iff_iff]; omega
  · intro x hx
    by_cases hv : x ≤ t ∧ t < x + N
    · exact edge_busy hN30 B hx hv
    · rw [sV, show t + 1 - 1 = t by omega, edge_idle hN30 hx hv]
      congr 3
      all_goals (unfold lw; rw [if_neg (by omega)])

theorem lkZ_eq (N W : Nat) : lkZ N W = lkV N W 0 (3 * N) := by
  unfold lkZ lkV
  refine packBV_congr fun k hk => ?_
  have hi : k / N < N := Nat.div_lt_of_lt_mul hk
  have hj : k % N < N := Nat.mod_lt _ (by have := Nat.pos_of_ne_zero (fun h : N = 0 => by simp [h] at hk); omega)
  unfold lw; rw [if_neg (by omega)]

/-- A core whose link holds no valid wavelet, and no `start`, writes nothing. -/
theorem core_idle {N W AccW : Nat} (B : BitVec (N * N * W)) {T i j : Nat} (hi : i < N) (hj : j < N)
    (hv : ¬ (i + j + 1 ≤ T ∧ T < i + j + 1 + N)) (a c am : LVec) :
    coreQ N W AccW (knownBit false) a c (.ofBitVec (lkV N W B T)) am i j = [] := by
  unfold coreQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, lk_valid B T hi hj, decide_eq_false hv, if_neg Bool.false_ne_true]

theorem nbaFold_flatMap_eq_self_mem {α : Type} {n : String} {f : α → NbaQueue2} : ∀ (l : List α),
    (∀ k ∈ l, ∀ x, nbaFold n (f k) x = x) → ∀ x, nbaFold n (l.flatMap f) x = x
  | [], _, _ => rfl
  | a :: l, h, x => by
    rw [List.flatMap_cons, nbaFold_append, h a List.mem_cons_self,
      nbaFold_flatMap_eq_self_mem l (fun k hk => h k (List.mem_cons_of_mem _ hk))]

/-- No core writes anything in an idle cycle (no `start`, no valid wavelet). -/
theorem cores_idle {N W AccW : Nat} (a c am : LVec) (n : String) (x : LVec) :
    nbaFold n ((List.range N).flatMap fun i => (List.range N).flatMap
      (coreQ N W AccW (knownBit false) a c (.ofBitVec (lkZ N W)) am i)) x = x := by
  rw [lkZ_eq]
  refine nbaFold_flatMap_eq_self_mem _ (fun i hi y => nbaFold_flatMap_eq_self_mem _ (fun j hj z => ?_) y) x
  have hi := List.mem_range.mp hi; have hj := List.mem_range.mp hj
  rw [core_idle 0 hi hj (by omega)]; rfl

/-- `done` holds in an idle cycle. -/
theorem done_idle {N W : Nat} (hN : 1 ≤ N) (dn : LVec) :
    nbaFold "done" (doneQ N W (knownBit false) (knownBit false) dn (.ofBitVec (lkZ N W))) dn = dn := by
  have e : N * N - 1 = (N - 1) * N + (N - 1) := by
    have : N * N = (N - 1) * N + N := by rw [← Nat.succ_mul]; congr 1; omega
    omega
  unfold doneQ
  rw [condTrue_knownBit, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, e, lkZ_eq,
    lk_valid 0 _ (show N - 1 < N by omega) (show N - 1 < N by omega), decide_eq_false (by omega),
    if_neg Bool.false_ne_true]
  rfl

/-- The links stay empty in an idle cycle. -/
theorem lnk_idle {N W : Nat} (hN : 1 ≤ N) (hN30 : N < 2 ^ 30) (b bs : LVec) :
    nbaFold "lnk" ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap
        (rtQ N W (knownBit false) (.ofBitVec (lkZ N W)) i))
      (nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W (knownBit false) (.ofBitVec (sV N (2 * N - 1))) bs))
        (nbaFold "lnk" (edge0Q N W (knownBit false) (knownBit false) b (.ofBitVec (sV N (2 * N - 1))) bs)
          (.ofBitVec (lkZ N W)))) = .ofBitVec (lkZ N W) := by
  unfold lkZ
  rw [lnk_fold hN _ _ _ _ (fun _ => 0) _ (by rw [sV]; exact edge0_idle hN30 hN (by omega) b bs)
    (fun x hx => by rw [sV]; exact edge_idle hN30 hx (by omega) bs)]
  exact congrArg _ (packBV_congr fun k _ => by split <;> rfl)

/-- The counter holds at its idle value. -/
theorem s_idle {N W : Nat} (hN30 : N < 2 ^ 30) (hN : 1 ≤ N) (b bs : LVec) :
    nbaFold "s" (ctrlQ N W (knownBit false) (knownBit false) b (.ofBitVec (sV N (2 * N - 1))) bs)
      (.ofBitVec (sV N (2 * N - 1))) = .ofBitVec (sV N (2 * N - 1)) := by
  have e : 2 * N - 1 = (2 * N - 2) + 1 := by omega
  rw [e, s_busy hN30 hN b bs (2 * N - 2)]
  unfold sV; congr 2; omega

/-- **An idle cycle** (no reset, no `start`) from a state with no wavelet keeps `done`, `C`, the counter and the
links; the edge buffer moves on. -/
theorem next_idle {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (ck a b dn c bs am : LVec) :
    ∃ bs', cNext N W AccW ck (knownBit false) (knownBit false) a b dn c (.ofBitVec (sV N (2 * N - 1))) bs
        (.ofBitVec (lkZ N W)) am =
      MS ck (knownBit false) (knownBit false) a b dn c (.ofBitVec (sV N (2 * N - 1))) bs' (.ofBitVec (lkZ N W)) am := by
  have hN := h.hN
  have hN30 : N < 2 ^ 30 := by have := N_small h hNW; omega
  rw [cNext, commit_SS _ _ _ _ _ _ _ (Q_names _ _ _ _ _ _ _ _ _ _ _ _ _), fold_done, fold_C, fold_s, fold_lnk,
    fold_amem, done_idle hN, cores_idle, cores_idle, s_idle hN30 hN, lnk_idle hN hN30]
  exact ⟨_, rfl⟩

theorem divmod_eq (k N : Nat) : k / N * N + k % N = k := by rw [Nat.mul_comm]; exact Nat.div_add_mod k N

/-- The accumulators on `start`: every one cleared, whatever it held. -/
theorem cores_start_C {N W AccW : Nat} (hN : 1 ≤ N) (a cv lk am c : LVec) (hc : c.width = N * N * AccW) :
    nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap
      (coreQ N W AccW (knownBit true) a cv lk am i)) c = .ofBitVec (packBV AccW (N * N) fun _ => 0) := by
  have key : ∀ k acc, nbaFold "C" (coreQ N W AccW (knownBit true) a cv lk am (k / N) (k % N)) acc =
      acc.insertAt (k * AccW) (.ofBitVec (0 : BitVec AccW)) := by
    intro k acc
    unfold coreQ
    rw [condTrue_knownBit, if_pos rfl, divmod_eq]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, zv_resize,
      if_neg (show ("amem" : String) ≠ "C" by decide)]
    rfl
  rw [flatMap_rowMajor, nbaFold_flatMap]
  simp only [key]
  exact LVec.insertEntries_ofBitVec (fun _ => 0) c hc

/-- The local memories on `start`: core `(i, j)` loads row `i` of `A`, whatever it held. -/
theorem cores_start_M {N W AccW : Nat} (hN : 1 ≤ N) (A : BitVec (N * N * W)) (cv lk am : LVec)
    (ham : am.width = N * N * N * W) :
    nbaFold "amem" ((List.range N).flatMap fun i => (List.range N).flatMap
      (coreQ N W AccW (knownBit true) (.ofBitVec A) cv lk am i)) am =
      .ofBitVec (packBV (N * W) (N * N) fun k => rowA N W A (k / N)) := by
  have key : ∀ k acc, k < N * N → nbaFold "amem" (coreQ N W AccW (knownBit true) (.ofBitVec A) cv lk am (k / N) (k % N)) acc =
      acc.insertAt (k * (N * W)) (.ofBitVec (rowA N W A (k / N))) := by
    intro k acc hk
    have hi : k / N < N := Nat.div_lt_of_lt_mul hk
    have hb : k / N * N * W + N * W ≤ N * N * W := by
      have := Nat.mul_le_mul_right (N * W) (show k / N + 1 ≤ N by omega)
      rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
    unfold coreQ
    rw [condTrue_knownBit, if_pos rfl, divmod_eq, LVec.extract_ofBitVec _ hb, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq, Nat.mul_assoc k N W]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte,
      if_neg (show ("C" : String) ≠ "amem" by decide)]
    rfl
  rw [flatMap_rowMajor, nbaFold_flatMap]
  have hfold : ∀ (l : List Nat), (∀ k ∈ l, k < N * N) → ∀ x : LVec,
      l.foldl (fun acc k => nbaFold "amem" (coreQ N W AccW (knownBit true) (.ofBitVec A) cv lk am (k / N) (k % N)) acc) x =
        l.foldl (fun acc k => acc.insertAt (k * (N * W)) (.ofBitVec (rowA N W A (k / N)))) x := by
    intro l; induction l with
    | nil => intros; rfl
    | cons k l ih =>
      intro hl x
      simp only [List.foldl_cons]
      rw [key k x (hl k List.mem_cons_self)]
      exact ih (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) _
  rw [hfold _ (fun k hk => List.mem_range.mp hk)]
  exact LVec.insertEntries_ofBitVec (fun k => rowA N W A (k / N)) am (by rw [ham, Nat.mul_assoc])

/-- The links on a reset: every one cleared, whatever it held. -/
theorem lnk_reset {N W : Nat} (hN : 1 ≤ N) (st b s bs lk : LVec) (hlk : lk.width = N * N * (W + 2)) :
    nbaFold "lnk" ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap (rtQ N W (knownBit true) lk i))
      (nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W (knownBit true) s bs))
        (nbaFold "lnk" (edge0Q N W (knownBit true) st b s bs) lk)) = .ofBitVec (lkZ N W) := by
  have ke0 : ∀ acc, nbaFold "lnk" (edge0Q N W (knownBit true) st b s bs) acc =
      acc.insertAt (0 * (W + 2)) (.ofBitVec (0 : BitVec (W + 2))) := by
    intro acc; unfold edge0Q
    rw [condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, zv_resize, Nat.zero_mul]
    rfl
  have ke : ∀ x acc, nbaFold "lnk" (edgeQ N W (knownBit true) s bs x) acc =
      acc.insertAt ((1 + x) * (W + 2)) (.ofBitVec (0 : BitVec (W + 2))) := by
    intro x acc; unfold edgeQ
    rw [condTrue_knownBit, if_pos rfl, Nat.add_comm 1 x]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, zv_resize]
    rfl
  have kr : ∀ r acc, nbaFold "lnk" (rtQ N W (knownBit true) lk (r / N) (r % N)) acc =
      acc.insertAt ((1 + (N - 1) + r) * (W + 2)) (.ofBitVec (0 : BitVec (W + 2))) := by
    intro r acc; unfold rtQ
    rw [condTrue_knownBit, if_pos rfl]
    have : (r / N + 1) * N + r % N = 1 + (N - 1) + r := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_right_comm, divmod_eq]; omega
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, zv_resize, this]
    rfl
  rw [ke0, flatMap_rowMajor, nbaFold_flatMap, nbaFold_flatMap]
  simp only [ke, kr]
  have hNN : N * N = 1 + (N - 1) + (N - 1) * N := by
    have : N * N = (N - 1) * N + N := by rw [← Nat.succ_mul]; congr 1; omega
    omega
  rw [lkZ, ← LVec.insertEntries_ofBitVec (fun _ => (0 : BitVec (W + 2))) lk hlk, LVec.insertEntries]
  conv => rhs; rw [hNN, List.range_add, List.range_add, List.foldl_append, List.foldl_append, List.foldl_map,
    List.foldl_map]
  simp

/-- **A reset cycle** clears `done` and every link and sets the counter to its idle value, from any state of the
shape. -/
theorem next_reset {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (ck st a b dn c s bs lk am : LVec)
    (hdn : dn.width = 1) (hs : s.width = 32) (hlk : lk.width = N * N * (W + 2)) :
    ∃ c' bs' am', cNext N W AccW ck (knownBit true) st a b dn c s bs lk am =
      MS ck (knownBit true) st a b (knownBit false) c' (.ofBitVec (sV N (2 * N - 1))) bs' (.ofBitVec (lkZ N W)) am' := by
  have hN := h.hN
  have hN30 : N < 2 ^ 30 := by have := N_small h hNW; omega
  rw [cNext, commit_SS _ _ _ _ _ _ _ (Q_names _ _ _ _ _ _ _ _ _ _ _ _ _), fold_done, fold_s, fold_lnk,
    lnk_reset hN st b s bs lk hlk]
  have hd : nbaFold "done" (doneQ N W (knownBit true) st dn lk) dn = knownBit false := by
    unfold doneQ
    rw [condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, wr, hdn, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by rw [hdn]; rfl)
  have hs' : nbaFold "s" (ctrlQ N W (knownBit true) st b s bs) s = .ofBitVec (sV N (2 * N - 1)) := by
    unfold ctrlQ
    rw [condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, wr, hs, sMax_eq hN30 hN,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [LVec.insertAt_zero_of_width_eq (by simp [hs])]
    unfold sV; congr 2; omega
  rw [hd, hs']
  exact ⟨_, _, _, rfl⟩

theorem l0_eq : (⟨#[.l0]⟩ : LVec) = LVec.ofBitVec (BitVec.ofBool false) := by
  rw [show (⟨#[.l0]⟩ : LVec) = LVec.ofLogic .l0 from rfl, LVec.ofLogic_l0]

/-- The edge buffer's load, evaluated. -/
theorem bsLoad_eq {N W : Nat} (hNW : N * N * W < 2 ^ 31) (hN1 : 1 ≤ N) (hW1 : 1 ≤ W) (B : BitVec (N * N * W)) :
    bsLoadV N W (.ofBitVec B) = .ofBitVec (bs0 N W B) := by
  have hNW' : N * W < 2 ^ 31 := by
    have : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hW : W < 2 ^ 32 := by have := Nat.le_mul_of_pos_left W (show 0 < N by omega); omega
  have hN : N < 2 ^ 32 := by have := Nat.le_mul_of_pos_right N hW1; omega
  have hm : nwV N W = LVec.ofBitVec (BitVec.ofNat 32 (N * W)) := by
    rw [nwV, ofInt_nat32 hN, ofInt_nat32 hW, LVec.mul_ofBitVec]
    congr 1
    rw [← BitVec.toNat_inj, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hW]
  have ht : (BitVec.ofNat 32 (N * W) + BitVec.ofNat 32 (N * W)).toNat = N * W + N * W := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    simp only [Nat.reducePow] at hNW' ⊢
    omega
  unfold bsLoadV
  rw [hm, LVec.add_ofBitVec, LVec.concatMany_singleton, l0_eq, LVec.replVec_ofBitVec, LVec.concatMany_cons_cons,
    LVec.concatMany_singleton, LVec.concat_ofBitVec, LVec.shr_ofBitVec, ht, LVec.resizeU_ofBitVec, bs0]

/-- **A start cycle** from a state with no wavelet: the state `1` (snapshot `0`) after the start. -/
theorem next_start {N W AccW : Nat} (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    (ck dn c bs am : LVec) (hdn : dn.width = 1) (hc : c.width = N * N * AccW) (hbs : bs.width = (2 * N - 1) * N * W)
    (ham : am.width = N * N * N * W) :
    cNext N W AccW ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c (.ofBitVec (sV N (2 * N - 1)))
        bs (.ofBitVec (lkZ N W)) am =
      MS ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) (knownBit false)
        (.ofBitVec (accV N W AccW A B 1)) (.ofBitVec (sV N 1)) (.ofBitVec (bsV N W B 1)) (.ofBitVec (lkV N W B 1))
        (.ofBitVec (amV N W A 1)) := by
  have hN := h.hN; have hW := h.hW
  have hN30 : N < 2 ^ 30 := by have := N_small h hNW; omega
  rw [cNext, commit_SS _ _ _ _ _ _ _ (Q_names _ _ _ _ _ _ _ _ _ _ _ _ _), fold_done, fold_C, fold_s, fold_bs,
    fold_lnk, fold_amem, cores_start_C hN _ _ _ _ c hc, cores_start_M hN A _ _ am ham]
  have hd : nbaFold "done" (doneQ N W (knownBit false) (knownBit true) dn (.ofBitVec (lkZ N W))) dn = knownBit false := by
    unfold doneQ
    rw [condTrue_knownBit, if_neg Bool.false_ne_true, condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, wr, hdn, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by rw [hdn]; rfl)
  have hs : nbaFold "s" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec B) (.ofBitVec (sV N (2 * N - 1))) bs)
      (.ofBitVec (sV N (2 * N - 1))) = .ofBitVec (sV N 1) := by
    unfold ctrlQ
    rw [condTrue_knownBit, if_neg Bool.false_ne_true, condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, wr, width_ofBitVec', zv_resize,
      if_neg (show ("bs" : String) ≠ "s" by decide)]
    rw [LVec.insertAt_zero_of_width_eq (by simp)]
    simp [sV]
  have hb : nbaFold "bs" (ctrlQ N W (knownBit false) (knownBit true) (.ofBitVec B) (.ofBitVec (sV N (2 * N - 1))) bs)
      bs = .ofBitVec (bsV N W B 1) := by
    unfold ctrlQ
    rw [condTrue_knownBit, if_neg Bool.false_ne_true, condTrue_knownBit, if_pos rfl]
    simp only [nbaFold, List.foldl_cons, List.foldl_nil, ite_true, ↓reduceIte, wr, hbs,
      if_neg (show ("s" : String) ≠ "bs" by decide)]
    rw [bsLoad_eq hNW hN hW B, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
      LVec.insertAt_zero_of_width_eq (by simp [hbs]), bsV, Nat.sub_self, Nat.zero_mul, BitVec.ushiftRight_zero]
  have hl : nbaFold "lnk" ((List.range (N - 1)).flatMap fun i => (List.range N).flatMap
        (rtQ N W (knownBit false) (.ofBitVec (lkZ N W)) i))
      (nbaFold "lnk" ((List.range (N - 1)).flatMap (edgeQ N W (knownBit false) (.ofBitVec (sV N (2 * N - 1))) bs))
        (nbaFold "lnk" (edge0Q N W (knownBit false) (knownBit true) (.ofBitVec B) (.ofBitVec (sV N (2 * N - 1))) bs)
          (.ofBitVec (lkZ N W)))) = .ofBitVec (lkV N W B 1) := by
    unfold lkZ
    rw [lnk_fold hN _ _ _ _ (fun k => lw N W B 1 0 k) _ (edge0_start hN30 hN hW B _ bs) (fun x hx => by
      rw [sV, edge_idle hN30 hx (by omega) bs]; congr 3; all_goals (unfold lw; rw [if_neg (by omega)])), lkV]
    refine congrArg _ (packBV_congr fun k hk => ?_)
    by_cases h1 : k < N
    · rw [if_pos h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1]
    · rw [if_neg h1]
      have : 1 ≤ k / N := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      unfold lw; rw [if_neg (by omega)]
  have e1 : accV N W AccW A B 1 = packBV AccW (N * N) (fun _ => 0) := by
    unfold accV; exact packBV_congr fun k _ => by simp [psum, fc]
  have e3 : amV N W A 1 = packBV (N * W) (N * N) (fun k => rowA N W A (k / N)) := by
    unfold amV; exact packBV_congr fun k _ => by simp [fc]
  rw [hd, hs, hb, hl, e1, e3]

/-! ## 6. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c s bs lk am : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ s.width = 32 ∧ bs.width = (2 * N - 1) * N * W ∧
    lk.width = N * N * (W + 2) ∧ am.width = N * N * N * W

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s0 a b dn c s bs lk am, st = MS ck r s0 a b dn c s bs lk am ∧ Wd N W AccW dn c s bs lk am

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem cNext_I (N W AccW : Nat) (ck r s0 a b dn c s bs lk am : LVec) (hw : Wd N W AccW dn c s bs lk am) :
    I N W AccW (cNext N W AccW ck r s0 a b dn c s bs lk am) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  rw [cNext, commit_SS _ _ _ _ _ _ _ (Q_names _ _ _ _ _ _ _ _ _ _ _ _ _)]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, *]⟩

theorem c_noq (N W AccW : Nat) : (cD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [cD, genPs, edgePs, rtPs, corePs, ctrlP, edge0P, doneP, edgeP, rtP, coreP, sext, nb, Process2.hasQualifiedCase,
    Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase, List.any_flatMap, List.any_map, List.any_append]

theorem c_init (N W AccW : Nat) (h : Rng N W AccW) : I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [c_sem_eq N W AccW h]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec ((2 * N - 1) * N * W), .xVec (N * N * (W + 2)), .xVec (N * N * N * W), ?_, by simp [Wd]⟩
  simp [initState2, cD, cDecls, MS]

/-! ## 7. The protocol: the phases -/

theorem MS_inj {ck r s0 a b dn c s bs lk am ck' r' s0' a' b' dn' c' s' bs' lk' am' : LVec}
    (h : MS ck r s0 a b dn c s bs lk am = MS ck' r' s0' a' b' dn' c' s' bs' lk' am') :
    dn = dn' ∧ c = c' ∧ s = s' ∧ bs = bs' ∧ lk = lk' ∧ am = am' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- The state `t` busy cycles after a start with operands `A`, `B`. -/
def AtT (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s0 a b, st = MS ck r s0 a b (knownBit false) (.ofBitVec (accV N W AccW A B t)) (.ofBitVec (sV N t))
    (.ofBitVec (bsV N W B t)) (.ofBitVec (lkV N W B t)) (.ofBitVec (amV N W A t))

/-- Finished with `A`, `B`: `done` = 1, `C` the product, the counter idle, no wavelet. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s0 a b bs am, st = MS ck r s0 a b (knownBit true) (.ofBitVec (Tasks.Matmul.product N W AccW A B))
    (.ofBitVec (sV N (2 * N - 1))) bs (.ofBitVec (lkZ N W)) am

/-- One cycle from a state of the shape, evaluated (`c_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s0 a b dn c s bs lk am, prev = MS ck r s0 a b dn c s bs lk am ∧ Wd N W AccW dn c s bs lk am ∧
    st = cNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s0) (appIn e "A" a)
      (appIn e "B" b) dn c s bs lk am

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- After `3N - 1` busy cycles the accumulators hold the product. -/
theorem accV_fin (N W AccW : Nat) (A B : BitVec (N * N * W)) :
    accV N W AccW A B (3 * N - 1) = Tasks.Matmul.product N W AccW A B := by
  rw [Tasks.Matmul.product, ← packBV_eq_ofNat, accV]
  refine packBV_congr fun k hk => ?_
  have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h => by simp [h] at hk)
  have hi : k / N < N := Nat.div_lt_of_lt_mul hk
  have hj : k % N < N := Nat.mod_lt _ hN0
  have : fc N (3 * N - 1) (k / N) (k % N) = N := by unfold fc; omega
  rw [this]; rfl

theorem lkV_fin (N W : Nat) (B : BitVec (N * N * W)) : lkV N W B (3 * N - 1) = lkZ N W := by
  unfold lkV lkZ
  refine packBV_congr fun k hk => ?_
  have hN0 : 0 < N := Nat.pos_of_ne_zero (fun h => by simp [h] at hk)
  have hi : k / N < N := Nat.div_lt_of_lt_mul hk
  have hj : k % N < N := Nat.mod_lt _ hN0
  unfold lw; rw [if_neg (by omega)]

theorem sV_fin (N : Nat) : sV N (3 * N - 1) = sV N (2 * N - 1) := by unfold sV; congr 1; omega

/-- **The phase model** at `(N, W, AccW)`, latency `3N - 2`. -/
def model (N W AccW : Nat) (h : Rng N W AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (3 * N - 2) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := c_init N W AccW h
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, hw⟩ hc
    exact ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (c_cycle N W AccW h σ e ck r s0 a b dn c s bs lk am k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, -, hw, rfl⟩
    exact cNext_I N W AccW _ _ _ _ _ dn c s bs lk am hw
  Ready st := ∃ ck r s0 a b c bs am, st = MS ck r s0 a b (knownBit false) c (.ofBitVec (sV N (2 * N - 1))) bs
    (.ofBitVec (lkZ N W)) am
  Busy x m st := ∃ t, t + m + 2 = 3 * N - 1 ∧ AtT N W AccW x.1 x.2.1 (t + 1) st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s0, a, b, c, bs, am, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s0, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s0, a, b, bs, am, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, -, hw, rfl⟩ hr
    obtain ⟨h1, -, h3, -, h5, -⟩ := hw
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', bs', am', hn⟩ := next_reset h hNW (appIn e "clk" ck) (appIn e "start" s0) (appIn e "A" a)
      (appIn e "B" b) dn c s bs lk am h1 h3 h5
    rw [hn]; exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, hw, rfl⟩ hidle hr hs hx
    obtain ⟨h1, h2, -, h4, -, h6⟩ := hw
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    have hid : s = .ofBitVec (sV N (2 * N - 1)) ∧ lk = .ofBitVec (lkZ N W) := by
      rcases hidle with ⟨ck', r', s0', a', b', c', bs', am', he⟩ | ⟨y, ck', r', s0', a', b', bs', am', he⟩
      · obtain ⟨-, -, h3, -, h5, -⟩ := MS_inj he; exact ⟨h3, h5⟩
      · obtain ⟨-, -, h3, -, h5, -⟩ := MS_inj he; exact ⟨h3, h5⟩
    obtain ⟨rfl, rfl⟩ := hid
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s0 = knownBit true from BitIs.appIn_eq hs s0, ha, hb,
      next_start h hNW _ _ _ dn c bs am h1 h2 h4 h6]
    exact .inr ⟨3 * N - 3, by have := h.hN; omega, 0, by have := h.hN; omega, _, _, _, _, _, rfl⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, -, rfl⟩ ⟨t, ht, ck', r', s0', a', b', hb⟩
      hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s0 = knownBit false from BitIs.appIn_eq hs s0, next_step h hNW _ _ (by omega)]
    by_cases hf : t + 2 = 3 * N - 1
    · left
      rw [decide_eq_true hf, hf, accV_fin, sV_fin, lkV_fin]
      exact ⟨_, _, _, _, _, _, _, rfl⟩
    · right
      rw [decide_eq_false hf]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, -, rfl⟩ ⟨ck', r', s0', a', b', c', bs', am', hb⟩
      hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s0 = knownBit false from BitIs.appIn_eq hs s0]
    obtain ⟨bs'', hn⟩ := next_idle h hNW (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) (knownBit false) c bs am
    rw [hn]; exact ⟨_, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, -, rfl⟩ ⟨ck', r', s0', a', b', bs', am', hb⟩
      hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s0 = knownBit false from BitIs.appIn_eq hs s0]
    obtain ⟨bs'', hn⟩ := next_idle h hNW (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) (knownBit true)
      (.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) bs am
    rw [hn]; exact ⟨_, _, _, _, _, _, _, rfl⟩

theorem c_interface (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [c_sem_eq N W AccW h]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "s", "bs", "lnk", "amem"] : List String).Nodup
    decide⟩

theorem c_disciplined (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [c_sem_eq N W AccW h]
  refine ⟨by simp [Tasks.Matmul.task, cD, cDecls, Design2.inputNames], fun p hp => ?_⟩
  rcases c_mem hp with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
  · simp [Tasks.Matmul.task, ctrlP, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, edge0P, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, doneP, nb, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, edgeP, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, rtP, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, coreP, sext, c32, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]

/-! ## 8. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3) -/

/-- **Rule 1.** -/
theorem c_moore (N W AccW : Nat) (h : Rng N W AccW) : MooreOutDep (design.sem N W AccW) [] := by
  rw [c_sem_eq N W AccW h]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (c_profile N W AccW)))
    (by simp [cD, cDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem c_powerUp (N W AccW : Nat) (h : Rng N W AccW) (st : SvState) (hp : PowerUp (design.sem N W AccW) st) :
    I N W AccW st := by
  rw [c_sem_eq N W AccW h] at hp
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp hp
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s0, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨s, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bs, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨lk, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨am, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain rfl := powerUp_nil.mp h11
  exact ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, w6, w7, w8, w9, w10, w11⟩

/-- **Termination from every power-up.** -/
theorem c_terminatesPU (N W AccW : Nat) (h : Rng N W AccW) : TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (c_powerUp N W AccW h) (fun σ => ⟨30, ?_⟩)
    (by rw [c_sem_eq N W AccW h]; exact c_noq N W AccW)
  rintro e _ kk ⟨ck, r, s0, a, b, dn, c, s, bs, lk, am, rfl, hw⟩
  exact ⟨_, _, c_cycle N W AccW h σ e ck r s0 a b dn c s bs lk am kk 30 (Nat.le_refl _),
    cNext_I N W AccW _ _ _ _ _ dn c s bs lk am hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem ctrl_xsafe (N W AccW : Nat) (hN : 1 ≤ N) : xsProc (cD N W AccW) (ctrlP N W) = true := by
  have hl0 : (⟨#[.l0]⟩ : LVec).width = 1 := rfl
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, ctrlP, nb, c32, cD, cDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt, hl0]

theorem edge0_xsafe (N W AccW : Nat) (hN : 1 ≤ N) : xsProc (cD N W AccW) (edge0P N W) = true := by
  have hA : W ≤ N * N * W := Nat.le_mul_of_pos_left W (Nat.mul_pos (by omega) (by omega))
  have hb : (N - 1) * N * W + W ≤ (2 * N - 1) * N * W := by
    have : (N - 1) * N + 1 ≤ (2 * N - 1) * N := by
      have : (N - 1) * N + N ≤ (2 * N - 1) * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.mul_le_mul_right W this; rw [Nat.add_mul, Nat.one_mul] at this; exact this
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, edge0P, c32, cD, cDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt, hA, hb]

theorem done_xsafe (N W AccW : Nat) (hN : 1 ≤ N) : xsProc (cD N W AccW) (doneP N W) = true := by
  have hNN : 1 ≤ N * N := Nat.mul_pos hN hN
  have hb : (N * N - 1) * (W + 2) + W + 1 + 1 ≤ N * N * (W + 2) := by
    have := Nat.mul_le_mul_right (W + 2) (show N * N - 1 + 1 ≤ N * N by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have hb' : (N * N - 1) * (W + 2) + W + 1 ≤ N * N * (W + 2) := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, doneP, nb, cD, cDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, hb, hb']

theorem edge_xsafe (N W AccW : Nat) {x : Nat} (hx : x + 1 < N) : xsProc (cD N W AccW) (edgeP N W x) = true := by
  have hb : ((N - 2 - x) * N + x + 1) * W + W ≤ (2 * N - 1) * N * W := by
    have e : (N - 2 - x) * N + x + 1 + 1 ≤ (2 * N - 1) * N := by
      have : (N - 2 - x) * N ≤ (N - 1) * N := Nat.mul_le_mul_right _ (by omega)
      have : (N - 1) * N + N ≤ (2 * N - 1) * N := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      omega
    have := Nat.mul_le_mul_right W e; rw [Nat.add_mul _ 1, Nat.one_mul] at this; exact this
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, edgeP, c32, cD, cDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt, hb]

theorem rt_xsafe (N W AccW : Nat) {i j : Nat} (hi : i + 1 < N) (hj : j < N) : xsProc (cD N W AccW) (rtP N W i j) = true := by
  have h1 := Lib.rowMajor_window_le (w := W + 2) hi hj
  have h2 := Lib.rowMajor_window_le (w := W + 2) (show i < N by omega) hj
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, rtP, cD, cDecls,
    LVec.replicate_l0, h1, h2]

theorem core_xsafe (N W AccW : Nat) (hW : 1 ≤ W) {i j : Nat} (hi : i < N) (hj : j < N) :
    xsProc (cD N W AccW) (coreP N W AccW i j) = true := by
  have hN : 0 < N := by omega
  have hC := Lib.rowMajor_window_le (w := AccW) hi hj
  have hM : (i * N + j) * N * W + N * W ≤ N * N * N * W := by
    have := Lib.rowMajor_window_le (w := N * W) hi hj
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have hM1 : (i * N + j) * N * W + W ≤ N * N * N * W := by
    have : W ≤ N * W := Nat.le_mul_of_pos_left W hN; omega
  have hM2 : (i * N + j) * N * W + W - 1 + 1 ≤ N * N * N * W := by omega
  have hA : i * N * W + N * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (show i + 1 ≤ N by omega)
    rw [Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc, ← Nat.mul_assoc] at this; exact this
  have hL := Lib.rowMajor_window_le (w := W + 2) hi hj
  have hL1 : (i * N + j) * (W + 2) + W ≤ N * N * (W + 2) := by omega
  have hL2 : (i * N + j) * (W + 2) + W - 1 + 1 ≤ N * N * (W + 2) := by omega
  have hL3 : (i * N + j) * (W + 2) + W + 1 + 1 ≤ N * N * (W + 2) := by omega
  have hL4 : (i * N + j) * (W + 2) + W + 1 ≤ N * N * (W + 2) := by omega
  have hl0 : (⟨#[.l0]⟩ : LVec).width = 1 := rfl
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, coreP, sext, c32, cD, cDecls,
    lvec_l0_known, LVec.replicate_l0, LVec.ofInt, hC, hM, hM1, hM2, hA, hL, hL1, hL2, hL3, hL4, hl0]

/-- **Rule 3.** -/
theorem c_xsafe (N W AccW : Nat) (h : Rng N W AccW) : XSafe (design.sem N W AccW) := by
  rw [c_sem_eq N W AccW h]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ ctrlP N W :: edge0P N W :: doneP N W :: genPs N W AccW := by simpa [cD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ctrl_xsafe N W AccW h.hN
  rcases List.mem_cons.mp hm with rfl | hm
  · exact edge0_xsafe N W AccW h.hN
  rcases List.mem_cons.mp hm with rfl | hm
  · exact done_xsafe N W AccW h.hN
  simp only [genPs, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · obtain ⟨j, hj, rfl⟩ := edge_mem hm; exact edge_xsafe N W AccW hj
  · obtain ⟨i, j, hi, hj, rfl⟩ := rt_mem hm; exact rt_xsafe N W AccW hi hj
  · obtain ⟨i, j, hi, hj, rfl⟩ := core_mem hm; exact core_xsafe N W AccW h.hW hi hj

/-- **The mesh of cores satisfies the matmul statement (txtask-v2) at latency `3N - 2`** (`10` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  have h : Rng N W AccW := ⟨hN, hW, hA⟩
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (c_interface N W AccW h)
    (c_disciplined N W AccW h) (c_terminatesPU N W AccW h) (show 1 ≤ 3 * N - 2 by omega)
    (model N W AccW h hNW) (c_powerUp N W AccW h) (c_moore N W AccW h) (c_xsafe N W AccW h)

end Submission
