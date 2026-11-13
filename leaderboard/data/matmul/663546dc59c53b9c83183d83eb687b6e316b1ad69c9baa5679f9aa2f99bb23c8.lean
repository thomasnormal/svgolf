-- svgolf-latency: 20
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
# A spatial dataflow pipeline for `matmul`: counter chain, two memory units, one compute unit

`solution.sv`: the counter chain `(cc_i, cc_j)` issues the item `(i, j)` of the Map domain in every cycle
(row-major); PMU_A's read port (row 0 of `pa_mem`, rotated to row `cc_i`) and PMU_B's (entry 0 of every row of
`pb_mem`, rotated to column `cc_j`) feed the PCU's vector inputs `pcu_va`, `pcu_vb` (one sign-extended `AccW`-bit
word per lane); the map stage multiplies lane by lane into the leaves of the reduction tree `pcu_tr` (a heap of
`2P - 1` nodes, `P = 2^clog2 N`, root at node 0, leaves at `P - 1 + k`); one tree level per pipeline stage; the
output unit shifts the root into `C` whenever the root stage is valid; the last item raises `done`.
`lat = N² + clog2 N + 2` (`20` at the scoring point).

Proved at every in-range `(N, W, AccW)`:
1. **Agreement** (`mm_sem_eq`): the loaded family is the hand-built `mmD`.
2. **The clock step** (`mm_profile`, `mm_cycle`): one cycle is the evaluated commit `mmNext`.
3. **The pipeline invariant** (`BusyR`): `t` cycles after a start, stage `s` holds item `t - 1 - s`, valid iff
   `s < t` and `t - 1 - s < N²`; tree node `(d, x)` holds the sum of its leaves' products; `C`'s top entries
   hold the finished items in order.
4. **The phases** (`model`) and txtask-v2's rules, then `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- `clog2 N`, the tree's depth. -/
abbrev Lg (N : Nat) : Nat := clog2 N

/-- `P = 2^clog2 N`, the tree's leaves. -/
abbrev Pw (N : Nat) : Nat := 2 ^ clog2 N

/-- The latency: the last of the `N²` items leaves the root `clog2 N + 2` cycles after it was issued. -/
def lat (N _W _AccW : Nat) : Nat := N * N + clog2 N + 2

/-! ## 0. Facts about `clog2` -/

theorem le_pw (N : Nat) : N ≤ Pw N := by
  unfold Pw clog2
  split
  · simp; omega
  · rename_i h
    have := Nat.lt_log2_self (n := N - 1)
    rw [Nat.pow_succ] at this ⊢
    omega

theorem pw_pos (N : Nat) : 0 < Pw N := Nat.two_pow_pos _

theorem pw_lt (N : Nat) (hN : 1 ≤ N) : Pw N < 2 * N := by
  unfold Pw clog2
  split
  · simp; omega
  · rename_i h
    have := Nat.log2_self_le (n := N - 1) (by omega)
    rw [Nat.pow_succ]
    omega

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `w` zero bits. -/
abbrev zv (w : Nat) : LVec := LVec.replicate w .l0

/-- One known bit. -/
abbrev b1 (b : Bool) : LVec := ⟨#[if b then .l1 else .l0]⟩

/-- A nonblocking write of a constant to a whole signal. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `N - 1` at 32 bits. -/
abbrev nm1 (N : Nat) : Expr2 := .binary .sub (c32 N) (c32 1)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The counter chain. -/
def ccP (N : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst") (nb "cc_run" (b1 false))
    (some (.ifStmt (.ident "start")
      (.block #[nb "cc_run" (b1 true), nb "cc_i" (zv 32), nb "cc_j" (zv 32)])
      (some (.ifStmt (.ident "cc_run")
        (.block #[.ifStmt (.binary .eq (.ident "cc_j") (nm1 N))
          (.block #[nb "cc_j" (zv 32), .nbaAssign (.ident "cc_i") (.binary .add (.ident "cc_i") (c32 1)),
            .ifStmt (.binary .eq (.ident "cc_i") (nm1 N)) (nb "cc_run" (b1 false)) none])
          (some (.nbaAssign (.ident "cc_j") (.binary .add (.ident "cc_j") (c32 1))))])
        none)))))

/-- PMU_A. -/
def paP (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start") (.nbaAssign (.ident "pa_mem") (.ident "A"))
    (some (.ifStmt (.ident "cc_run")
      (.block #[.ifStmt (.binary .eq (.ident "cc_j") (nm1 N))
        (.nbaAssign (.ident "pa_mem") (.binary .or
          (.binary (.shr false) (.ident "pa_mem") (.binary .mul (c32 N) (c32 W)))
          (.binary (.shl false) (.ident "pa_mem") (.binary .mul (.binary .mul (nm1 N) (c32 N)) (c32 W)))))
        none])
      none)))

/-- The PCU's control: the zero leaves, the valid and last bits. -/
def ctlP (N AccW : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .nbaAssign (.slice "pcu_tr" ((Pw N - 1 + N) * AccW) ((Pw N + 1 - N) * AccW)) (.lit (zv ((Pw N + 1 - N) * AccW))),
    .ifStmt (.ident "rst") (.block #[nb "pcu_vld" (zv (Lg N + 2)), nb "pcu_lst" (zv (Lg N + 2))])
      (some (.ifStmt (.ident "start") (.block #[nb "pcu_vld" (zv (Lg N + 2)), nb "pcu_lst" (zv (Lg N + 2))])
        (some (.block #[
          .nbaAssign (.ident "pcu_vld") (.concat #[.slice (.ident "pcu_vld") 0 (Lg N + 1), .ident "cc_run"]),
          .nbaAssign (.ident "pcu_lst") (.concat #[.slice (.ident "pcu_lst") 0 (Lg N + 1),
            .binary .and (.binary .eq (.ident "cc_i") (nm1 N)) (.binary .eq (.ident "cc_j") (nm1 N))])]))))])

/-- The output unit. -/
def outP (N AccW : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst") (nb "done" (b1 false))
    (some (.ifStmt (.ident "start") (nb "done" (b1 false))
      (some (.ifStmt (.slice (.ident "pcu_vld") (Lg N + 1) 1)
        (.block #[.nbaAssign (.ident "C") (.binary (.shr false) (.ident "C") (c32 AccW)),
          .nbaAssign (.slice "C" ((N * N - 1) * AccW) AccW) (.slice (.ident "pcu_tr") 0 AccW),
          .ifStmt (.slice (.ident "pcu_lst") (Lg N + 1) 1) (nb "done" (b1 true)) none])
        none)))))

/-- PMU_B, row `k`. -/
def pbP (N W k : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "pb_mem" (k * N * W) (N * W)) (.slice (.ident "B") (k * N * W) (N * W)))
    (some (.ifStmt (.ident "cc_run")
      (.nbaAssign (.slice "pb_mem" (k * N * W) (N * W)) (.binary .or
        (.binary (.shr false) (.slice (.ident "pb_mem") (k * N * W) (N * W)) (c32 W))
        (.binary (.shl false) (.slice (.ident "pb_mem") (k * N * W) (N * W)) (.binary .mul (nm1 N) (c32 W)))))
      none)))

/-- Tree node `h`: the sum of its children. -/
def redP (AccW h : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "pcu_tr" (h * AccW) AccW)
    (.binary .add (.slice (.ident "pcu_tr") ((2 * h + 1) * AccW) AccW)
      (.slice (.ident "pcu_tr") ((2 * h + 2) * AccW) AccW)))

/-- Lane `k`'s vector inputs. -/
def laneP (N W AccW k : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[
    .nbaAssign (.slice "pcu_va" (k * AccW) AccW) (.resize AccW (sext "pa_mem" AccW (k * W) W)),
    .nbaAssign (.slice "pcu_vb" (k * AccW) AccW) (.resize AccW (sext "pb_mem" AccW (k * N * W) W))])

/-- Lane `k`'s multiplier: leaf `P - 1 + k`. -/
def leafP (N AccW k : Nat) : Process2 :=
  .alwaysFF "clk" (.nbaAssign (.slice "pcu_tr" ((Pw N - 1 + k) * AccW) AccW)
    (.binary .mul (.slice (.ident "pcu_va") (k * AccW) AccW) (.slice (.ident "pcu_vb") (k * AccW) AccW)))

/-- The declarations. -/
def mmDecls (N W AccW : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true }, { name := "cc_i", width := 32 },
   { name := "cc_j", width := 32 }, { name := "cc_run", width := 1 }, { name := "pa_mem", width := N * N * W },
   { name := "pb_mem", width := N * N * W }, { name := "pcu_va", width := N * AccW },
   { name := "pcu_vb", width := N * AccW }, { name := "pcu_vld", width := Lg N + 2 },
   { name := "pcu_lst", width := Lg N + 2 }, { name := "pcu_tr", width := 2 * Pw N * AccW }]

/-- PMU_B's rows. -/
def pbPs (N W : Nat) : List Process2 := (List.range N).map (pbP N W)

/-- The tree's inner nodes. -/
def redPs (N AccW : Nat) : List Process2 := (List.range (Pw N - 1)).map (redP AccW)

/-- The lanes: vector inputs, then the multiplier. -/
def lanePs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun k => [laneP N W AccW k, leafP N AccW k]

/-- The generated processes, in source order. -/
def genPs (N W AccW : Nat) : List Process2 := pbPs N W ++ redPs N AccW ++ lanePs N W AccW

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls N W AccW).toArray
  processes := (ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

def mmScope (N W AccW : Nat) : IEnv :=
  { vals := [("P", (Pw N : Int)), ("L", (Lg N : Int)), ("N", N), ("W", W), ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("L", 32), ("P", 32)] }

def mmEnv (N W AccW : Nat) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) design.pdesign.decls }

theorem canonInt_small {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) : canonInt 32 true v = v := by
  have e : Int.emod v (2 ^ 32) = v := Int.emod_eq_of_lt h0 (by omega)
  unfold canonInt
  simp only [e]
  split
  · rename_i hc
    simp at hc
    omega
  · rfl

theorem declTy (env : IEnv) :
    declConstType env (some (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32))) none = .ok none :=
  rfl

theorem tyW (env : IEnv) : (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32)).width env = .ok 32 :=
  rfl

theorem mm_paramEnv (N W AccW : Nat) (hN : 1 ≤ N) (hr : N * N * W < 2 ^ 31) (hW : 1 ≤ W) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (mmEnv N W AccW) := by
  have hN2 : N < 2 ^ 16 := by
    have : N * N < 2 ^ 31 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hW) hr
    rcases Nat.lt_or_ge N (2 ^ 16) with h | h
    · exact h
    · have : 2 ^ 16 * 2 ^ 16 ≤ N * N := Nat.mul_le_mul h h
      omega
  have hP := pw_lt N hN
  have hL : clog2 N < 2 ^ clog2 N := Nat.lt_two_pow_self
  have e1 : canonInt 32 true ((clog2 N : Nat) : Int) = ((clog2 N : Nat) : Int) :=
    canonInt_small (by omega) (by unfold Pw at hP; omega)
  have e2 : canonInt 32 true ((2 : Int) ^ ((clog2 N : Nat) : Int).toNat) = ((2 ^ clog2 N : Nat) : Int) := by
    rw [Int.toNat_natCast, show ((2 : Int) ^ clog2 N) = ((2 ^ clog2 N : Nat) : Int) by push_cast; rfl]
    exact canonInt_small (by omega) (by unfold Pw at hP; omega)
  have h0 : ¬ ((N : Int) < 0) := by omega
  have h1 : ¬ (((clog2 N : Nat) : Int) < 0) := by omega
  simp [PDesign.paramEnv2, design.pdesign, bindPackageParams, bindPackageEnums, bindParamsRes, bindParams,
    bindLocals, bindLocal, evalIntTarget, evalInt, bindEnums, IEnv.bindVal, declTy, tyW, mmEnv, mmScope,
    Gen2.except_ok_bind, Except.mapError, List.lookup, List.filterMapM, List.filterMapM.loop, e1, e2, h0, h1]

theorem natAbs_cast {x : Nat} {X : Int} (h : (x : Int) = X) (hx : 0 < x) : (X - 1).natAbs + 1 = x := by
  subst h; omega

theorem mm_decls (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    buildDecls (mmEnv N W AccW) design.pdesign.decls = .ok (mmDecls N W AccW) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have hP := pw_pos N
  have h1 : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hW)
  have h2 : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW := natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN hA)
  have h3 : ((N : Int) * AccW - 1).natAbs + 1 = N * AccW := natAbs_cast (by push_cast; rfl) (Nat.mul_pos hN hA)
  have h4 : (2 * (2 : Int) ^ clog2 N * AccW - 1).natAbs + 1 = 2 * Pw N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (Nat.mul_pos (by decide) hP) hA)
  have h5 : (((Lg N : Nat) : Int) + 1).natAbs + 1 = Lg N + 2 := by omega
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, Gen2.except_ok_bind, mmDecls, h1, h2, h3, h4, h5]

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "cc_i", "cc_j", "cc_run", "pa_mem", "pb_mem", "pcu_va",
    "pcu_vb", "pcu_vld", "pcu_lst", "pcu_tr"].map (·, 1)

theorem mm_elems (N W AccW : Nat) : buildElems (mmEnv N W AccW) design.pdesign.decls = .ok mmElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, Gen2.except_ok_bind, mmElems]

/-- The instantiation environment. -/
abbrev mmE (N W AccW : Nat) : IEnv := (mmEnv N W AccW).withDecls (mmDecls N W AccW)

/-- The static processes' templates. -/
def ccT : PProcess := match design.pdesign.processes with
  | [p, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def paT : PProcess := match design.pdesign.processes with
  | [_, p, _, _] => p
  | _ => .alwaysFF "" (.block [])
def ctlT : PProcess := match design.pdesign.processes with
  | [_, _, p, _] => p
  | _ => .alwaysFF "" (.block [])
def outT : PProcess := match design.pdesign.processes with
  | [_, _, _, p] => p
  | _ => .alwaysFF "" (.block [])

/-- The generate templates. -/
def pbT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _] => p
  | _ => .alwaysFF "" (.block [])
def redT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.process p], _] => p
  | _ => .alwaysFF "" (.block [])
def laneT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.process p, _]] => p
  | _ => .alwaysFF "" (.block [])
def leafT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [_, .process p]] => p
  | _ => .alwaysFF "" (.block [])

macro "mm_simp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, mmEnv, mmScope, mmDecls, mmElems, ccT, paT, ctlT, outT, pbT, redT, laneT, leafT,
  ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, sext,
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

theorem cc_inst (N W AccW : Nat) : instProcess2 (mmE N W AccW) mmElems ccT = ccP N := by
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem pa_inst (N W AccW : Nat) : instProcess2 (mmE N W AccW) mmElems paT = paP N W := by
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem ctl_inst (N W AccW : Nat) (hN : 1 ≤ N) (hA : 1 ≤ AccW) :
    instProcess2 (mmE N W AccW) mmElems ctlT = ctlP N AccW := by
  have hP := le_pw N
  have hP0 := pw_pos N
  have w1 := winF (((2 : Int) ^ clog2 N - 1 + N) * AccW) (((2 : Int) ^ clog2 N + 1 - N) * AccW)
    (2 * (2 : Int) ^ clog2 N * AccW) (lo := (Pw N - 1 + N) * AccW) (w := (Pw N + 1 - N) * AccW)
    (c := 2 * Pw N * AccW) (by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega))
    (Nat.mul_pos (by omega) hA) (by push_cast [Int.ofNat_sub (show 1 ≤ Pw N by omega)]; rfl)
    (by push_cast [Int.ofNat_sub (show N ≤ Pw N + 1 by omega)]; rfl) (by push_cast; rfl)
  have hl1 : (((Lg N : Nat) : Int) + 1).toNat = Lg N + 1 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hc1 : (1 : Int) ≤ 2 * (2 : Int) ^ clog2 N * AccW := by
    have : ((2 * Pw N * AccW : Nat) : Int) = 2 * (2 : Int) ^ clog2 N * AccW := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos (show 0 < 2 by decide) hP0) hA
    omega
  have hL0 : ¬ (((Lg N : Nat) : Int) < 0) := by omega
  have hmin : min (((Lg N : Nat) : Int)) 0 = 0 := by omega
  have hab : (((Lg N : Nat) : Int) + 1).natAbs + 1 = Lg N + 2 := by omega
  have hcw : (((2 * (2 : Int) ^ clog2 N * AccW - 1).natAbs : Nat) : Int) + 1 = 2 * (2 : Int) ^ clog2 N * AccW := by
    omega
  have hLL : ¬ (((Lg N : Nat) : Int) + 2 ≤ ((Lg N : Nat) : Int)) := by omega
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem out_inst (N W AccW : Nat) (hN : 1 ≤ N) (hA : 1 ≤ AccW) :
    instProcess2 (mmE N W AccW) mmElems outT = outP N AccW := by
  have hP := le_pw N
  have hP0 := pw_pos N
  have hNN : 1 ≤ N * N := Nat.mul_pos hN hN
  have w1 := winF ((((N : Int) * N) - 1) * AccW) AccW ((N : Int) * N * AccW)
    (lo := (N * N - 1) * AccW) (w := AccW) (c := N * N * AccW)
    (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)) hA
    (by push_cast [Int.ofNat_sub hNN]; rfl) rfl (by push_cast; rfl)
  have w2 := winF 0 AccW (2 * ((Pw N : Nat) : Int) * AccW) (lo := 0) (w := AccW) (c := 2 * Pw N * AccW)
    (by have := Nat.mul_le_mul_right AccW (show 1 ≤ 2 * Pw N by omega); omega) hA rfl rfl (by push_cast; rfl)
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hc1 : (1 : Int) ≤ 2 * (2 : Int) ^ clog2 N * AccW := by
    have : ((2 * Pw N * AccW : Nat) : Int) = 2 * (2 : Int) ^ clog2 N * AccW := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos (show 0 < 2 by decide) hP0) hA
    omega
  have hcw : (((2 * (2 : Int) ^ clog2 N * AccW - 1).natAbs : Nat) : Int) + 1 = 2 * (2 : Int) ^ clog2 N * AccW := by
    omega
  have hL0 : ¬ (((Lg N : Nat) : Int) < 0) := by omega
  have hmin : min (((Lg N : Nat) : Int)) 0 = 0 := by omega
  have hab : (((Lg N : Nat) : Int) + 1).natAbs + 1 = Lg N + 2 := by omega
  have hLL : ¬ (((Lg N : Nat) : Int) + 2 ≤ ((Lg N : Nat) : Int)) := by omega
  have hLL' : ¬ (((Lg N : Nat) : Int) + 1 < 0) := by omega
  have hLL'' : ((Lg N : Nat) : Int) + 1 < ((Lg N : Nat) : Int) + 2 := by omega
  have hl1 : (((Lg N : Nat) : Int) + 1).toNat = Lg N + 1 := by omega
  have hnn : (1 : Int) ≤ (N : Int) * N * AccW := by
    have : ((N * N * AccW : Nat) : Int) = (N : Int) * N * AccW := by push_cast; rfl
    have := Nat.mul_pos hNN hA; omega
  have hncw : ((((N : Int) * N * AccW - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * AccW := by omega
  have hA0 : 0 < AccW := hA
  have hA0' : (0 : Int) < AccW := by omega
  have hm0 : min ((AccW : Int) - 1) 0 = 0 := by omega
  have hM0 : max ((AccW : Int) - 1) 0 = (AccW : Int) - 1 := by omega
  have hA1 : ((AccW : Int) - 1 + 1).toNat = AccW := by omega
  have hA2 : (AccW : Int) - 1 < 2 * (2 : Int) ^ clog2 N * AccW := by
    have h1 : ((2 * Pw N * AccW : Nat) : Int) = 2 * (2 : Int) ^ clog2 N * AccW := by push_cast; rfl
    have h2 : AccW ≤ 2 * Pw N * AccW := Nat.le_mul_of_pos_left _ (by omega)
    omega
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem mm_static (N W AccW : Nat) (hN : 1 ≤ N) (hA : 1 ≤ AccW) :
    design.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [ccP N, paP N W, ctlP N AccW, outP N AccW] := by
  rw [show design.pdesign.processes = [ccT, paT, ctlT, outT] from rfl]
  simp only [List.map_cons, List.map_nil, cc_inst, pa_inst, ctl_inst N W AccW hN hA, out_inst N W AccW hN hA]

/-- A window `k` of width `w` fits below window `n`. -/
theorem win_le {k n w : Nat} (h : k < n) : k * w + w ≤ n * w := by
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h

theorem pb_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hk : k < N) :
    instProcess2 ((mmE N W AccW).bindVal "k" k) mmElems pbT = pbP N W k := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hNW : 0 < N * W := Nat.mul_pos hN hW
  have w1 := winF ((k : Int) * N * W) ((N : Int) * W) ((N : Int) * N * W) (lo := k * N * W) (w := N * W)
    (c := N * N * W) (by rw [Nat.mul_assoc k, Nat.mul_assoc N]; exact win_le hk) hNW (by push_cast; rfl)
    (by push_cast; rfl) (by push_cast; rfl)
  have hc1 : (1 : Int) ≤ (N : Int) * N * W := by
    have : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos hN hN) hW; omega
  have hcw : ((((N : Int) * N * W - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * W := by omega
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem red_inst (N W AccW h : Nat) (hA : 1 ≤ AccW) (hh : h < Pw N - 1) :
    instProcess2 ((mmE N W AccW).bindVal "h" h) mmElems redT = redP AccW h := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hP0 := pw_pos N
  have hPI : ((Pw N : Nat) : Int) = (2 : Int) ^ clog2 N := by push_cast; rfl
  have w0 := winF ((h : Int) * AccW) AccW (2 * (2 : Int) ^ clog2 N * AccW) (lo := h * AccW) (w := AccW)
    (c := 2 * Pw N * AccW) (by have := win_le (w := AccW) (show h < 2 * Pw N by omega); omega) hA (by push_cast; rfl)
    rfl (by push_cast; rfl)
  have w1 := winF ((2 * (h : Int) + 1) * AccW) AccW (2 * (2 : Int) ^ clog2 N * AccW) (lo := (2 * h + 1) * AccW)
    (w := AccW) (c := 2 * Pw N * AccW) (by have := win_le (w := AccW) (show 2 * h + 1 < 2 * Pw N by omega); omega) hA
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have w2 := winF ((2 * (h : Int) + 2) * AccW) AccW (2 * (2 : Int) ^ clog2 N * AccW) (lo := (2 * h + 2) * AccW)
    (w := AccW) (c := 2 * Pw N * AccW) (by have := win_le (w := AccW) (show 2 * h + 2 < 2 * Pw N by omega); omega) hA
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have hc1 : (1 : Int) ≤ 2 * (2 : Int) ^ clog2 N * AccW := by
    have : ((2 * Pw N * AccW : Nat) : Int) = 2 * (2 : Int) ^ clog2 N * AccW := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos (show 0 < 2 by decide) hP0) hA
    omega
  have hcw : (((2 * (2 : Int) ^ clog2 N * AccW - 1).natAbs : Nat) : Int) + 1 = 2 * (2 : Int) ^ clog2 N * AccW := by
    omega
  have hA0 : 0 < AccW := hA
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem lane_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hk : k < N) :
    instProcess2 ((mmE N W AccW).bindVal "k" k) mmElems laneT = laneP N W AccW k := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hkN : k * W + W ≤ N * N * W := by
    have := win_le (w := W) hk; have := Nat.mul_le_mul_right W (Nat.le_mul_of_pos_left N hN); omega
  have hkNW : k * N * W + W ≤ N * N * W := by
    have := win_le (w := N * W) hk; rw [Nat.mul_assoc k, Nat.mul_assoc N]; have := Nat.le_mul_of_pos_left W hN; omega
  have wa := winF ((k : Int) * AccW) AccW ((N : Int) * AccW) (lo := k * AccW) (w := AccW) (c := N * AccW)
    (win_le hk) hA (by push_cast; rfl) rfl (by push_cast; rfl)
  have w1 := winF ((k : Int) * W) W ((N : Int) * N * W) (lo := k * W) (w := W) (c := N * N * W) hkN hW
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have w2 := winF ((k : Int) * N * W) W ((N : Int) * N * W) (lo := k * N * W) (w := W) (c := N * N * W) hkNW hW
    (by push_cast; rfl) rfl (by push_cast; rfl)
  have b1' := bitF ((k : Int) * W + W - 1) ((N : Int) * N * W) (i := k * W + W - 1) (c := N * N * W) (by omega)
    (by push_cast [Int.ofNat_sub (show 1 ≤ k * W + W by omega)]; rfl) (by push_cast; rfl)
  have b2' := bitF ((k : Int) * N * W + W - 1) ((N : Int) * N * W) (i := k * N * W + W - 1) (c := N * N * W)
    (by omega) (by push_cast [Int.ofNat_sub (show 1 ≤ k * N * W + W by omega)]; rfl) (by push_cast; rfl)
  have hc1 : (1 : Int) ≤ (N : Int) * N * W := by
    have : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos hN hN) hW; omega
  have hcw : ((((N : Int) * N * W - 1).natAbs : Nat) : Int) + 1 = (N : Int) * N * W := by omega
  have hc2 : (1 : Int) ≤ (N : Int) * AccW := by
    have : ((N * AccW : Nat) : Int) = (N : Int) * AccW := by push_cast; rfl
    have := Nat.mul_pos hN hA; omega
  have hcw2 : ((((N : Int) * AccW - 1).natAbs : Nat) : Int) + 1 = (N : Int) * AccW := by omega
  have hW0 : 0 < W := hW
  have hA0 : 0 < AccW := hA
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

theorem leaf_inst (N W AccW k : Nat) (hN : 1 ≤ N) (hA : 1 ≤ AccW) (hk : k < N) :
    instProcess2 ((mmE N W AccW).bindVal "k" k) mmElems leafT = leafP N AccW k := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hP := le_pw N
  have hP0 := pw_pos N
  have wa := winF ((k : Int) * AccW) AccW ((N : Int) * AccW) (lo := k * AccW) (w := AccW) (c := N * AccW)
    (win_le hk) hA (by push_cast; rfl) rfl (by push_cast; rfl)
  have wt := winF (((2 : Int) ^ clog2 N - 1 + k) * AccW) AccW (2 * (2 : Int) ^ clog2 N * AccW)
    (lo := (Pw N - 1 + k) * AccW) (w := AccW) (c := 2 * Pw N * AccW)
    (by have := win_le (w := AccW) (show Pw N - 1 + k < 2 * Pw N by omega); omega) hA
    (by push_cast [Int.ofNat_sub (show 1 ≤ Pw N by omega)]; rfl) rfl (by push_cast; rfl)
  have hc1 : (1 : Int) ≤ 2 * (2 : Int) ^ clog2 N * AccW := by
    have : ((2 * Pw N * AccW : Nat) : Int) = 2 * (2 : Int) ^ clog2 N * AccW := by push_cast; rfl
    have := Nat.mul_pos (Nat.mul_pos (show 0 < 2 by decide) hP0) hA
    omega
  have hcw : (((2 * (2 : Int) ^ clog2 N * AccW - 1).natAbs : Nat) : Int) + 1 = 2 * (2 : Int) ^ clog2 N * AccW := by
    omega
  have hc2 : (1 : Int) ≤ (N : Int) * AccW := by
    have : ((N * AccW : Nat) : Int) = (N : Int) * AccW := by push_cast; rfl
    have := Nat.mul_pos hN hA; omega
  have hcw2 : ((((N : Int) * AccW - 1).natAbs : Nat) : Int) + 1 = (N : Int) * AccW := by omega
  have hA0 : 0 < AccW := hA
  mm_simp
  try and_intros
  all_goals first | rfl | decide | skip

/-! ### The generates -/

def genFm (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

def pm1E : PExpr := .binary (.m0 .sub) (.paramRef "P" none) (.int 1)

theorem mm_gens_src : design.pdesign.generates =
    [genFm "pb_row" "k" (.paramRef "N" none) 4 ([pbT].map .process),
     genFm "pcu_red" "h" pm1E 3 ([redT].map .process),
     genFm "pcu_lane" "k" (.paramRef "N" none) 4 ([laneT, leafT].map .process)] :=
  rfl

theorem toNat_sub_zero (n : Nat) : ((n : Int) - 0).toNat = n := by omega

theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N + Pw N < F) :
    expandList2 (mmE N W AccW) mmElems F design.pdesign.generates = .ok (genPs N W AccW) := by
  have hP0 := pw_pos N
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  have hPv : (mmE N W AccW).vals.lookup "P" = some ((Pw N : Nat) : Int) := rfl
  have hK : ∀ v : Int, ((mmE N W AccW).bindVal "k" v).vals.lookup "N" = some (N : Int) :=
    fun v => by rw [vals_lookup_bindVal_ne _ (by decide), hNv]
  have hH : ∀ v : Int, ((mmE N W AccW).bindVal "h" v).vals.lookup "P" = some ((Pw N : Nat) : Int) :=
    fun v => by rw [vals_lookup_bindVal_ne _ (by decide), hPv]
  have hPm : (((Pw N : Nat) : Int) - 1 - 0).toNat = Pw N - 1 := by omega
  rw [mm_gens_src, genPs, List.append_assoc]
  refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_singleton_ok ?_))
  · rw [genFm, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun v => isInt_paramRef_of (hK v)) (fun v => evalInt_paramRef_of (hK v))
      (by rw [toNat_sub_zero]; omega), toNat_sub_zero, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, pbPs]
    congr 1
    refine List.map_congr_left fun k hk => ?_
    exact pb_inst N W AccW k hN hW (List.mem_range.mp hk)
  · rw [genFm, pm1E, GenItem.expand2_genFor_ascending_processes (N := ((Pw N : Nat) : Int) - 1) (evalInt_int 0)
      (fun v => isInt_binary_of rfl (isInt_paramRef_of (hH v)) rfl)
      (fun v => evalInt_sub_of (isInt_paramRef_of (hH v)) rfl (evalInt_paramRef_of (hH v)) (evalInt_int 1))
      (by rw [hPm]; omega), hPm, intRange_zero]
    simp only [List.map_cons, List.map_nil, Gen2.flatMap_singleton_map, List.map_map, redPs]
    exact congrArg _ (List.map_congr_left fun h hh => red_inst N W AccW h hA (List.mem_range.mp hh))
  · rw [genFm, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun v => isInt_paramRef_of (hK v)) (fun v => evalInt_paramRef_of (hK v))
      (by rw [toNat_sub_zero]; omega), toNat_sub_zero, intRange_zero]
    simp only [List.map_cons, List.map_nil, List.flatMap_map, lanePs]
    exact congrArg _ (CombView.flatMap_congr' fun k hk => by
      rw [lane_inst N W AccW k hN hW hA (List.mem_range.mp hk), leaf_inst N W AccW k hN hA (List.mem_range.mp hk)])

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (mmEnv N W AccW) (mmDecls N W AccW) mmElems (genPs N W AccW)) := by
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv N W AccW hN hr hW) (mm_decls N W AccW hN hW hA)
    (mm_elems N W AccW) (mm_gens N W AccW _ hN hW hA ?_)
  have hP := pw_lt N hN
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  have key : ∀ s : Nat, N ≤ s → N + Pw N < (s + 2) * (s + 2) + 64 := fun s hs => by
    have := Nat.mul_le_mul (show N ≤ s + 2 by omega) (show 3 ≤ s + 2 by omega); omega
  exact key _ (by omega)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA hr), PDesign.assemble2_processes,
    mm_static N W AccW hN hA]
  simp [design.pdesign]

/-! ### Pairwise disjoint writes -/

/-- Disjointness of the windows of two processes. -/
abbrev Disj (p q : Process2) : Prop := ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false

/-- Every window of `p` is of the name `n`, inside `[lo, lo + w)`. -/
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
    (hq : Within q n lo' w') (h : lo + w ≤ lo' ∨ lo' + w' ≤ lo) : Disj p q := by
  intro a ha b hb
  obtain ⟨-, l, v, hav, h1, h2⟩ := hp a ha
  obtain ⟨-, l', v', hbv, h1', h2'⟩ := hq b hb
  simp only [DrvWin.overlaps, hav, hbv, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  right; omega

theorem names_of_within {p : Process2} {n : String} {lo w : Nat} (h : Within p n lo w) : Names p [n] :=
  fun a ha => by simp [(h a ha).1]

theorem disj_symm {p q : Process2} (h : Disj p q) : Disj q p :=
  fun a ha b hb => by rw [DrvWin.overlaps_comm]; exact h b hb a ha

section windows
variable (N W AccW : Nat)

theorem names_of_fst {p : Process2} {ns : List String} (h : ∀ n ∈ p.procWins.map Prod.fst, n ∈ ns) :
    Names p ns := fun a ha => h a.1 (List.mem_map_of_mem ha)

theorem cc_names : Names (ccP N) ["cc_run", "cc_i", "cc_j"] :=
  names_of_fst (by simp [ccP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

theorem pa_names : Names (paP N W) ["pa_mem"] :=
  names_of_fst (by simp [paP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

theorem out_names : Names (outP N AccW) ["done", "C"] :=
  names_of_fst (by simp [outP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

theorem ctl_names : Names (ctlP N AccW) ["pcu_tr", "pcu_vld", "pcu_lst"] :=
  names_of_fst (by simp [ctlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins])

/-- The control's only `pcu_tr` window is above the lanes. -/
theorem ctl_tr : ∀ a ∈ (ctlP N AccW).procWins, a.1 = "pcu_tr" →
    a.2 = some ((Pw N - 1 + N) * AccW, (Pw N + 1 - N) * AccW) := by
  intro a ha
  simp [ctlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ctl_disj_tr {q : Process2} {lo w : Nat} (hq : Within q "pcu_tr" lo w)
    (hlt : lo + w ≤ (Pw N - 1 + N) * AccW) : Disj (ctlP N AccW) q := by
  intro a ha b hb
  obtain ⟨hb1, l, v, hbv, h1, h2⟩ := hq b hb
  by_cases ht : a.1 = "pcu_tr"
  · have h3 := ctl_tr N AccW a ha ht
    obtain ⟨an, aw⟩ := a; obtain ⟨bn, bw⟩ := b
    simp only at ht hb1 h3 hbv
    subst ht hb1 h3 hbv
    simp only [DrvWin.overlaps, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    left; omega
  · obtain ⟨an, aw⟩ := a; obtain ⟨bn, bw⟩ := b
    simp only at ht hb1
    subst hb1
    simp only [DrvWin.overlaps, Bool.and_eq_false_iff]
    left; simpa using ht

theorem pb_within (k : Nat) : Within (pbP N W k) "pb_mem" (k * N * W) (N * W) := by
  intro a ha
  simp [pbP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl <;> exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem red_within (h : Nat) : Within (redP AccW h) "pcu_tr" (h * AccW) AccW := by
  intro a ha
  simp [redP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  subst ha; exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem leaf_within (k : Nat) : Within (leafP N AccW k) "pcu_tr" ((Pw N - 1 + k) * AccW) AccW := by
  intro a ha
  simp [leafP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  subst ha; exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Lane `k`'s vector inputs: `pcu_va` and `pcu_vb`, word `k` each. -/
theorem lane_wins (k : Nat) : ∀ a ∈ (laneP N W AccW k).procWins,
    a = ("pcu_va", some (k * AccW, AccW)) ∨ a = ("pcu_vb", some (k * AccW, AccW)) := by
  intro a ha
  simp [laneP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  exact ha

theorem lane_names (k : Nat) : Names (laneP N W AccW k) ["pcu_va", "pcu_vb"] := by
  intro a ha
  rcases lane_wins N W AccW k a ha with rfl | rfl <;> simp

theorem lane_disj {k k' : Nat} (h : k < k') : Disj (laneP N W AccW k) (laneP N W AccW k') := by
  intro a ha b hb
  have := win_le (w := AccW) h
  rcases lane_wins N W AccW k a ha with rfl | rfl <;> rcases lane_wins N W AccW k' b hb with rfl | rfl <;>
    simp [DrvWin.overlaps] <;> omega

end windows

theorem mm_pairwise (N W AccW : Nat) (hN : 1 ≤ N) :
    (ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW).Pairwise Disj := by
  have hP := le_pw N
  have hpb : ∀ p ∈ pbPs N W, Names p ["pb_mem"] := by
    intro p hp; obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp; exact names_of_within (pb_within N W k)
  have hred : ∀ p ∈ redPs N AccW, ∃ h, h < Pw N - 1 ∧ p = redP AccW h := by
    intro p hp; obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp; exact ⟨h, List.mem_range.mp hh, rfl⟩
  have hlane : ∀ p ∈ lanePs N W AccW, ∃ k, k < N ∧ (p = laneP N W AccW k ∨ p = leafP N AccW k) := by
    intro p hp
    simp only [lanePs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hp
    obtain ⟨k, hk, h⟩ := hp; exact ⟨k, hk, h⟩
  have hgen : ∀ p ∈ genPs N W AccW, Names p ["pb_mem", "pcu_tr", "pcu_va", "pcu_vb"] := by
    intro p hp a ha
    simp only [genPs, List.mem_append] at hp
    rcases hp with (hp | hp) | hp
    · have := hpb p hp a ha; simp_all
    · obtain ⟨h, -, rfl⟩ := hred p hp; have := names_of_within (red_within AccW h) a ha; simp_all
    · obtain ⟨k, -, rfl | rfl⟩ := hlane p hp
      · have := lane_names N W AccW k a ha; simp_all
      · have := names_of_within (leaf_within N AccW k) a ha; simp_all
  -- the control against the generated processes
  have hctl : ∀ q ∈ genPs N W AccW, Disj (ctlP N AccW) q := by
    intro q hq
    simp only [genPs, List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact disj_of_names (ctl_names N AccW) (hpb q hq) (by decide)
    · obtain ⟨h, hh, rfl⟩ := hred q hq
      exact ctl_disj_tr N AccW (red_within AccW h) (win_le (show h < Pw N - 1 + N by omega))
    · obtain ⟨k, hk, rfl | rfl⟩ := hlane q hq
      · exact disj_of_names (ctl_names N AccW) (lane_names N W AccW k) (by decide)
      · exact ctl_disj_tr N AccW (leaf_within N AccW k) (win_le (show Pw N - 1 + k < Pw N - 1 + N by omega))
  refine .cons (fun q hq => ?_) (.cons (fun q hq => ?_) (.cons (fun q hq => ?_) (.cons (fun q hq => ?_) ?_)))
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (cc_names N) (pa_names N W) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (cc_names N) (ctl_names N AccW) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (cc_names N) (out_names N AccW) (by decide)
    · exact disj_of_names (cc_names N) (hgen q hq) (by decide)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (pa_names N W) (ctl_names N AccW) (by decide)
    rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (pa_names N W) (out_names N AccW) (by decide)
    · exact disj_of_names (pa_names N W) (hgen q hq) (by decide)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact disj_of_names (ctl_names N AccW) (out_names N AccW) (by decide)
    · exact hctl q hq
  · exact disj_of_names (out_names N AccW) (hgen q hq) (by decide)
  · simp only [genPs, List.pairwise_append]
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun hx hy hxy => ?_)
      exact disj_of_within (pb_within N W _) (pb_within N W _)
        (.inl (by rw [Nat.mul_assoc, Nat.mul_assoc _ N W]; exact win_le hxy))
    · refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun hx hy hxy => ?_)
      exact disj_of_within (red_within AccW _) (red_within AccW _) (.inl (win_le hxy))
    · intro p hp q hq
      obtain ⟨h, -, rfl⟩ := hred q hq
      exact disj_of_names (hpb p hp) (names_of_within (red_within AccW h)) (by decide)
    · refine pairwise_flatMap_range (fun k hk => ?_) (fun k k' hkk hk' a ha b hb => ?_)
      · refine List.pairwise_cons.mpr ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩
        rw [List.mem_singleton.mp hq]
        exact disj_of_names (lane_names N W AccW k) (names_of_within (leaf_within N AccW k)) (by decide)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact lane_disj N W AccW hkk
        · exact disj_of_names (lane_names N W AccW k) (names_of_within (leaf_within N AccW k')) (by decide)
        · exact disj_of_names (names_of_within (leaf_within N AccW k)) (lane_names N W AccW k') (by decide)
        · exact disj_of_within (leaf_within N AccW k) (leaf_within N AccW k')
            (.inl (win_le (show Pw N - 1 + k < Pw N - 1 + k' by omega)))
    · intro p hp q hq
      obtain ⟨k, hk, rfl | rfl⟩ := hlane q hq
      · simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact disj_of_names (hpb p hp) (lane_names N W AccW k) (by decide)
        · obtain ⟨h, -, rfl⟩ := hred p hp
          exact disj_of_names (names_of_within (red_within AccW h)) (lane_names N W AccW k) (by decide)
      · simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact disj_of_names (hpb p hp) (names_of_within (leaf_within N AccW k)) (by decide)
        · obtain ⟨h, hh, rfl⟩ := hred p hp
          exact disj_of_within (red_within AccW h) (leaf_within N AccW k)
            (.inl (win_le (show h < Pw N - 1 + k by omega)))

theorem mm_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW) :
    p = ccP N ∨ p = paP N W ∨ p = ctlP N AccW ∨ p = outP N AccW ∨ (∃ k, p = pbP N W k) ∨ (∃ h, p = redP AccW h) ∨
      (∃ k, p = laneP N W AccW k) ∨ ∃ k, p = leafP N AccW k := by
  simp only [genPs, pbPs, redPs, lanePs, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | ((⟨k, -, rfl⟩ | ⟨h, -, rfl⟩) | ⟨k, -, rfl | rfl⟩)
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨k, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨h, rfl⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨k, rfl⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨k, rfl⟩))))))

theorem mm_driversOk (N W AccW : Nat) (hN : 1 ≤ N) :
    driversOk design.pdesign.declNames design.pdesign.inputNames
      (ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW hN)
  · intro p hp
    rcases mm_mem hp with rfl | rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨h, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap]
    rintro n ⟨p, hp, hn⟩
    rcases mm_mem hp with rfl | rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨h, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    all_goals revert n; simp [ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, nb, Process2.procWrites,
      Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide

/-- **The loaded family is `mmD`**, at every in-range `(N, W, AccW)`. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31) :
    design.sem N W AccW = mmD N W AccW := by
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA hr]; exact mm_driversOk N W AccW hN)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA hr)]
  simp only [PDesign.assemble2, mm_static N W AccW hN hA, mmD]
  simp [design.pdesign]

/-! ## 2. G0's clock step for the loaded family -/

/-- **`mmD` is in G0's decidable FF-only profile at every `(N, W, AccW)`.** -/
theorem mm_profile (N W AccW : Nat) (hN : 1 ≤ N) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  have hl : (mmD N W AccW).processes.toList = ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by
    simp [mmD]
  refine ⟨?_, ffDisjB_of_pairwise (hl ▸ mm_pairwise N W AccW hN)⟩
  simp [mmD, genPs, pbPs, redPs, lanePs, ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, nb, List.all_flatMap,
    List.all_map, List.all_append, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly, Stmt2.nbaStaticB,
    Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?, Design2.declWidth, Design2.inputNames,
    Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, mmDecls]

/-- The 17 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("cc_i", ci), ("cc_j", cj),
   ("cc_run", rn), ("pa_mem", pa), ("pb_mem", pb), ("pcu_va", va), ("pcu_vb", vb), ("pcu_vld", vl),
   ("pcu_lst", ls), ("pcu_tr", tr)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c ci cj rn pa pb va vb vl ls tr := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The test `x == N - 1`. -/
abbrev eqm1 (N : Nat) (x : LVec) : Bool :=
  (LVec.ofLogic (x.eqLogical ((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)))).condTrue

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

def ccQ (N : Nat) (r s ci cj rn : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "cc_run" rn (b1 false)]
  else if s.condTrue then [wr "cc_run" rn (b1 true), wr "cc_i" ci (zv 32), wr "cc_j" cj (zv 32)]
  else if rn.condTrue then
    if eqm1 N cj then
      wr "cc_j" cj (zv 32) :: wr "cc_i" ci (ci.add (LVec.ofInt 32 1)) ::
        (if eqm1 N ci then [wr "cc_run" rn (b1 false)] else [])
    else [wr "cc_j" cj (cj.add (LVec.ofInt 32 1))]
  else []

/-- PMU_A's rotation by one row. -/
abbrev rotA (N W : Nat) (pa : LVec) : LVec :=
  (pa.shr ((LVec.ofInt 32 N).mul (LVec.ofInt 32 W))).or
    (pa.shl ((((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)).mul (LVec.ofInt 32 N)).mul (LVec.ofInt 32 W)))

def paQ (N W : Nat) (s a cj rn pa : LVec) : NbaQueue2 :=
  if s.condTrue then [wr "pa_mem" pa a]
  else if rn.condTrue then (if eqm1 N cj then [wr "pa_mem" pa (rotA N W pa)] else [])
  else []

def ctlQ (N AccW : Nat) (r s ci cj rn vl ls : LVec) : NbaQueue2 :=
  ("pcu_tr", (Pw N - 1 + N) * AccW, (zv ((Pw N + 1 - N) * AccW)).resizeU ((Pw N + 1 - N) * AccW)) ::
  (if r.condTrue then [wr "pcu_vld" vl (zv (Lg N + 2)), wr "pcu_lst" ls (zv (Lg N + 2))]
   else if s.condTrue then [wr "pcu_vld" vl (zv (Lg N + 2)), wr "pcu_lst" ls (zv (Lg N + 2))]
   else [wr "pcu_vld" vl (LVec.concatMany #[vl.extract 0 (Lg N + 1), rn]),
     wr "pcu_lst" ls (LVec.concatMany #[ls.extract 0 (Lg N + 1),
       (LVec.ofLogic (ci.eqLogical ((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)))).and
         (LVec.ofLogic (cj.eqLogical ((LVec.ofInt 32 N).sub (LVec.ofInt 32 1))))])])

def outQ (N AccW : Nat) (r s dn c vl ls tr : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "done" dn (b1 false)]
  else if s.condTrue then [wr "done" dn (b1 false)]
  else if (vl.extract (Lg N + 1) 1).condTrue then
    wr "C" c (c.shr (LVec.ofInt 32 AccW)) :: ("C", (N * N - 1) * AccW, (tr.extract 0 AccW).resizeU AccW) ::
      (if (ls.extract (Lg N + 1) 1).condTrue then [wr "done" dn (b1 true)] else [])
  else []

/-- PMU_B's row rotation by one entry. -/
abbrev rotB (N W : Nat) (row : LVec) : LVec :=
  (row.shr (LVec.ofInt 32 W)).or (row.shl (((LVec.ofInt 32 N).sub (LVec.ofInt 32 1)).mul (LVec.ofInt 32 W)))

def pbQ (N W : Nat) (s b rn pb : LVec) (k : Nat) : NbaQueue2 :=
  if s.condTrue then [("pb_mem", k * N * W, (b.extract (k * N * W) (N * W)).resizeU (N * W))]
  else if rn.condTrue then [("pb_mem", k * N * W, (rotB N W (pb.extract (k * N * W) (N * W))).resizeU (N * W))]
  else []

def redQ (AccW : Nat) (tr : LVec) (h : Nat) : NbaQueue2 :=
  [("pcu_tr", h * AccW,
    ((tr.extract ((2 * h + 1) * AccW) AccW).add (tr.extract ((2 * h + 2) * AccW) AccW)).resizeU AccW)]

def laneQ (N W AccW : Nat) (pa pb : LVec) (k : Nat) : NbaQueue2 :=
  [("pcu_va", k * AccW, ((sxv pa AccW (k * W) W).resizeU AccW).resizeU AccW),
   ("pcu_vb", k * AccW, ((sxv pb AccW (k * N * W) W).resizeU AccW).resizeU AccW)]

def leafQ (N AccW : Nat) (va vb : LVec) (k : Nat) : NbaQueue2 :=
  [("pcu_tr", (Pw N - 1 + k) * AccW,
    ((va.extract (k * AccW) AccW).mul (vb.extract (k * AccW) AccW)).resizeU AccW)]

section run
variable (F : Nat) (hF : 40 ≤ F) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec)
include hF

theorem cc_run (N : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) [] (ccP N) =
    .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, ccQ N r s ci cj rn) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold ccQ
  by_cases h1 : r.condTrue = true
  · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1]
  by_cases h2 : s.condTrue = true
  · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2]
  by_cases h3 : rn.condTrue = true
  · by_cases h4 : eqm1 N cj = true
    · by_cases h5 : eqm1 N ci = true
      · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
          SvState.lookup, evalBinOp, wr, h1, h2, h3, h4, h5]
      · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
          SvState.lookup, evalBinOp, wr, h1, h2, h3, h4, h5]
    · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
        SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]
  · simp [ccP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3]

theorem pa_run (N W : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) [] (paP N W) =
    .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, paQ N W s a cj rn pa) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold paQ
  by_cases h2 : s.condTrue = true
  · simp [paP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h2]
  by_cases h3 : rn.condTrue = true
  · by_cases h4 : eqm1 N cj = true
    · simp [paP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
        SvState.lookup, evalBinOp, wr, h2, h3, h4]
    · simp [paP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
        SvState.lookup, evalBinOp, wr, h2, h3, h4]
  · simp [paP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h2, h3]

theorem ctl_run (N AccW : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) []
    (ctlP N AccW) = .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, ctlQ N AccW r s ci cj rn vl ls) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold ctlQ
  by_cases h1 : r.condTrue = true
  · simp [ctlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      MS, SvState.lookup, evalBinOp, wr, h1]
  by_cases h2 : s.condTrue = true
  · simp [ctlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      MS, SvState.lookup, evalBinOp, wr, h1, h2]
  · simp [ctlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      MS, SvState.lookup, evalBinOp, wr, h1, h2]

theorem out_run (N AccW : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) []
    (outP N AccW) = .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, outQ N AccW r s dn c vl ls tr) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold outQ
  by_cases h1 : r.condTrue = true
  · simp [outP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1]
  by_cases h2 : s.condTrue = true
  · simp [outP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2]
  by_cases h3 : (vl.extract (Lg N + 1) 1).condTrue = true
  · by_cases h4 : (ls.extract (Lg N + 1) 1).condTrue = true
    · simp [outP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
        SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]
    · simp [outP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
        SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]
  · simp [outP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3]

theorem pb_run (N W k : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) [] (pbP N W k) =
    .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, pbQ N W s b rn pb k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold pbQ
  by_cases h2 : s.condTrue = true <;> by_cases h3 : rn.condTrue = true <;>
    simp_all [pbP, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp]

theorem red_run (AccW h : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) []
    (redP AccW h) = .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, redQ AccW tr h) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  simp [redP, redQ, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup, evalBinOp]

theorem lane_run (N W AccW k : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) []
    (laneP N W AccW k) = .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, laneQ N W AccW pa pb k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  simp [laneP, laneQ, sext, sxv, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
    readSignal, MS, SvState.lookup, evalBinOp]

theorem leaf_run (N AccW k : Nat) : runEdgeProcess2 F (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) []
    (leafP N AccW k) = .ok (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr, leafQ N AccW va vb k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  simp [leafP, leafQ, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
    SvState.lookup, evalBinOp]

end run

/-- The cycle's updates, in process order. -/
def Q (N W AccW : Nat) (r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) : NbaQueue2 :=
  ccQ N r s ci cj rn ++ paQ N W s a cj rn pa ++ ctlQ N AccW r s ci cj rn vl ls ++ outQ N AccW r s dn c vl ls tr ++
    ((List.range N).flatMap (pbQ N W s b rn pb) ++ (List.range (Pw N - 1)).flatMap (redQ AccW tr) ++
      (List.range N).flatMap fun k => laneQ N W AccW pa pb k ++ leafQ N AccW va vb k)

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr)

theorem mmD_procs (N W AccW : Nat) :
    (mmD N W AccW).processes.toList = ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by
  simp [mmD]

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus entry, any state
of the design's shape, every fuel from 40). -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hr : N * N * W < 2 ^ 31)
    (σ : ScheduleOracle) (e : SvState) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) (kk F : Nat)
    (hF : 40 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c ci cj rn pa pb va vb vl ls tr, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    rw [mmD_procs] at hp
    rcases mm_mem hp with rfl | rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨h, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rfl
  rw [mm_sem_eq N W AccW hN hW hA hr, cycleStep2_profile (mm_profile N W AccW hN) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD_procs, genPs, pbPs, redPs, lanePs, List.flatMap_cons, List.flatMap_append, List.flatMap_map,
      List.flatMap_assoc, List.flatMap_nil, List.append_nil, cc_run F hF, pa_run F hF, ctl_run F hF, out_run F hF,
      pb_run F hF, red_run F hF, lane_run F hF, leaf_run F hF, mmNext, Q, List.append_assoc]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by
      rw [← mmD_procs N W AccW]; exact List.mem_of_getElem? (by simpa using hp)
    rcases mm_mem hm with rfl | rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨h, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨_, cc_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N⟩
    · exact ⟨_, pa_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W⟩
    · exact ⟨_, ctl_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW⟩
    · exact ⟨_, out_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW⟩
    · exact ⟨_, pb_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W k⟩
    · exact ⟨_, red_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AccW h⟩
    · exact ⟨_, lane_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W AccW k⟩
    · exact ⟨_, leaf_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N AccW k⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The commit, register by register -/

section commit
variable {ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec} {lo : Nat} {w : LVec}
theorem nb_dn : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("done", lo, w) =
    MS ck r s a b (dn.insertAt lo w) c ci cj rn pa pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("C", lo, w) =
    MS ck r s a b dn (c.insertAt lo w) ci cj rn pa pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ci : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("cc_i", lo, w) =
    MS ck r s a b dn c (ci.insertAt lo w) cj rn pa pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_cj : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("cc_j", lo, w) =
    MS ck r s a b dn c ci (cj.insertAt lo w) rn pa pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_rn : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("cc_run", lo, w) =
    MS ck r s a b dn c ci cj (rn.insertAt lo w) pa pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_pa : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pa_mem", lo, w) =
    MS ck r s a b dn c ci cj rn (pa.insertAt lo w) pb va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_pb : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pb_mem", lo, w) =
    MS ck r s a b dn c ci cj rn pa (pb.insertAt lo w) va vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_va : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pcu_va", lo, w) =
    MS ck r s a b dn c ci cj rn pa pb (va.insertAt lo w) vb vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_vb : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pcu_vb", lo, w) =
    MS ck r s a b dn c ci cj rn pa pb va (vb.insertAt lo w) vl ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_vl : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pcu_vld", lo, w) =
    MS ck r s a b dn c ci cj rn pa pb va vb (vl.insertAt lo w) ls tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ls : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pcu_lst", lo, w) =
    MS ck r s a b dn c ci cj rn pa pb va vb vl (ls.insertAt lo w) tr := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_tr : nbaStep (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) ("pcu_tr", lo, w) =
    MS ck r s a b dn c ci cj rn pa pb va vb vl ls (tr.insertAt lo w) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- The twelve registers. -/
abbrev RegName (n : String) : Prop := n = "done" ∨ n = "C" ∨ n = "cc_i" ∨ n = "cc_j" ∨ n = "cc_run" ∨ n = "pa_mem" ∨ n = "pb_mem" ∨ n = "pcu_va" ∨ n = "pcu_vb" ∨ n = "pcu_vld" ∨ n = "pcu_lst" ∨ n = "pcu_tr"

/-- Committing a queue of writes to the twelve registers. -/
theorem commit_MS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c ci cj rn pa pb va vb vl ls tr : LVec),
    (∀ u ∈ q, RegName u.1) →
    commitNba2 (MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr) q = MS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "cc_i" q ci) (nbaFold "cc_j" q cj) (nbaFold "cc_run" q rn) (nbaFold "pa_mem" q pa) (nbaFold "pb_mem" q pb) (nbaFold "pcu_va" q va) (nbaFold "pcu_vb" q vb) (nbaFold "pcu_vld" q vl) (nbaFold "pcu_lst" q ls) (nbaFold "pcu_tr" q tr)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, h => by
    have hq := @commit_MS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;> subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_ci, nb_cj, nb_rn, nb_pa, nb_pb, nb_va, nb_vb, nb_vl, nb_ls, nb_tr,
        hq _ _ _ _ _ _ _ _ _ _ _ _ h', nbaFold]

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 := h u List.mem_cons_self
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

theorem skip_of_names {q : NbaQueue2} {ns : List String} (h : ∀ u ∈ q, u.1 ∈ ns) {n : String} (hn : n ∉ ns)
    (x : LVec) : nbaFold n q x = x :=
  nbaFold_of_forall_ne (fun u hu he => hn (by rw [← he]; exact h u hu)) x

theorem names_flatMap {α : Type} {l : List α} {f : α → NbaQueue2} {ns : List String}
    (h : ∀ k, ∀ u ∈ f k, u.1 ∈ ns) : ∀ u ∈ l.flatMap f, u.1 ∈ ns := by
  intro u hu
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hu
  exact h k u hk

section names
variable {N W AccW : Nat} {r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec}

theorem ccQ_names : ∀ u ∈ ccQ N r s ci cj rn, u.1 ∈ ["cc_run", "cc_i", "cc_j"] := by
  intro u hu; unfold ccQ at hu; (repeat' split at hu) <;> simp at hu <;> (try rcases hu with rfl | rfl | rfl) <;>
    (try rcases hu with rfl | rfl) <;> (try subst hu) <;> simp
theorem paQ_names : ∀ u ∈ paQ N W s a cj rn pa, u.1 ∈ ["pa_mem"] := by
  intro u hu; unfold paQ at hu; (repeat' split at hu) <;> simp at hu <;> (try subst hu) <;> simp
theorem ctlQ_names : ∀ u ∈ ctlQ N AccW r s ci cj rn vl ls, u.1 ∈ ["pcu_tr", "pcu_vld", "pcu_lst"] := by
  intro u hu; unfold ctlQ at hu; (repeat' split at hu) <;> simp at hu <;> rcases hu with rfl | rfl | rfl <;> simp
theorem outQ_names : ∀ u ∈ outQ N AccW r s dn c vl ls tr, u.1 ∈ ["done", "C"] := by
  intro u hu; unfold outQ at hu; (repeat' split at hu) <;> simp at hu <;> (try rcases hu with rfl | rfl | rfl) <;>
    (try rcases hu with rfl | rfl) <;> (try subst hu) <;> simp
theorem pbQ_names (k : Nat) : ∀ u ∈ pbQ N W s b rn pb k, u.1 ∈ ["pb_mem"] := by
  intro u hu; unfold pbQ at hu; (repeat' split at hu) <;> simp at hu <;> (try subst hu) <;> simp
theorem redQ_names (h : Nat) : ∀ u ∈ redQ AccW tr h, u.1 ∈ ["pcu_tr"] := by
  intro u hu; simp [redQ] at hu; subst hu; simp
theorem laneQ_names (k : Nat) : ∀ u ∈ laneQ N W AccW pa pb k, u.1 ∈ ["pcu_va", "pcu_vb"] := by
  intro u hu; simp [laneQ] at hu; rcases hu with rfl | rfl <;> simp
theorem leafQ_names (k : Nat) : ∀ u ∈ leafQ N AccW va vb k, u.1 ∈ ["pcu_tr"] := by
  intro u hu; simp [leafQ] at hu; subst hu; simp

theorem Q_names : ∀ u ∈ Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr, RegName u.1 := by
  intro u hu
  simp only [Q, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with (((hu | hu) | hu) | hu) | ((⟨k, -, hu⟩ | ⟨h, -, hu⟩) | ⟨k, -, hu | hu⟩)
  · have := ccQ_names u hu; simp at this; rcases this with h | h | h <;> simp [RegName, h]
  · have := paQ_names u hu; simp at this; simp [RegName, this]
  · have := ctlQ_names u hu; simp at this; rcases this with h | h | h <;> simp [RegName, h]
  · have := outQ_names u hu; simp at this; rcases this with h | h <;> simp [RegName, h]
  · have := pbQ_names k u hu; simp at this; simp [RegName, this]
  · have := redQ_names h u hu; simp at this; simp [RegName, this]
  · have := laneQ_names k u hu; simp at this; rcases this with h | h <;> simp [RegName, h]
  · have := leafQ_names k u hu; simp at this; simp [RegName, this]

theorem lanes_names : ∀ u ∈ (List.range N).flatMap (fun k => laneQ N W AccW pa pb k ++ leafQ N AccW va vb k),
    u.1 ∈ ["pcu_va", "pcu_vb", "pcu_tr"] := by
  refine names_flatMap fun k u hu => ?_
  rcases List.mem_append.mp hu with hu | hu
  · have := laneQ_names k u hu; simp at this ⊢; rcases this with h | h <;> simp [h]
  · have := leafQ_names k u hu; simp at this ⊢; simp [this]

theorem fold_dn (x : LVec) : nbaFold "done" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "done" (outQ N AccW r s dn c vl ls tr) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "done") (by decide), skip_of_names paQ_names (n := "done") (by decide), skip_of_names ctlQ_names (n := "done") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "done") (by decide), skip_of_names (names_flatMap redQ_names) (n := "done") (by decide), skip_of_names lanes_names (n := "done") (by decide)]

theorem fold_c (x : LVec) : nbaFold "C" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "C" (outQ N AccW r s dn c vl ls tr) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "C") (by decide), skip_of_names paQ_names (n := "C") (by decide), skip_of_names ctlQ_names (n := "C") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "C") (by decide), skip_of_names (names_flatMap redQ_names) (n := "C") (by decide), skip_of_names lanes_names (n := "C") (by decide)]

theorem fold_ci (x : LVec) : nbaFold "cc_i" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "cc_i" (ccQ N r s ci cj rn) x := by
  simp only [Q, nbaFold_append, skip_of_names paQ_names (n := "cc_i") (by decide), skip_of_names ctlQ_names (n := "cc_i") (by decide), skip_of_names outQ_names (n := "cc_i") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "cc_i") (by decide), skip_of_names (names_flatMap redQ_names) (n := "cc_i") (by decide), skip_of_names lanes_names (n := "cc_i") (by decide)]

theorem fold_cj (x : LVec) : nbaFold "cc_j" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "cc_j" (ccQ N r s ci cj rn) x := by
  simp only [Q, nbaFold_append, skip_of_names paQ_names (n := "cc_j") (by decide), skip_of_names ctlQ_names (n := "cc_j") (by decide), skip_of_names outQ_names (n := "cc_j") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "cc_j") (by decide), skip_of_names (names_flatMap redQ_names) (n := "cc_j") (by decide), skip_of_names lanes_names (n := "cc_j") (by decide)]

theorem fold_rn (x : LVec) : nbaFold "cc_run" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "cc_run" (ccQ N r s ci cj rn) x := by
  simp only [Q, nbaFold_append, skip_of_names paQ_names (n := "cc_run") (by decide), skip_of_names ctlQ_names (n := "cc_run") (by decide), skip_of_names outQ_names (n := "cc_run") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "cc_run") (by decide), skip_of_names (names_flatMap redQ_names) (n := "cc_run") (by decide), skip_of_names lanes_names (n := "cc_run") (by decide)]

theorem fold_pa (x : LVec) : nbaFold "pa_mem" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "pa_mem" (paQ N W s a cj rn pa) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pa_mem") (by decide), skip_of_names ctlQ_names (n := "pa_mem") (by decide), skip_of_names outQ_names (n := "pa_mem") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pa_mem") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pa_mem") (by decide), skip_of_names lanes_names (n := "pa_mem") (by decide)]

theorem fold_pb (x : LVec) : nbaFold "pb_mem" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    (List.range N).foldl (fun acc k => nbaFold "pb_mem" (pbQ N W s b rn pb k) acc) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pb_mem") (by decide), skip_of_names paQ_names (n := "pb_mem") (by decide), skip_of_names ctlQ_names (n := "pb_mem") (by decide), skip_of_names outQ_names (n := "pb_mem") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pb_mem") (by decide), skip_of_names lanes_names (n := "pb_mem") (by decide), nbaFold_flatMap]

theorem fold_va (x : LVec) : nbaFold "pcu_va" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    (List.range N).foldl (fun acc k => nbaFold "pcu_va" (laneQ N W AccW pa pb k) acc) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pcu_va") (by decide), skip_of_names paQ_names (n := "pcu_va") (by decide), skip_of_names ctlQ_names (n := "pcu_va") (by decide), skip_of_names outQ_names (n := "pcu_va") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pcu_va") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pcu_va") (by decide), nbaFold_flatMap, nbaFold_append, skip_of_names (leafQ_names _) (n := "pcu_va") (by decide)]

theorem fold_vb (x : LVec) : nbaFold "pcu_vb" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    (List.range N).foldl (fun acc k => nbaFold "pcu_vb" (laneQ N W AccW pa pb k) acc) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pcu_vb") (by decide), skip_of_names paQ_names (n := "pcu_vb") (by decide), skip_of_names ctlQ_names (n := "pcu_vb") (by decide), skip_of_names outQ_names (n := "pcu_vb") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pcu_vb") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pcu_vb") (by decide), nbaFold_flatMap, nbaFold_append, skip_of_names (leafQ_names _) (n := "pcu_vb") (by decide)]

theorem fold_vl (x : LVec) : nbaFold "pcu_vld" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "pcu_vld" (ctlQ N AccW r s ci cj rn vl ls) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pcu_vld") (by decide), skip_of_names paQ_names (n := "pcu_vld") (by decide), skip_of_names outQ_names (n := "pcu_vld") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pcu_vld") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pcu_vld") (by decide), skip_of_names lanes_names (n := "pcu_vld") (by decide)]

theorem fold_ls (x : LVec) : nbaFold "pcu_lst" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    nbaFold "pcu_lst" (ctlQ N AccW r s ci cj rn vl ls) x := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pcu_lst") (by decide), skip_of_names paQ_names (n := "pcu_lst") (by decide), skip_of_names outQ_names (n := "pcu_lst") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pcu_lst") (by decide), skip_of_names (names_flatMap redQ_names) (n := "pcu_lst") (by decide), skip_of_names lanes_names (n := "pcu_lst") (by decide)]

theorem fold_tr (x : LVec) : nbaFold "pcu_tr" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) x =
    (List.range N).foldl (fun acc k => nbaFold "pcu_tr" (leafQ N AccW va vb k) acc)
      ((List.range (Pw N - 1)).foldl (fun acc h => nbaFold "pcu_tr" (redQ AccW tr h) acc)
        (nbaFold "pcu_tr" (ctlQ N AccW r s ci cj rn vl ls) x)) := by
  simp only [Q, nbaFold_append, skip_of_names ccQ_names (n := "pcu_tr") (by decide), skip_of_names paQ_names (n := "pcu_tr") (by decide), skip_of_names outQ_names (n := "pcu_tr") (by decide), skip_of_names (names_flatMap pbQ_names) (n := "pcu_tr") (by decide), nbaFold_flatMap, nbaFold_append, skip_of_names (laneQ_names _) (n := "pcu_tr") (by decide)]

end names

/-! ## 4. The register values of a transaction, in `BitVec` -/

/-- A part select of a part select. -/
theorem xl_xl {n : Nat} (x : BitVec n) {a b m k : Nat} (h : b + k ≤ m) :
    (x.extractLsb' a m).extractLsb' b k = x.extractLsb' (a + b) k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', hi, show b + i < m by omega, Nat.add_assoc]

/-- Rotation by one entry of `w` bits, over `n` entries. -/
def rotG {m : Nat} (n w : Nat) (x : BitVec m) : BitVec m := (x >>> w) ||| (x <<< ((n - 1) * w))

theorem rotG_entry {m n w : Nat} (hm : m = n * w) (x : BitVec m) {r : Nat} (hr : r < n) :
    (rotG n w x).extractLsb' (r * w) w = x.extractLsb' (((r + 1) % n) * w) w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e1 : (n - 1) * w + w = n * w := by rw [← Nat.succ_mul]; congr 1; omega
  simp only [rotG, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, decide_eq_true hi, Bool.true_and]
  by_cases h : r + 1 < n
  · rw [Nat.mod_eq_of_lt h]
    have h1 : (r + 1) * w ≤ (n - 1) * w := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * w + w = (r + 1) * w := (Nat.succ_mul r w).symm
    have h3 : ¬ (r * w + i < (n - 1) * w) = False := by simp; omega
    rw [show w + (r * w + i) = (r + 1) * w + i by omega]
    simp only [show r * w + i < (n - 1) * w by omega, decide_true, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.or_false]
  · have hr' : r = n - 1 := by omega
    subst hr'
    rw [show n - 1 + 1 = n by omega, Nat.mod_self, Nat.zero_mul, Nat.zero_add]
    rw [BitVec.getLsbD_of_ge x (w + ((n - 1) * w + i)) (by omega)]
    simp only [Bool.false_or, show (n - 1) * w + i < m by omega, decide_true, Bool.true_and,
      show ¬ ((n - 1) * w + i < (n - 1) * w) by omega, decide_false, Bool.not_false,
      show (n - 1) * w + i - (n - 1) * w = i by omega]

/-- `c` rotations. -/
def rotN {m : Nat} (n w : Nat) (x : BitVec m) : Nat → BitVec m
  | 0 => x
  | c + 1 => rotG n w (rotN n w x c)

theorem rotN_entry {m n w : Nat} (hm : m = n * w) (x : BitVec m) : ∀ (c : Nat) {r : Nat}, r < n →
    (rotN n w x c).extractLsb' (r * w) w = x.extractLsb' (((r + c) % n) * w) w
  | 0, r, hr => by simp [rotN, Nat.mod_eq_of_lt hr]
  | c + 1, r, hr => by
    rw [rotN, rotG_entry hm _ hr, rotN_entry hm x c (Nat.mod_lt _ (by omega)), Nat.mod_add_mod,
      show r + 1 + c = r + (c + 1) by omega]

section vals
variable (N W AccW : Nat)

/-- PMU_A after `i` row rotations. -/
def paV (A : BitVec (N * N * W)) (i : Nat) : BitVec (N * N * W) := rotN N (N * W) A i

/-- PMU_B after `c` entry rotations of every row. -/
def pbV (B : BitVec (N * N * W)) (c : Nat) : BitVec (N * (N * W)) :=
  packBV (N * W) N fun k => rotN N W (B.extractLsb' (k * (N * W)) (N * W)) c

/-- Lane `k`'s words of item `q`: `A[i][k]` and `B[k][j]`, sign-extended to `AccW` bits. -/
def vaV (A : BitVec (N * N * W)) (q : Nat) : BitVec (N * AccW) :=
  packBV AccW N fun k => BitVec.ofInt AccW (Tasks.Matmul.entry W A (q / N * N + k))
def vbV (B : BitVec (N * N * W)) (q : Nat) : BitVec (N * AccW) :=
  packBV AccW N fun k => BitVec.ofInt AccW (Tasks.Matmul.entry W B (k * N + q % N))

/-- `Σ_{k < n} f (a + k)`. -/
def sumF (f : Nat → Int) (a : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => sumF f a n + f (a + n)

/-- Lane `k`'s product of item `q` (`0` beyond lane `N - 1`). -/
def pr (A B : BitVec (N * N * W)) (q k : Nat) : Int :=
  if k < N then Tasks.Matmul.entry W A (q / N * N + k) * Tasks.Matmul.entry W B (k * N + q % N) else 0

/-- Tree node `(d, x)` of item `q`: the sum of its leaves' products. -/
def nodeV (A B : BitVec (N * N * W)) (q d x : Nat) : BitVec AccW :=
  BitVec.ofInt AccW (sumF (pr N W A B q) (x * 2 ^ (Lg N - d)) (2 ^ (Lg N - d)))

/-- Item `q`'s result. -/
def resV (A B : BitVec (N * N * W)) (q : Nat) : BitVec AccW :=
  BitVec.ofInt AccW (Tasks.Matmul.dot N W A B (q / N) (q % N))

/-- Stage `s` holds a valid item `t` cycles after the start. -/
abbrev vOK (s t : Nat) : Prop := s < t ∧ t - 1 - s < N * N

/-- The valid bits, `t` cycles after the start. -/
def vV : Nat → BitVec (Lg N + 2)
  | 0 => 0
  | t + 1 => (vV t).extractLsb' 0 (Lg N + 1) ++ BitVec.ofBool (decide (t < N * N))

/-- The last bits, `t` cycles after the start. -/
def lV : Nat → BitVec (Lg N + 2)
  | 0 => 0
  | t + 1 => (lV t).extractLsb' 0 (Lg N + 1) ++ BitVec.ofBool (decide (t + 1 = N * N))

/-- The items written into `C` after `t` cycles. -/
abbrev wC (t : Nat) : Nat := t - (Lg N + 2)

end vals

theorem sumF_add (f : Nat → Int) (a m : Nat) : ∀ n, sumF f a (m + n) = sumF f a m + sumF f (a + m) n
  | 0 => by simp [sumF]
  | n + 1 => by rw [← Nat.add_assoc, sumF, sumF_add f a m n, sumF, Int.add_assoc, Nat.add_assoc]

theorem sumF_zero (f : Nat → Int) (a : Nat) : ∀ n, (∀ k, k < n → f (a + k) = 0) → sumF f a n = 0
  | 0, _ => rfl
  | n + 1, h => by rw [sumF, sumF_zero f a n (fun k hk => h k (by omega)), h n (by omega)]; rfl

theorem sumF_foldl (f : Nat → Int) : ∀ n, sumF f 0 n = (List.range n).foldl (fun acc k => acc + f k) 0
  | 0 => rfl
  | n + 1 => by rw [sumF, sumF_foldl f n, List.range_succ, List.foldl_append]; simp

theorem vV_bit (N : Nat) : ∀ t s, s < Lg N + 2 → (vV N t).getLsbD s = decide (vOK N s t)
  | 0, s, _ => by simp [vV]
  | t + 1, s, hs => by
    rw [vV, BitVec.getLsbD_append]
    by_cases h0 : s < 1
    · obtain rfl : s = 0 := by omega
      simp [BitVec.getLsbD_ofBool]
    · rw [if_neg h0, BitVec.getLsbD_extractLsb', Nat.zero_add, vV_bit N t (s - 1) (by omega)]
      simp only [decide_eq_true_eq, show s - 1 < Lg N + 1 by omega, decide_true, Bool.true_and]
      apply decide_eq_decide.mpr; omega

theorem lV_bit (N : Nat) : ∀ t s, s < Lg N + 2 → (lV N t).getLsbD s = decide (s < t ∧ t - 1 - s + 1 = N * N)
  | 0, s, _ => by simp [lV]
  | t + 1, s, hs => by
    rw [lV, BitVec.getLsbD_append]
    by_cases h0 : s < 1
    · obtain rfl : s = 0 := by omega
      simp [BitVec.getLsbD_ofBool]
    · rw [if_neg h0, BitVec.getLsbD_extractLsb', Nat.zero_add, lV_bit N t (s - 1) (by omega)]
      simp only [decide_eq_true_eq, show s - 1 < Lg N + 1 by omega, decide_true, Bool.true_and]
      apply decide_eq_decide.mpr; omega

/-! ## 5. One busy cycle, register by register -/

theorem dm_step {N t : Nat} (hN : 0 < N) :
    (t % N + 1 = N → (t + 1) % N = 0 ∧ (t + 1) / N = t / N + 1) ∧
    (t % N + 1 ≠ N → (t + 1) % N = t % N + 1 ∧ (t + 1) / N = t / N) := by
  have hd := Nat.div_add_mod t N
  have hm := Nat.mod_lt t hN
  constructor
  · intro h
    have e : t + 1 = N * (t / N + 1) := by rw [Nat.mul_succ]; omega
    rw [e, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hN]; exact ⟨rfl, rfl⟩
  · intro h
    have e : t + 1 = (t % N + 1) + N * (t / N) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hN, Nat.mod_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega)]
    exact ⟨rfl, by omega⟩

theorem last_iff {N t : Nat} (hN : 0 < N) (ht : t < N * N) : (t / N + 1 = N ∧ t % N + 1 = N) ↔ t + 1 = N * N := by
  have hd := Nat.div_add_mod t N
  have hm := Nat.mod_lt t hN
  have hq : t / N < N := (Nat.div_lt_iff_lt_mul hN).mpr ht
  constructor
  · rintro ⟨h1, h2⟩
    have : N * N = N * (t / N) + N := by rw [show N * (t / N) + N = N * (t / N + 1) from (Nat.mul_succ _ _).symm, h1]
    omega
  · intro h
    have h1 : (t % N + 1) % N = 0 := by
      have : (t % N + 1) + N * (t / N) = N * N := by omega
      have := congrArg (· % N) this
      simp only [Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
      exact this
    have h2 : t % N + 1 = N := by
      rcases Nat.lt_or_ge (t % N + 1) N with h3 | h3
      · rw [Nat.mod_eq_of_lt h3] at h1; omega
      · omega
    refine ⟨?_, h2⟩
    have : N * (t / N + 1) = N * N := by rw [Nat.mul_succ]; omega
    exact Nat.eq_of_mul_eq_mul_left hN this

theorem ofNat32_eq_sub_one {v N : Nat} (hv : v < 2 ^ 32) (hN1 : 1 ≤ N) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 32 v = BitVec.ofNat 32 N - 1#32) ↔ v + 1 = N := by
  rw [← BitVec.toNat_inj, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem lvec_one32 : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide

theorem lvec_N32 {N : Nat} (hN : N < 2 ^ 31) : LVec.ofInt 32 (N : Int) = LVec.ofBitVec (BitVec.ofNat 32 N) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast]

theorem eqm1_known {N v : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 31) (hv : v < 2 ^ 32) :
    eqm1 N (LVec.ofBitVec (BitVec.ofNat 32 v)) = decide (v + 1 = N) := by
  simp only [eqm1, lvec_N32 hN, lvec_one32, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    condTrue_knownBit]
  exact decide_eq_decide.mpr (ofNat32_eq_sub_one hv hN1 (by omega))

/-- The pipeline `t < lat` cycles after a start with operands `A`, `B`. -/
structure BusyR (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat)
    (dn c ci cj rn pa pb va vb vl ls tr : LVec) : Prop where
  dn : dn = knownBit false
  rn : rn = knownBit (decide (t < N * N))
  ci : ci = .ofBitVec (BitVec.ofNat 32 (min t (N * N) / N))
  cj : cj = .ofBitVec (BitVec.ofNat 32 (min t (N * N) % N))
  pa : pa = .ofBitVec (paV N W A (min t (N * N) / N))
  pb : pb = .ofBitVec (pbV N W B (min t (N * N)))
  vl : vl = .ofBitVec (vV N t)
  ls : ls = .ofBitVec (lV N t)
  vaw : va.width = N * AccW
  vbw : vb.width = N * AccW
  va : vOK N 0 t → va = .ofBitVec (vaV N W AccW A (t - 1))
  vb : vOK N 0 t → vb = .ofBitVec (vbV N W AccW B (t - 1))
  trw : tr.width = 2 * Pw N * AccW
  tr : ∀ d x, d ≤ Lg N → x < 2 ^ d → vOK N (1 + Lg N - d) t →
    tr.extract ((2 ^ d - 1 + x) * AccW) AccW = .ofBitVec (nodeV N W AccW A B (t - 1 - (1 + Lg N - d)) d x)
  cw : c.width = N * N * AccW
  c : ∀ r, r < N * N → N * N - wC N t ≤ r →
    c.extract (r * AccW) AccW = .ofBitVec (resV N W AccW A B (r + wC N t - N * N))

/-- The facts about the parameters the steps use. -/
structure Rng (N W AccW : Nat) : Prop where
  hN : 1 ≤ N
  hW : 1 ≤ W
  hA : 1 ≤ AccW
  hNW : N * N * W < 2 ^ 31
  hNA : N * N * AccW < 2 ^ 31

theorem Rng.hN31 {N W AccW : Nat} (h : Rng N W AccW) : N < 2 ^ 31 := by
  have := h.hNW; have := Nat.le_mul_of_pos_right (N * N) h.hW
  have := Nat.le_mul_of_pos_right N h.hN; omega

theorem Rng.hNN31 {N W AccW : Nat} (h : Rng N W AccW) : N * N < 2 ^ 31 := by
  have := h.hNW; have := Nat.le_mul_of_pos_right (N * N) h.hW; omega

/-! ### Windows of `LVec` writes (any contents, `x` included) -/

theorem width_foldWin {n : Nat} (f : Nat → Nat) (g : Nat → LVec) (x : LVec) :
    ((List.range n).foldl (fun acc k => acc.insertAt (f k) (g k)) x).width = x.width := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append]; simp [ih]

/-- Window `r` of a family of window writes `(b + k)·w`. -/
theorem foldWin_hit {w b : Nat} {f : Nat → Nat} {g : Nat → LVec} (x : LVec) : ∀ {n : Nat},
    (∀ k, k < n → f k = (b + k) * w) → (∀ k, k < n → (g k).width = w) → (b + n) * w ≤ x.width →
    ∀ {r : Nat}, r < n → ((List.range n).foldl (fun acc k => acc.insertAt (f k) (g k)) x).extract ((b + r) * w) w = g r
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | n + 1, hf, hg, hx, r, hr => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf n (by omega)]
    have hx' : (b + n) * w + w ≤ x.width := by rw [← Nat.succ_mul]; exact hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · have := win_le (w := w) (show b + r < b + n by omega)
      rw [LVec.extract_insertAt_of_disjoint (.inl this)]
      exact foldWin_hit x (fun k hk => hf k (by omega)) (fun k hk => hg k (by omega)) (by omega) hr
    · exact LVec.extract_insertAt_self (hg r (by omega)) (by rw [width_foldWin]; exact hx')

/-- A window outside a family of window writes. -/
theorem foldWin_miss {w b : Nat} {f : Nat → Nat} {g : Nat → LVec} (x : LVec) {lo len : Nat} : ∀ {n : Nat},
    (∀ k, k < n → f k = (b + k) * w) → (∀ k, k < n → (g k).width = w) → (lo + len ≤ b * w ∨ (b + n) * w ≤ lo) →
    ((List.range n).foldl (fun acc k => acc.insertAt (f k) (g k)) x).extract lo len = x.extract lo len
  | 0, _, _, _ => rfl
  | n + 1, hf, hg, h => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hf n (by omega)]
    have h1 : b * w ≤ (b + n) * w := Nat.mul_le_mul_right _ (by omega)
    have h2 : (b + n) * w + w = (b + (n + 1)) * w := by rw [← Nat.succ_mul]; rfl
    rw [LVec.extract_insertAt_of_disjoint (by rw [hg n (by omega)]; omega)]
    exact foldWin_miss x (fun k hk => hf k (by omega)) (fun k hk => hg k (by omega))
      (by rcases h with h | h
          · exact .inl h
          · right; have := Nat.mul_le_mul_right w (show b + n ≤ b + (n + 1) by omega); omega)

/-- A window inside a written part. -/
theorem extract_insertAt_sub {v p : LVec} {lo lo' w : Nat} (h1 : lo ≤ lo') (h2 : lo' + w ≤ lo + p.width)
    (h3 : lo + p.width ≤ v.width) : (v.insertAt lo p).extract lo' w = p.extract (lo' - lo) w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, LVec.getD_insertAt, if_pos ⟨by omega, by omega⟩, if_pos (by omega),
    LVec.getD_extract, if_pos hi]
  congr 2; omega

/-- A right shift by a constant, through a window. -/
theorem extract_shr32 {v : LVec} {s lo w : Nat} (hs : s < 2 ^ 31) (h : lo + s + w ≤ v.width) :
    (v.shr (LVec.ofInt 32 (s : Int))).extract lo w = v.extract (lo + s) w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, LVec.getD_extract, if_pos hi, lvec_N32 hs]
  simp only [LVec.shr, LVec.shiftAmount?, LVec.toNat?_ofBitVec, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show s < 2 ^ 32 by omega), Array.getElem?_ofFn]
  have h1 : lo + i < v.width := by omega
  have h2 : lo + i + s < v.bits.size := by show _ < v.width; omega
  have h3 : lo + s + i < v.bits.size := by show _ < v.width; omega
  simp only [show lo + i < v.bits.size from h1, dite_true, Option.getD_some, Array.getElem?_eq_getElem h2,
    Array.getElem?_eq_getElem h3, show lo + i + s = lo + s + i by omega]
  rw [dif_pos h1]; rfl

theorem resizeU_self' {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_resizeU] at hi
  simp only [LVec.resizeU, Array.getElem?_ofFn, hi, dite_true, Option.getD_some]
  have : i < v.bits.size := by rw [← h] at hi; exact hi
  simp [Array.getElem?_eq_getElem this]

/-- A sign-extended entry, as the lanes capture it. -/
theorem lane_val {m : Nat} (AccW W lo : Nat) (hW : 1 ≤ W) (X : BitVec m) (h : lo + W ≤ m) :
    ((sxv (LVec.ofBitVec X) AccW lo W).resizeU AccW).resizeU AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (X.extractLsb' lo W).toInt) := by
  simp only [sxv, LVec.extract_ofBitVec _ (show lo + W - 1 + 1 ≤ m by omega), LVec.extract_ofBitVec _ h,
    LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec,
    LVec.ofBitVec_replicate_append_eq_signExtend hW X AccW rfl, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_signExtend_of_le _ (show AccW ≤ AccW + W by omega)]
  rfl

section busy
variable {N W AccW : Nat} {A B : BitVec (N * N * W)} {t : Nat} {dn c ci cj rn pa pb va vb vl ls tr : LVec}

/-- The busy cycle's queue: reset and `start` low, the operands applied. -/
abbrev QB (N W AccW : Nat) (A B : BitVec (N * N * W)) (dn c ci cj rn pa pb va vb vl ls tr : LVec) : NbaQueue2 :=
  Q N W AccW (knownBit false) (knownBit false) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr

attribute [local simp] condTrue_knownBit

theorem step_cc (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "cc_run" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) rn = knownBit (decide (t + 1 < N * N)) ∧
    nbaFold "cc_i" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) ci =
      .ofBitVec (BitVec.ofNat 32 (min (t + 1) (N * N) / N)) ∧
    nbaFold "cc_j" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) cj =
      .ofBitVec (BitVec.ofNat 32 (min (t + 1) (N * N) % N)) := by
  have hN := h.hN; have h31 := h.hN31; have hNN := h.hNN31
  rw [fold_rn, fold_ci, fold_cj, hB.rn, hB.ci, hB.cj]
  unfold ccQ
  by_cases ht : t < N * N
  · have hm : min t (N * N) = t := Nat.min_eq_left (by omega)
    have hd : t / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr ht
    have hmod : t % N < N := Nat.mod_lt t (by omega)
    rw [hm, eqm1_known hN h31 (by omega), eqm1_known hN h31 (by omega)]
    have hm1 : min (t + 1) (N * N) = t + 1 := Nat.min_eq_left (by omega)
    rw [hm1]
    obtain ⟨d1, d2⟩ := dm_step (t := t) (show 0 < N by omega)
    by_cases hj : t % N + 1 = N
    · obtain ⟨e1, e2⟩ := d1 hj
      have hl : t + 1 < N * N ↔ ¬ (t / N + 1 = N) := by
        have := (last_iff (show 0 < N by omega) ht); constructor
        · intro h1 h2; have := this.mp ⟨h2, hj⟩; omega
        · intro h1; rcases Nat.lt_or_ge (t + 1) (N * N) with h3 | h3
          · exact h3
          · exact absurd (this.mpr (by omega)).1 h1
      by_cases hi : t / N + 1 = N
      · simp [ht, hj, hi, nbaFold, wr, e1, e2, lvec_one32, LVec.add_ofBitVec, LVec.insertAt_zero_of_width_eq,
          BitVec.ofNat_add_ofNat, show ¬ (t + 1 < N * N) from fun h' => hl.mp h' hi, b1, LVec.resizeU_one_l0]
      · simp [ht, hj, hi, nbaFold, wr, e1, e2, lvec_one32, LVec.add_ofBitVec, LVec.insertAt_zero_of_width_eq,
          BitVec.ofNat_add_ofNat, hl.mpr hi]
    · obtain ⟨e1, e2⟩ := d2 hj
      have hl : t + 1 < N * N := by
        rcases Nat.lt_or_ge (t + 1) (N * N) with h3 | h3
        · exact h3
        · exact absurd ((last_iff (show 0 < N by omega) ht).mpr (by omega)).2 hj
      simp [ht, hj, nbaFold, wr, e1, e2, lvec_one32, LVec.add_ofBitVec, LVec.insertAt_zero_of_width_eq,
        BitVec.ofNat_add_ofNat, hl]
  · have hm : min t (N * N) = N * N := Nat.min_eq_right (by omega)
    have hm1 : min (t + 1) (N * N) = N * N := Nat.min_eq_right (by omega)
    simp [ht, hm, hm1, nbaFold, show ¬ (t + 1 < N * N) by omega]

theorem shl_ofBitVec' {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn, LVec.width_ofBitVec, hi,
    dite_true, BitVec.getLsbD_shiftLeft, LVec.getElem?_ofBitVec]
  by_cases h : i < y.toNat
  · simp [h]
  · simp [h, show i - y.toNat < w by omega, hi]

theorem bv_sub_one {N : Nat} (h1 : 1 ≤ N) (h : N < 2 ^ 32) : BitVec.ofNat 32 N - 1#32 = BitVec.ofNat 32 (N - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem bv_mul32 (a b : Nat) : BitVec.ofNat 32 a * BitVec.ofNat 32 b = BitVec.ofNat 32 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, Nat.mul_mod]

theorem toNat32 {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- PMU_A's rotation on known values. -/
theorem rotA_known (h : Rng N W AccW) (X : BitVec (N * N * W)) :
    rotA N W (LVec.ofBitVec X) = LVec.ofBitVec (rotG N (N * W) X) := by
  have h31 := h.hN31
  have hNW := h.hNW
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ h.hN
  have h2 : (N - 1) * N * W ≤ N * N * W := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  have hW31 : W < 2 ^ 31 := by have := Nat.le_mul_of_pos_left W (Nat.mul_pos h.hN h.hN); omega
  simp only [rotA, rotG, lvec_N32 h31, lvec_N32 hW31, lvec_one32, LVec.mul_ofBitVec,
    LVec.sub_ofBitVec, bv_sub_one h.hN (by omega), bv_mul32, LVec.shr_ofBitVec, shl_ofBitVec', LVec.or_ofBitVec,
    toNat32 (show N * W < 2 ^ 32 by omega), toNat32 (show (N - 1) * N * W < 2 ^ 32 by omega), Nat.mul_assoc,
    toNat32 (show (N - 1) * (N * W) < 2 ^ 32 by rw [← Nat.mul_assoc]; omega)]

/-- PMU_B's row rotation on known values. -/
theorem rotB_known (h : Rng N W AccW) (y : BitVec (N * W)) :
    rotB N W (LVec.ofBitVec y) = LVec.ofBitVec (rotG N W y) := by
  have h31 := h.hN31
  have hNW := h.hNW
  have hW31 : W < 2 ^ 31 := by have := Nat.le_mul_of_pos_left W (Nat.mul_pos h.hN h.hN); omega
  have h2 : (N - 1) * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right W (show N - 1 ≤ N * N by have := Nat.le_mul_of_pos_left N h.hN; omega); omega
  simp only [rotB, rotG, lvec_N32 h31, lvec_N32 hW31, lvec_one32, LVec.mul_ofBitVec, LVec.sub_ofBitVec,
    bv_sub_one h.hN (by omega), bv_mul32, LVec.shr_ofBitVec, shl_ofBitVec', LVec.or_ofBitVec,
    toNat32 (show W < 2 ^ 32 by omega), toNat32 (show (N - 1) * W < 2 ^ 32 by omega)]

theorem step_pa (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "pa_mem" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) pa =
      .ofBitVec (paV N W A (min (t + 1) (N * N) / N)) := by
  have hN := h.hN; have h31 := h.hN31; have hNN := h.hNN31
  rw [fold_pa, hB.rn, hB.cj, hB.pa]
  unfold paQ
  by_cases ht : t < N * N
  · have hm : min t (N * N) = t := Nat.min_eq_left (by omega)
    have hm1 : min (t + 1) (N * N) = t + 1 := Nat.min_eq_left (by omega)
    have hmod : t % N < N := Nat.mod_lt t (by omega)
    rw [hm, hm1, eqm1_known hN h31 (by omega)]
    obtain ⟨d1, d2⟩ := dm_step (t := t) (show 0 < N by omega)
    by_cases hj : t % N + 1 = N
    · obtain ⟨-, e2⟩ := d1 hj
      simp [ht, hj, nbaFold, wr, e2, rotA_known h, LVec.insertAt_zero_of_width_eq, paV, rotN]
    · obtain ⟨-, e2⟩ := d2 hj
      simp [ht, hj, nbaFold, e2]
  · have hm : min t (N * N) = N * N := Nat.min_eq_right (by omega)
    have hm1 : min (t + 1) (N * N) = N * N := Nat.min_eq_right (by omega)
    simp [ht, hm, hm1, nbaFold]

theorem foldl_congr' {α β : Type} {f g : β → α → β} : ∀ {l : List α} (x : β), (∀ k ∈ l, ∀ acc, f acc k = g acc k) →
    l.foldl f x = l.foldl g x
  | [], _, _ => rfl
  | a :: l, x, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self x]
    exact foldl_congr' _ (fun k hk acc => h k (List.mem_cons_of_mem _ hk) acc)

theorem foldl_id' {α β : Type} : ∀ (l : List α) (x : β), l.foldl (fun acc _ => acc) x = x
  | [], _ => rfl
  | _ :: l, x => foldl_id' l x

theorem pb_row {k : Nat} (B : BitVec (N * N * W)) (c : Nat) (hk : k < N) :
    (LVec.ofBitVec (pbV N W B c)).extract (k * N * W) (N * W) =
      LVec.ofBitVec (rotN N W (B.extractLsb' (k * (N * W)) (N * W)) c) := by
  unfold pbV; exact extract_ofBitVec_packBV _ hk (Nat.mul_assoc _ _ _)

theorem step_pb (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "pb_mem" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) pb =
      .ofBitVec (pbV N W B (min (t + 1) (N * N))) := by
  have hN := h.hN
  rw [fold_pb, hB.rn, hB.pb]
  by_cases ht : t < N * N
  · have hm : min t (N * N) = t := Nat.min_eq_left (by omega)
    have hm1 : min (t + 1) (N * N) = t + 1 := Nat.min_eq_left (by omega)
    rw [hm, hm1]
    rw [foldl_congr' (g := fun acc k => acc.insertAt (k * (N * W))
        (LVec.ofBitVec (rotN N W (B.extractLsb' (k * (N * W)) (N * W)) (t + 1)))) _ (fun k hk acc => by
      have hk' := List.mem_range.mp hk
      simp only [pbQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, decide_eq_true ht]
      rw [pb_row B t hk', rotB_known h, LVec.resizeU_ofBitVec,
        BitVec.setWidth_eq]
      simp [nbaFold, Nat.mul_assoc]; rfl)]
    exact LVec.insertEntries_ofBitVec (fun k => rotN N W (B.extractLsb' (k * (N * W)) (N * W)) (t + 1)) _
      (LVec.width_ofBitVec _)
  · have hm : min t (N * N) = N * N := Nat.min_eq_right (by omega)
    have hm1 : min (t + 1) (N * N) = N * N := Nat.min_eq_right (by omega)
    rw [hm, hm1, foldl_congr' (g := fun acc _ => acc) _ (fun k hk acc => by simp [pbQ, ht, nbaFold]), foldl_id']

theorem step_vl (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "pcu_vld" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) vl = .ofBitVec (vV N (t + 1)) := by
  rw [fold_vl, hB.vl, hB.rn]
  simp [ctlQ, nbaFold, wr, LVec.insertAt_zero_of_width_eq, vV]

theorem ofNat32_eq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a = BitVec.ofNat 32 b) = (a = b) := by
  apply propext; constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [toNat32 ha, toNat32 hb] at this
  · rintro rfl; rfl

theorem step_ls (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "pcu_lst" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) ls = .ofBitVec (lV N (t + 1)) := by
  have hN := h.hN; have h31 := h.hN31; have hNN := h.hNN31
  have key : (decide (min t (N * N) / N = N - 1) && decide (min t (N * N) % N = N - 1)) = decide (t + 1 = N * N) := by
    by_cases ht : t < N * N
    · rw [Nat.min_eq_left (by omega)]
      have := last_iff (show 0 < N by omega) ht
      have hm := Nat.mod_lt t (show 0 < N by omega)
      have hd : t / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr ht
      by_cases h1 : t + 1 = N * N
      · obtain ⟨a1, a2⟩ := this.mpr h1; simp [h1]; omega
      · simp only [h1, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        by_cases h2 : t / N = N - 1
        · right; intro h3; exact h1 (this.mp ⟨by omega, by omega⟩)
        · left; exact h2
    · rw [Nat.min_eq_right (by omega), Nat.mul_div_cancel _ (by omega)]
      simp only [show ¬ N = N - 1 by omega, decide_false, Bool.false_and, show ¬ (t + 1 = N * N) by omega]
  have hdm : min t (N * N) / N < 2 ^ 32 := by
    have := Nat.div_le_self (min t (N * N)) N; have := Nat.min_le_right t (N * N); omega
  have hmm : min t (N * N) % N < 2 ^ 32 := by have := Nat.mod_lt (min t (N * N)) (show 0 < N by omega); omega
  rw [fold_ls, hB.ls, hB.ci, hB.cj]
  simp [ctlQ, nbaFold, wr, LVec.insertAt_zero_of_width_eq, lV, lvec_N32 h31, lvec_one32, bv_sub_one hN (by omega),
    ofNat32_eq hdm (show N - 1 < 2 ^ 32 by omega), ofNat32_eq hmm (show N - 1 < 2 ^ 32 by omega), BitVec.ofBool_and_ofBool,
    key]

theorem step_dn (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    nbaFold "done" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) dn =
      knownBit (decide (t + 1 = lat N W AccW)) := by
  have hNN := Nat.mul_pos h.hN h.hN
  rw [fold_dn, hB.dn, hB.vl, hB.ls]
  have hb1 := vV_bit N t (Lg N + 1) (by omega)
  have hb2 := lV_bit N t (Lg N + 1) (by omega)
  unfold outQ
  simp only [LVec.extract_one_ofBitVec _ (show Lg N + 1 < Lg N + 2 by omega), hb1, hb2]
  by_cases c1 : vOK N (Lg N + 1) t
  · by_cases c2 : Lg N + 1 < t ∧ t - 1 - (Lg N + 1) + 1 = N * N
    · have e : t + 1 = lat N W AccW := by show t + 1 = N * N + Lg N + 2; omega
      simp [nbaFold, wr, c1, c2, e, b1, LVec.resizeU_one_l1, LVec.insertAt_zero_of_width_eq]
    · have e : ¬ (t + 1 = lat N W AccW) := by show ¬ (t + 1 = N * N + Lg N + 2); omega
      have c2' : ¬ (t - 1 - (Lg N + 1) + 1 = N * N) := fun h' => c2 ⟨c1.1, h'⟩
      simp [nbaFold, wr, c1, c2', e]
  · have e : ¬ (t + 1 = lat N W AccW) := by show ¬ (t + 1 = N * N + Lg N + 2); omega
    simp [nbaFold, wr, c1, e]

theorem paV_lane (A : BitVec (N * N * W)) {i k : Nat} (hi : i < N) (hk : k < N) :
    (paV N W A i).extractLsb' (k * W) W = A.extractLsb' ((i * N + k) * W) W := by
  have hkW : k * W + W ≤ N * W := win_le hk
  have e0 := xl_xl (paV N W A i) (a := 0) (b := k * W) (m := N * W) (k := W) hkW
  rw [Nat.zero_add] at e0
  have e1 := rotN_entry (Nat.mul_assoc N N W) A i (r := 0) (by omega)
  rw [Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hi] at e1
  rw [← e0, paV, e1, xl_xl _ hkW]
  congr 1
  rw [Nat.add_mul, Nat.mul_assoc]

theorem pbV_lane (B : BitVec (N * N * W)) (c : Nat) {k : Nat} (hk : k < N) :
    (pbV N W B c).extractLsb' (k * N * W) W = B.extractLsb' ((k * N + c % N) * W) W := by
  have hN : 0 < N := by omega
  have hW0 : 0 * W + W ≤ N * W := by have := win_le (w := W) hN; omega
  have e0 := xl_xl (pbV N W B c) (a := k * (N * W)) (b := 0 * W) (m := N * W) (k := W) hW0
  rw [show k * N * W = k * (N * W) + 0 * W by simp [Nat.mul_assoc], ← e0, pbV, extractLsb'_packBV _ hk,
    rotN_entry rfl _ c hN, Nat.zero_add, xl_xl _ (win_le (Nat.mod_lt c hN))]
  congr 1
  rw [Nat.add_mul, Nat.mul_assoc k N W]

theorem step_va (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr)
    (hv : vOK N 0 (t + 1)) :
    nbaFold "pcu_va" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) va = .ofBitVec (vaV N W AccW A t) := by
  have hN := h.hN
  have ht : t < N * N := by simp only [vOK] at hv; omega
  have hd : t / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr ht
  rw [fold_va, hB.pa, Nat.min_eq_left (show t ≤ N * N by omega)]
  rw [foldl_congr' (g := fun acc k => acc.insertAt (k * AccW)
      (LVec.ofBitVec (BitVec.ofInt AccW (Tasks.Matmul.entry W A (t / N * N + k))))) _ (fun k hk acc => by
    have hk' := List.mem_range.mp hk
    have hb : k * W + W ≤ N * N * W := by
      have := win_le (w := W) hk'; have := Nat.mul_le_mul_right W (Nat.le_mul_of_pos_left N h.hN); omega
    simp only [laneQ, nbaFold, List.foldl_cons, List.foldl_nil, if_pos rfl,
      show ("pcu_vb" = "pcu_va") = False by decide, if_false]
    rw [lane_val AccW W (k * W) h.hW _ hb, paV_lane A hd hk']
    rfl)]
  exact LVec.insertEntries_ofBitVec _ _ hB.vaw

theorem step_vb (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr)
    (hv : vOK N 0 (t + 1)) :
    nbaFold "pcu_vb" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) vb = .ofBitVec (vbV N W AccW B t) := by
  have hN := h.hN
  have ht : t < N * N := by simp only [vOK] at hv; omega
  rw [fold_vb, hB.pb, Nat.min_eq_left (show t ≤ N * N by omega)]
  rw [foldl_congr' (g := fun acc k => acc.insertAt (k * AccW)
      (LVec.ofBitVec (BitVec.ofInt AccW (Tasks.Matmul.entry W B (k * N + t % N))))) _ (fun k hk acc => by
    have hk' := List.mem_range.mp hk
    have hb : k * N * W + W ≤ N * (N * W) := by
      have := win_le (w := N * W) hk'; have := Nat.le_mul_of_pos_left W h.hN; rw [Nat.mul_assoc k]; omega
    simp only [laneQ, nbaFold, List.foldl_cons, List.foldl_nil, if_pos rfl,
      show ("pcu_va" = "pcu_vb") = False by decide, if_false]
    rw [lane_val AccW W (k * N * W) h.hW _ hb, pbV_lane B t hk']
    rfl)]
  exact LVec.insertEntries_ofBitVec _ _ hB.vbw

/-- A tree node's written value. -/
abbrev rvV (AccW : Nat) (tr : LVec) (h : Nat) : LVec :=
  ((tr.extract ((2 * h + 1) * AccW) AccW).add (tr.extract ((2 * h + 2) * AccW) AccW)).resizeU AccW

/-- A leaf's written value. -/
abbrev lfV (AccW : Nat) (va vb : LVec) (k : Nat) : LVec :=
  ((va.extract (k * AccW) AccW).mul (vb.extract (k * AccW) AccW)).resizeU AccW

/-- The tree's next value, as three families of window writes. -/
theorem tr_next :
    nbaFold "pcu_tr" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) tr =
      (List.range N).foldl (fun acc k => acc.insertAt ((Pw N - 1 + k) * AccW) (lfV AccW va vb k))
        ((List.range (Pw N - 1)).foldl (fun acc h => acc.insertAt ((0 + h) * AccW) (rvV AccW tr h))
          (tr.insertAt ((Pw N - 1 + N) * AccW) ((zv ((Pw N + 1 - N) * AccW)).resizeU ((Pw N + 1 - N) * AccW)))) := by
  rw [fold_tr]
  have e1 : nbaFold "pcu_tr" (ctlQ N AccW (knownBit false) (knownBit false) ci cj rn vl ls) tr =
      tr.insertAt ((Pw N - 1 + N) * AccW) ((zv ((Pw N + 1 - N) * AccW)).resizeU ((Pw N + 1 - N) * AccW)) := by
    simp only [ctlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, nbaFold, List.foldl_cons, List.foldl_nil,
      if_pos rfl, show ("pcu_vld" = "pcu_tr") = False by decide, show ("pcu_lst" = "pcu_tr") = False by decide,
      if_false]
  have e2 : ∀ X, (List.range (Pw N - 1)).foldl (fun acc h => nbaFold "pcu_tr" (redQ AccW tr h) acc) X =
      (List.range (Pw N - 1)).foldl (fun acc h => acc.insertAt ((0 + h) * AccW) (rvV AccW tr h)) X :=
    fun X => foldl_congr' _ (fun h _ acc => by simp [redQ, nbaFold])
  have e3 : ∀ Y, (List.range N).foldl (fun acc k => nbaFold "pcu_tr" (leafQ N AccW va vb k) acc) Y =
      (List.range N).foldl (fun acc k => acc.insertAt ((Pw N - 1 + k) * AccW) (lfV AccW va vb k)) Y :=
    fun Y => foldl_congr' _ (fun k _ acc => by simp [leafQ, nbaFold])
  rw [e1, e2, e3]

theorem sum_split (f : Nat → Int) (x e : Nat) :
    sumF f (x * (e + e)) (e + e) = sumF f (2 * x * e) e + sumF f ((2 * x + 1) * e) e := by
  rw [sumF_add]
  congr 2
  · rw [Nat.mul_add, Nat.mul_assoc, Nat.two_mul]
  · rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_assoc, Nat.two_mul]

theorem nodeV_leaf (A B : BitVec (N * N * W)) (q x : Nat) :
    nodeV N W AccW A B q (Lg N) x = BitVec.ofInt AccW (pr N W A B q x) := by
  simp [nodeV, sumF]

theorem nodeV_inner (A B : BitVec (N * N * W)) (q d x : Nat) (hd : d < Lg N) :
    nodeV N W AccW A B q d x = nodeV N W AccW A B q (d + 1) (2 * x) + nodeV N W AccW A B q (d + 1) (2 * x + 1) := by
  have hL : Lg N - d = Lg N - (d + 1) + 1 := by omega
  rw [nodeV, nodeV, nodeV, ← BitVec.ofInt_add, hL, Nat.pow_succ, Nat.mul_two, sum_split]

/-- The tree window of an inner node. -/
theorem tr_inner (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) {d x : Nat}
    (hdL : d < Lg N) (hx : x < 2 ^ d) (hv : vOK N (1 + Lg N - d) (t + 1)) :
    (nbaFold "pcu_tr" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) tr).extract ((2 ^ d - 1 + x) * AccW) AccW =
      .ofBitVec (nodeV N W AccW A B (t + 1 - 1 - (1 + Lg N - d)) d x) := by
  have hP0 := pw_pos N
  have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have hpd1 : 2 ^ (d + 1) ≤ Pw N := Nat.pow_le_pow_right (by decide) hdL
  have hp2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ, Nat.mul_two]
  have hh : 2 ^ d - 1 + x < Pw N - 1 := by omega
  have hlf : ∀ k, k < N → (lfV AccW va vb k).width = AccW := fun _ _ => by simp
  have hrv : ∀ k, k < Pw N - 1 → (rvV AccW tr k).width = AccW := fun _ _ => by simp
  have hwid : (0 + (Pw N - 1)) * AccW ≤ (tr.insertAt ((Pw N - 1 + N) * AccW)
      ((zv ((Pw N + 1 - N) * AccW)).resizeU ((Pw N + 1 - N) * AccW))).width := by
    rw [LVec.width_insertAt, hB.trw]; exact Nat.mul_le_mul_right _ (by omega)
  rw [tr_next, foldWin_miss _ (b := Pw N - 1) (fun _ _ => rfl) hlf (.inl (win_le (w := AccW) hh)),
    show (2 ^ d - 1 + x) * AccW = (0 + (2 ^ d - 1 + x)) * AccW by rw [Nat.zero_add],
    foldWin_hit _ (b := 0) (fun _ _ => rfl) hrv hwid hh]
  have hv' : vOK N (1 + Lg N - (d + 1)) t := by simp only [vOK] at hv ⊢; omega
  have c1 := hB.tr (d + 1) (2 * x) (by omega) (by omega) hv'
  have c2 := hB.tr (d + 1) (2 * x + 1) (by omega) (by omega) hv'
  unfold rvV
  rw [show (2 * (2 ^ d - 1 + x) + 1) * AccW = (2 ^ (d + 1) - 1 + 2 * x) * AccW by congr 1; omega,
    show (2 * (2 ^ d - 1 + x) + 2) * AccW = (2 ^ (d + 1) - 1 + (2 * x + 1)) * AccW by congr 1; omega, c1, c2,
    LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, nodeV_inner A B _ d x hdL,
    show t - 1 - (1 + Lg N - (d + 1)) = t + 1 - 1 - (1 + Lg N - d) by omega]

/-- The tree window of a leaf. -/
theorem tr_leaf (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) {x : Nat}
    (hx : x < Pw N) (hv : vOK N 1 (t + 1)) :
    (nbaFold "pcu_tr" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) tr).extract ((Pw N - 1 + x) * AccW) AccW =
      .ofBitVec (BitVec.ofInt AccW (pr N W A B (t - 1) x)) := by
  have hN := h.hN
  have hP := le_pw N
  have hlf : ∀ k, k < N → (lfV AccW va vb k).width = AccW := fun _ _ => by simp
  have hrv : ∀ k, k < Pw N - 1 → (rvV AccW tr k).width = AccW := fun _ _ => by simp
  have hw2 : 2 * Pw N * AccW = (Pw N - 1 + N) * AccW + (Pw N + 1 - N) * AccW := by
    rw [← Nat.add_mul]; congr 1; omega
  rw [tr_next]
  by_cases hxN : x < N
  · have hwid : (Pw N - 1 + N) * AccW ≤ ((List.range (Pw N - 1)).foldl
        (fun acc h => acc.insertAt ((0 + h) * AccW) (rvV AccW tr h)) (tr.insertAt ((Pw N - 1 + N) * AccW)
          ((zv ((Pw N + 1 - N) * AccW)).resizeU ((Pw N + 1 - N) * AccW)))).width := by
      rw [width_foldWin, LVec.width_insertAt, hB.trw, hw2]; omega
    rw [foldWin_hit _ (b := Pw N - 1) (fun _ _ => rfl) hlf hwid hxN]
    have hv0 : vOK N 0 t := by simp only [vOK] at hv ⊢; omega
    rw [lfV, hB.va hv0, hB.vb hv0, vaV, vbV, extract_ofBitVec_packBV _ hxN rfl, extract_ofBitVec_packBV _ hxN rfl,
      LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, ← BitVec.ofInt_mul, pr, if_pos hxN]
  · have h1 : (Pw N - 1 + N) * AccW ≤ (Pw N - 1 + x) * AccW := Nat.mul_le_mul_right _ (by omega)
    have h2 : (0 + (Pw N - 1)) * AccW ≤ (Pw N - 1 + x) * AccW := Nat.mul_le_mul_right _ (by omega)
    have h3 : (Pw N - 1 + x) * AccW + AccW ≤ (Pw N - 1 + N) * AccW + (Pw N + 1 - N) * AccW := by
      rw [← Nat.succ_mul, ← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    rw [foldWin_miss _ (b := Pw N - 1) (fun _ _ => rfl) hlf (.inr h1),
      foldWin_miss _ (b := 0) (fun _ _ => rfl) hrv (.inr h2),
      extract_insertAt_sub h1 (by rw [LVec.width_resizeU]; exact h3)
        (by rw [LVec.width_resizeU, hB.trw, hw2]; exact Nat.le_refl _)]
    simp only [zv, LVec.replicate_l0, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [LVec.extract_ofBitVec _ (by omega), pr, if_neg hxN]
    congr 1
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp

theorem step_tr (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr) :
    ∀ d x, d ≤ Lg N → x < 2 ^ d → vOK N (1 + Lg N - d) (t + 1) →
      (nbaFold "pcu_tr" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) tr).extract ((2 ^ d - 1 + x) * AccW) AccW =
        .ofBitVec (nodeV N W AccW A B (t + 1 - 1 - (1 + Lg N - d)) d x) := by
  intro d x hd hx hv
  by_cases hdL : d < Lg N
  · exact tr_inner h hB hdL hx hv
  · obtain rfl : d = Lg N := by omega
    rw [nodeV_leaf, show t + 1 - 1 - (1 + Lg N - Lg N) = t - 1 by omega]
    exact tr_leaf h hB hx (by simpa using hv)

theorem nodeV_root (A B : BitVec (N * N * W)) (q : Nat) : nodeV N W AccW A B q 0 0 = resV N W AccW A B q := by
  unfold nodeV resV
  congr 1
  have hP := le_pw N
  rw [Nat.zero_mul, Nat.sub_zero, show 2 ^ Lg N = N + (Pw N - N) from (Nat.add_sub_cancel' hP).symm, sumF_add,
    sumF_zero (pr N W A B q) (0 + N) (Pw N - N) (fun k _ => by unfold pr; rw [if_neg (by omega)]), Int.add_zero,
    sumF_foldl]
  unfold Tasks.Matmul.dot
  exact foldl_congr' _ (fun k hk acc => by unfold pr; rw [if_pos (List.mem_range.mp hk)])

theorem width_shr' (v a : LVec) : (v.shr a).width = v.width := by
  unfold LVec.shr; split <;> simp [LVec.width, LVec.xVec, LVec.replicate]

theorem step_c (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr)
    (ht : t + 1 ≤ lat N W AccW) :
    ∀ r, r < N * N → N * N - wC N (t + 1) ≤ r →
      (nbaFold "C" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) c).extract (r * AccW) AccW =
        .ofBitVec (resV N W AccW A B (r + wC N (t + 1) - N * N)) := by
  intro r hr hw
  have hNN := Nat.mul_pos h.hN h.hN
  have ht' : t + 1 ≤ N * N + Lg N + 2 := ht
  have hA31 : AccW < 2 ^ 31 := by have := h.hNA; have := Nat.le_mul_of_pos_left AccW hNN; omega
  have hc1 : ((LVec.ofBitVec (vV N t)).extract (Lg N + 1) 1).condTrue = decide (vOK N (Lg N + 1) t) := by
    rw [LVec.extract_one_ofBitVec _ (by omega)]
    exact (condTrue_knownBit _).trans (vV_bit N t (Lg N + 1) (by omega))
  rw [fold_c, hB.vl]
  unfold outQ
  rw [if_neg (by simp), if_neg (by simp), hc1]
  by_cases c1 : vOK N (Lg N + 1) t
  · have hw1 : wC N (t + 1) = wC N t + 1 := by simp only [wC]; simp only [vOK] at c1; omega
    have e0 : c.insertAt 0 ((c.shr (LVec.ofInt 32 ↑AccW)).resizeU c.width) = c.shr (LVec.ofInt 32 ↑AccW) := by
      rw [LVec.insertAt_zero_of_width_eq (by simp), resizeU_self' (width_shr' _ _)]
    have e : ∀ (p : Prop) [Decidable p], nbaFold "C" (wr "C" c (c.shr (LVec.ofInt 32 ↑AccW)) ::
        ("C", (N * N - 1) * AccW, (tr.extract 0 AccW).resizeU AccW) :: (if p then [wr "done" dn (b1 true)] else []))
        c = (c.shr (LVec.ofInt 32 ↑AccW)).insertAt ((N * N - 1) * AccW) ((tr.extract 0 AccW).resizeU AccW) := by
      intro p _; split <;> simp [nbaFold, wr, e0]
    rw [if_pos (decide_eq_true c1), e]
    have hcw : (c.shr (LVec.ofInt 32 ↑AccW)).width = N * N * AccW := by rw [width_shr', hB.cw]
    by_cases hr1 : r = N * N - 1
    · have hr' : r * AccW = (N * N - 1) * AccW := by rw [hr1]
      have hb : (N * N - 1) * AccW + AccW ≤ (c.shr (LVec.ofInt 32 ↑AccW)).width := by
        rw [hcw, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      rw [hr', LVec.extract_insertAt_self (p := (tr.extract 0 AccW).resizeU AccW) (LVec.width_resizeU _ _) hb,
        resizeU_self' (LVec.width_extract _ _ _)]
      have h0 : vOK N (1 + Lg N - 0) t := by simp only [vOK] at c1 ⊢; omega
      have h00 := hB.tr 0 0 (Nat.zero_le _) (Nat.two_pow_pos 0) h0
      rw [show (2 ^ 0 - 1 + 0) * AccW = 0 by simp] at h00
      have e2 : t - 1 - (1 + Lg N - 0) = N * N - 1 + (wC N t + 1) - N * N := by
        simp only [wC]; simp only [vOK] at c1; omega
      rw [h00, nodeV_root, hw1, hr1, e2]
    · have hr2 : r + 1 < N * N := by omega
      rw [LVec.extract_insertAt_of_disjoint (.inl (win_le (show r < N * N - 1 by omega))),
        extract_shr32 hA31 (by rw [hB.cw, ← Nat.succ_mul, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)),
        show r * AccW + AccW = (r + 1) * AccW from (Nat.succ_mul r AccW).symm,
        hB.c (r + 1) hr2 (by omega), hw1, show r + 1 + wC N t - N * N = r + (wC N t + 1) - N * N by omega]
  · have hw0 : wC N (t + 1) = 0 := by simp only [wC]; simp only [vOK] at c1; omega
    rw [hw0] at hw; omega

end busy

/-! ## 6. The next state of each kind of cycle -/

/-- **The commit of a cycle, register by register.** -/
theorem next_eq (N W AccW : Nat) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec) :
    mmNext N W AccW ck r s a b dn c ci cj rn pa pb va vb vl ls tr =
      MS ck r s a b (nbaFold "done" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) dn)
        (nbaFold "C" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) c)
        (nbaFold "cc_i" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) ci)
        (nbaFold "cc_j" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) cj)
        (nbaFold "cc_run" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) rn)
        (nbaFold "pa_mem" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) pa)
        (nbaFold "pb_mem" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) pb)
        (nbaFold "pcu_va" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) va)
        (nbaFold "pcu_vb" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) vb)
        (nbaFold "pcu_vld" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) vl)
        (nbaFold "pcu_lst" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) ls)
        (nbaFold "pcu_tr" (Q N W AccW r s a b dn c ci cj rn pa pb va vb vl ls tr) tr) :=
  commit_MS _ _ _ _ _ _ _ _ _ _ _ _ _ Q_names

/-- A register of `n` windows is the packed vector of its windows. -/
theorem eq_of_windows {v : LVec} {W n : Nat} {f : Nat → BitVec W} (hw : v.width = n * W)
    (h : ∀ r, r < n → v.extract (r * W) W = .ofBitVec (f r)) : v = .ofBitVec (packBV W n f) := by
  rw [← LVec.insertEntries_ofBitVec f v hw]
  have key : ∀ m, m ≤ n → LVec.insertEntries W (fun r => .ofBitVec (f r)) m v = v := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; rw [LVec.insertEntries_succ, ih (by omega), ← h m (by omega), LVec.insertAt_extract_self]
  exact (key n (Nat.le_refl _)).symm

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem vV_lat (N W AccW : Nat) (hN : 1 ≤ N) : vV N (lat N W AccW) = 0#(Lg N + 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [vV_bit N _ i hi]
  simp only [BitVec.getLsbD_zero, decide_eq_false_iff_not, vOK]
  show ¬ (i < N * N + Lg N + 2 ∧ N * N + Lg N + 2 - 1 - i < N * N)
  omega

theorem zero_concat_zero (L : Nat) :
    ((0#(L + 2)).extractLsb' 0 (L + 1) ++ BitVec.ofBool false : BitVec (L + 2)) = 0#(L + 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_append, BitVec.getLsbD_ofBool]

/-- The register widths. -/
def Wd (N W AccW : Nat) (dn c ci cj rn pa pb va vb vl ls tr : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ ci.width = 32 ∧ cj.width = 32 ∧ rn.width = 1 ∧ pa.width = N * N * W ∧
    pb.width = N * N * W ∧ va.width = N * AccW ∧ vb.width = N * AccW ∧ vl.width = Lg N + 2 ∧ ls.width = Lg N + 2 ∧
    tr.width = 2 * Pw N * AccW

section steps
variable {N W AccW : Nat} {A B : BitVec (N * N * W)} {t : Nat} {dn c ci cj rn pa pb va vb vl ls tr : LVec}

attribute [local simp] condTrue_knownBit

/-- **A busy cycle** before the last one: the pipeline one cycle on. -/
theorem busy_next (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr)
    (ht : t + 1 < lat N W AccW) :
    BusyR N W AccW A B (t + 1)
      (nbaFold "done" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) dn)
      (nbaFold "C" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) c)
      (nbaFold "cc_i" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) ci)
      (nbaFold "cc_j" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) cj)
      (nbaFold "cc_run" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) rn)
      (nbaFold "pa_mem" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) pa)
      (nbaFold "pb_mem" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) pb)
      (nbaFold "pcu_va" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) va)
      (nbaFold "pcu_vb" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) vb)
      (nbaFold "pcu_vld" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) vl)
      (nbaFold "pcu_lst" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) ls)
      (nbaFold "pcu_tr" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) tr) := by
  obtain ⟨hrn, hci, hcj⟩ := step_cc h hB
  exact {
    dn := by rw [step_dn h hB, decide_eq_false (by omega)]
    rn := hrn
    ci := hci
    cj := hcj
    pa := step_pa h hB
    pb := step_pb h hB
    vl := step_vl hB
    ls := step_ls h hB
    vaw := by rw [width_nbaFold, hB.vaw]
    vbw := by rw [width_nbaFold, hB.vbw]
    va := fun hv => by rw [step_va h hB hv, Nat.add_sub_cancel]
    vb := fun hv => by rw [step_vb h hB hv, Nat.add_sub_cancel]
    trw := by rw [width_nbaFold, hB.trw]
    tr := step_tr h hB
    cw := by rw [width_nbaFold, hB.cw]
    c := step_c h hB (by omega) }

/-- **The last busy cycle**: `done` rises with the product in `C`, nothing valid is left. -/
theorem busy_last (h : Rng N W AccW) (hB : BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr)
    (ht : t + 1 = lat N W AccW) :
    nbaFold "done" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) dn = knownBit true ∧
    nbaFold "C" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) c =
      .ofBitVec (Tasks.Matmul.product N W AccW A B) ∧
    nbaFold "cc_run" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) rn = knownBit false ∧
    nbaFold "pcu_vld" (QB N W AccW A B dn c ci cj rn pa pb va vb vl ls tr) vl = .ofBitVec 0#(Lg N + 2) := by
  have ht' : t + 1 = N * N + Lg N + 2 := ht
  refine ⟨by rw [step_dn h hB, decide_eq_true ht], ?_, by rw [(step_cc h hB).1, decide_eq_false (by omega)],
    by rw [step_vl hB, ht, vV_lat N W AccW h.hN]⟩
  have hw : wC N (t + 1) = N * N := by simp only [wC]; omega
  rw [product_eq]
  apply eq_of_windows (by rw [width_nbaFold, hB.cw])
  intro r hr
  rw [step_c h hB (by omega) r hr (by omega), hw, Nat.add_sub_cancel]
  rfl

/-- **A start cycle** from any state of the shape: the pipeline at `t = 0`. -/
theorem start_next (h : Rng N W AccW) (hw : Wd N W AccW dn c ci cj rn pa pb va vb vl ls tr) :
    BusyR N W AccW A B 0
      (nbaFold "done" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) dn)
      (nbaFold "C" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) c)
      (nbaFold "cc_i" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) ci)
      (nbaFold "cc_j" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) cj)
      (nbaFold "cc_run" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) rn)
      (nbaFold "pa_mem" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) pa)
      (nbaFold "pb_mem" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) pb)
      (nbaFold "pcu_va" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) va)
      (nbaFold "pcu_vb" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) vb)
      (nbaFold "pcu_vld" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) vl)
      (nbaFold "pcu_lst" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) ls)
      (nbaFold "pcu_tr" (Q N W AccW (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c ci cj rn pa pb va vb vl ls tr) tr) := by
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := hw
  have hN := h.hN
  have hNN := Nat.mul_pos h.hN h.hN
  exact {
    dn := by rw [fold_dn]; simp [outQ, nbaFold, wr, w1, b1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    rn := by
      rw [fold_rn]; simp [ccQ, nbaFold, wr, w5, b1, LVec.resizeU_one_l1, LVec.insertAt_zero_of_width_eq, hNN]
    ci := by rw [fold_ci]; simp [ccQ, nbaFold, wr, w3, LVec.insertAt_zero_of_width_eq]
    cj := by rw [fold_cj]; simp [ccQ, nbaFold, wr, w4, LVec.insertAt_zero_of_width_eq]
    pa := by
      rw [fold_pa]; simp [paQ, nbaFold, wr, w6, LVec.insertAt_zero_of_width_eq, paV, rotN]
    pb := by
      rw [fold_pb, foldl_congr' (g := fun acc k => acc.insertAt (k * (N * W))
          (LVec.ofBitVec (rotN N W (B.extractLsb' (k * (N * W)) (N * W)) 0))) _ (fun k hk acc => by
        have hk' := List.mem_range.mp hk
        have hb : k * N * W + N * W ≤ N * N * W := by
          rw [Nat.mul_assoc k, Nat.mul_assoc N]; exact win_le hk'
        simp only [pbQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte]
        rw [LVec.extract_ofBitVec _ hb, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
        simp [nbaFold, Nat.mul_assoc, rotN])]
      exact LVec.insertEntries_ofBitVec _ _ (by rw [w7, Nat.mul_assoc])
    vl := by rw [fold_vl]; simp [ctlQ, nbaFold, wr, w10, LVec.insertAt_zero_of_width_eq, vV]
    ls := by rw [fold_ls]; simp [ctlQ, nbaFold, wr, w11, LVec.insertAt_zero_of_width_eq, lV]
    vaw := by rw [width_nbaFold, w8]
    vbw := by rw [width_nbaFold, w9]
    va := fun hv => absurd hv (by simp [vOK])
    vb := fun hv => absurd hv (by simp [vOK])
    trw := by rw [width_nbaFold, w12]
    tr := fun _ _ _ _ hv => absurd hv (by simp [vOK])
    cw := by rw [width_nbaFold, w2]
    c := fun r hr hw' => absurd hw' (by simp only [wC]; omega) }

/-- **An idle cycle** (reset and `start` low) with nothing running: `done`, `C` and the control stay. -/
theorem idle_next :
    let q := Q N W AccW (knownBit false) (knownBit false) a b dn c ci cj (knownBit false) pa pb va vb
      (.ofBitVec 0#(Lg N + 2)) ls tr
    nbaFold "done" q dn = dn ∧ nbaFold "C" q c = c ∧ nbaFold "cc_i" q ci = ci ∧ nbaFold "cc_j" q cj = cj ∧
      nbaFold "cc_run" q (knownBit false) = knownBit false ∧
      nbaFold "pcu_vld" q (.ofBitVec 0#(Lg N + 2)) = .ofBitVec 0#(Lg N + 2) := by
  intro q
  have hz : ((LVec.ofBitVec 0#(Lg N + 2)).extract (Lg N + 1) 1).condTrue = false := by
    rw [LVec.extract_one_ofBitVec _ (by omega)]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fold_dn]; simp [outQ, hz, nbaFold]
  · rw [fold_c]; simp [outQ, hz, nbaFold]
  · rw [fold_ci]; simp [ccQ, nbaFold]
  · rw [fold_cj]; simp [ccQ, nbaFold]
  · rw [fold_rn]; simp [ccQ, nbaFold]
  · rw [fold_vl]
    simp only [ctlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, nbaFold, List.foldl_cons, List.foldl_nil,
      show ("pcu_tr" = "pcu_vld") = False by decide, show ("pcu_lst" = "pcu_vld") = False by decide, if_false,
      if_pos rfl]
    rw [LVec.extract_ofBitVec _ (by omega), LVec.concatMany_cons_cons, LVec.concatMany_singleton,
      LVec.concat_ofBitVec, LVec.width_ofBitVec, LVec.resizeU_ofBitVec, LVec.insertAt_zero_of_width_eq (by simp)]
    congr 1
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_append, BitVec.getLsbD_ofBool]

/-- **A reset cycle** from any state of the shape: `done`, `cc_run` and the valid bits cleared. -/
theorem reset_next (hw : Wd N W AccW dn c ci cj rn pa pb va vb vl ls tr) :
    let q := Q N W AccW (knownBit true) s a b dn c ci cj rn pa pb va vb vl ls tr
    nbaFold "done" q dn = knownBit false ∧ nbaFold "cc_run" q rn = knownBit false ∧
      nbaFold "pcu_vld" q vl = .ofBitVec 0#(Lg N + 2) := by
  intro q
  obtain ⟨w1, -, -, -, w5, -, -, -, -, w10, -, -⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · rw [fold_dn]; simp [outQ, nbaFold, wr, w1, b1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
  · rw [fold_rn]; simp [ccQ, nbaFold, wr, w5, b1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
  · rw [fold_vl]; simp [ctlQ, nbaFold, wr, w10, LVec.insertAt_zero_of_width_eq]

end steps

/-! ## 7. Shape and termination -/

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c ci cj rn pa pb va vb vl ls tr, st = MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr ∧
    Wd N W AccW dn c ci cj rn pa pb va vb vl ls tr

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c ci cj rn pa pb va vb vl ls tr : LVec)
    (hw : Wd N W AccW dn c ci cj rn pa pb va vb vl ls tr) :
    I N W AccW (mmNext N W AccW ck r s a b dn c ci cj rn pa pb va vb vl ls tr) := by
  rw [next_eq]
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ := hw
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, genPs, pbPs, redPs, lanePs, ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, nb, List.any_flatMap,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (h : Rng N W AccW) : I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec (N * AccW), .xVec (N * AccW),
    .xVec (Lg N + 2), .xVec (Lg N + 2), .xVec (2 * Pw N * AccW), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c ci cj rn pa pb va vb vl ls tr, prev = MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr ∧
    Wd N W AccW dn c ci cj rn pa pb va vb vl ls tr ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
      dn c ci cj rn pa pb va vb vl ls tr

theorem MS_inj {ck r s a b dn c ci cj rn pa pb va vb vl ls tr ck' r' s' a' b' dn' c' ci' cj' rn' pa' pb' va' vb' vl' ls'
    tr' : LVec}
    (h : MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr = MS ck' r' s' a' b' dn' c' ci' cj' rn' pa' pb' va' vb' vl' ls' tr') :
    dn = dn' ∧ c = c' ∧ ci = ci' ∧ cj = cj' ∧ rn = rn' ∧ pa = pa' ∧ pb = pb' ∧ va = va' ∧ vb = vb' ∧ vl = vl' ∧
      ls = ls' ∧ tr = tr' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- The pipeline `t` busy cycles after a start with operands `A`, `B`. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c ci cj rn pa pb va vb vl ls tr, st = MS ck r s a b dn c ci cj rn pa pb va vb vl ls tr ∧
    BusyR N W AccW A B t dn c ci cj rn pa pb va vb vl ls tr

theorem lat_pos (N W AccW : Nat) : 1 ≤ lat N W AccW := by unfold lat; omega

/-- **The phase model** at `(N, W, AccW)`: `Ready` after a reset, `Busy x m` the pipeline `t = lat - 1 - m` cycles
after a start, `Fin x` the product shown with nothing running. -/
def model (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (lat N W AccW) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW h
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW h.hN h.hW h.hA h.hNW σ e ck r s a b dn c ci cj rn pa pb va vb vl ls tr k 40
        (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c ci cj rn pa pb va vb vl ls tr hw
  Ready st := ∃ ck r s a b c ci cj pa pb va vb ls tr,
    st = MS ck r s a b (knownBit false) c ci cj (knownBit false) pa pb va vb (.ofBitVec 0#(Lg N + 2)) ls tr
  Busy x m st := ∃ t, t + m + 1 = lat N W AccW ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := ∃ ck r s a b ci cj pa pb va vb ls tr,
    st = MS ck r s a b (knownBit true) (.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) ci cj (knownBit false)
      pa pb va vb (.ofBitVec 0#(Lg N + 2)) ls tr
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, ci, cj, pa, pb, va, vb, ls, tr, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, hB⟩
    rw [hB.dn]
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, ci, cj, pa, pb, va, vb, ls, tr, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r, next_eq]
    obtain ⟨h1, h2, h3⟩ := reset_next (s := appIn e "start" s) (a := appIn e "A" a) (b := appIn e "B" b) hw
    rw [h1, h2, h3]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb, next_eq]
    exact .inr ⟨lat N W AccW - 1, by have := lat_pos N W AccW; omega, 0, by have := lat_pos N W AccW; omega,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, start_next h hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', dn', c', ci', cj', rn', pa', pb', va', vb', vl', ls', tr', hst, hB⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hst
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, ha, hb, next_eq]
    by_cases hf : t + 1 = lat N W AccW
    · left
      obtain ⟨e1, e2, e3, e4⟩ := busy_last h hB hf
      rw [e1, e2, e3, e4]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    · right
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        busy_next h hB (by omega)⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', ci', cj', pa', pb', va', vb', ls', tr', hst⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hst
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_eq]
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := idle_next (N := N) (W := W) (AccW := AccW) (a := appIn e "A" a)
      (b := appIn e "B" b) (dn := knownBit false) (c := c) (ci := ci) (cj := cj) (pa := pa) (pb := pb)
      (va := va) (vb := vb) (ls := ls) (tr := tr)
    rw [e1, e2, e3, e4, e5, e6]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', ci', cj', pa', pb', va', vb', ls', tr', hst⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hst
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_eq]
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := idle_next (N := N) (W := W) (AccW := AccW) (a := appIn e "A" a)
      (b := appIn e "B" b) (dn := knownBit true) (c := .ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      (ci := ci) (cj := cj) (pa := pa) (pb := pb) (va := va) (vb := vb) (ls := ls) (tr := tr)
    rw [e1, e2, e3, e4, e5, e6]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-! ## 8. txtask-v2: interface, discipline, every power-up (rule 2), Moore outputs (rule 1), no x-creating
construct (rule 3), then the statement -/

theorem mm_interface (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "cc_i", "cc_j", "cc_run", "pa_mem", "pb_mem", "pcu_va",
      "pcu_vb", "pcu_vld", "pcu_lst", "pcu_tr"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (h : Rng N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by rwa [← mmD_procs]
  rcases mm_mem hm with rfl | rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩ <;>
    simp [Tasks.Matmul.task, ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, sext, nb, c32, edgeClock, asyncReset,
      processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

/-- **Rule 1.** -/
theorem mm_moore (N W AccW : Nat) (h : Rng N W AccW) : MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW h.hN)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem mm_powerUp (N W AccW : Nat) (h : Rng N W AccW) (st : SvState)
    (hp : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW] at hp
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp hp
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨ci, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨cj, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨rn, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨pa, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨pb, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨va, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨vb, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨vl, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain ⟨ls, r16, rfl, w16, -, h16⟩ := powerUp_cons.mp h15
  obtain ⟨tr, r17, rfl, w17, -, h17⟩ := powerUp_cons.mp h16
  obtain rfl := powerUp_nil.mp h17
  exact ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17⟩

/-- **Termination from every power-up** (the cycle of `mm_cycle`). -/
theorem mm_terminatesPU (N W AccW : Nat) (h : Rng N W AccW) : TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW h) (fun σ => ⟨40, ?_⟩)
    (by rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, ci, cj, rn, pa, pb, va, vb, vl, ls, tr, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW h.hN h.hW h.hA h.hNW σ e ck r s a b dn c ci cj rn pa pb va vb vl ls tr kk 40
    (Nat.le_refl _), mmNext_I N W AccW _ _ _ _ _ dn c ci cj rn pa pb va vb vl ls tr hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

macro "xs_simp" : tactic => `(tactic| simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW,
  sigWidth, ccP, paP, ctlP, outP, pbP, redP, laneP, leafP, sext, nb, c32, b1, zv, mmD, mmDecls, lvec_l0_known,
  lvec_l1_known, LVec.replicate_l0, LVec.ofInt, *])

theorem cc_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (ccP N) = true := by xs_simp
theorem pa_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (paP N W) = true := by xs_simp

theorem ctl_xsafe (N W AccW : Nat) (h : Rng N W AccW) : xsProc (mmD N W AccW) (ctlP N AccW) = true := by
  have hP := le_pw N
  have hP0 := pw_pos N
  have h1 : (Pw N - 1 + N) * AccW + (Pw N + 1 - N) * AccW ≤ 2 * Pw N * AccW := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right AccW (show Pw N - 1 + N + (Pw N + 1 - N) ≤ 2 * Pw N by omega)
  have h2 : Lg N + 1 ≤ Lg N + 2 := by omega
  xs_simp

theorem out_xsafe (N W AccW : Nat) (h : Rng N W AccW) : xsProc (mmD N W AccW) (outP N AccW) = true := by
  have hP := pw_pos N
  have h1 : AccW ≤ 2 * Pw N * AccW := Nat.le_mul_of_pos_left _ (by omega)
  have h2 : Lg N + 1 + 1 ≤ Lg N + 2 := by omega
  xs_simp

theorem pb_xsafe {N W AccW k : Nat} (hk : k < N) : xsProc (mmD N W AccW) (pbP N W k) = true := by
  have h1 : k * N * W + N * W ≤ N * N * W := by rw [Nat.mul_assoc k, Nat.mul_assoc N]; exact win_le hk
  xs_simp

theorem red_xsafe {N W AccW h : Nat} (hh : h < Pw N - 1) : xsProc (mmD N W AccW) (redP AccW h) = true := by
  have h1 : (2 * h + 1) * AccW + AccW ≤ 2 * Pw N * AccW := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  have h2 : (2 * h + 2) * AccW + AccW ≤ 2 * Pw N * AccW := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  xs_simp

theorem lane_xsafe {N W AccW k : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hk : k < N) :
    xsProc (mmD N W AccW) (laneP N W AccW k) = true := by
  have h0 : k * AccW + AccW ≤ N * AccW := win_le hk
  have h1 : k * W + W ≤ N * N * W := by
    have := win_le (w := W) hk; have := Nat.mul_le_mul_right W (Nat.le_mul_of_pos_left N hN); omega
  have h2 : k * N * W + W ≤ N * N * W := by
    have := win_le (w := N * W) hk; rw [Nat.mul_assoc k, Nat.mul_assoc N]; have := Nat.le_mul_of_pos_left W hN; omega
  have h3 : k * W + W - 1 + 1 ≤ N * N * W := by omega
  have h4 : k * N * W + W - 1 + 1 ≤ N * N * W := by omega
  xs_simp

theorem leaf_xsafe {N W AccW k : Nat} (hk : k < N) : xsProc (mmD N W AccW) (leafP N AccW k) = true := by
  have hP := le_pw N
  have h0 : k * AccW + AccW ≤ N * AccW := win_le hk
  have h1 : (Pw N - 1 + k) * AccW + AccW ≤ 2 * Pw N * AccW := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  xs_simp

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (h : Rng N W AccW) : XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW h.hN h.hW h.hA h.hNW]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ ccP N :: paP N W :: ctlP N AccW :: outP N AccW :: genPs N W AccW := by rwa [← mmD_procs]
  simp only [genPs, pbPs, redPs, lanePs, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_range, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | ((⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl | rfl⟩)
  · exact cc_xsafe N W AccW
  · exact pa_xsafe N W AccW
  · exact ctl_xsafe N W AccW h
  · exact out_xsafe N W AccW h
  · exact pb_xsafe hk
  · exact red_xsafe hk
  · exact lane_xsafe h.hN h.hW hk
  · exact leaf_xsafe hk

/-- **The spatial pipeline satisfies the matmul statement (txtask-v2) at latency `N² + clog2 N + 2`** (`20` at
the scoring point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, hNA⟩ := hp
  have h : Rng N W AccW := ⟨hN, hW, hA, hNW, hNA⟩
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW h) (mm_disciplined N W AccW h)
    (mm_terminatesPU N W AccW h) (lat_pos N W AccW) (model N W AccW h) (mm_powerUp N W AccW h) (mm_moore N W AccW h)
    (mm_xsafe N W AccW h)

end Submission
