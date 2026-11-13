-- svgolf-latency: 4
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
# matmul by one level of Strassen's scheme: seven block products of size `H = ⌈N/2⌉`

`solution.sv` (flip-flops only): `start` captures `A`, `B` into the shift registers `a_sh`, `b_sh`; busy edge
`t` loads the ten pre-sums of column `t` into `S`, `T` (seven lanes each), clears (`t = 0`) or accumulates the
seven engines `M` (lane `r` of cell `(u, v)` adds `S_r[u] · T_r[v]`), and at `t = H + 1` writes the four post-sums
into `C` and raises `done`: `lat = H + 2`. Proved at every in-range `(N, W, AccW)`:
1. agreement (`st_sem_eq`): the loaded family is the hand-built `stD`;
2. the clock step (`st_profile`, `st_cycle`);
3. the invariant on `t` (`next_step`), with the pre-sums exact in `W + 1` bits and the engines wrapping at `AccW`;
4. the arithmetic: Strassen's identities per contraction index, the padded sum equals the task's `dot`;
5. the phase model and txtask-v2's three rules, then `solution`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `⌈N/2⌉ + 2` snapshots after the start's. -/
def lat (N _W _AccW : Nat) : Nat := (N + 1) / 2 + 2

/-! ## 1. The hand-built design -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- `{x[p*W + W-1], x[p*W +: W]}`: entry `p` sign-extended by one bit. -/
def sx1 (x : String) (W p : Nat) : Expr2 :=
  .concat #[.slice (.ident x) (p * W + W - 1) 1, .slice (.ident x) (p * W) W]

/-- `{{AccW{x[b]}}, x[lo +: w]}`: the `w`-bit entry at `lo`, its top bit `b` replicated `AccW` times. -/
def sxA (x : String) (AccW b lo w : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) b 1]), .slice (.ident x) lo w]

/-- The control: `busy`, `done`, the step counter `t`, the operand shift registers. -/
def ctrlP (N W H : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "t" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "a_sh") (.resize ((2 * H + 1) * N * W) (.ident "A")),
        .nbaAssign (.ident "b_sh") (.resize ((2 * H + 1) * N * W) (.ident "B"))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "t") (.binary .add (.ident "t") (c32 1)),
          .nbaAssign (.ident "a_sh") (.binary (.shr false) (.ident "a_sh") (c32 W)),
          .nbaAssign (.ident "b_sh") (.binary (.shr false) (.ident "b_sh") (.binary .mul (c32 N) (c32 W))),
          .ifStmt (.binary .eq (.ident "t") (.binary .add (c32 H) (c32 1)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The A-side pre-sum of lane `r` (`S_{r+1}`) from the four block heads. -/
def preE (r : Nat) (x11 x12 x21 x22 : Expr2) : Expr2 :=
  match r with
  | 0 => .binary .add x11 x22
  | 1 => .binary .add x21 x22
  | 2 => x11
  | 3 => x22
  | 4 => .binary .add x11 x12
  | 5 => .binary .sub x21 x11
  | _ => .binary .sub x12 x22

/-- The B-side pre-sum of lane `r` (`T_{r+1}`) from the four block heads. -/
def preF (r : Nat) (y11 y12 y21 y22 : Expr2) : Expr2 :=
  match r with
  | 0 => .binary .add y11 y22
  | 1 => y11
  | 2 => .binary .sub y12 y22
  | 3 => .binary .sub y21 y11
  | 4 => y22
  | 5 => .binary .add y11 y12
  | _ => .binary .add y21 y22

/-- Lane `r` of the A-side pre-sums of row `u`. -/
def wS (N W H u r : Nat) : Stmt2 :=
  .nbaAssign (.slice "S" ((u * 7 + r) * (W + 1)) (W + 1))
    (preE r (sx1 "a_sh" W (u * N)) (sx1 "a_sh" W (u * N + H)) (sx1 "a_sh" W ((H + u) * N))
      (sx1 "a_sh" W ((H + u) * N + H)))

/-- Lane `r` of the B-side pre-sums of column `v`. -/
def wT (N W H v r : Nat) : Stmt2 :=
  .nbaAssign (.slice "T" ((v * 7 + r) * (W + 1)) (W + 1))
    (preF r (sx1 "b_sh" W v) (sx1 "b_sh" W (H + v)) (sx1 "b_sh" W (H * N + v)) (sx1 "b_sh" W (H * N + H + v)))

/-- The A-side pre-sums of row `u`. -/
def saP (N W H u : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.block #[wS N W H u 0, wS N W H u 1, wS N W H u 2, wS N W H u 3, wS N W H u 4, wS N W H u 5, wS N W H u 6])
    none)

/-- The B-side pre-sums of column `v`. -/
def tbP (N W H v : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.block #[wT N W H v 0, wT N W H v 1, wT N W H v 2, wT N W H v 3, wT N W H v 4, wT N W H v 5, wT N W H v 6])
    none)

/-- Cell `(u, v)` of engine `r`: clear at `t = 0`, else accumulate `S_r[u] · T_r[v]`. -/
def macP (H W AccW u v r : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.ifStmt (.binary .eq (.ident "t") (c32 0))
      (.nbaAssign (.slice "M" (((u * H + v) * 7 + r) * AccW) AccW) (.lit (LVec.replicate AccW .l0)))
      (some (.nbaAssign (.slice "M" (((u * H + v) * 7 + r) * AccW) AccW)
        (.resize AccW (.binary .add (.resize (AccW + (W + 1)) (.slice (.ident "M") (((u * H + v) * 7 + r) * AccW) AccW))
          (.binary .mul (sxA "S" AccW ((u * 7 + r) * (W + 1) + W) ((u * 7 + r) * (W + 1)) (W + 1))
            (sxA "T" AccW ((v * 7 + r) * (W + 1) + W) ((v * 7 + r) * (W + 1)) (W + 1))))))))
    none)

/-- Lane `r` of engine cell `(u, v)`. -/
def mS (H AccW u v r : Nat) : Expr2 := .slice (.ident "M") (((u * H + v) * 7 + r) * AccW) AccW

/-- A post-sum process: at `t = H + 1` it writes `e` into `C[lc +: AccW]`. -/
def cP (H AccW lc : Nat) (e : Expr2) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "busy")
    (.ifStmt (.binary .eq (.ident "t") (.binary .add (c32 H) (c32 1))) (.nbaAssign (.slice "C" lc AccW) e) none)
    none)

/-- The four post-sums at cell `(u, v)`. -/
def e11 (H AccW u v : Nat) : Expr2 :=
  .binary .add (.binary .sub (.binary .add (mS H AccW u v 0) (mS H AccW u v 3)) (mS H AccW u v 4)) (mS H AccW u v 6)
def e12 (H AccW u v : Nat) : Expr2 := .binary .add (mS H AccW u v 2) (mS H AccW u v 4)
def e21 (H AccW u v : Nat) : Expr2 := .binary .add (mS H AccW u v 1) (mS H AccW u v 3)
def e22 (H AccW u v : Nat) : Expr2 :=
  .binary .add (.binary .add (.binary .sub (mS H AccW u v 0) (mS H AccW u v 1)) (mS H AccW u v 2)) (mS H AccW u v 5)

def c11P (N H AccW u v : Nat) : Process2 := cP H AccW ((u * N + v) * AccW) (e11 H AccW u v)
def c12P (N H AccW u v : Nat) : Process2 := cP H AccW ((u * N + H + v) * AccW) (e12 H AccW u v)
def c21P (N H AccW u v : Nat) : Process2 := cP H AccW (((H + u) * N + v) * AccW) (e21 H AccW u v)
def c22P (N H AccW u v : Nat) : Process2 := cP H AccW (((H + u) * N + H + v) * AccW) (e22 H AccW u v)

/-- The declarations. -/
def stDecls (N W AccW H : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true }, { name := "t", width := 32 },
   { name := "busy", width := 1 }, { name := "a_sh", width := (2 * H + 1) * N * W },
   { name := "b_sh", width := (2 * H + 1) * N * W }, { name := "S", width := 7 * H * (W + 1) },
   { name := "T", width := 7 * H * (W + 1) }, { name := "M", width := 7 * H * H * AccW }]

def saPs (N W H : Nat) : List Process2 := (List.range H).map (saP N W H)
def tbPs (N W H : Nat) : List Process2 := (List.range H).map (tbP N W H)
def macPs (H W AccW : Nat) : List Process2 :=
  (List.range H).flatMap fun u => (List.range H).flatMap fun v => (List.range 7).map (macP H W AccW u v)
/-- The post-sums of the top block row, row by row. -/
def cTop (N H AccW : Nat) : List Process2 :=
  (List.range H).flatMap fun u => (List.range H).map (c11P N H AccW u) ++ (List.range (N - H)).map (c12P N H AccW u)
/-- The post-sums of the bottom block row, row by row. -/
def cBot (N H AccW : Nat) : List Process2 :=
  (List.range (N - H)).flatMap fun u => (List.range H).map (c21P N H AccW u) ++ (List.range (N - H)).map (c22P N H AccW u)
def cPs (N H AccW : Nat) : List Process2 := cTop N H AccW ++ cBot N H AccW

/-- The generated processes, in source order. -/
def genPs (N W AccW H : Nat) : List Process2 := saPs N W H ++ tbPs N W H ++ macPs H W AccW ++ cPs N H AccW

/-- **The hand-built design**, at block size `H`. -/
def stD (N W AccW H : Nat) : Design2 where
  name := "matmul"
  decls := (stDecls N W AccW H).toArray
  processes := (ctrlP N W H :: genPs N W AccW H).toArray

/-! ### The stages of `instantiate2` -/

def stScope (N W AccW h : Nat) : IEnv :=
  { vals := [("WS", (W : Int) + 1), ("L", (2 * (h : Int) + 1) * N), ("H", h), ("N", N), ("W", W),
      ("AccW", AccW)],
    pwidths := [("N", 32), ("W", 32), ("AccW", 32), ("H", 32), ("L", 32), ("WS", 32)] }

def stEnv (N W AccW h : Nat) : IEnv :=
  { stScope N W AccW h with dims := dimTable (stScope N W AccW h) design.pdesign.decls }

theorem declTy (env : IEnv) :
    declConstType env (some (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32))) none = .ok none :=
  rfl

theorem tyW (env : IEnv) : (PType.packed [{ msb := PExpr.int 31, lsb := PExpr.int 0 }] (some 32)).width env = .ok 32 :=
  rfl

theorem canonInt_small {v : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) : canonInt 32 true v = v := by
  have e : Int.emod v (2 ^ 32) = v := Int.emod_eq_of_lt h0 (by omega)
  unfold canonInt
  simp only [e]
  split
  · rename_i hc
    simp at hc
    omega
  · rfl

theorem hval (N : Nat) (hN : N < 2 ^ 31) :
    canonInt 32 true (((N : Int) + 1).tdiv 2) = (((N + 1) / 2 : Nat) : Int) := by
  have e : ((N : Int) + 1).tdiv 2 = (((N + 1) / 2 : Nat) : Int) := by
    rw [show ((N : Int) + 1) = ((N + 1 : Nat) : Int) by push_cast; rfl, show (2 : Int) = ((2 : Nat) : Int) from rfl,
      ← Int.ofNat_tdiv]
  rw [e, canonInt_small (by omega) (by omega)]

theorem st_paramEnv (N W AccW : Nat) (hN : N < 2 ^ 31) :
    design.pdesign.paramEnv2 [(N : Int), W, AccW] = .ok (stEnv N W AccW ((N + 1) / 2)) := by
  have h := hval N hN
  simp [PDesign.paramEnv2, design.pdesign, bindPackageParams, bindPackageEnums, bindParamsRes, bindParams,
    bindLocals, bindLocal, evalIntTarget, evalInt, bindEnums, IEnv.bindVal, declTy, tyW,
    Gen2.except_ok_bind, Except.mapError, List.lookup, List.filterMapM, List.filterMapM.loop, h, stEnv, stScope]

theorem natAbs_cast {x : Nat} {X : Int} (h : (x : Int) = X) (hx : 0 < x) : (X - 1).natAbs + 1 = x := by
  subst h; omega

theorem st_decls (N W AccW h : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh : 1 ≤ h) :
    buildDecls (stEnv N W AccW h) design.pdesign.decls = .ok (stDecls N W AccW h) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have h1 : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN (by omega))
  have h2 : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos hNN (by omega))
  have h3 : ((2 * (h : Int) + 1) * N * W - 1).natAbs + 1 = (2 * h + 1) * N * W :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (Nat.mul_pos (by omega) hN) (by omega))
  have h4 : (7 * (h : Int) * ((W : Int) + 1) - 1).natAbs + 1 = 7 * h * (W + 1) :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (Nat.mul_pos (by omega) hh) (by omega))
  have h5 : (7 * (h : Int) * h * AccW - 1).natAbs + 1 = 7 * h * h * AccW :=
    natAbs_cast (by push_cast; rfl) (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hh) hh) (by omega))
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    stEnv, stScope, List.lookup, Gen2.except_ok_bind, stDecls, h1, h2, h3, h4, h5]

def stElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "a_sh", "b_sh", "S", "T", "M"].map (·, 1)

theorem st_elems (N W AccW h : Nat) : buildElems (stEnv N W AccW h) design.pdesign.decls = .ok stElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, stEnv,
    stScope, List.lookup, Gen2.except_ok_bind, stElems]

/-- The instantiation environment. -/
abbrev stE (N W AccW h : Nat) : IEnv := (stEnv N W AccW h).withDecls (stDecls N W AccW h)

theorem st_ctrl (N W AccW h : Nat) :
    design.pdesign.processes.map (instProcess2 (stE N W AccW h) stElems) = [ctrlP N W h] := by
  sv2_inst_simp [instStmt2, instStmts2, design.pdesign, stEnv, stScope, stDecls, stElems, ctrlP,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2]
  try and_intros
  all_goals first | rfl | decide | skip

/-! ### The generate templates -/

def saT : PProcess := match design.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.process p], _, _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def tbT : PProcess := match design.pdesign.generates with
  | [_, .genFor _ _ _ _ _ _ [.process p], _, _, _] => p
  | _ => .alwaysFF "" (.block [])
def macT : PProcess := match design.pdesign.generates with
  | [_, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]], _, _] => p
  | _ => .alwaysFF "" (.block [])
def c11T : PProcess := match design.pdesign.generates with
  | [_, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p], _], _] => p
  | _ => .alwaysFF "" (.block [])
def c12T : PProcess := match design.pdesign.generates with
  | [_, _, _, .genFor _ _ _ _ _ _ [_, .genFor _ _ _ _ _ _ [.process p]], _] => p
  | _ => .alwaysFF "" (.block [])
def c21T : PProcess := match design.pdesign.generates with
  | [_, _, _, _, .genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p], _]] => p
  | _ => .alwaysFF "" (.block [])
def c22T : PProcess := match design.pdesign.generates with
  | [_, _, _, _, .genFor _ _ _ _ _ _ [_, .genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

/-- The window facts of a select `x[lo +: w]` of a `c`-bit signal, in the forms the instantiation writes. -/
theorem winF (X W C : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = X) (hW : (w : Int) = W)
    (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = lo ∧ X + W - 1 < C ∧ 1 ≤ X + W ∧ (X + W).toNat = lo + w ∧ 0 < W ∧ W.toNat = w ∧
      X ≤ X + W - 1 := by
  subst hx hW hy; omega

/-- The window facts of a bit select `x[i]` of a `c`-bit signal. -/
theorem bitF (X C : Int) {i c : Nat} (h : i < c) (hx : (i : Int) = X) (hy : (c : Int) = C) :
    0 ≤ X ∧ X.toNat = i ∧ X < C ∧ ¬ X < 0 ∧ ¬ C ≤ X := by
  subst hx hy; omega

macro "st_tsimp" : tactic => `(tactic| sv2_inst_simp [evalSized, ctype, evalAt, ctypeList, evalAtList,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, Gen2.except_pure,
  Lib.min_add_sub_one_self, Lib.max_add_sub_one_self, Lib.add_sub_one_sub_add_one, instStmt2, instStmts2,
  design.pdesign, stEnv, stScope, stDecls, stElems, saT, tbT, macT, c11T, c12T, c21T, c22T,
  saP, tbP, wS, wT, preE, preF, sx1, sxA, macP, mS, cP, e11, e12, e21, e22, c11P, c12P, c21P, c22P,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
  instDivOperand2, fitDivOperand2, divOperandWidthSum2, arraySelWidth, instDivParts2, *])

/-- An entry `p` of the operand registers (`(2h+1)·N` entries of `W` bits): its window and its top bit. -/
theorem entF (N W h p : Nat) (X : Int) (hp : p + 1 ≤ (2 * h + 1) * N) (hW : 1 ≤ W) (hx : (p : Int) = X) :
    (0 ≤ X * W ∧ (X * W).toNat = p * W ∧ X * W + W - 1 < (2 * h + 1) * N * W ∧ 1 ≤ X * W + W ∧
      (X * W + W).toNat = p * W + W ∧ (0 : Int) < W ∧ (W : Int).toNat = W ∧ X * W ≤ X * W + W - 1) ∧
    (0 ≤ X * W + W - 1 ∧ (X * W + W - 1).toNat = p * W + W - 1 ∧ X * W + W - 1 < (2 * h + 1) * N * W ∧
      ¬ X * W + W - 1 < 0 ∧ ¬ (2 * h + 1) * N * W ≤ X * W + W - 1) := by
  have h1 : p * W + W ≤ (2 * h + 1) * N * W := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp
  subst hx
  refine ⟨winF _ _ _ (lo := p * W) (w := W) (c := (2 * h + 1) * N * W) h1 (by omega) (by push_cast; rfl) rfl
    (by push_cast; rfl), bitF _ _ (i := p * W + W - 1) (c := (2 * h + 1) * N * W) (by omega) ?_ (by push_cast; rfl)⟩
  rw [Int.ofNat_sub (by have := Nat.le_mul_of_pos_left W (show 0 < p + 1 by omega); rw [Nat.succ_mul] at this; omega)]
  push_cast; rfl

/-- A lane `k = u·7 + r` of a pre-sum register (`7h` lanes of `W + 1` bits). -/
theorem laneF (W h k : Nat) (X : Int) (hk : k < 7 * h) (hx : (k : Int) = X) :
    0 ≤ X * (W + 1) ∧ (X * (W + 1)).toNat = k * (W + 1) ∧ X * (W + 1) + (W + 1) - 1 < 7 * h * (W + 1) ∧
      1 ≤ X * (W + 1) + (W + 1) ∧ (X * (W + 1) + (W + 1)).toNat = k * (W + 1) + (W + 1) ∧ (0 : Int) < W + 1 ∧
      ((W : Int) + 1).toNat = W + 1 ∧ X * (W + 1) ≤ X * (W + 1) + (W + 1) - 1 := by
  have h1 : k * (W + 1) + (W + 1) ≤ 7 * h * (W + 1) := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hk
  subst hx
  exact winF _ _ _ (lo := k * (W + 1)) (w := W + 1) (c := 7 * h * (W + 1)) h1 (by omega) (by push_cast; rfl)
    (by push_cast; rfl) (by push_cast; rfl)

/-- The declared widths, in the forms the instantiation writes. -/
theorem widF (N W AccW h : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) :
    ((1 : Int) ≤ (N : Int) * N * W ∧ ((N : Int) * N * W - 1).natAbs + 1 = N * N * W) ∧
    ((1 : Int) ≤ (N : Int) * N * AccW ∧ ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW) ∧
    ((1 : Int) ≤ (2 * (h : Int) + 1) * N * W ∧ ((2 * (h : Int) + 1) * N * W - 1).natAbs + 1 = (2 * h + 1) * N * W) ∧
    ((1 : Int) ≤ 7 * (h : Int) * ((W : Int) + 1) ∧ (7 * (h : Int) * ((W : Int) + 1) - 1).natAbs + 1 = 7 * h * (W + 1)) ∧
    ((1 : Int) ≤ 7 * (h : Int) * h * AccW ∧ (7 * (h : Int) * h * AccW - 1).natAbs + 1 = 7 * h * h * AccW) := by
  have hNN : 0 < N * N := Nat.mul_pos hN hN
  have p1 := Nat.mul_pos hNN (show 0 < W by omega)
  have p2 := Nat.mul_pos hNN (show 0 < AccW by omega)
  have p3 := Nat.mul_pos (Nat.mul_pos (show 0 < 2 * h + 1 by omega) hN) (show 0 < W by omega)
  have p4 := Nat.mul_pos (Nat.mul_pos (show 0 < 7 by omega) hh1) (show 0 < W + 1 by omega)
  have p5 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (show 0 < 7 by omega) hh1) hh1) (show 0 < AccW by omega)
  refine ⟨⟨?_, natAbs_cast (by push_cast; rfl) p1⟩, ⟨?_, natAbs_cast (by push_cast; rfl) p2⟩,
    ⟨?_, natAbs_cast (by push_cast; rfl) p3⟩, ⟨?_, natAbs_cast (by push_cast; rfl) p4⟩,
    ⟨?_, natAbs_cast (by push_cast; rfl) p5⟩⟩
  · have : ((N * N * W : Nat) : Int) = (N : Int) * N * W := by push_cast; rfl
    omega
  · have : ((N * N * AccW : Nat) : Int) = (N : Int) * N * AccW := by push_cast; rfl
    omega
  · have : (((2 * h + 1) * N * W : Nat) : Int) = (2 * (h : Int) + 1) * N * W := by push_cast; rfl
    omega
  · have : ((7 * h * (W + 1) : Nat) : Int) = 7 * (h : Int) * ((W : Int) + 1) := by push_cast; rfl
    omega
  · have : ((7 * h * h * AccW : Nat) : Int) = 7 * (h : Int) * h * AccW := by push_cast; rfl
    omega

theorem sa_inst (N W AccW h u : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (hu : u < h) :
    instProcess2 ((stE N W AccW h).bindVal "u" u) stElems saT = saP N W h u := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hW1' : (0 : Int) < W := by omega
  have hc1 : 1 + W ≤ W + 1 := by omega
  have hc2 : 1 + W = W + 1 := by omega
  have q1 := entF N W h (u * N) ((u : Int) * N) (by have := Nat.mul_le_mul_right N (show u + 1 ≤ 2 * h + 1 by omega); rw [Nat.succ_mul] at this; omega) hW (by push_cast; rfl)
  have q2 := entF N W h (u * N + h) ((u : Int) * N + h) (by have := Nat.mul_le_mul_right N (show u + 2 ≤ 2 * h + 1 by omega); rw [Nat.add_mul] at this; omega) hW (by push_cast; rfl)
  have q3 := entF N W h ((h + u) * N) (((h : Int) + u) * N) (by have := Nat.mul_le_mul_right N (show h + u + 1 ≤ 2 * h + 1 by omega); rw [Nat.succ_mul] at this; omega) hW (by push_cast; rfl)
  have q4 := entF N W h ((h + u) * N + h) (((h : Int) + u) * N + h) (by have := Nat.mul_le_mul_right N (show h + u + 2 ≤ 2 * h + 1 by omega); rw [Nat.add_mul] at this; omega) hW (by push_cast; rfl)
  have l0 := laneF W h (u * 7) ((u : Int) * 7) (by omega) (by push_cast; rfl)
  have l1 := laneF W h (u * 7 + 1) ((u : Int) * 7 + 1) (by omega) (by push_cast; rfl)
  have l2 := laneF W h (u * 7 + 2) ((u : Int) * 7 + 2) (by omega) (by push_cast; rfl)
  have l3 := laneF W h (u * 7 + 3) ((u : Int) * 7 + 3) (by omega) (by push_cast; rfl)
  have l4 := laneF W h (u * 7 + 4) ((u : Int) * 7 + 4) (by omega) (by push_cast; rfl)
  have l5 := laneF W h (u * 7 + 5) ((u : Int) * 7 + 5) (by omega) (by push_cast; rfl)
  have l6 := laneF W h (u * 7 + 6) ((u : Int) * 7 + 6) (by omega) (by push_cast; rfl)
  st_tsimp
  all_goals first | rfl | decide | skip

/-- Entry `m` of a family of `w`-bit windows in a `c`-bit signal: the window facts at `X · w`. -/
theorem famF (w c m : Nat) (X Wi Ci : Int) (hm : m * w + w ≤ c) (hw : 0 < w) (hx : (m : Int) = X)
    (hW : (w : Int) = Wi) (hC : (c : Int) = Ci) :
    0 ≤ X * Wi ∧ (X * Wi).toNat = m * w ∧ X * Wi + Wi - 1 < Ci ∧ 1 ≤ X * Wi + Wi ∧
      (X * Wi + Wi).toNat = m * w + w ∧ 0 < Wi ∧ Wi.toNat = w ∧ X * Wi ≤ X * Wi + Wi - 1 := by
  subst hx hW hC
  exact winF _ _ _ (lo := m * w) (w := w) (c := c) hm hw (by push_cast; rfl) rfl rfl

theorem fam_le {m n w : Nat} (h : m < n) : m * w + w ≤ n * w := by
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h

theorem tb_inst (N W AccW h v : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (hv : v < h) :
    instProcess2 ((stE N W AccW h).bindVal "v" v) stElems tbT = tbP N W h v := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hW1' : (0 : Int) < W := by omega
  have hc1 : 1 + W ≤ W + 1 := by omega
  have hc2 : 1 + W = W + 1 := by omega
  have k1 : h ≤ h * N := Nat.le_mul_of_pos_right h hN
  have k2 : (2 * h + 1) * N = 2 * (h * N) + N := by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  have q1 := entF N W h v (v : Int) (by omega) hW rfl
  have q2 := entF N W h (h + v) ((h : Int) + v) (by omega) hW (by push_cast; rfl)
  have q3 := entF N W h (h * N + v) ((h : Int) * N + v) (by omega) hW (by push_cast; rfl)
  have q4 := entF N W h (h * N + h + v) ((h : Int) * N + h + v) (by omega) hW (by push_cast; rfl)
  have l0 := laneF W h (v * 7) ((v : Int) * 7) (by omega) (by push_cast; rfl)
  have l1 := laneF W h (v * 7 + 1) ((v : Int) * 7 + 1) (by omega) (by push_cast; rfl)
  have l2 := laneF W h (v * 7 + 2) ((v : Int) * 7 + 2) (by omega) (by push_cast; rfl)
  have l3 := laneF W h (v * 7 + 3) ((v : Int) * 7 + 3) (by omega) (by push_cast; rfl)
  have l4 := laneF W h (v * 7 + 4) ((v : Int) * 7 + 4) (by omega) (by push_cast; rfl)
  have l5 := laneF W h (v * 7 + 5) ((v : Int) * 7 + 5) (by omega) (by push_cast; rfl)
  have l6 := laneF W h (v * 7 + 6) ((v : Int) * 7 + 6) (by omega) (by push_cast; rfl)
  clear k1 k2
  st_tsimp
  all_goals first | rfl | decide | skip

/-- Cell `(u, v)` of the engines is cell `u·h + v < h·h`. -/
theorem cell_lt {h u v : Nat} (hu : u < h) (hv : v < h) : u * h + v < h * h := by
  have := Nat.mul_le_mul_right h (show u + 1 ≤ h by omega); rw [Nat.succ_mul] at this; omega

theorem mac_inst (N W AccW h u v r : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h)
    (hu : u < h) (hv : v < h) (hr : r < 7) :
    instProcess2 ((((stE N W AccW h).bindVal "u" u).bindVal "v" v).bindVal "r" r) stElems macT =
      macP h W AccW u v r := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hW1 : 0 < W := hW
  have hA1 : 0 < AccW := hA
  have hWne : ¬ W = 0 := by omega
  have hW1' : (0 : Int) < W := by omega
  have hc := cell_lt hu hv
  have lm := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + r) ((((u : Int) * h + v) * 7 + r)) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl
    (by push_cast; rfl)
  have ls := laneF W h (u * 7 + r) ((u : Int) * 7 + r) (by omega) (by push_cast; rfl)
  have lt := laneF W h (v * 7 + r) ((v : Int) * 7 + r) (by omega) (by push_cast; rfl)
  have bs := bitF (((u : Int) * 7 + r) * ((W : Int) + 1) + W) (7 * (h : Int) * ((W : Int) + 1))
    (i := (u * 7 + r) * (W + 1) + W) (c := 7 * h * (W + 1)) (by have := fam_le (w := W + 1) (show u * 7 + r < 7 * h by omega); omega)
    (by push_cast; rfl) (by push_cast; rfl)
  have bt := bitF (((v : Int) * 7 + r) * ((W : Int) + 1) + W) (7 * (h : Int) * ((W : Int) + 1))
    (i := (v * 7 + r) * (W + 1) + W) (c := 7 * h * (W + 1)) (by have := fam_le (w := W + 1) (show v * 7 + r < 7 * h by omega); omega)
    (by push_cast; rfl) (by push_cast; rfl)
  have hlt1 : ¬ AccW + (W + 1) < AccW := by omega
  have hle1 : ¬ AccW + (W + 1) ≤ AccW := by omega
  have hlt2 : ¬ AccW + W + 1 < AccW := by omega
  have hle2 : ¬ AccW + W + 1 ≤ AccW := by omega
  st_tsimp
  repeat (unfold instExpr2; st_tsimp)
  all_goals first | rfl | decide | skip

/-- The facts every post-sum template needs: `C`'s window `m` and the four engine lanes it reads. -/
theorem c11_inst (N W AccW h u v : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (hu : u < h) (hv : v < h) :
    instProcess2 (((stE N W AccW h).bindVal "u" u).bindVal "v" v) stElems c11T = c11P N h AccW u v := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hA1 : 0 < AccW := hA
  have hc := cell_lt hu hv
  have hm : ((u * h + v) * 7 + 6) < 7 * h * h := by rw [Nat.mul_assoc 7]; omega
  have hC : u * N + v < N * N := by have := Nat.mul_le_mul_right N (show u + 1 ≤ N by omega); rw [Nat.succ_mul] at this; omega
  have lc := famF AccW (N * N * AccW) (u * N + v) ((u : Int) * N + v) AccW ((N : Int) * N * AccW)
    (fam_le hC) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m0 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7) (((u : Int) * h + v) * 7) AccW (7 * (h : Int) * h * AccW)
    (fam_le (by omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m3 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 3) (((u : Int) * h + v) * 7 + 3) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m4 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 4) (((u : Int) * h + v) * 7 + 4) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m6 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 6) (((u : Int) * h + v) * 7 + 6) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  st_tsimp
  all_goals first | rfl | decide | skip

theorem c12_inst (N W AccW h u v : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (h2N : N ≤ 2 * h)
    (hu : u < h) (hv : v < N - h) :
    instProcess2 (((stE N W AccW h).bindVal "u" u).bindVal "v" v) stElems c12T = c12P N h AccW u v := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hA1 : 0 < AccW := hA
  have hc := cell_lt hu (show v < h by omega)
  have hC : u * N + h + v < N * N := by
    have := Nat.mul_le_mul_right N (show u + 1 ≤ N by omega); rw [Nat.succ_mul] at this; omega
  have lc := famF AccW (N * N * AccW) (u * N + h + v) ((u : Int) * N + h + v) AccW ((N : Int) * N * AccW)
    (fam_le hC) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m2 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 2) (((u : Int) * h + v) * 7 + 2) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m4 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 4) (((u : Int) * h + v) * 7 + 4) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  st_tsimp
  all_goals first | rfl | decide | skip

theorem c21_inst (N W AccW h u v : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (h2N : N ≤ 2 * h)
    (hu : u < N - h) (hv : v < h) :
    instProcess2 (((stE N W AccW h).bindVal "u" u).bindVal "v" v) stElems c21T = c21P N h AccW u v := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hA1 : 0 < AccW := hA
  have hc := cell_lt (show u < h by omega) hv
  have hC : (h + u) * N + v < N * N := by
    have := Nat.mul_le_mul_right N (show h + u + 1 ≤ N by omega); rw [Nat.succ_mul] at this; omega
  have lc := famF AccW (N * N * AccW) ((h + u) * N + v) (((h : Int) + u) * N + v) AccW ((N : Int) * N * AccW)
    (fam_le hC) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m1 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 1) (((u : Int) * h + v) * 7 + 1) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m3 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 3) (((u : Int) * h + v) * 7 + 3) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  st_tsimp
  all_goals first | rfl | decide | skip

theorem c22_inst (N W AccW h u v : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (h2N : N ≤ 2 * h)
    (hu : u < N - h) (hv : v < N - h) :
    instProcess2 (((stE N W AccW h).bindVal "u" u).bindVal "v" v) stElems c22T = c22P N h AccW u v := by
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  obtain ⟨⟨d1, e1⟩, ⟨d2, e2⟩, ⟨d3, e3⟩, ⟨d4, e4⟩, ⟨d5, e5⟩⟩ := widF N W AccW h hN hW hA hh1
  have hA1 : 0 < AccW := hA
  have hc := cell_lt (show u < h by omega) (show v < h by omega)
  have hC : (h + u) * N + h + v < N * N := by
    have := Nat.mul_le_mul_right N (show h + u + 1 ≤ N by omega); rw [Nat.succ_mul] at this; omega
  have lc := famF AccW (N * N * AccW) ((h + u) * N + h + v) (((h : Int) + u) * N + h + v) AccW ((N : Int) * N * AccW)
    (fam_le hC) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m0 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7) (((u : Int) * h + v) * 7) AccW (7 * (h : Int) * h * AccW)
    (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m1 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 1) (((u : Int) * h + v) * 7 + 1) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m2 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 2) (((u : Int) * h + v) * 7 + 2) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  have m5 := famF AccW (7 * h * h * AccW) ((u * h + v) * 7 + 5) (((u : Int) * h + v) * 7 + 5) AccW
    (7 * (h : Int) * h * AccW) (fam_le (by rw [Nat.mul_assoc 7]; omega)) hA1 (by push_cast; rfl) rfl (by push_cast; rfl)
  st_tsimp
  all_goals first | rfl | decide | skip

/-! ### The generates -/

/-- One generate loop over a process template. -/
theorem gen1 {env : IEnv} {elems : List (String × Nat)} {F : Nat} {lu : Option String} {gu : String} {eu : PExpr}
    {rcu : Option Nat} {T : PProcess} {nu : Nat} {P : Nat → Process2}
    (hint : ∀ i : Int, eu.isInt (env.bindVal gu i) = true)
    (hev : ∀ i : Int, evalInt (env.bindVal gu i) eu = .ok (nu : Int)) (hF : nu < F)
    (hinst : ∀ u, u < nu → instProcess2 (env.bindVal gu (u : Int)) elems T = P u) :
    (GenItem.genFor lu gu (.int 0) (.binary .slt (.genvarRef gu) eu) (.unary .inc (.genvarRef gu)) rcu
      [.process T]).expand2 env elems F = .ok ((List.range nu).map P) := by
  have h := GenItem.expand2_genFor_ascending_processes (elems := elems) (label := lu) (rc := rcu) (ps := [T])
    (N := (nu : Int))
    (evalInt_int 0) hint hev (by simpa using hF)
  simp only [List.map_cons, List.map_nil] at h
  rw [h, intRange_zero]
  simp only [Int.sub_zero, Int.toNat_natCast, List.flatMap_map, Gen2.flatMap_singleton_map]
  congr 1
  exact List.map_congr_left fun u hu => hinst u (List.mem_range.mp hu)

/-- Two nested generate loops. -/
theorem gen2 {env : IEnv} {elems : List (String × Nat)} {F : Nat} {lu lv : Option String} {gu gv : String}
    {eu ev : PExpr} {rcu rcv : Option Nat} {T : PProcess} {nu nv : Nat} {P : Nat → Nat → Process2}
    (hint : ∀ i : Int, eu.isInt (env.bindVal gu i) = true)
    (hev : ∀ i : Int, evalInt (env.bindVal gu i) eu = .ok (nu : Int))
    (hint' : ∀ i j : Int, ev.isInt ((env.bindVal gu i).bindVal gv j) = true)
    (hev' : ∀ i j : Int, evalInt ((env.bindVal gu i).bindVal gv j) ev = .ok (nv : Int))
    (hF : nu < F) (hF' : nv < F)
    (hinst : ∀ u v, u < nu → v < nv → instProcess2 ((env.bindVal gu (u : Int)).bindVal gv (v : Int)) elems T = P u v) :
    (GenItem.genFor lu gu (.int 0) (.binary .slt (.genvarRef gu) eu) (.unary .inc (.genvarRef gu)) rcu
      [GenItem.genFor lv gv (.int 0) (.binary .slt (.genvarRef gv) ev) (.unary .inc (.genvarRef gv)) rcv
        [.process T]]).expand2 env elems F =
      .ok ((List.range nu).flatMap fun u => (List.range nv).map (P u)) := by
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (nu : Int))
      (f := fun i => (List.range nv).map fun v : Nat => instProcess2 ((env.bindVal gu i).bindVal gv (v : Int)) elems T)
      (evalInt_int 0) hint hev (by simpa using hF)]
  · rw [intRange_zero]
    simp only [Int.sub_zero, Int.toNat_natCast, List.flatMap_map]
    congr 1
    exact CombView.flatMap_congr' fun u hu => List.map_congr_left fun v hv =>
      hinst u v (List.mem_range.mp hu) (List.mem_range.mp hv)
  · intro i _ _
    exact expandList2_singleton_ok (gen1 (hint' i) (hev' i) hF' (fun _ _ => rfl))

/-- Three nested generate loops. -/
theorem gen3 {env : IEnv} {elems : List (String × Nat)} {F : Nat} {lu lv lr : Option String} {gu gv gr : String}
    {eu ev er : PExpr} {rcu rcv rcr : Option Nat} {T : PProcess} {nu nv nr : Nat} {P : Nat → Nat → Nat → Process2}
    (hint : ∀ i : Int, eu.isInt (env.bindVal gu i) = true)
    (hev : ∀ i : Int, evalInt (env.bindVal gu i) eu = .ok (nu : Int))
    (hint' : ∀ i j : Int, ev.isInt ((env.bindVal gu i).bindVal gv j) = true)
    (hev' : ∀ i j : Int, evalInt ((env.bindVal gu i).bindVal gv j) ev = .ok (nv : Int))
    (hint'' : ∀ i j k : Int, er.isInt (((env.bindVal gu i).bindVal gv j).bindVal gr k) = true)
    (hev'' : ∀ i j k : Int, evalInt (((env.bindVal gu i).bindVal gv j).bindVal gr k) er = .ok (nr : Int))
    (hF : nu < F) (hF' : nv < F) (hF'' : nr < F)
    (hinst : ∀ u v r, u < nu → v < nv → r < nr →
      instProcess2 (((env.bindVal gu (u : Int)).bindVal gv (v : Int)).bindVal gr (r : Int)) elems T = P u v r) :
    (GenItem.genFor lu gu (.int 0) (.binary .slt (.genvarRef gu) eu) (.unary .inc (.genvarRef gu)) rcu
      [GenItem.genFor lv gv (.int 0) (.binary .slt (.genvarRef gv) ev) (.unary .inc (.genvarRef gv)) rcv
        [GenItem.genFor lr gr (.int 0) (.binary .slt (.genvarRef gr) er) (.unary .inc (.genvarRef gr)) rcr
          [.process T]]]).expand2 env elems F =
      .ok ((List.range nu).flatMap fun u => (List.range nv).flatMap fun v => (List.range nr).map (P u v)) := by
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (nu : Int))
      (f := fun i => (List.range nv).flatMap fun v : Nat => (List.range nr).map fun r : Nat =>
        instProcess2 (((env.bindVal gu i).bindVal gv (v : Int)).bindVal gr (r : Int)) elems T)
      (evalInt_int 0) hint hev (by simpa using hF)]
  · rw [intRange_zero]
    simp only [Int.sub_zero, Int.toNat_natCast, List.flatMap_map]
    congr 1
    exact CombView.flatMap_congr' fun u hu => CombView.flatMap_congr' fun v hv => List.map_congr_left fun r hr =>
      hinst u v r (List.mem_range.mp hu) (List.mem_range.mp hv) (List.mem_range.mp hr)
  · intro i _ _
    exact expandList2_singleton_ok (gen2 (hint' i) (hev' i) (hint'' i) (hev'' i) hF' hF'' (fun _ _ _ _ => rfl))

/-- A generate loop whose body is two loops over process templates. -/
theorem genTwo {env : IEnv} {elems : List (String × Nat)} {F : Nat} {lu lv lw : Option String} {gu gv gw : String}
    {eu ev ew : PExpr} {rcu rcv rcw : Option Nat} {T1 T2 : PProcess} {nu nv nw : Nat} {P1 P2 : Nat → Nat → Process2}
    (hint : ∀ i : Int, eu.isInt (env.bindVal gu i) = true)
    (hev : ∀ i : Int, evalInt (env.bindVal gu i) eu = .ok (nu : Int))
    (hint1 : ∀ i j : Int, ev.isInt ((env.bindVal gu i).bindVal gv j) = true)
    (hev1 : ∀ i j : Int, evalInt ((env.bindVal gu i).bindVal gv j) ev = .ok (nv : Int))
    (hint2 : ∀ i j : Int, ew.isInt ((env.bindVal gu i).bindVal gw j) = true)
    (hev2 : ∀ i j : Int, evalInt ((env.bindVal gu i).bindVal gw j) ew = .ok (nw : Int))
    (hF : nu < F) (hF1 : nv < F) (hF2 : nw < F)
    (hinst1 : ∀ u v, u < nu → v < nv → instProcess2 ((env.bindVal gu (u : Int)).bindVal gv (v : Int)) elems T1 = P1 u v)
    (hinst2 : ∀ u v, u < nu → v < nw → instProcess2 ((env.bindVal gu (u : Int)).bindVal gw (v : Int)) elems T2 = P2 u v) :
    (GenItem.genFor lu gu (.int 0) (.binary .slt (.genvarRef gu) eu) (.unary .inc (.genvarRef gu)) rcu
      [GenItem.genFor lv gv (.int 0) (.binary .slt (.genvarRef gv) ev) (.unary .inc (.genvarRef gv)) rcv [.process T1],
       GenItem.genFor lw gw (.int 0) (.binary .slt (.genvarRef gw) ew) (.unary .inc (.genvarRef gw)) rcw
        [.process T2]]).expand2 env elems F =
      .ok ((List.range nu).flatMap fun u => (List.range nv).map (P1 u) ++ (List.range nw).map (P2 u)) := by
  rw [GenItem.expand2_genFor_ascending_flatMap (N := (nu : Int))
      (f := fun i => (List.range nv).map (fun v : Nat => instProcess2 ((env.bindVal gu i).bindVal gv (v : Int)) elems T1) ++
        (List.range nw).map fun v : Nat => instProcess2 ((env.bindVal gu i).bindVal gw (v : Int)) elems T2)
      (evalInt_int 0) hint hev (by simpa using hF)]
  · rw [intRange_zero]
    simp only [Int.sub_zero, Int.toNat_natCast, List.flatMap_map]
    congr 1
    refine CombView.flatMap_congr' fun u hu => ?_
    rw [List.map_congr_left fun v hv => hinst1 u v (List.mem_range.mp hu) (List.mem_range.mp hv),
      List.map_congr_left fun v hv => hinst2 u v (List.mem_range.mp hu) (List.mem_range.mp hv)]
  · intro i _ _
    exact expandList2_cons_ok (gen1 (hint1 i) (hev1 i) hF1 (fun _ _ => rfl))
      (expandList2_singleton_ok (gen1 (hint2 i) (hev2 i) hF2 (fun _ _ => rfl)))

def genU (lbl g : String) (bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) bound) (.unary .inc (.genvarRef g)) (some rc) body

def hE : PExpr := .paramRef "H" none
def nhE : PExpr := .binary (.m0 .sub) (.paramRef "N" none) (.paramRef "H" none)

theorem st_gens_src : design.pdesign.generates =
    [genU "g_sa" "u" hE 2 [.process saT], genU "g_tb" "v" hE 2 [.process tbT],
     genU "g_mu" "u" hE 2 [genU "g_mv" "v" hE 2 [genU "g_mr" "r" (.int 7) 7 [.process macT]]],
     genU "g_ct" "u" hE 2 [genU "g_c11" "v" hE 2 [.process c11T], genU "g_c12" "v" nhE 2 [.process c12T]],
     genU "g_cb" "u" nhE 2 [genU "g_c21" "v" hE 2 [.process c21T], genU "g_c22" "v" nhE 2 [.process c22T]]] := rfl

theorem st_gens (N W AccW h F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hh1 : 1 ≤ h) (hhN : h ≤ N)
    (h2N : N ≤ 2 * h) (hF : N + 7 < F) :
    expandList2 (stE N W AccW h) stElems F design.pdesign.generates = .ok (genPs N W AccW h) := by
  have hH1 : ∀ i : Int, ((stE N W AccW h).bindVal "u" i).vals.lookup "H" = some (h : Int) := fun i => by
    simp [IEnv.bindVal, List.lookup, stEnv, stScope]
  have hN1 : ∀ i : Int, ((stE N W AccW h).bindVal "u" i).vals.lookup "N" = some (N : Int) := fun i => by
    simp [IEnv.bindVal, List.lookup, stEnv, stScope]
  have hH1' : ∀ i : Int, ((stE N W AccW h).bindVal "v" i).vals.lookup "H" = some (h : Int) := fun i => by
    simp [IEnv.bindVal, List.lookup, stEnv, stScope]
  have hH2 : ∀ i j : Int, (((stE N W AccW h).bindVal "u" i).bindVal "v" j).vals.lookup "H" = some (h : Int) :=
    fun i j => by simp [IEnv.bindVal, List.lookup, stEnv, stScope]
  have hN2 : ∀ i j : Int, (((stE N W AccW h).bindVal "u" i).bindVal "v" j).vals.lookup "N" = some (N : Int) :=
    fun i j => by simp [IEnv.bindVal, List.lookup, stEnv, stScope]
  have iH1 : ∀ i : Int, hE.isInt ((stE N W AccW h).bindVal "u" i) = true := fun i => isInt_paramRef_of (hH1 i)
  have eH1 : ∀ i : Int, evalInt ((stE N W AccW h).bindVal "u" i) hE = .ok (h : Int) := fun i =>
    evalInt_paramRef_of (hH1 i)
  have iH1' : ∀ i : Int, hE.isInt ((stE N W AccW h).bindVal "v" i) = true := fun i => isInt_paramRef_of (hH1' i)
  have eH1' : ∀ i : Int, evalInt ((stE N W AccW h).bindVal "v" i) hE = .ok (h : Int) := fun i =>
    evalInt_paramRef_of (hH1' i)
  have iH2 : ∀ i j : Int, hE.isInt (((stE N W AccW h).bindVal "u" i).bindVal "v" j) = true := fun i j =>
    isInt_paramRef_of (hH2 i j)
  have eH2 : ∀ i j : Int, evalInt (((stE N W AccW h).bindVal "u" i).bindVal "v" j) hE = .ok (h : Int) :=
    fun i j => evalInt_paramRef_of (hH2 i j)
  have iD1 : ∀ i : Int, nhE.isInt ((stE N W AccW h).bindVal "u" i) = true := fun i =>
    isInt_binary_of rfl (isInt_paramRef_of (hN1 i)) (isInt_paramRef_of (hH1 i))
  have eD1 : ∀ i : Int, evalInt ((stE N W AccW h).bindVal "u" i) nhE = .ok ((N - h : Nat) : Int) := fun i => by
    rw [Int.ofNat_sub hhN]
    exact evalInt_sub_of (isInt_paramRef_of (hN1 i)) (isInt_paramRef_of (hH1 i)) (evalInt_paramRef_of (hN1 i))
      (evalInt_paramRef_of (hH1 i))
  have iD2 : ∀ i j : Int, nhE.isInt (((stE N W AccW h).bindVal "u" i).bindVal "v" j) = true := fun i j =>
    isInt_binary_of rfl (isInt_paramRef_of (hN2 i j)) (isInt_paramRef_of (hH2 i j))
  have eD2 : ∀ i j : Int, evalInt (((stE N W AccW h).bindVal "u" i).bindVal "v" j) nhE = .ok ((N - h : Nat) : Int) :=
    fun i j => by
      rw [Int.ofNat_sub hhN]
      exact evalInt_sub_of (isInt_paramRef_of (hN2 i j)) (isInt_paramRef_of (hH2 i j))
        (evalInt_paramRef_of (hN2 i j)) (evalInt_paramRef_of (hH2 i j))
  have i7 : ∀ i j k : Int, (PExpr.int 7).isInt ((((stE N W AccW h).bindVal "u" i).bindVal "v" j).bindVal "r" k) = true :=
    fun _ _ _ => rfl
  have e7 : ∀ i j k : Int,
      evalInt ((((stE N W AccW h).bindVal "u" i).bindVal "v" j).bindVal "r" k) (.int 7) = .ok ((7 : Nat) : Int) :=
    fun _ _ _ => rfl
  have hFh : h < F := by omega
  have hFd : N - h < F := by omega
  have hF7 : 7 < F := by omega
  rw [st_gens_src, genPs, cPs]
  simp only [List.append_assoc, genU]
  refine expandList2_cons_ok (gen1 iH1 eH1 hFh fun u hu => sa_inst N W AccW h u hN hW hA hh1 hhN hu)
    (expandList2_cons_ok (gen1 iH1' eH1' hFh fun v hv => tb_inst N W AccW h v hN hW hA hh1 hhN hv)
    (expandList2_cons_ok (gen3 iH1 eH1 iH2 eH2 i7 e7 hFh hFh hF7
      fun u v r hu hv hr => mac_inst N W AccW h u v r hN hW hA hh1 hu hv hr)
    (expandList2_cons_ok (genTwo iH1 eH1 iH2 eH2 iD2 eD2 hFh hFh hFd
      (fun u v hu hv => c11_inst N W AccW h u v hN hW hA hh1 hhN hu hv)
      (fun u v hu hv => c12_inst N W AccW h u v hN hW hA hh1 hhN h2N hu hv))
    (expandList2_singleton_ok (genTwo iD1 eD1 iH2 eH2 iD2 eD2 hFd hFh hFd
      (fun u v hu hv => c21_inst N W AccW h u v hN hW hA hh1 hhN h2N hu hv)
      (fun u v hu hv => c22_inst N W AccW h u v hN hW hA hh1 hhN h2N hu hv))))))

/-- The block size and its facts. -/
theorem hh_facts (N : Nat) (hN : 1 ≤ N) : 1 ≤ (N + 1) / 2 ∧ (N + 1) / 2 ≤ N ∧ N ≤ 2 * ((N + 1) / 2) := by omega

theorem st_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    design.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (design.pdesign.assemble2 (stEnv N W AccW ((N + 1) / 2)) (stDecls N W AccW ((N + 1) / 2)) stElems
        (genPs N W AccW ((N + 1) / 2))) := by
  obtain ⟨h1, h2, h3⟩ := hh_facts N hN
  refine PDesign.instantiate2_of_ok rfl (st_paramEnv N W AccW hN31) (st_decls N W AccW _ hN hW hA h1)
    (st_elems N W AccW _) (st_gens N W AccW _ _ hN hW hA h1 h2 h3 ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  have := Nat.le_mul_self (N + (W + (AccW + 0)) + 2)
  omega

theorem st_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    (design.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      ctrlP N W ((N + 1) / 2) :: genPs N W AccW ((N + 1) / 2) := by
  rw [PDesign.instantiateD2_of_ok (st_instantiate2 N W AccW hN hW hA hN31), PDesign.assemble2_processes, st_ctrl]
  simp [design.pdesign]

/-! ### Disjoint windows -/

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

theorem names_of_within {p : Process2} {n : String} {lo w : Nat} (h : Within p n lo w) : Names p [n] :=
  fun a ha => by simp [(h a ha).1]

/-- Two windows `k·w` and `k'·w` of one name, `k ≠ k'`, are disjoint. -/
theorem disj_ne {p q : Process2} {n : String} {w k k' : Nat} (hp : Within p n (k * w) w) (hq : Within q n (k' * w) w)
    (h : k ≠ k') : Disj p q := by
  intro a ha b hb
  obtain ⟨-, l, v, hav, h1, h2⟩ := hp a ha
  obtain ⟨-, l', v', hbv, h1', h2'⟩ := hq b hb
  simp only [DrvWin.overlaps, hav, hbv, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · have := rowMajor_le (K := w) h; right; right; omega
  · have := rowMajor_le (K := w) h; right; left; omega

/-- Row-major indices of different cells differ. -/
theorem rm_ne {K a b a' b' : Nat} (hb : b < K) (hb' : b' < K) (h : a ≠ a' ∨ b ≠ b') : a * K + b ≠ a' * K + b' := by
  intro e
  have d1 : (a * K + b) / K = a := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
  have d2 : (a' * K + b') / K = a' := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb', Nat.zero_add]
  have m1 : (a * K + b) % K = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have m2 : (a' * K + b') % K = b' := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb']
  rw [e] at d1 m1
  rcases h with h | h
  · exact h (d1.symm.trans d2)
  · exact h (m1.symm.trans m2)

section windows
variable (N W AccW h : Nat)

theorem ctrl_names : Names (ctrlP N W h) ["busy", "done", "t", "a_sh", "b_sh"] := by
  intro a ha
  simp only [ctrlP, nb, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins,
    List.append_nil, List.cons_append, List.nil_append] at ha
  revert ha a
  decide

theorem lane_eqs (u W : Nat) : u * 7 * (W + 1) = u * (7 * (W + 1)) ∧
    (u * 7 + 1) * (W + 1) = u * (7 * (W + 1)) + 1 * (W + 1) ∧ (u * 7 + 2) * (W + 1) = u * (7 * (W + 1)) + 2 * (W + 1) ∧
    (u * 7 + 3) * (W + 1) = u * (7 * (W + 1)) + 3 * (W + 1) ∧ (u * 7 + 4) * (W + 1) = u * (7 * (W + 1)) + 4 * (W + 1) ∧
    (u * 7 + 5) * (W + 1) = u * (7 * (W + 1)) + 5 * (W + 1) ∧ (u * 7 + 6) * (W + 1) = u * (7 * (W + 1)) + 6 * (W + 1) := by
  refine ⟨Nat.mul_assoc .., ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Nat.add_mul, Nat.mul_assoc]

theorem sa_within (u : Nat) : Within (saP N W h u) "S" (u * (7 * (W + 1))) (7 * (W + 1)) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := lane_eqs u W
  intro a ha
  simp [saP, wS, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, _, _, rfl, by omega, by omega⟩

theorem tb_within (v : Nat) : Within (tbP N W h v) "T" (v * (7 * (W + 1))) (7 * (W + 1)) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := lane_eqs v W
  intro a ha
  simp [tbP, wT, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, _, _, rfl, by omega, by omega⟩

theorem mac_within (u v r : Nat) : Within (macP h W AccW u v r) "M" (((u * h + v) * 7 + r) * AccW) AccW := by
  intro a ha
  simp [macP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  rcases ha with rfl | rfl <;> exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem cP_within (lc : Nat) (e : Expr2) : Within (cP h AccW lc e) "C" lc AccW := by
  intro a ha
  simp [cP, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at ha
  subst ha
  exact ⟨rfl, _, _, rfl, Nat.le_refl _, Nat.le_refl _⟩

end windows

/-- The post-sum processes, as cells `(i, j)` of `C`. -/
def CAt (N AccW : Nat) (p : Process2) (i j : Nat) : Prop := Within p "C" ((i * N + j) * AccW) AccW ∧ j < N

theorem disj_C {N AccW : Nat} {p q : Process2} {i j i' j' : Nat} (hp : CAt N AccW p i j) (hq : CAt N AccW q i' j')
    (h : i ≠ i' ∨ j ≠ j') : Disj p q :=
  disj_ne hp.1 hq.1 (rm_ne hp.2 hq.2 h)

section cells
variable {N AccW h : Nat}

theorem c11_at (u v : Nat) (hv : v < h) (hhN : h ≤ N) : CAt N AccW (c11P N h AccW u v) u v :=
  ⟨cP_within AccW h _ _, by omega⟩
theorem c12_at (u v : Nat) (hv : v < N - h) : CAt N AccW (c12P N h AccW u v) u (h + v) :=
  ⟨by rw [show u * N + (h + v) = u * N + h + v by omega]; exact cP_within AccW h _ _, by omega⟩
theorem c21_at (u v : Nat) (hv : v < h) (hhN : h ≤ N) : CAt N AccW (c21P N h AccW u v) (h + u) v :=
  ⟨cP_within AccW h _ _, by omega⟩
theorem c22_at (u v : Nat) (hv : v < N - h) : CAt N AccW (c22P N h AccW u v) (h + u) (h + v) :=
  ⟨by rw [show (h + u) * N + (h + v) = (h + u) * N + h + v by omega]; exact cP_within AccW h _ _, by omega⟩

end cells

/-- A family over a grid `a × b` whose cells are pairwise disjoint when their coordinates differ. -/
theorem pairwise_grid {R : Process2 → Process2 → Prop} {a b : Nat} {P : Nat → Nat → Process2}
    (h : ∀ u v u' v', u < a → v < b → u' < a → v' < b → (u ≠ u' ∨ v ≠ v') → R (P u v) (P u' v')) :
    ((List.range a).flatMap fun u => (List.range b).map (P u)).Pairwise R := by
  refine pairwise_flatMap_range (fun u hu => ?_) (fun u u' hlt hu' x hx y hy => ?_)
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun hv hv' hlt =>
      h _ _ _ _ hu (List.mem_range.mp hv) hu (List.mem_range.mp hv') (.inr (by omega)))
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v', hv', rfl⟩ := List.mem_map.mp hy
    exact h _ _ _ _ (by omega) (List.mem_range.mp hv) hu' (List.mem_range.mp hv') (.inl (by omega))

theorem st_pe_mem {W AccW h : Nat} {p : Process2} (hp : p ∈ macPs h W AccW) :
    ∃ u v r, u < h ∧ v < h ∧ r < 7 ∧ p = macP h W AccW u v r := by
  simp only [macPs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨u, hu, v, hv, r, hr, rfl⟩ := hp
  exact ⟨u, v, r, hu, hv, hr, rfl⟩

theorem grid_mem {a b : Nat} {P : Nat → Nat → Process2} {p : Process2}
    (hp : p ∈ (List.range a).flatMap fun u => (List.range b).map (P u)) : ∃ u v, u < a ∧ v < b ∧ p = P u v := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨u, hu, v, hv, rfl⟩ := hp
  exact ⟨u, v, hu, hv, rfl⟩

/-- `C`'s cell `(i, j)`: the post-sum process of its block. -/
def cPij (N h AccW i j : Nat) : Process2 :=
  if i < h then (if j < h then c11P N h AccW i j else c12P N h AccW i (j - h))
  else (if j < h then c21P N h AccW (i - h) j else c22P N h AccW (i - h) (j - h))

theorem range_split {h N : Nat} (hle : h ≤ N) : List.range N = List.range h ++ (List.range (N - h)).map (h + ·) := by
  have := @List.range_add h (N - h)
  rwa [show h + (N - h) = N by omega] at this

/-- A row-indexed family over `[0, N)` split at `h`. -/
theorem flatMap_split {α : Type} {h N : Nat} (hle : h ≤ N) (f : Nat → List α) :
    (List.range N).flatMap f = (List.range h).flatMap f ++ (List.range (N - h)).flatMap fun u => f (h + u) := by
  rw [range_split hle, List.flatMap_append, List.flatMap_map]

theorem map_split {α : Type} {h N : Nat} (hle : h ≤ N) (f : Nat → α) :
    (List.range N).map f = (List.range h).map f ++ (List.range (N - h)).map fun u => f (h + u) := by
  rw [range_split hle, List.map_append, List.map_map]; rfl

/-- **The post-sum processes are `C`'s cells, row by row.** -/
theorem cPs_eq (N h AccW : Nat) (hle : h ≤ N) :
    cPs N h AccW = (List.range N).flatMap fun i => (List.range N).map (cPij N h AccW i) := by
  rw [flatMap_split hle, cPs, cTop, cBot]
  congr 1
  · refine CombView.flatMap_congr' fun u hu => ?_
    have hu := List.mem_range.mp hu
    rw [map_split hle]
    congr 1
    · exact List.map_congr_left fun v hv => by have := List.mem_range.mp hv; simp [cPij, hu, this]
    · exact List.map_congr_left fun v hv => by simp [cPij, hu, show ¬ h + v < h by omega]
  · refine CombView.flatMap_congr' fun u hu => ?_
    rw [map_split hle]
    congr 1
    · exact List.map_congr_left fun v hv => by
        have := List.mem_range.mp hv; simp [cPij, this, show ¬ h + u < h by omega]
    · exact List.map_congr_left fun v hv => by
        simp [cPij, show ¬ h + u < h by omega, show ¬ h + v < h by omega]

theorem cPij_at {N h AccW i j : Nat} (hhN : h ≤ N) (h2N : N ≤ 2 * h) (hi : i < N) (hj : j < N) :
    CAt N AccW (cPij N h AccW i j) i j := by
  unfold cPij
  by_cases h1 : i < h <;> by_cases h2 : j < h <;> simp only [h1, h2, if_true, if_false]
  · exact c11_at i j h2 hhN
  · have := c12_at (N := N) (AccW := AccW) (h := h) i (j - h) (by omega); rwa [show h + (j - h) = j by omega] at this
  · have := c21_at (N := N) (AccW := AccW) (h := h) (i - h) j h2 hhN; rwa [show h + (i - h) = i by omega] at this
  · have := c22_at (N := N) (AccW := AccW) (h := h) (i - h) (j - h) (by omega)
    rwa [show h + (i - h) = i by omega, show h + (j - h) = j by omega] at this

theorem st_pairwise (N W AccW h : Nat) (hhN : h ≤ N) (h2N : N ≤ 2 * h) :
    (ctrlP N W h :: genPs N W AccW h).Pairwise Disj := by
  have hsa : ∀ p ∈ saPs N W h, Names p ["S"] := by
    intro p hp; obtain ⟨u, -, rfl⟩ := List.mem_map.mp hp; exact names_of_within (sa_within N W h u)
  have htb : ∀ p ∈ tbPs N W h, Names p ["T"] := by
    intro p hp; obtain ⟨v, -, rfl⟩ := List.mem_map.mp hp; exact names_of_within (tb_within N W h v)
  have hmac : ∀ p ∈ macPs h W AccW, Names p ["M"] := by
    intro p hp; obtain ⟨u, v, r, -, -, -, rfl⟩ := st_pe_mem hp; exact names_of_within (mac_within W AccW h u v r)
  have hC : ∀ p ∈ cPs N h AccW, Names p ["C"] := by
    intro p hp
    rw [cPs_eq N h AccW hhN] at hp
    obtain ⟨i, j, hi, hj, rfl⟩ := grid_mem hp
    exact names_of_within (cPij_at hhN h2N hi hj).1
  have hgen : ∀ p ∈ genPs N W AccW h, Names p ["S", "T", "M", "C"] := by
    intro p hp a ha
    simp only [genPs, List.mem_append] at hp
    rcases hp with ((hp | hp) | hp) | hp
    · have := hsa p hp a ha; simp_all
    · have := htb p hp a ha; simp_all
    · have := hmac p hp a ha; simp_all
    · have := hC p hp a ha; simp_all
  refine .cons (fun q hq => disj_of_names (ctrl_names N W h) (hgen q hq) (by decide)) ?_
  simp only [genPs, List.pairwise_append]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hxy =>
      disj_ne (sa_within N W h _) (sa_within N W h _) (by omega))
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ hxy =>
      disj_ne (tb_within N W h _) (tb_within N W h _) (by omega))
  · intro p hp q hq; exact disj_of_names (hsa p hp) (htb q hq) (by decide)
  · refine pairwise_flatMap_range (fun u hu => pairwise_grid fun v r v' r' hv hr hv' hr' hne => ?_)
      (fun u u' huu hu' x hx y hy => ?_)
    · refine disj_ne (mac_within W AccW h u v r) (mac_within W AccW h u v' r') (rm_ne hr hr' ?_)
      rcases hne with hne | hne
      · exact .inl (rm_ne hv hv' (.inr hne))
      · exact .inr hne
    · obtain ⟨v, r, hv, hr, rfl⟩ := grid_mem hx
      obtain ⟨v', r', hv', hr', rfl⟩ := grid_mem hy
      exact disj_ne (mac_within W AccW h u v r) (mac_within W AccW h u' v' r')
        (rm_ne hr hr' (.inl (rm_ne hv hv' (.inl (by omega)))))
  · intro p hp q hq
    simp only [List.mem_append] at hp
    rcases hp with hp | hp
    · exact disj_of_names (hsa p hp) (hmac q hq) (by decide)
    · exact disj_of_names (htb p hp) (hmac q hq) (by decide)
  · rw [cPs_eq N h AccW hhN]
    exact pairwise_grid fun i j i' j' hi hj hi' hj' hne =>
      disj_C (cPij_at hhN h2N hi hj) (cPij_at hhN h2N hi' hj') hne
  · intro p hp q hq
    have := hC q hq
    simp only [List.mem_append] at hp
    rcases hp with ((hp | hp) | hp)
    · exact disj_of_names (hsa p hp) this (by decide)
    · exact disj_of_names (htb p hp) this (by decide)
    · exact disj_of_names (hmac p hp) this (by decide)

/-! ### The one-driver rule, agreement, the profile -/

theorem st_mem {N W AccW h : Nat} {p : Process2} (hp : p ∈ ctrlP N W h :: genPs N W AccW h) :
    p = ctrlP N W h ∨ (∃ u, p = saP N W h u) ∨ (∃ v, p = tbP N W h v) ∨ (∃ u v r, p = macP h W AccW u v r) ∨
      (∃ u v, p = c11P N h AccW u v) ∨ (∃ u v, p = c12P N h AccW u v) ∨ (∃ u v, p = c21P N h AccW u v) ∨
      ∃ u v, p = c22P N h AccW u v := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact .inl rfl
  simp only [genPs, cPs, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp | hp
  · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hp; exact .inr (.inl ⟨u, rfl⟩)
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hp; exact .inr (.inr (.inl ⟨v, rfl⟩))
  · obtain ⟨u, v, r, -, -, -, rfl⟩ := st_pe_mem hp; exact .inr (.inr (.inr (.inl ⟨u, v, r, rfl⟩)))
  · simp only [cTop, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range] at hp
    obtain ⟨u, -, (⟨v, -, rfl⟩ | ⟨v, -, rfl⟩)⟩ := hp
    · exact .inr (.inr (.inr (.inr (.inl ⟨u, v, rfl⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨u, v, rfl⟩)))))
  · simp only [cBot, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range] at hp
    obtain ⟨u, -, (⟨v, -, rfl⟩ | ⟨v, -, rfl⟩)⟩ := hp
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨u, v, rfl⟩))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨u, v, rfl⟩))))))

theorem st_driversOk (N W AccW h : Nat) (hhN : h ≤ N) (h2N : N ≤ 2 * h) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (ctrlP N W h :: genPs N W AccW h) = true := by
  apply driversOk_of_ff ?_ ?_ (st_pairwise N W AccW h hhN h2N)
  · intro p hp
    rcases st_mem hp with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, r, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ |
      ⟨u, v, rfl⟩ <;> exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap]
    rintro n ⟨p, hp, hn⟩
    rcases st_mem hp with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, r, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ |
      ⟨u, v, rfl⟩
    all_goals revert n; simp [ctrlP, saP, tbP, wS, wT, macP, cP, c11P, c12P, c21P, c22P, nb, Process2.procWrites,
      Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide

/-- **The loaded family is `stD`** (block size `⌈N/2⌉`), at every in-range `(N, W, AccW)`. -/
theorem st_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    design.sem N W AccW = stD N W AccW ((N + 1) / 2) := by
  obtain ⟨_, h2, h3⟩ := hh_facts N hN
  have h1 : design.sem N W AccW = design.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show design.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by
      rw [st_processes N W AccW hN hW hA hN31]; exact st_driversOk N W AccW _ h2 h3)
  rw [h1, PDesign.instantiateD2_of_ok (st_instantiate2 N W AccW hN hW hA hN31)]
  simp only [PDesign.assemble2, st_ctrl, stD]
  simp [design.pdesign]

/-! ## 2. The clock step -/

/-- **`stD` is in G0's FF-only profile.** -/
theorem st_profile (N W AccW h : Nat) (hhN : h ≤ N) (h2N : N ≤ 2 * h) : (stD N W AccW h).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simp only [stD, List.toList_toArray]; exact st_pairwise N W AccW h hhN h2N)⟩
  simp [stD, genPs, cPs, cTop, cBot, saPs, tbPs, macPs, ctrlP, saP, tbP, wS, wT, macP, cP, c11P, c12P, c21P, c22P,
    nb, List.all_flatMap, List.all_map, List.all_append, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly,
    Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?, Design2.declWidth,
    Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, stDecls]

/-- The 14 signals of `stD`, in declaration order. -/
def SS (ck r s a b dn c t bz ash bsh sr tr m : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("t", t), ("busy", bz),
    ("a_sh", ash), ("b_sh", bsh), ("S", sr), ("T", tr), ("M", m)]

theorem apply_st (N W AccW h : Nat) (e : SvState) (ck r s a b dn c t bz ash bsh sr tr m : LVec) :
    applyInputs2 (stD N W AccW h) e (SS ck r s a b dn c t bz ash bsh sr tr m) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c t bz ash bsh sr tr m := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [stD, stDecls, SS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- The test `t == H + 1`. -/
abbrev lastB (h : Nat) (t : LVec) : Bool :=
  (LVec.ofLogic (t.eqLogical ((LVec.ofInt 32 (h : Int)).add (LVec.ofInt 32 1)))).condTrue

/-- The test `t == 0`. -/
abbrev zeroB (t : LVec) : Bool := (LVec.ofLogic (t.eqLogical (LVec.ofInt 32 0))).condTrue

def ctrlQ (N W h : Nat) (r s a b dn t bz ash bsh : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0),
    wr "a_sh" ash (a.resizeU ((2 * h + 1) * N * W)), wr "b_sh" bsh (b.resizeU ((2 * h + 1) * N * W))]
  else if bz.condTrue then
    if lastB h t then
      [wr "t" t (t.add (LVec.ofInt 32 1)), wr "a_sh" ash (ash.shr (LVec.ofInt 32 (W : Int))),
        wr "b_sh" bsh (bsh.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))),
        wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
    else [wr "t" t (t.add (LVec.ofInt 32 1)), wr "a_sh" ash (ash.shr (LVec.ofInt 32 (W : Int))),
        wr "b_sh" bsh (bsh.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))]
  else []

/-- `{x[p*W + W-1], x[p*W +: W]}`, evaluated. -/
def sxV (x : LVec) (W p : Nat) : LVec := LVec.concatMany #[x.extract (p * W + W - 1) 1, x.extract (p * W) W]

/-- The A-side pre-sum of lane `r`, evaluated. -/
def preV (r : Nat) (x11 x12 x21 x22 : LVec) : LVec :=
  match r with
  | 0 => x11.add x22
  | 1 => x21.add x22
  | 2 => x11
  | 3 => x22
  | 4 => x11.add x12
  | 5 => x21.sub x11
  | _ => x12.sub x22

/-- The B-side pre-sum of lane `r`, evaluated. -/
def preW (r : Nat) (y11 y12 y21 y22 : LVec) : LVec :=
  match r with
  | 0 => y11.add y22
  | 1 => y11
  | 2 => y12.sub y22
  | 3 => y21.sub y11
  | 4 => y22
  | 5 => y11.add y12
  | _ => y21.add y22

/-- Lane `r` of the A-side pre-sums of row `u`: its write. -/
def saL (N W h : Nat) (ash : LVec) (u r : Nat) : String × Nat × LVec :=
  ("S", (u * 7 + r) * (W + 1), (preV r (sxV ash W (u * N)) (sxV ash W (u * N + h)) (sxV ash W ((h + u) * N))
    (sxV ash W ((h + u) * N + h))).resizeU (W + 1))

/-- Lane `r` of the B-side pre-sums of column `v`: its write. -/
def tbL (N W h : Nat) (bsh : LVec) (v r : Nat) : String × Nat × LVec :=
  ("T", (v * 7 + r) * (W + 1), (preW r (sxV bsh W v) (sxV bsh W (h + v)) (sxV bsh W (h * N + v))
    (sxV bsh W (h * N + h + v))).resizeU (W + 1))

def saQ (N W h : Nat) (bz ash : LVec) (u : Nat) : NbaQueue2 :=
  if bz.condTrue then [saL N W h ash u 0, saL N W h ash u 1, saL N W h ash u 2, saL N W h ash u 3,
    saL N W h ash u 4, saL N W h ash u 5, saL N W h ash u 6] else []

def tbQ (N W h : Nat) (bz bsh : LVec) (v : Nat) : NbaQueue2 :=
  if bz.condTrue then [tbL N W h bsh v 0, tbL N W h bsh v 1, tbL N W h bsh v 2, tbL N W h bsh v 3,
    tbL N W h bsh v 4, tbL N W h bsh v 5, tbL N W h bsh v 6] else []

/-- `{{AccW{x[b]}}, x[lo +: w]}`, evaluated. -/
def sxAV (x : LVec) (AccW b lo w : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[x.extract b 1]), x.extract lo w]

/-- The new value of engine `r`'s cell `(u, v)` in an accumulating cycle, evaluated. -/
def macV (h W AccW : Nat) (m sr tr : LVec) (u v r : Nat) : LVec :=
  (((m.extract (((u * h + v) * 7 + r) * AccW) AccW).resizeU (AccW + (W + 1))).add
    ((sxAV sr AccW ((u * 7 + r) * (W + 1) + W) ((u * 7 + r) * (W + 1)) (W + 1)).mul
      (sxAV tr AccW ((v * 7 + r) * (W + 1) + W) ((v * 7 + r) * (W + 1)) (W + 1)))).resizeU AccW

def macQ (h W AccW : Nat) (bz t m sr tr : LVec) (u v r : Nat) : NbaQueue2 :=
  if bz.condTrue then
    if zeroB t then [("M", ((u * h + v) * 7 + r) * AccW, (LVec.replicate AccW .l0).resizeU AccW)]
    else [("M", ((u * h + v) * 7 + r) * AccW, (macV h W AccW m sr tr u v r).resizeU AccW)]
  else []

/-- Engine lane `r` of cell `(u, v)`, read. -/
def mV (h AccW : Nat) (m : LVec) (u v r : Nat) : LVec := m.extract (((u * h + v) * 7 + r) * AccW) AccW

def v11 (h AccW : Nat) (m : LVec) (u v : Nat) : LVec :=
  (((mV h AccW m u v 0).add (mV h AccW m u v 3)).sub (mV h AccW m u v 4)).add (mV h AccW m u v 6)
def v12 (h AccW : Nat) (m : LVec) (u v : Nat) : LVec := (mV h AccW m u v 2).add (mV h AccW m u v 4)
def v21 (h AccW : Nat) (m : LVec) (u v : Nat) : LVec := (mV h AccW m u v 1).add (mV h AccW m u v 3)
def v22 (h AccW : Nat) (m : LVec) (u v : Nat) : LVec :=
  (((mV h AccW m u v 0).sub (mV h AccW m u v 1)).add (mV h AccW m u v 2)).add (mV h AccW m u v 5)

def cQ (h AccW : Nat) (bz t : LVec) (lc : Nat) (val : LVec) : NbaQueue2 :=
  if bz.condTrue then (if lastB h t then [("C", lc, val.resizeU AccW)] else []) else []

/-- `C`'s cell `(i, j)`: its update. -/
def cQij (N h AccW : Nat) (bz t m : LVec) (i j : Nat) : NbaQueue2 :=
  if i < h then
    (if j < h then cQ h AccW bz t ((i * N + j) * AccW) (v11 h AccW m i j)
     else cQ h AccW bz t ((i * N + h + (j - h)) * AccW) (v12 h AccW m i (j - h)))
  else
    (if j < h then cQ h AccW bz t (((h + (i - h)) * N + j) * AccW) (v21 h AccW m (i - h) j)
     else cQ h AccW bz t (((h + (i - h)) * N + h + (j - h)) * AccW) (v22 h AccW m (i - h) (j - h)))

section run
variable (F : Nat) (hF : 40 ≤ F) (ck r s a b dn c t bz ash bsh sr tr m : LVec)
include hF

theorem ctrl_run (N W h : Nat) : runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (ctrlP N W h) =
    .ok (SS ck r s a b dn c t bz ash bsh sr tr m, ctrlQ N W h r s a b dn t bz ash bsh) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : lastB h t = true <;>
    simp [ctrlP, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, SS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem sa_run (N W h u : Nat) : runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (saP N W h u) =
    .ok (SS ck r s a b dn c t bz ash bsh sr tr m, saQ N W h bz ash u) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold saQ
  by_cases h1 : bz.condTrue = true <;>
    simp [saP, wS, preE, sx1, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, saL, preV, sxV, h1]

theorem tb_run (N W h v : Nat) : runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (tbP N W h v) =
    .ok (SS ck r s a b dn c t bz ash bsh sr tr m, tbQ N W h bz bsh v) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold tbQ
  by_cases h1 : bz.condTrue = true <;>
    simp [tbP, wT, preF, sx1, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, tbL, preW, sxV, h1]

theorem mac_run (h W AccW u v k : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (macP h W AccW u v k) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m, macQ h W AccW bz t m sr tr u v k) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold macQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : zeroB t = true <;>
    simp [macP, sxA, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, macV, sxAV, h1, h2]

theorem c11_run (N h AccW u v : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (c11P N h AccW u v) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m, cQ h AccW bz t ((u * N + v) * AccW) (v11 h AccW m u v)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold cQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : lastB h t = true <;>
    simp [c11P, cP, e11, mS, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, v11, mV, h1, h2]

theorem c12_run (N h AccW u v : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (c12P N h AccW u v) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m, cQ h AccW bz t ((u * N + h + v) * AccW) (v12 h AccW m u v)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold cQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : lastB h t = true <;>
    simp [c12P, cP, e12, mS, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, v12, mV, h1, h2]

theorem c21_run (N h AccW u v : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (c21P N h AccW u v) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m, cQ h AccW bz t (((h + u) * N + v) * AccW) (v21 h AccW m u v)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold cQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : lastB h t = true <;>
    simp [c21P, cP, e21, mS, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, v21, mV, h1, h2]

theorem c22_run (N h AccW u v : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (c22P N h AccW u v) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m,
        cQ h AccW bz t (((h + u) * N + h + v) * AccW) (v22 h AccW m u v)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 40 := ⟨F - 40, by omega⟩
  unfold cQ
  by_cases h1 : bz.condTrue = true <;> by_cases h2 : lastB h t = true <;>
    simp [c22P, cP, e22, mS, c32, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, v22, mV, h1, h2]

theorem cPij_run (N h AccW i j : Nat) :
    runEdgeProcess2 F (SS ck r s a b dn c t bz ash bsh sr tr m) [] (cPij N h AccW i j) =
      .ok (SS ck r s a b dn c t bz ash bsh sr tr m, cQij N h AccW bz t m i j) := by
  unfold cPij cQij
  by_cases h1 : i < h <;> by_cases h2 : j < h <;> simp only [h1, h2, if_true, if_false]
  · exact c11_run F hF .. 
  · exact c12_run F hF ..
  · exact c21_run F hF ..
  · exact c22_run F hF ..

end run

/-- The cycle's updates, in process order. -/
def Q (N W AccW h : Nat) (r s a b dn t bz ash bsh sr tr m : LVec) : NbaQueue2 :=
  ctrlQ N W h r s a b dn t bz ash bsh ++
    ((List.range h).flatMap (saQ N W h bz ash) ++
      ((List.range h).flatMap (tbQ N W h bz bsh) ++
        (((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
            (macQ h W AccW bz t m sr tr u v)) ++
          (List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i))))

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def stNext (N W AccW h : Nat) (ck r s a b dn c t bz ash bsh sr tr m : LVec) : SvState :=
  commitNba2 (SS ck r s a b dn c t bz ash bsh sr tr m) (Q N W AccW h r s a b dn t bz ash bsh sr tr m)

theorem st_cycle_hand (N W AccW h : Nat) (hhN : h ≤ N) (h2N : N ≤ 2 * h) (σ : ScheduleOracle) (e : SvState)
    (ck r s a b dn c t bz ash bsh sr tr m : LVec) (kk F : Nat) (hF : 40 ≤ F) :
    cycleStep2 (stD N W AccW h) σ F e (SS ck r s a b dn c t bz ash bsh sr tr m) kk =
      .ok (stNext N W AccW h (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c t bz ash bsh sr tr m, kk + 3) := by
  have hmem : ∀ p ∈ (stD N W AccW h).processes.toList, p ∈ ctrlP N W h :: genPs N W AccW h := by
    intro p hp; simpa [stD] using hp
  have hedge : ∀ p ∈ (stD N W AccW h).processes.toList, p.isEdgePhase = true := by
    intro p hp
    rcases st_mem (hmem p hp) with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, r, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ |
      ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ <;> rfl
  rw [cycleStep2_profile (st_profile N W AccW h hhN h2N) σ e _ kk ?_ ?_ (by omega), apply_st, clockStep,
    flatMap_ffUpd F _ hedge]
  · simp only [stD, List.toList_toArray, genPs, cPs_eq N h AccW hhN, saPs, tbPs, macPs, List.flatMap_cons,
      List.flatMap_append, List.flatMap_map, List.flatMap_assoc, ctrl_run F hF, sa_run F hF, tb_run F hF,
      mac_run F hF, cPij_run F hF, stNext, Q, List.append_assoc]
  · intro i p hp
    rw [apply_st]
    have hm : p ∈ ctrlP N W h :: genPs N W AccW h := List.mem_of_getElem? (by simpa [stD] using hp)
    rcases st_mem hm with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, k, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ |
      ⟨u, v, rfl⟩
    · exact ⟨_, ctrl_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W h⟩
    · exact ⟨_, sa_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W h u⟩
    · exact ⟨_, tb_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N W h v⟩
    · exact ⟨_, mac_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ h W AccW u v k⟩
    · exact ⟨_, c11_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N h AccW u v⟩
    · exact ⟨_, c12_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N h AccW u v⟩
    · exact ⟨_, c21_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N h AccW u v⟩
    · exact ⟨_, c22_run F hF _ _ _ _ _ _ _ _ _ _ _ _ _ _ N h AccW u v⟩
  · rw [apply_st]; simp [SS]

/-- **One cycle of the loaded design is G0's clock step** (any schedule, any stimulus entry, any state of the
shape `SS`, every fuel from 40). -/
theorem st_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31)
    (σ : ScheduleOracle) (e : SvState) (ck r s a b dn c t bz ash bsh sr tr m : LVec) (kk F : Nat) (hF : 40 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (SS ck r s a b dn c t bz ash bsh sr tr m) kk =
      .ok (stNext N W AccW ((N + 1) / 2) (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c t bz ash bsh sr tr m, kk + 3) := by
  obtain ⟨_, h2, h3⟩ := hh_facts N hN
  rw [st_sem_eq N W AccW hN hW hA hN31]
  exact st_cycle_hand N W AccW _ h2 h3 σ e ck r s a b dn c t bz ash bsh sr tr m kk F hF

/-! ## 3. The commit, register by register -/

section commit
variable {ck r s a b dn c t bz ash bsh sr tr m : LVec} {lo : Nat} {v : LVec}
theorem nb_dn : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("done", lo, v) =
    SS ck r s a b (dn.insertAt lo v) c t bz ash bsh sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_c : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("C", lo, v) =
    SS ck r s a b dn (c.insertAt lo v) t bz ash bsh sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_t : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("t", lo, v) =
    SS ck r s a b dn c (t.insertAt lo v) bz ash bsh sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_bz : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("busy", lo, v) =
    SS ck r s a b dn c t (bz.insertAt lo v) ash bsh sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_ash : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("a_sh", lo, v) =
    SS ck r s a b dn c t bz (ash.insertAt lo v) bsh sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_bsh : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("b_sh", lo, v) =
    SS ck r s a b dn c t bz ash (bsh.insertAt lo v) sr tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_sr : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("S", lo, v) =
    SS ck r s a b dn c t bz ash bsh (sr.insertAt lo v) tr m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_tr : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("T", lo, v) =
    SS ck r s a b dn c t bz ash bsh sr (tr.insertAt lo v) m := by simp [nbaStep, SS, SvState.lookup, SvState.set]
theorem nb_m : nbaStep (SS ck r s a b dn c t bz ash bsh sr tr m) ("M", lo, v) =
    SS ck r s a b dn c t bz ash bsh sr tr (m.insertAt lo v) := by simp [nbaStep, SS, SvState.lookup, SvState.set]
end commit

/-- The nine registers. -/
abbrev RegName (n : String) : Prop :=
  n = "done" ∨ n = "C" ∨ n = "t" ∨ n = "busy" ∨ n = "a_sh" ∨ n = "b_sh" ∨ n = "S" ∨ n = "T" ∨ n = "M"

/-- Committing a queue of writes to the nine registers. -/
theorem commit_SS {ck r s a b : LVec} : ∀ (q : NbaQueue2) (dn c t bz ash bsh sr tr m : LVec),
    (∀ u ∈ q, RegName u.1) →
    commitNba2 (SS ck r s a b dn c t bz ash bsh sr tr m) q =
      SS ck r s a b (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "t" q t) (nbaFold "busy" q bz)
        (nbaFold "a_sh" q ash) (nbaFold "b_sh" q bsh) (nbaFold "S" q sr) (nbaFold "T" q tr) (nbaFold "M" q m)
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | ⟨n, lo, v⟩ :: q, dn, c, t, bz, ash, bsh, sr, tr, m, h => by
    have hq := @commit_SS ck r s a b q
    have h' := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp only at h1 <;>
      subst h1 <;>
      simp [commitNba2_cons, nb_dn, nb_c, nb_t, nb_bz, nb_ash, nb_bsh, nb_sr, nb_tr, nb_m,
        hq _ _ _ _ _ _ _ _ _ h', nbaFold]

/-- A queue that writes no `n` leaves `n`. -/
theorem nbaFold_of_forall_ne {n : String} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 ≠ n) → ∀ x, nbaFold n q x = x
  | [], _, _ => rfl
  | u :: q, h, x => by
    have h1 := h u List.mem_cons_self
    simp only [nbaFold, List.foldl_cons, if_neg h1]
    exact nbaFold_of_forall_ne (fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) x

section names
variable {N W AccW h : Nat} {r s a b dn c t bz ash bsh sr tr m : LVec}

theorem ctrlQ_names : ∀ u ∈ ctrlQ N W h r s a b dn t bz ash bsh,
    u.1 = "busy" ∨ u.1 = "done" ∨ u.1 = "t" ∨ u.1 = "a_sh" ∨ u.1 = "b_sh" := by
  intro u hu; unfold ctrlQ at hu; (repeat' split at hu) <;> simp at hu <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
theorem saQ_names (u' : Nat) : ∀ u ∈ saQ N W h bz ash u', u.1 = "S" := by
  intro u hu; unfold saQ at hu; split at hu <;> simp [saL] at hu <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem tbQ_names (v' : Nat) : ∀ u ∈ tbQ N W h bz bsh v', u.1 = "T" := by
  intro u hu; unfold tbQ at hu; split at hu <;> simp [tbL] at hu <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem macQ_names (u' v' k : Nat) : ∀ u ∈ macQ h W AccW bz t m sr tr u' v' k, u.1 = "M" := by
  intro u hu; unfold macQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl
theorem cQij_names (i j : Nat) : ∀ u ∈ cQij N h AccW bz t m i j, u.1 = "C" := by
  intro u hu; unfold cQij cQ at hu; (repeat' split at hu) <;> simp at hu <;> subst hu <;> rfl

theorem Q_names : ∀ u ∈ Q N W AccW h r s a b dn t bz ash bsh sr tr m, RegName u.1 := by
  intro u hu
  simp only [Q, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with hu | ⟨k, -, hu⟩ | ⟨k, -, hu⟩ | ⟨i, -, j, -, k, -, hu⟩ | ⟨i, -, j, -, hu⟩
  · rcases ctrlQ_names u hu with h | h | h | h | h <;> rw [h] <;> simp [RegName]
  · rw [saQ_names k u hu]; simp [RegName]
  · rw [tbQ_names k u hu]; simp [RegName]
  · rw [macQ_names i j k u hu]; simp [RegName]
  · rw [cQij_names i j u hu]; simp [RegName]

theorem skip_ctrl {n : String} (h1 : n ≠ "busy") (h2 : n ≠ "done") (h3 : n ≠ "t") (h4 : n ≠ "a_sh")
    (h5 : n ≠ "b_sh") (x : LVec) : nbaFold n (ctrlQ N W h r s a b dn t bz ash bsh) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    rcases ctrlQ_names u hu with e | e | e | e | e <;> rw [e] at h' <;> subst h' <;> contradiction) x
theorem skip_sa {n : String} (hn : n ≠ "S") (x : LVec) :
    nbaFold n ((List.range h).flatMap (saQ N W h bz ash)) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    simp only [List.mem_flatMap] at hu
    obtain ⟨k, -, hu⟩ := hu
    exact hn (h'.symm.trans (saQ_names k u hu))) x
theorem skip_tb {n : String} (hn : n ≠ "T") (x : LVec) :
    nbaFold n ((List.range h).flatMap (tbQ N W h bz bsh)) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    simp only [List.mem_flatMap] at hu
    obtain ⟨k, -, hu⟩ := hu
    exact hn (h'.symm.trans (tbQ_names k u hu))) x
theorem skip_mac {n : String} (hn : n ≠ "M") (x : LVec) :
    nbaFold n ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW bz t m sr tr u v)) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    simp only [List.mem_flatMap] at hu
    obtain ⟨i, -, j, -, k, -, hu⟩ := hu
    exact hn (h'.symm.trans (macQ_names i j k u hu))) x
theorem skip_c {n : String} (hn : n ≠ "C") (x : LVec) :
    nbaFold n ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i)) x = x :=
  nbaFold_of_forall_ne (fun u hu h' => by
    simp only [List.mem_flatMap] at hu
    obtain ⟨i, -, j, -, hu⟩ := hu
    exact hn (h'.symm.trans (cQij_names i j u hu))) x

/-- The control's registers: only `ctrlQ` writes them. -/
theorem fold_ctrl (n : String) (h1 : n ≠ "S" := by decide) (h2 : n ≠ "T" := by decide) (h3 : n ≠ "M" := by decide)
    (h4 : n ≠ "C" := by decide) (x : LVec) :
    nbaFold n (Q N W AccW h r s a b dn t bz ash bsh sr tr m) x = nbaFold n (ctrlQ N W h r s a b dn t bz ash bsh) x := by
  simp only [Q, nbaFold_append, skip_sa h1, skip_tb h2, skip_mac h3, skip_c h4]

theorem fold_S (x : LVec) : nbaFold "S" (Q N W AccW h r s a b dn t bz ash bsh sr tr m) x =
    nbaFold "S" ((List.range h).flatMap (saQ N W h bz ash)) x := by
  simp only [Q, nbaFold_append, skip_ctrl (n := "S") (by decide) (by decide) (by decide) (by decide) (by decide),
    skip_tb (n := "S") (by decide), skip_mac (n := "S") (by decide), skip_c (n := "S") (by decide)]

theorem fold_T (x : LVec) : nbaFold "T" (Q N W AccW h r s a b dn t bz ash bsh sr tr m) x =
    nbaFold "T" ((List.range h).flatMap (tbQ N W h bz bsh)) x := by
  simp only [Q, nbaFold_append, skip_ctrl (n := "T") (by decide) (by decide) (by decide) (by decide) (by decide),
    skip_sa (n := "T") (by decide), skip_mac (n := "T") (by decide), skip_c (n := "T") (by decide)]

theorem fold_M (x : LVec) : nbaFold "M" (Q N W AccW h r s a b dn t bz ash bsh sr tr m) x =
    nbaFold "M" ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW bz t m sr tr u v)) x := by
  simp only [Q, nbaFold_append, skip_ctrl (n := "M") (by decide) (by decide) (by decide) (by decide) (by decide),
    skip_sa (n := "M") (by decide), skip_tb (n := "M") (by decide), skip_c (n := "M") (by decide)]

theorem fold_C (x : LVec) : nbaFold "C" (Q N W AccW h r s a b dn t bz ash bsh sr tr m) x =
    nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i)) x := by
  simp only [Q, nbaFold_append, skip_ctrl (n := "C") (by decide) (by decide) (by decide) (by decide) (by decide),
    skip_sa (n := "C") (by decide), skip_tb (n := "C") (by decide), skip_mac (n := "C") (by decide)]

end names

/-- The next state, register by register. -/
theorem stNext_eq (N W AccW h : Nat) (ck r s a b dn c t bz ash bsh sr tr m : LVec) :
    stNext N W AccW h ck r s a b dn c t bz ash bsh sr tr m =
      SS ck r s a b (nbaFold "done" (ctrlQ N W h r s a b dn t bz ash bsh) dn)
        (nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i)) c)
        (nbaFold "t" (ctrlQ N W h r s a b dn t bz ash bsh) t) (nbaFold "busy" (ctrlQ N W h r s a b dn t bz ash bsh) bz)
        (nbaFold "a_sh" (ctrlQ N W h r s a b dn t bz ash bsh) ash)
        (nbaFold "b_sh" (ctrlQ N W h r s a b dn t bz ash bsh) bsh)
        (nbaFold "S" ((List.range h).flatMap (saQ N W h bz ash)) sr)
        (nbaFold "T" ((List.range h).flatMap (tbQ N W h bz bsh)) tr)
        (nbaFold "M" ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
          (macQ h W AccW bz t m sr tr u v)) m) := by
  rw [stNext, commit_SS _ _ _ _ _ _ _ _ _ _ Q_names, fold_ctrl "done", fold_C, fold_ctrl "t", fold_ctrl "busy",
    fold_ctrl "a_sh", fold_ctrl "b_sh", fold_S, fold_T, fold_M]

/-! ## 4. The arithmetic: Strassen's identities per contraction index, the padding -/

/-- `Σ_{w < n} f w`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_add (f g : Nat → Int) : ∀ n, sumTo (fun w => f w + g w) n = sumTo f n + sumTo g n
  | 0 => by simp [sumTo]
  | n + 1 => by simp only [sumTo, sumTo_add f g n]; omega

theorem sumTo_split (f : Nat → Int) (a : Nat) : ∀ b, sumTo f (a + b) = sumTo f a + sumTo (fun w => f (a + w)) b
  | 0 => by simp [sumTo]
  | b + 1 => by rw [← Nat.add_assoc]; simp only [sumTo, sumTo_split f a b]; omega

theorem foldl_eq_sumTo (f : Nat → Int) : ∀ n, (List.range n).foldl (fun acc k => acc + f k) 0 = sumTo f n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.foldl_append, foldl_eq_sumTo f n]; rfl

theorem id11 (a11 a12 a22 b11 b21 b22 : Int) :
    (a11 + a22) * (b11 + b22) + a22 * (b21 - b11) - (a11 + a12) * b22 + (a12 - a22) * (b21 + b22) =
      a11 * b11 + a12 * b21 := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]; omega
theorem id12 (a11 a12 b12 b22 : Int) : a11 * (b12 - b22) + (a11 + a12) * b22 = a11 * b12 + a12 * b22 := by
  simp only [Int.add_mul, Int.mul_sub]; omega
theorem id21 (a21 a22 b11 b21 : Int) : (a21 + a22) * b11 + a22 * (b21 - b11) = a21 * b11 + a22 * b21 := by
  simp only [Int.add_mul, Int.mul_sub]; omega
theorem id22 (a11 a21 a22 b11 b12 b22 : Int) :
    (a11 + a22) * (b11 + b22) - (a21 + a22) * b11 + a11 * (b12 - b22) + (a21 - a11) * (b11 + b12) =
      a21 * b12 + a22 * b22 := by
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]; omega

/-- The padded matrices: entry `(i, k)` of `A`, `0` past the vector. -/
def Ah (N W : Nat) {n : Nat} (A : BitVec n) (i k : Nat) : Int := Tasks.Matmul.entry W A (i * N + k)
def Bh (N W : Nat) {n : Nat} (B : BitVec n) (k j : Nat) : Int := Tasks.Matmul.entry W B (k * N + j)

/-- The pre-sums as integers. -/
def preI (r : Nat) (x11 x12 x21 x22 : Int) : Int :=
  match r with
  | 0 => x11 + x22
  | 1 => x21 + x22
  | 2 => x11
  | 3 => x22
  | 4 => x11 + x12
  | 5 => x21 - x11
  | _ => x12 - x22

def preJ (r : Nat) (y11 y12 y21 y22 : Int) : Int :=
  match r with
  | 0 => y11 + y22
  | 1 => y11
  | 2 => y12 - y22
  | 3 => y21 - y11
  | 4 => y22
  | 5 => y11 + y12
  | _ => y21 + y22

/-- `S_{r+1}[u][w]` and `T_{r+1}[w][v]` of the padded blocks. -/
def sA (N W h : Nat) {n : Nat} (A : BitVec n) (r u w : Nat) : Int :=
  preI r (Ah N W A u w) (Ah N W A u (h + w)) (Ah N W A (h + u) w) (Ah N W A (h + u) (h + w))
def sB (N W h : Nat) {n : Nat} (B : BitVec n) (r w v : Nat) : Int :=
  preJ r (Bh N W B w v) (Bh N W B w (h + v)) (Bh N W B (h + w) v) (Bh N W B (h + w) (h + v))

/-- Engine `r`'s cell `(u, v)` after `k` steps: `Σ_{w < k} S_{r+1}[u][w] · T_{r+1}[w][v]`. -/
def msum (N W h : Nat) {n : Nat} (A B : BitVec n) (r u v k : Nat) : Int :=
  sumTo (fun w => sA N W h A r u w * sB N W h B r w v) k

section strassen
variable (N W h : Nat) {n : Nat} (A B : BitVec n)

theorem post11 (u v : Nat) : ∀ k, msum N W h A B 0 u v k + msum N W h A B 3 u v k - msum N W h A B 4 u v k +
    msum N W h A B 6 u v k = sumTo (fun w => Ah N W A u w * Bh N W B w v + Ah N W A u (h + w) * Bh N W B (h + w) v) k
  | 0 => by simp [msum, sumTo]
  | k + 1 => by
    have ih := post11 u v k
    have e := id11 (Ah N W A u k) (Ah N W A u (h + k)) (Ah N W A (h + u) (h + k)) (Bh N W B k v) (Bh N W B (h + k) v)
      (Bh N W B (h + k) (h + v))
    simp only [msum, sumTo, sA, sB, preI, preJ] at ih e ⊢
    omega

theorem post12 (u v : Nat) : ∀ k, msum N W h A B 2 u v k + msum N W h A B 4 u v k =
    sumTo (fun w => Ah N W A u w * Bh N W B w (h + v) + Ah N W A u (h + w) * Bh N W B (h + w) (h + v)) k
  | 0 => by simp [msum, sumTo]
  | k + 1 => by
    have ih := post12 u v k
    have e := id12 (Ah N W A u k) (Ah N W A u (h + k)) (Bh N W B k (h + v)) (Bh N W B (h + k) (h + v))
    simp only [msum, sumTo, sA, sB, preI, preJ] at ih e ⊢
    omega

theorem post21 (u v : Nat) : ∀ k, msum N W h A B 1 u v k + msum N W h A B 3 u v k =
    sumTo (fun w => Ah N W A (h + u) w * Bh N W B w v + Ah N W A (h + u) (h + w) * Bh N W B (h + w) v) k
  | 0 => by simp [msum, sumTo]
  | k + 1 => by
    have ih := post21 u v k
    have e := id21 (Ah N W A (h + u) k) (Ah N W A (h + u) (h + k)) (Bh N W B k v) (Bh N W B (h + k) v)
    simp only [msum, sumTo, sA, sB, preI, preJ] at ih e ⊢
    omega

theorem post22 (u v : Nat) : ∀ k, msum N W h A B 0 u v k - msum N W h A B 1 u v k + msum N W h A B 2 u v k +
    msum N W h A B 5 u v k =
    sumTo (fun w => Ah N W A (h + u) w * Bh N W B w (h + v) + Ah N W A (h + u) (h + w) * Bh N W B (h + w) (h + v)) k
  | 0 => by simp [msum, sumTo]
  | k + 1 => by
    have ih := post22 u v k
    have e := id22 (Ah N W A u k) (Ah N W A (h + u) k) (Ah N W A (h + u) (h + k)) (Bh N W B k v) (Bh N W B k (h + v))
      (Bh N W B (h + k) (h + v))
    simp only [msum, sumTo, sA, sB, preI, preJ] at ih e ⊢
    omega

end strassen

/-- The post-sum of `C`'s cell `(i, j)` from the engines after `k` steps. -/
def postI (N W h : Nat) {n : Nat} (A B : BitVec n) (i j k : Nat) : Int :=
  if i < h then
    (if j < h then msum N W h A B 0 i j k + msum N W h A B 3 i j k - msum N W h A B 4 i j k + msum N W h A B 6 i j k
     else msum N W h A B 2 i (j - h) k + msum N W h A B 4 i (j - h) k)
  else
    (if j < h then msum N W h A B 1 (i - h) j k + msum N W h A B 3 (i - h) j k
     else msum N W h A B 0 (i - h) (j - h) k - msum N W h A B 1 (i - h) (j - h) k +
       msum N W h A B 2 (i - h) (j - h) k + msum N W h A B 5 (i - h) (j - h) k)

/-- A part select past the end of a vector is zero. -/
theorem extractLsb'_past {n : Nat} (x : BitVec n) {start : Nat} (len : Nat) (h : n ≤ start) :
    x.extractLsb' start len = 0#len := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_of_ge x (start + i) (by omega)]

/-- **The post-sums are the task's dot products**: for `i, j < N`, with `N ≤ 2h ≤ N + 1`. -/
theorem post_dot {N W h : Nat} (A B : BitVec (N * N * W)) {i j : Nat} (hi : i < N) (hj : j < N) (hhN : h ≤ N)
    (h2N : N ≤ 2 * h) (h2N' : 2 * h ≤ N + 1) : postI N W h A B i j h = Tasks.Matmul.dot N W A B i j := by
  have hsum : postI N W h A B i j h = sumTo (fun k => Ah N W A i k * Bh N W B k j) (h + h) := by
    rw [sumTo_split, ← sumTo_add]
    unfold postI
    by_cases h1 : i < h <;> by_cases h2 : j < h <;> simp only [h1, h2, if_true, if_false]
    · exact post11 N W h A B i j h
    · have := post12 N W h A B i (j - h) h; rwa [show h + (j - h) = j by omega] at this
    · have := post21 N W h A B (i - h) j h; rwa [show h + (i - h) = i by omega] at this
    · have := post22 N W h A B (i - h) (j - h) h
      rwa [show h + (i - h) = i by omega, show h + (j - h) = j by omega] at this
  have hdot : Tasks.Matmul.dot N W A B i j = sumTo (fun k => Ah N W A i k * Bh N W B k j) N :=
    foldl_eq_sumTo (fun k => Ah N W A i k * Bh N W B k j) N
  rw [hsum, hdot]
  rcases (show h + h = N ∨ h + h = N + 1 by omega) with e | e
  · rw [e]
  · rw [e, sumTo]
    have hz : Bh N W B N j = 0 := by
      unfold Bh Tasks.Matmul.entry
      rw [extractLsb'_past _ _ (by rw [Nat.add_mul]; exact Nat.le_add_right _ _)]
      simp
    rw [hz, Int.mul_zero, Int.add_zero]

/-! ## 5. The registers through a cycle -/

attribute [local simp] condTrue_knownBit

section vals
variable (N W AccW h : Nat)

/-- The operand shift registers `t` steps after a start. -/
def ashV (A : BitVec (N * N * W)) (t : Nat) : BitVec ((2 * h + 1) * N * W) :=
  A.setWidth ((2 * h + 1) * N * W) >>> (t * W)
def bshV (B : BitVec (N * N * W)) (t : Nat) : BitVec ((2 * h + 1) * N * W) :=
  B.setWidth ((2 * h + 1) * N * W) >>> (t * (N * W))

/-- The pre-sum registers holding column `w`. -/
def Sv (A : BitVec (N * N * W)) (w : Nat) : BitVec (h * 7 * (W + 1)) :=
  packBV (W + 1) (h * 7) fun q => BitVec.ofInt (W + 1) (sA N W h A (q % 7) (q / 7) w)
def Tv (B : BitVec (N * N * W)) (w : Nat) : BitVec (h * 7 * (W + 1)) :=
  packBV (W + 1) (h * 7) fun q => BitVec.ofInt (W + 1) (sB N W h B (q % 7) w (q / 7))

/-- The engines after `k` steps. -/
def Mv (A B : BitVec (N * N * W)) (k : Nat) : BitVec (h * (h * 7) * AccW) :=
  packBV AccW (h * (h * 7)) fun q => BitVec.ofInt AccW (msum N W h A B (q % 7) (q / 7 / h) (q / 7 % h) k)

end vals

theorem rm_div {K a b : Nat} (hb : b < K) : (a * K + b) / K = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add]
theorem rm_mod {K a b : Nat} (hb : b < K) : (a * K + b) % K = b := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- A zero-extension reads like the original vector at every position. -/
theorem extractLsb'_setWidth_ge {n L : Nat} (x : BitVec n) (hL : n ≤ L) (lo len : Nat) :
    (x.setWidth L).extractLsb' lo len = x.extractLsb' lo len := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : lo + i < L
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x (lo + i) (by omega)]

/-- `{y[lo+W-1], y[lo +: W]}` is the entry sign-extended by one bit. -/
theorem bitcat_signExtend {n W : Nat} (hW : 1 ≤ W) (y : BitVec n) (lo : Nat) :
    LVec.ofBitVec (y.extractLsb' (lo + W - 1) 1 ++ y.extractLsb' lo W) =
      LVec.ofBitVec ((y.extractLsb' lo W).signExtend (W + 1)) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [Nat.add_comm], fun i hi => ?_⟩
  rw [LVec.getElem?_ofBitVec, if_pos (by omega)]
  congr 2
  rw [BitVec.getLsbD_append, BitVec.getLsbD_signExtend]
  by_cases h : i < W
  · simp [h, show i < W + 1 by omega]
  · have hiW : i = W := by omega
    subst hiW
    simp [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb', show i - 1 < i by omega,
      show lo + i - 1 = lo + (i - 1) by omega]

/-- A head of a shifted operand register, sign-extended by one bit. -/
theorem sxV_shr {n W : Nat} (hW : 1 ≤ W) (x : BitVec n) (sh p : Nat) (hp : p * W + W ≤ n) :
    sxV (LVec.ofBitVec (x >>> sh)) W p = LVec.ofBitVec ((x.extractLsb' (sh + p * W) W).signExtend (W + 1)) := by
  unfold sxV
  rw [LVec.extract_ofBitVec _ (by omega), LVec.extract_ofBitVec _ (by omega), LVec.concatMany_cons_cons,
    LVec.concatMany_singleton, LVec.concat_ofBitVec, Lib.extractLsb'_ushiftRight, Lib.extractLsb'_ushiftRight,
    show sh + (p * W + W - 1) = sh + p * W + W - 1 by omega]
  exact bitcat_signExtend hW x (sh + p * W)

theorem ofInt_sub' {n : Nat} (a b : Int) : BitVec.ofInt n (a - b) = BitVec.ofInt n a - BitVec.ofInt n b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- The A-side pre-sum of lane `r` on known heads is the integer pre-sum at `W + 1` bits. -/
theorem preV_ofBitVec {W : Nat} (r : Nat) (x11 x12 x21 x22 : BitVec W) :
    (preV r (LVec.ofBitVec (x11.signExtend (W + 1))) (LVec.ofBitVec (x12.signExtend (W + 1)))
      (LVec.ofBitVec (x21.signExtend (W + 1))) (LVec.ofBitVec (x22.signExtend (W + 1)))).resizeU (W + 1) =
      LVec.ofBitVec (BitVec.ofInt (W + 1) (preI r x11.toInt x12.toInt x21.toInt x22.toInt)) := by
  rcases r with _ | _ | _ | _ | _ | _ | _ | r <;>
    simp [preV, preI, BitVec.signExtend, BitVec.ofInt_add, ofInt_sub']

theorem preW_ofBitVec {W : Nat} (r : Nat) (y11 y12 y21 y22 : BitVec W) :
    (preW r (LVec.ofBitVec (y11.signExtend (W + 1))) (LVec.ofBitVec (y12.signExtend (W + 1)))
      (LVec.ofBitVec (y21.signExtend (W + 1))) (LVec.ofBitVec (y22.signExtend (W + 1)))).resizeU (W + 1) =
      LVec.ofBitVec (BitVec.ofInt (W + 1) (preJ r y11.toInt y12.toInt y21.toInt y22.toInt)) := by
  rcases r with _ | _ | _ | _ | _ | _ | _ | r <;>
    simp [preW, preJ, BitVec.signExtend, BitVec.ofInt_add, ofInt_sub']

/-- The heads of `a_sh`: entry `p` after `t` steps is `A`'s entry `p + t`. -/
theorem headA {N W h : Nat} (hW : 1 ≤ W) (A : BitVec (N * N * W)) (t p : Nat) (hp : p + 1 ≤ (2 * h + 1) * N)
    (hhN : N ≤ 2 * h + 1) :
    sxV (LVec.ofBitVec (ashV N W h A t)) W p = LVec.ofBitVec ((A.extractLsb' ((p + t) * W) W).signExtend (W + 1)) := by
  have hL : N * N * W ≤ (2 * h + 1) * N * W := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hhN)
  rw [ashV, sxV_shr hW _ _ _ (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp), extractLsb'_setWidth_ge _ hL,
    show t * W + p * W = (p + t) * W by rw [Nat.add_mul, Nat.add_comm]]

/-- The heads of `b_sh`: entry `p` after `t` steps is `B`'s entry `t·N + p`. -/
theorem headB {N W h : Nat} (hW : 1 ≤ W) (B : BitVec (N * N * W)) (t p : Nat) (hp : p + 1 ≤ (2 * h + 1) * N)
    (hhN : N ≤ 2 * h + 1) :
    sxV (LVec.ofBitVec (bshV N W h B t)) W p =
      LVec.ofBitVec ((B.extractLsb' ((t * N + p) * W) W).signExtend (W + 1)) := by
  have hL : N * N * W ≤ (2 * h + 1) * N * W := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hhN)
  rw [bshV, sxV_shr hW _ _ _ (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp), extractLsb'_setWidth_ge _ hL,
    show t * (N * W) + p * W = (t * N + p) * W by rw [Nat.add_mul, Nat.mul_assoc]]

/-- The positions of the four A-side heads of row `u` are entries of `a_sh`. -/
theorem posA {N h u : Nat} (hu : u < h) (hhN : h ≤ N) :
    u * N + 1 ≤ (2 * h + 1) * N ∧ u * N + h + 1 ≤ (2 * h + 1) * N ∧ (h + u) * N + 1 ≤ (2 * h + 1) * N ∧
      (h + u) * N + h + 1 ≤ (2 * h + 1) * N := by
  have hN : 1 ≤ N := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Nat.mul_le_mul_right N (show u + 1 ≤ 2 * h + 1 by omega); rw [Nat.succ_mul] at this; omega
  · have := Nat.mul_le_mul_right N (show u + 2 ≤ 2 * h + 1 by omega); rw [Nat.add_mul] at this; omega
  · have := Nat.mul_le_mul_right N (show h + u + 1 ≤ 2 * h + 1 by omega); rw [Nat.succ_mul] at this; omega
  · have := Nat.mul_le_mul_right N (show h + u + 2 ≤ 2 * h + 1 by omega); rw [Nat.add_mul] at this; omega

/-- The positions of the four B-side heads of column `v` are entries of `b_sh`. -/
theorem posB {N h v : Nat} (hv : v < h) (hhN : h ≤ N) :
    v + 1 ≤ (2 * h + 1) * N ∧ h + v + 1 ≤ (2 * h + 1) * N ∧ h * N + v + 1 ≤ (2 * h + 1) * N ∧
      h * N + h + v + 1 ≤ (2 * h + 1) * N := by
  have k1 : h ≤ h * N := Nat.le_mul_of_pos_right h (by omega)
  have k2 : (2 * h + 1) * N = 2 * (h * N) + N := by rw [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem saL_val {N W h : Nat} (hW : 1 ≤ W) (A : BitVec (N * N * W)) (t u r : Nat) (hu : u < h) (hhN : h ≤ N)
    (hN2 : N ≤ 2 * h + 1) :
    saL N W h (LVec.ofBitVec (ashV N W h A t)) u r =
      ("S", (u * 7 + r) * (W + 1), LVec.ofBitVec (BitVec.ofInt (W + 1) (sA N W h A r u t))) := by
  obtain ⟨p1, p2, p3, p4⟩ := posA hu hhN
  rw [saL, headA hW A t _ p1 hN2, headA hW A t _ p2 hN2, headA hW A t _ p3 hN2, headA hW A t _ p4 hN2, preV_ofBitVec]
  simp only [sA, Ah, Tasks.Matmul.entry, Nat.add_assoc]

theorem tbL_val {N W h : Nat} (hW : 1 ≤ W) (B : BitVec (N * N * W)) (t v r : Nat) (hv : v < h) (hhN : h ≤ N)
    (hN2 : N ≤ 2 * h + 1) :
    tbL N W h (LVec.ofBitVec (bshV N W h B t)) v r =
      ("T", (v * 7 + r) * (W + 1), LVec.ofBitVec (BitVec.ofInt (W + 1) (sB N W h B r t v))) := by
  obtain ⟨p1, p2, p3, p4⟩ := posB hv hhN
  have e1 : t * N + (h * N + v) = (h + t) * N + v := by rw [Nat.add_mul]; omega
  have e2 : t * N + (h * N + h + v) = (h + t) * N + (h + v) := by rw [Nat.add_mul]; omega
  rw [tbL, headB hW B t _ p1 hN2, headB hW B t _ p2 hN2, headB hW B t _ p3 hN2, headB hW B t _ p4 hN2, preW_ofBitVec,
    e1, e2]
  simp only [sB, Bh, Tasks.Matmul.entry]

/-- A pre-sum of two `W`-bit entries fits `W + 1` bits. -/
theorem pre_range {W : Nat} (hW : 1 ≤ W) (x : Int) (hx : ∀ c : Int, -2 ^ (W - 1) ≤ c → c < 2 ^ (W - 1) → True)
    (a b : BitVec W) :
    (-2 ^ (W + 1 - 1) ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 ^ (W + 1 - 1)) ∧
    (-2 ^ (W + 1 - 1) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ (W + 1 - 1)) ∧
    (-2 ^ (W + 1 - 1) ≤ a.toInt ∧ a.toInt < 2 ^ (W + 1 - 1)) := by
  have e : (2 : Int) ^ (W + 1 - 1) = 2 ^ (W - 1) * 2 := by
    rw [show W + 1 - 1 = (W - 1) + 1 by omega, Int.pow_succ]
  have ha1 := BitVec.le_toInt a; have ha2 := @BitVec.toInt_lt W a
  have hb1 := BitVec.le_toInt b; have hb2 := @BitVec.toInt_lt W b
  rw [e]; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

theorem preI_toInt {W : Nat} (hW : 1 ≤ W) (r : Nat) (x11 x12 x21 x22 : BitVec W) :
    (BitVec.ofInt (W + 1) (preI r x11.toInt x12.toInt x21.toInt x22.toInt)).toInt =
      preI r x11.toInt x12.toInt x21.toInt x22.toInt := by
  have q := fun a b => pre_range hW 0 (fun _ _ _ => trivial) a b
  rcases r with _ | _ | _ | _ | _ | _ | _ | r <;> simp only [preI] <;>
    first
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ _).1.1 (q _ _).1.2
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ _).2.1.1 (q _ _).2.1.2
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ x11).2.2.1 (q _ x11).2.2.2

theorem preJ_toInt {W : Nat} (hW : 1 ≤ W) (r : Nat) (x11 x12 x21 x22 : BitVec W) :
    (BitVec.ofInt (W + 1) (preJ r x11.toInt x12.toInt x21.toInt x22.toInt)).toInt =
      preJ r x11.toInt x12.toInt x21.toInt x22.toInt := by
  have q := fun a b => pre_range hW 0 (fun _ _ _ => trivial) a b
  rcases r with _ | _ | _ | _ | _ | _ | _ | r <;> simp only [preJ] <;>
    first
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ _).1.1 (q _ _).1.2
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ _).2.1.1 (q _ _).2.1.2
    | exact BitVec.toInt_ofInt_eq_self (by omega) (q _ x11).2.2.1 (q _ x11).2.2.2

theorem sA_toInt {N W h : Nat} (hW : 1 ≤ W) {n : Nat} (A : BitVec n) (r u w : Nat) :
    (BitVec.ofInt (W + 1) (sA N W h A r u w)).toInt = sA N W h A r u w := by
  unfold sA Ah Tasks.Matmul.entry; exact preI_toInt hW r _ _ _ _

theorem sB_toInt {N W h : Nat} (hW : 1 ≤ W) {n : Nat} (B : BitVec n) (r w v : Nat) :
    (BitVec.ofInt (W + 1) (sB N W h B r w v)).toInt = sB N W h B r w v := by
  unfold sB Bh Tasks.Matmul.entry; exact preJ_toInt hW r _ _ _ _

/-- A family over `n` rows of `K` entries is the family over the `n·K` row-major indices. -/
theorem flatMap_range_map {α : Type} (K : Nat) (f : Nat → α) : ∀ n,
    ((List.range n).flatMap fun i => (List.range K).map fun j => f (i * K + j)) = (List.range (n * K)).map f
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_map K f n, Nat.succ_mul, @List.range_add (n * K) K,
      List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- Three nested families, row-major. -/
theorem flatMap3_range_map {α : Type} (n m K : Nat) (f : Nat → α) :
    ((List.range n).flatMap fun i => (List.range m).flatMap fun j => (List.range K).map fun k => f ((i * m + j) * K + k)) =
      (List.range (n * (m * K))).map f := by
  rw [← flatMap_range_map (m * K) f n]
  refine CombView.flatMap_congr' fun i _ => ?_
  rw [← flatMap_range_map K (fun q => f (i * (m * K) + q)) m]
  refine CombView.flatMap_congr' fun j _ => List.map_congr_left fun k _ => ?_
  congr 1
  rw [Nat.add_mul, Nat.mul_assoc i m K]; omega

/-- Committing a row-major family of window writes. -/
theorem nbaFold_map (n : String) (w k : Nat) (g : Nat → LVec) (x : LVec) :
    nbaFold n ((List.range k).map fun i => (n, i * w, g i)) x = LVec.insertEntries w g k x := by
  simp [nbaFold, List.foldl_map, LVec.insertEntries]

theorem saQ_map (N W h : Nat) (bz ash : LVec) (u : Nat) :
    saQ N W h bz ash u = if bz.condTrue then (List.range 7).map (saL N W h ash u) else [] := rfl
theorem tbQ_map (N W h : Nat) (bz bsh : LVec) (v : Nat) :
    tbQ N W h bz bsh v = if bz.condTrue then (List.range 7).map (tbL N W h bsh v) else [] := rfl

/-- **`S` after a busy cycle** holds the pre-sums of column `t`. -/
theorem S_busy {N W h : Nat} (hW : 1 ≤ W) (hhN : h ≤ N) (hN2 : N ≤ 2 * h + 1) (A : BitVec (N * N * W)) (t : Nat)
    (sr : LVec) (hsr : sr.width = 7 * h * (W + 1)) :
    nbaFold "S" ((List.range h).flatMap (saQ N W h (knownBit true) (LVec.ofBitVec (ashV N W h A t)))) sr =
      LVec.ofBitVec (Sv N W h A t) := by
  have hq : (List.range h).flatMap (saQ N W h (knownBit true) (LVec.ofBitVec (ashV N W h A t))) =
      (List.range (h * 7)).map fun q =>
        ("S", q * (W + 1), LVec.ofBitVec (BitVec.ofInt (W + 1) (sA N W h A (q % 7) (q / 7) t))) := by
    rw [← flatMap_range_map 7 _ h]
    refine CombView.flatMap_congr' fun u hu => ?_
    rw [saQ_map, condTrue_knownBit, if_pos rfl]
    refine List.map_congr_left fun r hr => ?_
    have hr := List.mem_range.mp hr
    rw [saL_val hW A t u r (List.mem_range.mp hu) hhN hN2, rm_mod hr, rm_div hr]
  rw [hq, nbaFold_map, LVec.insertEntries_ofBitVec _ _ (by rw [hsr, Nat.mul_comm 7 h])]
  rfl

/-- **`T` after a busy cycle** holds the pre-sums of row `t`. -/
theorem T_busy {N W h : Nat} (hW : 1 ≤ W) (hhN : h ≤ N) (hN2 : N ≤ 2 * h + 1) (B : BitVec (N * N * W)) (t : Nat)
    (tr : LVec) (htr : tr.width = 7 * h * (W + 1)) :
    nbaFold "T" ((List.range h).flatMap (tbQ N W h (knownBit true) (LVec.ofBitVec (bshV N W h B t)))) tr =
      LVec.ofBitVec (Tv N W h B t) := by
  have hq : (List.range h).flatMap (tbQ N W h (knownBit true) (LVec.ofBitVec (bshV N W h B t))) =
      (List.range (h * 7)).map fun q =>
        ("T", q * (W + 1), LVec.ofBitVec (BitVec.ofInt (W + 1) (sB N W h B (q % 7) t (q / 7)))) := by
    rw [← flatMap_range_map 7 _ h]
    refine CombView.flatMap_congr' fun v hv => ?_
    rw [tbQ_map, condTrue_knownBit, if_pos rfl]
    refine List.map_congr_left fun r hr => ?_
    have hr := List.mem_range.mp hr
    rw [tbL_val hW B t v r (List.mem_range.mp hv) hhN hN2, rm_mod hr, rm_div hr]
  rw [hq, nbaFold_map, LVec.insertEntries_ofBitVec _ _ (by rw [htr, Nat.mul_comm 7 h])]
  rfl

/-- Lane `(u, v, r)` of the engines. -/
theorem M_lane {N W AccW h : Nat} (A B : BitVec (N * N * W)) (k u v r : Nat) (hu : u < h) (hv : v < h) (hr : r < 7) :
    (LVec.ofBitVec (Mv N W AccW h A B k)).extract (((u * h + v) * 7 + r) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (msum N W h A B r u v k)) := by
  have hq : (u * h + v) * 7 + r < h * (h * 7) := by
    have := cell_lt hu hv
    have := Nat.mul_le_mul_right 7 (show u * h + v + 1 ≤ h * h by omega)
    rw [Nat.succ_mul, Nat.mul_assoc] at this; omega
  rw [Mv, extract_ofBitVec_packBV _ hq rfl]
  simp only [rm_mod hr, rm_div hr, rm_div hv, rm_mod hv]

/-- Lane `(u, r)` of `S`, read and sign-extended as an engine operand. -/
theorem S_lane {N W AccW h : Nat} (hW : 1 ≤ W) (A : BitVec (N * N * W)) (k u r : Nat) (hu : u < h) (hr : r < 7) :
    sxAV (LVec.ofBitVec (Sv N W h A k)) AccW ((u * 7 + r) * (W + 1) + W) ((u * 7 + r) * (W + 1)) (W + 1) =
      LVec.ofBitVec ((BitVec.ofInt (W + 1) (sA N W h A r u k)).signExtend (AccW + (W + 1))) := by
  have hq : u * 7 + r < h * 7 := by omega
  have hs := fam_le (w := W + 1) hq
  have hl : (Sv N W h A k).extractLsb' ((u * 7 + r) * (W + 1)) (W + 1) = BitVec.ofInt (W + 1) (sA N W h A r u k) := by
    rw [Sv, extractLsb'_packBV _ hq, rm_mod hr, rm_div hr]
  unfold sxAV
  rw [LVec.extract_ofBitVec _ (by omega), LVec.extract_ofBitVec _ hs]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  rw [LVec.ofBitVec_replicate_append_eq_signExtend (by omega) _ _ (by omega), hl]

theorem T_lane {N W AccW h : Nat} (hW : 1 ≤ W) (B : BitVec (N * N * W)) (k v r : Nat) (hv : v < h) (hr : r < 7) :
    sxAV (LVec.ofBitVec (Tv N W h B k)) AccW ((v * 7 + r) * (W + 1) + W) ((v * 7 + r) * (W + 1)) (W + 1) =
      LVec.ofBitVec ((BitVec.ofInt (W + 1) (sB N W h B r k v)).signExtend (AccW + (W + 1))) := by
  have hq : v * 7 + r < h * 7 := by omega
  have hs := fam_le (w := W + 1) hq
  have hl : (Tv N W h B k).extractLsb' ((v * 7 + r) * (W + 1)) (W + 1) = BitVec.ofInt (W + 1) (sB N W h B r k v) := by
    rw [Tv, extractLsb'_packBV _ hq, rm_mod hr, rm_div hr]
  unfold sxAV
  rw [LVec.extract_ofBitVec _ (by omega), LVec.extract_ofBitVec _ hs]
  simp only [LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec]
  rw [LVec.ofBitVec_replicate_append_eq_signExtend (by omega) _ _ (by omega), hl]

/-- **An engine step**: cell `(u, v)` of engine `r` adds the term `w = k`. -/
theorem macV_val {N W AccW h : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (k u v r : Nat) (hu : u < h)
    (hv : v < h) (hr : r < 7) :
    macV h W AccW (LVec.ofBitVec (Mv N W AccW h A B k)) (LVec.ofBitVec (Sv N W h A k)) (LVec.ofBitVec (Tv N W h B k))
      u v r = LVec.ofBitVec (BitVec.ofInt AccW (msum N W h A B r u v (k + 1))) := by
  unfold macV
  rw [M_lane A B k u v r hu hv hr, S_lane hW A k u r hu hr, T_lane hW B k v r hv hr, LVec.resizeU_ofBitVec,
    LVec.mul_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, Lib.setWidth_add_mul_signExtend (by omega),
    sA_toInt hW, sB_toInt hW, ← BitVec.ofInt_add]
  rfl

theorem zeroB_val {t : Nat} (ht : t < 2 ^ 32) : zeroB (LVec.ofBitVec (BitVec.ofNat 32 t)) = decide (t = 0) := by
  have e : (BitVec.ofNat 32 t = BitVec.ofInt 32 0) ↔ t = 0 := by
    rw [← BitVec.toNat_inj]; simp [Nat.mod_eq_of_lt ht]
  simp only [zeroB, LVec.ofInt_eq_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, condTrue_knownBit]
  simp only [e]

theorem lastB_val {h t : Nat} (hh : h + 1 < 2 ^ 31) (ht : t < 2 ^ 32) :
    lastB h (LVec.ofBitVec (BitVec.ofNat 32 t)) = decide (t = h + 1) := by
  have e : (BitVec.ofNat 32 t = BitVec.ofInt 32 (h : Int) + BitVec.ofInt 32 1) ↔ t = h + 1 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_add, BitVec.ofInt_natCast, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [show BitVec.ofInt 32 1 = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (show h < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show 1 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show h + 1 < 2 ^ 32 by omega)]
  simp only [lastB, LVec.ofInt_eq_ofBitVec, LVec.add_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    condTrue_knownBit]
  simp only [e]

theorem macQ_zero {h W AccW : Nat} (m sr tr : LVec) (u v r : Nat) :
    macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 0)) m sr tr u v r =
      [("M", ((u * h + v) * 7 + r) * AccW, LVec.ofBitVec 0#AccW)] := by
  simp [macQ, zeroB_val (show 0 < 2 ^ 32 by omega)]

theorem macQ_acc {N W AccW h : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (k : Nat) (hk : k + 1 < 2 ^ 32)
    (u v r : Nat) (hu : u < h) (hv : v < h) (hr : r < 7) :
    macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 (k + 1))) (LVec.ofBitVec (Mv N W AccW h A B k))
      (LVec.ofBitVec (Sv N W h A k)) (LVec.ofBitVec (Tv N W h B k)) u v r =
      [("M", ((u * h + v) * 7 + r) * AccW, LVec.ofBitVec (BitVec.ofInt AccW (msum N W h A B r u v (k + 1))))] := by
  simp only [macQ, condTrue_knownBit, if_true, zeroB_val hk, macV_val hW A B k u v r hu hv hr, LVec.resizeU_ofBitVec,
    BitVec.setWidth_eq, Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, if_false]

theorem lanes_eq (h : Nat) : 7 * h * h = h * (h * 7) := by
  rw [Nat.mul_comm 7 h, Nat.mul_assoc, Nat.mul_comm 7 h]

/-- **The engines after the clearing cycle `t = 0`.** -/
theorem M_zero {N W AccW h : Nat} (A B : BitVec (N * N * W)) (m sr tr : LVec) (hm : m.width = 7 * h * h * AccW) :
    nbaFold "M" ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 0)) m sr tr u v)) m =
      LVec.ofBitVec (Mv N W AccW h A B 0) := by
  have hq : ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 0)) m sr tr u v)) =
      (List.range (h * (h * 7))).map fun q => ("M", q * AccW, LVec.ofBitVec 0#AccW) := by
    rw [← flatMap3_range_map h h 7 (fun q => ("M", q * AccW, LVec.ofBitVec 0#AccW))]
    refine CombView.flatMap_congr' fun u _ => CombView.flatMap_congr' fun v _ => ?_
    rw [← Gen2.flatMap_singleton_map]
    exact CombView.flatMap_congr' fun r _ => macQ_zero m sr tr u v r
  rw [hq, nbaFold_map, LVec.insertEntries_ofBitVec (fun _ => 0#AccW) _ (by rw [hm, lanes_eq]), Mv]
  congr 2

/-- **The engines after an accumulating cycle** `t = k + 1`. -/
theorem M_acc {N W AccW h : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (k : Nat) (hk : k + 1 < 2 ^ 32) :
    nbaFold "M" ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 (k + 1))) (LVec.ofBitVec (Mv N W AccW h A B k))
        (LVec.ofBitVec (Sv N W h A k)) (LVec.ofBitVec (Tv N W h B k)) u v)) (LVec.ofBitVec (Mv N W AccW h A B k)) =
      LVec.ofBitVec (Mv N W AccW h A B (k + 1)) := by
  have hq : ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 (k + 1))) (LVec.ofBitVec (Mv N W AccW h A B k))
        (LVec.ofBitVec (Sv N W h A k)) (LVec.ofBitVec (Tv N W h B k)) u v)) =
      (List.range (h * (h * 7))).map fun q => ("M", q * AccW,
        LVec.ofBitVec (BitVec.ofInt AccW (msum N W h A B (q % 7) (q / 7 / h) (q / 7 % h) (k + 1)))) := by
    rw [← flatMap3_range_map h h 7]
    refine CombView.flatMap_congr' fun u hu => CombView.flatMap_congr' fun v hv => ?_
    rw [← Gen2.flatMap_singleton_map]
    refine CombView.flatMap_congr' fun r hr => ?_
    have hu := List.mem_range.mp hu; have hv := List.mem_range.mp hv; have hr := List.mem_range.mp hr
    rw [macQ_acc hW A B k hk u v r hu hv hr]
    simp only [rm_mod hr, rm_div hr, rm_div hv, rm_mod hv]
  rw [hq, nbaFold_map, LVec.insertEntries_ofBitVec _ _ (by simp), Mv]

theorem mV_val {N W AccW h : Nat} (A B : BitVec (N * N * W)) (k u v r : Nat) (hu : u < h) (hv : v < h) (hr : r < 7) :
    mV h AccW (LVec.ofBitVec (Mv N W AccW h A B k)) u v r = LVec.ofBitVec (BitVec.ofInt AccW (msum N W h A B r u v k)) :=
  M_lane A B k u v r hu hv hr

/-- **The post-sum of cell `(i, j)`** at the last edge. -/
theorem cQij_last {N W AccW h : Nat} (hhN : h ≤ N) (h2N : N ≤ 2 * h) (hh : h + 1 < 2 ^ 31) (A B : BitVec (N * N * W))
    (i j : Nat) (hi : i < N) (hj : j < N) :
    cQij N h AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (LVec.ofBitVec (Mv N W AccW h A B h)) i j =
      [("C", (i * N + j) * AccW, LVec.ofBitVec (BitVec.ofInt AccW (postI N W h A B i j h)))] := by
  unfold cQij cQ postI
  rw [lastB_val hh (by omega)]
  simp only [condTrue_knownBit, decide_true, if_true]
  by_cases h1 : i < h <;> by_cases h2 : j < h <;> simp only [h1, h2, if_true, if_false]
  · rw [v11, mV_val A B h i j 0 h1 h2 (by omega), mV_val A B h i j 3 h1 h2 (by omega),
      mV_val A B h i j 4 h1 h2 (by omega), mV_val A B h i j 6 h1 h2 (by omega)]
    simp only [LVec.add_ofBitVec, LVec.sub_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, ← BitVec.ofInt_add,
      ← ofInt_sub']
  · rw [show i * N + h + (j - h) = i * N + j by omega, v12, mV_val A B h i (j - h) 2 h1 (by omega) (by omega),
      mV_val A B h i (j - h) 4 h1 (by omega) (by omega)]
    simp only [LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, ← BitVec.ofInt_add]
  · rw [show h + (i - h) = i by omega, v21, mV_val A B h (i - h) j 1 (by omega) h2 (by omega),
      mV_val A B h (i - h) j 3 (by omega) h2 (by omega)]
    simp only [LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, ← BitVec.ofInt_add]
  · rw [show (h + (i - h)) * N + h + (j - h) = i * N + j by rw [show h + (i - h) = i by omega]; omega, v22,
      mV_val A B h (i - h) (j - h) 0 (by omega) (by omega) (by omega),
      mV_val A B h (i - h) (j - h) 1 (by omega) (by omega) (by omega),
      mV_val A B h (i - h) (j - h) 2 (by omega) (by omega) (by omega),
      mV_val A B h (i - h) (j - h) 5 (by omega) (by omega) (by omega)]
    simp only [LVec.add_ofBitVec, LVec.sub_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, ← BitVec.ofInt_add,
      ← ofInt_sub']

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- **`C` after the last edge** is the product. -/
theorem C_last {N W AccW h : Nat} (hhN : h ≤ N) (h2N : N ≤ 2 * h) (h2N' : 2 * h ≤ N + 1) (hh : h + 1 < 2 ^ 31)
    (A B : BitVec (N * N * W))
    (c : LVec) (hc : c.width = N * N * AccW) :
    nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW (knownBit true)
      (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (LVec.ofBitVec (Mv N W AccW h A B h)) i)) c =
      LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  have hq : ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW (knownBit true)
      (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (LVec.ofBitVec (Mv N W AccW h A B h)) i)) =
      (List.range (N * N)).map fun q =>
        ("C", q * AccW, LVec.ofBitVec (BitVec.ofInt AccW (Tasks.Matmul.dot N W A B (q / N) (q % N)))) := by
    rw [← flatMap_range_map N _ N]
    refine CombView.flatMap_congr' fun i hi => ?_
    rw [← Gen2.flatMap_singleton_map]
    refine CombView.flatMap_congr' fun j hj => ?_
    have hi := List.mem_range.mp hi; have hj := List.mem_range.mp hj
    rw [cQij_last hhN h2N hh A B i j hi hj, post_dot A B hi hj hhN h2N h2N', rm_div hj, rm_mod hj]
  rw [hq, nbaFold_map, LVec.insertEntries_ofBitVec _ _ hc, product_eq]

/-- `C` is not written before the last edge. -/
theorem C_quiet {N h AccW : Nat} (bz t m c : LVec) (hq : ∀ i j, cQij N h AccW bz t m i j = []) :
    nbaFold "C" ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i)) c = c := by
  have h0 : ((List.range N).flatMap fun i => (List.range N).flatMap (cQij N h AccW bz t m i)) = [] := by
    rw [List.flatMap_eq_nil_iff]; intro i _; rw [List.flatMap_eq_nil_iff]; intro j _; exact hq i j
  rw [h0]; rfl

theorem cQij_nolast {N h AccW : Nat} (bz t m : LVec) (hl : lastB h t = false) (i j : Nat) :
    cQij N h AccW bz t m i j = [] := by
  unfold cQij cQ; split <;> split <;> simp [hl]

theorem cQij_idle {N h AccW : Nat} (t m : LVec) (i j : Nat) : cQij N h AccW (knownBit false) t m i j = [] := by
  unfold cQij cQ; split <;> split <;> simp

/-! ## 6. The control and the next state in each phase -/

theorem shr_W {N W h : Nat} (hW32 : W < 2 ^ 32) (A : BitVec (N * N * W)) (t : Nat) :
    (LVec.ofBitVec (ashV N W h A t)).shr (LVec.ofInt 32 (W : Int)) = LVec.ofBitVec (ashV N W h A (t + 1)) := by
  rw [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.shr_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW32, ashV,
    ashV, ← BitVec.shiftRight_add, Nat.add_mul t 1 W, Nat.one_mul]

theorem shr_NW {N W h : Nat} (hN32 : N < 2 ^ 32) (hW32 : W < 2 ^ 32) (hNW32 : N * W < 2 ^ 32)
    (B : BitVec (N * N * W)) (t : Nat) :
    (LVec.ofBitVec (bshV N W h B t)).shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))) =
      LVec.ofBitVec (bshV N W h B (t + 1)) := by
  rw [LVec.ofInt_eq_ofBitVec, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_natCast, LVec.mul_ofBitVec,
    LVec.shr_ofBitVec, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN32,
    Nat.mod_eq_of_lt hW32, Nat.mod_eq_of_lt hNW32, bshV, bshV, ← BitVec.shiftRight_add, Nat.add_mul t 1 (N * W),
    Nat.one_mul]

theorem t_succ {t : Nat} : (LVec.ofBitVec (BitVec.ofNat 32 t)).add (LVec.ofInt 32 1) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) := by
  rw [show LVec.ofInt 32 1 = LVec.ofBitVec 1#32 by decide, LVec.add_ofBitVec, BitVec.ofNat_add_ofNat]

/-- The control's updates in a busy cycle `t`. -/
theorem ctrlQ_busy {N W h : Nat} (hW32 : W < 2 ^ 32) (hN32 : N < 2 ^ 32) (hNW32 : N * W < 2 ^ 32) (hh : h + 1 < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t < 2 ^ 32) (a b : LVec) :
    ctrlQ N W h (knownBit false) (knownBit false) a b (knownBit false) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (ashV N W h A t)) (LVec.ofBitVec (bshV N W h B t)) =
      [wr "t" (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))),
        wr "a_sh" (LVec.ofBitVec (ashV N W h A t)) (LVec.ofBitVec (ashV N W h A (t + 1))),
        wr "b_sh" (LVec.ofBitVec (bshV N W h B t)) (LVec.ofBitVec (bshV N W h B (t + 1)))] ++
      (if t = h + 1 then [wr "busy" (knownBit true) ⟨#[.l0]⟩, wr "done" (knownBit false) ⟨#[.l1]⟩] else []) := by
  unfold ctrlQ
  rw [t_succ, shr_W hW32, shr_NW hN32 hW32 hNW32, lastB_val hh ht]
  by_cases e : t = h + 1 <;> simp [e]

theorem width_kb (b : Bool) : (knownBit b).width = 1 := by cases b <;> rfl

/-- A cycle without reset, start or busy changes nothing. -/
theorem next_idle (N W AccW h : Nat) (ck a b dn c t ash bsh sr tr m : LVec) :
    stNext N W AccW h ck (knownBit false) (knownBit false) a b dn c t (knownBit false) ash bsh sr tr m =
      SS ck (knownBit false) (knownBit false) a b dn c t (knownBit false) ash bsh sr tr m := by
  have h1 : (List.range h).flatMap (saQ N W h (knownBit false) ash) = [] := by
    simp [List.flatMap_eq_nil_iff, saQ]
  have h2 : (List.range h).flatMap (tbQ N W h (knownBit false) bsh) = [] := by
    simp [List.flatMap_eq_nil_iff, tbQ]
  have h3 : ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit false) t m sr tr u v)) = [] := by
    simp [List.flatMap_eq_nil_iff, macQ]
  rw [stNext_eq, h1, h2, h3, C_quiet _ _ _ _ (cQij_idle t m)]
  simp [ctrlQ, nbaFold]

/-- A reset cycle clears `busy` and `done`. -/
theorem next_reset {N W AccW h : Nat} (ck s a b dn c t bz ash bsh sr tr m : LVec) (hdn : dn.width = 1)
    (hbz : bz.width = 1) :
    ∃ c' t' ash' bsh' sr' tr' m', stNext N W AccW h ck (knownBit true) s a b dn c t bz ash bsh sr tr m =
      SS ck (knownBit true) s a b (knownBit false) c' t' (knownBit false) ash' bsh' sr' tr' m' := by
  have hd : nbaFold "done" (ctrlQ N W h (knownBit true) s a b dn t bz ash bsh) dn = knownBit false := by
    simp [ctrlQ, nbaFold, wr, hdn, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [width_kb, hdn])
  have hb : nbaFold "busy" (ctrlQ N W h (knownBit true) s a b dn t bz ash bsh) bz = knownBit false := by
    simp [ctrlQ, nbaFold, wr, hbz, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [width_kb, hbz])
  rw [stNext_eq, hd, hb]
  exact ⟨_, _, _, _, _, _, _, rfl⟩

/-- **A start from an idle state** captures the operands: the state `t = 0`. -/
theorem next_start {N W AccW h : Nat} (A B : BitVec (N * N * W)) (ck dn c t ash bsh sr tr m : LVec)
    (hdn : dn.width = 1) (ht : t.width = 32) (ha : ash.width = (2 * h + 1) * N * W)
    (hb : bsh.width = (2 * h + 1) * N * W) :
    stNext N W AccW h ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn c t (knownBit false)
      ash bsh sr tr m =
      SS ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true) (LVec.ofBitVec (ashV N W h A 0))
        (LVec.ofBitVec (bshV N W h B 0)) sr tr m := by
  have h1 : (List.range h).flatMap (saQ N W h (knownBit false) ash) = [] := by
    simp [List.flatMap_eq_nil_iff, saQ]
  have h2 : (List.range h).flatMap (tbQ N W h (knownBit false) bsh) = [] := by
    simp [List.flatMap_eq_nil_iff, tbQ]
  have h3 : ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit false) t m sr tr u v)) = [] := by
    simp [List.flatMap_eq_nil_iff, macQ]
  have hq : ctrlQ N W h (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn t (knownBit false)
      ash bsh = [wr "busy" (knownBit false) ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "t" t (LVec.replicate 32 .l0),
        wr "a_sh" ash ((LVec.ofBitVec A).resizeU ((2 * h + 1) * N * W)),
        wr "b_sh" bsh ((LVec.ofBitVec B).resizeU ((2 * h + 1) * N * W))] := by
    simp [ctrlQ]
  rw [stNext_eq, h1, h2, h3, C_quiet _ _ _ _ (cQij_idle t m), hq]
  simp only [nbaFold, List.foldl_cons, List.foldl_nil, wr]
  simp [hdn, ht, ha, hb, LVec.resizeU_one_l0, LVec.resizeU_one_l1, ashV, bshV]
  rw [LVec.insertAt_zero_of_width_eq (v := dn) (by simp [width_kb, hdn]),
    LVec.insertAt_zero_of_width_eq (v := t) (by simp [ht]), LVec.insertAt_zero_of_width_eq (v := ash) (by simp [ha]),
    LVec.insertAt_zero_of_width_eq (v := bsh) (by simp [hb]),
    show LVec.ofBitVec (bvInsertAt (0#1) 0 1#1) = knownBit true by decide]

/-- The parameter bounds the steps need. -/
theorem rng_facts {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) :
    N < 2 ^ 31 ∧ W < 2 ^ 32 ∧ N < 2 ^ 32 ∧ N * W < 2 ^ 32 := by
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc N N W]; exact Nat.le_mul_of_pos_left _ hN
  have h2 : W ≤ N * W := Nat.le_mul_of_pos_left W hN
  have h3 : N ≤ N * W := Nat.le_mul_of_pos_right N hW
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **A busy cycle before the last**: `t → t + 1`, the pre-sums of column `t`, the engines through column `t - 1`. -/
theorem next_busy {N W AccW h : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hhN : h ≤ N) (hN2 : N ≤ 2 * h + 1)
    (h2N' : 2 * h ≤ N + 1) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W)) {t : Nat} (ht : t < h + 1) (ck a b c sr tr m : LVec)
    (hsr : sr.width = 7 * h * (W + 1)) (htr : tr.width = 7 * h * (W + 1)) (hm : m.width = 7 * h * h * AccW)
    (hinv : ∀ k, t = k + 1 → sr = LVec.ofBitVec (Sv N W h A k) ∧ tr = LVec.ofBitVec (Tv N W h B k) ∧
      m = LVec.ofBitVec (Mv N W AccW h A B k)) :
    stNext N W AccW h ck (knownBit false) (knownBit false) a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) (LVec.ofBitVec (ashV N W h A t)) (LVec.ofBitVec (bshV N W h B t)) sr tr m =
      SS ck (knownBit false) (knownBit false) a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
        (knownBit true) (LVec.ofBitVec (ashV N W h A (t + 1))) (LVec.ofBitVec (bshV N W h B (t + 1)))
        (LVec.ofBitVec (Sv N W h A t)) (LVec.ofBitVec (Tv N W h B t)) (LVec.ofBitVec (Mv N W AccW h A B t)) := by
  obtain ⟨hN31, hW32, hN32, hNW32⟩ := rng_facts hN hW hr
  have hh : h + 1 < 2 ^ 31 := by omega
  have hM : nbaFold "M" ((List.range h).flatMap fun u => (List.range h).flatMap fun v => (List.range 7).flatMap
      (macQ h W AccW (knownBit true) (LVec.ofBitVec (BitVec.ofNat 32 t)) m sr tr u v)) m =
      LVec.ofBitVec (Mv N W AccW h A B t) := by
    rcases t with _ | k
    · exact M_zero A B m sr tr hm
    · obtain ⟨rfl, rfl, rfl⟩ := hinv k rfl
      exact M_acc hW A B k (by omega)
  have hl : lastB h (LVec.ofBitVec (BitVec.ofNat 32 t)) = false := by
    rw [lastB_val hh (by omega)]; simp; omega
  rw [stNext_eq, S_busy hW hhN hN2 A t sr hsr, T_busy hW hhN hN2 B t tr htr, hM,
    C_quiet _ _ _ _ (cQij_nolast _ _ _ hl), ctrlQ_busy hW32 hN32 hNW32 hh A B (by omega), if_neg (by omega)]
  simp only [nbaFold, List.append_nil, List.foldl_cons, List.foldl_nil, wr]
  simp [LVec.insertAt_zero_of_width_eq]

/-- **The last busy cycle** writes the product into `C` and raises `done`. -/
theorem next_last {N W AccW h : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hhN : h ≤ N) (h2N : N ≤ 2 * h)
    (h2N' : 2 * h ≤ N + 1) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W)) (ck a b c : LVec)
    (hc : c.width = N * N * AccW) :
    ∃ t' ash' bsh' sr' tr' m', stNext N W AccW h ck (knownBit false) (knownBit false) a b (knownBit false) c
      (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (knownBit true) (LVec.ofBitVec (ashV N W h A (h + 1)))
      (LVec.ofBitVec (bshV N W h B (h + 1))) (LVec.ofBitVec (Sv N W h A h)) (LVec.ofBitVec (Tv N W h B h))
      (LVec.ofBitVec (Mv N W AccW h A B h)) =
      SS ck (knownBit false) (knownBit false) a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B))
        t' (knownBit false) ash' bsh' sr' tr' m' := by
  obtain ⟨hN31, hW32, hN32, hNW32⟩ := rng_facts hN hW hr
  have hh : h + 1 < 2 ^ 31 := by omega
  rw [stNext_eq, C_last hhN h2N h2N' hh A B c hc, ctrlQ_busy hW32 hN32 hNW32 hh A B (by omega), if_pos rfl]
  have hd : nbaFold "done" ([wr "t" (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (LVec.ofBitVec (BitVec.ofNat 32 (h + 1 + 1))),
      wr "a_sh" (LVec.ofBitVec (ashV N W h A (h + 1))) (LVec.ofBitVec (ashV N W h A (h + 1 + 1))),
      wr "b_sh" (LVec.ofBitVec (bshV N W h B (h + 1))) (LVec.ofBitVec (bshV N W h B (h + 1 + 1)))] ++
      [wr "busy" (knownBit true) ⟨#[.l0]⟩, wr "done" (knownBit false) ⟨#[.l1]⟩]) (knownBit false) = knownBit true := by
    simp [nbaFold, wr, LVec.resizeU_one_l1]
    decide
  have hb : nbaFold "busy" ([wr "t" (LVec.ofBitVec (BitVec.ofNat 32 (h + 1))) (LVec.ofBitVec (BitVec.ofNat 32 (h + 1 + 1))),
      wr "a_sh" (LVec.ofBitVec (ashV N W h A (h + 1))) (LVec.ofBitVec (ashV N W h A (h + 1 + 1))),
      wr "b_sh" (LVec.ofBitVec (bshV N W h B (h + 1))) (LVec.ofBitVec (bshV N W h B (h + 1 + 1)))] ++
      [wr "busy" (knownBit true) ⟨#[.l0]⟩, wr "done" (knownBit false) ⟨#[.l1]⟩]) (knownBit true) = knownBit false := by
    simp [nbaFold, wr, LVec.resizeU_one_l0]
    decide
  rw [hd, hb]
  exact ⟨_, _, _, _, _, _, rfl⟩

/-! ## 7. Shape, termination, the phases, txtask-v2's rules -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW h : Nat) (dn c t bz ash bsh sr tr m : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ t.width = 32 ∧ bz.width = 1 ∧ ash.width = (2 * h + 1) * N * W ∧
    bsh.width = (2 * h + 1) * N * W ∧ sr.width = 7 * h * (W + 1) ∧ tr.width = 7 * h * (W + 1) ∧
    m.width = 7 * h * h * AccW

/-- A snapshot of the design's shape. -/
def I (N W AccW h : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz ash bsh sr tr m, st = SS ck r s a b dn c t bz ash bsh sr tr m ∧
    Wd N W AccW h dn c t bz ash bsh sr tr m

/-- **Every cycle keeps the shape** (any values). -/
theorem stNext_I (N W AccW h : Nat) (ck r s a b dn c t bz ash bsh sr tr m : LVec)
    (hw : Wd N W AccW h dn c t bz ash bsh sr tr m) :
    I N W AccW h (stNext N W AccW h ck r s a b dn c t bz ash bsh sr tr m) := by
  rw [stNext_eq]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hw
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by
    simp only [Wd, width_nbaFold]; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem st_noq (N W AccW h : Nat) : (stD N W AccW h).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [stD, genPs, cPs, cTop, cBot, saPs, tbPs, macPs, ctrlP, saP, tbP, wS, wT, macP, cP, c11P, c12P, c21P, c22P, nb,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem st_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    I N W AccW ((N + 1) / 2) (initState2 (design.sem N W AccW)) := by
  rw [st_sem_eq N W AccW hN hW hA hN31]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec ((2 * ((N + 1) / 2) + 1) * N * W), .xVec ((2 * ((N + 1) / 2) + 1) * N * W),
    .xVec (7 * ((N + 1) / 2) * (W + 1)), .xVec (7 * ((N + 1) / 2) * (W + 1)),
    .xVec (7 * ((N + 1) / 2) * ((N + 1) / 2) * AccW), ?_, by simp [Wd]⟩
  simp [initState2, stD, stDecls, SS]

/-- Every power-up state of the design has its shape. -/
theorem st_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW ((N + 1) / 2) st := by
  rw [st_sem_eq N W AccW hN hW hA hN31] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨t, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨ash, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bsh, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨sr, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨tr, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨m, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain rfl := powerUp_nil.mp h14
  exact ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, w6, w7, w8, w9, w10, w11, w12, w13, w14⟩

/-- **Termination from every power-up.** -/
theorem st_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW ((N + 1) / 2)) (st_powerUp N W AccW hN hW hA hN31)
    (fun σ => ⟨40, ?_⟩) (by rw [st_sem_eq N W AccW hN hW hA hN31]; exact st_noq N W AccW _)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, hw⟩
  exact ⟨_, _, st_cycle N W AccW hN hW hA hN31 σ e ck r s a b dn c t bz ash bsh sr tr m kk 40 (Nat.le_refl _),
    stNext_I N W AccW _ _ _ _ _ _ dn c t bz ash bsh sr tr m hw⟩

theorem SS_inj {ck r s a b dn c t bz ash bsh sr tr m ck' r' s' a' b' dn' c' t' bz' ash' bsh' sr' tr' m' : LVec}
    (h : SS ck r s a b dn c t bz ash bsh sr tr m = SS ck' r' s' a' b' dn' c' t' bz' ash' bsh' sr' tr' m') :
    dn = dn' ∧ c = c' ∧ t = t' ∧ bz = bz' ∧ ash = ash' ∧ bsh = bsh' ∧ sr = sr' ∧ tr = tr' ∧ m = m' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- The state `t` busy cycles after a start with operands `A`, `B` (the invariant on `t`). -/
def BusyAt (N W AccW h : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c sr tr m, st = SS ck r s a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
    (LVec.ofBitVec (ashV N W h A t)) (LVec.ofBitVec (bshV N W h B t)) sr tr m ∧
    ∀ k, t = k + 1 → sr = LVec.ofBitVec (Sv N W h A k) ∧ tr = LVec.ofBitVec (Tv N W h B k) ∧
      m = LVec.ofBitVec (Mv N W AccW h A B k)

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b t ash bsh sr tr m, st = SS ck r s a b (knownBit true)
    (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) t (knownBit false) ash bsh sr tr m

/-- One cycle from a state of the shape, evaluated (`st_cycle`). -/
def Stp (N W AccW h : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c t bz ash bsh sr tr m, prev = SS ck r s a b dn c t bz ash bsh sr tr m ∧
    Wd N W AccW h dn c t bz ash bsh sr tr m ∧
    st = stNext N W AccW h (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c t bz ash bsh sr tr m

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- **The phase model** at `(N, W, AccW)`, latency `⌈N/2⌉ + 2`. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) (lat N W AccW) (design.sem N W AccW) where
  Shape := I N W AccW ((N + 1) / 2)
  Step := Stp N W AccW ((N + 1) / 2)
  init := st_init N W AccW hN hW hA (rng_facts hN hW hNW).1
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (st_cycle N W AccW hN hW hA (rng_facts hN hW hNW).1 σ e ck r s a b dn c t bz ash bsh sr tr m k 40
        (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, -, hw, rfl⟩
    exact stNext_I N W AccW _ _ _ _ _ _ dn c t bz ash bsh sr tr m hw
  Ready st := ∃ ck r s a b c t ash bsh sr tr m, st = SS ck r s a b (knownBit false) c t (knownBit false) ash bsh sr tr m
  Busy x mm st := ∃ t, t + mm + 1 = lat N W AccW ∧ BusyAt N W AccW ((N + 1) / 2) x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, t, ash, bsh, sr, tr, m, rfl⟩
    simp [BitIs, Tasks.Matmul.task, SS, SvState.lookup]
  busy_done := by
    rintro x mm st ⟨t, -, ck, r, s, a, b, c, sr, tr, m, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, SS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, t, ash, bsh, sr, tr, m, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, SS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', t', ash', bsh', sr', tr', m', h⟩ := next_reset (N := N) (W := W) (AccW := AccW) (h := (N + 1) / 2)
      (appIn e "clk" ck) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn c t bz ash bsh sr tr m hw.1 hw.2.2.2.1
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, hw, rfl⟩ hprev hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    have hbz : bz = knownBit false := by
      rcases hprev with ⟨ck', r', s', a', b', c', t', ash', bsh', sr', tr', m', hp⟩ | ⟨y, ck', r', s', a', b', t', ash',
        bsh', sr', tr', m', hp⟩
      · exact (SS_inj hp).2.2.2.1
      · exact (SS_inj hp).2.2.2.1
    subst hbz
    obtain ⟨w1, -, w3, -, w5, w6, -, -, -⟩ := hw
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb, next_start _ _ _ dn c t ash bsh sr tr m w1 w3 w5 w6]
    refine .inr ⟨(N + 1) / 2 + 1, by simp only [lat]; omega, 0, by simp only [lat]; omega, _, _, _, _, _, _, _, _, _, rfl,
      fun k hk => absurd hk (by omega)⟩
  busy := by
    rintro e prev st x mm - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, hw, rfl⟩
      ⟨t0, ht, ck', r', s', a', b', c', sr', tr', m', hb, hinv⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := SS_inj hb
    obtain ⟨-, w2, -, -, -, -, w7, w8, w9⟩ := hw
    simp only [lat] at ht
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    by_cases hlast : t0 = (N + 1) / 2 + 1
    · subst hlast
      obtain ⟨rfl, rfl, rfl⟩ := hinv ((N + 1) / 2) rfl
      obtain ⟨t', ash', bsh', sr'', tr'', m'', h⟩ := next_last (AccW := AccW) (h := (N + 1) / 2) hN hW (by omega)
        (by omega) (by omega) hNW x.1 x.2.1 (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) c w2
      rw [h]
      exact .inl ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
    · rw [next_busy hN hW (by omega) (by omega) (by omega) hNW x.1 x.2.1 (by omega) _ _ _ _ _ _ _ w7 w8 w9 hinv]
      exact .inr ⟨mm - 1, by omega, t0 + 1, by simp only [lat]; omega, _, _, _, _, _, _, _, _, _, rfl,
        fun k hk => by obtain rfl : k = t0 := by omega
                       exact ⟨rfl, rfl, rfl⟩⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', t', ash', bsh', sr', tr', m', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := SS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, t, bz, ash, bsh, sr, tr, m, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', t', ash', bsh', sr', tr', m', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := SS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem st_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [st_sem_eq N W AccW hN hW hA hN31]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "t", "busy", "a_sh", "b_sh", "S", "T", "M"] : List String).Nodup
    decide⟩

theorem st_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [st_sem_eq N W AccW hN hW hA hN31]
  refine ⟨by simp [Tasks.Matmul.task, stD, stDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ ctrlP N W ((N + 1) / 2) :: genPs N W AccW ((N + 1) / 2) := by simpa [stD] using hp
  rcases st_mem hm with rfl | ⟨u, rfl⟩ | ⟨v, rfl⟩ | ⟨u, v, k, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ | ⟨u, v, rfl⟩ |
    ⟨u, v, rfl⟩ <;>
    simp [Tasks.Matmul.task, ctrlP, saP, tbP, wS, wT, preE, preF, sx1, sxA, macP, cP, c11P, c12P, c21P, c22P,
      e11, e12, e21, e22, mS, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]

/-- **Rule 1.** -/
theorem st_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    MooreOutDep (design.sem N W AccW) [] := by
  obtain ⟨_, h2, h3⟩ := hh_facts N hN
  rw [st_sem_eq N W AccW hN hW hA hN31]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (st_profile N W AccW _ h2 h3)))
    (by simp [stD, stDecls, Design2.outputNames, Design2.inputNames])

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem allKnown_ofInt (w : Nat) (v : Int) : (LVec.ofInt w v).allKnown = true := by
  rw [LVec.ofInt_eq_ofBitVec]; exact LVec.allKnown_ofBitVec _

theorem width_ofInt (w : Nat) (v : Int) : (LVec.ofInt w v).width = w := by
  rw [LVec.ofInt_eq_ofBitVec]; exact LVec.width_ofBitVec _

macro "xs_simp" : tactic => `(tactic| simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW,
  sigWidth, stD, stDecls, ctrlP, saP, tbP, wS, wT, preE, preF, sx1, sxA, macP, cP, c11P, c12P, c21P, c22P, e11, e12,
  e21, e22, mS, nb, c32, lvec_l0_known, lvec_l1_known, LVec.replicate_l0, allKnown_ofInt, width_ofInt, *])

theorem ctrl_xsafe (N W AccW h : Nat) : xsProc (stD N W AccW h) (ctrlP N W h) = true := by
  xs_simp

/-- The window facts of an entry `p` of `a_sh`/`b_sh`. -/
theorem entW {N W h p : Nat} (hW : 1 ≤ W) (hp : p + 1 ≤ (2 * h + 1) * N) :
    p * W + W ≤ (2 * h + 1) * N * W ∧ p * W + W - 1 + 1 ≤ (2 * h + 1) * N * W := by
  have := Nat.mul_le_mul_right W hp; rw [Nat.succ_mul] at this; omega

theorem sa_xsafe {N W AccW h u : Nat} (hW : 1 ≤ W) (hu : u < h) (hhN : h ≤ N) :
    xsProc (stD N W AccW h) (saP N W h u) = true := by
  obtain ⟨p1, p2, p3, p4⟩ := posA hu hhN
  obtain ⟨a1, b1⟩ := entW (W := W) hW p1
  obtain ⟨a2, b2⟩ := entW (W := W) hW p2
  obtain ⟨a3, b3⟩ := entW (W := W) hW p3
  obtain ⟨a4, b4⟩ := entW (W := W) hW p4
  clear p1 p2 p3 p4
  xs_simp

theorem tb_xsafe {N W AccW h v : Nat} (hW : 1 ≤ W) (hv : v < h) (hhN : h ≤ N) :
    xsProc (stD N W AccW h) (tbP N W h v) = true := by
  obtain ⟨p1, p2, p3, p4⟩ := posB hv hhN
  obtain ⟨a1, b1⟩ := entW (W := W) hW p1
  obtain ⟨a2, b2⟩ := entW (W := W) hW p2
  obtain ⟨a3, b3⟩ := entW (W := W) hW p3
  obtain ⟨a4, b4⟩ := entW (W := W) hW p4
  clear p1 p2 p3 p4
  xs_simp

/-- Lane `k` of cell `(u, v)` of the engines lies in `M`. -/
theorem mlane_le {h AccW u v : Nat} (hu : u < h) (hv : v < h) (k : Nat) (hk : k < 7) :
    ((u * h + v) * 7 + k) * AccW + AccW ≤ 7 * h * h * AccW := by
  have hc := cell_lt hu hv
  exact fam_le (by rw [Nat.mul_assoc 7]; omega)

theorem mac_xsafe {N W AccW h u v r : Nat} (hu : u < h) (hv : v < h) (hr : r < 7) :
    xsProc (stD N W AccW h) (macP h W AccW u v r) = true := by
  have hm := mlane_le (AccW := AccW) hu hv r hr
  have hs := fam_le (w := W + 1) (show u * 7 + r < 7 * h by omega)
  have ht := fam_le (w := W + 1) (show v * 7 + r < 7 * h by omega)
  have hs1 : (u * 7 + r) * (W + 1) + W + 1 ≤ 7 * h * (W + 1) := by omega
  have ht1 : (v * 7 + r) * (W + 1) + W + 1 ≤ 7 * h * (W + 1) := by omega
  xs_simp

theorem c11_xsafe {N W AccW h u v : Nat} (hu : u < h) (hv : v < h) : xsProc (stD N W AccW h) (c11P N h AccW u v) = true := by
  have m0 := mlane_le (AccW := AccW) hu hv 0 (by omega)
  have m3 := mlane_le (AccW := AccW) hu hv 3 (by omega)
  have m4 := mlane_le (AccW := AccW) hu hv 4 (by omega)
  have m6 := mlane_le (AccW := AccW) hu hv 6 (by omega)
  simp only [Nat.add_zero] at m0
  xs_simp

theorem c12_xsafe {N W AccW h u v : Nat} (hu : u < h) (hv : v < h) : xsProc (stD N W AccW h) (c12P N h AccW u v) = true := by
  have m2 := mlane_le (AccW := AccW) hu hv 2 (by omega)
  have m4 := mlane_le (AccW := AccW) hu hv 4 (by omega)
  xs_simp

theorem c21_xsafe {N W AccW h u v : Nat} (hu : u < h) (hv : v < h) : xsProc (stD N W AccW h) (c21P N h AccW u v) = true := by
  have m1 := mlane_le (AccW := AccW) hu hv 1 (by omega)
  have m3 := mlane_le (AccW := AccW) hu hv 3 (by omega)
  xs_simp

theorem c22_xsafe {N W AccW h u v : Nat} (hu : u < h) (hv : v < h) : xsProc (stD N W AccW h) (c22P N h AccW u v) = true := by
  have m0 := mlane_le (AccW := AccW) hu hv 0 (by omega)
  have m1 := mlane_le (AccW := AccW) hu hv 1 (by omega)
  have m2 := mlane_le (AccW := AccW) hu hv 2 (by omega)
  have m5 := mlane_le (AccW := AccW) hu hv 5 (by omega)
  simp only [Nat.add_zero] at m0
  xs_simp

theorem st_mem' {N W AccW h : Nat} {p : Process2} (hp : p ∈ ctrlP N W h :: genPs N W AccW h) :
    p = ctrlP N W h ∨ (∃ u, u < h ∧ p = saP N W h u) ∨ (∃ v, v < h ∧ p = tbP N W h v) ∨
      (∃ u v r, u < h ∧ v < h ∧ r < 7 ∧ p = macP h W AccW u v r) ∨
      (∃ u v, u < h ∧ v < h ∧ p = c11P N h AccW u v) ∨ (∃ u v, u < h ∧ v < N - h ∧ p = c12P N h AccW u v) ∨
      (∃ u v, u < N - h ∧ v < h ∧ p = c21P N h AccW u v) ∨ ∃ u v, u < N - h ∧ v < N - h ∧ p = c22P N h AccW u v := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact .inl rfl
  simp only [genPs, cPs, List.mem_append] at hp
  rcases hp with ((hp | hp) | hp) | hp | hp
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hp; exact .inr (.inl ⟨u, List.mem_range.mp hu, rfl⟩)
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp; exact .inr (.inr (.inl ⟨v, List.mem_range.mp hv, rfl⟩))
  · obtain ⟨u, v, r, hu, hv, hr, rfl⟩ := st_pe_mem hp; exact .inr (.inr (.inr (.inl ⟨u, v, r, hu, hv, hr, rfl⟩)))
  · simp only [cTop, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range] at hp
    obtain ⟨u, hu, (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)⟩ := hp
    · exact .inr (.inr (.inr (.inr (.inl ⟨u, v, hu, hv, rfl⟩))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨u, v, hu, hv, rfl⟩)))))
  · simp only [cBot, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range] at hp
    obtain ⟨u, hu, (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)⟩ := hp
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨u, v, hu, hv, rfl⟩))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨u, v, hu, hv, rfl⟩))))))

/-- **Rule 3.** -/
theorem st_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hN31 : N < 2 ^ 31) :
    XSafe (design.sem N W AccW) := by
  obtain ⟨_, h2, h3⟩ := hh_facts N hN
  rw [st_sem_eq N W AccW hN hW hA hN31]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ ctrlP N W ((N + 1) / 2) :: genPs N W AccW ((N + 1) / 2) := by simpa [stD] using hp
  rcases st_mem' hm with rfl | ⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨u, v, r, hu, hv, hr, rfl⟩ | ⟨u, v, hu, hv, rfl⟩ |
    ⟨u, v, hu, hv, rfl⟩ | ⟨u, v, hu, hv, rfl⟩ | ⟨u, v, hu, hv, rfl⟩
  · exact ctrl_xsafe N W AccW _
  · exact sa_xsafe hW hu h2
  · exact tb_xsafe hW hv h2
  · exact mac_xsafe hu hv hr
  · exact c11_xsafe hu hv
  · exact c12_xsafe hu (by omega)
  · exact c21_xsafe (by omega) hv
  · exact c22_xsafe (by omega) (by omega)

/-- **The design satisfies the matmul statement (txtask-v2) at latency `⌈N/2⌉ + 2`** (`4` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  have hN31 := (rng_facts hN hW hNW).1
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (st_interface N W AccW hN hW hA hN31)
    (st_disciplined N W AccW hN hW hA hN31) (st_terminatesPU N W AccW hN hW hA hN31)
    (show 1 ≤ lat N W AccW by simp only [lat]; omega) (model N W AccW hN hW hA hNW)
    (st_powerUp N W AccW hN hW hA hN31) (st_moore N W AccW hN hW hA hN31) (st_xsafe N W AccW hN hW hA hN31)

end Submission
