import Submission.Design
import LeanModels.Sv.Gen2
import LeanModels.Sv.Loop2
import SvGolf.Cycle
import SvGolf.Seq
import SvGolf.React

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 0. Width function `W = (N <= 1) ? 1 : $clog2(N)` -/

/-- Bit width of `gid` / `ngid`: `1` when `N ≤ 1`, else `clog2 N`. -/
def Wfn (N : Nat) : Nat := if N ≤ 1 then 1 else clog2 N

theorem clog2_le_self (n : Nat) : clog2 n ≤ n := by
  unfold clog2
  split
  · omega
  · next h =>
    have h1 : Nat.log2 (n - 1) < n - 1 ∨ n - 1 = 0 := by
      rcases Nat.eq_zero_or_pos (n - 1) with hz | hp
      · exact Or.inr hz
      · left
        have := Nat.log2_self_le (Nat.ne_of_gt hp)
        have hlt : Nat.log2 (n - 1) < 2 ^ Nat.log2 (n - 1) := Nat.lt_two_pow_self
        omega
    omega

theorem le_two_pow_clog2_self (n : Nat) : n ≤ 2 ^ clog2 n := by
  unfold clog2
  split
  · next h =>
    have : (1 : Nat) = 2 ^ 0 := rfl
    omega
  · next h =>
    have hp : n - 1 ≠ 0 := by omega
    have hlt := (Nat.log2_lt hp).mp (Nat.lt_succ_self (Nat.log2 (n - 1)))
    omega

theorem Wfn_pos (N : Nat) : 1 ≤ Wfn N := by
  unfold Wfn
  split
  · omega
  · next h =>
    unfold clog2
    split
    · omega
    · omega

theorem Wfn_le {N : Nat} (hN : 1 ≤ N) : Wfn N ≤ N := by
  unfold Wfn
  split
  · omega
  · exact clog2_le_self N

theorem le_two_pow_Wfn (N : Nat) : N ≤ 2 ^ Wfn N := by
  unfold Wfn
  split
  · next h => omega
  · exact le_two_pow_clog2_self N

abbrev Rng32 (N : Nat) : Prop := N < 2147483648

theorem rng32_of {N : Nat} (hN : 1 ≤ N) (hNN : N * N < 2 ^ 31) : Rng32 N := by
  have := Nat.le_mul_of_pos_right N hN
  show N < 2147483648
  omega

/-! ## 1. Hand-built mirror `arbD` and agreement with `design.sem` -/

abbrev z0 (w : Nat) : LVec := LVec.replicate w .l0
abbrev one1 : LVec := ⟨#[.l1]⟩
abbrev zero1 : LVec := ⟨#[.l0]⟩

def scanStep (src : String) (N W k : Nat) : Stmt2 :=
  .block #[
    .ifStmt
      (.binary .ne
        (.binary .and
          (.binary (.shr false) (.ident src) (.lit (LVec.ofInt 32 (k : Int))))
          (.ident "one"))
        (.lit (z0 N)))
      (.blockingAssign (.ident "ngid") (.lit (LVec.ofInt W (k : Int))))
      none]

def loopStmt (src : String) (N W : Nat) : Stmt2 :=
  .block ((List.range N).map (scanStep src N W)).toArray

def combBody (N W : Nat) : Stmt2 :=
  .block #[
    .blockingAssign (.ident "ngid") (.lit (z0 W)),
    loopStmt "req" N W,
    loopStmt "rm" N W]

def ffBody (N : Nat) : Stmt2 :=
  .block #[
    .ifStmt (.ident "rst")
      (.nbaAssign (.ident "valid") (.lit zero1))
      (some (.nbaAssign (.ident "valid") (.binary .ne (.ident "req") (.lit (z0 N))))),
    .nbaAssign (.ident "gid") (.ident "ngid")]

def arbP0 (N : Nat) : Process2 := .assign (.ident "one") (.resize N (.lit one1))
def arbP1 : Process2 := .assign (.ident "oh") (.binary (.shl false) (.ident "one") (.ident "gid"))
def arbP2 (N : Nat) : Process2 := .assign (.ident "gnt") (.ternary (.ident "valid") (.ident "oh") (.lit (z0 N)))
def arbP3 (N : Nat) : Process2 := .assign (.ident "mask") (.binary .sub (.ident "oh") (.resize N (.lit one1)))
def arbP4 : Process2 := .assign (.ident "rm") (.binary .and (.ident "req") (.ident "mask"))
def arbP5 (N W : Nat) : Process2 := .alwaysComb (combBody N W)
def arbP6 (N : Nat) : Process2 := .alwaysFF "clk" (ffBody N)

def arbDecls (N W : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true },
   { name := "rst", width := 1, isInput := true },
   { name := "req", width := N, isInput := true },
   { name := "gnt", width := N, isOutput := true },
   { name := "valid", width := 1 },
   { name := "gid", width := W },
   { name := "one", width := N },
   { name := "oh", width := N },
   { name := "mask", width := N },
   { name := "rm", width := N },
   { name := "ngid", width := W }]

def arbProcs (N W : Nat) : List Process2 :=
  [arbP0 N, arbP1, arbP2 N, arbP3 N, arbP4, arbP5 N W, arbP6 N]

def arbD (N : Nat) : Design2 where
  name := "arbiter"
  decls := (arbDecls N (Wfn N)).toArray
  processes := (arbProcs N (Wfn N)).toArray

/-! ### Instantiation of `design.pdesign` -/

private def wExpr : PExpr :=
  .squash2 32
    ((PExpr.binary .sle (.paramRef "N" none) (.int 1)).ternary (.int 1)
      (.sysCall .clog2 (.paramRef "N" none)))

private theorem evalAt_clog2_eq (env : IEnv) (ty : Nat × Bool) (e : PExpr) :
    evalAt env ty (.sysCall .clog2 e) = (do
      let ety ← ctype env e
      let v ← evalAt env ety e
      .ok (convertConst 32 ty.1 ty.2 (clog2 (v.emod ((2 : Int) ^ ety.1)).toNat : Int))) := rfl

private theorem wExpr_eval (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    evalIntTarget { nvals := [("N", (canonInt 32 true (N : Int), 32, true))], int32 := true } wExpr =
      .ok (Wfn N : Int) := by
  have hcN : canonInt 32 true (N : Int) = N := SvGolf.Cycle.canonInt32_natCast hR32
  have hcvN : convertConst 32 32 true (N : Int) = N := SvGolf.Cycle.convertConst32_natCast hR32
  have h1 : convertConst 32 32 true 1 = 1 := by decide
  have hmN : (N : Int).emod 4294967296 = N := SvGolf.Cycle.natCast_emod_4294967296 hR32
  have hcl : convertConst 32 32 true ((clog2 N : Nat) : Int) = (clog2 N : Nat) :=
    SvGolf.Cycle.convertConst32_natCast (by have := clog2_le_self N; omega)
  have hsle : evalAt { nvals := [("N", ((N : Int), 32, true))], int32 := true } (1, false)
      (PExpr.binary .sle (.paramRef "N" none) (.int 1)) =
      .ok (if (N : Int) ≤ 1 then 1 else 0) := by
    simp only [evalAt, ctype, SymBinOp.constClass, List.lookup, hcvN, h1, Nat.max_self,
      Bool.and_self, beq_self_eq_true, Gen2.except_ok_bind]
    change (if false = true then Except.error _
            else Except.ok (convertConst 1 1 false (if decide ((N : Int) ≤ 1) = true then 1 else 0))) = _
    rw [ite_eq_right (fun h => absurd h Bool.false_ne_true)]
    by_cases h : (N : Int) ≤ 1 <;> simp [h, convertConst, canonInt] <;> rfl
  simp only [wExpr, evalIntTarget, PExpr.isInt, Bool.false_eq_true, ↓reduceIte, evalIntExact,
    evalIntExactRec, evalSized, Bool.not_true, ctype, Gen2.except_ok_bind,
    PExpr.pushedTarget, hcN]
  unfold evalAt
  simp only [ctype, SymBinOp.constClass, Gen2.except_ok_bind,
    Bool.and_self, Nat.max_self, hsle, SvGolf.Cycle.ite_one_zero_bne]
  by_cases hle : N ≤ 1
  · have hleI : (N : Int) ≤ 1 := by omega
    simp [Wfn, hle, hleI, evalAt, h1, Gen2.except_ok_bind]
  · have hleI : ¬ (N : Int) ≤ 1 := by omega
    simp only [Wfn, hle, hleI, ↓reduceIte, decide_false, Bool.false_eq_true]
    rw [evalAt_clog2_eq]
    simp only [ctype, evalAt, List.lookup, beq_self_eq_true, hcvN, Gen2.except_ok_bind]
    show Except.ok (convertConst 32 32 true (clog2 ((N : Int).emod 4294967296).toNat : Int)) = .ok (clog2 N : Int)
    rw [hmN, Int.toNat_natCast, hcl]

private def arbScope (N W : Nat) : IEnv :=
  { nvals := [("W", ((W : Int), 32, true)), ("N", ((N : Int), 32, true))],
    pwidths := [("N", 32), ("W", 32)],
    int32 := true }

private def arbEnv0 (N W : Nat) : IEnv :=
  { arbScope N W with dims := dimTable (arbScope N W) design.pdesign.decls }

private def withW (e : IEnv) (ds : List Decl) : IEnv :=
  { e with widths := ds.map fun dc => (dc.name, dc.width) }

private def arbEnv (N W : Nat) : IEnv :=
  withW (arbEnv0 N W) (arbDecls N W)

private theorem arb_combGuard (N W : Nat) (env : IEnv)
    (hng : env.widths.lookup "ngid" = some W) :
    combGuardProc (fun n => env.widths.lookup n) (combBody N W) = .alwaysComb (combBody N W) := by
  have hwhole : CombGuard.whole (fun n => env.widths.lookup n) "ngid" = ("ngid", 0, W) := by
    simp [CombGuard.whole, hng]
  have hscan : ∀ (src : String), ∀ s ∈ ((List.range N).map (scanStep src N W)),
      Loop2.GuardIn (fun n => env.widths.lookup n) [("ngid", 0, W)] s := by
    intro src s hs
    simp only [List.mem_map, List.mem_range] at hs
    obtain ⟨k, _, rfl⟩ := hs
    refine Loop2.GuardIn.block ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨?_, ?_⟩
    · intro x hx
      simp [Stmt2.mayW, Stmt2.optMayW, Lhs2.mayW, hwhole] at hx
      subst hx
      exact fun n i hm => ⟨("ngid", 0, W), List.mem_cons_self, hm⟩
    · intro M A hM hA
      have hc : CombGuard.readsViol M
          (Stmt2.mayW (fun n => env.widths.lookup n)
            (.blockingAssign (.ident "ngid") (.lit (LVec.ofInt W (k : Int)))) ++
           Stmt2.optMayW (fun n => env.widths.lookup n) none ++ A)
          (Expr2.rdW (fun n => env.widths.lookup n)
            (.binary .ne
              (.binary .and
                (.binary (.shr false) (.ident src) (.lit (LVec.ofInt 32 (k : Int))))
                (.ident "one"))
              (.lit (z0 N)))) = none := by
        apply Loop2.readsViol_covered
        intro x hx
        simp only [List.mem_append, Stmt2.mayW, Stmt2.optMayW, Lhs2.mayW, hwhole,
          List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | hx
        · exact hM _ (fun n i hm => ⟨("ngid", 0, W), List.mem_cons_self, hm⟩)
        · exact hM _ (hA x hx)
      have ha : (Stmt2.blockingAssign (.ident "ngid") (.lit (LVec.ofInt W (k : Int)))).combViol
          (fun n => env.widths.lookup n) M A = none := by
        simp [Stmt2.combViol, Expr2.rdW, Lhs2.rdW, CombGuard.readsViol]
      simp only [Stmt2.combViol, Stmt2.optCombViol, hc]
      rw [show CombGuard.readsViol M (Lhs2.mayW (fun n => env.widths.lookup n) (.ident "ngid") ++ A)
            (Expr2.rdW (fun n => env.widths.lookup n) (.lit (LVec.ofInt W (k : Int))) ++
             Lhs2.rdW (fun n => env.widths.lookup n) (.ident "ngid")) = none from ha]
      rfl
  have hg1 : Loop2.GuardIn (fun n => env.widths.lookup n) [("ngid", 0, W)] (loopStmt "req" N W) :=
    Loop2.GuardIn.block (hscan "req")
  have hg2 : Loop2.GuardIn (fun n => env.widths.lookup n) [("ngid", 0, W)] (loopStmt "rm" N W) :=
    Loop2.GuardIn.block (hscan "rm")
  have hviol : (combBody N W).combViol (fun n => env.widths.lookup n) [] [] = none := by
    have h0 : (Stmt2.blockingAssign (.ident "ngid") (.lit (z0 W))).combViol
        (fun n => env.widths.lookup n) []
        (Stmt2.listMayW (fun n => env.widths.lookup n) [loopStmt "req" N W, loopStmt "rm" N W] ++ []) = none := by
      simp [Stmt2.combViol, Expr2.rdW, Lhs2.rdW, CombGuard.readsViol]
    have hM0 : (Stmt2.blockingAssign (.ident "ngid") (.lit (z0 W))).mustW
        (fun n => env.widths.lookup n) = [("ngid", 0, W)] := by
      simp [Stmt2.mustW, Lhs2.mustW, hwhole]
    have hrest : Stmt2.listCombViol (fun n => env.widths.lookup n) [("ngid", 0, W)] []
        [loopStmt "req" N W, loopStmt "rm" N W] = none :=
      Loop2.GuardIn.list [loopStmt "req" N W, loopStmt "rm" N W] [("ngid", 0, W)] []
        (fun s hs => by simp at hs; rcases hs with rfl | rfl; exact hg1; exact hg2)
        (fun _ hx => hx) (by simp)
    show ((Stmt2.blockingAssign (.ident "ngid") (.lit (z0 W))).combViol
            (fun n => env.widths.lookup n) []
            (Stmt2.listMayW (fun n => env.widths.lookup n) [loopStmt "req" N W, loopStmt "rm" N W] ++ []) <|>
          Stmt2.listCombViol (fun n => env.widths.lookup n)
            ([] ++ (Stmt2.blockingAssign (.ident "ngid") (.lit (z0 W))).mustW (fun n => env.widths.lookup n))
            [] [loopStmt "req" N W, loopStmt "rm" N W]) = none
    rw [h0, hM0, List.nil_append, hrest]
    rfl
  simp [combGuardProc, hviol]

private theorem loop_forValues (N W : Nat) :
    forValues2 (arbEnv N W) "k" (.int 0)
      (.binary .slt (.genvarRef "k") (.paramRef "N" none))
      (.unary .inc (.genvarRef "k")) = .ok (intRange 0 N) := by
  apply Loop2.forValues2_upto
  · intro v; simp [PExpr.isInt, IEnv.bindVal, arbEnv, withW, arbEnv0, arbScope, List.lookup]
  · intro v; simp [evalInt, IEnv.bindVal, arbEnv, withW, arbEnv0, arbScope, List.lookup]
  · simp [evalInt, arbEnv, withW, arbEnv0, arbScope, List.lookup]

private theorem inst_ne_fill (env : IEnv) (elems : List (String × Nat)) (ctx : Option Nat)
    (e : PExpr) (w : Nat) (hw : selfWidth2 env elems e = some w) :
    instExpr2 env elems ctx (.binary (.m0 .ne) e (.fill .l0)) =
      .binary .ne (fitExpr2 env elems (some w) e) (.lit (z0 w)) := by
  simp only [instExpr2, hw, selfWidth2]
  change Expr2.binary .ne (fitExpr2 env elems (some w) e) (fitExpr2 env elems (some w) (.fill .l0)) = _
  simp [fitExpr2, rigidExpr, instExpr2, z0]

private theorem arb_inst_loop (N W : Nat) (src : String)
    (hsrc : (arbEnv N W).widths.lookup src = some N) (elems : List (String × Nat)) :
    instStmt2 (arbEnv N W) elems
      (.forLoop "k" (.int 0)
        (.binary .slt (.genvarRef "k") (.paramRef "N" none))
        (.unary .inc (.genvarRef "k"))
        (.block
          [.ifStmt
            (.binary (.m0 .ne)
              (.binary (.m0 .and)
                (.binary (.m0 (.shr false)) (.ident src) (.genvarRef "k"))
                (.ident "one"))
              (.fill .l0))
            (.blockingAssign "ngid" (.genvarRef "k")) none])) =
      loopStmt src N W := by
  simp only [instStmt2, loop_forValues N W, loopStmt, intRange_eq_map, List.map_map]
  congr 1
  apply congrArg List.toArray
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_def, scanStep, instStmt2, instStmts2]
  have hsrc' : List.lookup src (arbEnv N W).widths = some N := hsrc
  have hone : List.lookup "one" (arbEnv N W).widths = some N := rfl
  have hng : List.lookup "ngid" (arbEnv N W).widths = some W := rfl
  have hsw : selfWidth2 ((arbEnv N W).bindVal "k" (0 + (k : Int))) elems
      (.binary (.m0 .and) (.binary (.m0 (.shr false)) (.ident src) (.genvarRef "k")) (.ident "one")) = some N := by
    simp only [selfWidth2, divOperandWidth2, IEnv.bindVal, hsrc', hone, Nat.max_self]
  rw [inst_ne_fill _ _ none _ N hsw]
  have hsh : fitExpr2 ((arbEnv N W).bindVal "k" (0 + (k : Int))) elems (some N)
      (.binary (.m0 (.shr false)) (.ident src) (.genvarRef "k")) =
      .binary (.shr false) (.ident src) (.lit (LVec.ofInt 32 (k : Int))) := by
    simp only [fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte, instExpr2, divOperandWidth2,
      shiftAmtWidth2, IEnv.bindVal, hsrc', maxW2_some, Nat.max_self, ctxTrunc2, Nat.le_refl,
      instDivOperand2, fitDivOperand2, List.lookup, beq_self_eq_true, Int.zero_add]
    rfl
  have hkW : fitExpr2 ((arbEnv N W).bindVal "k" (0 + (k : Int))) elems (some W) (.genvarRef "k") =
      .lit (LVec.ofInt W (k : Int)) := by
    simp only [fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte, instExpr2,
      IEnv.bindVal, List.lookup, beq_self_eq_true, Int.zero_add]
    rfl
  have hand : fitExpr2 ((arbEnv N W).bindVal "k" (0 + (k : Int))) elems (some N)
      (.binary (.m0 .and) (.binary (.m0 (.shr false)) (.ident src) (.genvarRef "k")) (.ident "one")) =
      .binary .and (.binary (.shr false) (.ident src) (.lit (LVec.ofInt 32 (k : Int)))) (.ident "one") := by
    simp only [fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte, instExpr2, hsh]
    simp only [selfWidth2, IEnv.bindVal, hone, beq_self_eq_true, ↓reduceIte]
  have hng' : List.lookup "ngid" ((arbEnv N W).bindVal "k" (0 + (k : Int))).widths = some W := hng
  rw [hand, hng', hkW]

private theorem one1_width : one1.width = 1 := rfl

private theorem inst_resize_one1 (env : IEnv) (elems : List (String × Nat)) (N : Nat) :
    instExpr2 env elems (some N) (.resize 8 (.lit one1)) = .resize N (.lit one1) := by
  have hlit : instExpr2 env elems (some 1) (.lit one1) = .lit one1 := by simp [one1]
  unfold instExpr2
  simp only [selfWidth2, PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, one1_width,
    Bool.false_eq_true, ↓reduceIte, hlit]
  split <;> rfl

private theorem inst_fit_resize_one1 (env : IEnv) (elems : List (String × Nat)) (N : Nat) :
    fitExpr2 env elems (some N) (.resize 8 (.lit one1)) = .resize N (.lit one1) := by
  simp only [fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte]
  exact inst_resize_one1 env elems N

private theorem arb_inst_p0 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.assign "one" (.resize 8 (.lit one1))) = arbP0 N := by
  have hone : (arbEnv N W).widths.lookup "one" = some N := rfl
  simp only [instProcess2, hone, arbP0]
  rw [inst_fit_resize_one1]

private theorem arb_inst_p1 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.assign "oh" (.binary (.m0 (.shl false)) (.ident "one") (.ident "gid"))) = arbP1 := by
  sv2_inst_simp [arbEnv, withW, arbEnv0, arbScope, arbDecls, arbP1,
    instDivOperand2, fitDivOperand2, ctxTrunc2, divOperandWidth2, shiftAmtWidth2]

private theorem arb_inst_p2 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.assign "gnt" ((PExpr.ident "valid").ternary (.ident "oh") (.fill .l0))) = arbP2 N := by
  sv2_inst_simp [arbEnv, withW, arbEnv0, arbScope, arbDecls, arbP2, z0]

private theorem arb_inst_p3 (N W : Nat) (hN : 1 ≤ N) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.assign "mask" (.binary (.m0 .sub) (.ident "oh") (.resize 8 (.lit one1)))) = arbP3 N := by
  have hmask : (arbEnv N W).widths.lookup "mask" = some N := rfl
  have hoh : (arbEnv N W).widths.lookup "oh" = some N := rfl
  simp only [instProcess2, hmask, fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte,
    instExpr2, ctxOpWidth2, selfWidth2, rigidMax2, hoh, one1_width, maxW2_some, Option.getD_some,
    Nat.max_eq_left hN, Nat.le_refl, beq_self_eq_true, arbP3]
  rw [inst_resize_one1]

private theorem arb_inst_p4 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.assign "rm" (.binary (.m0 .and) (.ident "req") (.ident "mask"))) = arbP4 := by
  sv2_inst_simp [arbEnv, withW, arbEnv0, arbScope, arbDecls, arbP4]

private theorem arb_inst_p5 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.alwaysComb (.block
        [.blockingAssign "ngid" (.fill .l0),
         .forLoop "k" (.int 0) (.binary .slt (.genvarRef "k") (.paramRef "N" none))
           (.unary .inc (.genvarRef "k"))
           (.block [.ifStmt
             (.binary (.m0 .ne)
               (.binary (.m0 .and)
                 (.binary (.m0 (.shr false)) (.ident "req") (.genvarRef "k"))
                 (.ident "one"))
               (.fill .l0))
             (.blockingAssign "ngid" (.genvarRef "k")) none]),
         .forLoop "k" (.int 0) (.binary .slt (.genvarRef "k") (.paramRef "N" none))
           (.unary .inc (.genvarRef "k"))
           (.block [.ifStmt
             (.binary (.m0 .ne)
               (.binary (.m0 .and)
                 (.binary (.m0 (.shr false)) (.ident "rm") (.genvarRef "k"))
                 (.ident "one"))
               (.fill .l0))
             (.blockingAssign "ngid" (.genvarRef "k")) none])])) = arbP5 N W := by
  have hbody : instStmt2 (arbEnv N W) elems
      (.block
        [.blockingAssign "ngid" (.fill .l0),
         .forLoop "k" (.int 0) (.binary .slt (.genvarRef "k") (.paramRef "N" none))
           (.unary .inc (.genvarRef "k"))
           (.block [.ifStmt
             (.binary (.m0 .ne)
               (.binary (.m0 .and)
                 (.binary (.m0 (.shr false)) (.ident "req") (.genvarRef "k"))
                 (.ident "one"))
               (.fill .l0))
             (.blockingAssign "ngid" (.genvarRef "k")) none]),
         .forLoop "k" (.int 0) (.binary .slt (.genvarRef "k") (.paramRef "N" none))
           (.unary .inc (.genvarRef "k"))
           (.block [.ifStmt
             (.binary (.m0 .ne)
               (.binary (.m0 .and)
                 (.binary (.m0 (.shr false)) (.ident "rm") (.genvarRef "k"))
                 (.ident "one"))
               (.fill .l0))
             (.blockingAssign "ngid" (.genvarRef "k")) none])]) = combBody N W := by
    have hl1 := arb_inst_loop N W "req" rfl elems
    have hl2 := arb_inst_loop N W "rm" rfl elems
    have h0 : instStmt2 (arbEnv N W) elems (.blockingAssign "ngid" (.fill .l0)) =
        .blockingAssign (.ident "ngid") (.lit (z0 W)) := by
      have hng : (arbEnv N W).widths.lookup "ngid" = some W := rfl
      simp [instStmt2, fitExpr2, rigidExpr, instExpr2, hng, z0]
    unfold combBody
    rw [show instStmt2 (arbEnv N W) elems (.block _) =
        .block #[instStmt2 (arbEnv N W) elems (.blockingAssign "ngid" (.fill .l0)),
                 instStmt2 (arbEnv N W) elems (.forLoop "k" (.int 0)
                   (.binary .slt (.genvarRef "k") (.paramRef "N" none))
                   (.unary .inc (.genvarRef "k"))
                   (.block [.ifStmt
                     (.binary (.m0 .ne)
                       (.binary (.m0 .and)
                         (.binary (.m0 (.shr false)) (.ident "req") (.genvarRef "k"))
                         (.ident "one"))
                       (.fill .l0))
                     (.blockingAssign "ngid" (.genvarRef "k")) none])),
                 instStmt2 (arbEnv N W) elems (.forLoop "k" (.int 0)
                   (.binary .slt (.genvarRef "k") (.paramRef "N" none))
                   (.unary .inc (.genvarRef "k"))
                   (.block [.ifStmt
                     (.binary (.m0 .ne)
                       (.binary (.m0 .and)
                         (.binary (.m0 (.shr false)) (.ident "rm") (.genvarRef "k"))
                         (.ident "one"))
                       (.fill .l0))
                     (.blockingAssign "ngid" (.genvarRef "k")) none]))] from rfl]
    rw [h0, hl1, hl2]
  simp only [instProcess2, hbody, arbP5]
  exact arb_combGuard N W (arbEnv N W) rfl

private theorem arb_inst_p6 (N W : Nat) (elems : List (String × Nat)) :
    instProcess2 (arbEnv N W) elems
      (.alwaysFF "clk" (.block
        [.ifStmt (.ident "rst")
          (.nbaAssign "valid" (.lit zero1))
          (some (.nbaAssign "valid" (.binary (.m0 .ne) (.ident "req") (.fill .l0)))),
         .nbaAssign "gid" (.ident "ngid")])) = arbP6 N := by
  have hval : (arbEnv N W).widths.lookup "valid" = some 1 := rfl
  have hreq : (arbEnv N W).widths.lookup "req" = some N := rfl
  have hgid : (arbEnv N W).widths.lookup "gid" = some W := rfl
  have hngid : (arbEnv N W).widths.lookup "ngid" = some W := rfl
  have hne : fitExpr2 (arbEnv N W) elems (some 1) (.binary (.m0 .ne) (.ident "req") (.fill .l0)) =
      .binary .ne (.ident "req") (.lit (z0 N)) := by
    have hsw : selfWidth2 (arbEnv N W) elems (.ident "req") = some N := by simp [selfWidth2, hreq]
    simp only [fitExpr2, rigidExpr, Bool.false_eq_true, ↓reduceIte]
    rw [inst_ne_fill (arbEnv N W) elems (some 1) (.ident "req") N hsw]
    simp [fitExpr2, rigidExpr, selfWidth2, hreq]
  have hz1 : zero1.width = 1 := rfl
  simp only [instProcess2, instStmt2, instStmts2, hval, hgid, hne, arbP6, ffBody]
  simp [fitExpr2, rigidExpr, selfWidth2, hngid, hz1]

private theorem buildElems_arb (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    buildElems (arbEnv0 N W) design.pdesign.decls =
      .ok [("clk", 1), ("rst", 1), ("req", 1), ("gnt", 1), ("valid", 1), ("gid", 1),
           ("one", 1), ("oh", 1), ("mask", 1), ("rm", 1), ("ngid", 1)] := by
  have hN1 : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hW1 : ((W : Int) - 1).natAbs + 1 = W := by omega
  have hp1 : (pure 1 : Except String Nat) = .ok 1 := rfl
  simp [design.pdesign, buildElems, PType.width_packed_cons, PType.elemWidth, PDim.width,
    evalInt, arbEnv0, arbScope, List.lookup, Gen2.except_ok_bind, Res.ok_bind, hN1, hW1, hp1]

theorem arb_instantiate2 (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    design.pdesign.instantiate2 [N] (PDesign.surfaceFuel [N]) = .ok (arbD N) := by
  have hcN : canonInt 32 true (N : Int) = N := SvGolf.Cycle.canonInt32_natCast hR32
  have hW1 : 1 ≤ Wfn N := Wfn_pos N
  have hW32 : Wfn N < 2147483648 := by have := Wfn_le hN; omega
  have hcW : canonInt 32 true (Wfn N : Int) = Wfn N := SvGolf.Cycle.canonInt32_natCast hW32
  have hw := wExpr_eval N hN hR32
  have hN1 : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hWsub : ((Wfn N : Int) - 1).natAbs + 1 = Wfn N := by omega
  have hdecls : buildDecls (arbEnv0 N (Wfn N)) design.pdesign.decls = .ok (arbDecls N (Wfn N)) := by
    simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      arbEnv0, arbScope, List.lookup, arbDecls, Gen2.except_ok_bind, hN1, hWsub]
  have helems := buildElems_arb N (Wfn N) hN hW1
  simp only [PDesign.instantiate2, PDesign.instantiate2From, design.pdesign, bindPackageParams,
    bindPackageEnums, bindParamsRes, bindParams, bindLocals, bindLocal, bindEnums,
    IEnv.bindNVal, Except.mapError, SvGolf.Cycle.int_declConstType, SvGolf.Cycle.int_width,
    List.filterMapM, List.filterMapM.loop, Gen2.except_ok_bind, Bool.false_eq_true, ↓reduceIte,
    List.map, List.cons_append, List.nil_append, List.append_nil, List.reverse_cons,
    List.reverse_nil, Res.ok_bind, Res.pure_eq, List.length_cons, List.length_nil, bne_self_eq_false]
  rw [show evalIntTarget { nvals := [("N", (canonInt 32 true (N : Int), 32, true))], int32 := true }
        (.squash2 32 ((PExpr.binary .sle (.paramRef "N" none) (.int 1)).ternary (.int 1)
          (.sysCall .clog2 (.paramRef "N" none)))) = .ok (Wfn N : Int) from hw]
  simp only [hcN, hcW, Gen2.except_ok_bind, Res.ok_bind]
  change (do
    let decls ← buildDecls (arbEnv0 N (Wfn N)) design.pdesign.decls
    let elems ← buildElems (arbEnv0 N (Wfn N)) design.pdesign.decls
    let gens ← expandList2 (withW (arbEnv0 N (Wfn N)) decls) elems (PDesign.surfaceFuel [↑N]) []
    Res.ok (Design2.mk "arbiter" decls.toArray
      ((design.pdesign.processes.map (instProcess2 (withW (arbEnv0 N (Wfn N)) decls) elems)) ++ gens).toArray)) =
    .ok (arbD N)
  rw [hdecls, helems]
  simp only [expandList2, Res.ok_bind, List.append_nil]
  change Res.ok (Design2.mk "arbiter" (arbDecls N (Wfn N)).toArray
    (design.pdesign.processes.map (instProcess2 (arbEnv N (Wfn N)) _)).toArray) = .ok (arbD N)
  simp only [design.pdesign, List.map, arb_inst_p0, arb_inst_p1, arb_inst_p2, arb_inst_p3 _ _ hN,
    arb_inst_p4, arb_inst_p5, arb_inst_p6, arbD, arbProcs]

/-! ### One-driver rule and alias guard -/

private theorem loop_drvWins (src : String) (N W : Nat) :
    ∀ w ∈ (loopStmt src N W).drvWins, w.1 = "ngid" := by
  intro w hw
  simp only [loopStmt, Stmt2.drvWins] at hw
  obtain ⟨s, hs, hws⟩ := Loop2.mem_drvWinsList hw
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨k, _, rfl⟩ := hs
  simp [scanStep, Stmt2.drvWins, Stmt2.drvWinsList, Stmt2.drvWinsOpt, Lhs2.drvWins] at hws
  rw [hws]

private theorem p5_procWins (N W : Nat) :
    ∀ w ∈ (arbP5 N W).procWins, w.1 = "ngid" := by
  intro w hw
  simp only [arbP5, Process2.procWins, combBody, Stmt2.drvWins, Stmt2.drvWinsList, Lhs2.drvWins,
    List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | hw | hw
  · rfl
  · exact loop_drvWins "req" N W w hw
  · exact loop_drvWins "rm" N W w hw

private theorem p5_procWrites (N W : Nat) :
    ∀ n ∈ (arbP5 N W).procWrites, n = "ngid" := by
  intro n hn
  simp only [Process2.procWrites, List.mem_map] at hn
  obtain ⟨w, hw, rfl⟩ := hn
  exact p5_procWins N W w hw

theorem arb_driversOk (N : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (arbProcs N (Wfn N)) = true := by
  apply SvGolf.Cycle.driversOk_of_procDisj
  · simp [driverWins, Process2.drvWins, Lhs2.drvWins, arbProcs, arbP0, arbP1, arbP2, arbP3, arbP4,
      arbP5, arbP6, DrvWin.overlaps, design.pdesign, PDesign.declNames]
  · intro w hw
    have hw' : w ∈ ([("one", none), ("oh", none), ("gnt", none), ("mask", none), ("rm", none)] : List DrvWin) := by
      simpa [driverWins, Process2.drvWins, Lhs2.drvWins, arbProcs, arbP0, arbP1, arbP2, arbP3,
        arbP4, arbP5, arbP6, design.pdesign, PDesign.declNames] using hw
    refine ⟨?_, fun v hv => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [arbProcs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
        arbP0, arbP1, arbP2, arbP3, arbP4, Process2.procWins, List.not_mem_nil, false_or] at hv
      rcases hv with hv | hv
      · have hng := p5_procWins N (Wfn N) v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl | rfl <;> simp [DrvWin.overlaps, hng]
      · simp [arbP6, ffBody, Stmt2.drvWins, Stmt2.drvWinsList, Stmt2.drvWinsOpt, Lhs2.drvWins] at hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl | rfl | rfl <;>
          rcases hv with rfl | rfl | rfl <;> rfl
  · intro n hn
    simp only [arbProcs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      arbP0, arbP1, arbP2, arbP3, arbP4, Process2.procWrites, Process2.procWins, List.map_nil,
      List.not_mem_nil, false_or] at hn
    rcases hn with hn | hn
    · have hng := p5_procWrites N (Wfn N) n hn
      subst hng; decide
    · simp [arbP6, ffBody, Stmt2.drvWins, Stmt2.drvWinsList, Stmt2.drvWinsOpt, Lhs2.drvWins] at hn
      rcases hn with rfl | rfl <;> decide
  · simp only [arbProcs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.Pairwise.nil, and_true]
    refine ⟨by intro q _ a ha; simp [arbP0, Process2.procWins] at ha,
            by intro q _ a ha; simp [arbP1, Process2.procWins] at ha,
            by intro q _ a ha; simp [arbP2, Process2.procWins] at ha,
            by intro q _ a ha; simp [arbP3, Process2.procWins] at ha,
            by intro q _ a ha; simp [arbP4, Process2.procWins] at ha,
            ?_, by intro q hq; cases hq⟩
    rintro q rfl a ha b hb
    have hng := p5_procWins N (Wfn N) a ha
    simp [arbP6, ffBody, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsList, Stmt2.drvWinsOpt,
      Lhs2.drvWins] at hb
    rcases hb with rfl | rfl | rfl <;> simp [DrvWin.overlaps, hng]

private theorem touches_ngid_false {A R : List CombGuard.BWin}
    (hA : ∀ x ∈ A, x.1 = "ngid") (hR : ∀ y ∈ R, y.1 ≠ "ngid") :
    CombGuard.touches A R = false := by
  unfold CombGuard.touches
  rw [List.any_eq_false]
  intro r hr
  rw [Bool.not_eq_true, List.any_eq_false]
  intro f hf
  have h1 := hA f hf
  have h2 := hR r hr
  have hne : r.1 ≠ f.1 := by rw [h1]; exact h2
  simp [CombGuard.BWin.inter, hne]

private theorem arb_aliasFlows_no_ngid (N : Nat) :
    ∀ f ∈ aliasFlows (arbD N).combWd (arbD N).processes.toList, ∀ r ∈ f.1, r.1 ≠ "ngid" := by
  intro f hf
  simp only [arbD, List.toList_toArray, arbProcs, aliasFlows, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.append_nil, Process2.aflow, arbP0, arbP1, arbP2, arbP3,
    arbP4, arbP5, arbP6, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · intro r hr; simp [Expr2.rdW, Lhs2.rdW] at hr
  · intro r hr; simp [Expr2.rdW, Lhs2.rdW, CombGuard.whole] at hr; rcases hr with rfl | rfl <;> simp
  · intro r hr; simp [Expr2.rdW, Lhs2.rdW, CombGuard.whole] at hr; rcases hr with rfl | rfl <;> simp
  · intro r hr; simp [Expr2.rdW, Lhs2.rdW, CombGuard.whole] at hr; subst hr; simp
  · intro r hr; simp [Expr2.rdW, Lhs2.rdW, CombGuard.whole] at hr; rcases hr with rfl | rfl <;> simp

private theorem fanOut_ngid_nil (N : Nat) {A : List CombGuard.BWin} (hA : ∀ x ∈ A, x.1 = "ngid") :
    CombGuard.fanOut (aliasFlows (arbD N).combWd (arbD N).processes.toList) A = [] := by
  have hfl : (aliasFlows (arbD N).combWd (arbD N).processes.toList).length = 5 := by
    simp [arbD, arbProcs, aliasFlows, Process2.aflow, arbP0, arbP1, arbP2, arbP3, arbP4, arbP5, arbP6]
  unfold CombGuard.fanOut
  rw [hfl]
  simp only [CombGuard.fanAux, List.append_nil]
  have hhit : CombGuard.hitsOf A (aliasFlows (arbD N).combWd (arbD N).processes.toList) = [] := by
    unfold CombGuard.hitsOf
    rw [List.filter_eq_nil_iff]
    intro f hf
    rw [touches_ngid_false hA (arb_aliasFlows_no_ngid N f hf)]
    decide
  rw [hhit]
  rfl

private theorem loop_mayW_ngid (wd : String → Option Nat) (src : String) (N W : Nat) :
    ∀ x ∈ (loopStmt src N W).mayW wd, x.1 = "ngid" := by
  intro x hx
  simp only [loopStmt, Stmt2.mayW] at hx
  obtain ⟨s, hs, hxs⟩ := Loop2.mem_listMayW hx
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨k, _, rfl⟩ := hs
  simp only [scanStep, Stmt2.mayW, Stmt2.listMayW, Stmt2.optMayW, Lhs2.mayW,
    List.append_nil, List.mem_singleton] at hxs
  rw [hxs]; rfl

private theorem loop_aliasViol_none (N : Nat) (src : String) {A : List CombGuard.BWin}
    (hA : ∀ x ∈ A, x.1 = "ngid") :
    (loopStmt src N (Wfn N)).aliasViol (arbD N).combWd
      (aliasFlows (arbD N).combWd (arbD N).processes.toList) A = none := by
  let wd := (arbD N).combWd
  let fl := aliasFlows wd (arbD N).processes.toList
  have hchk : ∀ X R, (∀ x ∈ X, x.1 = "ngid") → CombGuard.aliasChk fl X R = none := by
    intro X R hX
    simp [CombGuard.aliasChk, fl, wd, fanOut_ngid_nil N hX, CombGuard.readsViol]
  have hstep : ∀ (l : List Nat),
      Stmt2.listAliasViol wd fl A (l.map (scanStep src N (Wfn N))) = none := by
    intro l
    induction l with
    | nil => rfl
    | cons k rest ih =>
      simp only [List.map_cons, Stmt2.listAliasViol, ih]
      have hrestW : ∀ x ∈ Stmt2.listMayW wd (rest.map (scanStep src N (Wfn N))) ++ A, x.1 = "ngid" := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨s, hs, hxs⟩ := Loop2.mem_listMayW hx
          simp only [List.mem_map] at hs
          obtain ⟨j, _, rfl⟩ := hs
          simp only [scanStep, Stmt2.mayW, Stmt2.listMayW, Stmt2.optMayW, Lhs2.mayW,
            List.append_nil, List.mem_singleton] at hxs
          rw [hxs]; rfl
        · exact hA x hx
      have h1 : (scanStep src N (Wfn N) k).aliasViol wd fl
          (Stmt2.listMayW wd (rest.map (scanStep src N (Wfn N))) ++ A) = none := by
        simp only [scanStep, Stmt2.aliasViol, Stmt2.listAliasViol, Stmt2.optAliasViol,
          Stmt2.listMayW, List.nil_append]
        have hng1 : ∀ x ∈ Lhs2.mayW wd (.ident "ngid") ++
            (Stmt2.listMayW wd (rest.map (scanStep src N (Wfn N))) ++ A), x.1 = "ngid" := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · simp only [Lhs2.mayW, List.mem_singleton] at hx; rw [hx]; rfl
          · exact hrestW x hx
        have hng2 : ∀ x ∈ Stmt2.mayW wd (.blockingAssign (.ident "ngid") (.lit (LVec.ofInt (Wfn N) (k : Int)))) ++
            Stmt2.optMayW wd none ++
            (Stmt2.listMayW wd (rest.map (scanStep src N (Wfn N))) ++ A), x.1 = "ngid" := by
          intro x hx
          simp only [Stmt2.mayW, Stmt2.optMayW, List.append_nil] at hx
          exact hng1 x hx
        rw [hchk _ _ hng2, hchk _ _ hng1]
        rfl
      rw [h1]; rfl
  simpa [loopStmt, Stmt2.aliasViol] using hstep (List.range N)

theorem arb_aliasGuard (N : Nat) : (arbD N).aliasGuard = arbD N := by
  apply Design2.aliasGuard_of_admits
  intro b hb
  simp only [arbD, List.toList_toArray, arbProcs, arbP0, arbP1, arbP2, arbP3, arbP4, arbP5, arbP6,
    List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h <;> try cases h
  let wd := (arbD N).combWd
  let fl := aliasFlows wd (arbD N).processes.toList
  have h2 := loop_aliasViol_none N "rm" (A := []) (by simp)
  have h1 := loop_aliasViol_none N "req" (A := (loopStmt "rm" N (Wfn N)).mayW wd ++ []) (by
    intro x hx; simp only [List.append_nil] at hx; exact loop_mayW_ngid wd "rm" N (Wfn N) x hx)
  have h0 : (Stmt2.blockingAssign (.ident "ngid") (.lit (z0 (Wfn N)))).aliasViol wd fl
      (Stmt2.listMayW wd [loopStmt "req" N (Wfn N), loopStmt "rm" N (Wfn N)] ++ []) = none := by
    simp [Stmt2.aliasViol, CombGuard.aliasChk, Expr2.rdW, Lhs2.rdW, CombGuard.readsViol]
  show ((Stmt2.blockingAssign (.ident "ngid") (.lit (z0 (Wfn N)))).aliasViol wd fl
          (Stmt2.listMayW wd [loopStmt "req" N (Wfn N), loopStmt "rm" N (Wfn N)] ++ []) <|>
        ((loopStmt "req" N (Wfn N)).aliasViol wd fl
          (Stmt2.listMayW wd [loopStmt "rm" N (Wfn N)] ++ []) <|>
         ((loopStmt "rm" N (Wfn N)).aliasViol wd fl (Stmt2.listMayW wd [] ++ []) <|> none))) = none
  simp only [Stmt2.listMayW, List.append_nil] at h0 ⊢
  rw [h0, show (loopStmt "req" N (Wfn N)).aliasViol wd fl ((loopStmt "rm" N (Wfn N)).mayW wd) = none from by
    simpa [List.append_nil] using h1, h2]
  rfl

theorem arb_sem_eq (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : design.sem N = arbD N :=
  SvGolf.Cycle.sem_eq_of_mirror (arb_instantiate2 N hN hR32) rfl (arb_driversOk N) (arb_aliasGuard N)

/-! ## 2. Closed-form single cycle (any values, `x` included) -/

/-- The eleven signals of `arbD`, in declaration order. -/
def SS (ck r q g v gid one oh mask rm ngid : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("req", q), ("gnt", g), ("valid", v), ("gid", gid),
   ("one", one), ("oh", oh), ("mask", mask), ("rm", rm), ("ngid", ngid)]

theorem apply_arb (N : Nat) (e : SvState) (ck r q g v gid one oh mask rm ngid : LVec) :
    applyInputs2 (arbD N) e (SS ck r q g v gid one oh mask rm ngid) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v gid one oh mask rm ngid := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "req" <;>
    simp [arbD, arbDecls, SS, appIn, h1, h2, h3, SvState.set]

theorem insertAt_zero_full (v p : LVec) (h : p.width = v.width) : v.insertAt 0 p = p := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.insertAt, Array.getElem?_ofFn]
  by_cases hi : i < v.width
  · have hp : i < p.bits.size := by simp only [LVec.width] at h hi; omega
    simp only [hi, ↓reduceDIte, Array.getElem?_eq_getElem hp]
    simp [h, hi, Array.getElem?_eq_getElem hp]
  · have hp : p.bits.size ≤ i := by simp only [LVec.width] at h hi; omega
    simp only [hi, ↓reduceDIte, Array.getElem?_eq_none hp]

@[simp] theorem width_resizeU' (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

def OneV (N : Nat) (one : LVec) : LVec := (one1.resizeU N).resizeU one.width
def OhV (one gid oh : LVec) : LVec := (one.shl gid).resizeU oh.width
def GntV (N : Nat) (v oh g : LVec) : LVec := (LVec.ternary v oh (z0 N)).resizeU g.width
def MaskV (N : Nat) (oh mask : LVec) : LVec := (oh.sub (one1.resizeU N)).resizeU mask.width
def RmV (q mask rm : LVec) : LVec := (q.and mask).resizeU rm.width

def scanCond (N : Nat) (src one : LVec) (k : Nat) : Bool :=
  (LVec.ofLogic (((src.shr (LVec.ofInt 32 (k : Int))).and one).neLogical (z0 N))).condTrue

def scanFold (N W : Nat) (src one : LVec) (ks : List Nat) (acc : LVec) : LVec :=
  ks.foldl (fun ng k =>
    if scanCond N src one k then (LVec.ofInt W (k : Int)).resizeU ng.width else ng) acc

def NgidV (N W : Nat) (q rm one ngid : LVec) : LVec :=
  scanFold N W rm one (List.range N)
    (scanFold N W q one (List.range N) ((z0 W).resizeU ngid.width))

@[simp] theorem OneV_width (N : Nat) (one : LVec) : (OneV N one).width = one.width := width_resizeU' _ _
@[simp] theorem OhV_width (one gid oh : LVec) : (OhV one gid oh).width = oh.width := width_resizeU' _ _
@[simp] theorem GntV_width (N : Nat) (v oh g : LVec) : (GntV N v oh g).width = g.width := width_resizeU' _ _
@[simp] theorem MaskV_width (N : Nat) (oh mask : LVec) : (MaskV N oh mask).width = mask.width := width_resizeU' _ _
@[simp] theorem RmV_width (q mask rm : LVec) : (RmV q mask rm).width = rm.width := width_resizeU' _ _

theorem scanFold_cons (N W : Nat) (src one : LVec) (k : Nat) (ks : List Nat) (acc : LVec) :
    scanFold N W src one (k :: ks) acc =
      scanFold N W src one ks
        (if scanCond N src one k then (LVec.ofInt W (k : Int)).resizeU acc.width else acc) := rfl

@[simp] theorem scanFold_width (N W : Nat) (src one : LVec) :
    ∀ (ks : List Nat) (acc : LVec), (scanFold N W src one ks acc).width = acc.width
  | [], _ => rfl
  | k :: ks, acc => by
    rw [scanFold_cons, scanFold_width N W src one ks]
    split <;> simp

@[simp] theorem NgidV_width (N W : Nat) (q rm one ngid : LVec) :
    (NgidV N W q rm one ngid).width = ngid.width := by
  unfold NgidV; simp

theorem p0_run (N F : Nat) (hF : 10 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) (arbP0 N) =
      .ok (SS ck r q g v gid (OneV N one) oh mask rm ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbP0, OneV, runCombProcess2, evalExpr2, resolveLhs2, SS, SvState.lookup, SvState.set,
    insertAt_zero_full]

theorem p1_run (F : Nat) (hF : 10 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) arbP1 =
      .ok (SS ck r q g v gid one (OhV one gid oh) mask rm ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbP1, OhV, runCombProcess2, evalExpr2, evalBinOp, resolveLhs2, readSignal, SS,
    SvState.lookup, SvState.set, insertAt_zero_full]

theorem p2_run (N F : Nat) (hF : 10 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) (arbP2 N) =
      .ok (SS ck r q (GntV N v oh g) v gid one oh mask rm ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbP2, GntV, runCombProcess2, evalExpr2, resolveLhs2, readSignal, SS, SvState.lookup,
    SvState.set, insertAt_zero_full]

theorem p3_run (N F : Nat) (hF : 10 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) (arbP3 N) =
      .ok (SS ck r q g v gid one oh (MaskV N oh mask) rm ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbP3, MaskV, runCombProcess2, evalExpr2, evalBinOp, resolveLhs2, readSignal, SS,
    SvState.lookup, SvState.set, insertAt_zero_full]

theorem p4_run (F : Nat) (hF : 10 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) arbP4 =
      .ok (SS ck r q g v gid one oh mask (RmV q mask rm) ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbP4, RmV, runCombProcess2, evalExpr2, evalBinOp, resolveLhs2, readSignal, SS,
    SvState.lookup, SvState.set, insertAt_zero_full]

private theorem scanStep_run (N W F k : Nat) (hF : 12 ≤ F) (src : String) (srcv : LVec)
    (ck r q g v gid one oh mask rm ngid : LVec)
    (hlook : SvState.lookup (SS ck r q g v gid one oh mask rm ngid) src = some srcv) :
    execStmt2 F (SS ck r q g v gid one oh mask rm ngid) [] (scanStep src N W k) =
      .ok (SS ck r q g v gid one oh mask rm
        (if scanCond N srcv one k then (LVec.ofInt W (k : Int)).resizeU ngid.width else ngid), []) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 12 := ⟨F - 12, by omega⟩
  have hcond : evalExpr2 (f + 9) (SS ck r q g v gid one oh mask rm ngid)
      (.binary .ne
        (.binary .and
          (.binary (.shr false) (.ident src) (.lit (LVec.ofInt 32 (k : Int))))
          (.ident "one"))
        (.lit (z0 N))) =
      .ok (LVec.ofLogic (((srcv.shr (LVec.ofInt 32 (k : Int))).and one).neLogical (z0 N))) := by
    simp only [evalExpr2, readSignal, hlook, Res.ok_bind, Res.pure_eq, evalBinOp]
    simp [SS, SvState.lookup]
  unfold scanCond
  simp only [scanStep, execStmt2, execStmts2, hcond, Res.ok_bind]
  by_cases hc : (LVec.ofLogic (((srcv.shr (LVec.ofInt 32 (k : Int))).and one).neLogical (z0 N))).condTrue = true
  · simp only [hc, ↓reduceIte]
    simp [evalExpr2, resolveLhs2, SS, SvState.lookup, SvState.set, insertAt_zero_full]
  · simp only [hc]
    rfl

private theorem scanFold_run_req (N W : Nat) : ∀ (ks : List Nat) (F : Nat), ks.length + 13 ≤ F →
    ∀ (ck r q g v gid one oh mask rm ngid : LVec),
      execStmts2 F (SS ck r q g v gid one oh mask rm ngid) [] (ks.map (scanStep "req" N W)) =
        .ok (SS ck r q g v gid one oh mask rm (scanFold N W q one ks ngid), [])
  | [], F, hF, ck, r, q, g, v, gid, one, oh, mask, rm, ngid => by
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    simp [execStmts2, scanFold]
  | k :: ks, F, hF, ck, r, q, g, v, gid, one, oh, mask, rm, ngid => by
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    simp only [List.length_cons] at hF
    rw [List.map_cons, scanFold_cons]
    simp only [execStmts2]
    rw [scanStep_run N W f k (by omega) "req" q ck r q g v gid one oh mask rm ngid (by simp [SS, SvState.lookup])]
    simp only [Res.ok_bind]
    exact scanFold_run_req N W ks f (by omega) ck r q g v gid one oh mask rm _

private theorem scanFold_run_rm (N W : Nat) : ∀ (ks : List Nat) (F : Nat), ks.length + 13 ≤ F →
    ∀ (ck r q g v gid one oh mask rm ngid : LVec),
      execStmts2 F (SS ck r q g v gid one oh mask rm ngid) [] (ks.map (scanStep "rm" N W)) =
        .ok (SS ck r q g v gid one oh mask rm (scanFold N W rm one ks ngid), [])
  | [], F, hF, ck, r, q, g, v, gid, one, oh, mask, rm, ngid => by
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    simp [execStmts2, scanFold]
  | k :: ks, F, hF, ck, r, q, g, v, gid, one, oh, mask, rm, ngid => by
    obtain ⟨f, rfl⟩ : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    simp only [List.length_cons] at hF
    rw [List.map_cons, scanFold_cons]
    simp only [execStmts2]
    rw [scanStep_run N W f k (by omega) "rm" rm ck r q g v gid one oh mask rm ngid (by simp [SS, SvState.lookup])]
    simp only [Res.ok_bind]
    exact scanFold_run_rm N W ks f (by omega) ck r q g v gid one oh mask rm _

theorem p5_run (N W F : Nat) (hF : N + 20 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runCombProcess2 F (SS ck r q g v gid one oh mask rm ngid) (arbP5 N W) =
      .ok (SS ck r q g v gid one oh mask rm (NgidV N W q rm one ngid)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 6 := ⟨F - 6, by omega⟩
  have h0 : execStmt2 (f + 4) (SS ck r q g v gid one oh mask rm ngid) []
      (.blockingAssign (.ident "ngid") (.lit (z0 W))) =
      .ok (SS ck r q g v gid one oh mask rm ((z0 W).resizeU ngid.width), []) := by
    simp [execStmt2, evalExpr2, resolveLhs2, SS, SvState.lookup, SvState.set, insertAt_zero_full]
  have h1 : execStmt2 (f + 3) (SS ck r q g v gid one oh mask rm ((z0 W).resizeU ngid.width)) []
      (loopStmt "req" N W) =
      .ok (SS ck r q g v gid one oh mask rm
        (scanFold N W q one (List.range N) ((z0 W).resizeU ngid.width)), []) := by
    simp only [loopStmt, execStmt2]
    exact scanFold_run_req N W (List.range N) (f + 2) (by simp; omega) ck r q g v gid one oh mask rm _
  have h2 : execStmt2 (f + 2) (SS ck r q g v gid one oh mask rm
      (scanFold N W q one (List.range N) ((z0 W).resizeU ngid.width))) []
      (loopStmt "rm" N W) =
      .ok (SS ck r q g v gid one oh mask rm (NgidV N W q rm one ngid), []) := by
    simp only [loopStmt, execStmt2, NgidV]
    exact scanFold_run_rm N W (List.range N) (f + 1) (by simp; omega) ck r q g v gid one oh mask rm _
  have h3 : execStmts2 (f + 1) (SS ck r q g v gid one oh mask rm (NgidV N W q rm one ngid)) [] [] =
      .ok (SS ck r q g v gid one oh mask rm (NgidV N W q rm one ngid), []) := rfl
  simp only [arbP5, combBody, runCombProcess2]
  rw [show execStmt2 (f + 6) (SS ck r q g v gid one oh mask rm ngid) []
        (.block #[.blockingAssign (.ident "ngid") (.lit (z0 W)), loopStmt "req" N W, loopStmt "rm" N W]) =
        execStmts2 (f + 5) (SS ck r q g v gid one oh mask rm ngid) []
          [.blockingAssign (.ident "ngid") (.lit (z0 W)), loopStmt "req" N W, loopStmt "rm" N W] from rfl]
  rw [show execStmts2 (f + 5) (SS ck r q g v gid one oh mask rm ngid) []
        [.blockingAssign (.ident "ngid") (.lit (z0 W)), loopStmt "req" N W, loopStmt "rm" N W] =
        (do let p ← execStmt2 (f + 4) (SS ck r q g v gid one oh mask rm ngid) []
              (.blockingAssign (.ident "ngid") (.lit (z0 W)))
            execStmts2 (f + 4) p.1 p.2 [loopStmt "req" N W, loopStmt "rm" N W]) from rfl]
  rw [h0, Res.ok_bind]
  rw [show execStmts2 (f + 4) (SS ck r q g v gid one oh mask rm ((z0 W).resizeU ngid.width)) []
        [loopStmt "req" N W, loopStmt "rm" N W] =
        (do let p ← execStmt2 (f + 3) (SS ck r q g v gid one oh mask rm ((z0 W).resizeU ngid.width)) []
              (loopStmt "req" N W)
            execStmts2 (f + 3) p.1 p.2 [loopStmt "rm" N W]) from rfl]
  rw [h1, Res.ok_bind]
  rw [show execStmts2 (f + 3) (SS ck r q g v gid one oh mask rm
        (scanFold N W q one (List.range N) ((z0 W).resizeU ngid.width))) [] [loopStmt "rm" N W] =
        (do let p ← execStmt2 (f + 2) (SS ck r q g v gid one oh mask rm
              (scanFold N W q one (List.range N) ((z0 W).resizeU ngid.width))) [] (loopStmt "rm" N W)
            execStmts2 (f + 2) p.1 p.2 []) from rfl]
  rw [h2, Res.ok_bind]
  rfl

/-! ### Comb settle over every schedule permutation of `[0, 1, 2, 3, 4, 5]` -/

def oneS (N : Nat) (one : LVec) : LVec := OneV N one
def ohS (N : Nat) (gid one oh : LVec) : LVec := OhV (oneS N one) gid oh
def gntS (N : Nat) (v gid g one oh : LVec) : LVec := GntV N v (ohS N gid one oh) g
def maskS (N : Nat) (gid one oh mask : LVec) : LVec := MaskV N (ohS N gid one oh) mask
def rmS (N : Nat) (q gid one oh mask rm : LVec) : LVec := RmV q (maskS N gid one oh mask) rm
def ngidS (N : Nat) (q gid one oh mask rm ngid : LVec) : LVec :=
  NgidV N (Wfn N) q (rmS N q gid one oh mask rm) (oneS N one) ngid

def combS (N : Nat) (ck r q g v gid one oh mask rm ngid : LVec) : SvState :=
  SS ck r q (gntS N v gid g one oh) v gid (oneS N one) (ohS N gid one oh)
    (maskS N gid one oh mask) (rmS N q gid one oh mask rm)
    (ngidS N q gid one oh mask rm ngid)

private theorem combPass_dag (N f : Nat) (hf : N + 20 ≤ f) (ck r q v gid : LVec)
    (wg wone woh wmask wrm wngid : Nat)
    (oneT ohT gntT maskT rmT ngidT : LVec)
    (honeT : oneT = (one1.resizeU N).resizeU wone)
    (hohT : ohT = (oneT.shl gid).resizeU woh)
    (hgntT : gntT = (LVec.ternary v ohT (z0 N)).resizeU wg)
    (hmaskT : maskT = (ohT.sub (one1.resizeU N)).resizeU wmask)
    (hrmT : rmT = (q.and maskT).resizeU wrm)
    (hngidT : ngidT = scanFold N (Wfn N) rmT oneT (List.range N)
      (scanFold N (Wfn N) q oneT (List.range N) ((z0 (Wfn N)).resizeU wngid))) :
    ∀ (l : List Nat), (∀ i ∈ l, i < 6) →
    ∀ (g one oh mask rm ngid : LVec),
      g.width = wg → one.width = wone → oh.width = woh →
      mask.width = wmask → rm.width = wrm → ngid.width = wngid →
      ∃ g' one' oh' mask' rm' ngid',
        combPass2 (arbD N) f (SS ck r q g v gid one oh mask rm ngid) l =
          .ok (SS ck r q g' v gid one' oh' mask' rm' ngid') ∧
        g'.width = wg ∧ one'.width = wone ∧ oh'.width = woh ∧
        mask'.width = wmask ∧ rm'.width = wrm ∧ ngid'.width = wngid ∧
        ((one = oneT ∨ 0 ∈ l) → one' = oneT) ∧
        (one = oneT → (oh = ohT ∨ 1 ∈ l) → oh' = ohT) ∧
        (one = oneT → oh = ohT → (g = gntT ∨ 2 ∈ l) → g' = gntT) ∧
        (one = oneT → oh = ohT → (mask = maskT ∨ 3 ∈ l) → mask' = maskT) ∧
        (one = oneT → oh = ohT → mask = maskT → (rm = rmT ∨ 4 ∈ l) → rm' = rmT) ∧
        (one = oneT → oh = ohT → mask = maskT → rm = rmT → (ngid = ngidT ∨ 5 ∈ l) → ngid' = ngidT)
  | [], _, g, one, oh, mask, rm, ngid, hg, hone, hoh, hmask, hrm, hngid =>
    ⟨g, one, oh, mask, rm, ngid, rfl, hg, hone, hoh, hmask, hrm, hngid,
      fun h => by simpa using h,
      fun _ h => by simpa using h,
      fun _ _ h => by simpa using h,
      fun _ _ h => by simpa using h,
      fun _ _ _ h => by simpa using h,
      fun _ _ _ _ h => by simpa using h⟩
  | i :: l, hl, g, one, oh, mask, rm, ngid, hg, hone, hoh, hmask, hrm, hngid => by
    have hi : i < 6 := hl i List.mem_cons_self
    have hl' : ∀ j ∈ l, j < 6 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · have hp : (arbD N).processes[0]? = some (arbP0 N) := rfl
      have h1 : OneV N one = oneT := by simp [OneV, hone, honeT]
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' g oneT oh mask rm ngid hg (by rw [← h1, OneV_width, hone]) hoh hmask hrm hngid
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun _ => s1 (.inl rfl),
        fun _ h => s2 rfl (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun _ h2 h => s3 rfl h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun _ h2 h => s4 rfl h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun _ h2 h3 h => s5 rfl h2 h3 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun _ h2 h3 h4 h => s6 rfl h2 h3 h4 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h)⟩
      simp only [combPass2, hp, p0_run N f (by omega), h1, Res.ok_bind, hrun]
    · have hp : (arbD N).processes[1]? = some arbP1 := rfl
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' g one (OhV one gid oh) mask rm ngid hg hone (by rw [OhV_width, hoh]) hmask hrm hngid
      have hoh_eq : one = oneT → OhV one gid oh = ohT := fun h => by
        subst h; simp [OhV, hoh, hohT]
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun h => s1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 _ => s2 h1 (.inl (hoh_eq h1)),
        fun h1 _ h => s3 h1 (hoh_eq h1) (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 _ h => s4 h1 (hoh_eq h1) (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 _ h3 h => s5 h1 (hoh_eq h1) h3 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 _ h3 h4 h => s6 h1 (hoh_eq h1) h3 h4 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h)⟩
      simp only [combPass2, hp, p1_run f (by omega), Res.ok_bind, hrun]
    · have hp : (arbD N).processes[2]? = some (arbP2 N) := rfl
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' (GntV N v oh g) one oh mask rm ngid (by rw [GntV_width, hg]) hone hoh hmask hrm hngid
      have hg_eq : oh = ohT → GntV N v oh g = gntT := fun h => by
        subst h; simp [GntV, hg, hgntT]
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun h => s1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h => s2 h1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 _ => s3 h1 h2 (.inl (hg_eq h2)),
        fun h1 h2 h => s4 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h3 h => s5 h1 h2 h3 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h3 h4 h => s6 h1 h2 h3 h4 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h)⟩
      simp only [combPass2, hp, p2_run N f (by omega), Res.ok_bind, hrun]
    · have hp : (arbD N).processes[3]? = some (arbP3 N) := rfl
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' g one oh (MaskV N oh mask) rm ngid hg hone hoh (by rw [MaskV_width, hmask]) hrm hngid
      have hmask_eq : oh = ohT → MaskV N oh mask = maskT := fun h => by
        subst h; simp [MaskV, hmask, hmaskT]
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun h => s1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h => s2 h1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h => s3 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 _ => s4 h1 h2 (.inl (hmask_eq h2)),
        fun h1 h2 _ h => s5 h1 h2 (hmask_eq h2) (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 _ h4 h => s6 h1 h2 (hmask_eq h2) h4 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h)⟩
      simp only [combPass2, hp, p3_run N f (by omega), Res.ok_bind, hrun]
    · have hp : (arbD N).processes[4]? = some arbP4 := rfl
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' g one oh mask (RmV q mask rm) ngid hg hone hoh hmask (by rw [RmV_width, hrm]) hngid
      have hrm_eq : mask = maskT → RmV q mask rm = rmT := fun h => by
        subst h; simp [RmV, hrm, hrmT]
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun h => s1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h => s2 h1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h => s3 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h => s4 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h3 _ => s5 h1 h2 h3 (.inl (hrm_eq h3)),
        fun h1 h2 h3 _ h => s6 h1 h2 h3 (hrm_eq h3) (by rcases h with h | h; exact .inl h; simp at h; exact .inr h)⟩
      simp only [combPass2, hp, p4_run f (by omega), Res.ok_bind, hrun]
    · have hp : (arbD N).processes[5]? = some (arbP5 N (Wfn N)) := rfl
      obtain ⟨g', one', oh', mask', rm', ngid', hrun, hw1, hw2, hw3, hw4, hw5, hw6,
              s1, s2, s3, s4, s5, s6⟩ :=
        combPass_dag N f hf ck r q v gid wg wone woh wmask wrm wngid
          oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
          l hl' g one oh mask rm (NgidV N (Wfn N) q rm one ngid)
          hg hone hoh hmask hrm (by rw [NgidV_width, hngid])
      have hng_eq : one = oneT → rm = rmT → NgidV N (Wfn N) q rm one ngid = ngidT := fun h1 h2 => by
        subst h1; subst h2; simp [NgidV, hngid, hngidT]
      refine ⟨g', one', oh', mask', rm', ngid', ?_, hw1, hw2, hw3, hw4, hw5, hw6,
        fun h => s1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h => s2 h1 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h => s3 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h => s4 h1 h2 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h3 h => s5 h1 h2 h3 (by rcases h with h | h; exact .inl h; simp at h; exact .inr h),
        fun h1 h2 h3 h4 _ => s6 h1 h2 h3 h4 (.inl (hng_eq h1 h4))⟩
      simp only [combPass2, hp, p5_run N (Wfn N) f hf, Res.ok_bind, hrun]

private theorem SS_inj {ck r q g v gid one oh mask rm ngid ck' r' q' g' v' gid' one' oh' mask' rm' ngid' : LVec}
    (h : SS ck r q g v gid one oh mask rm ngid = SS ck' r' q' g' v' gid' one' oh' mask' rm' ngid') :
    g = g' ∧ v = v' ∧ gid = gid' ∧ one = one' ∧ oh = oh' ∧ mask = mask' ∧ rm = rm' ∧ ngid = ngid' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
         h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2⟩

/-- **The comb settle**: from any state, `combSettle2` reaches `combS` in at most 6 passes under any schedule. -/
theorem settle_arb (N : Nat) (σ : ScheduleOracle) (F k : Nat) (hF : N + 30 ≤ F)
    (ck r q g v gid one oh mask rm ngid : LVec) :
    ∃ k', combSettle2 (arbD N) σ F (SS ck r q g v gid one oh mask rm ngid) k =
      .ok (combS N ck r q g v gid one oh mask rm ngid, k') := by
  have hci : (arbD N).combIndices = [0, 1, 2, 3, 4, 5] := rfl
  let oneT := oneS N one
  let ohT := ohS N gid one oh
  let gntT := gntS N v gid g one oh
  let maskT := maskS N gid one oh mask
  let rmT := rmS N q gid one oh mask rm
  let ngidT := ngidS N q gid one oh mask rm ngid
  have honeT : oneT = (one1.resizeU N).resizeU one.width := rfl
  have hohT : ohT = (oneT.shl gid).resizeU oh.width := rfl
  have hgntT : gntT = (LVec.ternary v ohT (z0 N)).resizeU g.width := rfl
  have hmaskT : maskT = (ohT.sub (one1.resizeU N)).resizeU mask.width := rfl
  have hrmT : rmT = (q.and maskT).resizeU rm.width := rfl
  have hngidT : ngidT = scanFold N (Wfn N) rmT oneT (List.range N)
      (scanFold N (Wfn N) q oneT (List.range N) ((z0 (Wfn N)).resizeU ngid.width)) := rfl
  let Stage : Nat → LVec → LVec → LVec → LVec → LVec → LVec → Prop
    | 0, _, _, _, _, _, _ => True
    | 1, _, o, _, _, _, _ => o = oneT
    | 2, _, o, h, _, _, _ => o = oneT ∧ h = ohT
    | 3, gn, o, h, m, _, _ => o = oneT ∧ h = ohT ∧ gn = gntT ∧ m = maskT
    | 4, gn, o, h, m, r', _ => o = oneT ∧ h = ohT ∧ gn = gntT ∧ m = maskT ∧ r' = rmT
    | _ + 5, gn, o, h, m, r', ng =>
        o = oneT ∧ h = ohT ∧ gn = gntT ∧ m = maskT ∧ r' = rmT ∧ ng = ngidT
  have hpass : ∀ (f' j : Nat), N + 20 ≤ f' →
      ∀ (g1 one1' oh1 mask1 rm1 ngid1 : LVec),
        g1.width = g.width → one1'.width = one.width → oh1.width = oh.width →
        mask1.width = mask.width → rm1.width = rm.width → ngid1.width = ngid.width →
        ∃ g2 one2 oh2 mask2 rm2 ngid2,
          combPass2 (arbD N) f' (SS ck r q g1 v gid one1' oh1 mask1 rm1 ngid1)
            (σ.choose j (arbD N).combIndices) =
            .ok (SS ck r q g2 v gid one2 oh2 mask2 rm2 ngid2) ∧
          g2.width = g.width ∧ one2.width = one.width ∧ oh2.width = oh.width ∧
          mask2.width = mask.width ∧ rm2.width = rm.width ∧ ngid2.width = ngid.width ∧
          one2 = oneT ∧
          (one1' = oneT → oh2 = ohT) ∧
          (one1' = oneT → oh1 = ohT → g2 = gntT ∧ mask2 = maskT) ∧
          (one1' = oneT → oh1 = ohT → mask1 = maskT → rm2 = rmT) ∧
          (one1' = oneT → oh1 = ohT → mask1 = maskT → rm1 = rmT → ngid2 = ngidT) := by
    intro f' j hf' g1 one1' oh1 mask1 rm1 ngid1 hw1 hw2 hw3 hw4 hw5 hw6
    have hperm : (σ.choose j (arbD N).combIndices).Perm [0, 1, 2, 3, 4, 5] := by
      rw [hci]; exact σ.choose_perm j [0, 1, 2, 3, 4, 5]
    have hmem : ∀ a, a < 6 → a ∈ σ.choose j (arbD N).combIndices := fun a ha =>
      hperm.mem_iff.mpr (by have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 := by omega
                            rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    have hlt : ∀ a ∈ σ.choose j (arbD N).combIndices, a < 6 := fun a ha => by
      have := hperm.mem_iff.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    obtain ⟨g2, one2, oh2, mask2, rm2, ngid2, hr, w1, w2, w3, w4, w5, w6, s1, s2, s3, s4, s5, s6⟩ :=
      combPass_dag N f' hf' ck r q v gid g.width one.width oh.width mask.width rm.width ngid.width
        oneT ohT gntT maskT rmT ngidT honeT hohT hgntT hmaskT hrmT hngidT
        (σ.choose j (arbD N).combIndices) hlt g1 one1' oh1 mask1 rm1 ngid1 hw1 hw2 hw3 hw4 hw5 hw6
    exact ⟨g2, one2, oh2, mask2, rm2, ngid2, hr, w1, w2, w3, w4, w5, w6,
      s1 (.inr (hmem 0 (by omega))),
      fun h => s2 h (.inr (hmem 1 (by omega))),
      fun h1 h2 => ⟨s3 h1 h2 (.inr (hmem 2 (by omega))), s4 h1 h2 (.inr (hmem 3 (by omega)))⟩,
      fun h1 h2 h3 => s5 h1 h2 h3 (.inr (hmem 4 (by omega))),
      fun h1 h2 h3 h4 => s6 h1 h2 h3 h4 (.inr (hmem 5 (by omega)))⟩
  have hgo : ∀ (rem : Nat) (F' j : Nat), N + 20 + rem + 1 ≤ F' →
      ∀ (g1 one1' oh1 mask1 rm1 ngid1 : LVec),
        g1.width = g.width → one1'.width = one.width → oh1.width = oh.width →
        mask1.width = mask.width → rm1.width = rm.width → ngid1.width = ngid.width →
        Stage (5 - rem) g1 one1' oh1 mask1 rm1 ngid1 →
        ∃ k', combSettle2 (arbD N) σ F' (SS ck r q g1 v gid one1' oh1 mask1 rm1 ngid1) j =
          .ok (SS ck r q gntT v gid oneT ohT maskT rmT ngidT, k') := by
    intro rem
    induction rem with
    | zero =>
      intro F' j hF' g1 one1' oh1 mask1 rm1 ngid1 hw1 hw2 hw3 hw4 hw5 hw6 hst
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
      obtain ⟨f', rfl⟩ : ∃ f', F' = f' + 1 := ⟨F' - 1, by omega⟩
      obtain ⟨g2, one2, oh2, mask2, rm2, ngid2, hr, -, -, -, -, -, -, p1, p2, p3, p4, p5⟩ :=
        hpass f' j (by omega) gntT oneT ohT maskT rmT ngidT hw1 hw2 hw3 hw4 hw5 hw6
      have e1 : one2 = oneT := p1
      have e2 : oh2 = ohT := p2 rfl
      have e3 : g2 = gntT := (p3 rfl rfl).1
      have e4 : mask2 = maskT := (p3 rfl rfl).2
      have e5 : rm2 = rmT := p4 rfl rfl rfl
      have e6 : ngid2 = ngidT := p5 rfl rfl rfl rfl
      subst e1; subst e2; subst e3; subst e4; subst e5; subst e6
      rw [combSettle2.eq_2, hr]
      simp only [Res.ok_bind, beq_self_eq_true, ↓reduceIte]
      exact ⟨j + 1, rfl⟩
    | succ rem ih =>
      intro F' j hF' g1 one1' oh1 mask1 rm1 ngid1 hw1 hw2 hw3 hw4 hw5 hw6 hst
      obtain ⟨f', rfl⟩ : ∃ f', F' = f' + 1 := ⟨F' - 1, by omega⟩
      obtain ⟨g2, one2, oh2, mask2, rm2, ngid2, hr, w1, w2, w3, w4, w5, w6, p1, p2, p3, p4, p5⟩ :=
        hpass f' j (by omega) g1 one1' oh1 mask1 rm1 ngid1 hw1 hw2 hw3 hw4 hw5 hw6
      rw [combSettle2.eq_2, hr]
      simp only [Res.ok_bind]
      by_cases hb : (SS ck r q g2 v gid one2 oh2 mask2 rm2 ngid2 ==
          SS ck r q g1 v gid one1' oh1 mask1 rm1 ngid1) = true
      · simp only [hb, ↓reduceIte]
        have heq := SS_inj (eq_of_beq hb)
        have e1 : one1' = oneT := heq.2.2.2.1.symm.trans p1
        have e2 : oh1 = ohT := heq.2.2.2.2.1.symm.trans (p2 e1)
        have e3 : g1 = gntT := heq.1.symm.trans (p3 e1 e2).1
        have e4 : mask1 = maskT := heq.2.2.2.2.2.1.symm.trans (p3 e1 e2).2
        have e5 : rm1 = rmT := heq.2.2.2.2.2.2.1.symm.trans (p4 e1 e2 e4)
        have e6 : ngid1 = ngidT := heq.2.2.2.2.2.2.2.symm.trans (p5 e1 e2 e4 e5)
        refine ⟨j + 1, ?_⟩
        rw [eq_of_beq hb, e1, e2, e3, e4, e5, e6]
      · simp only [hb]
        refine ih f' (j + 1) (by omega) g2 one2 oh2 mask2 rm2 ngid2 w1 w2 w3 w4 w5 w6 ?_
        rcases rem with _ | rem
        · obtain ⟨h1, h2, h3, h4, h5⟩ := hst
          exact ⟨p1, p2 h1, (p3 h1 h2).1, (p3 h1 h2).2, p4 h1 h2 h4, p5 h1 h2 h4 h5⟩
        · rcases rem with _ | rem
          · obtain ⟨h1, h2, h3, h4⟩ := hst
            exact ⟨p1, p2 h1, (p3 h1 h2).1, (p3 h1 h2).2, p4 h1 h2 h4⟩
          · rcases rem with _ | rem
            · obtain ⟨h1, h2⟩ := hst
              exact ⟨p1, p2 h1, (p3 h1 h2).1, (p3 h1 h2).2⟩
            · rcases rem with _ | rem
              · exact ⟨p1, p2 hst⟩
              · rcases rem with _ | rem'
                · exact p1
                · simp [Stage]
  exact hgo 5 F k (by omega) g one oh mask rm ngid rfl rfl rfl rfl rfl rfl trivial

/-! ### Edge process, NBA commit, and full cycle -/

def ffQ (N : Nat) (r q v gid ngid : LVec) : NbaQueue2 :=
  if r.condTrue then
    [("valid", 0, zero1.resizeU v.width), ("gid", 0, ngid.resizeU gid.width)]
  else
    [("valid", 0, (LVec.ofLogic (q.neLogical (z0 N))).resizeU v.width),
     ("gid", 0, ngid.resizeU gid.width)]

theorem p6_run (N F : Nat) (hF : 20 ≤ F) (ck r q g v gid one oh mask rm ngid : LVec) :
    runEdgeProcess2 F (SS ck r q g v gid one oh mask rm ngid) [] (arbP6 N) =
      .ok (SS ck r q g v gid one oh mask rm ngid, ffQ N r q v gid ngid) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 20 := ⟨F - 20, by omega⟩
  unfold ffQ
  by_cases h1 : r.condTrue = true <;>
    simp [arbP6, ffBody, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalBinOp, resolveLhs2,
      readSignal, SS, SvState.lookup, h1]

def Vv (N : Nat) (r q v : LVec) : LVec :=
  if r.condTrue then zero1.resizeU v.width
  else (LVec.ofLogic (q.neLogical (z0 N))).resizeU v.width

def Gidv (gid ngid : LVec) : LVec := ngid.resizeU gid.width

@[simp] theorem Vv_width (N : Nat) (r q v : LVec) : (Vv N r q v).width = v.width := by
  unfold Vv; split <;> exact width_resizeU' _ _

@[simp] theorem Gidv_width (gid ngid : LVec) : (Gidv gid ngid).width = gid.width :=
  width_resizeU' _ _

theorem commit_ff (N : Nat) (ck r q g v gid one oh mask rm ngid : LVec) :
    commitNba2 (SS ck r q g v gid one oh mask rm ngid) (ffQ N r q v gid ngid) =
      SS ck r q g (Vv N r q v) (Gidv gid ngid) one oh mask rm ngid := by
  unfold ffQ Vv Gidv
  by_cases h1 : r.condTrue = true <;>
    simp [h1, commitNba2, SS, SvState.lookup, SvState.set, insertAt_zero_full]

/-- **One cycle of `arbD`**, in closed form. -/
def arbNext (N : Nat) (e : SvState) (ck r q g v gid one oh mask rm ngid : LVec) : SvState :=
  let ck' := appIn e "clk" ck
  let r' := appIn e "rst" r
  let q' := appIn e "req" q
  combS N ck' r' q' (gntS N v gid g one oh) (Vv N r' q' v)
    (Gidv gid (ngidS N q' gid one oh mask rm ngid))
    (oneS N one) (ohS N gid one oh) (maskS N gid one oh mask)
    (rmS N q' gid one oh mask rm) (ngidS N q' gid one oh mask rm ngid)

theorem arb_cycle (N : Nat) (σ : ScheduleOracle) (e : SvState)
    (ck r q g v gid one oh mask rm ngid : LVec) (kk F : Nat) (hF : N + 40 ≤ F) :
    ∃ k', cycleStep2 (arbD N) σ F e (SS ck r q g v gid one oh mask rm ngid) kk =
      .ok (arbNext N e ck r q g v gid one oh mask rm ngid, k') := by
  have hF' : N + 30 ≤ F := by omega
  obtain ⟨k1, h1⟩ := settle_arb N σ F kk hF' (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
    g v gid one oh mask rm ngid
  obtain ⟨k2, h2⟩ := settle_arb N σ F (k1 + 1) hF' (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
    (gntS N v gid g one oh) (Vv N (appIn e "rst" r) (appIn e "req" q) v)
    (Gidv gid (ngidS N (appIn e "req" q) gid one oh mask rm ngid))
    (oneS N one) (ohS N gid one oh) (maskS N gid one oh mask)
    (rmS N (appIn e "req" q) gid one oh mask rm) (ngidS N (appIn e "req" q) gid one oh mask rm ngid)
  have hE : edgePass2 (arbD N) F
      (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v gid one oh mask rm ngid) []
      (σ.choose k1 (arbD N).edgeIndices) =
      .ok (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v gid one oh mask rm ngid,
        ffQ N (appIn e "rst" r) (appIn e "req" q) v gid (ngidS N (appIn e "req" q) gid one oh mask rm ngid)) := by
    have hchoose : σ.choose k1 (arbD N).edgeIndices = [6] :=
      List.perm_singleton.mp (σ.choose_perm k1 [6])
    rw [hchoose]
    simp only [edgePass2, combS, show (arbD N).processes[6]? = some (arbP6 N) from rfl,
      p6_run N F (by omega), Res.ok_bind]
  have hC : commitNba2 (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v gid one oh mask rm ngid)
      (ffQ N (appIn e "rst" r) (appIn e "req" q) v gid (ngidS N (appIn e "req" q) gid one oh mask rm ngid)) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) (gntS N v gid g one oh)
        (Vv N (appIn e "rst" r) (appIn e "req" q) v)
        (Gidv gid (ngidS N (appIn e "req" q) gid one oh mask rm ngid))
        (oneS N one) (ohS N gid one oh) (maskS N gid one oh mask)
        (rmS N (appIn e "req" q) gid one oh mask rm) (ngidS N (appIn e "req" q) gid one oh mask rm ngid) :=
    commit_ff N _ _ _ _ v gid _ _ _ _ _
  have hre : ∀ a b, (arbD N).resetIndices a b = [] := fun _ _ => rfl
  refine ⟨k2, ?_⟩
  simp only [cycleStep2, apply_arb, h1, Res.ok_bind, Res.pure_eq, hre, hE, hC, h2]
  rfl

/-! ## 3. Shape invariant -/

def Shp (N : Nat) (st : SvState) : Prop :=
  ∃ ck r q g v gid one oh mask rm ngid,
    st = SS ck r q g v gid one oh mask rm ngid ∧
    g.width = N ∧ v.width = 1 ∧ gid.width = Wfn N ∧
    one.width = N ∧ oh.width = N ∧ mask.width = N ∧ rm.width = N ∧ ngid.width = Wfn N

theorem width_xVec (w : Nat) : (LVec.xVec w).width = w := by
  simp [LVec.xVec, LVec.replicate, LVec.width]

theorem arb_init (N : Nat) : Shp N (initState2 (arbD N)) :=
  ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec N, LVec.xVec N, LVec.xVec 1, LVec.xVec (Wfn N),
   LVec.xVec N, LVec.xVec N, LVec.xVec N, LVec.xVec N, LVec.xVec (Wfn N), rfl,
   width_xVec N, width_xVec 1, width_xVec (Wfn N), width_xVec N, width_xVec N,
   width_xVec N, width_xVec N, width_xVec (Wfn N)⟩

theorem arbNext_shp {N : Nat} {e : SvState} {ck r q g v gid one oh mask rm ngid : LVec}
    (hg : g.width = N) (hv : v.width = 1) (hgid : gid.width = Wfn N)
    (hone : one.width = N) (hoh : oh.width = N) (hmask : mask.width = N)
    (hrm : rm.width = N) (hngid : ngid.width = Wfn N) :
    Shp N (arbNext N e ck r q g v gid one oh mask rm ngid) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, rfl,
   by simp [gntS, hg], by simp [hv], by simp [hgid], by simp [oneS, hone],
   by simp [ohS, hoh], by simp [maskS, hmask], by simp [rmS, hrm], by simp [ngidS, hngid]⟩

def Stp (N : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r q g v gid one oh mask rm ngid,
    prev = SS ck r q g v gid one oh mask rm ngid ∧
    (g.width = N ∧ v.width = 1 ∧ gid.width = Wfn N ∧
     one.width = N ∧ oh.width = N ∧ mask.width = N ∧ rm.width = N ∧ ngid.width = Wfn N) ∧
    st = arbNext N e ck r q g v gid one oh mask rm ngid

/-! ## 4. Descending round-robin mathematics (`lowMask`, `scanHigh`, `pickIdx`, `rankDesc`) -/

/-- `lowMask N g = (1 << g) - 1`: bits `0 .. g-1` are 1, bits `g .. N-1` are 0 (for `g < N`). -/
def lowMask (N g : Nat) : BitVec N := BitVec.twoPow N g - 1#N

theorem toNat_lowMask {N g : Nat} (hg : g < N) : (lowMask N g).toNat = 2 ^ g - 1 := by
  have hN : 0 < N := by omega
  have h1 : (1#N).toNat = 1 := BitVec.toNat_one hN
  unfold lowMask
  rw [BitVec.toNat_sub, BitVec.toNat_twoPow_of_lt hg, h1]
  have hp : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hlt : 2 ^ g < 2 ^ N := Nat.pow_lt_pow_right (by decide) hg
  rw [show 2 ^ N - 1 + 2 ^ g = (2 ^ g - 1) + 2 ^ N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem getLsbD_lowMask {N g : Nat} (hg : g < N) (i : Nat) :
    (lowMask N g).getLsbD i = decide (i < g) := by
  rw [← BitVec.testBit_toNat, toNat_lowMask hg, Nat.testBit_two_pow_sub_one]

/-- Highest set bit scan via `List.range N`, starting at `init`. -/
def scanHigh {N : Nat} (s : BitVec N) (init : Nat) : Nat :=
  (List.range N).foldl (fun acc k => if s.getLsbD k then k else acc) init

def IsHigh {N : Nat} (s : BitVec N) (k : Nat) : Prop :=
  s.getLsbD k = true ∧ ∀ j, k < j → s.getLsbD j = false

private theorem scanHigh_prefix {N : Nat} (s : BitVec N) (init : Nat) :
    ∀ m, m ≤ N →
      ((∀ k, k < m → s.getLsbD k = false) →
        (List.range m).foldl (fun acc k => if s.getLsbD k then k else acc) init = init) ∧
      ((∃ k, k < m ∧ s.getLsbD k = true) →
        let r := (List.range m).foldl (fun acc k => if s.getLsbD k then k else acc) init
        r < m ∧ s.getLsbD r = true ∧ ∀ j, r < j → j < m → s.getLsbD j = false)
  | 0, _ => ⟨fun _ => rfl, fun ⟨_, hk, _⟩ => absurd hk (Nat.not_lt_zero _)⟩
  | m + 1, hm => by
    obtain ⟨ih0, ih1⟩ := scanHigh_prefix s init m (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    constructor
    · intro hall
      have hsm : s.getLsbD m = false := hall m (Nat.lt_succ_self m)
      simp only [hsm, Bool.false_eq_true, ↓reduceIte]
      exact ih0 (fun k hk => hall k (by omega))
    · intro hex
      by_cases hsm : s.getLsbD m = true
      · simp only [hsm, ↓reduceIte]
        exact ⟨Nat.lt_succ_self m, trivial, fun j hj1 hj2 => by omega⟩
      · have hsmf : s.getLsbD m = false := by cases hb : s.getLsbD m <;> simp_all
        simp only [hsmf, Bool.false_eq_true, ↓reduceIte]
        have hex' : ∃ k, k < m ∧ s.getLsbD k = true := by
          obtain ⟨k, hk, hsk⟩ := hex
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
          · exact ⟨k, hlt, hsk⟩
          · exact absurd hsk hsm
        obtain ⟨hrlt, hrs, hrhi⟩ := ih1 hex'
        refine ⟨by omega, hrs, fun j hj1 hj2 => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj2) with hlt | rfl
        · exact hrhi j hj1 hlt
        · exact hsmf

theorem scanHigh_zero {N : Nat} (init : Nat) : scanHigh (0#N) init = init :=
  (scanHigh_prefix (0#N) init N (Nat.le_refl N)).1 (fun _ _ => BitVec.getLsbD_zero)

private theorem bv_getLsbD_ge {w : Nat} (s : BitVec w) {j : Nat} (hj : w ≤ j) :
    s.getLsbD j = false := by
  cases hb : s.getLsbD j
  · rfl
  · have := BitVec.lt_of_getLsbD hb; omega

theorem scanHigh_isHigh {N : Nat} {s : BitVec N} (hs : s ≠ 0#N) (init : Nat) :
    IsHigh s (scanHigh s init) := by
  have hex : ∃ k, k < N ∧ s.getLsbD k = true := by
    refine Classical.byContradiction fun hno => hs ?_
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_zero]
    cases hb : s.getLsbD i
    · rfl
    · exact absurd ⟨i, hi, hb⟩ hno
  obtain ⟨hrlt, hrs, hrhi⟩ := (scanHigh_prefix s init N (Nat.le_refl N)).2 hex
  refine ⟨hrs, fun j hj => ?_⟩
  by_cases hjN : j < N
  · exact hrhi j hj hjN
  · exact bv_getLsbD_ge s (by omega)

theorem scanHigh_lt {N : Nat} (s : BitVec N) {init : Nat} (hinit : init < N) :
    scanHigh s init < N := by
  by_cases hs : s = 0#N
  · subst hs; rw [scanHigh_zero]; exact hinit
  · exact BitVec.lt_of_getLsbD (scanHigh_isHigh hs init).1

/-- The next `gid` index computed by the two loops. -/
def pickIdx (N : Nat) (x : BitVec N) (g : Nat) : Nat :=
  scanHigh (x &&& lowMask N g) (scanHigh x 0)

theorem pickIdx_lt {N : Nat} (hN : 1 ≤ N) (x : BitVec N) (g : Nat) : pickIdx N x g < N :=
  scanHigh_lt _ (scanHigh_lt _ (by omega))

def selDesc {N : Nat} (x : BitVec N) (g : Nat) : BitVec N :=
  if x &&& lowMask N g = 0#N then x else x &&& lowMask N g

theorem pickIdx_isHigh {N : Nat} {x : BitVec N} (hx : x ≠ 0#N) (g : Nat) :
    IsHigh (selDesc x g) (pickIdx N x g) := by
  unfold pickIdx selDesc
  by_cases hm : x &&& lowMask N g = 0#N
  · simp only [hm, ↓reduceIte, scanHigh_zero]
    exact scanHigh_isHigh hx 0
  · simp only [hm, ↓reduceIte]
    exact scanHigh_isHigh hm (scanHigh x 0)

/-- The grant vector produced on a non-reset cycle with request `x` and prior `gid = g`. -/
def pickGnt (N : Nat) (x : BitVec N) (g : Nat) : BitVec N :=
  if x = 0#N then 0#N else BitVec.twoPow N (pickIdx N x g)

theorem pickGnt_grants {N : Nat} (x : BitVec N) (g : Nat) :
    Tasks.Arbiter.Grants x (pickGnt N x g) := by
  by_cases hx : x = 0#N
  · subst hx
    refine ⟨fun i j hi _ => by simp [pickGnt] at hi,
            fun i hi => by simp [pickGnt] at hi,
            fun h => absurd rfl h⟩
  · have hh : IsHigh (selDesc x g) (pickIdx N x g) := pickIdx_isHigh hx g
    have hkN : pickIdx N x g < N := BitVec.lt_of_getLsbD hh.1
    have hkx : x.getLsbD (pickIdx N x g) = true := by
      have h1 := hh.1
      unfold selDesc at h1
      split at h1
      · exact h1
      · rw [BitVec.getLsbD_and, Bool.and_eq_true] at h1; exact h1.1
    refine ⟨fun i j hi hj => ?_, fun i hi => ?_, fun _ h0 => ?_⟩
    · simp only [pickGnt, hx, ↓reduceIte, BitVec.getLsbD_twoPow, Bool.and_eq_true,
        decide_eq_true_eq] at hi hj
      omega
    · simp only [pickGnt, hx, ↓reduceIte, BitVec.getLsbD_twoPow, Bool.and_eq_true,
        decide_eq_true_eq] at hi
      rw [← hi.2]; exact hkx
    · have hbit := congrArg (fun v => v.getLsbD (pickIdx N x g)) h0
      simp [pickGnt, hx, hkN] at hbit

/-- Descending cyclic rank of client `i` from priority pointer `g`:
`(g - 1) mod N` has rank `0`, ..., `g` has rank `N - 1`. -/
def rankDesc (N g i : Nat) : Nat :=
  if i < g then g - 1 - i else g + N - 1 - i

theorem rankDesc_le {N g i : Nat} (hg : g < N) (hi : i < N) : rankDesc N g i ≤ N - 1 := by
  unfold rankDesc; split <;> omega

theorem rankDesc_step {N g i : Nat} {x : BitVec N} (hg : g < N) (hi : i < N)
    (hxi : x.getLsbD i = true) (hng : (pickGnt N x g).getLsbD i = false) :
    rankDesc N (pickIdx N x g) i < rankDesc N g i := by
  have hx : x ≠ 0#N := by
    intro h0; subst h0; rw [BitVec.getLsbD_zero] at hxi; exact absurd hxi (by decide)
  have hh := pickIdx_isHigh hx g
  let k := pickIdx N x g
  have hkN : k < N := BitVec.lt_of_getLsbD hh.1
  have hik : i ≠ k := by
    intro heq; subst heq
    have hkN' : pickIdx N x g < N := hkN
    simp [pickGnt, hx, hkN'] at hng
    exact hng rfl
  by_cases hm : x &&& lowMask N g = 0#N
  · rw [show selDesc x g = x by simp [selDesc, hm]] at hh
    have hmi : (lowMask N g).getLsbD i = false := by
      have h0 := congrArg (fun v => v.getLsbD i) hm
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero, hxi, Bool.true_and] at h0
      exact h0
    have hgi : ¬ i < g := by
      rw [getLsbD_lowMask hg i] at hmi; simpa using hmi
    have hik_lt : i < pickIdx N x g := by
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · have hgt : k < i := by omega
        exact absurd (hxi.symm.trans (hh.2 i hgt)) (by decide)
    simp only [rankDesc, hik_lt, hgi, ↓reduceIte]
    omega
  · rw [show selDesc x g = x &&& lowMask N g by simp [selDesc, hm]] at hh
    have hmk : (lowMask N g).getLsbD k = true := by
      have h0 := hh.1; rw [BitVec.getLsbD_and, Bool.and_eq_true] at h0; exact h0.2
    have hkg : k < g := by
      rw [getLsbD_lowMask hg k] at hmk; exact of_decide_eq_true hmk
    by_cases hig : i < g
    · have hik_lt : i < pickIdx N x g := by
        rcases Nat.lt_or_ge i k with h | h
        · exact h
        · have hgt : k < i := by omega
          have h0 := hh.2 i hgt
          rw [BitVec.getLsbD_and, hxi, getLsbD_lowMask hg i, decide_eq_true hig] at h0
          exact absurd h0 (by decide)
      simp only [rankDesc, hik_lt, hig, ↓reduceIte]
      omega
    · have hnik : ¬ i < pickIdx N x g := by omega
      simp only [rankDesc, hnik, hig, ↓reduceIte]
      omega

/-! ## 5. Evaluation of `arbNext` on known values (and arbitrary states on reset) -/

theorem z0_eq_ofBitVec (w : Nat) : z0 w = LVec.ofBitVec (0#w) := by
  apply LVec.ext_getElem?
  intro i
  by_cases hi : i < w
  · simp [z0, LVec.replicate, LVec.getElem?_ofBitVec, hi, Logic.ofBool]
  · simp [z0, LVec.replicate, LVec.getElem?_ofBitVec, hi]

theorem one1_resize {N : Nat} : one1.resizeU N = LVec.ofBitVec (1#N) := by
  have h : one1 = LVec.ofBitVec (BitVec.ofBool true) := LVec.ofLogic_l1
  rw [h, LVec.resizeU_ofBitVec]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem shl_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shl (LVec.ofBitVec y) = LVec.ofBitVec (x <<< y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shl, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shl, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn,
    LVec.width_ofBitVec, hi, dite_true, BitVec.getLsbD_shiftLeft]
  by_cases h : i < y.toNat
  · simp [h, Logic.ofBool]
  · have h2 : i - y.toNat < w := by omega
    simp [h, h2, LVec.getElem?_ofBitVec]

theorem shr_ofBitVec {w v : Nat} (x : BitVec w) (y : BitVec v) :
    (LVec.ofBitVec x).shr (LVec.ofBitVec y) = LVec.ofBitVec (x >>> y.toNat) := by
  rw [LVec.eq_ofBitVec_iff]
  refine ⟨by simp [LVec.shr, LVec.shiftAmount?, LVec.width]; exact LVec.width_ofBitVec x, fun i hi => ?_⟩
  simp only [LVec.shr, LVec.shiftAmount?, LVec.toNat?_ofBitVec, Array.getElem?_ofFn,
    LVec.width_ofBitVec, hi, dite_true, BitVec.getLsbD_ushiftRight]
  by_cases h : i + y.toNat < w
  · simp only [LVec.getElem?_ofBitVec, h, ↓reduceIte, Option.getD_some, Nat.add_comm]
  · have hsz : (LVec.ofBitVec x).bits.size ≤ i + y.toNat := by
      have hw : (LVec.ofBitVec x).bits.size = w := LVec.width_ofBitVec x
      omega
    rw [Array.getElem?_eq_none hsz, Option.getD_none, bv_getLsbD_ge x (by omega)]
    rfl

theorem ofInt_natCast {w k : Nat} : LVec.ofInt w (k : Int) = LVec.ofBitVec (BitVec.ofNat w k) := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.ofInt, LVec.ofNat, LVec.getElem?_ofBitVec, Array.getElem?_ofFn]
  by_cases hi : i < w
  · simp only [hi, ↓reduceDIte]
    have hm : ((k : Int) % ((2 : Int) ^ w)).toNat = k % 2 ^ w := by
      have : (k : Int) % ((2 : Int) ^ w) = ((k % 2 ^ w : Nat) : Int) := by
        exact_mod_cast (Int.natCast_emod k (2 ^ w)).symm
      rw [this, Int.toNat_natCast]
    have ht : (k % 2 ^ w).testBit i = k.testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    change some (if ((k : Int).emod ((2 : Int) ^ w)).toNat.testBit i = true then Logic.l1 else Logic.l0) =
      some (Logic.ofBool ((BitVec.ofNat w k).getLsbD i))
    have he : (k : Int).emod ((2 : Int) ^ w) = (k : Int) % ((2 : Int) ^ w) := rfl
    rw [he, hm, BitVec.getLsbD_ofNat, ht]
    simp only [hi, decide_true, Bool.true_and]
    cases k.testBit i <;> rfl
  · simp [hi]

theorem one_shl_eq_twoPow {N g : Nat} (hg : g < N) : (1#N) <<< g = BitVec.twoPow N g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, BitVec.getLsbD_twoPow, hi, decide_true,
    Bool.true_and]
  by_cases h1 : g ≤ i
  · by_cases h2 : i = g
    · subst h2; simp [show 0 < N by omega, hi]
    · have : i - g ≠ 0 := by omega
      simp [this, Ne.symm h2]
  · have : g ≠ i := by omega
    simp [h1, this]

/-- **Crucial reset property**: on ANY `src` and `one` (even containing `x`), `scanFold` over
indices `< N` starting from a known vector `< N` always yields a known vector `< N`. -/
theorem scanFold_known_lt {N : Nat} (hN : 1 ≤ N) (src one : LVec) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < N) →
    ∀ (g0 : BitVec (Wfn N)), g0.toNat < N →
      ∃ g1 : BitVec (Wfn N),
        scanFold N (Wfn N) src one ks (LVec.ofBitVec g0) = LVec.ofBitVec g1 ∧ g1.toNat < N
  | [], _, g0, hg0 => ⟨g0, rfl, hg0⟩
  | k :: ks, hks, g0, hg0 => by
    have hk : k < N := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j < N := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    rw [scanFold_cons]
    by_cases hc : scanCond N src one k = true
    · simp only [hc, ↓reduceIte]
      have harg : (LVec.ofInt (Wfn N) (k : Int)).resizeU (LVec.ofBitVec g0).width =
          LVec.ofBitVec (BitVec.ofNat (Wfn N) k) := by
        rw [LVec.width_ofBitVec, ofInt_natCast, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
      rw [harg]
      have hkW : (BitVec.ofNat (Wfn N) k).toNat < N := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hk (le_two_pow_Wfn N))]
        exact hk
      exact scanFold_known_lt hN src one ks hks' (BitVec.ofNat (Wfn N) k) hkW
    · simp only [hc]
      exact scanFold_known_lt hN src one ks hks' g0 hg0

theorem ngidS_known_lt {N : Nat} (hN : 1 ≤ N) (q gid one oh mask rm ngid : LVec)
    (hngid : ngid.width = Wfn N) :
    ∃ g' : BitVec (Wfn N), ngidS N q gid one oh mask rm ngid = LVec.ofBitVec g' ∧ g'.toNat < N := by
  unfold ngidS NgidV
  have h0 : (z0 (Wfn N)).resizeU ngid.width = LVec.ofBitVec (0#(Wfn N)) := by
    rw [z0_eq_ofBitVec, hngid, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  rw [h0]
  obtain ⟨g1, hg1, hlt1⟩ := scanFold_known_lt hN q (oneS N one) (List.range N)
    (fun k hk => List.mem_range.mp hk) (0#(Wfn N)) (by simp; omega)
  rw [hg1]
  exact scanFold_known_lt hN (rmS N q gid one oh mask rm) (oneS N one) (List.range N)
    (fun k hk => List.mem_range.mp hk) g1 hlt1

theorem scanCond_ofBitVec {N : Nat} (hN : 1 ≤ N) (s : BitVec N) {k : Nat} (hk : k < 2 ^ 32) :
    scanCond N (LVec.ofBitVec s) (LVec.ofBitVec (1#N)) k = s.getLsbD k := by
  unfold scanCond
  rw [ofInt_natCast, shr_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, LVec.and_ofBitVec]
  have hne : (LVec.ofBitVec ((s >>> k) &&& 1#N)).neLogical (z0 N) =
      Logic.ofBool (decide (((s >>> k) &&& 1#N) ≠ 0#N)) := by
    rw [z0_eq_ofBitVec, LVec.neLogical, LVec.eqLogical_ofBitVec]
    by_cases h : ((s >>> k) &&& 1#N) = 0#N <;> simp [h, Logic.not]
  rw [hne, LVec.ofLogic_ofBool, condTrue_knownBit]
  have heq : (((s >>> k) &&& 1#N) ≠ 0#N) ↔ s.getLsbD k = true := by
    constructor
    · intro h
      refine Classical.byContradiction fun hsk => h ?_
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_one,
        BitVec.getLsbD_zero]
      cases i with
      | zero => simp [hi]; cases hb : s.getLsbD k <;> simp_all
      | succ i => simp
    · intro hsk h0
      have hb := congrArg (fun v => v.getLsbD 0) h0
      simp [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_one, hsk] at hb
      omega
  cases hb : s.getLsbD k
  · rw [decide_eq_false (by intro h; exact absurd (heq.1 h) (by simp [hb]))]
  · rw [decide_eq_true (heq.2 hb)]

theorem scanFold_ofBitVec {N : Nat} (hN : 1 ≤ N) (hR32 : Rng32 N) (s : BitVec N) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < N) → ∀ (a0 : Nat),
      scanFold N (Wfn N) (LVec.ofBitVec s) (LVec.ofBitVec (1#N)) ks
        (LVec.ofBitVec (BitVec.ofNat (Wfn N) a0)) =
      LVec.ofBitVec (BitVec.ofNat (Wfn N)
        (ks.foldl (fun acc k => if s.getLsbD k then k else acc) a0))
  | [], _, _ => rfl
  | k :: ks, hks, a0 => by
    have hk : k < N := hks k List.mem_cons_self
    have hk32 : k < 2 ^ 32 := by unfold Rng32 at hR32; omega
    have hks' : ∀ j ∈ ks, j < N := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    rw [scanFold_cons, List.foldl_cons, scanCond_ofBitVec hN s hk32]
    cases hb : s.getLsbD k
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact scanFold_ofBitVec hN hR32 s ks hks' a0
    · simp only [↓reduceIte]
      have harg : (LVec.ofInt (Wfn N) (k : Int)).resizeU (LVec.ofBitVec (BitVec.ofNat (Wfn N) a0)).width =
          LVec.ofBitVec (BitVec.ofNat (Wfn N) k) := by
        rw [LVec.width_ofBitVec, ofInt_natCast, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
      rw [harg]
      exact scanFold_ofBitVec hN hR32 s ks hks' k

theorem oneS_val {N : Nat} (one : LVec) (hone : one.width = N) :
    oneS N one = LVec.ofBitVec (1#N) := by
  simp [oneS, OneV, one1_resize, hone]

theorem ohS_val {N : Nat} (g : BitVec (Wfn N)) (hg : g.toNat < N) (one oh : LVec)
    (hone : one.width = N) (hoh : oh.width = N) :
    ohS N (LVec.ofBitVec g) one oh = LVec.ofBitVec (BitVec.twoPow N g.toNat) := by
  unfold ohS OhV
  rw [oneS_val one hone, shl_ofBitVec, one_shl_eq_twoPow hg, hoh, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq]

theorem gntS_val {N : Nat} (v : Bool) (g : BitVec (Wfn N)) (hg : g.toNat < N) (gn one oh : LVec)
    (hgn : gn.width = N) (hone : one.width = N) (hoh : oh.width = N) :
    gntS N (knownBit v) (LVec.ofBitVec g) gn one oh =
      LVec.ofBitVec (if v then BitVec.twoPow N g.toNat else 0#N) := by
  unfold gntS GntV
  rw [ohS_val g hg one oh hone hoh, z0_eq_ofBitVec, LVec.ternary]
  cases v
  · have hc : (knownBit false).condTrue = false := condTrue_knownBit false
    have hz : (knownBit false).isKnownZero = true := by
      have hk : knownBit false = zero1 := LVec.ofLogic_l0.symm
      rw [hk, LVec.isKnownZero, Array.all_eq_true]
      intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0; rfl
    simp [hc, hz, hgn]
  · have hc : (knownBit true).condTrue = true := condTrue_knownBit true
    simp [hc, hgn]

theorem maskS_val {N : Nat} (g : BitVec (Wfn N)) (hg : g.toNat < N) (one oh mask : LVec)
    (hone : one.width = N) (hoh : oh.width = N) (hmask : mask.width = N) :
    maskS N (LVec.ofBitVec g) one oh mask = LVec.ofBitVec (lowMask N g.toNat) := by
  unfold maskS MaskV lowMask
  rw [ohS_val g hg one oh hone hoh, one1_resize, LVec.sub_ofBitVec, hmask, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq]

theorem rmS_val {N : Nat} (x : BitVec N) (g : BitVec (Wfn N)) (hg : g.toNat < N)
    (one oh mask rm : LVec) (hone : one.width = N) (hoh : oh.width = N)
    (hmask : mask.width = N) (hrm : rm.width = N) :
    rmS N (LVec.ofBitVec x) (LVec.ofBitVec g) one oh mask rm =
      LVec.ofBitVec (x &&& lowMask N g.toNat) := by
  unfold rmS RmV
  rw [maskS_val g hg one oh mask hone hoh hmask, LVec.and_ofBitVec, hrm, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq]

theorem ngidS_val {N : Nat} (hN : 1 ≤ N) (hR32 : Rng32 N) (x : BitVec N) (g : BitVec (Wfn N))
    (hg : g.toNat < N) (one oh mask rm ngid : LVec) (hone : one.width = N) (hoh : oh.width = N)
    (hmask : mask.width = N) (hrm : rm.width = N) (hngid : ngid.width = Wfn N) :
    ngidS N (LVec.ofBitVec x) (LVec.ofBitVec g) one oh mask rm ngid =
      LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x g.toNat)) := by
  unfold ngidS NgidV pickIdx scanHigh
  rw [oneS_val one hone, rmS_val x g hg one oh mask rm hone hoh hmask hrm]
  have h0 : (z0 (Wfn N)).resizeU ngid.width = LVec.ofBitVec (BitVec.ofNat (Wfn N) 0) := by
    rw [z0_eq_ofBitVec, hngid, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  rw [h0, scanFold_ofBitVec hN hR32 x (List.range N) (fun k hk => List.mem_range.mp hk) 0,
      scanFold_ofBitVec hN hR32 (x &&& lowMask N g.toNat) (List.range N)
        (fun k hk => List.mem_range.mp hk)]

theorem Vv_reset {N : Nat} {v : LVec} (q : LVec) (hv : v.width = 1) :
    Vv N (knownBit true) q v = knownBit false := by
  simp [Vv, hv, zero1, LVec.resizeU_one_l0, knownBit]

theorem Vv_run {N : Nat} {v : LVec} (x : BitVec N) (hv : v.width = 1) :
    Vv N (knownBit false) (LVec.ofBitVec x) v = knownBit (decide (x ≠ 0#N)) := by
  simp only [Vv, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, hv]
  have hne : (LVec.ofBitVec x).neLogical (z0 N) = Logic.ofBool (decide (x ≠ 0#N)) := by
    rw [z0_eq_ofBitVec, LVec.neLogical, LVec.eqLogical_ofBitVec]
    by_cases h : x = 0#N <;> simp [h, Logic.not]
  rw [hne, LVec.ofLogic_ofBool, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem arbNext_reset {N : Nat} (hN : 1 ≤ N) (hR32 : Rng32 N)
    {e : SvState} {ck r q g v gid one oh mask rm ngid : LVec} {x : BitVec N}
    (hb : BitIs e "rst" true) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hg : g.width = N) (hv : v.width = 1) (hgid : gid.width = Wfn N)
    (hone : one.width = N) (hoh : oh.width = N) (hmask : mask.width = N)
    (hrm : rm.width = N) (hngid : ngid.width = Wfn N) :
    ∃ g' : BitVec (Wfn N), g'.toNat < N ∧
      arbNext N e ck r q g v gid one oh mask rm ngid =
        SS (appIn e "clk" ck) (knownBit true) (LVec.ofBitVec x)
          (LVec.ofBitVec 0#N) (knownBit false) (LVec.ofBitVec g')
          (LVec.ofBitVec (1#N)) (LVec.ofBitVec (BitVec.twoPow N g'.toNat))
          (LVec.ofBitVec (lowMask N g'.toNat))
          (LVec.ofBitVec (x &&& lowMask N g'.toNat))
          (LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x g'.toNat))) := by
  have hr : appIn e "rst" r = knownBit true := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  obtain ⟨g', hg'eq, hg'lt⟩ := ngidS_known_lt hN (LVec.ofBitVec x) gid one oh mask rm ngid hngid
  refine ⟨g', hg'lt, ?_⟩
  unfold arbNext combS
  dsimp only
  rw [hr, hq', Vv_reset _ hv, hg'eq]
  have hgv : Gidv gid (LVec.ofBitVec g') = LVec.ofBitVec g' := by simp [Gidv, hgid]
  have hone1 : (oneS N one).width = N := by simp [oneS, hone]
  have hoh1 : (ohS N gid one oh).width = N := by simp [ohS, hoh]
  have hg1 : (gntS N v gid g one oh).width = N := by simp [gntS, hg]
  have hmask1 : (maskS N gid one oh mask).width = N := by simp [maskS, hmask]
  have hrm1 : (rmS N (LVec.ofBitVec x) gid one oh mask rm).width = N := by simp [rmS, hrm]
  rw [hgv,
      oneS_val (oneS N one) hone1,
      ohS_val g' hg'lt _ _ hone1 hoh1,
      gntS_val false g' hg'lt _ _ _ hg1 hone1 hoh1,
      maskS_val g' hg'lt _ _ _ hone1 hoh1 hmask1,
      rmS_val x g' hg'lt _ _ _ _ hone1 hoh1 hmask1 hrm1,
      ngidS_val hN hR32 x g' hg'lt _ _ _ _ _ hone1 hoh1 hmask1 hrm1 (LVec.width_ofBitVec g')]
  simp only [Bool.false_eq_true, ↓reduceIte]

theorem arbNext_run {N : Nat} (hN : 1 ≤ N) (hR32 : Rng32 N)
    {e : SvState} {ck r q g v gid one oh mask rm ngid : LVec} {x : BitVec N} {gp : BitVec (Wfn N)}
    (hb : BitIs e "rst" false) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hgp : gid = LVec.ofBitVec gp) (hgplt : gp.toNat < N)
    (hg : g.width = N) (hv : v.width = 1)
    (hone : one.width = N) (hoh : oh.width = N) (hmask : mask.width = N)
    (hrm : rm.width = N) (hngid : ngid.width = Wfn N) :
    let g' := BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)
    g'.toNat = pickIdx N x gp.toNat ∧
    arbNext N e ck r q g v gid one oh mask rm ngid =
      SS (appIn e "clk" ck) (knownBit false) (LVec.ofBitVec x)
        (LVec.ofBitVec (pickGnt N x gp.toNat)) (knownBit (decide (x ≠ 0#N))) (LVec.ofBitVec g')
        (LVec.ofBitVec (1#N)) (LVec.ofBitVec (BitVec.twoPow N g'.toNat))
        (LVec.ofBitVec (lowMask N g'.toNat))
        (LVec.ofBitVec (x &&& lowMask N g'.toNat))
        (LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x g'.toNat))) := by
  subst hgp
  have hr : appIn e "rst" r = knownBit false := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  have hpk_lt : pickIdx N x gp.toNat < N := pickIdx_lt hN x gp.toNat
  have hg'nat : (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)).toNat = pickIdx N x gp.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hpk_lt (le_two_pow_Wfn N))]
  have hg'lt : (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)).toNat < N := by rw [hg'nat]; exact hpk_lt
  refine ⟨hg'nat, ?_⟩
  unfold arbNext combS
  dsimp only
  rw [hr, hq', Vv_run x hv,
      ngidS_val hN hR32 x gp hgplt one oh mask rm ngid hone hoh hmask hrm hngid]
  have hgv : Gidv (LVec.ofBitVec gp) (LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat))) =
      LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)) := by
    simp [Gidv]
  have hone1 : (oneS N one).width = N := by simp [oneS, hone]
  have hoh1 : (ohS N (LVec.ofBitVec gp) one oh).width = N := by simp [ohS, hoh]
  have hg1 : (gntS N v (LVec.ofBitVec gp) g one oh).width = N := by simp [gntS, hg]
  have hmask1 : (maskS N (LVec.ofBitVec gp) one oh mask).width = N := by simp [maskS, hmask]
  have hrm1 : (rmS N (LVec.ofBitVec x) (LVec.ofBitVec gp) one oh mask rm).width = N := by simp [rmS, hrm]
  rw [hgv,
      oneS_val (oneS N one) hone1,
      ohS_val _ hg'lt _ _ hone1 hoh1,
      gntS_val (decide (x ≠ 0#N)) _ hg'lt _ _ _ hg1 hone1 hoh1,
      maskS_val _ hg'lt _ _ _ hone1 hoh1 hmask1,
      rmS_val x _ hg'lt _ _ _ _ hone1 hoh1 hmask1 hrm1,
      ngidS_val hN hR32 x _ hg'lt _ _ _ _ _ hone1 hoh1 hmask1 hrm1 (LVec.width_ofBitVec _)]
  have hgnt_eq : (if decide (x ≠ 0#N) = true then BitVec.twoPow N (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)).toNat else 0#N) =
      pickGnt N x gp.toNat := by
    unfold pickGnt
    rw [hg'nat]
    by_cases hx : x = 0#N <;> simp [hx]
  rw [hgnt_eq]

/-! ## 6. Rank model, structure, rules, and main theorem -/

def bvOf (N : Nat) (n : String) (st : SvState) : BitVec N :=
  BitVec.ofNat N ((SvState.lookup st n).getD (LVec.xVec N)).toNat

def natOf (W : Nat) (n : String) (st : SvState) : Nat :=
  ((SvState.lookup st n).getD (LVec.xVec W)).toNat

theorem bvOf_gnt {N : Nat} {ck r q v gid one oh mask rm ngid : LVec} {g : BitVec N} :
    bvOf N "gnt" (SS ck r q (LVec.ofBitVec g) v gid one oh mask rm ngid) = g := by
  simp [bvOf, SS, SvState.lookup, BitVec.ofNat_toNat]

theorem natOf_gid {W : Nat} {ck r q g v one oh mask rm ngid : LVec} {gp : BitVec W} :
    natOf W "gid" (SS ck r q g v (LVec.ofBitVec gp) one oh mask rm ngid) = gp.toNat := by
  simp [natOf, SS, SvState.lookup]

def ArbInv (N : Nat) (st : SvState) : Prop :=
  ∃ (ck : LVec) (b v : Bool) (x : BitVec N) (g : BitVec (Wfn N)),
    g.toNat < N ∧
    st = SS ck (knownBit b) (LVec.ofBitVec x)
      (LVec.ofBitVec (if v then BitVec.twoPow N g.toNat else 0#N))
      (knownBit v) (LVec.ofBitVec g)
      (LVec.ofBitVec (1#N))
      (LVec.ofBitVec (BitVec.twoPow N g.toNat))
      (LVec.ofBitVec (lowMask N g.toNat))
      (LVec.ofBitVec (x &&& lowMask N g.toNat))
      (LVec.ofBitVec (BitVec.ofNat (Wfn N) (pickIdx N x g.toNat)))

def model (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.RankModel N (N - 1) (design.sem N) where
  Shape := Shp N
  Step := Stp N
  init := by rw [arb_sem_eq N hN hR32]; exact arb_init N
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, rfl, hw⟩ hc
    rw [arb_sem_eq N hN hR32] at hc
    obtain ⟨k2, h2⟩ := arb_cycle N σ e ck r q g v gid one oh mask rm ngid k (N + 40) (Nat.le_refl _)
    exact ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc h2)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, -,
      ⟨hg, hv, hgid, hone, hoh, hmask, hrm, hngid⟩, rfl⟩
    exact arbNext_shp hg hv hgid hone hoh hmask hrm hngid
  Inv := fun _ st => ArbInv N st
  out := fun st => (bvOf N "gnt" st, ())
  shows := by
    rintro - st ⟨ck, b, v, x, g, -, rfl⟩
    show SvState.lookup _ "gnt" = some (LVec.ofBitVec (bvOf N "gnt" _)) ∧ True
    rw [bvOf_gnt]
    exact ⟨by simp [SS, SvState.lookup], trivial⟩
  rank := fun o st => rankDesc N (natOf (Wfn N) "gid" st) o.val
  rank_le := by
    rintro o - st ⟨ck, b, v, x, g, hglt, rfl⟩
    show rankDesc N (natOf (Wfn N) "gid" _) o.val ≤ N - 1
    rw [natOf_gid]
    exact rankDesc_le hglt o.isLt
  reset := by
    rintro e prev st ⟨x, ⟨⟩⟩ - ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, -,
      ⟨hg, hv, hgid, hone, hoh, hmask, hrm, hngid⟩, rfl⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    obtain ⟨g', hg'lt, heq⟩ := arbNext_reset hN hR32 hb hq hg hv hgid hone hoh hmask hrm hngid
    rw [heq]
    refine ⟨⟨appIn e "clk" ck, true, false, x, g', hg'lt, rfl⟩, ?_⟩
    show bvOf N "gnt" _ = 0#N
    rw [bvOf_gnt]
  step := by
    rintro e prev st - ⟨x, ⟨⟩⟩ -
      ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, rfl,
        ⟨hg, hv, hgid, hone, hoh, hmask, hrm, hngid⟩, rfl⟩
      ⟨ck', b', v', xp, gp, hgplt, hprev⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    have hgp : gid = LVec.ofBitVec gp := (SS_inj hprev).2.2.1
    have hgid_prev : natOf (Wfn N) "gid" (SS ck r q g v gid one oh mask rm ngid) = gp.toNat := by
      rw [hgp, natOf_gid]
    obtain ⟨hg'nat, hnext⟩ := arbNext_run hN hR32 hb hq hgp hgplt hg hv hone hoh hmask hrm hngid
    rw [hnext]
    have hg'lt : (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)).toNat < N := by
      rw [hg'nat]; exact pickIdx_lt hN x gp.toNat
    have hgnt_eq : (if decide (x ≠ 0#N) = true then BitVec.twoPow N (BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat)).toNat else 0#N) =
        pickGnt N x gp.toNat := by
      unfold pickGnt; rw [hg'nat]; by_cases h : x = 0#N <;> simp [h]
    refine ⟨⟨_, false, decide (x ≠ 0#N), x, BitVec.ofNat (Wfn N) (pickIdx N x gp.toNat),
              hg'lt, by rw [hgnt_eq]⟩, ?_, fun o ho => ?_⟩
    · show Tasks.Arbiter.Grants x (bvOf N "gnt" _)
      rw [bvOf_gnt]
      exact pickGnt_grants x gp.toNat
    · have ho' : x.getLsbD o.val = true := ho
      by_cases hp : (pickGnt N x gp.toNat).getLsbD o.val = true
      · left
        show (bvOf N "gnt" _).getLsbD o.val = true
        rw [bvOf_gnt]
        exact hp
      · right
        show rankDesc N (natOf (Wfn N) "gid" _) o.val <
          rankDesc N (natOf (Wfn N) "gid" (SS ck r q g v gid one oh mask rm ngid)) o.val
        rw [natOf_gid, hgid_prev, hg'nat]
        exact rankDesc_step hgplt o.isLt ho' (by simpa using hp)

theorem arb_interface (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.Interface N (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "req", "gnt", "valid", "gid", "one", "oh", "mask", "rm", "ngid"] : List String).Nodup
    decide⟩

private theorem loop_targets (src : String) (N W : Nat) :
    ∀ m ∈ stmtTargets (loopStmt src N W), m = "ngid" := by
  intro m hm
  have hlist : ∀ (l : List Nat), ∀ m ∈ stmtListTargets (l.map (scanStep src N W)), m = "ngid" := by
    intro l
    induction l with
    | nil => intro m hm; simp [stmtListTargets] at hm
    | cons k rest ih =>
      intro m hm
      simp only [List.map_cons, stmtListTargets, List.mem_append] at hm
      rcases hm with hm | hm
      · simp [scanStep, stmtTargets, stmtListTargets, stmtOptTargets, lhsTargets] at hm; exact hm
      · exact ih m hm
  exact hlist (List.range N) m hm

theorem arb_moore (N : Nat) : MooreOut (arbD N) := by
  refine ⟨fun n => n = "clk" ∨ n = "rst" ∨ n = "req" ∨ n = "rm" ∨ n = "ngid", ?_, ?_, ?_⟩
  · intro n hn
    simp [arbD, arbDecls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl <;> simp
  · intro p hp hcomb ⟨n, hn, hSn⟩ m hm
    simp only [arbD, List.toList_toArray, arbProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [arbP0, processDataNames, lhsNames, exprNames] at hn
      subst hn; simp at hSn
    · simp [arbP1, processDataNames, lhsNames, exprNames] at hn
      rcases hn with rfl | rfl | rfl <;> simp at hSn
    · simp [arbP2, processDataNames, lhsNames, exprNames] at hn
      rcases hn with rfl | rfl | rfl <;> simp at hSn
    · simp [arbP3, processDataNames, lhsNames, exprNames] at hn
      rcases hn with rfl | rfl <;> simp at hSn
    · simp [arbP4, processTargets, lhsTargets] at hm
      subst hm; simp
    · simp only [arbP5, processTargets, combBody, stmtTargets, stmtListTargets, lhsTargets,
        List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | hm | hm
      · simp
      · rw [loop_targets "req" N (Wfn N) m hm]; simp
      · rw [loop_targets "rm" N (Wfn N) m hm]; simp
    · simp [arbP6, Process2.isCombPhase] at hcomb
  · intro o ho
    simp [arbD, arbDecls, Design2.outputNames] at ho
    subst ho; decide

private theorem loop_no_clk (src : String) (hsrc : src ≠ "clk") (N W : Nat) :
    "clk" ∉ stmtNames (loopStmt src N W) := by
  have hlist : ∀ (l : List Nat), "clk" ∉ stmtListNames (l.map (scanStep src N W)) := by
    intro l
    induction l with
    | nil => simp [stmtListNames]
    | cons k rest ih =>
      simp only [List.map_cons, stmtListNames, List.mem_append, not_or]
      refine ⟨?_, ih⟩
      intro h
      simp [scanStep, stmtNames, stmtListNames, stmtOptNames, lhsNames, exprNames] at h
      exact hsrc h.symm
  exact fun h => hlist (List.range N) h

theorem arb_disciplined (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.Disciplined (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  refine ⟨⟨by simp [Tasks.Arbiter.task, arbD, arbDecls, Design2.inputNames], fun p hp => ?_⟩,
    arb_moore N⟩
  simp only [arbD, List.toList_toArray, arbProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [Tasks.Arbiter.task, arbP0, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Arbiter.task, arbP1, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Arbiter.task, arbP2, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Arbiter.task, arbP3, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Arbiter.task, arbP4, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, Process2.isEdgePhase]
  · simp only [Tasks.Arbiter.task, arbP5, edgeClock, asyncReset, processDataNames, Process2.isEdgePhase,
      Bool.false_eq_true, false_implies, true_and, combBody, stmtNames, stmtListNames, lhsNames,
      exprNames, List.mem_append, List.not_mem_nil, or_false, not_or]
    exact ⟨fun _ h => h, ⟨by decide, loop_no_clk "req" (by decide) N (Wfn N),
           loop_no_clk "rm" (by decide) N (Wfn N)⟩⟩
  · simp [Tasks.Arbiter.task, arbP6, ffBody, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, Process2.isEdgePhase]

theorem arb_powerUp (N : Nat) : ∀ st, PowerUp (arbD N) st → Shp N st := by
  intro st h
  have h' : st.map Prod.fst = (arbDecls N (Wfn N)).map Decl.name ∧
      ∀ b ∈ st.zip (arbDecls N (Wfn N)), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true := h
  rw [arbDecls] at h'
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h'
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨q, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨g, r4, rfl, hg, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨v, r5, rfl, hv, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨gid, r6, rfl, hgid, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨one, r7, rfl, hone, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨oh, r8, rfl, hoh, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨mask, r9, rfl, hmask, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨rm, r10, rfl, hrm, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨ngid, r11, rfl, hngid, -, h11⟩ := powerUp_cons.mp h10
  obtain rfl := powerUp_nil.mp h11
  exact ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, rfl,
    hg, hv, hgid, hone, hoh, hmask, hrm, hngid⟩

private theorem loop_noQCase (src : String) (N W : Nat) :
    (loopStmt src N W).hasQualifiedCase = false := by
  have hlist : ∀ (l : List Nat), Stmt2.listHasQualifiedCase (l.map (scanStep src N W)) = false := by
    intro l
    induction l with
    | nil => rfl
    | cons k rest ih =>
      simp [scanStep, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase, ih]
  exact hlist (List.range N)

theorem arb_terminates (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : TerminatesPU (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  refine TerminatesPU.of_invariant (Shp N) (arb_powerUp N) (fun σ => ⟨N + 40, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, q, g, v, gid, one, oh, mask, rm, ngid, rfl,
      hg, hv, hgid, hone, hoh, hmask, hrm, hngid⟩
    obtain ⟨k', h⟩ := arb_cycle N σ e ck r q g v gid one oh mask rm ngid kk (N + 40) (Nat.le_refl _)
    exact ⟨_, _, h, arbNext_shp hg hv hgid hone hoh hmask hrm hngid⟩
  · simp [arbD, arbProcs, arbP0, arbP1, arbP2, arbP3, arbP4, arbP5, arbP6, combBody, ffBody,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase,
      loop_noQCase]

private theorem xsStmts_loop (N : Nat) (src : String)
    (hsrc : sigWidth (arbD N) src = some N) :
    xsStmt (arbD N) (loopStmt src N (Wfn N)) = true := by
  have hone : sigWidth (arbD N) "one" = some N := by simp [sigWidth, arbD, arbDecls]
  have hlist : ∀ (l : List Nat), xsStmts (arbD N) (l.map (scanStep src N (Wfn N))) = true := by
    intro l
    induction l with
    | nil => rfl
    | cons k rest ih =>
      simp [scanStep, xsStmts, xsStmt, xsOpt, xsLhs, xsWidth, binW, hsrc, hone,
        ofInt_natCast, LVec.allKnown_ofBitVec, LVec.width_ofBitVec, ih]
  exact hlist (List.range N)

theorem arb_xsafe (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : XSafe (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  have h1 : xsStmt (arbD N) (loopStmt "req" N (Wfn N)) = true :=
    xsStmts_loop N "req" (by simp [sigWidth, arbD, arbDecls])
  have h2 : xsStmt (arbD N) (loopStmt "rm" N (Wfn N)) = true :=
    xsStmts_loop N "rm" (by simp [sigWidth, arbD, arbDecls])
  have hone1 : one1.allKnown = true := by
    rw [show one1 = LVec.ofBitVec (BitVec.ofBool true) from LVec.ofLogic_l1]
    exact LVec.allKnown_ofBitVec _
  have hzero1 : zero1.allKnown = true := by
    rw [show zero1 = LVec.ofBitVec (BitVec.ofBool false) from LVec.ofLogic_l0]
    exact LVec.allKnown_ofBitVec _
  have hp5 : xsProc (arbD N) (arbP5 N (Wfn N)) = true := by
    simp only [arbP5, combBody, xsProc, xsStmt, xsStmts, h1, h2, Bool.and_true]
    simp [xsLhs, xsWidth, LVec.allKnown_ofBitVec]
  have hall : (arbProcs N (Wfn N)).all (xsProc (arbD N)) = true := by
    simp only [arbProcs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, hp5, ?_⟩
    · simp [arbP0, xsProc, xsLhs, xsWidth, hone1]
    · simp [arbP1, xsProc, xsLhs, xsWidth, binW, sigWidth, arbD, arbDecls]
    · simp [arbP2, xsProc, xsLhs, xsWidth, sigWidth, arbD, arbDecls,
        LVec.allKnown_ofBitVec, LVec.width_ofBitVec]
    · simp [arbP3, xsProc, xsLhs, xsWidth, binW, sigWidth, arbD, arbDecls, hone1]
    · simp [arbP4, xsProc, xsLhs, xsWidth, binW, sigWidth, arbD, arbDecls]
    · simp [arbP6, ffBody, xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth,
        arbD, arbDecls, hzero1, LVec.allKnown_ofBitVec, LVec.width_ofBitVec]
  exact hall

/-- **The binary-index descending round-robin arbiter satisfies the arbiter statement**
at every `N` in range (`1 ≤ N`, `N * N < 2^31`). -/
theorem solution : Goal := by
  intro N hN
  obtain ⟨hN1, hNN⟩ := hN
  have hR32 : Rng32 N := rng32_of hN1 hNN
  exact Tasks.Arbiter.task.satisfiedAt_of_rank (arb_interface N hN1 hR32)
    (arb_disciplined N hN1 hR32) (arb_terminates N hN1 hR32) (model N hN1 hR32)
    (fun st h => arb_powerUp N st (by rw [arb_sem_eq N hN1 hR32] at h; exact h))
    (arb_xsafe N hN1 hR32)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
