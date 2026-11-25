-- svgolf-latency: 1
import Submission.Design
import SvGolf.Cycle
import SvGolf.SeqV2
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib.BitVecArith
import LeanModels.Sv.CombViewArith

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := (N + 3) / 4

theorem winA_le {N W i : Nat} (m : Nat) (hm : m ≤ 3) (hi : i < N) :
    (i * N + m) * W + W ≤ (N * N + 3) * W := by
  have h1 : (i + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  have h : i * N + m + 1 ≤ N * N + 3 := by omega
  have h2 := Nat.mul_le_mul_right W h
  rw [Nat.add_mul (i * N + m) 1 W, Nat.one_mul] at h2
  exact h2

theorem winB_le {N W j : Nat} (m : Nat) (hm : m ≤ 3) (hj : j < N) :
    (m * N + j) * W + W ≤ (N * N + 3 * N) * W := by
  have h1 : m * N ≤ 3 * N := Nat.mul_le_mul_right N hm
  have h3 : N ≤ N * N := Nat.le_mul_self N
  have h : m * N + j + 1 ≤ N * N + 3 * N := by omega
  have h2 := Nat.mul_le_mul_right W h
  rw [Nat.add_mul (m * N + j) 1 W, Nat.one_mul] at h2
  exact h2

theorem winRM_le {N K i j : Nat} (hi : i < N) (hj : j < N) :
    (i * N + j) * K + K ≤ N * N * K := by
  have h1 : (i + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  have h : i * N + j + 1 ≤ N * N := by omega
  have h2 := Nat.mul_le_mul_right K h
  rw [Nat.add_mul (i * N + j) 1 K, Nat.one_mul] at h2
  exact h2

theorem natAbs_sub1 {k : Nat} (hk : 1 ≤ k) : ((k : Int) - 1).natAbs + 1 = k := by omega

set_option hygiene false in
macro "ab_win" : tactic => `(tactic| (
  first
  | (have h1 : (3 * (W : Int)).toNat = 3 * W := by
       rw [show (3 : Int) * W = ((3 * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
     have h2 : (((N : Int) * N + 3) * W - 1).natAbs + 1 = (N * N + 3) * W := by
       rw [show ((N : Int) * N + 3) * W = (((N * N + 3) * W : Nat) : Int) by push_cast; rfl]
       exact natAbs_sub1 (Nat.mul_pos (by omega) (by omega))
     rw [h1, h2, Nat.add_mul]; omega)
  | (have h1 : (3 * (N : Int) * W).toNat = 3 * N * W := by
       rw [show (3 : Int) * N * W = ((3 * N * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
     have h2 : (((N : Int) * N + 3 * N) * W - 1).natAbs + 1 = (N * N + 3 * N) * W := by
       rw [show ((N : Int) * N + 3 * N) * W = (((N * N + 3 * N) * W : Nat) : Int) by push_cast; rfl]
       exact natAbs_sub1 (Nat.mul_pos (by omega) (by omega))
     rw [h1, h2, Nat.add_mul]; omega)
  | (have hTA : (1 : Int) ≤ ((N : Int) * N + 3) * W := by exact_mod_cast Nat.mul_pos (Nat.succ_pos _) (by omega)
     have a0 : (i : Int) * N * W + W ≤ ((N : Int) * N + 3) * W := by
       have := winA_le (W := W) 0 (by omega) hi; simp only [Nat.add_zero] at this; exact_mod_cast this
     have a1 : ((i : Int) * N + 1) * W + W ≤ ((N : Int) * N + 3) * W := by exact_mod_cast winA_le (W := W) 1 (by omega) hi
     have a2 : ((i : Int) * N + 2) * W + W ≤ ((N : Int) * N + 3) * W := by exact_mod_cast winA_le (W := W) 2 (by omega) hi
     have a3 : ((i : Int) * N + 3) * W + W ≤ ((N : Int) * N + 3) * W := by exact_mod_cast winA_le (W := W) 3 (by omega) hi
     have z0 : (0 : Int) ≤ (i : Int) * N * W := by exact_mod_cast Nat.zero_le _
     have z1 : (0 : Int) ≤ ((i : Int) * N + 1) * W := by exact_mod_cast Nat.zero_le ((i * N + 1) * W)
     have z2 : (0 : Int) ≤ ((i : Int) * N + 2) * W := by exact_mod_cast Nat.zero_le ((i * N + 2) * W)
     have z3 : (0 : Int) ≤ ((i : Int) * N + 3) * W := by exact_mod_cast Nat.zero_le ((i * N + 3) * W)
     simp (disch := omega) only [Int.natAbs_of_nonneg]
     omega)
  | (have hTB : (1 : Int) ≤ ((N : Int) * N + 3 * N) * W := by
       exact_mod_cast Nat.mul_pos (show 0 < N * N + 3 * N by omega) (by omega)
     have b0 : (j : Int) * W + W ≤ ((N : Int) * N + 3 * N) * W := by
       have := winB_le (W := W) 0 (by omega) hj; simp only [Nat.zero_mul, Nat.zero_add] at this; exact_mod_cast this
     have b1 : ((N : Int) + j) * W + W ≤ ((N : Int) * N + 3 * N) * W := by
       have := winB_le (W := W) 1 (by omega) hj; simp only [Nat.one_mul] at this; exact_mod_cast this
     have b2 : (2 * (N : Int) + j) * W + W ≤ ((N : Int) * N + 3 * N) * W := by exact_mod_cast winB_le (W := W) 2 (by omega) hj
     have b3 : (3 * (N : Int) + j) * W + W ≤ ((N : Int) * N + 3 * N) * W := by exact_mod_cast winB_le (W := W) 3 (by omega) hj
     have y0 : (0 : Int) ≤ (j : Int) * W := by exact_mod_cast Nat.zero_le _
     have y1 : (0 : Int) ≤ ((N : Int) + j) * W := by exact_mod_cast Nat.zero_le ((N + j) * W)
     have y2 : (0 : Int) ≤ (2 * (N : Int) + j) * W := by exact_mod_cast Nat.zero_le ((2 * N + j) * W)
     have y3 : (0 : Int) ≤ (3 * (N : Int) + j) * W := by exact_mod_cast Nat.zero_le ((3 * N + j) * W)
     simp (disch := omega) only [Int.natAbs_of_nonneg]
     omega)
  | (have hp : ((i : Int) * N + j) * (2 * W) + 2 * W ≤ (N : Int) * N * (2 * W) := by
       exact_mod_cast winRM_le (K := 2 * W) hi hj
     have hs : ((i : Int) * N + j) * (2 * W + 2) + (2 * W + 2) ≤ (N : Int) * N * (2 * W + 2) := by
       exact_mod_cast winRM_le (K := 2 * W + 2) hi hj
     have hTp : (1 : Int) ≤ (N : Int) * N * (2 * W) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
     have hTs : (1 : Int) ≤ (N : Int) * N * (2 * W + 2) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
     have zp : (0 : Int) ≤ ((i : Int) * N + j) * (2 * W) := by exact_mod_cast Nat.zero_le ((i * N + j) * (2 * W))
     have zs : (0 : Int) ≤ ((i : Int) * N + j) * (2 * W + 2) := by exact_mod_cast Nat.zero_le ((i * N + j) * (2 * W + 2))
     simp (disch := omega) only [Int.natAbs_of_nonneg]
     omega)))

sv_mirror mmG (window := by ab_win) := design (N W AccW : Nat)
  (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127) (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64)


/-! ## Section 1: Clean hand-written mirror `mmD` and `mm_sem_eq` -/

abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)
abbrev amtA (W : Nat) : Expr2 := .binary .mul (c32 2) (c32 W)
abbrev amtB (N W : Nat) : Expr2 := .binary .mul (.binary .mul (c32 2) (c32 N)) (c32 W)
abbrev condSel (N : Nat) : Expr2 :=
  .logical (SymBinOp.lor == SymBinOp.land) (.ident "start") (.scmp .le (c32 N) (c32 4))
abbrev condGt4 (N : Nat) : Expr2 := .scmp .gt (c32 N) (c32 4)
abbrev condLe4 (N : Nat) : Expr2 := .scmp .le (c32 N) (c32 4)

def sextSel (N W : Nat) (x1 x2 : String) (lo : Nat) : Expr2 :=
  .concat #[
    .repl W (.concat #[.ternary (condSel N) (.slice (.ident x1) (lo + W - 1) 1) (.slice (.ident x2) (lo + W - 1) 1)]),
    .ternary (condSel N) (.slice (.ident x1) lo W) (.slice (.ident x2) lo W)]

def sext2 (x : String) (lo pw : Nat) : Expr2 :=
  .concat #[.repl 2 (.concat #[.slice (.ident x) (lo + pw - 1) 1]), .slice (.ident x) lo pw]

def sextAcc (AccW : Nat) (x : String) (lo sw : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + sw - 1) 1]), .slice (.ident x) lo sw]

def pAp (W : Nat) : Process2 :=
  .assign (.ident "Ap") (.concat #[.repl (3 * W) (.concat #[.lit ⟨#[.l0]⟩]), .ident "A"])

def pBp (N W : Nat) : Process2 :=
  .assign (.ident "Bp") (.concat #[.repl (3 * N * W) (.concat #[.lit ⟨#[.l0]⟩]), .ident "B"])

def pCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.block #[.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "drain" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.ofBitVec 0#32)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "done" ⟨#[.l0]⟩, nb "k" (LVec.ofBitVec 4#32),
        .ifStmt (condLe4 N)
          (.block #[nb "busy" ⟨#[.l0]⟩, nb "drain" ⟨#[.l1]⟩])
          (some (.block #[nb "busy" ⟨#[.l1]⟩, nb "drain" ⟨#[.l0]⟩,
            .nbaAssign (.ident "a_sh") (.binary (.shr false) (.binary (.shr false) (.ident "Ap") (amtA W)) (amtA W)),
            .nbaAssign (.ident "b_sh") (.binary (.shr false) (.binary (.shr false) (.ident "Bp") (amtB N W)) (amtB N W))]))])
      (some (.ifStmt (.logical (SymBinOp.land == SymBinOp.land) (.ident "busy") (condGt4 N))
        (.block #[
          .nbaAssign (.ident "k") (.binary .add (.ident "k") (.lit (LVec.ofBitVec 4#32))),
          .nbaAssign (.ident "a_sh") (.binary (.shr false) (.binary (.shr false) (.ident "a_sh") (amtA W)) (amtA W)),
          .nbaAssign (.ident "b_sh") (.binary (.shr false) (.binary (.shr false) (.ident "b_sh") (amtB N W)) (amtB N W)),
          .ifStmt (.binary .ge (.binary .add (.ident "k") (.lit (LVec.ofBitVec 4#32))) (c32 N))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "drain" ⟨#[.l1]⟩]) none])
        (some (.ifStmt (.ident "drain")
          (.block #[nb "drain" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none))))))])

def pPm (N W m i j : Nat) (nm : String) : Process2 :=
  .assign (.slice nm ((i * N + j) * (2 * W)) (2 * W))
    (.binary .mul (sextSel N W "Ap" "a_sh" ((i * N + m) * W)) (sextSel N W "Bp" "b_sh" ((m * N + j) * W)))

def pX1 (N W i j : Nat) : Process2 :=
  let lo := (i * N + j) * (2 * W)
  .assign (.slice "x1" ((i * N + j) * (2 * W + 2)) (2 * W + 2))
    (.binary .xor (.binary .xor (sext2 "p0" lo (2 * W)) (sext2 "p1" lo (2 * W))) (sext2 "p2" lo (2 * W)))

def pY1 (N W i j : Nat) : Process2 :=
  let lo := (i * N + j) * (2 * W)
  let e0 := sext2 "p0" lo (2 * W)
  let e1 := sext2 "p1" lo (2 * W)
  let e2 := sext2 "p2" lo (2 * W)
  .assign (.slice "y1" ((i * N + j) * (2 * W + 2)) (2 * W + 2))
    (.binary (.shl false) (.binary .or (.binary .or (.binary .and e0 e1) (.binary .and e0 e2)) (.binary .and e1 e2)) (c32 1))

def pS2 (N W i j : Nat) : Process2 :=
  let loP := (i * N + j) * (2 * W)
  let loS := (i * N + j) * (2 * W + 2)
  .assign (.slice "s2" loS (2 * W + 2))
    (.binary .xor (.binary .xor (.slice (.ident "x1") loS (2 * W + 2)) (.slice (.ident "y1") loS (2 * W + 2)))
      (sext2 "p3" loP (2 * W)))

def pC2 (N W i j : Nat) : Process2 :=
  let loP := (i * N + j) * (2 * W)
  let loS := (i * N + j) * (2 * W + 2)
  let vx := .slice (.ident "x1") loS (2 * W + 2)
  let vy := .slice (.ident "y1") loS (2 * W + 2)
  let e3 := sext2 "p3" loP (2 * W)
  .assign (.slice "c2" loS (2 * W + 2))
    (.binary (.shl false) (.binary .or (.binary .or (.binary .and vx vy) (.binary .and vx e3)) (.binary .and vy e3)) (c32 1))

def pS4 (N W i j : Nat) : Process2 :=
  let loS := (i * N + j) * (2 * W + 2)
  .assign (.slice "s4" loS (2 * W + 2))
    (.binary .add (.slice (.ident "rs") loS (2 * W + 2)) (.slice (.ident "rc") loS (2 * W + 2)))

def pFF (N W AccW i j : Nat) : Process2 :=
  let loS := (i * N + j) * (2 * W + 2)
  let loC := (i * N + j) * AccW
  let sx := sextAcc AccW "s4" loS (2 * W + 2)
  let addC := .resize AccW (.binary .add (.resize (AccW + (2 * W + 2)) (.slice (.ident "C") loC AccW)) sx)
  .alwaysFF "clk" (.block #[
    .nbaAssign (.slice "rs" loS (2 * W + 2)) (.slice (.ident "s2") loS (2 * W + 2)),
    .nbaAssign (.slice "rc" loS (2 * W + 2)) (.slice (.ident "c2") loS (2 * W + 2)),
    .ifStmt (.logical (SymBinOp.land == SymBinOp.land) (.ident "start") (condGt4 N))
      (.nbaAssign (.slice "C" loC AccW) (.lit (LVec.ofBitVec 0#AccW)))
      (some (.ifStmt (.logical (SymBinOp.land == SymBinOp.land) (.ident "busy") (condGt4 N))
        (.nbaAssign (.slice "C" loC AccW) addC)
        (some (.ifStmt (.ident "drain")
          (.block #[.ifStmt (condLe4 N)
            (.nbaAssign (.slice "C" loC AccW) (.resize AccW sx))
            (some (.nbaAssign (.slice "C" loC AccW) addC))]) none))))])

def mmDecls (N W AccW : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true },
   { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true },
   { name := "A", width := N * N * W, isInput := true },
   { name := "B", width := N * N * W, isInput := true },
   { name := "done", width := 1, isOutput := true },
   { name := "C", width := N * N * AccW, isOutput := true },
   { name := "k", width := 32 },
   { name := "busy", width := 1 },
   { name := "drain", width := 1 },
   { name := "a_sh", width := (N * N + 3) * W },
   { name := "Ap", width := (N * N + 3) * W },
   { name := "b_sh", width := (N * N + 3 * N) * W },
   { name := "Bp", width := (N * N + 3 * N) * W },
   { name := "rs", width := N * N * (2 * W + 2) },
   { name := "rc", width := N * N * (2 * W + 2) },
   { name := "p0", width := N * N * (2 * W) },
   { name := "p1", width := N * N * (2 * W) },
   { name := "p2", width := N * N * (2 * W) },
   { name := "p3", width := N * N * (2 * W) },
   { name := "x1", width := N * N * (2 * W + 2) },
   { name := "y1", width := N * N * (2 * W + 2) },
   { name := "s2", width := N * N * (2 * W + 2) },
   { name := "c2", width := N * N * (2 * W + 2) },
   { name := "s4", width := N * N * (2 * W + 2) }]

def peProcs (N W AccW i j : Nat) : List Process2 :=
  [pPm N W 0 i j "p0", pPm N W 1 i j "p1", pPm N W 2 i j "p2", pPm N W 3 i j "p3",
   pX1 N W i j, pY1 N W i j, pS2 N W i j, pC2 N W i j, pS4 N W i j, pFF N W AccW i j]

def mmProcs (N W AccW : Nat) : List Process2 :=
  pAp W :: pBp N W :: pCtrl N W ::
    (List.range N).flatMap fun i => (List.range N).flatMap fun j => peProcs N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls N W AccW).toArray
  processes := (mmProcs N W AccW).toArray

private theorem toNat_natCast_eq (k : Nat) : ((k : Int)).toNat = k := Int.toNat_natCast k

theorem mmG_D (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) :
    mmG.D N W AccW = mmD N W AccW := by
  have hd1 : (((N * N : Nat) + 3 : Int) * W - 1).natAbs + 1 = (N * N + 3) * W := by
    rw [show (((N * N : Nat) + 3 : Int) * W) = (((N * N + 3) * W : Nat) : Int) by push_cast; rfl]
    exact natAbs_sub1 (Nat.mul_pos (by omega) (by omega))
  have hd2 : (((N * N : Nat) + 3 * (N : Int)) * W - 1).natAbs + 1 = (N * N + 3 * N) * W := by
    rw [show (((N * N : Nat) + 3 * (N : Int)) * W) = (((N * N + 3 * N) * W : Nat) : Int) by push_cast; rfl]
    exact natAbs_sub1 (Nat.mul_pos (by omega) (by omega))
  have hd3 : ((N * N : Nat) * (2 * (W : Int) + 2) - 1).natAbs + 1 = N * N * (2 * W + 2) := by
    rw [show ((N * N : Nat) * (2 * (W : Int) + 2)) = ((N * N * (2 * W + 2) : Nat) : Int) by push_cast; rfl]
    exact natAbs_sub1 (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
  have hd4 : ((N * N : Nat) * (2 * (W : Int)) - 1).natAbs + 1 = N * N * (2 * W) := by
    rw [show ((N * N : Nat) * (2 * (W : Int))) = ((N * N * (2 * W) : Nat) : Int) by push_cast; rfl]
    exact natAbs_sub1 (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
  have ht1 : (3 * (W : Int)).toNat = 3 * W := by
    rw [show (3 : Int) * W = ((3 * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have ht2 : (3 * (N : Int) * W).toNat = 3 * N * W := by
    rw [show (3 : Int) * N * W = ((3 * N * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have htw : (2 * (W : Int)).toNat = 2 * W := by
    rw [show (2 : Int) * W = ((2 * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hts : (2 * (W : Int) + 2).toNat = 2 * W + 2 := by
    rw [show (2 : Int) * W + 2 = ((2 * W + 2 : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hloP : ∀ i j : Nat, (((i : Int) * N + j) * (2 * W)).toNat = (i * N + j) * (2 * W) := fun i j => by
    rw [show (((i : Int) * N + j) * (2 * W)) = (((i * N + j) * (2 * W) : Nat) : Int) by push_cast; rfl]
    exact Int.toNat_natCast _
  have hloP1 : ∀ i j : Nat, (((i : Int) * N + j) * (2 * W) + 2 * W).toNat = (i * N + j) * (2 * W) + 2 * W := fun i j => by
    rw [show (((i : Int) * N + j) * (2 * W) + 2 * W) = (((i * N + j) * (2 * W) + 2 * W : Nat) : Int) by push_cast; rfl]
    exact Int.toNat_natCast _
  have hloS : ∀ i j : Nat, (((i : Int) * N + j) * (2 * W + 2)).toNat = (i * N + j) * (2 * W + 2) := fun i j => by
    rw [show (((i : Int) * N + j) * (2 * W + 2)) = (((i * N + j) * (2 * W + 2) : Nat) : Int) by push_cast; rfl]
    exact Int.toNat_natCast _
  have hloS1 : ∀ i j : Nat, (((i : Int) * N + j) * (2 * W + 2) + (2 * W + 2)).toNat = (i * N + j) * (2 * W + 2) + (2 * W + 2) := fun i j => by
    rw [show (((i : Int) * N + j) * (2 * W + 2) + (2 * W + 2)) = (((i * N + j) * (2 * W + 2) + (2 * W + 2) : Nat) : Int) by push_cast; rfl]
    exact Int.toNat_natCast _
  have ha2 : ∀ i : Nat, (((i : Int) * N + 2) * W).toNat = (i * N + 2) * W := fun i => by
    rw [show (((i : Int) * N + 2) * W) = (((i * N + 2) * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have ha21 : ∀ i : Nat, (((i : Int) * N + 2) * W + W).toNat = (i * N + 2) * W + W := fun i => by
    rw [show (((i : Int) * N + 2) * W + W) = (((i * N + 2) * W + W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have ha3 : ∀ i : Nat, (((i : Int) * N + 3) * W).toNat = (i * N + 3) * W := fun i => by
    rw [show (((i : Int) * N + 3) * W) = (((i * N + 3) * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have ha31 : ∀ i : Nat, (((i : Int) * N + 3) * W + W).toNat = (i * N + 3) * W + W := fun i => by
    rw [show (((i : Int) * N + 3) * W + W) = (((i * N + 3) * W + W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hb2 : ∀ j : Nat, ((2 * (N : Int) + j) * W).toNat = (2 * N + j) * W := fun j => by
    rw [show ((2 * (N : Int) + j) * W) = (((2 * N + j) * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hb21 : ∀ j : Nat, ((2 * (N : Int) + j) * W + W).toNat = (2 * N + j) * W + W := fun j => by
    rw [show ((2 * (N : Int) + j) * W + W) = (((2 * N + j) * W + W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hb3 : ∀ j : Nat, ((3 * (N : Int) + j) * W).toNat = (3 * N + j) * W := fun j => by
    rw [show ((3 * (N : Int) + j) * W) = (((3 * N + j) * W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hb31 : ∀ j : Nat, ((3 * (N : Int) + j) * W + W).toNat = (3 * N + j) * W + W := fun j => by
    rw [show ((3 * (N : Int) + j) * W + W) = (((3 * N + j) * W + W : Nat) : Int) by push_cast; rfl]; exact Int.toNat_natCast _
  have hg0 : mmG.g_col N W AccW = fun i j => pPm N W 0 i j "p0" := by
    funext i j; simp [mmG.g_col, pPm, sextSel, condSel, c32, hloP, htw]
  have hg1 : mmG.g_col_1 N W AccW = fun i j => pPm N W 1 i j "p1" := by
    funext i j; simp [mmG.g_col_1, pPm, sextSel, condSel, c32, hloP, htw]
  have hg2 : mmG.g_col_2 N W AccW = fun i j => pPm N W 2 i j "p2" := by
    funext i j; simp [mmG.g_col_2, pPm, sextSel, condSel, c32, hloP, htw, ha2, ha21, hb2, hb21]
  have hg3 : mmG.g_col_3 N W AccW = fun i j => pPm N W 3 i j "p3" := by
    funext i j; simp [mmG.g_col_3, pPm, sextSel, condSel, c32, hloP, htw, ha3, ha31, hb3, hb31]
  have hg4 : mmG.g_col_4 N W AccW = pX1 N W := by
    funext i j; simp [mmG.g_col_4, pX1, sext2, hloP, hloP1, hloS, htw, hts]
  have hg5 : mmG.g_col_5 N W AccW = pY1 N W := by
    funext i j; simp [mmG.g_col_5, pY1, sext2, c32, hloP, hloP1, hloS, htw, hts]
  have hg6 : mmG.g_col_6 N W AccW = pS2 N W := by
    funext i j; simp [mmG.g_col_6, pS2, sext2, hloP, hloP1, hloS, htw, hts]
  have hg7 : mmG.g_col_7 N W AccW = pC2 N W := by
    funext i j
    have h2w : 2 + 2 * W = 2 * W + 2 := by omega
    simp [mmG.g_col_7, pC2, sext2, c32, hloP, hloP1, hloS, htw, h2w]
  have hg8 : mmG.g_col_8 N W AccW = pS4 N W := by
    funext i j; simp [mmG.g_col_8, pS4, hloS, hts]
  have hg9 : mmG.g_col_9 N W AccW = pFF N W AccW := by
    funext i j; simp [mmG.g_col_9, pFF, sextAcc, condGt4, condLe4, c32, hloS, hloS1, hts]
  have hp0 : mmG.p0 N W AccW = pAp W := by simp [mmG.p0, pAp, ht1]
  have hp1 : mmG.p1 N W AccW = pBp N W := by simp [mmG.p1, pBp, ht2]
  have hp2 : mmG.p2 N W AccW = pCtrl N W := by simp [mmG.p2, pCtrl, nb, c32, amtA, amtB, condLe4, condGt4]
  simp only [mmG.D, mmD, mmG.decls, mmDecls, mmG.procs, mmProcs, peProcs,
    hd1, hd2, hd3, hd4, hp0, hp1, hp2, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9,
    List.cons_append, List.nil_append]

/-! ## Section 2: BitVec 4:2 CSA and exact signed arithmetic -/

private theorem xor_div2 (a b : Nat) : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_xor]

private theorem and_div2 (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_and]

private theorem or_div2 (a b : Nat) : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  simp [Nat.testBit_div_two, Nat.testBit_or]

private theorem xor_mod2 (a b : Nat) : (a ^^^ b) % 2 = (a % 2) ^^^ (b % 2) := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;> simp_all

private theorem and_mod2 (a b : Nat) : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
  have h := Nat.testBit_and a b 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a &&& b) % 2 = 0 ∨ (a &&& b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;> simp_all

private theorem or_mod2 (a b : Nat) : (a ||| b) % 2 = (a % 2) ||| (b % 2) := by
  have h := Nat.testBit_or a b 0
  simp only [Nat.testBit_zero] at h
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  have hab : (a ||| b) % 2 = 0 ∨ (a ||| b) % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hab with hab | hab <;> simp_all

theorem csa32_nat (a b c : Nat) :
    (a ^^^ b ^^^ c) + 2 * ((a &&& b) ||| (a &&& c) ||| (b &&& c)) = a + b + c := by
  induction a using Nat.strongRecOn generalizing b c with
  | ind a ih =>
    by_cases ha : a = 0
    · subst ha
      induction b using Nat.strongRecOn generalizing c with
      | ind b ihb =>
        by_cases hb : b = 0
        · subst hb; simp
        · have hb' : b / 2 < b := Nat.div_lt_self (by omega) (by omega)
          have hrec := ihb (b / 2) hb' (c / 2)
          have hxor : (b ^^^ c) = 2 * ((b / 2) ^^^ (c / 2)) + ((b % 2) ^^^ (c % 2)) := by
            have h1 := Nat.div_add_mod (b ^^^ c) 2
            rw [xor_div2, xor_mod2] at h1; omega
          have hand : (b &&& c) = 2 * ((b / 2) &&& (c / 2)) + ((b % 2) &&& (c % 2)) := by
            have h1 := Nat.div_add_mod (b &&& c) 2
            rw [and_div2, and_mod2] at h1; omega
          have h0 : ((b % 2) ^^^ (c % 2)) + 2 * ((b % 2) &&& (c % 2)) = b % 2 + c % 2 := by
            have : b % 2 = 0 ∨ b % 2 = 1 := by omega
            have : c % 2 = 0 ∨ c % 2 = 1 := by omega
            rcases ‹b % 2 = 0 ∨ b % 2 = 1› with h | h <;> rcases ‹c % 2 = 0 ∨ c % 2 = 1› with h' | h' <;> simp [h, h']
          have hb2 := Nat.div_add_mod b 2
          have hc2 := Nat.div_add_mod c 2
          simp only [Nat.zero_xor, Nat.zero_and, Nat.zero_or, Nat.zero_add] at hrec ⊢
          omega
    · have ha' : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have hrec := ih (a / 2) ha' (b / 2) (c / 2)
      have hxor : (a ^^^ b ^^^ c) = 2 * ((a / 2) ^^^ (b / 2) ^^^ (c / 2)) + ((a % 2) ^^^ (b % 2) ^^^ (c % 2)) := by
        have h1 := Nat.div_add_mod (a ^^^ b ^^^ c) 2
        rw [xor_div2, xor_div2, xor_mod2, xor_mod2] at h1; omega
      have hcar : ((a &&& b) ||| (a &&& c) ||| (b &&& c)) =
          2 * (((a / 2) &&& (b / 2)) ||| ((a / 2) &&& (c / 2)) ||| ((b / 2) &&& (c / 2))) +
          (((a % 2) &&& (b % 2)) ||| ((a % 2) &&& (c % 2)) ||| ((b % 2) &&& (c % 2))) := by
        have h1 := Nat.div_add_mod ((a &&& b) ||| (a &&& c) ||| (b &&& c)) 2
        rw [or_div2, or_div2, and_div2, and_div2, and_div2,
            or_mod2, or_mod2, and_mod2, and_mod2, and_mod2] at h1
        omega
      have h0 : ((a % 2) ^^^ (b % 2) ^^^ (c % 2)) +
          2 * (((a % 2) &&& (b % 2)) ||| ((a % 2) &&& (c % 2)) ||| ((b % 2) &&& (c % 2))) =
          a % 2 + b % 2 + c % 2 := by
        have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        have hc2 : c % 2 = 0 ∨ c % 2 = 1 := by omega
        rcases ha2 with h1 | h1 <;> rcases hb2 with h2 | h2 <;> rcases hc2 with h3 | h3 <;> simp [h1, h2, h3]
      have ha2 := Nat.div_add_mod a 2
      have hb2 := Nat.div_add_mod b 2
      have hc2 := Nat.div_add_mod c 2
      omega

theorem csa32_add {n : Nat} (a b c : BitVec n) :
    (a ^^^ b ^^^ c) + (((a &&& b) ||| (a &&& c) ||| (b &&& c)) <<< 1) = a + b + c := by
  apply BitVec.eq_of_toNat_eq
  have hshl : ∀ (x : BitVec n), (x <<< 1).toNat = (2 * x.toNat) % 2 ^ n := fun x => by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_xor, BitVec.toNat_xor,
    hshl, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_and,
    Nat.add_mod_mod, Nat.mod_add_mod, csa32_nat]

theorem csa42_add {n : Nat} (e0 e1 e2 e3 : BitVec n) :
    let x1 := e0 ^^^ e1 ^^^ e2
    let y1 := ((e0 &&& e1) ||| (e0 &&& e2) ||| (e1 &&& e2)) <<< 1
    let s2 := x1 ^^^ y1 ^^^ e3
    let c2 := ((x1 &&& y1) ||| (x1 &&& e3) ||| (y1 &&& e3)) <<< 1
    s2 + c2 = e0 + e1 + e2 + e3 := by
  intro x1 y1 s2 c2
  rw [csa32_add x1 y1 e3, csa32_add e0 e1 e2]

theorem setWidth_ofInt_le {w n : Nat} (h : n ≤ w) (z : Int) :
    (BitVec.ofInt w z).setWidth n = BitVec.ofInt n z := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have hdvd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ w : Nat) : Int) := by
    exact_mod_cast Nat.pow_dvd_pow 2 h
  have hnn1 : 0 ≤ z % (2 ^ w : Nat) := Int.emod_nonneg z (by exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos w))
  have hnn2 : 0 ≤ z % (2 ^ n : Nat) := Int.emod_nonneg z (by exact_mod_cast Nat.ne_of_gt (Nat.two_pow_pos n))
  apply Int.ofNat.inj
  simp only [Int.ofNat_eq_natCast]
  rw [Int.natCast_emod, Int.toNat_of_nonneg hnn1, Int.toNat_of_nonneg hnn2, Int.emod_emod_of_dvd z hdvd]

theorem signExtend_eq_ofInt_toInt {w n : Nat} (x : BitVec w) :
    x.signExtend n = BitVec.ofInt n x.toInt := by
  by_cases h : w ≤ n
  · rw [← BitVec.ofInt_toInt (x := x.signExtend n), BitVec.toInt_signExtend_of_le h]
  · rw [BitVec.signExtend_eq_setWidth_of_le _ (by omega)]
    conv => lhs; rw [← BitVec.ofInt_toInt (x := x)]
    exact setWidth_ofInt_le (by omega) _

theorem int_bmod_eq_self {x : Int} {m : Nat} (h1 : -((m / 2 : Nat) : Int) ≤ x) (h2 : x < (((m + 1) / 2 : Nat) : Int)) :
    x.bmod m = x := by
  unfold Int.bmod
  have hm : (m : Int) > 0 := by omega
  have hmod : x % (m : Int) = if 0 ≤ x then x else x + m := by
    split
    · exact Int.emod_eq_of_lt (by omega) (by omega)
    · have h0 : 0 ≤ x + m := by omega
      have hlt : x + m < m := by omega
      rw [← Int.add_emod_right, Int.emod_eq_of_lt h0 hlt]
  rw [hmod]
  split <;> dsimp only <;> split <;> omega

theorem mul_toInt_bounds {W : Nat} (hW : 1 ≤ W) (a b : BitVec W) :
    -(2 ^ (2 * W - 2) : Int) ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ 2 ^ (2 * W - 2) := by
  have ha1 : -(2 ^ (W - 1) : Int) ≤ a.toInt := BitVec.le_toInt a
  have ha2 : a.toInt < (2 ^ (W - 1) : Int) := BitVec.toInt_lt
  have hb1 : -(2 ^ (W - 1) : Int) ≤ b.toInt := BitVec.le_toInt b
  have hb2 : b.toInt < (2 ^ (W - 1) : Int) := BitVec.toInt_lt
  have hp1 : ((2 ^ (W - 1) : Nat) : Int) = (2 : Int) ^ (W - 1) := by push_cast; rfl
  have hp2 : ((2 ^ (2 * W - 2) : Nat) : Int) = (2 : Int) ^ (2 * W - 2) := by push_cast; rfl
  have hna : a.toInt.natAbs ≤ 2 ^ (W - 1) := by omega
  have hnb : b.toInt.natAbs ≤ 2 ^ (W - 1) := by omega
  have hnab : (a.toInt * b.toInt).natAbs ≤ 2 ^ (2 * W - 2) := by
    rw [Int.natAbs_mul]
    calc a.toInt.natAbs * b.toInt.natAbs
        ≤ 2 ^ (W - 1) * 2 ^ (W - 1) := Nat.mul_le_mul hna hnb
      _ = 2 ^ (2 * W - 2) := by rw [← Nat.pow_add]; congr 1; omega
  omega

theorem toInt_mul_signExtend_2W {W : Nat} (hW : 1 ≤ W) (a b : BitVec W) :
    (a.signExtend (2 * W) * b.signExtend (2 * W)).toInt = a.toInt * b.toInt := by
  have hmb := mul_toInt_bounds hW a b
  have hpow2 : (2 ^ (2 * W - 1) : Int) = 2 * 2 ^ (2 * W - 2) := by
    rw [show 2 * W - 1 = (2 * W - 2) + 1 by omega, Int.pow_succ]; omega
  have hpos : (1 : Int) ≤ 2 ^ (2 * W - 2) := by exact_mod_cast Nat.one_le_two_pow
  have hm : a.signExtend (2 * W) * b.signExtend (2 * W) = BitVec.ofInt (2 * W) (a.toInt * b.toInt) := by
    rw [signExtend_eq_ofInt_toInt, signExtend_eq_ofInt_toInt, ← BitVec.ofInt_mul]
  have h2w : 2 ^ (2 * W) = 2 * 2 ^ (2 * W - 1) := by
    have h1 : 2 * W = (2 * W - 1) + 1 := by omega
    conv => lhs; rw [h1]
    rw [Nat.pow_succ]; omega
  have hd : 2 ^ (2 * W) / 2 = 2 ^ (2 * W - 1) := by omega
  have hd2 : (2 ^ (2 * W) + 1) / 2 = 2 ^ (2 * W - 1) := by omega
  have hpc : ((2 ^ (2 * W - 1) : Nat) : Int) = (2 : Int) ^ (2 * W - 1) := by push_cast; rfl
  rw [hm, BitVec.toInt_ofInt, int_bmod_eq_self]
  · rw [hd, hpc]; omega
  · rw [hd2, hpc]; omega

theorem toInt_ofInt_sum4 {W : Nat} (hW : 1 ≤ W) (a0 b0 a1 b1 a2 b2 a3 b3 : BitVec W) :
    (BitVec.ofInt (2 * W + 2)
      (a0.toInt * b0.toInt + a1.toInt * b1.toInt + a2.toInt * b2.toInt + a3.toInt * b3.toInt)).toInt =
      a0.toInt * b0.toInt + a1.toInt * b1.toInt + a2.toInt * b2.toInt + a3.toInt * b3.toInt := by
  have h0 := mul_toInt_bounds hW a0 b0
  have h1 := mul_toInt_bounds hW a1 b1
  have h2 := mul_toInt_bounds hW a2 b2
  have h3 := mul_toInt_bounds hW a3 b3
  have hpos : (1 : Int) ≤ 2 ^ (2 * W - 2) := by exact_mod_cast Nat.one_le_two_pow
  have hpow : (2 ^ (2 * W + 1) : Int) = 8 * 2 ^ (2 * W - 2) := by
    rw [show 2 * W + 1 = (2 * W - 2) + 3 by omega, Int.pow_add]
    have h8 : (2 : Int) ^ 3 = 8 := by decide
    rw [h8]; omega
  have hd : 2 ^ (2 * W + 2) / 2 = 2 ^ (2 * W + 1) := by
    rw [show 2 * W + 2 = (2 * W + 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
  have hd2 : (2 ^ (2 * W + 2) + 1) / 2 = 2 ^ (2 * W + 1) := by
    rw [show 2 * W + 2 = (2 * W + 1) + 1 by omega, Nat.pow_succ]; omega
  have hpc : ((2 ^ (2 * W + 1) : Nat) : Int) = (2 : Int) ^ (2 * W + 1) := by push_cast; rfl
  rw [BitVec.toInt_ofInt, int_bmod_eq_self]
  · rw [hd, hpc]; omega
  · rw [hd2, hpc]; omega

theorem signExtend_add4_exact {W : Nat} (hW : 1 ≤ W) (a0 b0 a1 b1 a2 b2 a3 b3 : BitVec W) :
    (a0.signExtend (2 * W) * b0.signExtend (2 * W)).signExtend (2 * W + 2) +
    (a1.signExtend (2 * W) * b1.signExtend (2 * W)).signExtend (2 * W + 2) +
    (a2.signExtend (2 * W) * b2.signExtend (2 * W)).signExtend (2 * W + 2) +
    (a3.signExtend (2 * W) * b3.signExtend (2 * W)).signExtend (2 * W + 2) =
    BitVec.ofInt (2 * W + 2)
      (a0.toInt * b0.toInt + a1.toInt * b1.toInt + a2.toInt * b2.toInt + a3.toInt * b3.toInt) := by
  have hse : ∀ x y : BitVec W,
      (x.signExtend (2 * W) * y.signExtend (2 * W)).signExtend (2 * W + 2) =
        BitVec.ofInt (2 * W + 2) (x.toInt * y.toInt) := fun x y => by
    rw [signExtend_eq_ofInt_toInt, toInt_mul_signExtend_2W hW]
  rw [hse, hse, hse, hse, ← BitVec.ofInt_add, ← BitVec.ofInt_add, ← BitVec.ofInt_add]

theorem setWidth_signExtend_add_sw {AccW sw : Nat} (x : BitVec sw) :
    (x.signExtend (AccW + sw)).setWidth AccW = BitVec.ofInt AccW x.toInt := by
  rw [Lib.setWidth_signExtend_of_le _ (Nat.le_add_right AccW sw), signExtend_eq_ofInt_toInt]

theorem setWidth_add_signExtend_sw {AccW sw : Nat} (c : BitVec AccW) (x : BitVec sw) :
    (c.setWidth (AccW + sw) + x.signExtend (AccW + sw)).setWidth AccW =
      c + BitVec.ofInt AccW x.toInt := by
  rw [BitVec.setWidth_add _ _ (Nat.le_add_right AccW sw),
    BitVec.setWidth_setWidth_of_le _ (Nat.le_add_right AccW sw), BitVec.setWidth_eq,
    setWidth_signExtend_add_sw]

/-! ## Section 1b: Disjointness (`WinDisj`), `driversOk`, and `mm_sem_eq` -/

theorem pe_proc_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ p ∈ peProcs N W AccW i j, ∀ q ∈ peProcs N W AccW i' j', SvGolf.Cycle.WinDisj p q := by
  have hP := rowMajor_le (K := 2 * W) h
  have hS := rowMajor_le (K := 2 * W + 2) h
  have hC := rowMajor_le (K := AccW) h
  intro p hp q hq
  simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine SvGolf.Cycle.WinDisj.of_all (by
      simp [SvGolf.Cycle.allWins, pPm, pX1, pY1, pS2, pC2, pS4, pFF,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)

theorem peProcs_pairwise (N W AccW i j : Nat) :
    (peProcs N W AccW i j).Pairwise SvGolf.Cycle.WinDisj := by
  simp only [peProcs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.Pairwise.nil, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ h => False.elim h⟩
  all_goals intro q hq
  all_goals first
    | (rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl | rfl)
    | (rcases hq with rfl | rfl | rfl)
    | (rcases hq with rfl | rfl)
    | (subst hq)
  all_goals exact SvGolf.Cycle.WinDisj.of_all (by
    simp [SvGolf.Cycle.allWins, pPm, pX1, pY1, pS2, pC2, pS4, pFF,
      Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins, DrvWin.overlaps])

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ mmProcs N W AccW) :
    p = pAp W ∨ p = pBp N W ∨ p = pCtrl N W ∨
      ∃ i j, i < N ∧ j < N ∧ p ∈ peProcs N W AccW i j := by
  simp only [mmProcs, List.mem_cons, List.mem_flatMap, List.mem_range] at hp
  rcases hp with rfl | rfl | rfl | ⟨i, hi, j, hj, hp⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr ⟨i, j, hi, hj, hp⟩))

theorem mm_winDisj (N W AccW : Nat) : (mmProcs N W AccW).Pairwise SvGolf.Cycle.WinDisj := by
  simp only [mmProcs, List.pairwise_cons]
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_flatMap, List.mem_range] at hq
    rcases hq with rfl | rfl | ⟨i, -, j, -, hq⟩
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pAp, pBp, Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pAp, pCtrl, nb, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pAp, pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_cons, List.mem_flatMap, List.mem_range] at hq
    rcases hq with rfl | ⟨i, -, j, -, hq⟩
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pBp, pCtrl, nb, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pBp, pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_flatMap, List.mem_range] at hq
    obtain ⟨i, -, j, -, hq⟩ := hq
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, pCtrl, nb, pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · refine pairwise_flatMap_range (fun i _ => ?_) ?_
    · refine pairwise_flatMap_range (fun j _ => peProcs_pairwise N W AccW i j) ?_
      intro j j' hj _ p hp q hq
      exact pe_proc_disj (by omega) p hp q hq
    · intro i i' hi _ p hp q hq
      obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨j', -, hq⟩ := List.mem_flatMap.mp hq
      have hrow := rowMajor_le (K := N) hi
      have hjN := List.mem_range.mp hj
      exact pe_proc_disj (by omega) p hp q hq

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mmProcs N W AccW) = true := by
  refine SvGolf.Cycle.driversOk_of_winDisj (mm_winDisj N W AccW) ?_ ?_
  · rw [List.all_eq_true]; intro p hp
    rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · simp [pAp, Process2.drvWins, Lhs2.drvWins, drvWinsDisjoint]
    · simp [pBp, Process2.drvWins, Lhs2.drvWins, drvWinsDisjoint]
    · simp [pCtrl, Process2.drvWins, drvWinsDisjoint]
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.drvWins, Lhs2.drvWins, drvWinsDisjoint]
  · rw [List.all_eq_true]; intro p hp
    rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · simp [SvGolf.Cycle.allWins, pAp, Process2.drvWins, Process2.procWins, Lhs2.drvWins, design.pdesign, PDesign.inputNames]
    · simp [SvGolf.Cycle.allWins, pBp, Process2.drvWins, Process2.procWins, Lhs2.drvWins, design.pdesign, PDesign.inputNames]
    · simp [SvGolf.Cycle.allWins, pCtrl, nb, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign, PDesign.inputNames]
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [SvGolf.Cycle.allWins, pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign, PDesign.inputNames]

theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    design.sem N W AccW = mmD N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror
    (mmG.instantiate N W AccW hN hN256 hW hW127 hA hA64)
    (mmG_D N W AccW hN hW)
    (by simpa [mmD] using mm_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by
      rw [List.all_eq_true]; intro p hp
      have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
      rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
      · rfl
      · rfl
      · rfl
      · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl))

/-! ## Section 3: State, comb settle (4-layer DAG), edge execution, and `mm_cycle` -/

structure MIns where
  ck : LVec
  r : LVec
  s : LVec
  a : LVec
  b : LVec
deriving DecidableEq

structure MRegs where
  dn : LVec
  c : LVec
  k : LVec
  bz : LVec
  dr : LVec
  ash : LVec
  bsh : LVec
  rs : LVec
  rc : LVec
deriving DecidableEq

structure MWires where
  ap : LVec
  bp : LVec
  p0 : LVec
  p1 : LVec
  p2 : LVec
  p3 : LVec
  x1 : LVec
  y1 : LVec
  s2 : LVec
  c2 : LVec
  s4 : LVec
deriving DecidableEq

def MS (ins : MIns) (reg : MRegs) (w : MWires) : SvState :=
  [("clk", ins.ck), ("rst", ins.r), ("start", ins.s), ("A", ins.a), ("B", ins.b),
   ("done", reg.dn), ("C", reg.c), ("k", reg.k), ("busy", reg.bz), ("drain", reg.dr),
   ("a_sh", reg.ash), ("Ap", w.ap), ("b_sh", reg.bsh), ("Bp", w.bp),
   ("rs", reg.rs), ("rc", reg.rc),
   ("p0", w.p0), ("p1", w.p1), ("p2", w.p2), ("p3", w.p3),
   ("x1", w.x1), ("y1", w.y1), ("s2", w.s2), ("c2", w.c2), ("s4", w.s4)]

theorem MS_inj {ins ins' : MIns} {reg reg' : MRegs} {w w' : MWires}
    (h : MS ins reg w = MS ins' reg' w') : ins = ins' ∧ reg = reg' ∧ w = w' := by
  cases ins; cases ins'; cases reg; cases reg'; cases w; cases w'
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

def WdRegs (N W AccW : Nat) (reg : MRegs) : Prop :=
  reg.dn.width = 1 ∧ reg.c.width = N * N * AccW ∧ reg.k.width = 32 ∧
  reg.bz.width = 1 ∧ reg.dr.width = 1 ∧
  reg.ash.width = (N * N + 3) * W ∧ reg.bsh.width = (N * N + 3 * N) * W ∧
  reg.rs.width = N * N * (2 * W + 2) ∧ reg.rc.width = N * N * (2 * W + 2)

def WdWires (N W : Nat) (w : MWires) : Prop :=
  w.ap.width = (N * N + 3) * W ∧ w.bp.width = (N * N + 3 * N) * W ∧
  w.p0.width = N * N * (2 * W) ∧ w.p1.width = N * N * (2 * W) ∧
  w.p2.width = N * N * (2 * W) ∧ w.p3.width = N * N * (2 * W) ∧
  w.x1.width = N * N * (2 * W + 2) ∧ w.y1.width = N * N * (2 * W + 2) ∧
  w.s2.width = N * N * (2 * W + 2) ∧ w.c2.width = N * N * (2 * W + 2) ∧
  w.s4.width = N * N * (2 * W + 2)

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ins reg w, st = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w

def appIns (e : SvState) (ins : MIns) : MIns :=
  ⟨appIn e "clk" ins.ck, appIn e "rst" ins.r, appIn e "start" ins.s,
   appIn e "A" ins.a, appIn e "B" ins.b⟩

theorem apply_mm (N W AccW : Nat) (e : SvState) (ins : MIns) (reg : MRegs) (w : MWires) :
    applyInputs2 (mmD N W AccW) e (MS ins reg w) = MS (appIns e ins) reg w := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIns, appIn, h1, h2, h3, h4, h5, SvState.set]

/-! ### Row-major grid helpers -/

theorem rm_lt {N i j : Nat} (hi : i < N) (hj : j < N) : i * N + j < N * N := by
  have := Nat.mul_le_mul_right N (show i + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem rm_inj {N i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : i * N + j = i' * N + j') :
    i = i' ∧ j = j' := by
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · have := rowMajor_le (K := N) hlt; omega
  · omega
  · have := rowMajor_le (K := N) hlt; omega

theorem rm_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem rm_mod {N i j : Nat} (hj : j < N) : (i * N + j) % N = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

theorem step_extract {E n r0 r : Nat} {x p g : LVec} (hx : x.width = n * E) (hp : p.width = E)
    (hr0 : r0 < n) (h : (r0 = r ∧ p = g) ∨ (r0 ≠ r ∧ x.extract (r * E) E = g)) :
    (x.insertAt (r0 * E) p).extract (r * E) E = g := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hne, hx'⟩
  · have := rowMajor_le (K := E) hr0
    exact LVec.extract_insertAt_self hp (by omega)
  · rw [LVec.extract_insertAt_of_disjoint]
    · exact hx'
    · rw [hp]
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact .inr (rowMajor_le h)
      · exact .inl (rowMajor_le h)

theorem eq_of_chunks {E n : Nat} {u v : LVec} (hu : u.width = n * E) (hv : v.width = n * E)
    (h : ∀ r, r < n → u.extract (r * E) E = v.extract (r * E) E) : u = v := by
  refine LVec.eq_of_extract_one (hu.trans hv.symm) fun i hi => ?_
  rw [hu] at hi
  have hE : 0 < E := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hi
  have hr : i / E < n := (Nat.div_lt_iff_lt_mul hE).mpr hi
  have hd : i / E * E + i % E = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i E
  have hm : i % E + 1 ≤ E := Nat.mod_lt i hE
  have h1 := congrArg (fun x : LVec => x.extract (i % E) 1) (h _ hr)
  simp only [LVec.extract_extract _ hm, hd] at h1
  exact h1

def packGrid (E N : Nat) (f : Nat → Nat → LVec) : LVec :=
  LVec.insertEntries E (fun r => f (r / N) (r % N)) (N * N) (LVec.xVec (N * N * E))

@[simp] theorem width_packGrid (E N : Nat) (f : Nat → Nat → LVec) :
    (packGrid E N f).width = N * N * E := by simp [packGrid]

theorem packGrid_extract {E N i j : Nat} {f : Nat → Nat → LVec}
    (hf : ∀ a b, (f a b).width = E) (hi : i < N) (hj : j < N) :
    (packGrid E N f).extract ((i * N + j) * E) E = f i j := by
  have h := LVec.extract_insertEntries (E := E) (g := fun r => f (r / N) (r % N))
    (fun _ => hf _ _) (LVec.xVec (N * N * E)) (N * N) (by simp) (i * N + j) (rm_lt hi hj)
  simpa [packGrid, rm_div hj, rm_mod hj] using h

theorem eq_packGrid {E N : Nat} (hN : 1 ≤ N) {f : Nat → Nat → LVec}
    (hf : ∀ a b, (f a b).width = E) {v : LVec} (hv : v.width = N * N * E)
    (h : ∀ i j, i < N → j < N → v.extract ((i * N + j) * E) E = f i j) :
    v = packGrid E N f := by
  refine eq_of_chunks hv (width_packGrid ..) fun r hr => ?_
  have hi : r / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have hj : r % N < N := Nat.mod_lt _ (by omega)
  have hr' : r / N * N + r % N = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r N
  have h1 := h _ _ hi hj
  have h2 := packGrid_extract hf hi hj
  rw [hr'] at h1 h2
  rw [h1, h2]

theorem insertAt_packGrid_self {E N i0 j0 : Nat} (hN : 1 ≤ N) {f : Nat → Nat → LVec}
    (hf : ∀ a b, (f a b).width = E) (hi0 : i0 < N) (hj0 : j0 < N) :
    (packGrid E N f).insertAt ((i0 * N + j0) * E) (f i0 j0) = packGrid E N f := by
  refine eq_packGrid hN hf (by simp) fun i j hi hj => ?_
  by_cases heq : i0 * N + j0 = i * N + j
  · obtain ⟨rfl, rfl⟩ := rm_inj hj0 hj heq
    exact step_extract (width_packGrid ..) (hf _ _) (rm_lt hi0 hj0) (.inl ⟨rfl, rfl⟩)
  · exact step_extract (width_packGrid ..) (hf _ _) (rm_lt hi0 hj0) (.inr ⟨heq, packGrid_extract hf hi hj⟩)

/-! ### Evaluated combinational functions -/

def scmpLe4 (N : Nat) : LVec := SvGolf.Cycle.scmpVal .le (LVec.ofInt 32 N) (LVec.ofInt 32 4)
def scmpGt4 (N : Nat) : LVec := SvGolf.Cycle.scmpVal .gt (LVec.ofInt 32 N) (LVec.ofInt 32 4)

def lorL (a b : LVec) : LVec :=
  LVec.ofLogic (if (a.condTrue || b.condTrue) = true then .l1
    else if (a.isKnownZero && b.isKnownZero) = true then .l0 else .lx)

def landL (a b : LVec) : LVec :=
  LVec.ofLogic (if (a.isKnownZero || b.isKnownZero) = true then .l0
    else if (a.condTrue && b.condTrue) = true then .l1 else .lx)

def apV (N W : Nat) (a : LVec) : LVec :=
  (LVec.concatMany #[LVec.replVec (3 * W) (LVec.concatMany #[⟨#[.l0]⟩]), a]).resizeU ((N * N + 3) * W)

def bpV (N W : Nat) (b : LVec) : LVec :=
  (LVec.concatMany #[LVec.replVec (3 * N * W) (LVec.concatMany #[⟨#[.l0]⟩]), b]).resizeU ((N * N + 3 * N) * W)

def sextSelV (N W : Nat) (s x1 x2 : LVec) (lo : Nat) : LVec :=
  let c := lorL s (scmpLe4 N)
  LVec.concatMany #[
    LVec.replVec W (LVec.concatMany #[LVec.ternary c (x1.extract (lo + W - 1) 1) (x2.extract (lo + W - 1) 1)]),
    LVec.ternary c (x1.extract lo W) (x2.extract lo W)]

def pmV (N W m i j : Nat) (s ap bp ash bsh : LVec) : LVec :=
  ((sextSelV N W s ap ash ((i * N + m) * W)).mul (sextSelV N W s bp bsh ((m * N + j) * W))).resizeU (2 * W)

def sext2V (v : LVec) (lo pw : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec 2 (LVec.concatMany #[v.extract (lo + pw - 1) 1]), v.extract lo pw]

def x1V (N W i j : Nat) (p0 p1 p2 : LVec) : LVec :=
  let lo := (i * N + j) * (2 * W)
  (((sext2V p0 lo (2 * W)).xor (sext2V p1 lo (2 * W))).xor (sext2V p2 lo (2 * W))).resizeU (2 * W + 2)

def y1V (N W i j : Nat) (p0 p1 p2 : LVec) : LVec :=
  let lo := (i * N + j) * (2 * W)
  let e0 := sext2V p0 lo (2 * W)
  let e1 := sext2V p1 lo (2 * W)
  let e2 := sext2V p2 lo (2 * W)
  ((((e0.and e1).or (e0.and e2)).or (e1.and e2)).shl (LVec.ofInt 32 1)).resizeU (2 * W + 2)

def s2V (N W i j : Nat) (x1 y1 p3 : LVec) : LVec :=
  let loP := (i * N + j) * (2 * W)
  let loS := (i * N + j) * (2 * W + 2)
  (((x1.extract loS (2 * W + 2)).xor (y1.extract loS (2 * W + 2))).xor (sext2V p3 loP (2 * W))).resizeU (2 * W + 2)

def c2V (N W i j : Nat) (x1 y1 p3 : LVec) : LVec :=
  let loP := (i * N + j) * (2 * W)
  let loS := (i * N + j) * (2 * W + 2)
  let vx := x1.extract loS (2 * W + 2)
  let vy := y1.extract loS (2 * W + 2)
  let e3 := sext2V p3 loP (2 * W)
  ((((vx.and vy).or (vx.and e3)).or (vy.and e3)).shl (LVec.ofInt 32 1)).resizeU (2 * W + 2)

def s4V (N W i j : Nat) (rs rc : LVec) : LVec :=
  let loS := (i * N + j) * (2 * W + 2)
  ((rs.extract loS (2 * W + 2)).add (rc.extract loS (2 * W + 2))).resizeU (2 * W + 2)

@[simp] theorem width_apV (N W : Nat) (a : LVec) : (apV N W a).width = (N * N + 3) * W := by simp [apV]
@[simp] theorem width_bpV (N W : Nat) (b : LVec) : (bpV N W b).width = (N * N + 3 * N) * W := by simp [bpV]
@[simp] theorem width_pmV (N W m i j : Nat) (s ap bp ash bsh : LVec) : (pmV N W m i j s ap bp ash bsh).width = 2 * W := by simp [pmV]
@[simp] theorem width_x1V (N W i j : Nat) (p0 p1 p2 : LVec) : (x1V N W i j p0 p1 p2).width = 2 * W + 2 := by simp [x1V]
@[simp] theorem width_y1V (N W i j : Nat) (p0 p1 p2 : LVec) : (y1V N W i j p0 p1 p2).width = 2 * W + 2 := by simp [y1V]
@[simp] theorem width_s2V (N W i j : Nat) (x1 y1 p3 : LVec) : (s2V N W i j x1 y1 p3).width = 2 * W + 2 := by simp [s2V]
@[simp] theorem width_c2V (N W i j : Nat) (x1 y1 p3 : LVec) : (c2V N W i j x1 y1 p3).width = 2 * W + 2 := by simp [c2V]
@[simp] theorem width_s4V (N W i j : Nat) (rs rc : LVec) : (s4V N W i j rs rc).width = 2 * W + 2 := by simp [s4V]

/-- The unique settled wires for `(ins, reg)`. -/
def wSet (N W : Nat) (ins : MIns) (reg : MRegs) : MWires :=
  let ap := apV N W ins.a
  let bp := bpV N W ins.b
  let s4 := packGrid (2 * W + 2) N (fun i j => s4V N W i j reg.rs reg.rc)
  let p0 := packGrid (2 * W) N (fun i j => pmV N W 0 i j ins.s ap bp reg.ash reg.bsh)
  let p1 := packGrid (2 * W) N (fun i j => pmV N W 1 i j ins.s ap bp reg.ash reg.bsh)
  let p2 := packGrid (2 * W) N (fun i j => pmV N W 2 i j ins.s ap bp reg.ash reg.bsh)
  let p3 := packGrid (2 * W) N (fun i j => pmV N W 3 i j ins.s ap bp reg.ash reg.bsh)
  let x1 := packGrid (2 * W + 2) N (fun i j => x1V N W i j p0 p1 p2)
  let y1 := packGrid (2 * W + 2) N (fun i j => y1V N W i j p0 p1 p2)
  let s2 := packGrid (2 * W + 2) N (fun i j => s2V N W i j x1 y1 p3)
  let c2 := packGrid (2 * W + 2) N (fun i j => c2V N W i j x1 y1 p3)
  ⟨ap, bp, p0, p1, p2, p3, x1, y1, s2, c2, s4⟩

theorem wdWires_wSet (N W : Nat) (ins : MIns) (reg : MRegs) : WdWires N W (wSet N W ins reg) := by
  simp [WdWires, wSet]

/-! ### Single combinational process evaluation lemmas -/

theorem pAp_comb (N W F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires)
    (hw : w.ap.width = (N * N + 3) * W) :
    runCombProcess2 F (MS ins reg w) (pAp W) = .ok (MS ins reg { w with ap := apV N W ins.a }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pAp, apV, runCombProcess2, evalExpr2, evalExprs2, readSignal, resolveLhs2, MS,
    SvState.lookup, SvState.set, hw, LVec.insertAt_zero_of_width_eq]

theorem pBp_comb (N W F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires)
    (hw : w.bp.width = (N * N + 3 * N) * W) :
    runCombProcess2 F (MS ins reg w) (pBp N W) = .ok (MS ins reg { w with bp := bpV N W ins.b }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pBp, bpV, runCombProcess2, evalExpr2, evalExprs2, readSignal, resolveLhs2, MS,
    SvState.lookup, SvState.set, hw, LVec.insertAt_zero_of_width_eq]

theorem pCtrl_comb (N W F : Nat) (st : SvState) :
    runCombProcess2 F st (pCtrl N W) = .ok st := by cases F <;> rfl

theorem pFF_comb (N W AccW i j F : Nat) (st : SvState) :
    runCombProcess2 F st (pFF N W AccW i j) = .ok st := by cases F <;> rfl

theorem toInt?_ofBitVec {w : Nat} (x : BitVec w) :
    (LVec.ofBitVec x).toInt? = some x.toInt := by
  rw [LVec.toInt?, LVec.toNat?_ofBitVec, LVec.width_ofBitVec]
  cases w with
  | zero =>
    have hx0 : x.toNat = 0 := by have := x.isLt; omega
    simp [BitVec.toInt, hx0]
  | succ w' =>
    simp only [Nat.add_sub_cancel, beq_iff_eq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    rw [BitVec.toInt_eq_toNat_cond]
    have hpow : 2 ^ (w' + 1) = 2 * 2 ^ w' := by rw [Nat.pow_succ]; omega
    by_cases h : x.toNat < 2 ^ w'
    · simp [h, show 2 * x.toNat < 2 ^ (w' + 1) by omega]
    · simp [h, show ¬ (2 * x.toNat < 2 ^ (w' + 1)) by omega]

theorem toInt?_ofInt (w : Nat) (z : Int) :
    (LVec.ofInt w z).toInt? = some (BitVec.ofInt w z).toInt := by
  rw [LVec.ofInt_eq_ofBitVec, toInt?_ofBitVec]

theorem scmpLe4_eq (N : Nat) :
    scmpLe4 N = LVec.ofLogic (if (BitVec.ofInt 32 (N : Int)).toInt ≤ (BitVec.ofInt 32 4).toInt then .l1 else .l0) := by
  simp [scmpLe4, SvGolf.Cycle.scmpVal, toInt?_ofInt]

theorem scmpGt4_eq (N : Nat) :
    scmpGt4 N = LVec.ofLogic (if (BitVec.ofInt 32 (N : Int)).toInt > (BitVec.ofInt 32 4).toInt then .l1 else .l0) := by
  simp [scmpGt4, SvGolf.Cycle.scmpVal, toInt?_ofInt]

theorem pP0_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pPm N W 0 i j "p0") =
      .ok (MS ins reg { w with p0 := w.p0.insertAt ((i * N + j) * (2 * W)) (pmV N W 0 i j ins.s w.ap w.bp reg.ash reg.bsh) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hlor : (SymBinOp.lor == SymBinOp.land) = false := by decide
  simp [pPm, sextSel, condSel, pmV, sextSelV, hlor, runCombProcess2, evalExpr2, evalExprs2,
    toInt?_ofInt, scmpLe4_eq, evalBinOp, c32, readSignal, resolveLhs2, MS, SvState.lookup,
    SvState.set, lorL]

theorem pP1_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pPm N W 1 i j "p1") =
      .ok (MS ins reg { w with p1 := w.p1.insertAt ((i * N + j) * (2 * W)) (pmV N W 1 i j ins.s w.ap w.bp reg.ash reg.bsh) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hlor : (SymBinOp.lor == SymBinOp.land) = false := by decide
  simp [pPm, sextSel, condSel, pmV, sextSelV, hlor, runCombProcess2, evalExpr2, evalExprs2,
    toInt?_ofInt, scmpLe4_eq, evalBinOp, c32, readSignal, resolveLhs2, MS, SvState.lookup,
    SvState.set, lorL]

theorem pP2_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pPm N W 2 i j "p2") =
      .ok (MS ins reg { w with p2 := w.p2.insertAt ((i * N + j) * (2 * W)) (pmV N W 2 i j ins.s w.ap w.bp reg.ash reg.bsh) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hlor : (SymBinOp.lor == SymBinOp.land) = false := by decide
  simp [pPm, sextSel, condSel, pmV, sextSelV, hlor, runCombProcess2, evalExpr2, evalExprs2,
    toInt?_ofInt, scmpLe4_eq, evalBinOp, c32, readSignal, resolveLhs2, MS, SvState.lookup,
    SvState.set, lorL]

theorem pP3_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pPm N W 3 i j "p3") =
      .ok (MS ins reg { w with p3 := w.p3.insertAt ((i * N + j) * (2 * W)) (pmV N W 3 i j ins.s w.ap w.bp reg.ash reg.bsh) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hlor : (SymBinOp.lor == SymBinOp.land) = false := by decide
  simp [pPm, sextSel, condSel, pmV, sextSelV, hlor, runCombProcess2, evalExpr2, evalExprs2,
    toInt?_ofInt, scmpLe4_eq, evalBinOp, c32, readSignal, resolveLhs2, MS, SvState.lookup,
    SvState.set, lorL]

theorem pX1_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pX1 N W i j) =
      .ok (MS ins reg { w with x1 := w.x1.insertAt ((i * N + j) * (2 * W + 2)) (x1V N W i j w.p0 w.p1 w.p2) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pX1, sext2, x1V, sext2V, runCombProcess2, evalExpr2, evalExprs2, evalBinOp,
    readSignal, resolveLhs2, MS, SvState.lookup, SvState.set]

theorem pY1_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pY1 N W i j) =
      .ok (MS ins reg { w with y1 := w.y1.insertAt ((i * N + j) * (2 * W + 2)) (y1V N W i j w.p0 w.p1 w.p2) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pY1, sext2, c32, y1V, sext2V, runCombProcess2, evalExpr2, evalExprs2, evalBinOp,
    readSignal, resolveLhs2, MS, SvState.lookup, SvState.set]

theorem pS2_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pS2 N W i j) =
      .ok (MS ins reg { w with s2 := w.s2.insertAt ((i * N + j) * (2 * W + 2)) (s2V N W i j w.x1 w.y1 w.p3) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pS2, sext2, s2V, sext2V, runCombProcess2, evalExpr2, evalExprs2, evalBinOp,
    readSignal, resolveLhs2, MS, SvState.lookup, SvState.set]

theorem pC2_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pC2 N W i j) =
      .ok (MS ins reg { w with c2 := w.c2.insertAt ((i * N + j) * (2 * W + 2)) (c2V N W i j w.x1 w.y1 w.p3) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pC2, sext2, c32, c2V, sext2V, runCombProcess2, evalExpr2, evalExprs2, evalBinOp,
    readSignal, resolveLhs2, MS, SvState.lookup, SvState.set]

theorem pS4_comb (N W i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runCombProcess2 F (MS ins reg w) (pS4 N W i j) =
      .ok (MS ins reg { w with s4 := w.s4.insertAt ((i * N + j) * (2 * W + 2)) (s4V N W i j reg.rs reg.rc) }) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pS4, s4V, runCombProcess2, evalExpr2, evalBinOp,
    readSignal, resolveLhs2, MS, SvState.lookup, SvState.set]

/-! ### 4-layer DAG combinational settling (`settle_mm`) -/

def procLo : Process2 → Nat
  | .assign (.slice _ lo _) _ => lo
  | _ => 0

theorem combPass_cons {d : Design2} {F idx : Nat} {p : Process2} {st st' : SvState} {rest : List Nat}
    (hp : d.processes[idx]? = some p) (hr : runCombProcess2 F st p = .ok st') :
    combPass2 d F st (idx :: rest) = combPass2 d F st' rest := by
  simp [combPass2, hp, hr]

theorem combPass_cons_none {d : Design2} {F idx : Nat} {st : SvState} {rest : List Nat}
    (hp : d.processes[idx]? = none) :
    combPass2 d F st (idx :: rest) = combPass2 d F st rest := by
  simp [combPass2, hp]

theorem hit_cons {d : Design2} {idx : Nat} {rest : List Nat} {q : Process2} {P : Prop}
    (h : (∃ x ∈ idx :: rest, d.processes[x]? = some q) ∨ P) :
    d.processes[idx]? = some q ∨ ((∃ x ∈ rest, d.processes[x]? = some q) ∨ P) := by
  rcases h with ⟨x, hx, hq⟩ | h
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl hq
    · exact .inr (.inl ⟨x, hx, hq⟩)
  · exact .inr (.inr h)

theorem mem_combIndices_of_mem {N W AccW : Nat} {p : Process2}
    (hm : p ∈ mmProcs N W AccW) (hc : p.isCombPhase = true) :
    ∃ idx ∈ (mmD N W AccW).combIndices, (mmD N W AccW).processes[idx]? = some p := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hm
  have hsome : (mmD N W AccW).processes[idx]? = some p := by simpa [mmD] using hidx
  have ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hsome
  exact ⟨idx, by simp [Design2.combIndices, List.mem_filter, List.mem_range, hlt, heq, hc], hsome⟩

theorem mmD_get_mem {N W AccW idx : Nat} {p : Process2}
    (hp : (mmD N W AccW).processes[idx]? = some p) : p ∈ mmProcs N W AccW := by
  have := List.mem_of_getElem? (by rwa [← Array.getElem?_toList] at hp)
  simpa [mmD] using this

/-- Single comb step on `MS ins reg w`: always succeeds into `MS ins reg w'`, preserves `WdWires`. -/
def stepW (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) (p : Process2) : MWires :=
  match p with
  | .assign (.ident "Ap") _ => { w with ap := apV N W ins.a }
  | .assign (.ident "Bp") _ => { w with bp := bpV N W ins.b }
  | .assign (.slice "p0" lo _) _ =>
      let r := lo / (2 * W)
      { w with p0 := w.p0.insertAt lo (pmV N W 0 (r / N) (r % N) ins.s w.ap w.bp reg.ash reg.bsh) }
  | .assign (.slice "p1" lo _) _ =>
      let r := lo / (2 * W)
      { w with p1 := w.p1.insertAt lo (pmV N W 1 (r / N) (r % N) ins.s w.ap w.bp reg.ash reg.bsh) }
  | .assign (.slice "p2" lo _) _ =>
      let r := lo / (2 * W)
      { w with p2 := w.p2.insertAt lo (pmV N W 2 (r / N) (r % N) ins.s w.ap w.bp reg.ash reg.bsh) }
  | .assign (.slice "p3" lo _) _ =>
      let r := lo / (2 * W)
      { w with p3 := w.p3.insertAt lo (pmV N W 3 (r / N) (r % N) ins.s w.ap w.bp reg.ash reg.bsh) }
  | .assign (.slice "x1" lo _) _ =>
      let r := lo / (2 * W + 2)
      { w with x1 := w.x1.insertAt lo (x1V N W (r / N) (r % N) w.p0 w.p1 w.p2) }
  | .assign (.slice "y1" lo _) _ =>
      let r := lo / (2 * W + 2)
      { w with y1 := w.y1.insertAt lo (y1V N W (r / N) (r % N) w.p0 w.p1 w.p2) }
  | .assign (.slice "s2" lo _) _ =>
      let r := lo / (2 * W + 2)
      { w with s2 := w.s2.insertAt lo (s2V N W (r / N) (r % N) w.x1 w.y1 w.p3) }
  | .assign (.slice "c2" lo _) _ =>
      let r := lo / (2 * W + 2)
      { w with c2 := w.c2.insertAt lo (c2V N W (r / N) (r % N) w.x1 w.y1 w.p3) }
  | .assign (.slice "s4" lo _) _ =>
      let r := lo / (2 * W + 2)
      { w with s4 := w.s4.insertAt lo (s4V N W (r / N) (r % N) reg.rs reg.rc) }
  | _ => w

theorem runComb_stepW {N W AccW F : Nat} (hW : 1 ≤ W) (hF : 30 ≤ F)
    (ins : MIns) (reg : MRegs) (w : MWires) (hw : WdWires N W w)
    {p : Process2} (hp : p ∈ mmProcs N W AccW) :
    runCombProcess2 F (MS ins reg w) p = .ok (MS ins reg (stepW N W ins reg w p)) ∧
      WdWires N W (stepW N W ins reg w p) := by
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, hi, hj, hp⟩
  · exact ⟨pAp_comb N W F hF ins reg w hw.1, by simp [stepW, pAp, WdWires, hw.2]⟩
  · exact ⟨pBp_comb N W F hF ins reg w hw.2.1, by simp [stepW, pBp, WdWires, hw.1, hw.2.2]⟩
  · exact ⟨pCtrl_comb N W F _, by simpa [stepW, pCtrl] using hw⟩
  · have hPpos : 0 < 2 * W := by omega
    have hSpos : 0 < 2 * W + 2 := by omega
    have hdP : (i * N + j) * (2 * W) / (2 * W) = i * N + j := Nat.mul_div_cancel _ hPpos
    have hdS : (i * N + j) * (2 * W + 2) / (2 * W + 2) = i * N + j := Nat.mul_div_cancel _ hSpos
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by simpa [stepW, pPm, hdP, rm_div hj, rm_mod hj] using pP0_comb N W i j F hF ins reg w,
        by simp [stepW, pPm, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pPm, hdP, rm_div hj, rm_mod hj] using pP1_comb N W i j F hF ins reg w,
        by simp [stepW, pPm, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pPm, hdP, rm_div hj, rm_mod hj] using pP2_comb N W i j F hF ins reg w,
        by simp [stepW, pPm, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pPm, hdP, rm_div hj, rm_mod hj] using pP3_comb N W i j F hF ins reg w,
        by simp [stepW, pPm, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pX1, hdS, rm_div hj, rm_mod hj] using pX1_comb N W i j F hF ins reg w,
        by simp [stepW, pX1, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pY1, hdS, rm_div hj, rm_mod hj] using pY1_comb N W i j F hF ins reg w,
        by simp [stepW, pY1, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pS2, hdS, rm_div hj, rm_mod hj] using pS2_comb N W i j F hF ins reg w,
        by simp [stepW, pS2, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pC2, hdS, rm_div hj, rm_mod hj] using pC2_comb N W i j F hF ins reg w,
        by simp [stepW, pC2, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨by simpa [stepW, pS4, hdS, rm_div hj, rm_mod hj] using pS4_comb N W i j F hF ins reg w,
        by simp [stepW, pS4, WdWires, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2.1,
          hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.2.2.2]⟩
    · exact ⟨pFF_comb N W AccW i j F _, by simpa [stepW, pFF] using hw⟩

/-- Fold `stepW` over a list of process indices. -/
def passW (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : List Nat → MWires
  | [] => w
  | idx :: rest =>
    match (mmD N W AccW).processes[idx]? with
    | none => passW N W AccW ins reg w rest
    | some p => passW N W AccW ins reg (stepW N W ins reg w p) rest

theorem combPass_eq_passW {N W AccW F : Nat} (hW : 1 ≤ W) (hF : 30 ≤ F)
    (ins : MIns) (reg : MRegs) :
    ∀ (is : List Nat) (w : MWires), WdWires N W w →
      combPass2 (mmD N W AccW) F (MS ins reg w) is = .ok (MS ins reg (passW N W AccW ins reg w is)) ∧
        WdWires N W (passW N W AccW ins reg w is)
  | [], w, hw => ⟨rfl, hw⟩
  | idx :: rest, w, hw => by
    cases hp : (mmD N W AccW).processes[idx]? with
    | none =>
      simpa [passW, hp, combPass_cons_none hp] using combPass_eq_passW hW hF ins reg rest w hw
    | some p =>
      have ⟨hr, hw'⟩ := runComb_stepW hW hF ins reg w hw (mmD_get_mem hp)
      simpa [passW, hp, combPass_cons hp hr] using
        combPass_eq_passW hW hF ins reg rest (stepW N W ins reg w p) hw'

/-- Generic single-field grid convergence over `passW` (handles all 9 PE grid wires!). -/
theorem passW_grid {N W AccW E : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hE : 0 < E)
    (ins : MIns) (reg : MRegs) (field : MWires → LVec) (val : Nat → Nat → LVec)
    (hval : ∀ a b, (val a b).width = E) (hfw : ∀ w, WdWires N W w → (field w).width = N * N * E)
    (P : MWires → Prop) (hPstep : ∀ w p, WdWires N W w → P w → p ∈ mmProcs N W AccW → P (stepW N W ins reg w p))
    (mkP : Nat → Nat → Process2)
    (hmkP_mem : ∀ i j, i < N → j < N → mkP i j ∈ mmProcs N W AccW ∧ (mkP i j).isCombPhase = true)
    (hstep : ∀ w p, WdWires N W w → P w → p ∈ mmProcs N W AccW →
      field (stepW N W ins reg w p) = field w ∨
      ∃ i0 j0, i0 < N ∧ j0 < N ∧ p = mkP i0 j0 ∧
        field (stepW N W ins reg w p) = (field w).insertAt ((i0 * N + j0) * E) (val i0 j0))
    (hmkP_hit : ∀ w i j, WdWires N W w → P w → i < N → j < N →
      field (stepW N W ins reg w (mkP i j)) = (field w).insertAt ((i * N + j) * E) (val i j))
    (hmkP_inj : ∀ i0 j0 i j, i0 < N → j0 < N → i < N → j < N → mkP i0 j0 = mkP i j → i0 = i ∧ j0 = j) :
    ∀ (is : List Nat) (w : MWires), WdWires N W w → P w →
      WdWires N W (passW N W AccW ins reg w is) ∧ P (passW N W AccW ins reg w is) ∧
      ∀ i j, i < N → j < N →
        ((∃ x ∈ is, (mmD N W AccW).processes[x]? = some (mkP i j)) ∨
          (field w).extract ((i * N + j) * E) E = val i j) →
        (field (passW N W AccW ins reg w is)).extract ((i * N + j) * E) E = val i j := by
  intro is
  induction is with
  | nil =>
    intro w hw hP
    exact ⟨hw, hP, fun _ _ _ _ h => h.resolve_left (by simp)⟩
  | cons idx rest ih =>
    intro w hw hP
    cases hp : (mmD N W AccW).processes[idx]? with
    | none =>
      obtain ⟨hw', hP', hres⟩ := ih w hw hP
      refine ⟨by simpa [passW, hp] using hw', by simpa [passW, hp] using hP', fun i j hi hj h => ?_⟩
      simpa [passW, hp] using hres i j hi hj (by
        rcases hit_cons h with h0 | h0
        · rw [hp] at h0; cases h0
        · exact h0)
    | some p =>
      have hpm := mmD_get_mem hp
      have hw1 : WdWires N W (stepW N W ins reg w p) := (runComb_stepW hW (by omega : 30 ≤ 30) ins reg w hw hpm).2
      have hP1 : P (stepW N W ins reg w p) := hPstep w p hw hP hpm
      obtain ⟨hw', hP', hres⟩ := ih (stepW N W ins reg w p) hw1 hP1
      refine ⟨by simpa [passW, hp] using hw', by simpa [passW, hp] using hP', fun i j hi hj h => ?_⟩
      simp only [passW, hp]
      refine hres i j hi hj ?_
      rcases hit_cons h with h0 | h0
      · rw [hp] at h0; injection h0 with hpeq; subst hpeq
        right
        rw [hmkP_hit w i j hw hP hi hj]
        exact step_extract (hfw w hw) (hval i j) (rm_lt hi hj) (.inl ⟨rfl, rfl⟩)
      · rcases h0 with h0 | h0
        · exact .inl h0
        · right
          rcases hstep w p hw hP hpm with hsame | ⟨i0, j0, hi0, hj0, rfl, hupd⟩
          · rw [hsame]; exact h0
          · rw [hupd]
            by_cases heq : i0 * N + j0 = i * N + j
            · obtain ⟨rfl, rfl⟩ := rm_inj hj0 hj heq
              exact step_extract (hfw w hw) (hval _ _) (rm_lt hi0 hj0) (.inl ⟨rfl, rfl⟩)
            · exact step_extract (hfw w hw) (hval _ _) (rm_lt hi0 hj0) (.inr ⟨heq, h0⟩)

theorem passW_grid_perm {N W AccW E : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hE : 0 < E)
    (ins : MIns) (reg : MRegs) (field : MWires → LVec) (val : Nat → Nat → LVec)
    (hval : ∀ a b, (val a b).width = E) (hfw : ∀ w, WdWires N W w → (field w).width = N * N * E)
    (P : MWires → Prop) (hPstep : ∀ w p, WdWires N W w → P w → p ∈ mmProcs N W AccW → P (stepW N W ins reg w p))
    (mkP : Nat → Nat → Process2)
    (hmkP_mem : ∀ i j, i < N → j < N → mkP i j ∈ mmProcs N W AccW ∧ (mkP i j).isCombPhase = true)
    (hstep : ∀ w p, WdWires N W w → P w → p ∈ mmProcs N W AccW →
      field (stepW N W ins reg w p) = field w ∨
      ∃ i0 j0, i0 < N ∧ j0 < N ∧ p = mkP i0 j0 ∧
        field (stepW N W ins reg w p) = (field w).insertAt ((i0 * N + j0) * E) (val i0 j0))
    (hmkP_hit : ∀ w i j, WdWires N W w → P w → i < N → j < N →
      field (stepW N W ins reg w (mkP i j)) = (field w).insertAt ((i * N + j) * E) (val i j))
    (hmkP_inj : ∀ i0 j0 i j, i0 < N → j0 < N → i < N → j < N → mkP i0 j0 = mkP i j → i0 = i ∧ j0 = j)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires} (hw : WdWires N W w) (hP : P w) :
    field (passW N W AccW ins reg w is) = packGrid E N val := by
  obtain ⟨hw', -, hex⟩ := passW_grid hN hW hE ins reg field val hval hfw P hPstep mkP hmkP_mem hstep hmkP_hit hmkP_inj is w hw hP
  refine eq_packGrid hN hval (hfw _ hw') fun i j hi hj => hex i j hi hj (.inl ?_)
  obtain ⟨idx, hidx, hget⟩ := mem_combIndices_of_mem (hmkP_mem i j hi hj).1 (hmkP_mem i j hi hj).2
  exact ⟨idx, hperm.mem_iff.mpr hidx, hget⟩

theorem passW_whole {N W AccW : Nat} (ins : MIns) (reg : MRegs) (field : MWires → LVec) (tgt : LVec)
    (P0 : Process2) (hP0_mem : P0 ∈ mmProcs N W AccW ∧ P0.isCombPhase = true)
    (hstep : ∀ w p, p ∈ mmProcs N W AccW → field (stepW N W ins reg w p) = field w ∨ field (stepW N W ins reg w p) = tgt)
    (hhit : ∀ w, field (stepW N W ins reg w P0) = tgt) :
    ∀ (is : List Nat) (w : MWires),
      ((∃ x ∈ is, (mmD N W AccW).processes[x]? = some P0) ∨ field w = tgt) →
      field (passW N W AccW ins reg w is) = tgt
  | [], w, h => h.resolve_left (by simp)
  | idx :: rest, w, h => by
    cases hp : (mmD N W AccW).processes[idx]? with
    | none =>
      simp only [passW, hp]
      exact passW_whole ins reg field tgt P0 hP0_mem hstep hhit rest w (by
        rcases hit_cons h with h0 | h0
        · rw [hp] at h0; cases h0
        · exact h0)
    | some p =>
      simp only [passW, hp]
      refine passW_whole ins reg field tgt P0 hP0_mem hstep hhit rest _ ?_
      rcases hit_cons h with h0 | h0
      · rw [hp] at h0; injection h0 with heq; subst heq; exact .inr (hhit w)
      · rcases h0 with h0 | h0
        · exact .inl h0
        · rcases hstep w p (mmD_get_mem hp) with h1 | h1
          · exact .inr (h1.trans h0)
          · exact .inr h1

def L1 (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : Prop :=
  let wT := wSet N W ins reg
  w.ap = wT.ap ∧ w.bp = wT.bp ∧ w.s4 = wT.s4

def L2 (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : Prop :=
  let wT := wSet N W ins reg
  L1 N W ins reg w ∧ w.p0 = wT.p0 ∧ w.p1 = wT.p1 ∧ w.p2 = wT.p2 ∧ w.p3 = wT.p3

def L3 (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : Prop :=
  let wT := wSet N W ins reg
  L2 N W ins reg w ∧ w.x1 = wT.x1 ∧ w.y1 = wT.y1

private theorem stepW_pres_L1 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {w : MWires} {p : Process2} (h1 : L1 N W ins reg w) (hp : p ∈ mmProcs N W AccW) :
    L1 N W ins reg (stepW N W ins reg w p) := by
  obtain ⟨hap, hbp, hs4⟩ := h1
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, hi, hj, hp⟩
  · exact ⟨rfl, hbp, hs4⟩
  · exact ⟨hap, rfl, hs4⟩
  · exact ⟨hap, hbp, hs4⟩
  · have hdS : (i * N + j) * (2 * W + 2) / (2 * W + 2) = i * N + j := Nat.mul_div_cancel _ (by omega)
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · exact ⟨hap, hbp, hs4⟩
    · refine ⟨hap, hbp, ?_⟩
      simp only [stepW, pS4, hdS, rm_div hj, rm_mod hj, hs4, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_s4V N W a b reg.rs reg.rc) hi hj
    · exact ⟨hap, hbp, hs4⟩

private theorem stepW_pres_L2 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {w : MWires} {p : Process2} (h2 : L2 N W ins reg w) (hp : p ∈ mmProcs N W AccW) :
    L2 N W ins reg (stepW N W ins reg w p) := by
  obtain ⟨h1, hp0, hp1, hp2, hp3⟩ := h2
  refine ⟨stepW_pres_L1 hN hW ins reg h1 hp, ?_⟩
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, hi, hj, hp⟩
  · exact ⟨hp0, hp1, hp2, hp3⟩
  · exact ⟨hp0, hp1, hp2, hp3⟩
  · exact ⟨hp0, hp1, hp2, hp3⟩
  · have hdP : (i * N + j) * (2 * W) / (2 * W) = i * N + j := Nat.mul_div_cancel _ (by omega)
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, hp1, hp2, hp3⟩
      simp only [stepW, pPm, hdP, rm_div hj, rm_mod hj, h1.1, h1.2.1, hp0, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_pmV N W 0 a b ..) hi hj
    · refine ⟨hp0, ?_, hp2, hp3⟩
      simp only [stepW, pPm, hdP, rm_div hj, rm_mod hj, h1.1, h1.2.1, hp1, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_pmV N W 1 a b ..) hi hj
    · refine ⟨hp0, hp1, ?_, hp3⟩
      simp only [stepW, pPm, hdP, rm_div hj, rm_mod hj, h1.1, h1.2.1, hp2, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_pmV N W 2 a b ..) hi hj
    · refine ⟨hp0, hp1, hp2, ?_⟩
      simp only [stepW, pPm, hdP, rm_div hj, rm_mod hj, h1.1, h1.2.1, hp3, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_pmV N W 3 a b ..) hi hj
    · exact ⟨hp0, hp1, hp2, hp3⟩
    · exact ⟨hp0, hp1, hp2, hp3⟩
    · exact ⟨hp0, hp1, hp2, hp3⟩
    · exact ⟨hp0, hp1, hp2, hp3⟩
    · exact ⟨hp0, hp1, hp2, hp3⟩
    · exact ⟨hp0, hp1, hp2, hp3⟩

private theorem stepW_pres_L3 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {w : MWires} {p : Process2} (h3 : L3 N W ins reg w) (hp : p ∈ mmProcs N W AccW) :
    L3 N W ins reg (stepW N W ins reg w p) := by
  obtain ⟨h2, hx1, hy1⟩ := h3
  refine ⟨stepW_pres_L2 hN hW ins reg h2 hp, ?_⟩
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, hi, hj, hp⟩
  · exact ⟨hx1, hy1⟩
  · exact ⟨hx1, hy1⟩
  · exact ⟨hx1, hy1⟩
  · have hdS : (i * N + j) * (2 * W + 2) / (2 * W + 2) = i * N + j := Nat.mul_div_cancel _ (by omega)
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩
    · refine ⟨?_, hy1⟩
      simp only [stepW, pX1, hdS, rm_div hj, rm_mod hj, h2.2.1, h2.2.2.1, h2.2.2.2.1, hx1, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_x1V N W a b ..) hi hj
    · refine ⟨hx1, ?_⟩
      simp only [stepW, pY1, hdS, rm_div hj, rm_mod hj, h2.2.1, h2.2.2.1, h2.2.2.2.1, hy1, wSet]
      exact insertAt_packGrid_self hN (fun a b => width_y1V N W a b ..) hi hj
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩
    · exact ⟨hx1, hy1⟩

private theorem pe_mem_mmProcs {N W AccW i j : Nat} (hi : i < N) (hj : j < N)
    {p : Process2} (hp : p ∈ peProcs N W AccW i j) : p ∈ mmProcs N W AccW := by
  simp only [mmProcs, List.mem_cons, List.mem_flatMap, List.mem_range]
  exact .inr (.inr (.inr ⟨i, hi, j, hj, hp⟩))

theorem passW_L1 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires} (hw : WdWires N W w) :
    L1 N W ins reg (passW N W AccW ins reg w is) := by
  have hap : (passW N W AccW ins reg w is).ap = (wSet N W ins reg).ap := by
    refine passW_whole ins reg MWires.ap (wSet N W ins reg).ap (pAp W)
      ⟨by simp [mmProcs], rfl⟩
      (fun w' p hp => by rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
                         · exact .inr rfl
                         · exact .inl rfl
                         · exact .inl rfl
                         · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
                           rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact .inl rfl)
      (fun _ => rfl) is w (.inl ?_)
    obtain ⟨idx, hidx, hget⟩ := mem_combIndices_of_mem (N := N) (W := W) (AccW := AccW) (p := pAp W) (by simp [mmProcs]) rfl
    exact ⟨idx, hperm.mem_iff.mpr hidx, hget⟩
  have hbp : (passW N W AccW ins reg w is).bp = (wSet N W ins reg).bp := by
    refine passW_whole ins reg MWires.bp (wSet N W ins reg).bp (pBp N W)
      ⟨by simp [mmProcs], rfl⟩
      (fun w' p hp => by rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
                         · exact .inl rfl
                         · exact .inr rfl
                         · exact .inl rfl
                         · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
                           rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact .inl rfl)
      (fun _ => rfl) is w (.inl ?_)
    obtain ⟨idx, hidx, hget⟩ := mem_combIndices_of_mem (N := N) (W := W) (AccW := AccW) (p := pBp N W) (by simp [mmProcs]) rfl
    exact ⟨idx, hperm.mem_iff.mpr hidx, hget⟩
  have hs4 : (passW N W AccW ins reg w is).s4 = (wSet N W ins reg).s4 := by
    refine passW_grid_perm hN hW (by omega) ins reg MWires.s4 (fun i j => s4V N W i j reg.rs reg.rc)
      (fun _ _ => width_s4V ..) (fun w' hw' => hw'.2.2.2.2.2.2.2.2.2.2) (fun _ => True)
      (fun _ _ _ _ _ => trivial) (pS4 N W)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (by simp [peProcs]), rfl⟩)
      (fun w' p _ _ hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pS4, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj0, rm_mod hj0]⟩
          · exact .inl rfl)
      (fun w' i j _ _ _ hj => by simp [stepW, pS4, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj, rm_mod hj])
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W + 2) (congrArg procLo heq)))
      hperm hw trivial
  exact ⟨hap, hbp, hs4⟩

theorem passW_L2 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires}
    (hw : WdWires N W w) (h1 : L1 N W ins reg w) :
    L2 N W ins reg (passW N W AccW ins reg w is) := by
  have hL1 : L1 N W ins reg (passW N W AccW ins reg w is) := passW_L1 hN hW ins reg hperm hw
  have hP := fun (m : Nat) (nm : String) (fld : MWires → LVec)
      (hfw : ∀ w', WdWires N W w' → (fld w').width = N * N * (2 * W))
      (hmem : ∀ i j, i < N → j < N → pPm N W m i j nm ∈ peProcs N W AccW i j)
      (hstep : ∀ w' p, L1 N W ins reg w' → p ∈ mmProcs N W AccW →
        fld (stepW N W ins reg w' p) = fld w' ∨
        ∃ i0 j0, i0 < N ∧ j0 < N ∧ p = pPm N W m i0 j0 nm ∧
          fld (stepW N W ins reg w' p) = (fld w').insertAt ((i0 * N + j0) * (2 * W)) (pmV N W m i0 j0 ins.s (wSet N W ins reg).ap (wSet N W ins reg).bp reg.ash reg.bsh))
      (hhit : ∀ w' i j, L1 N W ins reg w' → i < N → j < N →
        fld (stepW N W ins reg w' (pPm N W m i j nm)) = (fld w').insertAt ((i * N + j) * (2 * W)) (pmV N W m i j ins.s (wSet N W ins reg).ap (wSet N W ins reg).bp reg.ash reg.bsh)) =>
    passW_grid_perm hN hW (by omega) ins reg fld
      (fun i j => pmV N W m i j ins.s (wSet N W ins reg).ap (wSet N W ins reg).bp reg.ash reg.bsh)
      (fun _ _ => width_pmV ..) hfw (L1 N W ins reg)
      (fun _ _ _ h1' hp => stepW_pres_L1 hN hW ins reg h1' hp)
      (fun i j => pPm N W m i j nm)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (hmem i j hi hj), rfl⟩)
      (fun w' p _ h1' hp => hstep w' p h1' hp)
      (fun w' i j _ h1' hi hj => hhit w' i j h1' hi hj)
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W) (congrArg procLo heq)))
      hperm hw h1
  refine ⟨hL1, ?_, ?_, ?_, ?_⟩
  · exact hP 0 "p0" MWires.p0 (fun _ hw' => hw'.2.2.1) (fun _ _ _ _ => by simp [peProcs])
      (fun w' p h1' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj0, rm_mod hj0, h1'.1, h1'.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j h1' _ hj => by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj, rm_mod hj, h1'.1, h1'.2.1])
  · exact hP 1 "p1" MWires.p1 (fun _ hw' => hw'.2.2.2.1) (fun _ _ _ _ => by simp [peProcs])
      (fun w' p h1' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj0, rm_mod hj0, h1'.1, h1'.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j h1' _ hj => by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj, rm_mod hj, h1'.1, h1'.2.1])
  · exact hP 2 "p2" MWires.p2 (fun _ hw' => hw'.2.2.2.2.1) (fun _ _ _ _ => by simp [peProcs])
      (fun w' p h1' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj0, rm_mod hj0, h1'.1, h1'.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j h1' _ hj => by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj, rm_mod hj, h1'.1, h1'.2.1])
  · exact hP 3 "p3" MWires.p3 (fun _ hw' => hw'.2.2.2.2.2.1) (fun _ _ _ _ => by simp [peProcs])
      (fun w' p h1' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj0, rm_mod hj0, h1'.1, h1'.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j h1' _ hj => by simp [stepW, pPm, Nat.mul_div_cancel _ (by omega : 0 < 2 * W), rm_div hj, rm_mod hj, h1'.1, h1'.2.1])

theorem passW_L3 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires}
    (hw : WdWires N W w) (h2 : L2 N W ins reg w) :
    L3 N W ins reg (passW N W AccW ins reg w is) := by
  refine ⟨passW_L2 hN hW ins reg hperm hw h2.1, ?_, ?_⟩
  · exact passW_grid_perm hN hW (by omega) ins reg MWires.x1
      (fun i j => x1V N W i j (wSet N W ins reg).p0 (wSet N W ins reg).p1 (wSet N W ins reg).p2)
      (fun _ _ => width_x1V ..) (fun _ hw' => hw'.2.2.2.2.2.2.1) (L2 N W ins reg)
      (fun _ _ _ h2' hp => stepW_pres_L2 hN hW ins reg h2' hp) (pX1 N W)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (by simp [peProcs]), rfl⟩)
      (fun w' p _ h2' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pX1, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj0, rm_mod hj0, h2'.2.1, h2'.2.2.1, h2'.2.2.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j _ h2' _ hj => by simp [stepW, pX1, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj, rm_mod hj, h2'.2.1, h2'.2.2.1, h2'.2.2.2.1])
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W + 2) (congrArg procLo heq)))
      hperm hw h2
  · exact passW_grid_perm hN hW (by omega) ins reg MWires.y1
      (fun i j => y1V N W i j (wSet N W ins reg).p0 (wSet N W ins reg).p1 (wSet N W ins reg).p2)
      (fun _ _ => width_y1V ..) (fun _ hw' => hw'.2.2.2.2.2.2.2.1) (L2 N W ins reg)
      (fun _ _ _ h2' hp => stepW_pres_L2 hN hW ins reg h2' hp) (pY1 N W)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (by simp [peProcs]), rfl⟩)
      (fun w' p _ h2' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pY1, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj0, rm_mod hj0, h2'.2.1, h2'.2.2.1, h2'.2.2.2.1]⟩
          all_goals exact .inl rfl)
      (fun w' i j _ h2' _ hj => by simp [stepW, pY1, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj, rm_mod hj, h2'.2.1, h2'.2.2.1, h2'.2.2.2.1])
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W + 2) (congrArg procLo heq)))
      hperm hw h2

theorem passW_L4 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires}
    (hw : WdWires N W w) (h3 : L3 N W ins reg w) :
    passW N W AccW ins reg w is = wSet N W ins reg := by
  have hL3 := passW_L3 hN hW ins reg hperm hw h3.1
  have hs2 : (passW N W AccW ins reg w is).s2 = (wSet N W ins reg).s2 :=
    passW_grid_perm hN hW (by omega) ins reg MWires.s2
      (fun i j => s2V N W i j (wSet N W ins reg).x1 (wSet N W ins reg).y1 (wSet N W ins reg).p3)
      (fun _ _ => width_s2V ..) (fun _ hw' => hw'.2.2.2.2.2.2.2.2.1) (L3 N W ins reg)
      (fun _ _ _ h3' hp => stepW_pres_L3 hN hW ins reg h3' hp) (pS2 N W)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (by simp [peProcs]), rfl⟩)
      (fun w' p _ h3' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pS2, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj0, rm_mod hj0, h3'.2.1, h3'.2.2, h3'.1.2.2.2.2]⟩
          all_goals exact .inl rfl)
      (fun w' i j _ h3' _ hj => by simp [stepW, pS2, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj, rm_mod hj, h3'.2.1, h3'.2.2, h3'.1.2.2.2.2])
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W + 2) (congrArg procLo heq)))
      hperm hw h3
  have hc2 : (passW N W AccW ins reg w is).c2 = (wSet N W ins reg).c2 :=
    passW_grid_perm hN hW (by omega) ins reg MWires.c2
      (fun i j => c2V N W i j (wSet N W ins reg).x1 (wSet N W ins reg).y1 (wSet N W ins reg).p3)
      (fun _ _ => width_c2V ..) (fun _ hw' => hw'.2.2.2.2.2.2.2.2.2.1) (L3 N W ins reg)
      (fun _ _ _ h3' hp => stepW_pres_L3 hN hW ins reg h3' hp) (pC2 N W)
      (fun i j hi hj => ⟨pe_mem_mmProcs hi hj (by simp [peProcs]), rfl⟩)
      (fun w' p _ h3' hp => by
        rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i0, j0, hi0, hj0, hp⟩
        · exact .inl rfl
        · exact .inl rfl
        · exact .inl rfl
        · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inl rfl
          · exact .inr ⟨i0, j0, hi0, hj0, rfl, by simp [stepW, pC2, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj0, rm_mod hj0, h3'.2.1, h3'.2.2, h3'.1.2.2.2.2]⟩
          all_goals exact .inl rfl)
      (fun w' i j _ h3' _ hj => by simp [stepW, pC2, Nat.mul_div_cancel _ (by omega : 0 < 2 * W + 2), rm_div hj, rm_mod hj, h3'.2.1, h3'.2.2, h3'.1.2.2.2.2])
      (fun i0 j0 i j _ hj0 _ hj heq => rm_inj hj0 hj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * W + 2) (congrArg procLo heq)))
      hperm hw h3
  obtain ⟨⟨⟨hap, hbp, hs4⟩, hp0, hp1, hp2, hp3⟩, hx1, hy1⟩ := hL3
  cases h : passW N W AccW ins reg w is
  cases hT : wSet N W ins reg
  simp only [h, hT] at hap hbp hs4 hp0 hp1 hp2 hp3 hx1 hy1 hs2 hc2
  subst hap; subst hbp; subst hs4; subst hp0; subst hp1; subst hp2; subst hp3
  subst hx1; subst hy1; subst hs2; subst hc2; rfl

theorem passW_fix_eq {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (ins : MIns) (reg : MRegs)
    {is : List Nat} (hperm : is.Perm (mmD N W AccW).combIndices) {w : MWires}
    (hw : WdWires N W w) (hfix : passW N W AccW ins reg w is = w) : w = wSet N W ins reg := by
  have h1 : L1 N W ins reg w := hfix ▸ passW_L1 hN hW ins reg hperm hw
  have h2 : L2 N W ins reg w := hfix ▸ passW_L2 hN hW ins reg hperm hw h1
  have h3 : L3 N W ins reg w := hfix ▸ passW_L3 hN hW ins reg hperm hw h2
  exact hfix.symm.trans (passW_L4 hN hW ins reg hperm hw h3)

/-- **The 4-layer DAG comb settle**, under every schedule, for every fuel `F ≥ 36`. -/
theorem settle_mm {N W AccW F : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hF : 36 ≤ F)
    (σ : ScheduleOracle) (ins : MIns) (reg : MRegs) (w : MWires) (hw : WdWires N W w) (k : Nat) :
    ∃ k', combSettle2 (mmD N W AccW) σ F (MS ins reg w) k = .ok (MS ins reg (wSet N W ins reg), k') := by
  have hdone : ∀ (F' j : Nat) (w' : MWires), 31 ≤ F' → WdWires N W w' → w' = wSet N W ins reg →
      ∃ k', combSettle2 (mmD N W AccW) σ F' (MS ins reg w') j = .ok (MS ins reg (wSet N W ins reg), k') := by
    intro F' j w' hF' hw' heq; subst heq
    obtain ⟨f, rfl⟩ : ∃ f, F' = f + 1 := ⟨F' - 1, by omega⟩
    have hperm := σ.choose_perm j (mmD N W AccW).combIndices
    have hL3 : L3 N W ins reg (wSet N W ins reg) := ⟨⟨⟨rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
    have hpass := (combPass_eq_passW (AccW := AccW) hW (by omega : 30 ≤ f) ins reg
      (σ.choose j (mmD N W AccW).combIndices) (wSet N W ins reg) hw').1
    rw [passW_L4 hN hW ins reg hperm hw' hL3] at hpass
    rw [combSettle2.eq_2, hpass]
    simp only [Res.ok_bind, beq_self_eq_true, ↓reduceIte]
    exact ⟨j + 1, rfl⟩
  have hstep : ∀ (F' j : Nat) (w' : MWires), 32 ≤ F' → WdWires N W w' →
      (∀ w'', WdWires N W w'' → w'' = passW N W AccW ins reg w' (σ.choose j (mmD N W AccW).combIndices) →
        ∃ k', combSettle2 (mmD N W AccW) σ (F' - 1) (MS ins reg w'') (j + 1) = .ok (MS ins reg (wSet N W ins reg), k')) →
      ∃ k', combSettle2 (mmD N W AccW) σ F' (MS ins reg w') j = .ok (MS ins reg (wSet N W ins reg), k') := by
    intro F' j w' hF' hw' hcont
    obtain ⟨f, rfl⟩ : ∃ f, F' = f + 1 := ⟨F' - 1, by omega⟩
    have hperm := σ.choose_perm j (mmD N W AccW).combIndices
    obtain ⟨hpass, hw''⟩ := combPass_eq_passW hW (by omega : 30 ≤ f) ins reg (σ.choose j (mmD N W AccW).combIndices) w' hw'
    rw [combSettle2.eq_2, hpass]
    simp only [Res.ok_bind]
    by_cases hb : (MS ins reg (passW N W AccW ins reg w' (σ.choose j (mmD N W AccW).combIndices)) == MS ins reg w') = true
    · simp only [hb, ↓reduceIte]
      have hfix := (MS_inj (eq_of_beq hb)).2.2
      rw [hfix, passW_fix_eq hN hW ins reg hperm hw' hfix]
      exact ⟨j + 1, rfl⟩
    · simp only [hb]
      exact hcont _ hw'' rfl
  refine hstep F k w (by omega) hw fun w1 hw1 heq1 => ?_
  have hL1 : L1 N W ins reg w1 := heq1 ▸ passW_L1 hN hW ins reg (σ.choose_perm k _) hw
  refine hstep (F - 1) (k + 1) w1 (by omega) hw1 fun w2 hw2 heq2 => ?_
  have hL2 : L2 N W ins reg w2 := heq2 ▸ passW_L2 hN hW ins reg (σ.choose_perm (k + 1) _) hw1 hL1
  refine hstep (F - 2) (k + 2) w2 (by omega) hw2 fun w3 hw3 heq3 => ?_
  have hL3 : L3 N W ins reg w3 := heq3 ▸ passW_L3 hN hW ins reg (σ.choose_perm (k + 2) _) hw2 hL2
  refine hstep (F - 3) (k + 3) w3 (by omega) hw3 fun w4 hw4 heq4 => ?_
  have hL4 : w4 = wSet N W ins reg := heq4 ▸ passW_L4 hN hW ins reg (σ.choose_perm (k + 3) _) hw3 hL3
  exact hdone (F - 4) (k + 4) w4 (by omega) hw4 hL4

/-! ### Section 3b: Edge execution, NBA commit, and `mm_cycle` -/

abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

def shA (W : Nat) (v : LVec) : LVec :=
  (v.shr ((LVec.ofInt 32 2).mul (LVec.ofInt 32 (W : Int)))).shr ((LVec.ofInt 32 2).mul (LVec.ofInt 32 (W : Int)))

def shB (N W : Nat) (v : LVec) : LVec :=
  (v.shr (((LVec.ofInt 32 2).mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int)))).shr
    (((LVec.ofInt 32 2).mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int)))

def ctrlQ (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : NbaQueue2 :=
  if ins.r.condTrue then
    [wr "busy" reg.bz ⟨#[.l0]⟩, wr "drain" reg.dr ⟨#[.l0]⟩, wr "done" reg.dn ⟨#[.l0]⟩, wr "k" reg.k (LVec.ofBitVec 0#32)]
  else if ins.s.condTrue then
    [wr "done" reg.dn ⟨#[.l0]⟩, wr "k" reg.k (LVec.ofBitVec 4#32)] ++
    (if (scmpLe4 N).condTrue then
      [wr "busy" reg.bz ⟨#[.l0]⟩, wr "drain" reg.dr ⟨#[.l1]⟩]
    else
      [wr "busy" reg.bz ⟨#[.l1]⟩, wr "drain" reg.dr ⟨#[.l0]⟩,
       wr "a_sh" reg.ash (shA W w.ap), wr "b_sh" reg.bsh (shB N W w.bp)])
  else if (landL reg.bz (scmpGt4 N)).condTrue then
    [wr "k" reg.k (reg.k.add (LVec.ofBitVec 4#32)),
     wr "a_sh" reg.ash (shA W reg.ash), wr "b_sh" reg.bsh (shB N W reg.bsh)] ++
    (if (LVec.ofLogic ((reg.k.add (LVec.ofBitVec 4#32)).ge (LVec.ofInt 32 (N : Int)))).condTrue then
      [wr "busy" reg.bz ⟨#[.l0]⟩, wr "drain" reg.dr ⟨#[.l1]⟩]
    else [])
  else if reg.dr.condTrue then
    [wr "drain" reg.dr ⟨#[.l0]⟩, wr "done" reg.dn ⟨#[.l1]⟩]
  else []

def sxAccV (AccW : Nat) (s4 : LVec) (lo sw : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[s4.extract (lo + sw - 1) 1]), s4.extract lo sw]

def addCV (N W AccW i j : Nat) (c s4 : LVec) : LVec :=
  (((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + (2 * W + 2))).add
    (sxAccV AccW s4 ((i * N + j) * (2 * W + 2)) (2 * W + 2))).resizeU AccW

def setCV (N W AccW i j : Nat) (s4 : LVec) : LVec :=
  (sxAccV AccW s4 ((i * N + j) * (2 * W + 2)) (2 * W + 2)).resizeU AccW

def peFFQ (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) (i j : Nat) : NbaQueue2 :=
  let loS := (i * N + j) * (2 * W + 2)
  let loC := (i * N + j) * AccW
  [("rs", loS, (w.s2.extract loS (2 * W + 2)).resizeU (2 * W + 2)),
   ("rc", loS, (w.c2.extract loS (2 * W + 2)).resizeU (2 * W + 2))] ++
  (if (landL ins.s (scmpGt4 N)).condTrue then
    [("C", loC, (LVec.ofBitVec 0#AccW).resizeU AccW)]
  else if (landL reg.bz (scmpGt4 N)).condTrue then
    [("C", loC, (addCV N W AccW i j reg.c w.s4).resizeU AccW)]
  else if reg.dr.condTrue then
    if (scmpLe4 N).condTrue then
      [("C", loC, (setCV N W AccW i j w.s4).resizeU AccW)]
    else
      [("C", loC, (addCV N W AccW i j reg.c w.s4).resizeU AccW)]
  else [])

def allPeFFQ (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j => peFFQ N W AccW ins reg w i j

def edgeQ (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) : NbaQueue2 :=
  ctrlQ N W ins reg w ++ allPeFFQ N W AccW ins reg w

theorem ctrl_run (N W F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runEdgeProcess2 F (MS ins reg w) [] (pCtrl N W) = .ok (MS ins reg w, ctrlQ N W ins reg w) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hland : (SymBinOp.land == SymBinOp.land) = true := by decide
  unfold ctrlQ
  by_cases h1 : ins.r.condTrue = true
  · simp [pCtrl, nb, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal,
      MS, SvState.lookup, wr, h1]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : ins.s.condTrue = true
    · simp only [h2, ↓reduceIte]
      by_cases h3 : (scmpLe4 N).condTrue = true
      · simp only [h3, ↓reduceIte]; simp [scmpLe4_eq] at h3
        simp [pCtrl, nb, c32, condLe4, runEdgeProcess2, execStmt2, execStmts2, evalExpr2,
          toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup, wr, h1, h2, h3]
      · simp only [h3, ↓reduceIte]; simp [scmpLe4_eq] at h3
        simp [pCtrl, nb, c32, amtA, amtB, shA, shB, condLe4, runEdgeProcess2, execStmt2, execStmts2,
          evalExpr2, evalBinOp, toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup, wr, h1, h2, h3]
    · simp only [h2, ↓reduceIte]
      by_cases h4 : (landL reg.bz (scmpGt4 N)).condTrue = true
      · simp only [h4, ↓reduceIte]; simp [scmpGt4_eq, landL] at h4
        by_cases h5 : (LVec.ofLogic ((reg.k.add (LVec.ofBitVec 4#32)).ge (LVec.ofInt 32 (N : Int)))).condTrue = true
        · simp only [h5, ↓reduceIte]
          simp [pCtrl, nb, c32, amtA, amtB, shA, shB, condGt4, hland, runEdgeProcess2, execStmt2,
            execStmts2, evalExpr2, evalBinOp, toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup,
            wr, h1, h2, h4, h5]
        · simp only [h5, ↓reduceIte]
          simp [pCtrl, nb, c32, amtA, amtB, shA, shB, condGt4, hland, runEdgeProcess2, execStmt2,
            execStmts2, evalExpr2, evalBinOp, toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup,
            wr, h1, h2, h4, h5]
      · simp only [h4, ↓reduceIte]; simp [scmpGt4_eq, landL] at h4
        by_cases h6 : reg.dr.condTrue = true
        · simp only [h6, ↓reduceIte]
          simp [pCtrl, nb, c32, condGt4, hland, runEdgeProcess2, execStmt2, execStmts2, evalExpr2,
            toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup, wr, h1, h2, h4, h6]
        · simp only [h6, ↓reduceIte]
          simp [pCtrl, nb, c32, condGt4, hland, runEdgeProcess2, execStmt2, execStmts2, evalExpr2,
            toInt?_ofInt, resolveLhs2, readSignal, MS, SvState.lookup, wr, h1, h2, h4, h6]

theorem peFF_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    runEdgeProcess2 F (MS ins reg w) [] (pFF N W AccW i j) = .ok (MS ins reg w, peFFQ N W AccW ins reg w i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hland : (SymBinOp.land == SymBinOp.land) = true := by decide
  unfold peFFQ
  by_cases h1 : (landL ins.s (scmpGt4 N)).condTrue = true <;>
    by_cases h2 : (landL reg.bz (scmpGt4 N)).condTrue = true <;>
    by_cases h3 : reg.dr.condTrue = true <;>
    by_cases h4 : (scmpLe4 N).condTrue = true
  all_goals
    simp only [h1, h2, h3, h4, ↓reduceIte]
    simp [scmpLe4_eq, scmpGt4_eq, landL] at h1 h2 h4
    simp [pFF, sextAcc, sxAccV, addCV, setCV, condGt4, condLe4, c32, hland, runEdgeProcess2,
      execStmt2, execStmts2, evalExpr2, evalExprs2, evalBinOp, toInt?_ofInt,
      resolveLhs2, readSignal, MS, SvState.lookup, h1, h2, h3, h4]

theorem mm_edgeQ (N W AccW F : Nat) (hF : 30 ≤ F) (ins : MIns) (reg : MRegs) (w : MWires) :
    (mmD N W AccW).processes.toList.flatMap (SvGolf.Cycle.runQ F (MS ins reg w)) =
      edgeQ N W AccW ins reg w := by
  have hA : ∀ tg e, SvGolf.Cycle.runQ F (MS ins reg w) (.assign tg e) = [] := fun _ _ => by
    cases F <;> rfl
  simp only [mmD, List.toList_toArray, mmProcs, peProcs, edgeQ, allPeFFQ,
    List.flatMap_cons, List.flatMap_nil, List.flatMap_assoc,
    pAp, pBp, pPm, pX1, pY1, pS2, pC2, pS4, hA,
    SvGolf.Cycle.runQ_of (ctrl_run N W F hF ins reg w),
    SvGolf.Cycle.runQ_of (peFF_run N W AccW _ _ F hF ins reg w),
    List.nil_append, List.append_nil]

theorem ctrlQ_names (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) :
    ∀ u ∈ ctrlQ N W ins reg w, u.1 ∈ ["done", "C", "k", "busy", "drain", "a_sh", "b_sh", "rs", "rc"] := by
  intro u hu; unfold ctrlQ at hu
  split at hu
  · simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl <;> simp
  · split at hu
    · split at hu <;> (simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    · split at hu
      · split at hu <;> (simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp)
      · split at hu
        · simp [wr] at hu; rcases hu with rfl | rfl <;> simp
        · simp at hu

theorem peFFQ_names (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) (i j : Nat) :
    ∀ u ∈ peFFQ N W AccW ins reg w i j, u.1 ∈ ["done", "C", "k", "busy", "drain", "a_sh", "b_sh", "rs", "rc"] := by
  intro u hu; unfold peFFQ at hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with (rfl | rfl) | hu
  · simp
  · simp
  · split at hu
    · simp at hu; rw [hu]; simp
    · split at hu
      · simp at hu; rw [hu]; simp
      · split at hu
        · split at hu <;> (simp at hu; rw [hu]; simp)
        · simp at hu

theorem edgeQ_names (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) :
    ∀ u ∈ edgeQ N W AccW ins reg w, u.1 ∈ ["done", "C", "k", "busy", "drain", "a_sh", "b_sh", "rs", "rc"] := by
  intro u hu
  simp only [edgeQ, allPeFFQ, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with hu | ⟨i, -, j, -, hu⟩
  · exact ctrlQ_names N W ins reg w u hu
  · exact peFFQ_names N W AccW ins reg w i j u hu

theorem commit_regs {ins : MIns} {reg : MRegs} {w : MWires} {Q : NbaQueue2}
    (hQ : ∀ u ∈ Q, u.1 ∈ ["done", "C", "k", "busy", "drain", "a_sh", "b_sh", "rs", "rc"]) :
    commitNba2 (MS ins reg w) Q =
      MS ins
        ⟨nbaFold "done" Q reg.dn, nbaFold "C" Q reg.c, nbaFold "k" Q reg.k,
         nbaFold "busy" Q reg.bz, nbaFold "drain" Q reg.dr,
         nbaFold "a_sh" Q reg.ash, nbaFold "b_sh" Q reg.bsh,
         nbaFold "rs" Q reg.rs, nbaFold "rc" Q reg.rc⟩ w := by
  rw [commitNba2_eq_map_of_names (by simp [MS]) hQ]
  simp [MS]

def nextRegs (N W AccW : Nat) (ins : MIns) (reg : MRegs) : MRegs :=
  let w := wSet N W ins reg
  let Q := edgeQ N W AccW ins reg w
  ⟨nbaFold "done" Q reg.dn, nbaFold "C" Q reg.c, nbaFold "k" Q reg.k,
   nbaFold "busy" Q reg.bz, nbaFold "drain" Q reg.dr,
   nbaFold "a_sh" Q reg.ash, nbaFold "b_sh" Q reg.bsh,
   nbaFold "rs" Q reg.rs, nbaFold "rc" Q reg.rc⟩

def mmNext (N W AccW : Nat) (ins : MIns) (reg : MRegs) : SvState :=
  let reg' := nextRegs N W AccW ins reg
  MS ins reg' (wSet N W ins reg')

@[simp] theorem nbaFold_width' (s : String) : ∀ (q : NbaQueue2) (v : LVec), (nbaFold s q v).width = v.width
  | [], _ => rfl
  | u :: q, v => by rw [nbaFold_cons, nbaFold_width' s q]; split <;> simp

theorem wdRegs_nextRegs (N W AccW : Nat) (ins : MIns) (reg : MRegs) (hw : WdRegs N W AccW reg) :
    WdRegs N W AccW (nextRegs N W AccW ins reg) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hw
  simp [WdRegs, nextRegs, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem mmNext_I (N W AccW : Nat) (ins : MIns) (reg : MRegs) (hw : WdRegs N W AccW reg) :
    I N W AccW (mmNext N W AccW ins reg) :=
  ⟨ins, nextRegs N W AccW ins reg, wSet N W ins (nextRegs N W AccW ins reg), rfl,
    wdRegs_nextRegs N W AccW ins reg hw, wdWires_wSet N W ins _⟩

/-- **One clock cycle of the loaded design**, under every schedule and every fuel `F ≥ 36`. -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64)
    (σ : ScheduleOracle) (e : SvState) (ins : MIns) (reg : MRegs) (w : MWires)
    (hw : WdWires N W w) (kk F : Nat) (hF : 36 ≤ F) :
    ∃ kk', cycleStep2 (design.sem N W AccW) σ F e (MS ins reg w) kk =
      .ok (mmNext N W AccW (appIns e ins) reg, kk') := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  refine SvGolf.Cycle.cycleStep2_mixed σ e _ kk (S1 := MS (appIns e ins) reg (wSet N W (appIns e ins) reg))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rw [apply_mm]
    exact settle_mm hN hW hF σ (appIns e ins) reg w hw j
  · refine SvGolf.Cycle.resetIndices_nil_of (List.all_eq_true.mpr fun p hp => ?_)
    have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
    rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · rfl
    · rfl
    · rfl
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro idx p hp he
    rcases mm_proc_mem (mmD_get_mem hp) with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · cases he
    · cases he
    · exact ⟨_, _, rfl, by simp [pCtrl, nb, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly]⟩
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · exact ⟨_, _, rfl, by simp [pFF, Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly]⟩
  · intro idx p hp he
    rcases mm_proc_mem (mmD_get_mem hp) with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · cases he
    · cases he
    · exact ⟨_, ctrl_run N W F (by omega) _ _ _⟩
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · cases he
      · exact ⟨_, peFF_run N W AccW i j F (by omega) _ _ _⟩
  · exact ffDisjB_of_pairwise (by simpa [mmD] using SvGolf.Cycle.procDisj_of_winDisj (mm_winDisj N W AccW))
  · show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "drain",
      "a_sh", "Ap", "b_sh", "Bp", "rs", "rc", "p0", "p1", "p2", "p3",
      "x1", "y1", "s2", "c2", "s4"] : List String).Nodup
    decide
  · intro j
    rw [SvGolf.Cycle.flatMap_ffUpd_all, mm_edgeQ N W AccW F (by omega),
      commit_regs (edgeQ_names N W AccW _ _ _)]
    exact settle_mm hN hW hF σ (appIns e ins) (nextRegs N W AccW (appIns e ins) reg)
      (wSet N W (appIns e ins) reg) (wdWires_wSet N W _ _) j

/-! ## Section 4: Arithmetic invariants and state transitions -/

attribute [local simp] condTrue_knownBit

theorem knownBit_false_eq : knownBit false = ⟨#[.l0]⟩ := by decide
theorem knownBit_true_eq : knownBit true = ⟨#[.l1]⟩ := by decide

@[simp] theorem width_knownBit' (b : Bool) : (knownBit b).width = 1 := by simp [knownBit]

theorem isKnownZero_knownBit (b : Bool) : (knownBit b).isKnownZero = !b := by
  cases b
  · rw [knownBit_false_eq, LVec.isKnownZero, ← Array.all_toList]; rfl
  · rw [knownBit_true_eq, LVec.isKnownZero, ← Array.all_toList]; rfl

theorem scmpLe4_known {N : Nat} (hN256 : N ≤ 256) : scmpLe4 N = knownBit (decide (N ≤ 4)) := by
  rw [scmpLe4_eq]
  have h1 : (BitVec.ofInt 32 (N : Int)).toInt = (N : Int) := by
    rw [BitVec.toInt_ofInt, int_bmod_eq_self] <;> (simp only [Nat.reducePow]; omega)
  have h2 : (BitVec.ofInt 32 4).toInt = 4 := by decide
  rw [h1, h2]
  by_cases h : N ≤ 4
  · simp [h, show (N : Int) ≤ 4 by omega, knownBit_true_eq, LVec.ofLogic]
  · simp [h, show ¬ ((N : Int) ≤ 4) by omega, knownBit_false_eq, LVec.ofLogic]

theorem scmpGt4_known {N : Nat} (hN256 : N ≤ 256) : scmpGt4 N = knownBit (decide (4 < N)) := by
  rw [scmpGt4_eq]
  have h1 : (BitVec.ofInt 32 (N : Int)).toInt = (N : Int) := by
    rw [BitVec.toInt_ofInt, int_bmod_eq_self] <;> (simp only [Nat.reducePow]; omega)
  have h2 : (BitVec.ofInt 32 4).toInt = 4 := by decide
  rw [h1, h2]
  by_cases h : 4 < N
  · simp [h, show (4 : Int) < N by omega, knownBit_true_eq, LVec.ofLogic]
  · simp [h, show ¬ ((4 : Int) < N) by omega, knownBit_false_eq, LVec.ofLogic]

theorem lorL_knownBit (a b : Bool) : lorL (knownBit a) (knownBit b) = knownBit (a || b) := by
  unfold lorL
  cases a <;> cases b <;>
    (simp only [condTrue_knownBit, isKnownZero_knownBit]; simp [LVec.ofLogic, knownBit_true_eq, knownBit_false_eq])

theorem landL_knownBit (a b : Bool) : landL (knownBit a) (knownBit b) = knownBit (a && b) := by
  unfold landL
  cases a <;> cases b <;>
    (simp only [condTrue_knownBit, isKnownZero_knownBit]; simp [LVec.ofLogic, knownBit_true_eq, knownBit_false_eq])

theorem ternary_knownBit (b : Bool) (t f : LVec) :
    LVec.ternary (knownBit b) t f = if b then t else f := by
  cases b <;> simp [LVec.ternary]

def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def chunk4 (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) +
  Tasks.Matmul.entry W A (i * N + (t + 1)) * Tasks.Matmul.entry W B ((t + 1) * N + j) +
  Tasks.Matmul.entry W A (i * N + (t + 2)) * Tasks.Matmul.entry W B ((t + 2) * N + j) +
  Tasks.Matmul.entry W A (i * N + (t + 3)) * Tasks.Matmul.entry W B ((t + 3) * N + j)

def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r => BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B (t + 1) i j =
      psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem psum_add4 (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B (t + 4) i j = psum N W A B t i j + chunk4 N W A B t i j := by
  have h1 : psum N W A B (t + 1) i j = _ := psum_succ N W A B t i j
  have h2 : psum N W A B (t + 2) i j = _ := psum_succ N W A B (t + 1) i j
  have h3 : psum N W A B (t + 3) i j = _ := psum_succ N W A B (t + 2) i j
  have h4 : psum N W A B (t + 4) i j = _ := psum_succ N W A B (t + 3) i j
  rw [h4, h3, h2, h1]; unfold chunk4; omega

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) :
    Tasks.Matmul.product N W AccW a b =
      packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

theorem entry_B_zero {N W : Nat} (B : BitVec (N * N * W)) {k j : Nat} (hk : N ≤ k) :
    Tasks.Matmul.entry W B (k * N + j) = 0 := by
  have h : N * N * W ≤ (k * N + j) * W := by
    have h1 : N * N ≤ k * N + j := by have := Nat.mul_le_mul_right N hk; omega
    exact Nat.mul_le_mul_right W h1
  have e : B.extractLsb' ((k * N + j) * W) W = 0#W := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_of_ge B ((k * N + j) * W + i) (by omega)]
  simp [Tasks.Matmul.entry, e]

theorem psum_ge (N W : Nat) (A B : BitVec (N * N * W)) (i j : Nat) :
    ∀ d, psum N W A B (N + d) i j = psum N W A B N i j
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc, psum_succ, psum_ge N W A B i j d, entry_B_zero B (by omega), Int.mul_zero, Int.add_zero]

theorem accC_ge (N W AccW : Nat) (A B : BitVec (N * N * W)) {t : Nat} (ht : N ≤ t) :
    accC N W AccW A B t = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  obtain ⟨d, rfl⟩ : ∃ d, t = N + d := ⟨t - N, by omega⟩
  rw [← accC_N]; simp only [accC, psum_ge]

def padA (N W : Nat) (A : BitVec (N * N * W)) : BitVec ((N * N + 3) * W) := A.setWidth ((N * N + 3) * W)
def padB (N W : Nat) (B : BitVec (N * N * W)) : BitVec ((N * N + 3 * N) * W) := B.setWidth ((N * N + 3 * N) * W)

theorem extractLsb'_setWidth_of_le {n n' : Nat} (h : n ≤ n') (x : BitVec n) (s l : Nat) :
    (x.setWidth n').extractLsb' s l = x.extractLsb' s l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hs : s + i < n
  · simp [hi, hs, show s + i < n' by omega]
  · simp [hi, BitVec.getLsbD_of_ge x (s + i) (by omega)]

theorem apV_ofBitVec (N W : Nat) (A : BitVec (N * N * W)) :
    apV N W (.ofBitVec A) = .ofBitVec (padA N W A) := by
  have hl0 : (⟨#[.l0]⟩ : LVec) = LVec.ofBitVec 0#1 := knownBit_false_eq.symm
  simp only [apV, hl0, LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
    LVec.concat_ofBitVec, LVec.resizeU_ofBitVec, padA]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < N * N * W
  · simp [BitVec.getLsbD_append, hi, h]
  · simp [BitVec.getLsbD_append, hi, h, BitVec.getLsbD_replicate, BitVec.getLsbD_of_ge A i (by omega)]

theorem bpV_ofBitVec (N W : Nat) (B : BitVec (N * N * W)) :
    bpV N W (.ofBitVec B) = .ofBitVec (padB N W B) := by
  have hl0 : (⟨#[.l0]⟩ : LVec) = LVec.ofBitVec 0#1 := knownBit_false_eq.symm
  simp only [bpV, hl0, LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
    LVec.concat_ofBitVec, LVec.resizeU_ofBitVec, padB]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases h : i < N * N * W
  · simp [BitVec.getLsbD_append, hi, h]
  · simp [BitVec.getLsbD_append, hi, h, BitVec.getLsbD_replicate, BitVec.getLsbD_of_ge B i (by omega)]

theorem ofBitVec_sext {W : Nat} (hW : 1 ≤ W) (m : Nat) (x : BitVec W) :
    LVec.ofBitVec (BitVec.replicate m (x.extractLsb' (W - 1) 1) ++ x) =
      LVec.ofBitVec (x.signExtend (m + W)) := by
  have hx : x.extractLsb' 0 W = x := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  have h := LVec.ofBitVec_replicate_append_eq_signExtend (p := W - 1) (lo := 0) (W := W) hW x m (by omega)
  simpa [hx] using h

private theorem ofBitVec_signExtend_congr {w m n : Nat} (h : m = n) (x : BitVec w) :
    LVec.ofBitVec (x.signExtend m) = LVec.ofBitVec (x.signExtend n) := by
  subst h; rfl

/-- The 4:2 CSA pair-sum invariant for `(rs, rc)` holding chunk `t..t+3`. -/
def PairSum (N W : Nat) (A B : BitVec (N * N * W)) (t : Nat) (rs rc : LVec) : Prop :=
  ∃ rsB rcB : BitVec (N * N * (2 * W + 2)),
    rs = .ofBitVec rsB ∧ rc = .ofBitVec rcB ∧
    ∀ i j, i < N → j < N →
      rsB.extractLsb' ((i * N + j) * (2 * W + 2)) (2 * W + 2) +
      rcB.extractLsb' ((i * N + j) * (2 * W + 2)) (2 * W + 2) =
      BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)

theorem toInt_chunk4 {N W : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) (t i j : Nat) :
    (BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)).toInt = chunk4 N W A B t i j := by
  exact toInt_ofInt_sum4 hW
    (A.extractLsb' ((i * N + t) * W) W) (B.extractLsb' ((t * N + j) * W) W)
    (A.extractLsb' ((i * N + (t + 1)) * W) W) (B.extractLsb' (((t + 1) * N + j) * W) W)
    (A.extractLsb' ((i * N + (t + 2)) * W) W) (B.extractLsb' (((t + 2) * N + j) * W) W)
    (A.extractLsb' ((i * N + (t + 3)) * W) W) (B.extractLsb' (((t + 3) * N + j) * W) W)

theorem s4V_of_pairSum {N W i j t : Nat} {A B : BitVec (N * N * W)} {rs rc : LVec}
    (hp : PairSum N W A B t rs rc) (hi : i < N) (hj : j < N) :
    s4V N W i j rs rc = LVec.ofBitVec (BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)) := by
  obtain ⟨rsB, rcB, rfl, rfl, hsum⟩ := hp
  have hS := winRM_le (K := 2 * W + 2) hi hj
  simp (disch := omega) only [s4V, LVec.extract_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec,
    BitVec.setWidth_eq, hsum i j hi hj]

theorem setCV_of_pairSum {N W AccW i j t : Nat} (hW : 1 ≤ W) {A B : BitVec (N * N * W)}
    {ins : MIns} {reg : MRegs} (hp : PairSum N W A B t reg.rs reg.rc) (hi : i < N) (hj : j < N) :
    setCV N W AccW i j (wSet N W ins reg).s4 =
      LVec.ofBitVec (BitVec.ofInt AccW (chunk4 N W A B t i j)) := by
  have hs4 : (wSet N W ins reg).s4.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2) =
      LVec.ofBitVec (BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)) := by
    rw [show (wSet N W ins reg).s4 = packGrid (2 * W + 2) N (fun a b => s4V N W a b reg.rs reg.rc) from rfl,
      packGrid_extract (fun _ _ => width_s4V ..) hi hj, s4V_of_pairSum hp hi hj]
  have hs4b : (wSet N W ins reg).s4.extract ((i * N + j) * (2 * W + 2) + (2 * W + 2) - 1) 1 =
      LVec.ofBitVec ((BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)).extractLsb' (2 * W + 2 - 1) 1) := by
    have h1 := LVec.extract_extract (wSet N W ins reg).s4 (lo := (i * N + j) * (2 * W + 2)) (w := 2 * W + 2)
      (lo' := 2 * W + 2 - 1) (w' := 1) (by omega)
    rw [hs4, LVec.extract_ofBitVec _ (by omega)] at h1
    rw [show (i * N + j) * (2 * W + 2) + (2 * W + 2) - 1 = (i * N + j) * (2 * W + 2) + (2 * W + 2 - 1) by omega, ← h1]
  simp only [setCV, sxAccV, hs4, hs4b, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, ofBitVec_sext (by omega : 1 ≤ 2 * W + 2),
    LVec.resizeU_ofBitVec, setWidth_signExtend_add_sw, toInt_chunk4 hW]

theorem addCV_of_pairSum {N W AccW i j t : Nat} (hW : 1 ≤ W) {A B : BitVec (N * N * W)}
    {ins : MIns} {reg : MRegs} (hp : PairSum N W A B t reg.rs reg.rc) (hi : i < N) (hj : j < N) :
    addCV N W AccW i j (accC N W AccW A B t) (wSet N W ins reg).s4 =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 4) i j)) := by
  have hs4 : (wSet N W ins reg).s4.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2) =
      LVec.ofBitVec (BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)) := by
    rw [show (wSet N W ins reg).s4 = packGrid (2 * W + 2) N (fun a b => s4V N W a b reg.rs reg.rc) from rfl,
      packGrid_extract (fun _ _ => width_s4V ..) hi hj, s4V_of_pairSum hp hi hj]
  have hs4b : (wSet N W ins reg).s4.extract ((i * N + j) * (2 * W + 2) + (2 * W + 2) - 1) 1 =
      LVec.ofBitVec ((BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)).extractLsb' (2 * W + 2 - 1) 1) := by
    have h1 := LVec.extract_extract (wSet N W ins reg).s4 (lo := (i * N + j) * (2 * W + 2)) (w := 2 * W + 2)
      (lo' := 2 * W + 2 - 1) (w' := 1) (by omega)
    rw [hs4, LVec.extract_ofBitVec _ (by omega)] at h1
    rw [show (i * N + j) * (2 * W + 2) + (2 * W + 2) - 1 = (i * N + j) * (2 * W + 2) + (2 * W + 2 - 1) by omega, ← h1]
  have hC := winRM_le (K := AccW) hi hj
  have hrm := rm_lt hi hj
  simp (disch := omega) only [addCV, sxAccV, accC, hs4, hs4b, LVec.extract_ofBitVec, extractLsb'_packBV,
    rm_div hj, rm_mod hj, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, ofBitVec_sext (by omega : 1 ≤ 2 * W + 2),
    LVec.resizeU_ofBitVec, LVec.add_ofBitVec, setWidth_add_signExtend_sw, toInt_chunk4 hW,
    ← BitVec.ofInt_add, psum_add4]

theorem packGrid_ofBitVec {E N : Nat} (f : Nat → Nat → BitVec E) :
    packGrid E N (fun i j => LVec.ofBitVec (f i j)) =
      LVec.ofBitVec (packBV E (N * N) fun r => f (r / N) (r % N)) := by
  unfold packGrid
  exact LVec.insertEntries_ofBitVec (fun r => f (r / N) (r % N)) (LVec.xVec (N * N * E)) (by simp)

/-- Evaluated 4:2 CSA outputs `(s2, c2)` on shifted `padA, padB` satisfy `PairSum N W A B t`. -/
theorem wSet_csa_pairSum {N W t : Nat} (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W)
    (A B : BitVec (N * N * W)) {ins : MIns} {reg : MRegs} {bs : Bool}
    (hs : ins.s = knownBit bs)
    (hsrc : (bs || decide (N ≤ 4)) = true ∧ t = 0 ∧ ins.a = .ofBitVec A ∧ ins.b = .ofBitVec B ∨
            (bs || decide (N ≤ 4)) = false ∧ reg.ash = .ofBitVec (padA N W A >>> (t * W)) ∧
              reg.bsh = .ofBitVec (padB N W B >>> (t * (N * W)))) :
    PairSum N W A B t (wSet N W ins reg).s2 (wSet N W ins reg).c2 := by
  have hcond : lorL ins.s (scmpLe4 N) = knownBit (bs || decide (N ≤ 4)) := by
    rw [hs, scmpLe4_known hN256, lorL_knownBit]
  let aBV (m i : Nat) : BitVec W := A.extractLsb' ((i * N + (t + m)) * W) W
  let bBV (m j : Nat) : BitVec W := B.extractLsb' (((t + m) * N + j) * W) W
  let pBV (m i j : Nat) : BitVec (2 * W) := (aBV m i).signExtend (2 * W) * (bBV m j).signExtend (2 * W)
  let eBV (m i j : Nat) : BitVec (2 * W + 2) := (pBV m i j).signExtend (2 * W + 2)
  let x1BV (i j : Nat) : BitVec (2 * W + 2) := eBV 0 i j ^^^ eBV 1 i j ^^^ eBV 2 i j
  let y1BV (i j : Nat) : BitVec (2 * W + 2) :=
    ((eBV 0 i j &&& eBV 1 i j) ||| (eBV 0 i j &&& eBV 2 i j) ||| (eBV 1 i j &&& eBV 2 i j)) <<< 1
  let s2BV (i j : Nat) : BitVec (2 * W + 2) := x1BV i j ^^^ y1BV i j ^^^ eBV 3 i j
  let c2BV (i j : Nat) : BitVec (2 * W + 2) :=
    ((x1BV i j &&& y1BV i j) ||| (x1BV i j &&& eBV 3 i j) ||| (y1BV i j &&& eBV 3 i j)) <<< 1
  have hpm : ∀ m, m ≤ 3 → ∀ i j, i < N → j < N →
      pmV N W m i j ins.s (wSet N W ins reg).ap (wSet N W ins reg).bp reg.ash reg.bsh =
        LVec.ofBitVec (pBV m i j) := by
    intro m hm i j hi hj
    have hwa := winA_le (N := N) (W := W) (i := i) m hm hi
    have hwb := winB_le (N := N) (W := W) (j := j) m hm hj
    have hpA : N * N * W ≤ (N * N + 3) * W := Nat.mul_le_mul_right W (by omega)
    have hpB : N * N * W ≤ (N * N + 3 * N) * W := Nat.mul_le_mul_right W (by omega)
    have eA : t * W + (i * N + m) * W = (i * N + (t + m)) * W := by rw [← Nat.add_mul]; congr 1; omega
    have eB : t * (N * W) + (m * N + j) * W = ((t + m) * N + j) * W := by
      simp only [Nat.add_mul, Nat.mul_assoc]; omega
    have h2W : W + W = 2 * W := by omega
    rcases hsrc with ⟨hc, rfl, ha, hb⟩ | ⟨hc, hash, hbsh⟩
    · simp (disch := omega) only [pmV, sextSelV, hcond, hc, ternary_knownBit, ↓reduceIte, wSet, ha, hb,
        apV_ofBitVec, bpV_ofBitVec, LVec.extract_ofBitVec,
        LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
        LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
        LVec.mul_ofBitVec, LVec.resizeU_ofBitVec,
        BitVec.setWidth_mul _ _ (show 2 * W ≤ W + W by omega),
        Lib.setWidth_signExtend_of_le _ (show 2 * W ≤ W + W by omega),
        padA, padB, extractLsb'_setWidth_of_le, pBV, aBV, bBV, Nat.zero_add]
    · simp (disch := omega) only [pmV, sextSelV, hcond, hc, ternary_knownBit, Bool.false_eq_true, ↓reduceIte,
        hash, hbsh, LVec.extract_ofBitVec,
        LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
        LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
        LVec.mul_ofBitVec, LVec.resizeU_ofBitVec,
        BitVec.setWidth_mul _ _ (show 2 * W ≤ W + W by omega),
        Lib.setWidth_signExtend_of_le _ (show 2 * W ≤ W + W by omega),
        Lib.extractLsb'_ushiftRight, padA, padB, extractLsb'_setWidth_of_le, eA, eB, pBV, aBV, bBV]
  have hp_grid : ∀ m, m ≤ 3 →
      packGrid (2 * W) N (fun i j => pmV N W m i j ins.s (wSet N W ins reg).ap (wSet N W ins reg).bp reg.ash reg.bsh) =
        LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV m (r / N) (r % N)) := fun m hm => by
    rw [← packGrid_ofBitVec (pBV m)]
    refine eq_packGrid hN (fun _ _ => by simp) (width_packGrid ..) fun i j hi hj => ?_
    rw [packGrid_extract (fun _ _ => width_pmV ..) hi hj, hpm m hm i j hi hj]
  have hp0 : (wSet N W ins reg).p0 = LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV 0 (r / N) (r % N)) := hp_grid 0 (by omega)
  have hp1 : (wSet N W ins reg).p1 = LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV 1 (r / N) (r % N)) := hp_grid 1 (by omega)
  have hp2 : (wSet N W ins reg).p2 = LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV 2 (r / N) (r % N)) := hp_grid 2 (by omega)
  have hp3 : (wSet N W ins reg).p3 = LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV 3 (r / N) (r % N)) := hp_grid 3 (by omega)
  have hsext2 : ∀ (m i j : Nat) (v : LVec), i < N → j < N →
      v = LVec.ofBitVec (packBV (2 * W) (N * N) fun r => pBV m (r / N) (r % N)) →
      sext2V v ((i * N + j) * (2 * W)) (2 * W) = LVec.ofBitVec (eBV m i j) := by
    intro m i j v hi hj hv
    have hloP := winRM_le (K := 2 * W) hi hj
    have hrm := rm_lt hi hj
    have h2sw : 2 + 2 * W = 2 * W + 2 := by omega
    have hbit : (packBV (2 * W) (N * N) fun r => pBV m (r / N) (r % N)).extractLsb' ((i * N + j) * (2 * W) + 2 * W - 1) 1 =
        (pBV m i j).extractLsb' (2 * W - 1) 1 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      obtain rfl : k = 0 := by omega
      have hpe := extractLsb'_packBV (fun r => pBV m (r / N) (r % N)) hrm
      rw [rm_div hj, rm_mod hj] at hpe
      have hgb := congrArg (fun bv : BitVec (2 * W) => bv.getLsbD (2 * W - 1)) hpe
      simpa [BitVec.getLsbD_extractLsb', show 2 * W - 1 < 2 * W by omega,
        show (i * N + j) * (2 * W) + (2 * W - 1) = (i * N + j) * (2 * W) + 2 * W - 1 by omega] using hgb
    rw [hv]
    simp (disch := omega) only [sext2V, LVec.extract_ofBitVec,
      extractLsb'_packBV, rm_div hj, rm_mod hj, hbit,
      LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
      LVec.concat_ofBitVec, ofBitVec_sext (by omega : 1 ≤ 2 * W), eBV]
    exact ofBitVec_signExtend_congr h2sw _
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  have hx1_eq : (wSet N W ins reg).x1 = LVec.ofBitVec (packBV (2 * W + 2) (N * N) fun r => x1BV (r / N) (r % N)) := by
    rw [← packGrid_ofBitVec x1BV]
    have hx1w : (wSet N W ins reg).x1 = packGrid (2 * W + 2) N (fun a b => x1V N W a b (wSet N W ins reg).p0 (wSet N W ins reg).p1 (wSet N W ins reg).p2) := rfl
    rw [hx1w]
    refine eq_packGrid hN (fun _ _ => by simp) (width_packGrid ..) fun i j hi hj => ?_
    rw [packGrid_extract (fun _ _ => width_x1V ..) hi hj]
    simp only [x1V, hsext2 0 i j _ hi hj hp0, hsext2 1 i j _ hi hj hp1, hsext2 2 i j _ hi hj hp2,
      LVec.xor_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, x1BV]
  have hy1_eq : (wSet N W ins reg).y1 = LVec.ofBitVec (packBV (2 * W + 2) (N * N) fun r => y1BV (r / N) (r % N)) := by
    rw [← packGrid_ofBitVec y1BV]
    have hy1w : (wSet N W ins reg).y1 = packGrid (2 * W + 2) N (fun a b => y1V N W a b (wSet N W ins reg).p0 (wSet N W ins reg).p1 (wSet N W ins reg).p2) := rfl
    rw [hy1w]
    refine eq_packGrid hN (fun _ _ => by simp) (width_packGrid ..) fun i j hi hj => ?_
    rw [packGrid_extract (fun _ _ => width_y1V ..) hi hj]
    simp only [y1V, hsext2 0 i j _ hi hj hp0, hsext2 1 i j _ hi hj hp1, hsext2 2 i j _ hi hj hp2,
      h1', LVec.and_ofBitVec, LVec.or_ofBitVec, LVec.shl_ofBitVec, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq, y1BV]
    rfl
  have hs2_eq : (wSet N W ins reg).s2 = LVec.ofBitVec (packBV (2 * W + 2) (N * N) fun r => s2BV (r / N) (r % N)) := by
    rw [← packGrid_ofBitVec s2BV]
    have hs2w : (wSet N W ins reg).s2 = packGrid (2 * W + 2) N (fun a b => s2V N W a b (wSet N W ins reg).x1 (wSet N W ins reg).y1 (wSet N W ins reg).p3) := rfl
    rw [hs2w]
    refine eq_packGrid hN (fun _ _ => by simp) (width_packGrid ..) fun i j hi hj => ?_
    have hloS := winRM_le (K := 2 * W + 2) hi hj
    have hrm := rm_lt hi hj
    rw [packGrid_extract (fun _ _ => width_s2V ..) hi hj]
    simp (disch := omega) only [s2V, hx1_eq, hy1_eq, hsext2 3 i j _ hi hj hp3,
      LVec.extract_ofBitVec, extractLsb'_packBV, rm_div hj, rm_mod hj,
      LVec.xor_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, s2BV]
  have hc2_eq : (wSet N W ins reg).c2 = LVec.ofBitVec (packBV (2 * W + 2) (N * N) fun r => c2BV (r / N) (r % N)) := by
    rw [← packGrid_ofBitVec c2BV]
    have hc2w : (wSet N W ins reg).c2 = packGrid (2 * W + 2) N (fun a b => c2V N W a b (wSet N W ins reg).x1 (wSet N W ins reg).y1 (wSet N W ins reg).p3) := rfl
    rw [hc2w]
    refine eq_packGrid hN (fun _ _ => by simp) (width_packGrid ..) fun i j hi hj => ?_
    have hloS := winRM_le (K := 2 * W + 2) hi hj
    have hrm := rm_lt hi hj
    rw [packGrid_extract (fun _ _ => width_c2V ..) hi hj]
    simp (disch := omega) only [c2V, hx1_eq, hy1_eq, hsext2 3 i j _ hi hj hp3, h1',
      LVec.extract_ofBitVec, extractLsb'_packBV, rm_div hj, rm_mod hj,
      LVec.and_ofBitVec, LVec.or_ofBitVec, LVec.shl_ofBitVec, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq, c2BV]
    rfl
  refine ⟨_, _, hs2_eq, hc2_eq, fun i j hi hj => ?_⟩
  have hrm := rm_lt hi hj
  rw [extractLsb'_packBV _ hrm, extractLsb'_packBV _ hrm, rm_div hj, rm_mod hj]
  show s2BV i j + c2BV i j = BitVec.ofInt (2 * W + 2) (chunk4 N W A B t i j)
  rw [csa42_add (eBV 0 i j) (eBV 1 i j) (eBV 2 i j) (eBV 3 i j)]
  simpa [eBV, pBV, aBV, bBV, chunk4, Tasks.Matmul.entry] using
    signExtend_add4_exact hW (aBV 0 i) (bBV 0 j) (aBV 1 i) (bBV 1 j) (aBV 2 i) (bBV 2 j) (aBV 3 i) (bBV 3 j)

/-! ### Section 4b: Register fold helpers and cycle transitions -/

theorem nbaFold_append (s : String) (q1 q2 : NbaQueue2) (v : LVec) :
    nbaFold s (q1 ++ q2) v = nbaFold s q2 (nbaFold s q1 v) := by
  simp [nbaFold, List.foldl_append]

theorem nbaFold_disj (s : String) : ∀ (q : NbaQueue2) (v : LVec),
    (∀ u ∈ q, u.1 ≠ s) → nbaFold s q v = v
  | [], _, _ => rfl
  | u :: q, v, h => by
    rw [nbaFold_cons, ite_eq_right (h u List.mem_cons_self)]
    exact nbaFold_disj s q v fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem ctrlQ_not_pe (N W : Nat) (ins : MIns) (reg : MRegs) (w : MWires) :
    ∀ u ∈ ctrlQ N W ins reg w, u.1 ≠ "rs" ∧ u.1 ≠ "rc" ∧ u.1 ≠ "C" := by
  intro u hu; unfold ctrlQ at hu
  split at hu
  · simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl <;> simp
  · split at hu
    · split at hu <;> (simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    · split at hu
      · split at hu <;> (simp [wr] at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp)
      · split at hu
        · simp [wr] at hu; rcases hu with rfl | rfl <;> simp
        · simp at hu

theorem allPeFFQ_not_ctrl (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires) :
    ∀ u ∈ allPeFFQ N W AccW ins reg w,
      u.1 ≠ "done" ∧ u.1 ≠ "k" ∧ u.1 ≠ "busy" ∧ u.1 ≠ "drain" ∧ u.1 ≠ "a_sh" ∧ u.1 ≠ "b_sh" := by
  intro u hu
  simp only [allPeFFQ, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  unfold peFFQ at hu
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with (rfl | rfl) | hu
  · simp
  · simp
  · split at hu
    · simp at hu; rw [hu]; simp
    · split at hu
      · simp at hu; rw [hu]; simp
      · split at hu
        · split at hu <;> (simp at hu; rw [hu]; simp)
        · simp at hu

theorem nbaFold_edgeQ_ctrl (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires)
    (s : String) (hs : s = "done" ∨ s = "k" ∨ s = "busy" ∨ s = "drain" ∨ s = "a_sh" ∨ s = "b_sh") (v : LVec) :
    nbaFold s (edgeQ N W AccW ins reg w) v = nbaFold s (ctrlQ N W ins reg w) v := by
  rw [edgeQ, nbaFold_append, nbaFold_disj]
  intro u hu
  have h := allPeFFQ_not_ctrl N W AccW ins reg w u hu
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h]

theorem nbaFold_edgeQ_pe (N W AccW : Nat) (ins : MIns) (reg : MRegs) (w : MWires)
    (s : String) (hs : s = "rs" ∨ s = "rc" ∨ s = "C") (v : LVec) :
    nbaFold s (edgeQ N W AccW ins reg w) v = nbaFold s (allPeFFQ N W AccW ins reg w) v := by
  rw [edgeQ, nbaFold_append]
  have h1 : nbaFold s (ctrlQ N W ins reg w) v = v := by
    refine nbaFold_disj _ _ _ fun u hu => ?_
    have h := ctrlQ_not_pe N W ins reg w u hu
    rcases hs with rfl | rfl | rfl <;> simp [h]
  rw [h1]

theorem nbaFold_insertEntries_rowMajor {N E : Nat} (s : String) {f : Nat → Nat → NbaQueue2}
    (g : Nat → LVec) (h : ∀ i j, i < N → j < N →
      ∀ v, nbaFold s (f i j) v = v.insertAt ((i * N + j) * E) (g (i * N + j))) :
    ∀ v, nbaFold s ((List.range N).flatMap fun i => (List.range N).flatMap (f i)) v =
      LVec.insertEntries E g (N * N) v := by
  suffices ∀ M, M ≤ N → ∀ v,
      nbaFold s ((List.range M).flatMap fun i => (List.range N).flatMap (f i)) v =
        LVec.insertEntries E g (M * N) v from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _ v; simp [nbaFold, LVec.insertEntries]
  | succ M ih =>
    intro hM v
    rw [List.range_succ, List.flatMap_append, nbaFold_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hinner : ∀ K, K ≤ N → ∀ u,
        nbaFold s ((List.range K).flatMap (f M)) u =
          (List.range K).foldl (fun acc j => acc.insertAt ((M * N + j) * E) (g (M * N + j))) u := by
      intro K; induction K with
      | zero => intro _ u; rfl
      | succ K ihK =>
        intro hK u
        rw [List.range_succ, List.flatMap_append, nbaFold_append, ihK (by omega)]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact h M K (by omega) (by omega) _
    rw [hinner N (Nat.le_refl _), Nat.succ_mul]
    unfold LVec.insertEntries
    rw [List.range_add, List.foldl_append, List.foldl_map]

theorem nbaFold_noop_rowMajor {N : Nat} (s : String) {f : Nat → Nat → NbaQueue2}
    (h : ∀ i j, i < N → j < N → ∀ v, nbaFold s (f i j) v = v) :
    ∀ v, nbaFold s ((List.range N).flatMap fun i => (List.range N).flatMap (f i)) v = v := by
  suffices ∀ M, M ≤ N → ∀ v,
      nbaFold s ((List.range M).flatMap fun i => (List.range N).flatMap (f i)) v = v from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _ v; rfl
  | succ M ih =>
    intro hM v
    rw [List.range_succ, List.flatMap_append, nbaFold_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    suffices ∀ K, K ≤ N → ∀ u, nbaFold s ((List.range K).flatMap (f M)) u = u from this N (Nat.le_refl _) v
    intro K; induction K with
    | zero => intro _ u; rfl
    | succ K ihK =>
      intro hK u
      rw [List.range_succ, List.flatMap_append, nbaFold_append, ihK (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact h M K (by omega) (by omega) u

theorem insertEntries_self_extract {E n : Nat} {u v : LVec}
    (hu : u.width = n * E) (hv : v.width = n * E) :
    LVec.insertEntries E (fun r => u.extract (r * E) E) n v = u := by
  refine eq_of_chunks (by simp [hv]) hu fun r hr => ?_
  exact LVec.extract_insertEntries (E := E) (g := fun r => u.extract (r * E) E)
    (fun _ => by simp) v n (by omega) r hr

theorem resizeU_self (v : LVec) : v.resizeU v.width = v := by
  apply LVec.ext_getElem?; intro i
  simp only [LVec.resizeU, LVec.width, Array.getElem?_ofFn]
  by_cases hi : i < v.bits.size <;> simp [hi]

theorem nextRegs_rs {N W AccW : Nat} (ins : MIns) (reg : MRegs) (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).rs = (wSet N W ins reg).s2 := by
  simp only [nextRegs]
  rw [nbaFold_edgeQ_pe N W AccW ins reg _ "rs" (.inl rfl)]
  have h1 : ∀ i j, i < N → j < N → ∀ v,
      nbaFold "rs" (peFFQ N W AccW ins reg (wSet N W ins reg) i j) v =
        v.insertAt ((i * N + j) * (2 * W + 2)) ((wSet N W ins reg).s2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2)) := by
    intro i j _ _ v
    unfold peFFQ
    rw [nbaFold_append, nbaFold_disj "rs" _ _ (fun u hu => by
      split at hu
      · simp at hu; rw [hu]; simp
      · split at hu
        · simp at hu; rw [hu]; simp
        · split at hu
          · split at hu <;> (simp at hu; rw [hu]; simp)
          · simp at hu)]
    have hre : ((wSet N W ins reg).s2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2)).resizeU (2 * W + 2) =
        (wSet N W ins reg).s2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2) := by
      simpa using resizeU_self ((wSet N W ins reg).s2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2))
    simp [nbaFold, hre]
  rw [allPeFFQ, nbaFold_insertEntries_rowMajor (E := 2 * W + 2) "rs"
    (fun r => (wSet N W ins reg).s2.extract (r * (2 * W + 2)) (2 * W + 2)) h1]
  exact insertEntries_self_extract (wdWires_wSet N W ins reg).2.2.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2.1

theorem nextRegs_rc {N W AccW : Nat} (ins : MIns) (reg : MRegs) (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).rc = (wSet N W ins reg).c2 := by
  simp only [nextRegs]
  rw [nbaFold_edgeQ_pe N W AccW ins reg _ "rc" (.inr (.inl rfl))]
  have h1 : ∀ i j, i < N → j < N → ∀ v,
      nbaFold "rc" (peFFQ N W AccW ins reg (wSet N W ins reg) i j) v =
        v.insertAt ((i * N + j) * (2 * W + 2)) ((wSet N W ins reg).c2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2)) := by
    intro i j _ _ v
    unfold peFFQ
    rw [nbaFold_append, nbaFold_disj "rc" _ _ (fun u hu => by
      split at hu
      · simp at hu; rw [hu]; simp
      · split at hu
        · simp at hu; rw [hu]; simp
        · split at hu
          · split at hu <;> (simp at hu; rw [hu]; simp)
          · simp at hu)]
    have hre : ((wSet N W ins reg).c2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2)).resizeU (2 * W + 2) =
        (wSet N W ins reg).c2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2) := by
      simpa using resizeU_self ((wSet N W ins reg).c2.extract ((i * N + j) * (2 * W + 2)) (2 * W + 2))
    simp [nbaFold, hre]
  rw [allPeFFQ, nbaFold_insertEntries_rowMajor (E := 2 * W + 2) "rc"
    (fun r => (wSet N W ins reg).c2.extract (r * (2 * W + 2)) (2 * W + 2)) h1]
  exact insertEntries_self_extract (wdWires_wSet N W ins reg).2.2.2.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2.2

theorem toNat_mul_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hab : a * b < 2 ^ w) :
    (BitVec.ofNat w a * BitVec.ofNat w b).toNat = a * b := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hab]

theorem toNat_mul3_lt {w a b c : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w)
    (hab : a * b < 2 ^ w) (habc : a * b * c < 2 ^ w) :
    (BitVec.ofNat w a * BitVec.ofNat w b * BitVec.ofNat w c).toNat = a * b * c := by
  rw [BitVec.toNat_mul, toNat_mul_lt ha hb hab, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt habc]

theorem shA_ofBitVec {W n : Nat} (hW127 : W ≤ 127) (v : BitVec n) :
    shA W (.ofBitVec v) = .ofBitVec (v >>> (4 * W)) := by
  have h2' : LVec.ofInt 32 2 = LVec.ofBitVec 2#32 := by decide
  have hyW : (BitVec.ofNat 32 2 * BitVec.ofNat 32 W).toNat = 2 * W :=
    toNat_mul_lt (by decide) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  simp only [shA, h2', LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.mul_ofBitVec,
    LVec.shr_ofBitVec, hyW, ← BitVec.shiftRight_add]
  congr 2; omega

theorem shB_ofBitVec {N W n : Nat} (hN256 : N ≤ 256) (hW127 : W ≤ 127) (v : BitVec n) :
    shB N W (.ofBitVec v) = .ofBitVec (v >>> (4 * (N * W))) := by
  have h2' : LVec.ofInt 32 2 = LVec.ofBitVec 2#32 := by decide
  have h2NW : 2 * N * W < 2 ^ 32 := by
    have : 2 * N * W ≤ 2 * 256 * 127 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hN256) hW127
    simp only [Nat.reducePow]; omega
  have hyNW : (BitVec.ofNat 32 2 * BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = 2 * N * W :=
    toNat_mul3_lt (by decide) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
      (by simp only [Nat.reducePow]; omega) h2NW
  simp only [shB, h2', LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.mul_ofBitVec,
    LVec.shr_ofBitVec, hyNW, ← BitVec.shiftRight_add]
  congr 2; rw [Nat.mul_assoc]; omega

theorem ge_four_iff {t N : Nat} (ht : t < N) (hN256 : N ≤ 256) :
    BitVec.ofNat 32 N ≤ BitVec.ofNat 32 t + 4#32 ↔ N ≤ t + 4 := by
  rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]; omega

/-! ### Cycle transitions on `nextRegs` -/

theorem next_reset {N W AccW : Nat} {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit true) (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).dn = knownBit false ∧
    (nextRegs N W AccW ins reg).bz = knownBit false ∧
    (nextRegs N W AccW ins reg).dr = knownBit false := by
  have hl0 : (⟨#[.l0]⟩ : LVec) = knownBit false := knownBit_false_eq.symm
  obtain ⟨hdn, -, -, hbz, hdr, -, -, -, -⟩ := hw
  simp only [nextRegs]
  rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl),
      nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl))),
      nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
  simp [ctrlQ, hr, wr, hdn, hbz, hdr, nbaFold, LVec.resizeU_one_l0, hl0,
    LVec.insertAt_zero_of_width_eq]

theorem next_idle {N W AccW : Nat} (hN256 : N ≤ 256) {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit false) (hs : ins.s = knownBit false)
    (hbz : reg.bz = knownBit false) (hdr : reg.dr = knownBit false) :
    (nextRegs N W AccW ins reg).dn = reg.dn ∧
    (nextRegs N W AccW ins reg).c = reg.c ∧
    (nextRegs N W AccW ins reg).bz = knownBit false ∧
    (nextRegs N W AccW ins reg).dr = knownBit false := by
  simp only [nextRegs]
  rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl),
      nbaFold_edgeQ_pe N W AccW ins reg _ "C" (.inr (.inr rfl)),
      nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl))),
      nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
  have hc0 : ctrlQ N W ins reg (wSet N W ins reg) = [] := by
    simp [ctrlQ, hr, hs, hbz, hdr, scmpGt4_known hN256, landL_knownBit]
  have hC : nbaFold "C" (allPeFFQ N W AccW ins reg (wSet N W ins reg)) reg.c = reg.c := by
    rw [allPeFFQ]
    refine nbaFold_noop_rowMajor "C" (fun i j _ _ v => ?_) reg.c
    simp [peFFQ, hs, hbz, hdr, scmpGt4_known hN256, landL_knownBit, nbaFold]
  rw [hc0, hC]
  simp [hbz, hdr, nbaFold]

theorem next_start_le4 {N W AccW : Nat} (hN : 1 ≤ N) (hN4 : N ≤ 4) (hW : 1 ≤ W)
    (A B : BitVec (N * N * W)) {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit false) (hs : ins.s = knownBit true)
    (ha : ins.a = .ofBitVec A) (hb : ins.b = .ofBitVec B) (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).dn = knownBit false ∧
    (nextRegs N W AccW ins reg).bz = knownBit false ∧
    (nextRegs N W AccW ins reg).dr = knownBit true ∧
    PairSum N W A B 0 (nextRegs N W AccW ins reg).rs (nextRegs N W AccW ins reg).rc := by
  have hN256 : N ≤ 256 := by omega
  have hl0 : (⟨#[.l0]⟩ : LVec) = knownBit false := knownBit_false_eq.symm
  have hl1 : (⟨#[.l1]⟩ : LVec) = knownBit true := knownBit_true_eq.symm
  have hw0 := hw
  obtain ⟨hdn, -, -, hbz, hdr, -, -, -, -⟩ := hw0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl)]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hN4, wr, hdn, nbaFold, LVec.resizeU_one_l0,
      hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl)))]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hN4, wr, hbz, nbaFold, LVec.resizeU_one_l0,
      hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hN4, wr, hdr, nbaFold, LVec.resizeU_one_l1,
      hl1, LVec.insertAt_zero_of_width_eq]
  · rw [nextRegs_rs ins reg hw, nextRegs_rc ins reg hw]
    exact wSet_csa_pairSum hN hN256 hW A B hs (.inl ⟨by simp, rfl, ha, hb⟩)

theorem next_start_gt4 {N W AccW : Nat} (hN4 : 4 < N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (A B : BitVec (N * N * W)) {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit false) (hs : ins.s = knownBit true)
    (ha : ins.a = .ofBitVec A) (hb : ins.b = .ofBitVec B) (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).dn = knownBit false ∧
    (nextRegs N W AccW ins reg).bz = knownBit true ∧
    (nextRegs N W AccW ins reg).dr = knownBit false ∧
    (nextRegs N W AccW ins reg).k = .ofBitVec (BitVec.ofNat 32 4) ∧
    (nextRegs N W AccW ins reg).ash = .ofBitVec (padA N W A >>> (4 * W)) ∧
    (nextRegs N W AccW ins reg).bsh = .ofBitVec (padB N W B >>> (4 * (N * W))) ∧
    (nextRegs N W AccW ins reg).c = accC N W AccW A B 0 ∧
    PairSum N W A B 0 (nextRegs N W AccW ins reg).rs (nextRegs N W AccW ins reg).rc := by
  have hN : 1 ≤ N := by omega
  have hnot4 : ¬ (N ≤ 4) := by omega
  have hl0 : (⟨#[.l0]⟩ : LVec) = knownBit false := knownBit_false_eq.symm
  have hl1 : (⟨#[.l1]⟩ : LVec) = knownBit true := knownBit_true_eq.symm
  have hw0 := hw
  obtain ⟨hdn, hc, hk, hbz, hdr, hash, hbsh, -, -⟩ := hw0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl)]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, wr, hdn, nbaFold, LVec.resizeU_one_l0,
      hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl)))]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, wr, hbz, nbaFold, LVec.resizeU_one_l1,
      hl1, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, wr, hdr, nbaFold, LVec.resizeU_one_l0,
      hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "k" (.inr (.inl rfl))]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, wr, hk, nbaFold,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "a_sh" (.inr (.inr (.inr (.inr (.inl rfl)))))]
    have hap : (wSet N W ins reg).ap = .ofBitVec (padA N W A) := by
      simp [wSet, ha, apV_ofBitVec]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, hap, shA_ofBitVec hW127, wr, hash, nbaFold,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "b_sh" (.inr (.inr (.inr (.inr (.inr rfl)))))]
    have hbp : (wSet N W ins reg).bp = .ofBitVec (padB N W B) := by
      simp [wSet, hb, bpV_ofBitVec]
    simp [ctrlQ, hr, hs, scmpLe4_known hN256, hnot4, hbp, shB_ofBitVec hN256 hW127, wr, hbsh, nbaFold,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_pe N W AccW ins reg _ "C" (.inr (.inr rfl)), allPeFFQ]
    have h1 : ∀ i j, i < N → j < N → ∀ v,
        nbaFold "C" (peFFQ N W AccW ins reg (wSet N W ins reg) i j) v =
          v.insertAt ((i * N + j) * AccW) (LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 ((i * N + j) / N) ((i * N + j) % N)))) := by
      intro i j _ _ v
      simp [peFFQ, hs, scmpGt4_known hN256, hN4, landL_knownBit, nbaFold, psum,
        LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [nbaFold_insertEntries_rowMajor (E := AccW) "C"
      (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N)))) h1,
      LVec.insertEntries_ofBitVec _ _ hc]
    rfl
  · rw [nextRegs_rs ins reg hw, nextRegs_rc ins reg hw]
    exact wSet_csa_pairSum hN hN256 hW A B hs (.inl ⟨by simp, rfl, ha, hb⟩)

theorem next_busy_gt4 {N W AccW j : Nat} (hN4 : 4 < N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hj1 : 1 ≤ j) (hjN : 4 * j < N)
    (A B : BitVec (N * N * W)) {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit false) (hs : ins.s = knownBit false)
    (hdn : reg.dn = knownBit false) (hbz : reg.bz = knownBit true) (hdr : reg.dr = knownBit false)
    (hk : reg.k = .ofBitVec (BitVec.ofNat 32 (4 * j)))
    (hash : reg.ash = .ofBitVec (padA N W A >>> (4 * j * W)))
    (hbsh : reg.bsh = .ofBitVec (padB N W B >>> (4 * j * (N * W))))
    (hc : reg.c = accC N W AccW A B (4 * (j - 1)))
    (hp : PairSum N W A B (4 * (j - 1)) reg.rs reg.rc)
    (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).dn = knownBit false ∧
    (nextRegs N W AccW ins reg).bz = knownBit (decide (¬ N ≤ 4 * j + 4)) ∧
    (nextRegs N W AccW ins reg).dr = knownBit (decide (N ≤ 4 * j + 4)) ∧
    (nextRegs N W AccW ins reg).k = .ofBitVec (BitVec.ofNat 32 (4 * (j + 1))) ∧
    (nextRegs N W AccW ins reg).ash = .ofBitVec (padA N W A >>> (4 * (j + 1) * W)) ∧
    (nextRegs N W AccW ins reg).bsh = .ofBitVec (padB N W B >>> (4 * (j + 1) * (N * W))) ∧
    (nextRegs N W AccW ins reg).c = accC N W AccW A B (4 * j) ∧
    PairSum N W A B (4 * j) (nextRegs N W AccW ins reg).rs (nextRegs N W AccW ins reg).rc := by
  have hN : 1 ≤ N := by omega
  have hl0 : (⟨#[.l0]⟩ : LVec) = knownBit false := knownBit_false_eq.symm
  have hl1 : (⟨#[.l1]⟩ : LVec) = knownBit true := knownBit_true_eq.symm
  have hge : (LVec.ofLogic ((reg.k.add (LVec.ofBitVec 4#32)).ge (LVec.ofInt 32 (N : Int)))).condTrue =
      decide (N ≤ 4 * j + 4) := by
    rw [hk, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.add_ofBitVec, LVec.ge_ofBitVec,
      LVec.ofLogic_ofBool, condTrue_knownBit]
    exact decide_eq_decide.mpr (ge_four_iff hjN hN256)
  have h4j : 4 * (j - 1) + 4 = 4 * j := by omega
  have h4j1 : 4 * j + 4 = 4 * (j + 1) := by omega
  have eA4 : 4 * j * W + 4 * W = 4 * (j + 1) * W := by rw [← Nat.add_mul]; congr 1
  have eB4 : 4 * j * (N * W) + 4 * (N * W) = 4 * (j + 1) * (N * W) := by rw [← Nat.add_mul]; congr 1
  have hw0 := hw
  obtain ⟨whdn, whc, whk, whbz, whdr, whash, whbsh, -, -⟩ := hw0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl)]
    by_cases hf : N ≤ 4 * j + 4 <;>
      simp [ctrlQ, hr, hs, hbz, hdn, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf, wr, nbaFold]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl)))]
    by_cases hf : N ≤ 4 * j + 4 <;>
      simp [ctrlQ, hr, hs, hbz, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf, wr, whbz, nbaFold,
        LVec.resizeU_one_l0, hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
    by_cases hf : N ≤ 4 * j + 4 <;>
      simp [ctrlQ, hr, hs, hbz, hdr, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf, wr, whdr, nbaFold,
        LVec.resizeU_one_l1, hl1, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "k" (.inr (.inl rfl))]
    by_cases hf : N ≤ 4 * j + 4 <;>
      (simp only [ctrlQ, hr, hs, hbz, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf,
        decide_true, decide_false, Bool.true_and, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte]
       simp [hk, wr, nbaFold, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
         LVec.insertAt_zero_of_width_eq, BitVec.ofNat_add_ofNat, h4j1])
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "a_sh" (.inr (.inr (.inr (.inr (.inl rfl)))))]
    by_cases hf : N ≤ 4 * j + 4 <;>
      simp [ctrlQ, hr, hs, hbz, hash, shA_ofBitVec hW127, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf,
        wr, whash, nbaFold, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq,
        ← BitVec.shiftRight_add, eA4]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "b_sh" (.inr (.inr (.inr (.inr (.inr rfl)))))]
    by_cases hf : N ≤ 4 * j + 4 <;>
      simp [ctrlQ, hr, hs, hbz, hbsh, shB_ofBitVec hN256 hW127, scmpGt4_known hN256, hN4, landL_knownBit, hge, hf,
        wr, whbsh, nbaFold, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.insertAt_zero_of_width_eq,
        ← BitVec.shiftRight_add, eB4]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_pe N W AccW ins reg _ "C" (.inr (.inr rfl)), allPeFFQ]
    have h1 : ∀ i j', i < N → j' < N → ∀ v,
        nbaFold "C" (peFFQ N W AccW ins reg (wSet N W ins reg) i j') v =
          v.insertAt ((i * N + j') * AccW) (LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (4 * j) ((i * N + j') / N) ((i * N + j') % N)))) := by
      intro i j' hi hj' v
      have hadd := addCV_of_pairSum (AccW := AccW) (ins := ins) hW hp hi hj'
      rw [h4j] at hadd
      simp [peFFQ, hs, hbz, hc, scmpGt4_known hN256, hN4, landL_knownBit,
        nbaFold, hadd, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, rm_div hj', rm_mod hj']
    rw [nbaFold_insertEntries_rowMajor (E := AccW) "C"
      (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (4 * j) (r / N) (r % N)))) h1,
      LVec.insertEntries_ofBitVec _ _ whc]
    rfl
  · rw [nextRegs_rs ins reg hw, nextRegs_rc ins reg hw]
    exact wSet_csa_pairSum hN hN256 hW A B hs (.inr ⟨by simp [show ¬ (N ≤ 4) by omega], hash, hbsh⟩)

theorem next_drain {N W AccW t : Nat} (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W)
    (ht : N ≤ t + 4) (ht0 : N ≤ 4 → t = 0)
    (A B : BitVec (N * N * W)) {ins : MIns} {reg : MRegs}
    (hr : ins.r = knownBit false) (hs : ins.s = knownBit false)
    (hbz : reg.bz = knownBit false) (hdr : reg.dr = knownBit true)
    (hc : 4 < N → reg.c = accC N W AccW A B t)
    (hp : PairSum N W A B t reg.rs reg.rc)
    (hw : WdRegs N W AccW reg) :
    (nextRegs N W AccW ins reg).dn = knownBit true ∧
    (nextRegs N W AccW ins reg).bz = knownBit false ∧
    (nextRegs N W AccW ins reg).dr = knownBit false ∧
    (nextRegs N W AccW ins reg).c = .ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  have hl0 : (⟨#[.l0]⟩ : LVec) = knownBit false := knownBit_false_eq.symm
  have hl1 : (⟨#[.l1]⟩ : LVec) = knownBit true := knownBit_true_eq.symm
  obtain ⟨whdn, whc, -, -, whdr, -, -, -, -⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "done" (.inl rfl)]
    simp [ctrlQ, hr, hs, hbz, hdr, scmpGt4_known hN256, landL_knownBit, wr, whdn, nbaFold,
      LVec.resizeU_one_l1, hl1, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "busy" (.inr (.inr (.inl rfl)))]
    simp [ctrlQ, hr, hs, hbz, hdr, scmpGt4_known hN256, landL_knownBit, wr, nbaFold]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_ctrl N W AccW ins reg _ "drain" (.inr (.inr (.inr (.inl rfl))))]
    simp [ctrlQ, hr, hs, hbz, hdr, scmpGt4_known hN256, landL_knownBit, wr, whdr, nbaFold,
      LVec.resizeU_one_l0, hl0, LVec.insertAt_zero_of_width_eq]
  · simp only [nextRegs]; rw [nbaFold_edgeQ_pe N W AccW ins reg _ "C" (.inr (.inr rfl)), allPeFFQ]
    rw [← accC_ge N W AccW A B ht]
    have h1 : ∀ i j', i < N → j' < N → ∀ v,
        nbaFold "C" (peFFQ N W AccW ins reg (wSet N W ins reg) i j') v =
          v.insertAt ((i * N + j') * AccW) (LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 4) ((i * N + j') / N) ((i * N + j') % N)))) := by
      intro i j' hi hj' v
      by_cases hle4 : N ≤ 4
      · obtain rfl := ht0 hle4
        have hset := setCV_of_pairSum (AccW := AccW) (ins := ins) hW hp hi hj'
        have hp4 : psum N W A B (0 + 4) i j' = chunk4 N W A B 0 i j' := by
          rw [psum_add4]; simp [psum]
        simp [peFFQ, hs, hbz, hdr, scmpGt4_known hN256, scmpLe4_known hN256, hle4, landL_knownBit,
          nbaFold, hset, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, rm_div hj', rm_mod hj', hp4]
      · have hgt4 : 4 < N := by omega
        have hadd := addCV_of_pairSum (AccW := AccW) (ins := ins) hW hp hi hj'
        simp [peFFQ, hs, hbz, hdr, hc hgt4, scmpGt4_known hN256, scmpLe4_known hN256, hle4, landL_knownBit,
          nbaFold, hadd, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, rm_div hj', rm_mod hj']
    rw [nbaFold_insertEntries_rowMajor (E := AccW) "C"
      (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 4) (r / N) (r % N)))) h1,
      LVec.insertEntries_ofBitVec _ _ whc]
    rfl

/-! ## Section 5: `PhaseModel`, txtask-v2 rules, and `solution : Goal lat` -/

def DrainAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ins reg w t, st = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w ∧
    N ≤ t + 4 ∧ (N ≤ 4 → t = 0) ∧
    reg.dn = knownBit false ∧ reg.bz = knownBit false ∧ reg.dr = knownBit true ∧
    (4 < N → reg.c = accC N W AccW A B t) ∧ PairSum N W A B t reg.rs reg.rc

def RunAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (j : Nat) (st : SvState) : Prop :=
  ∃ ins reg w, st = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w ∧
    4 < N ∧ 1 ≤ j ∧ 4 * j < N ∧
    reg.dn = knownBit false ∧ reg.bz = knownBit true ∧ reg.dr = knownBit false ∧
    reg.k = .ofBitVec (BitVec.ofNat 32 (4 * j)) ∧
    reg.ash = .ofBitVec (padA N W A >>> (4 * j * W)) ∧
    reg.bsh = .ofBitVec (padB N W B >>> (4 * j * (N * W))) ∧
    reg.c = accC N W AccW A B (4 * (j - 1)) ∧ PairSum N W A B (4 * (j - 1)) reg.rs reg.rc

def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ins reg w, st = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w ∧
    reg.dn = knownBit true ∧ reg.c = .ofBitVec (Tasks.Matmul.product N W AccW A B) ∧
    reg.bz = knownBit false ∧ reg.dr = knownBit false

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ins reg w, prev = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w ∧
    st = mmNext N W AccW (appIns e ins) reg

theorem ops_appIns {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (ins : MIns) :
    (appIns e ins).a = .ofBitVec x.1 ∧ (appIns e ins).b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIns, appIn, h.1, h.2.1]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  refine ⟨⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W)⟩,
    ⟨.xVec 1, .xVec (N * N * AccW), .xVec 32, .xVec 1, .xVec 1,
     .xVec ((N * N + 3) * W), .xVec ((N * N + 3 * N) * W),
     .xVec (N * N * (2 * W + 2)), .xVec (N * N * (2 * W + 2))⟩,
    ⟨.xVec ((N * N + 3) * W), .xVec ((N * N + 3 * N) * W),
     .xVec (N * N * (2 * W)), .xVec (N * N * (2 * W)),
     .xVec (N * N * (2 * W)), .xVec (N * N * (2 * W)),
     .xVec (N * N * (2 * W + 2)), .xVec (N * N * (2 * W + 2)),
     .xVec (N * N * (2 * W + 2)), .xVec (N * N * (2 * W + 2)),
     .xVec (N * N * (2 * W + 2))⟩, ?_, by simp [WdRegs], by simp [WdWires]⟩
  simp [initState2, mmD, mmDecls, MS]

def model (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) ((N + 3) / 4) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hN256 hW hW127 hA hA64
  cycle := by
    rintro σ F e prev k st k' ⟨ins, reg, w, rfl, hwr, hww⟩ hc
    obtain ⟨kk', hnext⟩ := mm_cycle N W AccW hN hN256 hW hW127 hA hA64 σ e ins reg w hww k 36 (Nat.le_refl _)
    exact ⟨ins, reg, w, rfl, hwr, hww, (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ins, reg, w, -, hwr, -, rfl⟩
    exact mmNext_I N W AccW _ reg hwr
  Ready st := ∃ ins reg w, st = MS ins reg w ∧ WdRegs N W AccW reg ∧ WdWires N W w ∧
    reg.dn = knownBit false ∧ reg.bz = knownBit false ∧ reg.dr = knownBit false
  Busy x m st :=
    if m = 0 then DrainAt N W AccW x.1 x.2.1 st
    else ∃ j, j + m = (N + 3) / 4 ∧ RunAt N W AccW x.1 x.2.1 j st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ins, reg, w, rfl, -, -, hdn, -, -⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup, hdn]
  busy_done := by
    rintro x m st hb
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte] at hb
      obtain ⟨ins, reg, w, t, rfl, -, -, -, -, hdn, -, -, -, -⟩ := hb
      simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup, hdn]
    · simp only [hm, ↓reduceIte] at hb
      obtain ⟨j, -, ins, reg, w, rfl, -, -, -, -, -, hdn, -, -, -, -, -, -, -⟩ := hb
      simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup, hdn]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ins, reg, w, rfl, -, -, hdn, hc, -, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup, hdn, hc]
  reset := by
    rintro e prev st - ⟨ins, reg, w, -, hwr, -, rfl⟩ hr
    have hr' : (appIns e ins).r = knownBit true := BitIs.appIn_eq hr ins.r
    obtain ⟨hdn, hbz, hdr⟩ := next_reset hr' hwr
    exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
      wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hdn, hbz, hdr⟩
  start := by
    rintro e prev st ⟨A, B, ⟨⟩⟩ - ⟨ins, reg, w, -, hwr, -, rfl⟩ - hr hs hx
    have hr' : (appIns e ins).r = knownBit false := BitIs.appIn_eq hr ins.r
    have hs' : (appIns e ins).s = knownBit true := BitIs.appIn_eq hs ins.s
    obtain ⟨ha, hb⟩ := ops_appIns hx ins
    right
    refine ⟨(N + 3) / 4 - 1, by omega, ?_⟩
    by_cases h4 : N ≤ 4
    · have hlat : (N + 3) / 4 - 1 = 0 := by omega
      simp only [hlat, ↓reduceIte]
      obtain ⟨hdn, hbz, hdr, hp⟩ := next_start_le4 hN h4 hW A B hr' hs' ha hb hwr
      exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, 0, rfl,
        wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, by omega, fun _ => rfl,
        hdn, hbz, hdr, fun h => absurd h (by omega), hp⟩
    · have hgt4 : 4 < N := by omega
      have hlat : (N + 3) / 4 - 1 ≠ 0 := by omega
      simp only [hlat, ↓reduceIte]
      obtain ⟨hdn, hbz, hdr, hk, hash, hbsh, hc, hp⟩ := next_start_gt4 hgt4 hN256 hW hW127 A B hr' hs' ha hb hwr
      exact ⟨1, by omega, appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
        wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hgt4, by omega, by omega,
        hdn, hbz, hdr, hk, hash, hbsh, hc, hp⟩
  busy := by
    rintro e prev st ⟨A, B, ⟨⟩⟩ m - ⟨ins, reg, w, rfl, hwr, hww, rfl⟩ hb hr hs -
    have hr' : (appIns e ins).r = knownBit false := BitIs.appIn_eq hr ins.r
    have hs' : (appIns e ins).s = knownBit false := BitIs.appIn_eq hs ins.s
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte] at hb
      obtain ⟨ins', reg', w', t, heq, -, -, ht, ht0, -, hbz, hdr, hc, hp⟩ := hb
      obtain ⟨-, rfl, -⟩ := MS_inj heq
      obtain ⟨hdn', hbz', hdr', hc'⟩ := next_drain hN hN256 hW ht ht0 A B hr' hs' hbz hdr hc hp hwr
      left
      exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
        wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hdn', hc', hbz', hdr'⟩
    · simp only [hm, ↓reduceIte] at hb
      obtain ⟨j, hjm, ins', reg', w', heq, -, -, hgt4, hj1, hjN, hdn, hbz, hdr, hk, hash, hbsh, hc, hp⟩ := hb
      obtain ⟨-, rfl, -⟩ := MS_inj heq
      obtain ⟨hdn', hbz', hdr', hk', hash', hbsh', hc', hp'⟩ :=
        next_busy_gt4 hgt4 hN256 hW hW127 hj1 hjN A B hr' hs' hdn hbz hdr hk hash hbsh hc hp hwr
      right
      refine ⟨m - 1, by omega, ?_⟩
      by_cases hm1 : m - 1 = 0
      · simp only [hm1, ↓reduceIte]
        have hreach : N ≤ 4 * j + 4 := by omega
        simp only [hreach, not_true_eq_false, decide_false, decide_true] at hbz' hdr'
        exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, 4 * j, rfl,
          wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hreach, fun h => absurd h (by omega),
          hdn', hbz', hdr', fun _ => hc', hp'⟩
      · simp only [hm1, ↓reduceIte]
        have hlt : ¬ (N ≤ 4 * j + 4) := by omega
        simp only [hlt, not_false_eq_true, decide_true, decide_false] at hbz' hdr'
        exact ⟨j + 1, by omega, appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
          wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hgt4, by omega, by omega,
          hdn', hbz', hdr', hk', hash', hbsh', by simpa using hc', by simpa using hp'⟩
  hold_ready := by
    rintro e prev st - ⟨ins, reg, w, rfl, hwr, -, rfl⟩ ⟨ins', reg', w', heq, -, -, hdn, hbz, hdr⟩ hr hs
    obtain ⟨-, rfl, -⟩ := MS_inj heq
    have hr' : (appIns e ins).r = knownBit false := BitIs.appIn_eq hr ins.r
    have hs' : (appIns e ins).s = knownBit false := BitIs.appIn_eq hs ins.s
    obtain ⟨hdn', -, hbz', hdr'⟩ := next_idle hN256 hr' hs' hbz hdr
    exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
      wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hdn'.trans hdn, hbz', hdr'⟩
  hold_fin := by
    rintro e prev st ⟨A, B, ⟨⟩⟩ - ⟨ins, reg, w, rfl, hwr, -, rfl⟩ ⟨ins', reg', w', heq, -, -, hdn, hc, hbz, hdr⟩ hr hs
    obtain ⟨-, rfl, -⟩ := MS_inj heq
    have hr' : (appIns e ins).r = knownBit false := BitIs.appIn_eq hr ins.r
    have hs' : (appIns e ins).s = knownBit false := BitIs.appIn_eq hs ins.s
    obtain ⟨hdn', hc', hbz', hdr'⟩ := next_idle hN256 hr' hs' hbz hdr
    exact ⟨appIns e ins, nextRegs N W AccW (appIns e ins) reg, _, rfl,
      wdRegs_nextRegs N W AccW _ reg hwr, wdWires_wSet N W _ _, hdn'.trans hdn, hc'.trans hc, hbz', hdr'⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "drain",
      "a_sh", "Ap", "b_sh", "Bp", "rs", "rc", "p0", "p1", "p2", "p3",
      "x1", "y1", "s2", "c2", "s4"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
  rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
  · simp [Tasks.Matmul.task, pAp, Process2.isEdgePhase, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, pBp, Process2.isEdgePhase, edgeClock, asyncReset, processDataNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, pCtrl, nb, c32, amtA, amtB, condLe4, condGt4, Process2.isEdgePhase, edgeClock, asyncReset,
      processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Tasks.Matmul.task, pPm, pX1, pY1, pS2, pC2, pS4, pFF, sextSel, sext2, sextAcc,
        condSel, condGt4, condLe4, c32, Process2.isEdgePhase, edgeClock, asyncReset, processDataNames,
        stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]; intro p hp
  have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
  rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
  · simp [pAp, Process2.hasQualifiedCase]
  · simp [pBp, Process2.hasQualifiedCase]
  · simp [pCtrl, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]
  · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [pPm, pX1, pY1, pS2, pC2, pS4, pFF, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) (st : SvState) (h : PowerUp (design.sem N W AccW) st) :
    I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨k, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨dr, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨ash, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨ap, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨bsh, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain ⟨bp, r14, rfl, w14, -, h14⟩ := powerUp_cons.mp h13
  obtain ⟨rs, r15, rfl, w15, -, h15⟩ := powerUp_cons.mp h14
  obtain ⟨rc, r16, rfl, w16, -, h16⟩ := powerUp_cons.mp h15
  obtain ⟨p0, r17, rfl, w17, -, h17⟩ := powerUp_cons.mp h16
  obtain ⟨p1, r18, rfl, w18, -, h18⟩ := powerUp_cons.mp h17
  obtain ⟨p2, r19, rfl, w19, -, h19⟩ := powerUp_cons.mp h18
  obtain ⟨p3, r20, rfl, w20, -, h20⟩ := powerUp_cons.mp h19
  obtain ⟨x1, r21, rfl, w21, -, h21⟩ := powerUp_cons.mp h20
  obtain ⟨y1, r22, rfl, w22, -, h22⟩ := powerUp_cons.mp h21
  obtain ⟨s2, r23, rfl, w23, -, h23⟩ := powerUp_cons.mp h22
  obtain ⟨c2, r24, rfl, w24, -, h24⟩ := powerUp_cons.mp h23
  obtain ⟨s4, r25, rfl, w25, -, h25⟩ := powerUp_cons.mp h24
  obtain rfl := powerUp_nil.mp h25
  exact ⟨⟨ck, r, s, a, b⟩, ⟨dn, c, k, bz, dr, ash, bsh, rs, rc⟩,
    ⟨ap, bp, p0, p1, p2, p3, x1, y1, s2, c2, s4⟩, rfl,
    ⟨w6, w7, w8, w9, w10, w11, w13, w15, w16⟩,
    ⟨w12, w14, w17, w18, w19, w20, w21, w22, w23, w24, w25⟩⟩

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hN256 hW hW127 hA hA64) (fun σ => ⟨36, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ins, reg, w, rfl, hwr, hww⟩
  obtain ⟨kk', hcyc⟩ := mm_cycle N W AccW hN hN256 hW hW127 hA hA64 σ e ins reg w hww kk 36 (Nat.le_refl _)
  exact ⟨_, _, hcyc, mmNext_I N W AccW _ reg hwr⟩

/-- **Rule 1 (`MooreOutDep`)**: no continuous assign writes `"done"` or `"C"`. -/
theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  refine ⟨fun n => n ≠ "done" ∧ n ≠ "C", ?_, ?_, ?_⟩
  · intro n hn _
    simp [mmD, mmDecls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he _
    simp only [combDeps, List.mem_flatMap] at he
    obtain ⟨p, hp, he⟩ := he
    have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
    rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, -, -, hp⟩
    · simp [pAp, processDeps, lhsTargets] at he; rw [he]; simp
    · simp [pBp, processDeps, lhsTargets] at he; rw [he]; simp
    · simp [pCtrl, processDeps] at he
    · simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp [pPm, pX1, pY1, pS2, pC2, pS4, pFF, processDeps, lhsTargets] at he; try (rw [he]; simp))
  · intro o ho
    simp [mmD, mmDecls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> simp

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  rw [← knownBit_false_eq]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  rw [← knownBit_true_eq]; exact LVec.allKnown_ofBitVec _

/-- **Rule 3 (`XSafe`)**: every slice is in range and every bitwise/ternary op has matching widths. -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hN256 : N ≤ 256) (hW : 1 ≤ W) (hW127 : W ≤ 127)
    (hA : 1 ≤ AccW) (hA64 : AccW ≤ 64) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hN256 hW hW127 hA hA64]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hp' : p ∈ mmProcs N W AccW := by simpa [mmD] using hp
  have h0k := lvec_l0_known
  have h1k := lvec_l1_known
  have hofInt : ∀ z : Int, (LVec.ofInt 32 z).allKnown = true := fun z => by
    rw [LVec.ofInt_eq_ofBitVec]; exact LVec.allKnown_ofBitVec _
  rcases mm_proc_mem hp' with rfl | rfl | rfl | ⟨i, j, hi, hj, hp⟩
  · simp [xsProc, xsLhs, xsWidth, xsWidthList, sigWidth, pAp, mmD, mmDecls, h0k]
  · simp [xsProc, xsLhs, xsWidth, xsWidthList, sigWidth, pBp, mmD, mmDecls, h0k]
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, scmpOp, sigWidth, pCtrl, nb, c32,
      amtA, amtB, condLe4, condGt4, mmD, mmDecls, h0k, h1k, hofInt, LVec.allKnown_ofBitVec]
  · have hwa : ∀ m, m ≤ 3 → (i * N + m) * W + W ≤ (N * N + 3) * W := fun m hm => winA_le m hm hi
    have hwb : ∀ m, m ≤ 3 → (m * N + j) * W + W ≤ (N * N + 3 * N) * W := fun m hm => winB_le m hm hj
    have hwa0 : i * N * W + W ≤ (N * N + 3) * W := by simpa using hwa 0 (by omega)
    have hwa01 : i * N * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
    have hwb0 : j * W + W ≤ (N * N + 3 * N) * W := by simpa using hwb 0 (by omega)
    have hwb01 : j * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
    have hwb1 : (N + j) * W + W ≤ (N * N + 3 * N) * W := by simpa using hwb 1 (by omega)
    have hwb11 : (N + j) * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
    have hwa1 : ∀ m, m ≤ 3 → (i * N + m) * W + W - 1 + 1 ≤ (N * N + 3) * W := fun m hm => by have := hwa m hm; omega
    have hwb' : ∀ m, m ≤ 3 → (m * N + j) * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := fun m hm => by have := hwb m hm; omega
    have hP := winRM_le (K := 2 * W) hi hj
    have hP1 : (i * N + j) * (2 * W) + 2 * W - 1 + 1 ≤ N * N * (2 * W) := by omega
    have hS := winRM_le (K := 2 * W + 2) hi hj
    have hS1 : (i * N + j) * (2 * W + 2) + (2 * W + 1) + 1 ≤ N * N * (2 * W + 2) := by omega
    have hC := winRM_le (K := AccW) hi hj
    have h2sw : 2 + 2 * W = 2 * W + 2 := by omega
    simp only [peProcs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, scmpOp, sigWidth, pPm, sextSel, condSel, c32,
        mmD, mmDecls, hofInt, hwa0, hwa01, hwb0, hwb01]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, scmpOp, sigWidth, pPm, sextSel, condSel, c32,
        mmD, mmDecls, hofInt, hwa 1 (by omega), hwa1 1 (by omega), hwb1, hwb11]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, scmpOp, sigWidth, pPm, sextSel, condSel, c32,
        mmD, mmDecls, hofInt, hwa 2 (by omega), hwb 2 (by omega), hwa1 2 (by omega), hwb' 2 (by omega)]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, scmpOp, sigWidth, pPm, sextSel, condSel, c32,
        mmD, mmDecls, hofInt, hwa 3 (by omega), hwb 3 (by omega), hwa1 3 (by omega), hwb' 3 (by omega)]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pX1, sext2, mmD, mmDecls, hP, hP1]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pY1, sext2, c32, mmD, mmDecls, hofInt, hP, hP1]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pS2, sext2, mmD, mmDecls, hP, hP1, hS, h2sw]
    · simp [xsProc, xsLhs, xsWidth, xsWidthList, binW, sigWidth, pC2, sext2, c32, mmD, mmDecls, hofInt, hP, hP1, hS, h2sw]
    · simp [xsProc, xsLhs, xsWidth, binW, sigWidth, pS4, mmD, mmDecls, hS]
    · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, scmpOp, sigWidth, pFF,
        sextAcc, condGt4, condLe4, c32, mmD, mmDecls, hofInt, LVec.allKnown_ofBitVec, hS, hS1, hC]

/-- **The 2-stage pipelined G4 4:2-CSA matmul satisfies `Goal lat` (`lat = (N + 3) / 4`, `1` at `(4, 8, 32)`).** -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases
    (mm_interface N W AccW hN hN256 hW hW127 hA hA64)
    (mm_disciplined N W AccW hN hN256 hW hW127 hA hA64)
    (mm_terminatesPU N W AccW hN hN256 hW hW127 hA hA64)
    (by show 1 ≤ (N + 3) / 4; omega)
    (model N W AccW hN hN256 hW hW127 hA hA64)
    (mm_powerUp N W AccW hN hN256 hW hW127 hA hA64)
    (mm_moore N W AccW hN hN256 hW hW127 hA hA64)
    (mm_xsafe N W AccW hN hN256 hW hW127 hA hA64)

end Submission
