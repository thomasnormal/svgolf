-- svgolf-latency: 1
-- MAINTAINER PORT (2026-11-16): the svGolf maintainers' port of the player's proof to the checker at Proglib 4fcda4c8 (Lean v4.35.0); the design is the player's, byte for byte, and the player's own proof is in the record this one replaces (the repository's history). The lines below say what changed versus the player's file.
-- pin2 port (Proglib 32756c0b, Lean v4.35.0): the agreement mm_sem_eq re-proved from sv_mirror's instantiation (the hand-written stages of instantiate2 removed), a range hypothesis hR32 threaded to its users and derived in solution, the one-clock guard passed to Terminates2.of_invariant; the mirror and the rest of the proof unchanged; pin3: the two range conjuncts of 2026-11-14 (W, AccW < 2^20) dropped where `solution` destructures inRange; pin5 (2026-11-16, Proglib 4fcda4c8): matmul's range of 2026-11-16 (1 ≤ N < 2^5, 1 ≤ W < 2^10, 1 ≤ AccW < 2^12): the destructuring of inRange, the products derived from the new bounds
-- range of 2026-11-19 (1 ≤ N ≤ 256, W ≤ 127, AccW ≤ 64): the destructuring of inRange in `solution`, and the two port-width bounds it derives, N * N * W < 2 ^ 31 and N * N * AccW < 2 ^ 31, from the new bounds (256 * 256 * 127 and 256 * 256 * 64); the rest of the proof unchanged
import Submission.Design
import SvGolf.Cycle
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
# Reference solution for task `matmul`, G1: `N²` multiply-accumulate units and one step counter

On `start`, `reference/matmul_g1.sv` captures `A`, `B` into shift registers and clears `C`; for `N`
busy cycles PE `(i, j)` adds `A[i][k]·B[k][j]` (sign-extended, mod `2^AccW`); `done` shows in the
snapshot `N` cycles after the start's (`lat = N`). Proved at every in-range `(N, W, AccW)`:
1. **Agreement** (`mm_sem_eq`): the loaded family `design.sem N W AccW` is the hand-built `mmD`.
2. **G0's clock step** (`mm_profile`, `mm_cycle`): one cycle of the loaded design, from any state
   of its shape, any schedule, is the evaluated commit `mmNext`.
3. **The invariant on `k`** (`pe_step`, `next_step`): busy cycle `t` turns every accumulator's
   `Σ_{k' < t} A[i][k']·B[k'][j]` into the sum to `t + 1`, mod `2^AccW` (`accC`).
4. **The spec's arithmetic** (`product_eq`, `accC_N`): `product` is `accC` at `t = N`.
5. **The protocol** (`model`): the phases of `TxTask.satisfiedAt_of_phases`.
6. **txtask-v2** (section 8): rule 2 (`mm_powerUp`: every power-up state has the model's shape, so
   the claim and termination hold from every power-up), rule 1 (`mm_moore`: every process an
   `always_ff`, so no combinational dependency) and rule 3 (`mm_xsafe`), then `solution`.

The design-independent lemmas are in the library: the packed view and its commit (`packBV`,
`LVec.insertEntries_ofBitVec`) in `LeanModels.Sv.SeqFamily`, the clock step (`ffDisjB_of_pairwise`,
`flatMap_ffUpd`) in `LeanModels.Sv.SeqProfile`, the window arithmetic and the datapath's `BitVec` facts in
`LeanModels.Sv.Lib.NatArith` and `LeanModels.Sv.Lib.BitVecArith`.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-- The latency: `done` shows `ceil(N/4)` snapshots after the start's (1 at the scoring point). -/
def lat (N _W _AccW : Nat) : Nat := (N + 3) / 4

/-! ## 0. Small `BitVec` facts for the four-step datapath -/

theorem setWidth_signExtend_mul4 {m n w : Nat} (h : m ≤ n) (a b : BitVec w) :
    (a.signExtend n * b.signExtend n).setWidth m = BitVec.ofInt m (a.toInt * b.toInt) := by
  rw [BitVec.setWidth_mul _ _ h, Lib.setWidth_signExtend_of_le _ h, Lib.setWidth_signExtend_of_le _ h,
    BitVec.ofInt_mul]
  rfl

/-- Four multiply-accumulates at a wider width, truncated back (`Lib.setWidth_add_mul_signExtend` four times). -/
theorem setWidth_add4_mul_signExtend {m n w : Nat} (h : m ≤ n) (x : BitVec m)
    (a0 b0 a1 b1 a2 b2 a3 b3 : BitVec w) :
    (x.setWidth n + a0.signExtend n * b0.signExtend n + a1.signExtend n * b1.signExtend n
      + a2.signExtend n * b2.signExtend n + a3.signExtend n * b3.signExtend n).setWidth m =
    x + BitVec.ofInt m (a0.toInt * b0.toInt) + BitVec.ofInt m (a1.toInt * b1.toInt)
      + BitVec.ofInt m (a2.toInt * b2.toInt) + BitVec.ofInt m (a3.toInt * b3.toInt) := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_add _ _ h, BitVec.setWidth_add _ _ h,
    BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    setWidth_signExtend_mul4 h, setWidth_signExtend_mul4 h, setWidth_signExtend_mul4 h,
    setWidth_signExtend_mul4 h]

/-- Zero-extending first changes no part select. -/
theorem extractLsb'_setWidth_of_le {n n' : Nat} (h : n ≤ n') (x : BitVec n) (s l : Nat) :
    (x.setWidth n').extractLsb' s l = x.extractLsb' s l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  by_cases hs : s + i < n
  · simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, hs, show s + i < n' by omega]
  · simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, hs, BitVec.getLsbD_of_ge x (s + i) (by omega)]

/-- The four-step counter test: `t < N < 2^31`, `t + 4` at 32 bits against `N`. -/
theorem ge_four_iff {t N : Nat} (ht : t < N) (hN : N < 2 ^ 31) :
    BitVec.ofNat 32 N ≤ BitVec.ofNat 32 t + 4#32 ↔ N ≤ t + 4 := by
  rw [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at hN ⊢
  omega

/-- The four `a_sh` windows `[(i·N + m)·W +: W]`, `m ≤ 3`, lie inside the `(N·N + 3)·W`-bit register. -/
theorem winA_le {N W i : Nat} (m : Nat) (hm : m ≤ 3) (hi : i < N) : (i * N + m) * W + W ≤ (N * N + 3) * W := by
  have h1 : (i + 1) * N ≤ N * N := Nat.mul_le_mul_right N (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1
  have h : i * N + m + 1 ≤ N * N + 3 := by omega
  have h2 := Nat.mul_le_mul_right W h
  rw [Nat.add_mul (i * N + m) 1 W, Nat.one_mul] at h2
  exact h2

/-- The four `b_sh` windows `[(m·N + j)·W +: W]`, `m ≤ 3`, lie inside the `(N·N + 3·N)·W`-bit register. -/
theorem winB_le {N W j : Nat} (m : Nat) (hm : m ≤ 3) (hj : j < N) :
    (m * N + j) * W + W ≤ (N * N + 3 * N) * W := by
  have h1 : m * N ≤ 3 * N := Nat.mul_le_mul_right N hm
  have h3 : N ≤ N * N := Nat.le_mul_self N
  have h : m * N + j + 1 ≤ N * N + 3 * N := by omega
  have h2 := Nat.mul_le_mul_right W h
  rw [Nat.add_mul (m * N + j) 1 W, Nat.one_mul] at h2
  exact h2

/-! ## 1. Agreement: the stages of `instantiate2` -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- One product of the busy sum: `a_sh[la +: W]` times `b_sh[lb +: W]`, both sign-extended by `AccW` bits. -/
def mulT (AccW W la lb : Nat) : Expr2 :=
  .binary .mul (sext "a_sh" AccW la W) (sext "b_sh" AccW lb W)

/-- The PE at `(i, j)`: clear on `start`, else add four products `A[i][k+m]·B[k+m][j]` (`m < 4`) while `busy`. -/
def mmPE (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0)))
    (some (.ifStmt (.ident "busy")
      (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW)
        (.resize AccW (.binary .add (.binary .add (.binary .add (.binary .add
          (.resize (AccW + W) (.slice (.ident "C") ((i * N + j) * AccW) AccW))
          (mulT AccW W (i * N * W) (j * W)))
          (mulT AccW W ((i * N + 1) * W) ((N + j) * W)))
          (mulT AccW W ((i * N + 2) * W) ((2 * N + j) * W)))
          (mulT AccW W ((i * N + 3) * W) ((3 * N + j) * W)))))
      none)))

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- A shift amount `2·N·W` / `2·W`, as the instantiation writes it. -/
abbrev amtA (W : Nat) : Expr2 := .binary .mul (c32 2) (c32 W)
abbrev amtB (N W : Nat) : Expr2 := .binary .mul (.binary .mul (c32 2) (c32 N)) (c32 W)

/-- The control: `busy`, `done`, the step counter `k` (steps of four), the operand shift registers. -/
def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "a_sh") (.resize ((N * N + 3) * W) (.ident "A")),
        .nbaAssign (.ident "b_sh") (.resize ((N * N + 3 * N) * W) (.ident "B"))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "k") (.binary .add (.ident "k") (c32 4)),
          .nbaAssign (.ident "a_sh")
            (.binary (.shr false) (.binary (.shr false) (.ident "a_sh") (amtA W)) (amtA W)),
          .nbaAssign (.ident "b_sh")
            (.binary (.shr false) (.binary (.shr false) (.ident "b_sh") (amtB N W)) (amtB N W)),
          .ifStmt (.binary .ge (.binary .add (.ident "k") (c32 4)) (c32 N))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The declarations: `A`/`B` at `wa` bits, `a_sh` at `wp`, `b_sh` at `wq`, `C` at `wc`. -/
def mmDecls (wa wp wq wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "k", width := 32 },
   { name := "busy", width := 1 }, { name := "a_sh", width := wp }, { name := "b_sh", width := wq }]

/-- The PEs, row-major. -/
def mmPEs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => mmPE N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) ((N * N + 3) * W) ((N * N + 3 * N) * W) (N * N * AccW)).toArray
  processes := (mmCtrl N W :: mmPEs N W AccW).toArray

/-! ### The stages of `instantiate2` -/

/-- Two PEs write disjoint windows of `C`. -/
theorem pe_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ a ∈ (mmPE N W AccW i j).procWins, ∀ b ∈ (mmPE N W AccW i' j').procWins,
      a.overlaps b = false := by
  have := rowMajor_le (K := AccW) h
  simp [mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins]
  omega

theorem mm_pe_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPEs N W AccW) :
    ∃ i j, p = mmPE N W AccW i j := by
  simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, -, j, -, rfl⟩ := hp
  exact ⟨i, j, rfl⟩

/-- The control and the PEs drive pairwise disjoint windows. -/
theorem mm_pairwise (N W AccW : Nat) : (mmCtrl N W :: mmPEs N W AccW).Pairwise
    fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false := by
  refine List.Pairwise.cons (fun p hp => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)
  · obtain ⟨i, j, rfl⟩ := mm_pe_mem hp
    simp [mmCtrl, mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins]
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ h => pe_disj (by omega))
  · intro i i' hii _ a ha b hb
    simp only [List.mem_map, List.mem_range] at ha hb
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨j', -, rfl⟩ := hb
    exact pe_disj (by have := rowMajor_le (K := N) hii; omega)

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mmCtrl N W :: mmPEs N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (mm_pairwise N W AccW)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hp; exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, List.mem_cons]
    rintro n ⟨p, hp | hp, hn⟩
    all_goals first | subst hp | obtain ⟨i, j, rfl⟩ := mm_pe_mem hp
    all_goals revert n; simp [mmCtrl, mmPE, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide

/-- (port) The exact 32-bit `int` instantiation: the parameters' ranges (`N < 46341` from `N * N * W < 2^31`). -/
abbrev Rng32 (N W AccW : Nat) : Prop := N < 46341 ∧ W < 2147483648 ∧ AccW < 2147483648

/-- (port) The statement's range gives it. -/
theorem rng32_of {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hNW : N * N * W < 2 ^ 31)
    (hNA : N * N * AccW < 2 ^ 31) : Rng32 N W AccW := by
  have h2 := Nat.le_mul_of_pos_right (N * N) hW
  have h3 := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  have h4 := Nat.le_mul_of_pos_left AccW (Nat.mul_pos hN hN)
  refine ⟨Nat.lt_of_not_le fun h => ?_, by omega, by omega⟩
  have := Nat.mul_le_mul h h
  omega

-- (port) The windows of `a_sh` and `b_sh` in the instantiation's `Int` form, for `sv_mirror`'s window tactic.
set_option hygiene false in
macro "ab_win" : tactic => `(tactic| (
  have hTA : (1 : Int) ≤ ((N : Int) * N + 3) * W := by exact_mod_cast Nat.mul_pos (Nat.succ_pos _) (by omega)
  have hTB : (1 : Int) ≤ ((N : Int) * N + 3 * N) * W := by
    exact_mod_cast Nat.mul_pos (show 0 < N * N + 3 * N by omega) (by omega)
  first
  | (have a0 : (i : Int) * N * W + W ≤ ((N : Int) * N + 3) * W := by
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
  | (have b0 : (j : Int) * W + W ≤ ((N : Int) * N + 3 * N) * W := by
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
     omega)))

-- (port) The instantiation, generated.
sv_mirror mmG (window := by ab_win) := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hN46 : N < 46341)

/-- (port) The generated mirror is the hand-built one. -/
theorem mmG_D (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) : mmG.D N W AccW = mmD N W AccW := by
  have hg : mmG.g_col N W AccW = fun i j => mmPE N W AccW i j := by
    funext i j
    have e1 : ((i : Int) * N + 2) * W = (((i * N + 2) * W : Nat) : Int) := by push_cast; rfl
    have e2 : ((i : Int) * N + 3) * W = (((i * N + 3) * W : Nat) : Int) := by push_cast; rfl
    have e3 : (2 * (N : Int) + j) * W = (((2 * N + j) * W : Nat) : Int) := by push_cast; rfl
    have e4 : (3 * (N : Int) + j) * W = (((3 * N + j) * W : Nat) : Int) := by push_cast; rfl
    simp [mmG.g_col, mmPE, sext, mulT, LVec.ofInt_eq_ofBitVec]
    and_intros <;> simp only [e1, e2, e3, e4, ← Int.natCast_add, Int.toNat_natCast] <;> omega
  have d1 : (((N : Int) * N + 3) * W - 1).natAbs + 1 = (N * N + 3) * W := by
    rw [show ((N : Int) * N + 3) * W = (((N * N + 3) * W : Nat) : Int) by push_cast; rfl]
    exact Lib.natAbs_sub_one_add_one (Nat.mul_pos (by omega) (by omega))
  have d2 : (((N : Int) * N + 3 * N) * W - 1).natAbs + 1 = (N * N + 3 * N) * W := by
    rw [show ((N : Int) * N + 3 * N) * W = (((N * N + 3 * N) * W : Nat) : Int) by push_cast; rfl]
    exact Lib.natAbs_sub_one_add_one (Nat.mul_pos (by omega) (by omega))
  simp [mmG.D, mmD, mmG.decls, mmDecls, mmG.procs, mmPEs, mmG.p0, mmCtrl, nb, c32, amtA, amtB,
    LVec.ofInt_eq_ofBitVec, hg, d1, d2]

/-- **The loaded family is `mmD`** (port: from the generated instantiation, `SvGolf.Cycle.sem_eq_of_mirror`). -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    design.sem N W AccW = mmD N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror (mmG.instantiate N W AccW hN hW hA (by have := hR32.1; omega) hR32.2.1 hR32.2.2 hR32.1) (mmG_D N W AccW hN hW)
    (by simpa [mmD] using mm_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by simp [mmD, mmCtrl, mmPEs, mmPE, List.all_flatMap, List.all_map,
      SvGolf.Cycle.notComb]))


/-! ## 2. G0's clock step for the loaded family, at every `(N, W, AccW)` -/

/-- **`mmD` is in G0's decidable FF-only profile at every `(N, W, AccW)`** (symbolic, not `rfl`). -/
theorem mm_profile (N W AccW : Nat) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by simpa [mmD] using mm_pairwise N W AccW)⟩
  simp [mmD, mmCtrl, mmPEs, mmPE, nb, List.all_flatMap, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB, Lhs2.window?,
    Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, mmDecls]

/-- The 11 signals of `mmD`, in declaration order. -/
def MS (ck r s a b dn c k bz ash bsh : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c), ("k", k),
    ("busy", bz), ("a_sh", ash), ("b_sh", bsh)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz ash bsh : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c k bz ash bsh) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz ash bsh := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

/-- A nonblocking write of `v` to the whole of `n` (old value `old`). -/
abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

/-- `v >> (2·W) >> (2·W)`, evaluated. -/
def shA (W : Nat) (v : LVec) : LVec :=
  (v.shr ((LVec.ofInt 32 2).mul (LVec.ofInt 32 (W : Int)))).shr ((LVec.ofInt 32 2).mul (LVec.ofInt 32 (W : Int)))

/-- `v >> (2·N·W) >> (2·N·W)`, evaluated. -/
def shB (N W : Nat) (v : LVec) : LVec :=
  (v.shr (((LVec.ofInt 32 2).mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int)))).shr
    (((LVec.ofInt 32 2).mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int)))

/-- The control's updates, from the pre-edge values. -/
def ctrlQ (N W : Nat) (r s a b dn k bz ash bsh : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "k" k (LVec.replicate 32 .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩,
    wr "k" k (LVec.replicate 32 .l0), wr "a_sh" ash (a.resizeU ((N * N + 3) * W)),
    wr "b_sh" bsh (b.resizeU ((N * N + 3 * N) * W))]
  else if bz.condTrue then
    if (LVec.ofLogic ((k.add (LVec.ofInt 32 4)).ge (LVec.ofInt 32 (N : Int)))).condTrue then
      [wr "k" k (k.add (LVec.ofInt 32 4)), wr "a_sh" ash (shA W ash), wr "b_sh" bsh (shB N W bsh),
        wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
    else [wr "k" k (k.add (LVec.ofInt 32 4)), wr "a_sh" ash (shA W ash), wr "b_sh" bsh (shB N W bsh)]
  else []

/-- `{{AccW{v[lo+W-1]}}, v[lo +: W]}`, evaluated. -/
def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

/-- One product of the busy sum, evaluated. -/
def mulV (AccW W : Nat) (ash bsh : LVec) (la lb : Nat) : LVec :=
  (sxv ash AccW la W).mul (sxv bsh AccW lb W)

/-- The new accumulator `(i, j)` of a busy cycle (four products), evaluated. -/
def peV (N W AccW i j : Nat) (c ash bsh : LVec) : LVec :=
  let r0 := (c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)
  let r1 := r0.add (mulV AccW W ash bsh (i * N * W) (j * W))
  let r2 := r1.add (mulV AccW W ash bsh ((i * N + 1) * W) ((N + j) * W))
  let r3 := r2.add (mulV AccW W ash bsh ((i * N + 2) * W) ((2 * N + j) * W))
  let r4 := r3.add (mulV AccW W ash bsh ((i * N + 3) * W) ((3 * N + j) * W))
  r4.resizeU AccW

/-- The PE's update, from the pre-edge values. -/
def peQ (N W AccW : Nat) (s bz c ash bsh : LVec) (i j : Nat) : NbaQueue2 :=
  if s.condTrue then [("C", (i * N + j) * AccW, (LVec.replicate AccW .l0).resizeU AccW)]
  else if bz.condTrue then [("C", (i * N + j) * AccW, (peV N W AccW i j c ash bsh).resizeU AccW)]
  else []

theorem ctrl_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh) [] (mmCtrl N W) =
      .ok (MS ck r s a b dn c k bz ash bsh, ctrlQ N W r s a b dn k bz ash bsh) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic ((k.add (LVec.ofInt 32 4)).ge (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp [mmCtrl, nb, c32, amtA, amtB, shA, shB, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, wr, h1, h2, h3, h4]

theorem pe_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ash bsh : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz ash bsh) [] (mmPE N W AccW i j) =
      .ok (MS ck r s a b dn c k bz ash bsh, peQ N W AccW s bz c ash bsh i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold peQ
  by_cases h1 : s.condTrue = true <;> by_cases h2 : bz.condTrue = true <;>
    simp [mmPE, mulT, mulV, sext, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, peV, sxv, h1, h2]

/-- One cycle's next state, from the pre-edge (inputs applied) values. -/
def mmNext (N W AccW : Nat) (ck r s a b dn c k bz ash bsh : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c k bz ash bsh) (ctrlQ N W r s a b dn k bz ash bsh ++
    (List.range N).flatMap fun i => (List.range N).flatMap (peQ N W AccW s bz c ash bsh i))

/-- **One cycle of the loaded design is G0's clock step**, evaluated (any schedule, any stimulus
entry, any state of the design's shape, every fuel from 30). -/
theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (σ : ScheduleOracle)
    (e : SvState) (ck r s a b dn c k bz ash bsh : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c k bz ash bsh) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn c k bz ash bsh, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
    rcases List.mem_cons.mp hm with rfl | hm
    · rfl
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm; rfl
  rw [mm_sem_eq N W AccW hN hW hA hR32, cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega),
    apply_mm, clockStep, flatMap_ffUpd F _ hedge]
  · simp only [mmD, List.toList_toArray, List.flatMap_cons, ctrl_run N W F hF, mmPEs, List.flatMap_assoc,
      List.flatMap_map, pe_run N W AccW _ _ F hF, mmNext]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ mmCtrl N W :: mmPEs N W AccW :=
      List.mem_of_getElem? (by simpa [mmD] using hp : (mmCtrl N W :: mmPEs N W AccW)[i]? = some p)
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, ctrl_run N W F hF _ _ _ _ _ _ _ _ _ _ _⟩
    · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm
      exact ⟨_, pe_run N W AccW i j F hF _ _ _ _ _ _ _ _ _ _ _⟩
  · rw [apply_mm]; simp [MS]

/-! ## 3. The busy cycle on known values: the invariant on `k` -/

attribute [local simp] condTrue_knownBit

/-- `Σ_{k' < t} A[i][k']·B[k'][j]` in the integers (`Tasks.Matmul.dot` at `t = N`). -/
def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

/-- The accumulators after `t` busy cycles: entry `(i, j)` is `psum t i j` mod `2^AccW`. -/
def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r => BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 1) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem psum_add4 (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : psum N W A B (t + 4) i j =
    psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j)
      + Tasks.Matmul.entry W A (i * N + (t + 1)) * Tasks.Matmul.entry W B ((t + 1) * N + j)
      + Tasks.Matmul.entry W A (i * N + (t + 2)) * Tasks.Matmul.entry W B ((t + 2) * N + j)
      + Tasks.Matmul.entry W A (i * N + (t + 3)) * Tasks.Matmul.entry W B ((t + 3) * N + j) := by
  have h1 : psum N W A B (t + 1) i j = _ := psum_succ N W A B t i j
  have h2 : psum N W A B (t + 2) i j = _ := psum_succ N W A B (t + 1) i j
  have h3 : psum N W A B (t + 3) i j = _ := psum_succ N W A B (t + 2) i j
  have h4 : psum N W A B (t + 4) i j = _ := psum_succ N W A B (t + 3) i j
  rw [h4, h3, h2, h1]

/-- `A` zero-extended to the `a_sh` register's width. -/
def padA (N W : Nat) (A : BitVec (N * N * W)) : BitVec ((N * N + 3) * W) := A.setWidth ((N * N + 3) * W)

/-- `B` zero-extended to the `b_sh` register's width. -/
def padB (N W : Nat) (B : BitVec (N * N * W)) : BitVec ((N * N + 3 * N) * W) := B.setWidth ((N * N + 3 * N) * W)

/-- The `A` window of step `t + m`, as the shifted register shows it. -/
theorem eA {t i N W : Nat} (m : Nat) : t * W + (i * N + m) * W = (i * N + (t + m)) * W := by
  rw [← Nat.add_mul]; congr 1; omega

/-- The `B` window of step `t + m`, as the shifted register shows it. -/
theorem eB {t j N W : Nat} (m : Nat) : t * (N * W) + (m * N + j) * W = ((t + m) * N + j) * W := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]; omega

/-- **PE `(i, j)` in a busy cycle** adds `Σ_{m<4} A[i][t+m]·B[t+m][j]` to its accumulator. -/
theorem pe_step {N W AccW : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {t i j : Nat} (hi : i < N)
    (hj : j < N) : peQ N W AccW (knownBit false) (knownBit true) (accC N W AccW A B t)
      (.ofBitVec (padA N W A >>> (t * W))) (.ofBitVec (padB N W B >>> (t * (N * W)))) i j =
      [("C", (i * N + j) * AccW,
        .ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 4) ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have hr : i * N + j < N * N := by
    have := Lib.rowMajor_window_le (w := 1) hi hj
    simp at this
    omega
  have wa0 : i * N * W + W ≤ (N * N + 3) * W := by
    simpa using winA_le (N := N) (W := W) (i := i) 0 (by omega) hi
  have wa1 := winA_le (N := N) (W := W) (i := i) 1 (by omega) hi
  have wa2 := winA_le (N := N) (W := W) (i := i) 2 (by omega) hi
  have wa3 := winA_le (N := N) (W := W) (i := i) 3 (by omega) hi
  have wb0 : j * W + W ≤ (N * N + 3 * N) * W := by
    simpa using winB_le (N := N) (W := W) (j := j) 0 (by omega) hj
  have wb1 : (N + j) * W + W ≤ (N * N + 3 * N) * W := by
    simpa using winB_le (N := N) (W := W) (j := j) 1 (by omega) hj
  have wb2 := winB_le (N := N) (W := W) (j := j) 2 (by omega) hj
  have wb3 := winB_le (N := N) (W := W) (j := j) 3 (by omega) hj
  have hpA : N * N * W ≤ (N * N + 3) * W := Nat.mul_le_mul_right W (by omega)
  have hpB : N * N * W ≤ (N * N + 3 * N) * W := Nat.mul_le_mul_right W (by omega)
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  have eA1 := eA (t := t) (i := i) (N := N) (W := W) 1
  have eA2 := eA (t := t) (i := i) (N := N) (W := W) 2
  have eA3 := eA (t := t) (i := i) (N := N) (W := W) 3
  have eB1 : t * (N * W) + (N + j) * W = ((t + 1) * N + j) * W := by
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]; omega
  have eB2 := eB (t := t) (j := j) (N := N) (W := W) 2
  have eB3 := eB (t := t) (j := j) (N := N) (W := W) 3
  simp (disch := omega) only [peQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, peV, mulV, sxv, accC, padA,
    padB, LVec.extract_ofBitVec, extractLsb'_packBV, hd, hm, LVec.concatMany_singleton,
    LVec.concatMany_cons_cons, LVec.replVec_ofBitVec, LVec.concat_ofBitVec,
    LVec.ofBitVec_replicate_append_eq_signExtend hW, LVec.mul_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec,
    BitVec.setWidth_eq, setWidth_add4_mul_signExtend, Lib.extractLsb'_ushiftRight, extractLsb'_setWidth_of_le,
    e1, e2, eA1, eA2, eA3, eB1, eB2, eB3, psum_add4, BitVec.ofInt_add, Tasks.Matmul.entry]

/-! ## 4. The spec's arithmetic: `product` is the packed vector of the wrapped dot products -/

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) : Tasks.Matmul.product N W AccW a b =
    packBV AccW (N * N) fun r => BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

/-- After `N` busy cycles the accumulators hold the product (`psum N` is `dot`). -/
theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

/-! ## 5. The registers through a cycle: the commit, then the invariant on `k` -/

section commit
variable {ck r s a b dn c k bz ash bsh : LVec} {lo : Nat} {v : LVec}
theorem nb_busy : nbaStep (MS ck r s a b dn c k bz ash bsh) ("busy", lo, v) =
    MS ck r s a b dn c k (bz.insertAt lo v) ash bsh := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_done : nbaStep (MS ck r s a b dn c k bz ash bsh) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c k bz ash bsh := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_k : nbaStep (MS ck r s a b dn c k bz ash bsh) ("k", lo, v) =
    MS ck r s a b dn c (k.insertAt lo v) bz ash bsh := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ash : nbaStep (MS ck r s a b dn c k bz ash bsh) ("a_sh", lo, v) =
    MS ck r s a b dn c k bz (ash.insertAt lo v) bsh := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bsh : nbaStep (MS ck r s a b dn c k bz ash bsh) ("b_sh", lo, v) =
    MS ck r s a b dn c k bz ash (bsh.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

/-- Committing writes of `C` only. -/
theorem commit_C {ck r s a b dn k bz ash bsh : LVec} : ∀ {q : NbaQueue2}, (∀ u ∈ q, u.1 = "C") → ∀ c,
    commitNba2 (MS ck r s a b dn c k bz ash bsh) q =
      MS ck r s a b dn (q.foldl (fun acc u => acc.insertAt u.2.1 u.2.2) c) k bz ash bsh
  | [], _, _ => rfl
  | ⟨n, lo, v⟩ :: q, h, c => by
    obtain rfl : n = "C" := h _ List.mem_cons_self
    rw [commitNba2_cons, List.foldl_cons, ← commit_C (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    congr 1

/-- The PEs' updates, row-major, when PE `(i, j)` writes window `i·N + j` with `g (i·N + j)`. -/
theorem rowMajor_map {N AccW : Nat} {q : Nat → Nat → NbaQueue2} (g : Nat → LVec)
    (h : ∀ i j, i < N → j < N → q i j = [("C", (i * N + j) * AccW, g (i * N + j))]) :
    ((List.range N).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (N * N)).map fun r => ("C", r * AccW, g r) := by
  suffices ∀ M, M ≤ N → ((List.range M).flatMap fun i => (List.range N).flatMap (q i)) =
      (List.range (M * N)).map (fun r => ("C", r * AccW, g r)) from this N (Nat.le_refl _)
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

theorem commit_map {ck r s a b dn k bz ash bsh : LVec} (AccW : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) :
    commitNba2 (MS ck r s a b dn c k bz ash bsh) ((List.range n).map fun r => ("C", r * AccW, g r)) =
      MS ck r s a b dn (LVec.insertEntries AccW g n c) k bz ash bsh := by
  rw [commit_C (by simp), List.foldl_map]; rfl

theorem toNat_mul_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hab : a * b < 2 ^ w) :
    (BitVec.ofNat w a * BitVec.ofNat w b).toNat = a * b := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hab]

theorem toNat_mul3_lt {w a b c : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) (hc : c < 2 ^ w)
    (hab : a * b < 2 ^ w) (habc : a * b * c < 2 ^ w) :
    (BitVec.ofNat w a * BitVec.ofNat w b * BitVec.ofNat w c).toNat = a * b * c := by
  rw [BitVec.toNat_mul, toNat_mul_lt ha hb hab, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt habc]

/-- The control in a busy cycle `t < N`: `k` steps by four, the shift registers shift by four entries / rows;
the cycle that reaches `N` ends. -/
theorem ctrl_busy {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t < N) (ck a b c : LVec) :
    commitNba2 (MS ck (knownBit false) (knownBit false) a b (knownBit false) c (.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) (.ofBitVec (padA N W A >>> (t * W))) (.ofBitVec (padB N W B >>> (t * (N * W)))))
      (ctrlQ N W (knownBit false) (knownBit false) a b (knownBit false) (.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (.ofBitVec (padA N W A >>> (t * W))) (.ofBitVec (padB N W B >>> (t * (N * W))))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (N ≤ t + 4))) c
      (.ofBitVec (BitVec.ofNat 32 (t + 4))) (knownBit (decide (¬ N ≤ t + 4)))
      (.ofBitVec (padA N W A >>> (t * W + 2 * W + 2 * W)))
      (.ofBitVec (padB N W B >>> (t * (N * W) + 2 * N * W + 2 * N * W))) := by
  simp only [Nat.reducePow] at hr
  have h1 : N * W ≤ N * N * W := by rw [Nat.mul_assoc N N W]; exact Nat.le_mul_of_pos_left _ hN
  have hNW : N * W < 2 ^ 31 := by simp only [Nat.reducePow]; omega
  have hN31 : N < 2 ^ 31 := by
    have : N ≤ N * W := Nat.le_mul_of_pos_right N hW
    simp only [Nat.reducePow]; omega
  have hW31 : W < 2 ^ 31 := by
    have : W ≤ N * W := Nat.le_mul_of_pos_left W hN
    simp only [Nat.reducePow]; omega
  have hN' : N < 2 ^ 32 := by simp only [Nat.reducePow]; omega
  have hW' : W < 2 ^ 32 := by simp only [Nat.reducePow]; omega
  have h2 : 2 < 2 ^ 32 := by decide
  have h2W : 2 * W < 2 ^ 32 := by simp only [Nat.reducePow]; omega
  have h2N : 2 * N < 2 ^ 32 := by simp only [Nat.reducePow]; omega
  have h2NW : 2 * N * W < 2 ^ 32 := by
    rw [Nat.mul_assoc]; simp only [Nat.reducePow]; omega
  have hyW : (BitVec.ofNat 32 2 * BitVec.ofNat 32 W).toNat = 2 * W := toNat_mul_lt h2 hW' h2W
  have hyNW : (BitVec.ofNat 32 2 * BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = 2 * N * W :=
    toNat_mul3_lt h2 hN' hW' h2N h2NW
  have h2' : LVec.ofInt 32 2 = LVec.ofBitVec 2#32 := by decide
  have h4' : LVec.ofInt 32 4 = LVec.ofBitVec 4#32 := by decide
  simp only [ctrlQ, shA, shB, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, h2', h4',
    LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.mul_ofBitVec,
    LVec.add_ofBitVec, LVec.ge_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq, ge_four_iff ht hN31,
    LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW,
    ← BitVec.shiftRight_add]
  by_cases hf : N ≤ t + 4 <;>
    simp [hf, commitNba2_cons, commitNba2_nil, nb_k, nb_ash, nb_bsh, nb_busy, nb_done,
      LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1, BitVec.ofNat_add_ofNat]

/-- **The invariant on `k`, one step**: from the state `t < N` steps after a start with operands `A`, `B`
(`acc[i][j] = Σ_{k' < t} A[i][k']·B[k'][j] mod 2^AccW`, `k = t`, the operands shifted by `t` entries), one cycle
without `start` reaches the state at `t + 4`; `done` rises (and `busy` falls) exactly when `N ≤ t + 4`. -/
theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) (accC N W AccW A B t)
      (.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (.ofBitVec (padA N W A >>> (t * W)))
      (.ofBitVec (padB N W B >>> (t * (N * W)))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (N ≤ t + 4))) (accC N W AccW A B (t + 4))
      (.ofBitVec (BitVec.ofNat 32 (t + 4))) (knownBit (decide (¬ N ≤ t + 4)))
      (.ofBitVec (padA N W A >>> ((t + 4) * W))) (.ofBitVec (padB N W B >>> ((t + 4) * (N * W)))) := by
  have hq := rowMajor_map (N := N) (AccW := AccW) (q := peQ N W AccW (knownBit false) (knownBit true)
    (accC N W AccW A B t) (.ofBitVec (padA N W A >>> (t * W))) (.ofBitVec (padB N W B >>> (t * (N * W)))))
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 4) (r / N) (r % N))))
    (fun i j hi hj => pe_step hW A B hi hj)
  have eA4 : t * W + 2 * W + 2 * W = (t + 4) * W := by rw [Nat.add_mul]; omega
  have eB4 : t * (N * W) + 2 * N * W + 2 * N * W = (t + 4) * (N * W) := by
    simp only [Nat.add_mul, Nat.mul_assoc]; omega
  rw [mmNext, commitNba2_append, ctrl_busy hN hW hr A B ht, hq, commit_map,
    LVec.insertEntries_ofBitVec _ _ (by simp [accC]), eA4, eB4]
  rfl

/-! ## 6. Shape and termination -/

/-- The register widths are the declared ones. -/
def Wd (N W AccW : Nat) (dn c k bz ash bsh : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧ ash.width = (N * N + 3) * W ∧
    bsh.width = (N * N + 3 * N) * W

/-- A snapshot of the design's shape. -/
def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh, st = MS ck r s a b dn c k bz ash bsh ∧ Wd N W AccW dn c k bz ash bsh

theorem peQ_C (N W AccW : Nat) (s bz c ash bsh : LVec) :
    ∀ u ∈ (List.range N).flatMap fun i => (List.range N).flatMap (peQ N W AccW s bz c ash bsh i), u.1 = "C" := by
  intro u hu
  simp only [List.mem_flatMap] at hu
  obtain ⟨_, _, _, _, hu⟩ := hu
  unfold peQ at hu
  by_cases h1 : s.condTrue = true <;> by_cases h2 : bz.condTrue = true <;> simp_all

/-- **Every cycle keeps the design's shape** (any values, `x` included). -/
theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz ash bsh : LVec) (hw : Wd N W AccW dn c k bz ash bsh) :
    I N W AccW (mmNext N W AccW ck r s a b dn c k bz ash bsh) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  simp only [mmNext, commitNba2_append, ctrlQ]
  by_cases c1 : r.condTrue = true <;> by_cases c2 : s.condTrue = true <;> by_cases c3 : bz.condTrue = true <;>
    by_cases c4 : (LVec.ofLogic ((k.add (LVec.ofInt 32 4)).ge (LVec.ofInt 32 (N : Int)))).condTrue = true <;>
    simp only [c1, c2, c3, c4, Bool.false_eq_true, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy, nb_done, nb_k,
      nb_ash, nb_bsh, wr] <;>
    rw [commit_C (peQ_C N W AccW _ _ _ _ _)] <;>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, width_foldl_insertAt, *]⟩

theorem mm_noq (N W AccW : Nat) : (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmCtrl, mmPEs, mmPE, mulT, nb, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
    Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1, .xVec (N * N * AccW),
    .xVec 32, .xVec 1, .xVec ((N * N + 3) * W), .xVec ((N * N + 3 * N) * W), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

/-- **Termination**: every schedule and every stimulus completes. -/
theorem mm_terminates (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Terminates2 (design.sem N W AccW) := by
  refine Terminates2.of_invariant (I N W AccW) (mm_init N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
    (run2ClockGuard_ok_of_profile (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_profile N W AccW))
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz ash bsh kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh hw⟩

/-! ## 7. The protocol: the phases of `TxTask.satisfiedAt_of_phases`, and the statement -/

theorem MS_inj {ck r s a b dn c k bz ash bsh ck' r' s' a' b' dn' c' k' bz' ash' bsh' : LVec}
    (h : MS ck r s a b dn c k bz ash bsh = MS ck' r' s' a' b' dn' c' k' bz' ash' bsh') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ ash = ash' ∧ bsh = bsh' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- A cycle without `rst` and `start` from an idle state (`busy` = 0) changes no register. -/
theorem next_idle (N W AccW : Nat) (ck a b dn c k ash bsh : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bsh =
      MS ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bsh := by
  have h : ((List.range N).flatMap fun i => (List.range N).flatMap
      (peQ N W AccW (knownBit false) (knownBit false) c ash bsh i)) = [] := by simp [List.flatMap_eq_nil_iff, peQ]
  rw [mmNext, h]; simp [ctrlQ]; rfl

/-- A reset cycle clears `busy` and `done`. -/
theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz ash bsh : LVec) (hw : Wd N W AccW dn c k bz ash bsh) :
    ∃ c' k', mmNext N W AccW ck (knownBit true) s a b dn c k bz ash bsh =
      MS ck (knownBit true) s a b (knownBit false) c' k' (knownBit false) ash bsh := by
  obtain ⟨h1, -, -, h4, -, -⟩ := hw
  simp only [mmNext, commitNba2_append, ctrlQ, condTrue_knownBit, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, wr, h1, h4, LVec.resizeU_one_l0]
  rw [commit_C (peQ_C N W AccW _ _ _ _ _)]
  exact ⟨_, _, by rw [LVec.insertAt_zero_of_width_eq (v := dn) (p := knownBit false) (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (v := bz) (p := knownBit false) (by simp [h4])]⟩

/-- A start cycle captures the operands and clears the accumulators: the state at `t = 0`. -/
theorem next_start {N W AccW : Nat} (A B : BitVec (N * N * W)) (ck dn c k bz ash bsh : LVec)
    (hw : Wd N W AccW dn c k bz ash bsh) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) dn c k bz ash bsh =
      MS ck (knownBit false) (knownBit true) (.ofBitVec A) (.ofBitVec B) (knownBit false) (accC N W AccW A B 0)
        (.ofBitVec (BitVec.ofNat 32 0)) (knownBit true) (.ofBitVec (padA N W A >>> (0 * W)))
        (.ofBitVec (padB N W B >>> (0 * (N * W)))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw
  have hq := rowMajor_map (N := N) (AccW := AccW) (q := peQ N W AccW (knownBit true) bz c ash bsh)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N))))
    (fun i j _ _ => by simp [peQ, psum])
  rw [mmNext, commitNba2_append, hq]
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, nb_ash, nb_bsh, wr, h1, h3, h4, h5, h6, LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.replicate_l0,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  rw [commit_map, LVec.insertEntries_ofBitVec _ _ h2, LVec.insertAt_zero_of_width_eq (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (by simp [h3]), LVec.insertAt_zero_of_width_eq (by simp [h4]),
    LVec.insertAt_zero_of_width_eq (by simp [h5]), LVec.insertAt_zero_of_width_eq (by simp [h6])]
  simp [accC, padA, padB]

/-- The state `t` busy cycles after a start with operands `A`, `B` (the invariant on `k`). -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b, st = MS ck r s a b (knownBit false) (accC N W AccW A B t) (.ofBitVec (BitVec.ofNat 32 t))
    (knownBit true) (.ofBitVec (padA N W A >>> (t * W))) (.ofBitVec (padB N W B >>> (t * (N * W))))

/-- Past the last real step the accumulators stay: terms with `k ≥ N` read `B` out of range, as 0. -/
theorem entry_B_zero {N W : Nat} (B : BitVec (N * N * W)) {k j : Nat} (hk : N ≤ k) :
    Tasks.Matmul.entry W B (k * N + j) = 0 := by
  have h : N * N * W ≤ (k * N + j) * W := by
    have h1 : N * N ≤ k * N + j := by
      have := Nat.mul_le_mul_right N hk
      omega
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
  rw [← accC_N]
  simp only [accC, psum_ge]

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k ash bsh, st = MS ck r s a b (knownBit true) (.ofBitVec (Tasks.Matmul.product N W AccW A B)) k
    (knownBit false) ash bsh

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bsh, prev = MS ck r s a b dn c k bz ash bsh ∧ Wd N W AccW dn c k bz ash bsh ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz ash bsh

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = .ofBitVec x.1 ∧ appIn e "B" b = .ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

/-- **The phase model** at `(N, W, AccW)`, latency `N`: `Ready` after a reset, `Busy x m` the state
`t = N - 1 - m` busy cycles after a start, `Fin x` the product shown. -/
def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) ((N + 3) / 4) (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hR32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bsh, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c kk bz ash bsh k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh hw
  Ready st := ∃ ck r s a b c k ash bsh, st = MS ck r s a b (knownBit false) c k (knownBit false) ash bsh
  Busy x m st := ∃ t j, t = 4 * j ∧ j + m + 1 = (N + 3) / 4 ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, ash, bsh, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, j, -, -, ck, r, s, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, ash, bsh, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', h⟩ := next_reset (appIn e "clk" ck) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
      dn c k bz ash bsh hw
    rw [h]; exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb, next_start _ _ _ dn c k bz ash bsh hw]
    exact .inr ⟨(N + 3) / 4 - 1, by omega, 0, 0, by omega, by omega, _, _, _, _, _, rfl⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, -, rfl⟩ ⟨t, j, htj, hj, ck', r', s', a', b', hb⟩
      hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    have htN : t < N := by omega
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_step hN hW hNW _ _ htN]
    by_cases hf : N ≤ t + 4
    · left
      simp only [hf, accC_ge N W AccW _ _ hf, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, rfl⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 4, j + 1, by omega, by omega, _, _, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, -, rfl⟩ ⟨ck', r', s', a', b', c', k', ash',
      bsh', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, -, rfl⟩ ⟨ck', r', s', a', b', k', ash',
      bsh', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_sh", "b_sh"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · simp [Tasks.Matmul.task, mmCtrl, nb, c32, amtA, amtB, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · obtain ⟨i, j, rfl⟩ := mm_pe_mem hm
    simp [Tasks.Matmul.task, mmPE, mulT, sext, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      lhsNames, exprNames, exprListNames]

/-! ## 8. txtask-v2: every power-up (rule 2), Moore outputs (rule 1), no x-creating construct (rule 3)

Rule 2: the phase model's shape `I` (the register widths, any values) holds at every power-up state
(`mm_powerUp`), and every obligation of the model holds from any state of the shape, so the claim holds
from every power-up (`TxTask.satisfiedAtV2_of_phases`, `SvGolf.SeqV2`); the same cycle gives
termination from every power-up (`mm_terminatesPU`). Rule 1: every process is an `always_ff`
(`mm_profile`), so the design has no combinational dependency at all (`combDeps_of_ffOnly`). Rule 3
(`mm_xsafe`): every expression is a known literal, a declared signal, an in-range constant slice
(`C`'s windows, the operand entries), a concatenation, a replication, a width conversion or `+`, `-`,
`*`, `>>`, `==` on operands of matching widths. -/

/-- **Rule 1.** -/
theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

/-- Every power-up state of the design has its shape. -/
theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA hR32] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨k, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨ash, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bsh, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain rfl := powerUp_nil.mp h11
  exact ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, w6, w7, w8, w9, w10, w11⟩

/-- **Termination from every power-up** (the cycle of `mm_terminates`). -/
theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bsh, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz ash bsh kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bsh hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

/-- The control passes rule 3. -/
theorem ctrl_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (mmCtrl N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmCtrl, nb, c32, amtA, amtB, mmD, mmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

/-- A PE passes rule 3: its windows of `C` and of the operand registers are in range. -/
theorem pe_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (mmPE N W AccW i j) = true := by
  have hN : 0 < N := by omega
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have wa0 : i * N * W + W ≤ (N * N + 3) * W := by
    simpa using winA_le (N := N) (W := W) (i := i) 0 (by omega) hi
  have wa1 := winA_le (N := N) (W := W) (i := i) 1 (by omega) hi
  have wa2 := winA_le (N := N) (W := W) (i := i) 2 (by omega) hi
  have wa3 := winA_le (N := N) (W := W) (i := i) 3 (by omega) hi
  have wb0 : j * W + W ≤ (N * N + 3 * N) * W := by
    simpa using winB_le (N := N) (W := W) (j := j) 0 (by omega) hj
  have wb1 := winB_le (N := N) (W := W) (j := j) 1 (by omega) hj
  have wb2 := winB_le (N := N) (W := W) (j := j) 2 (by omega) hj
  have wb3 := winB_le (N := N) (W := W) (j := j) 3 (by omega) hj
  have sa0 : i * N * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa1 : (i * N + 1) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa2 : (i * N + 2) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa3 : (i * N + 3) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have wb1' : (N + j) * W + W ≤ (N * N + 3 * N) * W := by
    simpa using winB_le (N := N) (W := W) (j := j) 1 (by omega) hj
  have wb2' : (2 * N + j) * W + W ≤ (N * N + 3 * N) * W := winB_le (N := N) (W := W) (j := j) 2 (by omega) hj
  have wb3' : (3 * N + j) * W + W ≤ (N * N + 3 * N) * W := winB_le (N := N) (W := W) (j := j) 3 (by omega) hj
  have sb0 : j * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
  have sb1 : (N + j) * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
  have sb2 : (2 * N + j) * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
  have sb3 : (3 * N + j) * W + W - 1 + 1 ≤ (N * N + 3 * N) * W := by omega
  have sa0 : i * N * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa1 : (i * N + 1) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa2 : (i * N + 2) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  have sa3 : (i * N + 3) * W + W - 1 + 1 ≤ (N * N + 3) * W := by omega
  simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmPE, mulT, sext, mmD, mmDecls,
    LVec.replicate_l0, hC, wa0, wa1, wa2, wa3, wb0, wb1', wb2', wb3', sa0, sa1, sa2, sa3, sb0, sb1, sb2, sb3]

theorem mm_pe_mem' {N W AccW : Nat} {p : Process2} (hp : p ∈ mmPEs N W AccW) :
    ∃ i j, i < N ∧ j < N ∧ p = mmPE N W AccW i j := by
  simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, j, hj, rfl⟩ := hp
  exact ⟨i, j, hi, hj, rfl⟩

/-- **Rule 3.** -/
theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ mmCtrl N W :: mmPEs N W AccW := by simpa [mmD] using hp
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ctrl_xsafe N W AccW
  · obtain ⟨i, j, hi, hj, rfl⟩ := mm_pe_mem' hm
    exact pe_xsafe hW hi hj

/-- **The reference satisfies the matmul statement (txtask-v2) at latency `N`** (`4` at the scoring
point). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hNW : N * N * W < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hW127) (by decide)
  have hNA : N * N * AccW < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hA64) (by decide)
  have hR32 : Rng32 N W AccW := rng32_of hN hW hA hNW hNA
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA hR32)
    (mm_disciplined N W AccW hN hW hA hR32) (mm_terminatesPU N W AccW hN hW hA hR32)
    (show 1 ≤ (N + 3) / 4 by omega) (model N W AccW hN hW hA hR32 hNW) (mm_powerUp N W AccW hN hW hA hR32) (mm_moore N W AccW hN hW hA hR32)
    (mm_xsafe N W AccW hN hW hA hR32)

end Submission
