-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Common helpers -/

def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r =>
    BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B (t + 1) i j =
      psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) :
    Tasks.Matmul.product N W AccW a b =
      packBV AccW (N * N) fun r =>
        BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

theorem knownBit_false_eq : knownBit false = ⟨#[.l0]⟩ := by
  symm; rw [knownBit, LVec.eq_ofBitVec_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  decide

theorem knownBit_true_eq : knownBit true = ⟨#[.l1]⟩ := by
  symm; rw [knownBit, LVec.eq_ofBitVec_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  decide

@[simp] theorem width_knownBit (b : Bool) : (knownBit b).width = 1 := by simp [knownBit]

theorem mem_of_mem_ite_nil {α : Type} {P : Prop} [Decidable P] {l : List α} {x : α}
    (h : x ∈ if P then l else []) : x ∈ l := by
  by_cases hP : P
  · simpa [hP] using h
  · simp [hP] at h

theorem isKnownZero_knownBit (b : Bool) : (knownBit b).isKnownZero = !b := by
  cases b
  · rw [knownBit_false_eq, LVec.isKnownZero, ← Array.all_toList]; rfl
  · rw [knownBit_true_eq, LVec.isKnownZero, ← Array.all_toList]; rfl

theorem lor_cond_knownBit (b1 b2 : Bool) :
    (LVec.ofLogic
      (if (SymBinOp.lor == SymBinOp.land) = true then
        if ((knownBit b1).isKnownZero || (knownBit b2).isKnownZero) = true then Logic.l0
        else if ((knownBit b1).condTrue && (knownBit b2).condTrue) = true then Logic.l1 else Logic.lx
      else
        if ((knownBit b1).condTrue || (knownBit b2).condTrue) = true then Logic.l1
        else if ((knownBit b1).isKnownZero && (knownBit b2).isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue =
      (b1 || b2) := by
  have hne : (SymBinOp.lor == SymBinOp.land) = false := by decide
  have hl0 : (LVec.ofLogic Logic.l0).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  have hl1 : (LVec.ofLogic Logic.l1).condTrue = true := by simp [LVec.ofLogic, LVec.condTrue]
  cases b1 <;> cases b2 <;>
    simp only [hne, condTrue_knownBit, isKnownZero_knownBit, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.or_true, Bool.or_false, Bool.and_self, hl0, hl1]

theorem lor_cond_true_left (x : LVec) :
    (LVec.ofLogic
      (if (SymBinOp.lor == SymBinOp.land) = true then
        if ((knownBit true).isKnownZero || x.isKnownZero) = true then Logic.l0
        else if ((knownBit true).condTrue && x.condTrue) = true then Logic.l1 else Logic.lx
      else
        if ((knownBit true).condTrue || x.condTrue) = true then Logic.l1
        else if ((knownBit true).isKnownZero && x.isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue =
      true := by
  have hne : (SymBinOp.lor == SymBinOp.land) = false := by decide
  have hl1 : (LVec.ofLogic Logic.l1).condTrue = true := by simp [LVec.ofLogic, LVec.condTrue]
  simp only [hne, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, Bool.true_or, hl1]

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

theorem rowMajor_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem flatMap_range_singleton {N : Nat} {α : Type} (f : Nat → List α) {g : Nat → α}
    (h : ∀ j, j < N → f j = [g j]) :
    (List.range N).flatMap f = (List.range N).map g := by
  rw [CombView.flatMap_congr' (fun j hj => h j (List.mem_range.mp hj))]
  induction (List.range N) with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem flatMap_range_rowMajor {N : Nat} {α : Type} {f : Nat → Nat → List α} (g : Nat → α)
    (h : ∀ i j, i < N → j < N → f i j = [g (i * N + j)]) :
    ((List.range N).flatMap fun i => (List.range N).flatMap (f i)) =
      (List.range (N * N)).map g := by
  suffices ∀ M, M ≤ N → ((List.range M).flatMap fun i => (List.range N).flatMap (f i)) =
      (List.range (M * N)).map g from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [flatMap_range_singleton _ fun j hj => h M j (by omega) hj]
    rfl

theorem nbaFold_map_insertEntries (s : String) (AccW : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) :
    nbaFold s ((List.range n).map fun r => (s, r * AccW, g r)) c = LVec.insertEntries AccW g n c := by
  unfold nbaFold LVec.insertEntries
  rw [List.foldl_map]
  simp

@[simp] theorem nbaFold_width (s : String) : ∀ (q : NbaQueue2) (v : LVec), (nbaFold s q v).width = v.width
  | [], _ => rfl
  | u :: q, v => by
    rw [nbaFold_cons, nbaFold_width s q]
    split <;> simp

theorem nbaFold_disj (s : String) : ∀ (q : NbaQueue2) (v : LVec),
    (∀ u ∈ q, u.1 ≠ s) → nbaFold s q v = v
  | [], _, _ => rfl
  | u :: q, v, h => by
    rw [nbaFold_cons, ite_eq_right (h u List.mem_cons_self)]
    exact nbaFold_disj s q v fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem signExtend_eq_ofInt {n w : Nat} (h : w ≤ n) (x : BitVec w) :
    x.signExtend n = BitVec.ofInt n x.toInt := by
  have hbmod : x.toInt.bmod (2 ^ w) = x.toInt := by
    have := congrArg BitVec.toInt (BitVec.ofInt_toInt (x := x))
    rwa [BitVec.toInt_ofInt] at this
  rw [← BitVec.ofInt_toInt (x := x.signExtend n), BitVec.toInt_signExtend, Nat.min_eq_right h, hbmod]

theorem ofInt_sub_eq {w : Nat} (a b : Int) :
    BitVec.ofInt w a - BitVec.ofInt w b = BitVec.ofInt w (a - b) := by
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add, Int.sub_eq_add_neg]

theorem setWidth_ofInt_le {m n : Nat} (h : m ≤ n) (z : Int) :
    (BitVec.ofInt n z).setWidth m = BitVec.ofInt m z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  apply Int.ofNat.inj
  change (((z % (2 : Int) ^ n).toNat % 2 ^ m : Nat) : Int) = ((z % (2 : Int) ^ m).toNat : Int)
  have hne : ∀ k : Nat, ((2 : Int) ^ k) ≠ 0 := fun k => by
    have := Int.natCast_ne_zero.mpr (Nat.ne_of_gt (Nat.two_pow_pos k))
    simpa using this
  have hdvd : ((2 : Int) ^ m) ∣ ((2 : Int) ^ n) := by
    have := Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
    simpa using this
  rw [Int.natCast_emod, Int.natCast_pow, show (↑(2 : Nat) : Int) = 2 from rfl,
    Int.toNat_of_nonneg (Int.emod_nonneg z (hne n)),
    Int.toNat_of_nonneg (Int.emod_nonneg z (hne m)),
    Int.emod_emod_of_dvd z hdvd]

/-! ## 2. Branch 1: N = 2 (Strassen 2x2 tile) -/

sv_mirror mmS := design (N W AccW : Nat) (hN2 : N = 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem mmS_disj (N W AccW : Nat) :
    (mmS.procs N W AccW).Pairwise ProcDisj := by
  simp only [mmS.procs, List.cons_append, List.nil_append]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;>
      exact ProcDisj.of_all (by simp [mmS.p0, mmS.gen, mmS.gen_1, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq
    exact ProcDisj.of_all (by simp [mmS.gen, mmS.gen_1, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · intro _ h; cases h

sv_cycle mmS using mmS_disj N W AccW

section Strassen

def strP0 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW ((Tasks.Matmul.entry W A 0 + Tasks.Matmul.entry W A 3) *
    (Tasks.Matmul.entry W B 0 + Tasks.Matmul.entry W B 3))

def strP1 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW ((Tasks.Matmul.entry W A 2 + Tasks.Matmul.entry W A 3) *
    Tasks.Matmul.entry W B 0)

def strP2 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW (Tasks.Matmul.entry W A 0 *
    (Tasks.Matmul.entry W B 1 - Tasks.Matmul.entry W B 3))

def strP3 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW (Tasks.Matmul.entry W A 3 *
    (Tasks.Matmul.entry W B 2 - Tasks.Matmul.entry W B 0))

def strP4 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW ((Tasks.Matmul.entry W A 0 + Tasks.Matmul.entry W A 1) *
    Tasks.Matmul.entry W B 3)

def strP5 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW ((Tasks.Matmul.entry W A 2 - Tasks.Matmul.entry W A 0) *
    (Tasks.Matmul.entry W B 0 + Tasks.Matmul.entry W B 1))

def strP6 (W AccW : Nat) (A B : BitVec (2 * 2 * W)) : BitVec AccW :=
  BitVec.ofInt AccW ((Tasks.Matmul.entry W A 1 - Tasks.Matmul.entry W A 3) *
    (Tasks.Matmul.entry W B 2 + Tasks.Matmul.entry W B 3))

theorem strassen_entry_sext {W AccW : Nat} (hW : 1 ≤ W) (M : BitVec (2 * 2 * W)) (idx : Nat) (hi : idx < 4) :
    LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec M).extract (idx * W + W - 1) 1]),
      (LVec.ofBitVec M).extract (idx * W) W] =
    LVec.ofBitVec (BitVec.ofInt (AccW + W) (Tasks.Matmul.entry W M idx)) := by
  have hex : (LVec.ofBitVec M).extract (idx * W) W = LVec.ofBitVec (M.extractLsb' (idx * W) W) :=
    LVec.extract_ofBitVec M (by
      have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at this
      omega)
  rw [LVec.sext_of_extract hW hex, signExtend_eq_ofInt (by omega)]
  rfl

theorem concatMany_four_packBV {AccW : Nat} (hA : 1 ≤ AccW) (c3 c2 c1 c0 : BitVec AccW) :
    ((LVec.concatMany #[LVec.ofBitVec c3, LVec.ofBitVec c2, LVec.ofBitVec c1, LVec.ofBitVec c0]).resizeU
      ((4 * (AccW : Int) - 1).natAbs + 1)) =
    LVec.ofBitVec (packBV AccW 4 fun r =>
      if r = 0 then c0 else if r = 1 then c1 else if r = 2 then c2 else c3) := by
  have h4A : (4 * (AccW : Int) - 1).natAbs + 1 = 4 * AccW := by omega
  rw [h4A]
  simp only [LVec.concatMany_cons_cons, LVec.concatMany_singleton, LVec.concat_ofBitVec,
    LVec.resizeU_ofBitVec]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨r, m, hr, hm, him⟩ : ∃ r m, r < 4 ∧ m < AccW ∧ i = r * AccW + m :=
    ⟨i / AccW, i % AccW, Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt i (by omega), by
      have := Nat.div_add_mod i AccW; rw [Nat.mul_comm] at this; exact this.symm⟩
  have hpack : (packBV AccW 4 fun r =>
      if r = 0 then c0 else if r = 1 then c1 else if r = 2 then c2 else c3).getLsbD i =
      (if r = 0 then c0 else if r = 1 then c1 else if r = 2 then c2 else c3).getLsbD m := by
    have hex := extractLsb'_packBV (W := AccW)
      (fun r => if r = 0 then c0 else if r = 1 then c1 else if r = 2 then c2 else c3) hr
    have hg := congrArg (fun bv => bv.getLsbD m) hex
    rw [BitVec.getLsbD_extractLsb', show decide (m < AccW) = true from decide_eq_true hm,
      Bool.true_and, ← him] at hg
    exact hg
  rw [hpack, BitVec.getLsbD_setWidth, show decide (i < 4 * AccW) = true from decide_eq_true hi,
    Bool.true_and]
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_append]
  have hr0123 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hr0123 with rfl | rfl | rfl | rfl
  · have hlt1 : i < AccW := by omega
    have hlt2 : i < AccW + AccW := by omega
    have hlt3 : i < AccW + (AccW + AccW) := by omega
    simp [hlt1, hlt2, hlt3, show m = i by omega]
  · have hlt1 : ¬ i < AccW := by omega
    have hlt2 : i < AccW + AccW := by omega
    have hlt3 : i < AccW + (AccW + AccW) := by omega
    simp [hlt1, hlt2, hlt3, show i - AccW = m by omega]
  · have hlt1 : ¬ i < AccW + AccW := by omega
    have hlt2 : i < AccW + (AccW + AccW) := by omega
    simp [hlt1, hlt2, show i - (AccW + AccW) = m by omega]
  · have hlt1 : ¬ i < AccW + (AccW + AccW) := by omega
    simp [hlt1, show i - (AccW + (AccW + AccW)) = m by omega]

theorem strassen_recombine {W AccW : Nat} (hA : 1 ≤ AccW) (A B : BitVec (2 * 2 * W)) :
    ((LVec.concatMany #[
      (((LVec.ofBitVec (strP0 W AccW A B)).sub (LVec.ofBitVec (strP1 W AccW A B))).add
        (LVec.ofBitVec (strP2 W AccW A B))).add (LVec.ofBitVec (strP5 W AccW A B)),
      (LVec.ofBitVec (strP1 W AccW A B)).add (LVec.ofBitVec (strP3 W AccW A B)),
      (LVec.ofBitVec (strP2 W AccW A B)).add (LVec.ofBitVec (strP4 W AccW A B)),
      (((LVec.ofBitVec (strP0 W AccW A B)).add (LVec.ofBitVec (strP3 W AccW A B))).sub
        (LVec.ofBitVec (strP4 W AccW A B))).add (LVec.ofBitVec (strP6 W AccW A B))
    ]).resizeU ((4 * (AccW : Int) - 1).natAbs + 1)) =
    LVec.ofBitVec (Tasks.Matmul.product 2 W AccW A B) := by
  simp only [strP0, strP1, strP2, strP3, strP4, strP5, strP6,
    LVec.add_ofBitVec, LVec.sub_ofBitVec,
    ← BitVec.ofInt_add, ofInt_sub_eq]
  rw [concatMany_four_packBV hA, product_eq]
  congr 1
  have ha00 : ∀ a00 a01 a10 a11 b00 b01 b10 b11 : Int,
      (a00 + a11) * (b00 + b11) + a11 * (b10 - b00) - (a00 + a01) * b11 + (a01 - a11) * (b10 + b11) =
        a00 * b00 + a01 * b10 := by
    intro a00 a01 a10 a11 b00 b01 b10 b11
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]; omega
  have ha01 : ∀ a00 a01 a10 a11 b00 b01 b10 b11 : Int,
      a00 * (b01 - b11) + (a00 + a01) * b11 = a00 * b01 + a01 * b11 := by
    intro a00 a01 a10 a11 b00 b01 b10 b11
    simp only [Int.add_mul, Int.mul_sub]; omega
  have ha10 : ∀ a00 a01 a10 a11 b00 b01 b10 b11 : Int,
      (a10 + a11) * b00 + a11 * (b10 - b00) = a10 * b00 + a11 * b10 := by
    intro a00 a01 a10 a11 b00 b01 b10 b11
    simp only [Int.add_mul, Int.mul_sub]; omega
  have ha11 : ∀ a00 a01 a10 a11 b00 b01 b10 b11 : Int,
      (a00 + a11) * (b00 + b11) - (a10 + a11) * b00 + a00 * (b01 - b11) + (a10 - a00) * (b00 + b01) =
        a10 * b01 + a11 * b11 := by
    intro a00 a01 a10 a11 b00 b01 b10 b11
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨r, m, hr, hm, him⟩ : ∃ r m, r < 4 ∧ m < AccW ∧ i = r * AccW + m :=
    ⟨i / AccW, i % AccW, Nat.div_lt_of_lt_mul (by omega), Nat.mod_lt i (by omega), by
      have := Nat.div_add_mod i AccW; rw [Nat.mul_comm] at this; exact this.symm⟩
  have hget : ∀ (f : Nat → BitVec AccW), (packBV AccW 4 f).getLsbD (r * AccW + m) = (f r).getLsbD m := fun f => by
    have h := congrArg (fun bv : BitVec AccW => bv.getLsbD m) (extractLsb'_packBV (W := AccW) (n := 4) f hr)
    rwa [BitVec.getLsbD_extractLsb', show decide (m < AccW) = true from decide_eq_true hm, Bool.true_and] at h
  have hget2 := hget (fun r => BitVec.ofInt AccW (Tasks.Matmul.dot 2 W A B (r / 2) (r % 2)))
  rw [him, hget]; exact (hget2.symm ▸ (by
    have hr0123 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr0123 with rfl | rfl | rfl | rfl
    · simp only [↓reduceIte, Tasks.Matmul.dot, List.range_succ, List.range_zero,
        List.foldl_append, List.foldl_nil, List.foldl_cons, Int.zero_add]; congr 2
      simpa using ha00 (Tasks.Matmul.entry W A 0) (Tasks.Matmul.entry W A 1)
        (Tasks.Matmul.entry W A 2) (Tasks.Matmul.entry W A 3)
        (Tasks.Matmul.entry W B 0) (Tasks.Matmul.entry W B 1)
        (Tasks.Matmul.entry W B 2) (Tasks.Matmul.entry W B 3)
    · simp only [Nat.reduceEqDiff, ↓reduceIte, Tasks.Matmul.dot, List.range_succ,
        List.range_zero, List.foldl_append, List.foldl_nil, List.foldl_cons, Int.zero_add]; congr 2
      simpa using ha01 (Tasks.Matmul.entry W A 0) (Tasks.Matmul.entry W A 1)
        (Tasks.Matmul.entry W A 2) (Tasks.Matmul.entry W A 3)
        (Tasks.Matmul.entry W B 0) (Tasks.Matmul.entry W B 1)
        (Tasks.Matmul.entry W B 2) (Tasks.Matmul.entry W B 3)
    · simp only [Nat.reduceEqDiff, ↓reduceIte, Tasks.Matmul.dot, List.range_succ,
        List.range_zero, List.foldl_append, List.foldl_nil, List.foldl_cons, Int.zero_add]; congr 2
      simpa using ha10 (Tasks.Matmul.entry W A 0) (Tasks.Matmul.entry W A 1)
        (Tasks.Matmul.entry W A 2) (Tasks.Matmul.entry W A 3)
        (Tasks.Matmul.entry W B 0) (Tasks.Matmul.entry W B 1)
        (Tasks.Matmul.entry W B 2) (Tasks.Matmul.entry W B 3)
    · simp only [Nat.reduceEqDiff, ↓reduceIte, Tasks.Matmul.dot, List.range_succ,
        List.range_zero, List.foldl_append, List.foldl_nil, List.foldl_cons, Int.zero_add]; congr 2
      simpa using ha11 (Tasks.Matmul.entry W A 0) (Tasks.Matmul.entry W A 1)
        (Tasks.Matmul.entry W A 2) (Tasks.Matmul.entry W A 3)
        (Tasks.Matmul.entry W B 0) (Tasks.Matmul.entry W B 1)
        (Tasks.Matmul.entry W B 2) (Tasks.Matmul.entry W B 3) : _ = _))

def allQS (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) : NbaQueue2 :=
  mmS.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ++
    (mmS.genQ N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ++
      mmS.gen_1Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6)

theorem mmS_next_eq (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmS.next N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      mmS.St ck r s a b
        (nbaFold "done" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) dn)
        (nbaFold "C" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) c)
        (nbaFold "k" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) k)
        (nbaFold "busy" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) bz)
        (nbaFold "A_mem" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) am)
        (nbaFold "B_mem" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) bm)
        (nbaFold "p0" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p0)
        (nbaFold "p1" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p1)
        (nbaFold "p2" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p2)
        (nbaFold "p3" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p3)
        (nbaFold "p4" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p4)
        (nbaFold "p5" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p5)
        (nbaFold "p6" (allQS N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) p6) := by
  have h1 : ∀ (q : NbaQueue2) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec),
      (∀ u ∈ q, u.1 ∈ ["done", "C", "k", "busy", "A_mem", "B_mem",
        "p0", "p1", "p2", "p3", "p4", "p5", "p6"]) →
      commitNba2 (mmS.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) q =
        mmS.St ck r s a b
          (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "k" q k)
          (nbaFold "busy" q bz) (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
          (nbaFold "p0" q p0) (nbaFold "p1" q p1) (nbaFold "p2" q p2)
          (nbaFold "p3" q p3) (nbaFold "p4" q p4) (nbaFold "p5" q p5) (nbaFold "p6" q p6) := by
    intro q; induction q with
    | nil => intros; rfl
    | cons u q ih =>
      intro ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hmem
      obtain ⟨n, lo, v⟩ := u
      have hn : n ∈ ["done", "C", "k", "busy", "A_mem", "B_mem",
          "p0", "p1", "p2", "p3", "p4", "p5", "p6"] := hmem _ List.mem_cons_self
      have hq := fun u hu => hmem u (List.mem_cons_of_mem _ hu)
      rw [commitNba2_cons]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [mmS.St] at ih
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [nbaStep, mmS.St, SvState.lookup, SvState.set, nbaFold_cons,
          ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq]
  apply h1
  intro u hu
  simp only [List.mem_append] at hu
  rcases hu with hu | hu | hu
  · unfold mmS.p0Q at hu
    split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
      · split at hu
        · split at hu
          · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
          · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
        · simp at hu
  · unfold mmS.genQ at hu
    have hu' := mem_of_mem_ite_nil hu
    simp at hu'; rcases hu' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold mmS.gen_1Q at hu
    by_cases hcond : (LVec.ofLogic
        (if (SymBinOp.lor == SymBinOp.land) = true then
          if (r.isKnownZero || s.isKnownZero) = true then Logic.l0
          else if (r.condTrue && s.condTrue) = true then Logic.l1 else Logic.lx
        else
          if (r.condTrue || s.condTrue) = true then Logic.l1
          else if (r.isKnownZero && s.isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue = true
    · simp only [hcond, ↓reduceIte, List.mem_singleton] at hu; rw [hu]; simp
    · simp only [hcond] at hu
      have hu' := mem_of_mem_ite_nil hu
      simp only [List.mem_singleton] at hu'; rw [hu']; simp

def WdS (W AccW : Nat) (dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) : Prop :=
  dn.width = 1 ∧ c.width = 4 * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  am.width = 4 * W ∧ bm.width = 4 * W ∧
  p0.width = AccW ∧ p1.width = AccW ∧ p2.width = AccW ∧ p3.width = AccW ∧
  p4.width = AccW ∧ p5.width = AccW ∧ p6.width = AccW

def IS (W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmS.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdS W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6

theorem mmS_init (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    IS W AccW (initState2 (design.sem 2 W AccW)) := by
  rw [mmS.init 2 W AccW rfl hW hA hW32 hA32]
  have h4W : (4 * (W : Int) - 1).natAbs + 1 = 4 * W := by omega
  have h4A : (4 * (AccW : Int) - 1).natAbs + 1 = 4 * AccW := by omega
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
    by simp, by simp [h4A], by simp, by simp, by simp [h4W], by simp [h4W],
    by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem mmS_next_I (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdS W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    IS W AccW (mmS.next N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) := by
  rw [mmS_next_eq]
  refine ⟨ck, r, s, a, b, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  exact ⟨by rw [nbaFold_width, h1], by rw [nbaFold_width, h2], by rw [nbaFold_width, h3],
    by rw [nbaFold_width, h4], by rw [nbaFold_width, h5], by rw [nbaFold_width, h6],
    by rw [nbaFold_width, h7], by rw [nbaFold_width, h8], by rw [nbaFold_width, h9],
    by rw [nbaFold_width, h10], by rw [nbaFold_width, h11], by rw [nbaFold_width, h12],
    by rw [nbaFold_width, h13]⟩

theorem mmS_St_inj {ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
    ck' r' s' a' b' dn' c' k' bz' am' bm' p0' p1' p2' p3' p4' p5' p6' : LVec}
    (h : mmS.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      mmS.St ck' r' s' a' b' dn' c' k' bz' am' bm' p0' p1' p2' p3' p4' p5' p6') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ am = am' ∧ bm = bm' ∧
    p0 = p0' ∧ p1 = p1' ∧ p2 = p2' ∧ p3 = p3' ∧ p4 = p4' ∧ p5 = p5' ∧ p6 = p6' := by
  simp only [mmS.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem mmS_next_reset {W AccW : Nat}
    (ck s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdS W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    ∃ c' k' am' bm' p0' p1' p2' p3' p4' p5' p6',
      mmS.next 2 W AccW ck (knownBit true) s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
        mmS.St ck (knownBit true) s a b (knownBit false) c' k' (knownBit false)
          am' bm' p0' p1' p2' p3' p4' p5' p6' ∧
      WdS W AccW (knownBit false) c' k' (knownBit false) am' bm' p0' p1' p2' p3' p4' p5' p6' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  let q := allQS 2 W AccW ck (knownBit true) s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
  refine ⟨nbaFold "C" q c, nbaFold "k" q k, nbaFold "A_mem" q am, nbaFold "B_mem" q bm,
    nbaFold "p0" q p0, nbaFold "p1" q p1, nbaFold "p2" q p2, nbaFold "p3" q p3,
    nbaFold "p4" q p4, nbaFold "p5" q p5, nbaFold "p6" q p6, ?_, ?_⟩
  · rw [mmS_next_eq]
    have hdn : nbaFold "done" q dn = knownBit false := by
      simp only [q, allQS, mmS.p0Q, mmS.genQ, mmS.gen_1Q, lor_cond_true_left]
      simp [nbaFold, h1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    have hbz : nbaFold "busy" q bz = knownBit false := by
      simp only [q, allQS, mmS.p0Q, mmS.genQ, mmS.gen_1Q, lor_cond_true_left]
      simp [nbaFold, h4, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    rw [hdn, hbz]
  · exact ⟨by simp, by rw [nbaFold_width, h2], by rw [nbaFold_width, h3], by simp,
      by rw [nbaFold_width, h5], by rw [nbaFold_width, h6],
      by rw [nbaFold_width, h7], by rw [nbaFold_width, h8], by rw [nbaFold_width, h9],
      by rw [nbaFold_width, h10], by rw [nbaFold_width, h11], by rw [nbaFold_width, h12],
      by rw [nbaFold_width, h13]⟩

theorem mmS_next_idle (W AccW : Nat) (ck a b dn c k am bm p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmS.next 2 W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      am bm p0 p1 p2 p3 p4 p5 p6 =
    mmS.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      am bm p0 p1 p2 p3 p4 p5 p6 := by
  rw [mmS_next_eq]
  simp only [allQS, mmS.p0Q, mmS.genQ, mmS.gen_1Q, lor_cond_knownBit]
  simp [nbaFold]

theorem mmS_next_start {W AccW : Nat} (hW : 1 ≤ W) (_hA : 1 ≤ AccW)
    (ck : LVec) (Av Bv : BitVec (2 * 2 * W))
    (dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdS W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    ∃ c' am' bm',
      mmS.next 2 W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      mmS.St ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        (knownBit false) c' (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true)
        am' bm'
        (LVec.ofBitVec (strP0 W AccW Av Bv)) (LVec.ofBitVec (strP1 W AccW Av Bv))
        (LVec.ofBitVec (strP2 W AccW Av Bv)) (LVec.ofBitVec (strP3 W AccW Av Bv))
        (LVec.ofBitVec (strP4 W AccW Av Bv)) (LVec.ofBitVec (strP5 W AccW Av Bv))
        (LVec.ofBitVec (strP6 W AccW Av Bv)) ∧
      c'.width = 4 * AccW ∧ am'.width = 4 * W ∧ bm'.width = 4 * W := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  have h2W : (2 * (W : Int)).toNat = 2 * W := by omega
  have h3W : (3 * (W : Int)).toNat = 3 * W := by omega
  have h4W : (4 * (W : Int)).toNat = 4 * W := by omega
  have hA0 := strassen_entry_sext (AccW := AccW) hW Av 0 (by omega)
  have hA1 := strassen_entry_sext (AccW := AccW) hW Av 1 (by omega)
  have hA2 := strassen_entry_sext (AccW := AccW) hW Av 2 (by omega)
  have hA3 := strassen_entry_sext (AccW := AccW) hW Av 3 (by omega)
  have hB0 := strassen_entry_sext (AccW := AccW) hW Bv 0 (by omega)
  have hB1 := strassen_entry_sext (AccW := AccW) hW Bv 1 (by omega)
  have hB2 := strassen_entry_sext (AccW := AccW) hW Bv 2 (by omega)
  have hB3 := strassen_entry_sext (AccW := AccW) hW Bv 3 (by omega)
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul] at hA0 hA1 hB0 hB1
  rw [show W + W = 2 * W by omega] at hA1 hB1
  rw [show 2 * W + W = 3 * W by omega] at hA2 hB2
  rw [show 3 * W + W = 4 * W by omega] at hA3 hB3
  let q := allQS 2 W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
    dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
  refine ⟨nbaFold "C" q c, nbaFold "A_mem" q am, nbaFold "B_mem" q bm, ?_,
    by rw [nbaFold_width, h2], by rw [nbaFold_width, h5], by rw [nbaFold_width, h6]⟩
  rw [mmS_next_eq]
  change mmS.St _ _ _ _ _ (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "k" q k)
    (nbaFold "busy" q bz) (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
    (nbaFold "p0" q p0) (nbaFold "p1" q p1) (nbaFold "p2" q p2) (nbaFold "p3" q p3)
    (nbaFold "p4" q p4) (nbaFold "p5" q p5) (nbaFold "p6" q p6) = _
  have hq : q =
    [("busy", 0, knownBit true), ("done", 0, knownBit false),
      ("k", 0, LVec.ofBitVec 0#32), ("A_mem", 0, (LVec.ofBitVec Av).resizeU am.width),
      ("B_mem", 0, (LVec.ofBitVec Bv).resizeU bm.width),
      ("p6", 0, LVec.ofBitVec (strP6 W AccW Av Bv)),
      ("p5", 0, LVec.ofBitVec (strP5 W AccW Av Bv)),
      ("p4", 0, LVec.ofBitVec (strP4 W AccW Av Bv)),
      ("p3", 0, LVec.ofBitVec (strP3 W AccW Av Bv)),
      ("p2", 0, LVec.ofBitVec (strP2 W AccW Av Bv)),
      ("p1", 0, LVec.ofBitVec (strP1 W AccW Av Bv)),
      ("p0", 0, LVec.ofBitVec (strP0 W AccW Av Bv)),
      ("C", 0, (LVec.ofBitVec 0#((4 * (AccW : Int) - 1).natAbs + 1)).resizeU c.width)] := by
    simp only [q, allQS, mmS.p0Q, mmS.genQ, mmS.gen_1Q, lor_cond_knownBit]
    simp only [Bool.false_or, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      h1, h3, h4, h7, h8, h9, h10, h11, h12, h13, h2W, h3W, h4W,
      hA0, hA1, hA2, hA3, hB0, hB1, hB2, hB3,
      LVec.add_ofBitVec, LVec.sub_ofBitVec, LVec.mul_ofBitVec, LVec.resizeU_ofBitVec,
      BitVec.setWidth_eq, ← BitVec.ofInt_add, ofInt_sub_eq, ← BitVec.ofInt_mul,
      setWidth_ofInt_le (by omega : AccW ≤ AccW + W),
      LVec.resizeU_one_l0, LVec.resizeU_one_l1, List.cons_append, List.nil_append,
      strP0, strP1, strP2, strP3, strP4, strP5, strP6]
  have hcongr : ∀ (dn' k' bz' p0' p1' p2' p3' p4' p5' p6' : LVec),
      nbaFold "done" q dn = dn' → nbaFold "k" q k = k' → nbaFold "busy" q bz = bz' →
      nbaFold "p0" q p0 = p0' → nbaFold "p1" q p1 = p1' → nbaFold "p2" q p2 = p2' →
      nbaFold "p3" q p3 = p3' → nbaFold "p4" q p4 = p4' → nbaFold "p5" q p5 = p5' →
      nbaFold "p6" q p6 = p6' →
      mmS.St ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "k" q k) (nbaFold "busy" q bz)
        (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
        (nbaFold "p0" q p0) (nbaFold "p1" q p1) (nbaFold "p2" q p2) (nbaFold "p3" q p3)
        (nbaFold "p4" q p4) (nbaFold "p5" q p5) (nbaFold "p6" q p6) =
      mmS.St ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn' (nbaFold "C" q c) k' bz' (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
        p0' p1' p2' p3' p4' p5' p6' := by
    rintro _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl; rfl
  apply hcongr <;> (rw [hq]; simp [nbaFold, LVec.insertAt_zero_of_width_eq,
    h1, h3, h4, h7, h8, h9, h10, h11, h12, h13])

theorem mmS_next_step {W AccW : Nat} (hA : 1 ≤ AccW)
    (Av Bv : BitVec (2 * 2 * W)) {t : Nat} (ht : t < 2)
    (ck a b c am bm : LVec) (hcw : c.width = 4 * AccW) (ham : am.width = 4 * W) (hbm : bm.width = 4 * W) :
    ∃ am' bm',
      mmS.next 2 W AccW ck (knownBit false) (knownBit false) a b
        (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm
        (LVec.ofBitVec (strP0 W AccW Av Bv)) (LVec.ofBitVec (strP1 W AccW Av Bv))
        (LVec.ofBitVec (strP2 W AccW Av Bv)) (LVec.ofBitVec (strP3 W AccW Av Bv))
        (LVec.ofBitVec (strP4 W AccW Av Bv)) (LVec.ofBitVec (strP5 W AccW Av Bv))
        (LVec.ofBitVec (strP6 W AccW Av Bv)) =
      mmS.St ck (knownBit false) (knownBit false) a b
        (knownBit (decide (t + 1 = 2))) (LVec.ofBitVec (Tasks.Matmul.product 2 W AccW Av Bv))
        (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ 2))) am' bm'
        (LVec.ofBitVec (strP0 W AccW Av Bv)) (LVec.ofBitVec (strP1 W AccW Av Bv))
        (LVec.ofBitVec (strP2 W AccW Av Bv)) (LVec.ofBitVec (strP3 W AccW Av Bv))
        (LVec.ofBitVec (strP4 W AccW Av Bv)) (LVec.ofBitVec (strP5 W AccW Av Bv))
        (LVec.ofBitVec (strP6 W AccW Av Bv)) ∧
      am'.width = 4 * W ∧ bm'.width = 4 * W := by
  have hrecomb := strassen_recombine hA Av Bv
  let q := allQS 2 W AccW ck (knownBit false) (knownBit false) a b
    (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm
    (LVec.ofBitVec (strP0 W AccW Av Bv)) (LVec.ofBitVec (strP1 W AccW Av Bv))
    (LVec.ofBitVec (strP2 W AccW Av Bv)) (LVec.ofBitVec (strP3 W AccW Av Bv))
    (LVec.ofBitVec (strP4 W AccW Av Bv)) (LVec.ofBitVec (strP5 W AccW Av Bv))
    (LVec.ofBitVec (strP6 W AccW Av Bv))
  refine ⟨nbaFold "A_mem" q am, nbaFold "B_mem" q bm, ?_,
    by rw [nbaFold_width, ham], by rw [nbaFold_width, hbm]⟩
  rw [mmS_next_eq]
  change mmS.St _ _ _ _ _ (nbaFold "done" q _) (nbaFold "C" q c) (nbaFold "k" q _)
    (nbaFold "busy" q _) (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
    (nbaFold "p0" q _) (nbaFold "p1" q _) (nbaFold "p2" q _) (nbaFold "p3" q _)
    (nbaFold "p4" q _) (nbaFold "p5" q _) (nbaFold "p6" q _) = _
  have hq : q =
    (if t + 1 = 2 then
      [("A_mem", 0, (am.shr (LVec.ofBitVec (BitVec.ofNat 32 W))).resizeU am.width),
        ("B_mem", 0, (bm.shr (LVec.ofBitVec (BitVec.ofNat 32 2 * BitVec.ofNat 32 W))).resizeU bm.width),
        ("k", 0, LVec.ofBitVec (BitVec.ofNat 32 (t + 1))),
        ("busy", 0, knownBit false), ("done", 0, knownBit true),
        ("C", 0, LVec.ofBitVec (Tasks.Matmul.product 2 W AccW Av Bv))]
    else
      [("A_mem", 0, (am.shr (LVec.ofBitVec (BitVec.ofNat 32 W))).resizeU am.width),
        ("B_mem", 0, (bm.shr (LVec.ofBitVec (BitVec.ofNat 32 2 * BitVec.ofNat 32 W))).resizeU bm.width),
        ("k", 0, LVec.ofBitVec (BitVec.ofNat 32 (t + 1))),
        ("C", 0, LVec.ofBitVec (Tasks.Matmul.product 2 W AccW Av Bv))]) := by
    simp only [q, allQS, mmS.p0Q, mmS.genQ, mmS.gen_1Q, lor_cond_knownBit]
    simp only [Bool.or_self, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, hrecomb, hcw]
    simp only [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat,
      LVec.sub_ofBitVec, LVec.mul_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
      Lib.ofNat_eq_ofNat_sub_one_iff ht (by omega : 2 ≤ 2 ^ 32),
      LVec.add_ofBitVec, BitVec.ofNat_add_ofNat, LVec.width_ofBitVec,
      LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    by_cases hf : t + 1 = 2 <;> simp [hf]
  have hcongr : ∀ (dn' c' k' bz' p0' p1' p2' p3' p4' p5' p6' : LVec),
      nbaFold "done" q (knownBit false) = dn' → nbaFold "C" q c = c' →
      nbaFold "k" q (LVec.ofBitVec (BitVec.ofNat 32 t)) = k' → nbaFold "busy" q (knownBit true) = bz' →
      nbaFold "p0" q (LVec.ofBitVec (strP0 W AccW Av Bv)) = p0' →
      nbaFold "p1" q (LVec.ofBitVec (strP1 W AccW Av Bv)) = p1' →
      nbaFold "p2" q (LVec.ofBitVec (strP2 W AccW Av Bv)) = p2' →
      nbaFold "p3" q (LVec.ofBitVec (strP3 W AccW Av Bv)) = p3' →
      nbaFold "p4" q (LVec.ofBitVec (strP4 W AccW Av Bv)) = p4' →
      nbaFold "p5" q (LVec.ofBitVec (strP5 W AccW Av Bv)) = p5' →
      nbaFold "p6" q (LVec.ofBitVec (strP6 W AccW Av Bv)) = p6' →
      mmS.St ck (knownBit false) (knownBit false) a b
        (nbaFold "done" q (knownBit false)) (nbaFold "C" q c)
        (nbaFold "k" q (LVec.ofBitVec (BitVec.ofNat 32 t))) (nbaFold "busy" q (knownBit true))
        (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
        (nbaFold "p0" q (LVec.ofBitVec (strP0 W AccW Av Bv)))
        (nbaFold "p1" q (LVec.ofBitVec (strP1 W AccW Av Bv)))
        (nbaFold "p2" q (LVec.ofBitVec (strP2 W AccW Av Bv)))
        (nbaFold "p3" q (LVec.ofBitVec (strP3 W AccW Av Bv)))
        (nbaFold "p4" q (LVec.ofBitVec (strP4 W AccW Av Bv)))
        (nbaFold "p5" q (LVec.ofBitVec (strP5 W AccW Av Bv)))
        (nbaFold "p6" q (LVec.ofBitVec (strP6 W AccW Av Bv))) =
      mmS.St ck (knownBit false) (knownBit false) a b
        dn' c' k' bz' (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
        p0' p1' p2' p3' p4' p5' p6' := by
    rintro _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl; rfl
  apply hcongr <;> (rw [hq]; by_cases hf : t + 1 = 2 <;>
    simp [hf, nbaFold, LVec.insertAt_zero_of_width_eq, hcw])

def StpS (W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
    prev = mmS.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdS W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    st = mmS.next 2 W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz am bm p0 p1 p2 p3 p4 p5 p6

def modelS (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.PhaseModel (2, W, AccW) 2 (design.sem 2 W AccW) where
  Shape := IS W AccW
  Step := StpS W AccW
  init := mmS_init W AccW hW hA hW32 hA32
  cycle := by
    rintro σ F e prev kk st kk' ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩ hc
    have hnext := mmS.cycle 2 W AccW rfl hW hA hW32 hA32 σ e
      ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 kk 30 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩
    exact mmS_next_I 2 W AccW _ _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
  Ready st := ∃ ck r s a b c k am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmS.St ck r s a b (knownBit false) c k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdS W AccW (knownBit false) c k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6
  Busy x m st := ∃ t, t + m + 1 = 2 ∧ ∃ ck r s a b c am bm,
    st = mmS.St ck r s a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm
      (LVec.ofBitVec (strP0 W AccW x.1 x.2.1)) (LVec.ofBitVec (strP1 W AccW x.1 x.2.1))
      (LVec.ofBitVec (strP2 W AccW x.1 x.2.1)) (LVec.ofBitVec (strP3 W AccW x.1 x.2.1))
      (LVec.ofBitVec (strP4 W AccW x.1 x.2.1)) (LVec.ofBitVec (strP5 W AccW x.1 x.2.1))
      (LVec.ofBitVec (strP6 W AccW x.1 x.2.1)) ∧
    c.width = 4 * AccW ∧ am.width = 4 * W ∧ bm.width = 4 * W
  Fin x st := ∃ ck r s a b k am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmS.St ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product 2 W AccW x.1 x.2.1))
      k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdS W AccW (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product 2 W AccW x.1 x.2.1))
      k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmS.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, c, am, bm, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmS.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmS.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', am', bm', p0', p1', p2', p3', p4', p5', p6', heq, hw'⟩ :=
      mmS_next_reset _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
    exact ⟨_, _, _, _, _, c', k', am', bm', p0', p1', p2', p3', p4', p5', p6', heq, hw'⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩
      - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    obtain ⟨c', am', bm', heq, hcw', ham', hbm'⟩ :=
      mmS_next_start hW hA (appIn e "clk" ck) x.1 x.2.1 dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
    exact .inr ⟨1, by omega, 0, rfl, _, _, _, _, _, c', am', bm', heq, hcw', ham', hbm'⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', c', am', bm', hb, hcw, ham, hbm⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmS_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨am', bm', hstep, ham', hbm'⟩ :=
      mmS_next_step hA x.1 x.2.1 (t := t) (by omega)
        (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) c am bm hcw ham hbm
    by_cases hf : t + 1 = 2
    · left
      simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false] at hstep
      exact ⟨_, _, _, _, _, _, am', bm', _, _, _, _, _, _, _, hstep,
        by simp, by simp, by simp, by simp, ham', hbm',
        by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · right
      simp only [hf, decide_false, ne_eq, not_false_eq_true, decide_true] at hstep
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, am', bm', hstep,
        by simp, ham', hbm'⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', am', bm', p0', p1', p2', p3', p4', p5', p6', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmS_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmS_next_idle]
    exact ⟨_, _, _, _, _, c, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', am', bm', p0', p1', p2', p3', p4', p5', p6', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmS_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmS_next_idle]
    exact ⟨_, _, _, _, _, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩

theorem mmS_proc_mem {W AccW : Nat} {p : Process2} (hp : p ∈ (mmS.D 2 W AccW).processes.toList) :
    p = mmS.p0 2 W AccW ∨ p = mmS.gen 2 W AccW ∨ p = mmS.gen_1 2 W AccW := by
  simpa [mmS.D, mmS.procs] using hp

theorem mmS_interface (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (2, W, AccW) (design.sem 2 W AccW) := by
  rw [mmS.sem_eq 2 W AccW rfl hW hA hW32 hA32]
  have h4W : (4 * (W : Int) - 1).natAbs + 1 = 4 * W := by omega
  have h4A : (4 * (AccW : Int) - 1).natAbs + 1 = 4 * AccW := by omega
  refine ⟨by simp [Tasks.Matmul.task, mmS.D, mmS.decls, inputPorts, h4W],
    by simp [Tasks.Matmul.task, mmS.D, mmS.decls, outputPorts, h4A], ?_⟩
  show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
    "A_mem", "B_mem", "p0", "p1", "p2", "p3", "p4", "p5", "p6"] : List String).Nodup
  decide

theorem mmS_disciplined (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem 2 W AccW) := by
  rw [mmS.sem_eq 2 W AccW rfl hW hA hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmS.D, mmS.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mmS_proc_mem hp with rfl | rfl | rfl
  · simp [Tasks.Matmul.task, mmS.p0, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmS.gen, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, mmS.gen_1, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, lhsNames, exprNames, exprListNames]

theorem mmS_moore (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem 2 W AccW) [] := by
  rw [mmS.sem_eq 2 W AccW rfl hW hA hW32 hA32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mmS.profile 2 W AccW rfl hW hA hW32 hA32)))
    (by simp [mmS.D, mmS.decls, Design2.outputNames, Design2.inputNames])

theorem mmS_powerUp (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem 2 W AccW) st) : IS W AccW st := by
  have h4W : (4 * (W : Int) - 1).natAbs + 1 = 4 * W := by omega
  have h4A : (4 * (AccW : Int) - 1).natAbs + 1 = 4 * AccW := by omega
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl,
    -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    mmS.powerUp 2 W AccW rfl hW hA hW32 hA32 st h
  rw [h4A] at h7; rw [h4W] at h10 h11
  exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl,
    h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

theorem mmS_noq (W AccW : Nat) :
    (mmS.D 2 W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mmS_proc_mem hp with rfl | rfl | rfl <;>
    simp [mmS.p0, mmS.gen, mmS.gen_1, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

theorem mmS_terminatesPU (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem 2 W AccW) := by
  refine TerminatesPU.of_invariant (IS W AccW)
    (mmS_powerUp W AccW hW hA hW32 hA32) (fun σ => ⟨30, ?_⟩)
    (by rw [mmS.sem_eq 2 W AccW rfl hW hA hW32 hA32]; exact mmS_noq W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩
  exact ⟨_, _, mmS.cycle 2 W AccW rfl hW hA hW32 hA32 σ e
      ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 kk 30 (Nat.le_refl _),
    mmS_next_I 2 W AccW _ _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw⟩

theorem mmS_xsafe (W AccW : Nat) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem 2 W AccW) := by
  rw [mmS.sem_eq 2 W AccW rfl hW hA hW32 hA32]
  have h4W : (4 * (W : Int) - 1).natAbs + 1 = 4 * W := by omega
  have h4A : (4 * (AccW : Int) - 1).natAbs + 1 = 4 * AccW := by omega
  have h2W : (2 * (W : Int)).toNat = 2 * W := by omega
  have h3W : (3 * (W : Int)).toNat = 3 * W := by omega
  have h4Wn : (4 * (W : Int)).toNat = 4 * W := by omega
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mmS_proc_mem hp with rfl | rfl | rfl
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmS.p0, mmS.D, mmS.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hW0 : W ≤ 4 * W := by omega
    have hW1 : W + W ≤ 4 * W := by omega
    have hW2 : 2 * W + W ≤ 4 * W := by omega
    have hW3 : 3 * W + W ≤ 4 * W := by omega
    have hB0 : W - 1 + 1 ≤ 4 * W := by omega
    have hB1 : 2 * W - 1 + 1 ≤ 4 * W := by omega
    have hB2 : 3 * W - 1 + 1 ≤ 4 * W := by omega
    have hB3 : 4 * W - 1 + 1 ≤ 4 * W := by omega
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmS.gen, mmS.D, mmS.decls, h4W, h2W, h3W, h4Wn,
      hW0, hW1, hW2, hW3, hB0, hB1, hB2, hB3]
  · simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmS.gen_1, mmS.D, mmS.decls, h4A, LVec.allKnown_ofBitVec]

end Strassen

/-! ## 3. Branch 2: N ≠ 2 (Parametric shift-register fallback) -/

sv_mirror mmF := design (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem mmF_disj (N W AccW : Nat) :
    (mmF.procs N W AccW).Pairwise ProcDisj := by
  have sepA : ∀ a b : Nat, a < b → a * AccW + AccW ≤ b * AccW := fun _ _ h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h); rwa [Nat.succ_mul] at this
  simp only [mmF.procs, List.pairwise_cons]
  refine ⟨fun q hq => ?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨i, -, j, -, rfl⟩ := hq
    exact ProcDisj.of_all (by simp [mmF.p0, mmF.g_col, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · exact pairwise_rowMajor fun i j i' j' _ _ _ _ h => by
      have hA := sepA (i * N + j) (i' * N + j') h
      exact ProcDisj.of_all (by simp [mmF.g_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Lhs2.drvWins, DrvWin.overlaps] <;> omega)

sv_cycle mmF using mmF_disj N W AccW

section Fallback

def colQ (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmF.g_colQ N W AccW i j ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6

theorem colQ_only_C (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) :
    ∀ u ∈ colQ N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6, u.1 = "C" := by
  intro u hu
  simp only [colQ, List.mem_flatMap] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  unfold mmF.g_colQ at hu
  split at hu
  · simp at hu; rw [hu]
  · split at hu
    · simp at hu; rw [hu]
    · simp at hu

theorem mmF_next_eq (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmF.next N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      mmF.St ck r s a b
        (nbaFold "done" (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) dn)
        (nbaFold "C" (colQ N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) c)
        (nbaFold "k" (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) k)
        (nbaFold "busy" (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) bz)
        (nbaFold "A_mem" (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) am)
        (nbaFold "B_mem" (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) bm)
        p0 p1 p2 p3 p4 p5 p6 := by
  have h1 : ∀ (q : NbaQueue2) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec),
      (∀ u ∈ q, u.1 ∈ ["done", "C", "k", "busy", "A_mem", "B_mem"]) →
      commitNba2 (mmF.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) q =
        mmF.St ck r s a b
          (nbaFold "done" q dn) (nbaFold "C" q c) (nbaFold "k" q k)
          (nbaFold "busy" q bz) (nbaFold "A_mem" q am) (nbaFold "B_mem" q bm)
          p0 p1 p2 p3 p4 p5 p6 := by
    intro q; induction q with
    | nil => intros; rfl
    | cons u q ih =>
      intro ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hmem
      obtain ⟨n, lo, v⟩ := u
      have hn : n ∈ ["done", "C", "k", "busy", "A_mem", "B_mem"] := hmem _ List.mem_cons_self
      have hq := fun u hu => hmem u (List.mem_cons_of_mem _ hu)
      rw [commitNba2_cons]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [mmF.St] at ih
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [nbaStep, mmF.St, SvState.lookup, SvState.set, nbaFold_cons,
          ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq]
  have hp_mem : ∀ u ∈ mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
      u.1 ∈ ["done", "k", "busy", "A_mem", "B_mem"] := by
    intro u hu; unfold mmF.p0Q at hu
    split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
      · split at hu
        · split at hu
          · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
          · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
        · simp at hu
  have hc_mem := colQ_only_C N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
  have hall : ∀ u ∈ mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ++
      colQ N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
      u.1 ∈ ["done", "C", "k", "busy", "A_mem", "B_mem"] := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · have := hp_mem u h; simp at this ⊢
      rcases this with h | h | h | h | h <;> simp [h]
    · simp [hc_mem u h]
  show commitNba2 (mmF.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6)
    (mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ++
      colQ N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) = _
  rw [h1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hall]
  have hfold_app : ∀ s q1 q2 v, nbaFold s (q1 ++ q2) v = nbaFold s q2 (nbaFold s q1 v) := by
    intro s q1 q2 v; simp [nbaFold, List.foldl_append]
  have hp_noC : ∀ u ∈ mmF.p0Q N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6, u.1 ≠ "C" := by
    intro u hu; have := hp_mem u hu; simp at this; rcases this with h | h | h | h | h <;> simp [h]
  simp only [hfold_app]
  rw [nbaFold_disj "done" _ _ (fun u hu => by rw [hc_mem u hu]; decide),
    nbaFold_disj "k" _ _ (fun u hu => by rw [hc_mem u hu]; decide),
    nbaFold_disj "busy" _ _ (fun u hu => by rw [hc_mem u hu]; decide),
    nbaFold_disj "A_mem" _ _ (fun u hu => by rw [hc_mem u hu]; decide),
    nbaFold_disj "B_mem" _ _ (fun u hu => by rw [hc_mem u hu]; decide),
    nbaFold_disj "C" _ _ hp_noC]

def WdF (N W AccW : Nat) (dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  am.width = N * N * W ∧ bm.width = N * N * W ∧
  p0.width = AccW ∧ p1.width = AccW ∧ p2.width = AccW ∧ p3.width = AccW ∧
  p4.width = AccW ∧ p5.width = AccW ∧ p6.width = AccW

def IFa (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmF.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdF N W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6

theorem mmF_init (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    IFa N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mmF.init N W AccW hN hNe hW hA hN32 hW32 hA32]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
    by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem mmF_next_I (N W AccW : Nat) (ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdF N W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    IFa N W AccW (mmF.next N W AccW ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) := by
  rw [mmF_next_eq]
  refine ⟨ck, r, s, a, b, _, _, _, _, _, _, p0, p1, p2, p3, p4, p5, p6, rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  exact ⟨by rw [nbaFold_width, h1], by rw [nbaFold_width, h2], by rw [nbaFold_width, h3],
    by rw [nbaFold_width, h4], by rw [nbaFold_width, h5], by rw [nbaFold_width, h6],
    h7, h8, h9, h10, h11, h12, h13⟩

theorem mmF_St_inj {ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
    ck' r' s' a' b' dn' c' k' bz' am' bm' p0' p1' p2' p3' p4' p5' p6' : LVec}
    (h : mmF.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      mmF.St ck' r' s' a' b' dn' c' k' bz' am' bm' p0' p1' p2' p3' p4' p5' p6') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ am = am' ∧ bm = bm' ∧
    p0 = p0' ∧ p1 = p1' ∧ p2 = p2' ∧ p3 = p3' ∧ p4 = p4' ∧ p5 = p5' ∧ p6 = p6' := by
  simp only [mmF.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem mmF_next_reset (N W AccW : Nat)
    (ck s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdF N W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    ∃ c' k' am' bm',
      mmF.next N W AccW ck (knownBit true) s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
        mmF.St ck (knownBit true) s a b (knownBit false) c' k' (knownBit false)
          am' bm' p0 p1 p2 p3 p4 p5 p6 ∧
      WdF N W AccW (knownBit false) c' k' (knownBit false) am' bm' p0 p1 p2 p3 p4 p5 p6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hw
  let qp := mmF.p0Q N W AccW ck (knownBit true) s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
  let qc := colQ N W AccW ck (knownBit true) s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6
  refine ⟨nbaFold "C" qc c, nbaFold "k" qp k, nbaFold "A_mem" qp am, nbaFold "B_mem" qp bm, ?_, ?_⟩
  · rw [mmF_next_eq]
    have hdn : nbaFold "done" qp dn = knownBit false := by
      simp [qp, mmF.p0Q, nbaFold, h1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    have hbz : nbaFold "busy" qp bz = knownBit false := by
      simp [qp, mmF.p0Q, nbaFold, h4, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    rw [hdn, hbz]
  · exact ⟨by simp, by rw [nbaFold_width, h2], by rw [nbaFold_width, h3], by simp,
      by rw [nbaFold_width, h5], by rw [nbaFold_width, h6], h7, h8, h9, h10, h11, h12, h13⟩

theorem mmF_next_idle (N W AccW : Nat) (ck a b dn c k am bm p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmF.next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      am bm p0 p1 p2 p3 p4 p5 p6 =
    mmF.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      am bm p0 p1 p2 p3 p4 p5 p6 := by
  have hcol : colQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      am bm p0 p1 p2 p3 p4 p5 p6 = [] := by
    unfold colQ
    have : ∀ i j, mmF.g_colQ N W AccW i j ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
        am bm p0 p1 p2 p3 p4 p5 p6 = [] := by
      intro i j; simp [mmF.g_colQ]
    simp [this]
  rw [mmF_next_eq, hcol]
  simp [mmF.p0Q, nbaFold]

theorem mmF_next_start {N W AccW : Nat} (ck : LVec) (Av Bv : BitVec (N * N * W))
    (dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 : LVec)
    (hw : WdF N W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6) :
    mmF.next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
    mmF.St ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      (knownBit false) (accC N W AccW Av Bv 0) (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true)
      (LVec.ofBitVec (Av >>> (0 * W))) (LVec.ofBitVec (Bv >>> (0 * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hw
  have hcol : colQ N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 0 (r / N) (r % N)))) := by
    refine flatMap_range_rowMajor _ fun i j _ _ => ?_
    simp [mmF.g_colQ, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, psum]
  rw [mmF_next_eq, hcol, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h2]
  simp only [mmF.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
    nbaFold, List.foldl_cons, List.foldl_nil, h1, h3, h4, h5, h6,
    LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    LVec.insertAt_zero_of_width_eq, LVec.width_ofBitVec, Nat.zero_mul, BitVec.ushiftRight_zero]
  simp [accC, LVec.insertAt_zero_of_width_eq, h1, h3, h5, h6]

theorem mmF_pe_step {N W AccW : Nat} (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {t i j : Nat} (hi : i < N) (hj : j < N) (ck a b dn k p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmF.g_colQ N W AccW i j ck (knownBit false) (knownBit false) a b dn (accC N W AccW Av Bv t) k
      (knownBit true) (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 =
    [("C", (i * N + j) * AccW,
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := rowMajor_div hj
  have hm : (i * N + j) % N = j := Nat.mul_add_mod_of_lt hj
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have ha : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
  have hb : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj; simpa using this
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  simp (disch := omega) only [mmF.g_colQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, accC,
    LVec.extract_ofBitVec, extractLsb'_packBV, hd, hm, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.add_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend, Lib.extractLsb'_ushiftRight, e1, e2, psum_succ, BitVec.ofInt_add,
    Tasks.Matmul.entry]

theorem mmF_next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW32 : N * W < 2 ^ 32)
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b p0 p1 p2 p3 p4 p5 p6 : LVec) :
    mmF.next N W AccW ck (knownBit false) (knownBit false) a b
      (knownBit false) (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 =
    mmF.St ck (knownBit false) (knownBit false) a b
      (knownBit (decide (t + 1 = N))) (accC N W AccW Av Bv (t + 1))
      (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ N)))
      (LVec.ofBitVec (Av >>> ((t + 1) * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 := by
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW32
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW32
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW',
      Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW32]
  have hcol : colQ N W AccW ck (knownBit false) (knownBit false) a b
      (knownBit false) (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) (r / N) (r % N)))) :=
    flatMap_range_rowMajor _ fun i j hi hj => mmF_pe_step hW Av Bv hi hj ..
  rw [mmF_next_eq, hcol, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (by simp [accC])]
  simp only [mmF.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
    LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat,
    LVec.mul_ofBitVec, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
    Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN'),
    LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.add_ofBitVec,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW,
    ← BitVec.shiftRight_add, BitVec.ofNat_add_ofNat, Nat.succ_mul]
  by_cases hf : t + 1 = N <;>
    simp [hf, nbaFold, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1, accC]

def StpF (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6,
    prev = mmF.St ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdF N W AccW dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 ∧
    st = mmF.next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz am bm p0 p1 p2 p3 p4 p5 p6

def modelF (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hNW32 : N * W < 2 ^ 32) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := IFa N W AccW
  Step := StpF N W AccW
  init := mmF_init N W AccW hN hNe hW hA hN32 hW32 hA32
  cycle := by
    rintro σ F e prev kk st kk' ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩ hc
    have hnext := mmF.cycle N W AccW hN hNe hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 kk 30 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩
    exact mmF_next_I N W AccW _ _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
  Ready st := ∃ ck r s a b c k am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmF.St ck r s a b (knownBit false) c k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdF N W AccW (knownBit false) c k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6
  Busy x m st := ∃ t, t + m + 1 = N ∧ ∃ ck r s a b p0 p1 p2 p3 p4 p5 p6,
    st = mmF.St ck r s a b (knownBit false) (accC N W AccW x.1 x.2.1 t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (x.1 >>> (t * W))) (LVec.ofBitVec (x.2.1 >>> (t * (N * W))))
      p0 p1 p2 p3 p4 p5 p6 ∧
    p0.width = AccW ∧ p1.width = AccW ∧ p2.width = AccW ∧ p3.width = AccW ∧
    p4.width = AccW ∧ p5.width = AccW ∧ p6.width = AccW
  Fin x st := ∃ ck r s a b k am bm p0 p1 p2 p3 p4 p5 p6,
    st = mmF.St ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6 ∧
    WdF N W AccW (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      k (knownBit false) am bm p0 p1 p2 p3 p4 p5 p6
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmF.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, p0, p1, p2, p3, p4, p5, p6, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmF.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmF.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', am', bm', heq, hw'⟩ :=
      mmF_next_reset N W AccW _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
    exact ⟨_, _, _, _, _, c', k', am', bm', p0, p1, p2, p3, p4, p5, p6, heq, hw'⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, -, hw, rfl⟩
      - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    have hst := mmF_next_start (appIn e "clk" ck) x.1 x.2.1 dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw
    exact .inr ⟨N - 1, by omega, 0, by omega, _, _, _, _, _, p0, p1, p2, p3, p4, p5, p6, hst,
      hw.2.2.2.2.2.2⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', p0', p1', p2', p3', p4', p5', p6', hb, h7, h8, h9, h10, h11, h12, h13⟩
      hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmF_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    have hstep := mmF_next_step (AccW := AccW) hN hW hNW32 x.1 x.2.1 (t := t) (by omega)
      (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) p0 p1 p2 p3 p4 p5 p6
    by_cases hf : t + 1 = N
    · left
      simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false, accC_N] at hstep
      exact ⟨_, _, _, _, _, _, _, _, p0, p1, p2, p3, p4, p5, p6, hstep,
        by simp, by simp, by simp, by simp, by simp, by simp, h7, h8, h9, h10, h11, h12, h13⟩
    · right
      simp only [hf, decide_false, ne_eq, not_false_eq_true, decide_true] at hstep
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, p0, p1, p2, p3, p4, p5, p6, hstep,
        h7, h8, h9, h10, h11, h12, h13⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', am', bm', p0', p1', p2', p3', p4', p5', p6', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmF_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmF_next_idle]
    exact ⟨_, _, _, _, _, c, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', am', bm', p0', p1', p2', p3', p4', p5', p6', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := mmF_St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, mmF_next_idle]
    exact ⟨_, _, _, _, _, k, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩

theorem mmF_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmF.D N W AccW).processes.toList) :
    p = mmF.p0 N W AccW ∨ ∃ i j, i < N ∧ j < N ∧ p = mmF.g_col N W AccW i j := by
  simp only [mmF.D, List.toList_toArray, mmF.procs, List.mem_cons, List.mem_flatMap,
    List.mem_map, List.mem_range] at hp
  rcases hp with rfl | ⟨i, hi, j, hj, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨i, j, hi, hj, rfl⟩

theorem mmF_interface (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mmF.sem_eq N W AccW hN hNe hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "A_mem", "B_mem", "p0", "p1", "p2", "p3", "p4", "p5", "p6"] : List String).Nodup
    decide⟩

theorem mmF_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mmF.sem_eq N W AccW hN hNe hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmF.D, mmF.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mmF_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmF.p0, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmF.g_col, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, lhsNames, exprNames, exprListNames]

theorem mmF_moore (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mmF.sem_eq N W AccW hN hNe hW hA hN32 hW32 hA32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mmF.profile N W AccW hN hNe hW hA hN32 hW32 hA32)))
    (by simp [mmF.D, mmF.decls, Design2.outputNames, Design2.inputNames])

theorem mmF_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : IFa N W AccW st := by
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl,
    -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ :=
    mmF.powerUp N W AccW hN hNe hW hA hN32 hW32 hA32 st h
  exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl,
    h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

theorem mmF_noq (N W AccW : Nat) :
    (mmF.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mmF_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩ <;>
    simp [mmF.p0, mmF.g_col, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

theorem mmF_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (IFa N W AccW)
    (mmF_powerUp N W AccW hN hNe hW hA hN32 hW32 hA32) (fun σ => ⟨30, ?_⟩)
    (by rw [mmF.sem_eq N W AccW hN hNe hW hA hN32 hW32 hA32]; exact mmF_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, p0, p1, p2, p3, p4, p5, p6, rfl, hw⟩
  exact ⟨_, _, mmF.cycle N W AccW hN hNe hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 kk 30 (Nat.le_refl _),
    mmF_next_I N W AccW _ _ _ _ _ dn c k bz am bm p0 p1 p2 p3 p4 p5 p6 hw⟩

theorem mmF_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hNe : N ≠ 2) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mmF.sem_eq N W AccW hN hNe hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mmF_proc_mem hp with rfl | ⟨i, j, hi, hj, rfl⟩
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmF.p0, mmF.D, mmF.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hA' : i * N * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
    have hB' : j * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
    have hA1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
    have hB1 : j * W + W - 1 + 1 ≤ N * N * W := by omega
    have hC' : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
    simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmF.g_col, mmF.D, mmF.decls, LVec.allKnown_ofBitVec, hA', hB', hA1, hB1, hC']

end Fallback

/-! ## 4. Main theorem -/

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hN32 : N < 2147483648 := by omega
  have hW32 : W < 2147483648 := by omega
  have hA32 : AccW < 2147483648 := by omega
  by_cases hN2 : N = 2
  · subst hN2
    exact Tasks.Matmul.task.satisfiedAtV2_of_phases
      (mmS_interface W AccW hW hA hW32 hA32)
      (mmS_disciplined W AccW hW hA hW32 hA32)
      (mmS_terminatesPU W AccW hW hA hW32 hA32) (show 1 ≤ 2 by omega)
      (modelS W AccW hW hA hW32 hA32)
      (mmS_powerUp W AccW hW hA hW32 hA32)
      (mmS_moore W AccW hW hA hW32 hA32)
      (mmS_xsafe W AccW hW hA hW32 hA32)
  · have hNW32 : N * W < 2 ^ 32 := by
      have : N * W ≤ 256 * 127 := Nat.mul_le_mul hN256 hW127
      omega
    exact Tasks.Matmul.task.satisfiedAtV2_of_phases
      (mmF_interface N W AccW hN hN2 hW hA hN32 hW32 hA32)
      (mmF_disciplined N W AccW hN hN2 hW hA hN32 hW32 hA32)
      (mmF_terminatesPU N W AccW hN hN2 hW hA hN32 hW32 hA32) hN
      (modelF N W AccW hN hN2 hW hA hN32 hW32 hA32 hNW32)
      (mmF_powerUp N W AccW hN hN2 hW hA hN32 hW32 hA32)
      (mmF_moore N W AccW hN hN2 hW hA hN32 hW32 hA32)
      (mmF_xsafe N W AccW hN hN2 hW hA hN32 hW32 hA32)

end Submission
