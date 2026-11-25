-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Mirror, disjointness, and generated clock cycle -/

sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem mmG_disj (N W AccW : Nat) : (mmG.procs N W AccW).Pairwise SvGolf.Cycle.WinDisj := by
  have sepW : ∀ q q', q < q' → q * W + W ≤ q' * W := fun q q' h => by
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  have sepNW : ∀ q q', q < q' → q * (N * W) + N * W ≤ q' * (N * W) := fun q q' h => by
    have := Nat.mul_le_mul_right (N * W) (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  have sepA : ∀ q q', q < q' → q * AccW + AccW ≤ q' * AccW := fun q q' h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  have cell : ∀ i j i' j', i * N + j < i' * N + j' →
      ∀ p ∈ (List.range N).map (mmG.g_col_word N W AccW i j) ++
          ([mmG.g_mesh_col N W AccW i j] ++ [mmG.g_mesh_col_1 N W AccW i j]),
      ∀ q ∈ (List.range N).map (mmG.g_col_word N W AccW i' j') ++
          ([mmG.g_mesh_col N W AccW i' j'] ++ [mmG.g_mesh_col_1 N W AccW i' j']),
      SvGolf.Cycle.WinDisj p q := by
    intro i j i' j' h p hp q hq
    have hA := sepA (i * N + j) (i' * N + j') h
    have hNW : (i * N + j) * N * W + N * W ≤ (i' * N + j') * N * W := by
      simpa [Nat.mul_assoc] using sepNW (i * N + j) (i' * N + j') h
    simp only [List.mem_append, List.mem_map, List.mem_range, List.singleton_append,
      List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with ⟨t, ht, rfl⟩ | rfl | rfl <;> rcases hq with ⟨t', ht', rfl⟩ | rfl | rfl
    · have hW : (i * N + j) * N * W + t * W + W ≤ (i' * N + j') * N * W + t' * W := by
        simpa [Nat.add_mul] using sepW ((i * N + j) * N + t) ((i' * N + j') * N + t') (rowMajor_lt ht h)
      exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col_1, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col_1, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  unfold mmG.procs
  refine List.Pairwise.cons (fun q hq => ?_)
    (List.Pairwise.cons (fun q hq => ?_)
      (List.Pairwise.cons (fun q hq => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)))
  · simp only [List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
      List.singleton_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | ⟨i, -, j, -, ⟨t, -, rfl⟩ | rfl | rfl⟩
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.p1,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.p2,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_cons, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
      List.singleton_append, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | ⟨i, -, j, -, ⟨t, -, rfl⟩ | rfl | rfl⟩
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p1, mmG.p2,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p1, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p1, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p1, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨i, -, j, -, ⟨t, -, rfl⟩ | rfl | rfl⟩ := hq
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p2, mmG.g_col_word,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p2, mmG.g_mesh_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p2, mmG.g_mesh_col_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
  · refine pairwise_flatMap_range (fun j _ => ?_) ?_
    · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
      · refine pairwise_map_range fun t t' htt' _ => ?_
        have hW := sepW t t' htt'
        exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word,
          Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
      · simp only [List.singleton_append]
        exact .cons (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq
          exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_mesh_col, mmG.g_mesh_col_1,
            Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, DrvWin.overlaps])) (.cons (fun _ h => by simp at h) .nil)
      · intro p hp q hq
        simp only [List.mem_map, List.mem_range, List.singleton_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp hq
        obtain ⟨t, -, rfl⟩ := hp
        rcases hq with rfl | rfl
        · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word, mmG.g_mesh_col,
            Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, DrvWin.overlaps])
        · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_col_word, mmG.g_mesh_col_1,
            Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
            Lhs2.drvWins, DrvWin.overlaps])
    · intro j j' hjj' _ p hp q hq
      exact cell i j i j' (by omega) p hp q hq
  · intro i i' hii' _ p hp q hq
    obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j', -, hq⟩ := List.mem_flatMap.mp hq
    exact cell i j i' j' (rowMajor_lt (List.mem_range.mp hj) hii') p hp q hq

sv_cycle mmG using mmG_disj N W AccW

/-! ## 2. Arithmetic and skew-bank packing -/

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

theorem accC_width (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) :
    (accC N W AccW A B t).width = N * N * AccW := by
  simp [accC]

def ttA (N W : Nat) (A : BitVec (N * N * W)) : BitVec (N * N * N * W) :=
  packBV W (N * N * N) fun q => A.extractLsb' ((q / N / N * N + q % N) * W) W

def ttB (N W : Nat) (B : BitVec (N * N * W)) : BitVec (N * N * N * W) :=
  packBV W (N * N * N) fun q => B.extractLsb' ((q % N * N + q / N % N) * W) W

theorem ttA_shift_extract {N W : Nat} (A : BitVec (N * N * W)) {i j t : Nat}
    (hi : i < N) (hj : j < N) (ht : t < N) :
    (ttA N W A >>> (t * W)).extractLsb' ((i * N + j) * N * W) W =
      A.extractLsb' ((i * N + t) * W) W := by
  have hq : (i * N + j) * N + t < N * N * N := by
    have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
    have := rowMajor_le (K := N) h1; omega
  have hidx : t * W + (i * N + j) * N * W = ((i * N + j) * N + t) * W := by
    rw [Nat.add_comm, ← Nat.add_mul]
  rw [Lib.extractLsb'_ushiftRight, hidx, ttA, extractLsb'_packBV _ hq,
    rowMajor_div ht, Nat.mul_add_mod_of_lt ht, rowMajor_div hj]

theorem ttB_shift_extract {N W : Nat} (B : BitVec (N * N * W)) {i j t : Nat}
    (hi : i < N) (hj : j < N) (ht : t < N) :
    (ttB N W B >>> (t * W)).extractLsb' ((i * N + j) * N * W) W =
      B.extractLsb' ((t * N + j) * W) W := by
  have hq : (i * N + j) * N + t < N * N * N := by
    have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
    have := rowMajor_le (K := N) h1; omega
  have hidx : t * W + (i * N + j) * N * W = ((i * N + j) * N + t) * W := by
    rw [Nat.add_comm, ← Nat.add_mul]
  rw [Lib.extractLsb'_ushiftRight, hidx, ttB, extractLsb'_packBV _ hq,
    rowMajor_div ht, Nat.mul_add_mod_of_lt ht, Nat.mul_add_mod_of_lt hj]

theorem shiftRight_shiftRight {w : Nat} (x : BitVec w) (a b : Nat) :
    (x >>> a) >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1; omega

theorem eq_packBV_self {W n : Nat} (bv : BitVec (n * W)) :
    bv = packBV W n (fun q => bv.extractLsb' (q * W) W) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h => by simp [h] at hi
  have hr : i / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hi
  have hm : i % W < W := Nat.mod_lt i hW
  have hd : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  rw [← hd, packBV, getLsbD_bvInsertEntries _ _ _ (Nat.le_refl _) _ _ hr hm,
    BitVec.getLsbD_extractLsb', decide_eq_true hm, Bool.true_and]

theorem insertEntries_rowA {N W : Nat} (hN : 1 ≤ N) (Av : BitVec (N * N * W)) (x : LVec)
    (hx : x.width = N * N * N * W) :
    LVec.insertEntries (N * W) (fun r => ((LVec.ofBitVec Av).extract (r / N * N * W) (N * W)).resizeU (N * W))
      (N * N) x = LVec.ofBitVec (ttA N W Av) := by
  refine LVec.eq_ofBitVec_packBV (by rw [LVec.width_insertEntries, hx]) fun q hq => ?_
  have hr : q / N < N * N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hi : q / N / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have ht : q % N < N := Nat.mod_lt _ (by omega)
  have hNW : q % N * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt ht); rwa [Nat.succ_mul] at this
  have hqsplit : q * W = q / N * (N * W) + q % N * W := by
    have hd : q / N * N + q % N = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q N
    calc q * W = (q / N * N + q % N) * W := by rw [hd]
      _ = q / N * (N * W) + q % N * W := by rw [Nat.add_mul, Nat.mul_assoc]
  have hrow : q / N / N * N * W + N * W ≤ N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (Nat.succ_le_of_lt hi)
    simpa [Nat.succ_mul, Nat.mul_assoc] using this
  have hxw : N * N * (N * W) ≤ x.width := by
    rw [hx]; exact Nat.le_of_eq (Nat.mul_assoc (N * N) N W).symm
  rw [hqsplit, ← LVec.extract_extract _ hNW,
    LVec.extract_insertEntries (fun _ => LVec.width_resizeU ..) x (N * N) hxw _ hr,
    LVec.extract_ofBitVec Av hrow, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    LVec.extract_ofBitVec _ hNW]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hb, Bool.true_and,
    decide_eq_true (by omega : q % N * W + b < N * W)]
  congr 1; rw [Nat.add_mul, Nat.add_assoc]

theorem insertEntries_copy_ofBitVec {N W : Nat} (hN : 1 ≤ N) (bv : BitVec (N * N * N * W)) (x : LVec)
    (hx : x.width = N * N * N * W) :
    LVec.insertEntries (N * W) (fun r => ((LVec.ofBitVec bv).extract (r * (N * W)) (N * W)).resizeU (N * W))
      (N * N) x = LVec.ofBitVec bv := by
  conv => rhs; rw [eq_packBV_self bv]
  refine LVec.eq_ofBitVec_packBV (by rw [LVec.width_insertEntries, hx]) fun q hq => ?_
  have hr : q / N < N * N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have ht : q % N < N := Nat.mod_lt _ (by omega)
  have hNW : q % N * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt ht); rwa [Nat.succ_mul] at this
  have hqsplit : q * W = q / N * (N * W) + q % N * W := by
    have hd : q / N * N + q % N = q := by rw [Nat.mul_comm]; exact Nat.div_add_mod q N
    calc q * W = (q / N * N + q % N) * W := by rw [hd]
      _ = q / N * (N * W) + q % N * W := by rw [Nat.add_mul, Nat.mul_assoc]
  have hrb : q / N * (N * W) + N * W ≤ N * N * N * W := by
    have := Nat.mul_le_mul_right (N * W) (Nat.succ_le_of_lt hr)
    simpa [Nat.succ_mul, Nat.mul_assoc] using this
  have hxw : N * N * (N * W) ≤ x.width := by
    rw [hx]; exact Nat.le_of_eq (Nat.mul_assoc (N * N) N W).symm
  rw [hqsplit, ← LVec.extract_extract _ hNW,
    LVec.extract_insertEntries (fun _ => LVec.width_resizeU ..) x (N * N) hxw _ hr,
    LVec.extract_ofBitVec bv hrb, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    LVec.extract_ofBitVec _ hNW]
  congr 1
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp only [BitVec.getLsbD_extractLsb', decide_eq_true hb, Bool.true_and,
    decide_eq_true (by omega : q % N * W + b < N * W)]
  congr 1; omega

/-! ## 3. Helpers on `nbaFold`, `comb`, and `edgeQ` -/

@[simp] theorem nbaFold_width (n : String) : ∀ (q : NbaQueue2) (x : LVec),
    (nbaFold n q x).width = x.width
  | [], _ => rfl
  | u :: q, x => by
    rw [nbaFold_cons, nbaFold_width n q]
    split <;> simp

theorem nbaFold_append (n : String) (q₁ q₂ : NbaQueue2) (x : LVec) :
    nbaFold n (q₁ ++ q₂) x = nbaFold n q₂ (nbaFold n q₁ x) := by
  simp [nbaFold, List.foldl_append]

theorem nbaFold_flatMap_drop_right (n : String) {α : Type} (l : List α) (f g : α → NbaQueue2)
    (hg : ∀ a, ∀ u ∈ g a, u.1 ≠ n) (x : LVec) :
    nbaFold n (l.flatMap fun a => f a ++ g a) x = nbaFold n (l.flatMap f) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, nbaFold_append, nbaFold_of_forall_ne (hg a)]
    exact ih _

theorem nbaFold_flatMap_drop_left (n : String) {α : Type} (l : List α) (f g : α → NbaQueue2)
    (hf : ∀ a, ∀ u ∈ f a, u.1 ≠ n) (x : LVec) :
    nbaFold n (l.flatMap fun a => f a ++ g a) x = nbaFold n (l.flatMap g) x := by
  induction l generalizing x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, nbaFold_append, nbaFold_of_forall_ne (hf a)]
    exact ih _

theorem nbaFold_flatMap₂_drop_right (n : String) {α β : Type} (l₁ : List α) (l₂ : List β)
    (f g : α → β → NbaQueue2) (hg : ∀ a b, ∀ u ∈ g a b, u.1 ≠ n) (x : LVec) :
    nbaFold n (l₁.flatMap fun a => l₂.flatMap fun b => f a b ++ g a b) x =
      nbaFold n (l₁.flatMap fun a => l₂.flatMap fun b => f a b) x := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons a l₁ ih =>
    simp only [List.flatMap_cons, nbaFold_append, nbaFold_flatMap_drop_right n l₂ (f a) (g a) (hg a)]
    exact ih _

theorem nbaFold_flatMap₂_drop_left (n : String) {α β : Type} (l₁ : List α) (l₂ : List β)
    (f g : α → β → NbaQueue2) (hf : ∀ a b, ∀ u ∈ f a b, u.1 ≠ n) (x : LVec) :
    nbaFold n (l₁.flatMap fun a => l₂.flatMap fun b => f a b ++ g a b) x =
      nbaFold n (l₁.flatMap fun a => l₂.flatMap fun b => g a b) x := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons a l₁ ih =>
    simp only [List.flatMap_cons, nbaFold_append, nbaFold_flatMap_drop_left n l₂ (f a) (g a) (hf a)]
    exact ih _

theorem p0Q_eq_nil (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.p0Q N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh = [] := rfl
theorem p1Q_eq_nil (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.p1Q N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh = [] := rfl
theorem g_col_wordQ_eq_nil (N W AccW i j q : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.g_col_wordQ N W AccW i j q ck r s a b dn c k bz as_ bs_ bc ash bsh = [] := rfl

def cellsAllQ (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_mesh_colQ N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh ++
      mmG.g_mesh_col_1Q N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh

def cellsSkewQ (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_mesh_colQ N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh

def cellsCQ (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_mesh_col_1Q N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh

theorem edgeQ_eq (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.edgeQ N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh =
      mmG.p2Q N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh ++
        cellsAllQ N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh := by
  have hnil : ∀ l : List Nat, (l.flatMap fun _ => ([] : NbaQueue2)) = [] := by
    intro l; induction l <;> simp [*]
  simp [mmG.edgeQ, cellsAllQ, p0Q_eq_nil, p1Q_eq_nil, g_col_wordQ_eq_nil, hnil]

theorem p2Q_names (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    ∀ u ∈ mmG.p2Q N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh,
      u.1 ∈ ["busy", "done", "k"] := by
  intro u hu
  unfold mmG.p2Q at hu
  split at hu
  · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
    · split at hu
      · split at hu
        · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
        · simp at hu; subst hu; simp
      · simp at hu

theorem g_mesh_colQ_names (N W AccW i j : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    ∀ u ∈ mmG.g_mesh_colQ N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh,
      u.1 ∈ ["a_skew_bank", "b_skew_bank"] := by
  intro u hu
  unfold mmG.g_mesh_colQ at hu
  split at hu
  · simp at hu; rcases hu with rfl | rfl <;> simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl <;> simp
    · split at hu
      · simp at hu; rcases hu with rfl | rfl <;> simp
      · simp at hu

theorem g_mesh_col_1Q_names (N W AccW i j : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    ∀ u ∈ mmG.g_mesh_col_1Q N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh,
      u.1 ∈ ["C"] := by
  have haux : ∀ (c1 c2 : Bool) (v1 v2 : LVec) (u : String × Nat × LVec),
      u ∈ (if c1 = true then [("C", (i * N + j) * AccW, v1)]
           else if c2 = true then [("C", (i * N + j) * AccW, v2)] else []) → u.1 ∈ ["C"] := by
    intro c1 c2 v1 v2 u hu
    cases c1 <;> cases c2 <;> simp at hu
    · subst hu; simp
    · subst hu; simp
    · subst hu; simp
  intro u hu
  exact haux _ _ _ _ u hu

theorem cellsAllQ_names (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    ∀ u ∈ cellsAllQ N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh,
      u.1 ∈ ["a_skew_bank", "b_skew_bank", "C"] := by
  intro u hu
  simp only [cellsAllQ, List.mem_flatMap, List.mem_range, List.mem_append] at hu
  obtain ⟨i, -, j, -, hu | hu⟩ := hu
  · have := g_mesh_colQ_names N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh u hu
    simp at this ⊢; rcases this with h | h <;> simp [h]
  · have := g_mesh_col_1Q_names N W AccW i j ck r s a b dn c k bz as_ bs_ bc ash bsh u hu
    simp at this ⊢; simp [this]

theorem edgeQ_names (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    ∀ u ∈ mmG.edgeQ N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh,
      u.1 ∈ ["busy", "done", "k", "a_skew_bank", "b_skew_bank", "C"] := by
  rw [edgeQ_eq]
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · have := p2Q_names N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh u hu
    simp at this ⊢; rcases this with h | h | h <;> simp [h]
  · have := cellsAllQ_names N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh u hu
    simp at this ⊢; rcases this with h | h | h <;> simp [h]

theorem mmG_next_eq (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    let bc1 := mmG.comb_b_col_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
    let ash1 := mmG.comb_a_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
    let bsh1 := mmG.comb_b_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
    let pQ := mmG.p2Q N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
    let sQ := cellsSkewQ N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
    let cQ := cellsCQ N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
    mmG.next N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh =
      mmG.comb N W AccW ck r s a b
        (nbaFold "done" pQ dn) (nbaFold "C" cQ c) (nbaFold "k" pQ k) (nbaFold "busy" pQ bz)
        (nbaFold "a_skew_bank" sQ as_) (nbaFold "b_skew_bank" sQ bs_) bc1 ash1 bsh1 := by
  dsimp only [mmG.next]
  let bc1 := mmG.comb_b_col_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
  let ash1 := mmG.comb_a_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
  let bsh1 := mmG.comb_b_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh
  have he := edgeQ_names N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
  have hp := p2Q_names N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
  have hca := cellsAllQ_names N W AccW ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1
  rw [nbaFold_of_names he (by decide : "clk" ∉ _),
      nbaFold_of_names he (by decide : "rst" ∉ _),
      nbaFold_of_names he (by decide : "start" ∉ _),
      nbaFold_of_names he (by decide : "A" ∉ _),
      nbaFold_of_names he (by decide : "B" ∉ _),
      nbaFold_of_names he (by decide : "b_col_bank" ∉ _),
      nbaFold_of_names he (by decide : "a_shift_bank" ∉ _),
      nbaFold_of_names he (by decide : "b_shift_bank" ∉ _)]
  simp only [edgeQ_eq, nbaFold_append]
  rw [nbaFold_of_names hca (by decide : "done" ∉ _),
      nbaFold_of_names hca (by decide : "k" ∉ _),
      nbaFold_of_names hca (by decide : "busy" ∉ _),
      nbaFold_of_names hp (by decide : "C" ∉ _),
      nbaFold_of_names hp (by decide : "a_skew_bank" ∉ _),
      nbaFold_of_names hp (by decide : "b_skew_bank" ∉ _)]
  unfold cellsAllQ cellsSkewQ cellsCQ
  rw [nbaFold_flatMap₂_drop_left "C" _ _ _ _ (fun i j u hu => by
        have := g_mesh_colQ_names N W AccW i j ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1 u hu
        simp at this; rcases this with h | h <;> simp [h]),
      nbaFold_flatMap₂_drop_right "a_skew_bank" _ _ _ _ (fun i j u hu => by
        have := g_mesh_col_1Q_names N W AccW i j ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1 u hu
        simp at this; simp [this]),
      nbaFold_flatMap₂_drop_right "b_skew_bank" _ _ _ _ (fun i j u hu => by
        have := g_mesh_col_1Q_names N W AccW i j ck r s a b dn c k bz as_ bs_ bc1 ash1 bsh1 u hu
        simp at this; simp [this])]

theorem comb_a_shift_bank_eq {N W AccW : Nat} (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.comb_a_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh =
      (as_.shr (LVec.ofInt 32 ↑W)).resizeU ash.width := by
  unfold mmG.comb_a_shift_bank mmG.combQ mmG.p0C mmG.p1C
  simp only [List.singleton_append, nbaFold_cons_self, nbaFold_cons_ne (by decide : "b_shift_bank" ≠ "a_shift_bank")]
  rw [nbaFold_of_forall_ne (fun u hu => by
        simp only [List.mem_flatMap, List.mem_range, mmG.g_col_wordC, List.mem_singleton] at hu
        obtain ⟨-, -, -, -, -, -, rfl⟩ := hu; simp)]
  exact LVec.insertAt_zero_of_width_eq (by simp)

theorem comb_b_shift_bank_eq {N W AccW : Nat} (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec) :
    mmG.comb_b_shift_bank N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh =
      (bs_.shr (LVec.ofInt 32 ↑W)).resizeU bsh.width := by
  unfold mmG.comb_b_shift_bank mmG.combQ mmG.p0C mmG.p1C
  simp only [List.singleton_append, nbaFold_cons_ne (by decide : "a_shift_bank" ≠ "b_shift_bank"), nbaFold_cons_self]
  rw [nbaFold_of_forall_ne (fun u hu => by
        simp only [List.mem_flatMap, List.mem_range, mmG.g_col_wordC, List.mem_singleton] at hu
        obtain ⟨-, -, -, -, -, -, rfl⟩ := hu; simp)]
  exact LVec.insertAt_zero_of_width_eq (by simp)

theorem comb_b_col_bank_known {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (Bv : BitVec (N * N * W)) (ck r s a dn c k bz as_ bs_ bc ash bsh : LVec)
    (hbc : bc.width = N * N * N * W) :
    mmG.comb_b_col_bank N W AccW ck r s a (LVec.ofBitVec Bv) dn c k bz as_ bs_ bc ash bsh =
      LVec.ofBitVec (ttB N W Bv) := by
  refine LVec.eq_ofBitVec_packBV (by simp [mmG.comb_b_col_bank, hbc]) fun q hq => ?_
  have hqN : q / N < N * N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hi : q / N / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hqN
  have hj : q / N % N < N := Nat.mod_lt _ (by omega)
  have ht : q % N < N := Nat.mod_lt _ (by omega)
  have h1 : q / N / N * N + q / N % N = q / N := by rw [Nat.mul_comm]; exact Nat.div_add_mod (q / N) N
  have h2 : (q / N / N * N + q / N % N) * N * W + q % N * W = q * W := by
    rw [h1, ← Nat.add_mul, show q / N * N + q % N = q by rw [Nat.mul_comm]; exact Nat.div_add_mod q N]
  have hm : ("b_col_bank", q * W, ((LVec.ofBitVec Bv).extract ((q % N * N + q / N % N) * W) W).resizeU W) ∈
      mmG.combQ N W AccW ck r s a (LVec.ofBitVec Bv) dn c k bz as_ bs_ bc ash bsh := by
    simp only [mmG.combQ, mmG.p0C, mmG.p1C, mmG.g_col_wordC, List.singleton_append,
      List.mem_cons, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr ⟨q / N / N, hi, q / N % N, hj, q % N, ht, by rw [h2]⟩)
  have hbound : q * W + (((LVec.ofBitVec Bv).extract ((q % N * N + q / N % N) * W) W).resizeU W).width ≤ bc.width := by
    rw [LVec.width_resizeU, hbc]
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq)
    rwa [Nat.succ_mul] at this
  have hex := SvGolf.Cycle.extract_nbaFold_of_mem
    (mmG.combQ_disj N W AccW hN hW hA hN32 hW32 hA32 ck r s a (LVec.ofBitVec Bv) dn c k bz as_ bs_ bc ash bsh)
    hm hbound
  rw [LVec.width_resizeU] at hex
  change (nbaFold "b_col_bank" _ bc).extract (q * W) W = _
  rw [hex, LVec.extract_ofBitVec Bv (Lib.rowMajor_window_le ht hj), LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

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
  have hlx : (LVec.ofLogic Logic.lx).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  cases b1 <;> cases b2 <;> simp only [hne, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
    Bool.or_true, Bool.true_or, Bool.or_false, hl1]
  split <;> simp [hl0, hlx]

/-! ## 4. Shape and one-cycle transitions -/

def Wd (N W AccW : Nat) (dn c k bz as_ bs_ bc ash bsh : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  as_.width = N * N * N * W ∧ bs_.width = N * N * N * W ∧
  bc.width = N * N * N * W ∧ ash.width = N * N * N * W ∧ bsh.width = N * N * N * W

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz as_ bs_ bc ash bsh,
    st = mmG.St ck r s a b dn c k bz as_ bs_ bc ash bsh ∧
    Wd N W AccW dn c k bz as_ bs_ bc ash bsh

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mmG.init N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd]⟩

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz as_ bs_ bc ash bsh : LVec)
    (hw : Wd N W AccW dn c k bz as_ bs_ bc ash bsh) :
    I N W AccW (mmG.next N W AccW ck r s a b dn c k bz as_ bs_ bc ash bsh) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hw
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [Wd, mmG.comb_b_col_bank, mmG.comb_a_shift_bank, mmG.comb_b_shift_bank,
    h1, h2, h3, h4, h5, h6, h7, h8, h9]

def Ready (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c k as_ bs_ bc ash bsh,
    st = mmG.St ck r s a b (knownBit false) c k (knownBit false) as_ bs_ bc ash bsh ∧
    c.width = N * N * AccW ∧ k.width = 32 ∧
    as_.width = N * N * N * W ∧ bs_.width = N * N * N * W ∧
    bc.width = N * N * N * W ∧ ash.width = N * N * N * W ∧ bsh.width = N * N * N * W

def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b bc ash bsh,
    st = mmG.St ck r s a b (knownBit false) (accC N W AccW A B t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (ttA N W A >>> (t * W))) (LVec.ofBitVec (ttB N W B >>> (t * W)))
      bc ash bsh ∧
    bc.width = N * N * N * W ∧ ash.width = N * N * N * W ∧ bsh.width = N * N * N * W

def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k as_ bs_ bc ash bsh,
    st = mmG.St ck r s a b (knownBit true)
      (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k (knownBit false) as_ bs_ bc ash bsh ∧
    k.width = 32 ∧ as_.width = N * N * N * W ∧ bs_.width = N * N * N * W ∧
    bc.width = N * N * N * W ∧ ash.width = N * N * N * W ∧ bsh.width = N * N * N * W

theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz as_ bs_ bc ash bsh : LVec)
    (hw : Wd N W AccW dn c k bz as_ bs_ bc ash bsh) :
    Ready N W AccW (mmG.next N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hw
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p2Q N W AccW ck (knownBit true) s a b dn c k bz as_ bs_
      (mmG.comb_b_col_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)
      (mmG.comb_a_shift_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)
      (mmG.comb_b_shift_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)) dn =
      knownBit false := by
    simp (disch := decide) only [mmG.p2Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p2Q N W AccW ck (knownBit true) s a b dn c k bz as_ bs_
      (mmG.comb_b_col_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)
      (mmG.comb_a_shift_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)
      (mmG.comb_b_shift_bank N W AccW ck (knownBit true) s a b dn c k bz as_ bs_ bc ash bsh)) bz =
      knownBit false := by
    simp (disch := decide) only [mmG.p2Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [hd, hb]
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [h2], by simp [h3], by simp [h5], by simp [h6],
    by simp [mmG.comb_b_col_bank, h7], by simp [mmG.comb_a_shift_bank, h8], by simp [mmG.comb_b_shift_bank, h9]⟩

theorem next_idle {N W AccW : Nat} (ck a b dn c k as_ bs_ bc ash bsh : LVec) :
    ∃ bc' ash' bsh',
      mmG.next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh =
        mmG.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc' ash' bsh' ∧
      bc'.width = bc.width ∧ ash'.width = ash.width ∧ bsh'.width = bsh.width := by
  rw [mmG_next_eq]
  have hp : mmG.p2Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_
      (mmG.comb_b_col_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_a_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_b_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh) = [] := by
    simp [mmG.p2Q]
  have hs : cellsSkewQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_
      (mmG.comb_b_col_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_a_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_b_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh) = [] := by
    simp [cellsSkewQ, mmG.g_mesh_colQ]
  have hc : cellsCQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_
      (mmG.comb_b_col_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_a_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh)
      (mmG.comb_b_shift_bank N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) as_ bs_ bc ash bsh) = [] := by
    simp [cellsCQ, mmG.g_mesh_col_1Q]
  rw [hp, hs, hc]
  exact ⟨_, _, _, rfl, by simp [mmG.comb_b_col_bank], by simp [mmG.comb_a_shift_bank],
    by simp [mmG.comb_b_shift_bank]⟩

theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (Av Bv : BitVec (N * N * W)) (ck dn c k bz as_ bs_ bc ash bsh : LVec)
    (hw : Wd N W AccW dn c k bz as_ bs_ bc ash bsh) :
    BusyAt N W AccW Av Bv 0
      (mmG.next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn c k bz as_ bs_ bc ash bsh) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hw
  rw [mmG_next_eq]
  rw [comb_b_col_bank_known hN hW hA hN32 hW32 hA32 Bv _ _ _ _ _ _ _ _ _ _ _ _ _ h7]
  let ash1 := mmG.comb_a_shift_bank N W AccW ck (knownBit false) (knownBit true)
    (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ bc ash bsh
  let bsh1 := mmG.comb_b_shift_bank N W AccW ck (knownBit false) (knownBit true)
    (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ bc ash bsh
  have hd : nbaFold "done" (mmG.p2Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) dn =
      knownBit false := by
    simp (disch := decide) only [mmG.p2Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p2Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) bz =
      knownBit true := by
    simp (disch := decide) only [mmG.p2Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l1]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  have hk : nbaFold "k" (mmG.p2Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) k =
      LVec.ofBitVec (BitVec.ofNat 32 0) := by
    simp (disch := decide) only [mmG.p2Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h3, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h3])
  have hc : nbaFold "C" (cellsCQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) c =
      accC N W AccW Av Bv 0 := by
    have hq : cellsCQ N W AccW ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1 =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 0 (r / N) (r % N)))) := by
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp only [mmG.g_mesh_col_1Q, lor_cond_knownBit]
      simp [psum, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h2]; rfl
  have has : nbaFold "a_skew_bank" (cellsSkewQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) as_ =
      LVec.ofBitVec (ttA N W Av) := by
    unfold cellsSkewQ
    have hstep : ∀ i j, mmG.g_mesh_colQ N W AccW i j ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1 =
      [("a_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec Av).extract (i * N * W) (N * W)).resizeU (N * W))] ++
      [("b_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec (ttB N W Bv)).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] := by
      intro i j; simp [mmG.g_mesh_colQ, Nat.mul_assoc]
    simp only [hstep]
    rw [nbaFold_flatMap₂_drop_right "a_skew_bank" _ _ _ _ (fun _ _ u hu => by simp at hu; subst hu; simp)]
    have hq := flatMap_range_rowMajor (R := N) (M := N)
      (q := fun i j => [("a_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec Av).extract (i * N * W) (N * W)).resizeU (N * W))])
      (fun r => ("a_skew_bank", r * (N * W), ((LVec.ofBitVec Av).extract (r / N * N * W) (N * W)).resizeU (N * W)))
      (fun i j hi hj => by simp [rowMajor_div hj])
    rw [hq, nbaFold_map_insertEntries, insertEntries_rowA hN Av as_ h5]
  have hbs : nbaFold "b_skew_bank" (cellsSkewQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1) bs_ =
      LVec.ofBitVec (ttB N W Bv) := by
    unfold cellsSkewQ
    have hstep : ∀ i j, mmG.g_mesh_colQ N W AccW i j ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz as_ bs_ (LVec.ofBitVec (ttB N W Bv)) ash1 bsh1 =
      [("a_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec Av).extract (i * N * W) (N * W)).resizeU (N * W))] ++
      [("b_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec (ttB N W Bv)).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] := by
      intro i j; simp [mmG.g_mesh_colQ, Nat.mul_assoc]
    simp only [hstep]
    rw [nbaFold_flatMap₂_drop_left "b_skew_bank" _ _ _ _ (fun _ _ u hu => by simp at hu; subst hu; simp)]
    have hq := flatMap_range_rowMajor (R := N) (M := N)
      (q := fun i j => [("b_skew_bank", (i * N + j) * (N * W), ((LVec.ofBitVec (ttB N W Bv)).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))])
      (fun r => ("b_skew_bank", r * (N * W), ((LVec.ofBitVec (ttB N W Bv)).extract (r * (N * W)) (N * W)).resizeU (N * W)))
      (fun i j hi hj => rfl)
    rw [hq, nbaFold_map_insertEntries, insertEntries_copy_ofBitVec hN (ttB N W Bv) bs_ h6]
  change BusyAt N W AccW Av Bv 0
    (mmG.comb _ _ _ _ _ _ _ _ (nbaFold "done" _ _) (nbaFold "C" _ _) (nbaFold "k" _ _) (nbaFold "busy" _ _)
      (nbaFold "a_skew_bank" _ _) (nbaFold "b_skew_bank" _ _) _ ash1 bsh1)
  rw [hd, hb, hk, hc, has, hbs]
  unfold mmG.comb BusyAt
  simp only [Nat.zero_mul, BitVec.ushiftRight_zero]
  refine ⟨_, _, _, _, _, _, _, _, rfl,
    by simp [mmG.comb_b_col_bank],
    by simp [mmG.comb_a_shift_bank, ash1, h8],
    by simp [mmG.comb_b_shift_bank, bsh1, h9]⟩

theorem cell_acc_step {N W AccW : Nat} (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {t i j : Nat} (hi : i < N) (hj : j < N) (ht : t < N) :
    let as_ := LVec.ofBitVec (ttA N W Av >>> (t * W))
    let bs_ := LVec.ofBitVec (ttB N W Bv >>> (t * W))
    let c := accC N W AccW Av Bv t
    ((((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        ((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[as_.extract ((i * N + j) * N * W + W - 1) 1]),
            as_.extract ((i * N + j) * N * W) W]).mul
          (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[bs_.extract ((i * N + j) * N * W + W - 1) 1]),
            bs_.extract ((i * N + j) * N * W) W]))).resizeU AccW).resizeU AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) i j)) := by
  dsimp only
  have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
  have hWbound : (i * N + j) * N * W + W ≤ N * N * N * W := by
    have hq : (i * N + j) * N < N * N * N := by have := rowMajor_le (K := N) h1; omega
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq)
    rwa [Nat.succ_mul] at this
  have hexC : (accC N W AccW Av Bv t).extract ((i * N + j) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv t i j)) := by
    rw [accC, extract_ofBitVec_packBV _ h1 rfl, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
  have hexA : (LVec.ofBitVec (ttA N W Av >>> (t * W))).extract ((i * N + j) * N * W) W =
      LVec.ofBitVec (Av.extractLsb' ((i * N + t) * W) W) := by
    rw [LVec.extract_ofBitVec _ hWbound, ttA_shift_extract Av hi hj ht]
  have hexB : (LVec.ofBitVec (ttB N W Bv >>> (t * W))).extract ((i * N + j) * N * W) W =
      LVec.ofBitVec (Bv.extractLsb' ((t * N + j) * W) W) := by
    rw [LVec.extract_ofBitVec _ hWbound, ttB_shift_extract Bv hi hj ht]
  rw [hexC, LVec.sext_of_extract hW hexA, LVec.sext_of_extract hW hexB,
    LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec,
    LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend (by omega : AccW ≤ AccW + W),
    ← BitVec.ofInt_add, psum_succ]
  rfl

theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648)
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b bc ash bsh : LVec)
    (hbc : bc.width = N * N * N * W) (hash : ash.width = N * N * N * W) (hbsh : bsh.width = N * N * N * W) :
    ∃ bc' ash' bsh',
      mmG.next N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
          (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
          (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc ash bsh =
        mmG.St ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N)))
          (accC N W AccW Av Bv (t + 1)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
          (knownBit (decide (t + 1 ≠ N)))
          (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W)))
          bc' ash' bsh' ∧
      bc'.width = N * N * N * W ∧ ash'.width = N * N * N * W ∧ bsh'.width = N * N * N * W := by
  have hW_toNat : (BitVec.ofNat 32 W).toNat = W := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [mmG_next_eq]
  rw [comb_a_shift_bank_eq, comb_b_shift_bank_eq]
  simp only [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.shr_ofBitVec, hW_toNat,
    hash, hbsh, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, shiftRight_shiftRight, ← Nat.succ_mul]
  let bc1 := mmG.comb_b_col_bank N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
    (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
    (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc ash bsh
  have hc : nbaFold "C" (cellsCQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
      (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
      (accC N W AccW Av Bv t) = accC N W AccW Av Bv (t + 1) := by
    have hq : cellsCQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))) =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) (r / N) (r % N)))) := by
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp only [mmG.g_mesh_col_1Q, lor_cond_knownBit]
      simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        condTrue_knownBit, cell_acc_step hW Av Bv hi hj ht, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (accC_width ..)]; rfl
  have has : nbaFold "a_skew_bank" (cellsSkewQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
      (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
      (LVec.ofBitVec (ttA N W Av >>> (t * W))) = LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W)) := by
    unfold cellsSkewQ
    have hstep : ∀ i j, mmG.g_mesh_colQ N W AccW i j ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))) =
      [("a_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] ++
      [("b_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] := by
      intro i j; simp [mmG.g_mesh_colQ, Nat.mul_assoc]
    simp only [hstep]
    rw [nbaFold_flatMap₂_drop_right "a_skew_bank" _ _ _ _ (fun _ _ u hu => by simp at hu; subst hu; simp)]
    have hq := flatMap_range_rowMajor (R := N) (M := N)
      (q := fun i j => [("a_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))])
      (fun r => ("a_skew_bank", r * (N * W),
        ((LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))).extract (r * (N * W)) (N * W)).resizeU (N * W)))
      (fun i j hi hj => rfl)
    rw [hq, nbaFold_map_insertEntries, insertEntries_copy_ofBitVec hN _ _ (by simp)]
  have hbs : nbaFold "b_skew_bank" (cellsSkewQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
      (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
      (LVec.ofBitVec (ttB N W Bv >>> (t * W))) = LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W)) := by
    unfold cellsSkewQ
    have hstep : ∀ i j, mmG.g_mesh_colQ N W AccW i j ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))) =
      [("a_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] ++
      [("b_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))] := by
      intro i j; simp [mmG.g_mesh_colQ, Nat.mul_assoc]
    simp only [hstep]
    rw [nbaFold_flatMap₂_drop_left "b_skew_bank" _ _ _ _ (fun _ _ u hu => by simp at hu; subst hu; simp)]
    have hq := flatMap_range_rowMajor (R := N) (M := N)
      (q := fun i j => [("b_skew_bank", (i * N + j) * (N * W),
        ((LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))).extract ((i * N + j) * (N * W)) (N * W)).resizeU (N * W))])
      (fun r => ("b_skew_bank", r * (N * W),
        ((LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))).extract (r * (N * W)) (N * W)).resizeU (N * W)))
      (fun i j hi hj => rfl)
    rw [hq, nbaFold_map_insertEntries, insertEntries_copy_ofBitVec hN _ _ (by simp)]
  have hctrl :
      nbaFold "done" (mmG.p2Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
        (knownBit false) = knownBit (decide (t + 1 = N)) ∧
      nbaFold "k" (mmG.p2Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
        (LVec.ofBitVec (BitVec.ofNat 32 t)) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
      nbaFold "busy" (mmG.p2Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) bc1
        (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))))
        (knownBit true) = knownBit (decide (t + 1 ≠ N)) := by
    simp only [mmG.p2Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
      BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec,
      LVec.ofLogic_ofBool, decide_eq_true_eq,
      Lib.ofNat_eq_ofNat_sub_one_iff ht (by omega : N ≤ 2 ^ 32),
      LVec.width_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    by_cases hf : t + 1 = N <;>
      simp [hf, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
        BitVec.ofNat_add_ofNat]
  obtain ⟨h1, h2, h3⟩ := hctrl
  change ∃ bc' ash' bsh',
    mmG.comb _ _ _ _ _ _ _ _ (nbaFold "done" _ _) (nbaFold "C" _ _) (nbaFold "k" _ _)
      (nbaFold "busy" _ _) (nbaFold "a_skew_bank" _ _) (nbaFold "b_skew_bank" _ _) bc1 _ _ = _ ∧ _
  rw [hc, has, hbs, h1, h2, h3]
  refine ⟨_, _, _, rfl,
    by simp [mmG.comb_b_col_bank, bc1, hbc],
    by simp [mmG.comb_a_shift_bank],
    by simp [mmG.comb_b_shift_bank]⟩

/-! ## 5. Phase model -/

theorem St_inj {ck r s a b dn c k bz as_ bs_ bc ash bsh ck' r' s' a' b' dn' c' k' bz' as' bs' bc' ash' bsh' : LVec}
    (h : mmG.St ck r s a b dn c k bz as_ bs_ bc ash bsh =
      mmG.St ck' r' s' a' b' dn' c' k' bz' as' bs' bc' ash' bsh') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ as_ = as' ∧ bs_ = bs' ∧ bc = bc' ∧ ash = ash' ∧ bsh = bsh' := by
  simp only [mmG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz as_ bs_ bc ash bsh,
    prev = mmG.St ck r s a b dn c k bz as_ bs_ bc ash bsh ∧
    Wd N W AccW dn c k bz as_ bs_ bc ash bsh ∧
    st = mmG.next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz as_ bs_ bc ash bsh

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hN32 hW32 hA32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, as_, bs_, bc, ash, bsh, rfl, hw⟩ hc
    obtain ⟨kk', hnext⟩ := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c kk bz as_ bs_ bc ash bsh k 32 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, as_, bs_, bc, ash, bsh, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz as_ bs_ bc ash bsh hw
  Ready := Ready N W AccW
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, as_, bs_, bc, ash, bsh, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, bc, ash, bsh, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, as_, bs_, bc, ash, bsh, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmG.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset _ _ _ _ dn c k bz as_ bs_ bc ash bsh hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N - 1, by omega, 0, by omega,
      next_start hN hW hA hN32 hW32 hA32 _ _ _ dn c k bz as_ bs_ bc ash bsh hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', bc', ash', bsh', hb, hbc, hash, hbsh⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨bc1, ash1, bsh1, hstep, hbc1, hash1, hbsh1⟩ :=
      next_step (AccW := AccW) hN hW hN32 hW32 x.1 x.2.1 (t := t) (by omega)
        (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) bc ash bsh hbc hash hbsh
    rw [hstep]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, by simp, by simp, by simp, hbc1, hash1, hbsh1⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, _, _, rfl, hbc1, hash1, hbsh1⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', as', bs', bc', ash', bsh', hb, h2, h3, h5, h6, h7, h8, h9⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨bc1, ash1, bsh1, hidle, hbc1, hash1, hbsh1⟩ :=
      next_idle (N := N) (W := W) (AccW := AccW) (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
        (knownBit false) c k as_ bs_ bc ash bsh
    rw [hidle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, h2, h3, h5, h6, hbc1.trans h7, hash1.trans h8, hbsh1.trans h9⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', as', bs', bc', ash', bsh', hb, h3, h5, h6, h7, h8, h9⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨bc1, ash1, bsh1, hidle, hbc1, hash1, hbsh1⟩ :=
      next_idle (N := N) (W := W) (AccW := AccW) (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
        (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) k as_ bs_ bc ash bsh
    rw [hidle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, h3, h5, h6, hbc1.trans h7, hash1.trans h8, hbsh1.trans h9⟩

/-! ## 6. Interface, discipline, and the three v2 rules -/

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmG.D N W AccW).processes.toList) :
    p = mmG.p0 N W AccW ∨ p = mmG.p1 N W AccW ∨ p = mmG.p2 N W AccW ∨
      (∃ i j t, i < N ∧ j < N ∧ t < N ∧ p = mmG.g_col_word N W AccW i j t) ∨
      (∃ i j, i < N ∧ j < N ∧ (p = mmG.g_mesh_col N W AccW i j ∨ p = mmG.g_mesh_col_1 N W AccW i j)) := by
  simp only [mmG.D, List.toList_toArray, mmG.procs, List.mem_cons, List.mem_flatMap, List.mem_append,
    List.mem_map, List.mem_range, List.singleton_append, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | ⟨i, hi, j, hj, ⟨t, ht, rfl⟩ | rfl | rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl ⟨i, j, t, hi, hj, ht, rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨i, j, hi, hj, .inl rfl⟩)))
  · exact .inr (.inr (.inr (.inr ⟨i, j, hi, hj, .inr rfl⟩)))

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "a_skew_bank", "b_skew_bank", "b_col_bank", "a_shift_bank", "b_shift_bank"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmG.D, mmG.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, t, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl | rfl⟩
  · simp [Tasks.Matmul.task, mmG.p0, edgeClock, asyncReset, processDataNames, lhsNames, exprNames,
      Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.p1, edgeClock, asyncReset, processDataNames, lhsNames, exprNames,
      Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.p2, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_col_word, edgeClock, asyncReset, processDataNames, lhsNames, exprNames,
      Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.g_mesh_col, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_mesh_col_1, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, lhsNames, exprNames, exprListNames]

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨fun n => n ≠ "done" ∧ n ≠ "C", ?_, ?_, ?_⟩
  · intro n hn _
    simp [mmG.D, mmG.decls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he _
    obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, t, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl | rfl⟩
    · simp [mmG.p0, processDeps, lhsTargets] at he; simp [he]
    · simp [mmG.p1, processDeps, lhsTargets] at he; simp [he]
    · simp [mmG.p2, processDeps] at he
    · simp [mmG.g_col_word, processDeps, lhsTargets] at he; simp [he]
    · simp [mmG.g_mesh_col, processDeps] at he
    · simp [mmG.g_mesh_col_1, processDeps] at he
  · intro o ho
    simp [mmG.D, mmG.decls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> simp

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl,
    -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
    mmG.powerUp N W AccW hN hW hA hN32 hW32 hA32 st h
  exact ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem mm_noq (N W AccW : Nat) :
    (mmG.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, t, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl | rfl⟩ <;>
    simp [mmG.p0, mmG.p1, mmG.p2, mmG.g_col_word, mmG.g_mesh_col, mmG.g_mesh_col_1,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32) (fun σ => ⟨32, ?_⟩)
    (by rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, as_, bs_, bc, ash, bsh, rfl, hw⟩
  obtain ⟨kk', hnext⟩ := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
    ck r s a b dn c k bz as_ bs_ bc ash bsh kk 32 (Nat.le_refl _)
  exact ⟨_, _, hnext, mmNext_I N W AccW _ _ _ _ _ dn c k bz as_ bs_ bc ash bsh hw⟩

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mm_proc_mem hp with rfl | rfl | rfl | ⟨i, j, t, hi, hj, ht, rfl⟩ | ⟨i, j, hi, hj, rfl | rfl⟩
  · simp [xsProc, xsLhs, xsWidth, binW, sigWidth, mmG.p0, mmG.D, mmG.decls, LVec.ofInt]
  · simp [xsProc, xsLhs, xsWidth, binW, sigWidth, mmG.p1, mmG.D, mmG.decls, LVec.ofInt]
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmG.p2, mmG.D, mmG.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hB' : (t * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le ht hj
    simp [xsProc, xsLhs, xsWidth, sigWidth, mmG.g_col_word, mmG.D, mmG.decls, hB']
  · have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
    have hA' : i * N * W + N * W ≤ N * N * W := by
      have := Nat.mul_le_mul_right (N * W) (Nat.succ_le_of_lt hi)
      simpa [Nat.succ_mul, Nat.mul_assoc] using this
    have hS : (i * N + j) * N * W + N * W ≤ N * N * N * W := by
      have := Nat.mul_le_mul_right (N * W) (Nat.succ_le_of_lt h1)
      simpa [Nat.succ_mul, Nat.mul_assoc] using this
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, sigWidth, mmG.g_mesh_col, mmG.D, mmG.decls,
      LVec.allKnown_ofBitVec, hA', hS]
  · have hC : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
    have hS : (i * N + j) * N * W + W ≤ N * N * N * W := by
      have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
      have hq : (i * N + j) * N < N * N * N := by have := rowMajor_le (K := N) h1; omega
      have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq); rwa [Nat.succ_mul] at this
    have hS1 : (i * N + j) * N * W + W - 1 + 1 ≤ N * N * N * W := by omega
    simp [xsProc, xsStmt, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_mesh_col_1, mmG.D, mmG.decls, LVec.allKnown_ofBitVec, hC, hS, hS1]

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hN32 : N < 2147483648 := by omega
  have hW32 : W < 2147483648 := by omega
  have hA32 : AccW < 2147483648 := by omega
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases
    (mm_interface N W AccW hN hW hA hN32 hW32 hA32)
    (mm_disciplined N W AccW hN hW hA hN32 hW32 hA32)
    (mm_terminatesPU N W AccW hN hW hA hN32 hW32 hA32) hN
    (model N W AccW hN hW hA hN32 hW32 hA32)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32)
    (mm_moore N W AccW hN hW hA hN32 hW32 hA32)
    (mm_xsafe N W AccW hN hW hA hN32 hW32 hA32)

end Submission
