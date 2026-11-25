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
  have sepA : ∀ q q', q < q' → q * AccW + AccW ≤ q' * AccW := fun q q' h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  have cell : ∀ i j i' j', i * N + j < i' * N + j' →
      ∀ p ∈ ((List.range N).flatMap fun t => [mmG.g_time_word N W AccW i j t] ++ [mmG.g_time_word_1 N W AccW i j t]) ++
          [mmG.g_time_col N W AccW i j],
      ∀ q ∈ ((List.range N).flatMap fun t => [mmG.g_time_word N W AccW i' j' t] ++ [mmG.g_time_word_1 N W AccW i' j' t]) ++
          [mmG.g_time_col N W AccW i' j'],
      SvGolf.Cycle.WinDisj p q := by
    intro i j i' j' h p hp q hq
    have hA := sepA (i * N + j) (i' * N + j') h
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.singleton_append,
      List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with ⟨t, ht, rfl | rfl⟩ | rfl <;> rcases hq with ⟨t', ht', rfl | rfl⟩ | rfl
    · have hW := sepW ((i * N + j) * N + t) ((i' * N + j') * N + t') (rowMajor_lt ht h)
      exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word, mmG.g_time_word_1,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word, mmG.g_time_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word_1, mmG.g_time_word,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])
    · have hW := sepW ((i * N + j) * N + t) ((i' * N + j') * N + t') (rowMajor_lt ht h)
      exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word_1,
        Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word_1, mmG.g_time_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_col, mmG.g_time_word,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_col, mmG.g_time_word_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  unfold mmG.procs
  refine List.Pairwise.cons (fun q hq => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)
  · simp only [List.mem_flatMap, List.mem_append, List.mem_range, List.singleton_append,
      List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨i, -, j, -, ⟨t, -, rfl | rfl⟩ | rfl⟩ := hq
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_time_word,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_time_word_1,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
    · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.p0, mmG.g_time_col,
        Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
  · refine pairwise_flatMap_range (fun j _ => ?_) ?_
    · refine List.pairwise_append.mpr ⟨?_, List.pairwise_singleton _ _, ?_⟩
      · refine pairwise_flatMap_range (fun t _ => ?_) ?_
        · simp only [List.singleton_append]
          exact .cons (fun q hq => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq
            exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word, mmG.g_time_word_1,
              Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps])) (.cons (fun _ h => by simp at h) .nil)
        · intro t t' htt' _ p hp q hq
          have hW := sepW ((i * N + j) * N + t) ((i * N + j) * N + t') (by omega)
          simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hp hq
          rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
            exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word, mmG.g_time_word_1,
              Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
      · intro p hp q hq
        simp only [List.mem_flatMap, List.mem_range, List.singleton_append, List.mem_cons,
          List.not_mem_nil, or_false] at hp hq
        subst hq
        obtain ⟨t, -, rfl | rfl⟩ := hp
        · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word, mmG.g_time_col,
            Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, DrvWin.overlaps])
        · exact SvGolf.Cycle.WinDisj.of_all (by simp [SvGolf.Cycle.allWins, mmG.g_time_word_1, mmG.g_time_col,
            Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
            Lhs2.drvWins, DrvWin.overlaps])
    · intro j j' hjj' _ p hp q hq
      exact cell i j i j' (by omega) p hp q hq
  · intro i i' hii' _ p hp q hq
    obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨j', -, hq⟩ := List.mem_flatMap.mp hq
    exact cell i j i' j' (rowMajor_lt (List.mem_range.mp hj) hii') p hp q hq

sv_cycle mmG using mmG_disj N W AccW

/-! ## 2. Arithmetic and timetable packing -/

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
    have h1 : i * N + j < N * N := by
      have := rowMajor_le (K := N) hi; omega
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
    have h1 : i * N + j < N * N := by
      have := rowMajor_le (K := N) hi; omega
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

theorem g_time_wordQ_eq_nil (N W AccW i j t : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    mmG.g_time_wordQ N W AccW i j t ck r s a b dn c k bz at_ bt_ as_ bs_ = [] := rfl

theorem g_time_word_1Q_eq_nil (N W AccW i j t : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    mmG.g_time_word_1Q N W AccW i j t ck r s a b dn c k bz at_ bt_ as_ bs_ = [] := rfl

def cellsQ (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_time_colQ N W AccW i j ck r s a b dn c k bz at_ bt_ as_ bs_

theorem edgeQ_eq (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    mmG.edgeQ N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ =
      mmG.p0Q N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ ++
        cellsQ N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ := by
  have hnil : ∀ l : List Nat, (l.flatMap fun _ => ([] : NbaQueue2)) = [] := by
    intro l; induction l <;> simp [*]
  simp [mmG.edgeQ, cellsQ, g_time_wordQ_eq_nil, g_time_word_1Q_eq_nil, hnil]

theorem p0Q_names (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    ∀ u ∈ mmG.p0Q N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_,
      u.1 ∈ ["busy", "done", "k", "a_stream", "b_stream"] := by
  intro u hu
  unfold mmG.p0Q at hu
  split at hu
  · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · split at hu
        · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
        · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
      · simp at hu

theorem cellsQ_names (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    ∀ u ∈ cellsQ N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_, u.1 ∈ ["C"] := by
  intro u hu
  simp only [cellsQ, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  unfold mmG.g_time_colQ at hu
  split at hu
  · simp at hu; subst hu; simp
  · split at hu
    · simp at hu; subst hu; simp
    · split at hu
      · simp at hu; subst hu; simp
      · simp at hu

theorem edgeQ_names (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    ∀ u ∈ mmG.edgeQ N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_,
      u.1 ∈ ["busy", "done", "k", "a_stream", "b_stream", "C"] := by
  rw [edgeQ_eq]
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · have := p0Q_names N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ u hu
    simp at this ⊢
    rcases this with h | h | h | h | h <;> simp [h]
  · have := cellsQ_names N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ u hu
    simp at this ⊢; simp [this]

theorem mmG_next_eq (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec) :
    let at1 := mmG.comb_a_timetable N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_
    let bt1 := mmG.comb_b_timetable N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_
    let pQ := mmG.p0Q N W AccW ck r s a b dn c k bz at1 bt1 as_ bs_
    let cQ := cellsQ N W AccW ck r s a b dn c k bz at1 bt1 as_ bs_
    mmG.next N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_ =
      mmG.comb N W AccW ck r s a b
        (nbaFold "done" pQ dn) (nbaFold "C" cQ c) (nbaFold "k" pQ k) (nbaFold "busy" pQ bz)
        at1 bt1 (nbaFold "a_stream" pQ as_) (nbaFold "b_stream" pQ bs_) := by
  dsimp only [mmG.next]
  let at1 := mmG.comb_a_timetable N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_
  let bt1 := mmG.comb_b_timetable N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_
  have he := edgeQ_names N W AccW ck r s a b dn c k bz at1 bt1 as_ bs_
  have hp := p0Q_names N W AccW ck r s a b dn c k bz at1 bt1 as_ bs_
  have hc := cellsQ_names N W AccW ck r s a b dn c k bz at1 bt1 as_ bs_
  rw [nbaFold_of_names he (by decide : "clk" ∉ _),
      nbaFold_of_names he (by decide : "rst" ∉ _),
      nbaFold_of_names he (by decide : "start" ∉ _),
      nbaFold_of_names he (by decide : "A" ∉ _),
      nbaFold_of_names he (by decide : "B" ∉ _),
      nbaFold_of_names he (by decide : "a_timetable" ∉ _),
      nbaFold_of_names he (by decide : "b_timetable" ∉ _)]
  simp only [edgeQ_eq, nbaFold_append]
  rw [nbaFold_of_names hc (by decide : "done" ∉ _),
      nbaFold_of_names hc (by decide : "k" ∉ _),
      nbaFold_of_names hc (by decide : "busy" ∉ _),
      nbaFold_of_names hc (by decide : "a_stream" ∉ _),
      nbaFold_of_names hc (by decide : "b_stream" ∉ _),
      nbaFold_of_names hp (by decide : "C" ∉ _)]

theorem comb_a_timetable_known {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (Av : BitVec (N * N * W)) (ck r s b dn c k bz at_ bt_ as_ bs_ : LVec)
    (hat : at_.width = N * N * N * W) :
    mmG.comb_a_timetable N W AccW ck r s (LVec.ofBitVec Av) b dn c k bz at_ bt_ as_ bs_ =
      LVec.ofBitVec (ttA N W Av) := by
  refine LVec.eq_ofBitVec_packBV (by simp [mmG.comb_a_timetable, hat]) fun q hq => ?_
  have hqN : q / N < N * N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hi : q / N / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hqN
  have hj : q / N % N < N := Nat.mod_lt _ (by omega)
  have ht : q % N < N := Nat.mod_lt _ (by omega)
  have h1 : q / N / N * N + q / N % N = q / N := by rw [Nat.mul_comm]; exact Nat.div_add_mod (q / N) N
  have h2 : (q / N / N * N + q / N % N) * N + q % N = q := by
    rw [h1, Nat.mul_comm]; exact Nat.div_add_mod q N
  have hm : ("a_timetable", q * W, ((LVec.ofBitVec Av).extract ((q / N / N * N + q % N) * W) W).resizeU W) ∈
      mmG.combQ N W AccW ck r s (LVec.ofBitVec Av) b dn c k bz at_ bt_ as_ bs_ := by
    simp only [mmG.combQ, mmG.g_time_wordC, mmG.g_time_word_1C, List.mem_flatMap, List.mem_range,
      List.mem_append, List.mem_singleton]
    exact ⟨q / N / N, hi, q / N % N, hj, q % N, ht, Or.inl (by rw [h2])⟩
  have hbound : q * W + (((LVec.ofBitVec Av).extract ((q / N / N * N + q % N) * W) W).resizeU W).width ≤ at_.width := by
    rw [LVec.width_resizeU, hat]
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq)
    rwa [Nat.succ_mul] at this
  have hex := SvGolf.Cycle.extract_nbaFold_of_mem
    (mmG.combQ_disj N W AccW hN hW hA hN32 hW32 hA32 ck r s (LVec.ofBitVec Av) b dn c k bz at_ bt_ as_ bs_)
    hm hbound
  rw [LVec.width_resizeU] at hex
  change (nbaFold "a_timetable" _ at_).extract (q * W) W = _
  rw [hex, LVec.extract_ofBitVec Av (Lib.rowMajor_window_le hi ht), LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem comb_b_timetable_known {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (Bv : BitVec (N * N * W)) (ck r s a dn c k bz at_ bt_ as_ bs_ : LVec)
    (hbt : bt_.width = N * N * N * W) :
    mmG.comb_b_timetable N W AccW ck r s a (LVec.ofBitVec Bv) dn c k bz at_ bt_ as_ bs_ =
      LVec.ofBitVec (ttB N W Bv) := by
  refine LVec.eq_ofBitVec_packBV (by simp [mmG.comb_b_timetable, hbt]) fun q hq => ?_
  have hqN : q / N < N * N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
  have hi : q / N / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hqN
  have hj : q / N % N < N := Nat.mod_lt _ (by omega)
  have ht : q % N < N := Nat.mod_lt _ (by omega)
  have h1 : q / N / N * N + q / N % N = q / N := by rw [Nat.mul_comm]; exact Nat.div_add_mod (q / N) N
  have h2 : (q / N / N * N + q / N % N) * N + q % N = q := by
    rw [h1, Nat.mul_comm]; exact Nat.div_add_mod q N
  have hm : ("b_timetable", q * W, ((LVec.ofBitVec Bv).extract ((q % N * N + q / N % N) * W) W).resizeU W) ∈
      mmG.combQ N W AccW ck r s a (LVec.ofBitVec Bv) dn c k bz at_ bt_ as_ bs_ := by
    simp only [mmG.combQ, mmG.g_time_wordC, mmG.g_time_word_1C, List.mem_flatMap, List.mem_range,
      List.mem_append, List.mem_singleton]
    exact ⟨q / N / N, hi, q / N % N, hj, q % N, ht, Or.inr (by rw [h2])⟩
  have hbound : q * W + (((LVec.ofBitVec Bv).extract ((q % N * N + q / N % N) * W) W).resizeU W).width ≤ bt_.width := by
    rw [LVec.width_resizeU, hbt]
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq)
    rwa [Nat.succ_mul] at this
  have hex := SvGolf.Cycle.extract_nbaFold_of_mem
    (mmG.combQ_disj N W AccW hN hW hA hN32 hW32 hA32 ck r s a (LVec.ofBitVec Bv) dn c k bz at_ bt_ as_ bs_)
    hm hbound
  rw [LVec.width_resizeU] at hex
  change (nbaFold "b_timetable" _ bt_).extract (q * W) W = _
  rw [hex, LVec.extract_ofBitVec Bv (Lib.rowMajor_window_le ht hj), LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

/-! ## 4. Shape and one-cycle transitions -/

def Wd (N W AccW : Nat) (dn c k bz at_ bt_ as_ bs_ : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  at_.width = N * N * N * W ∧ bt_.width = N * N * N * W ∧
  as_.width = N * N * N * W ∧ bs_.width = N * N * N * W

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz at_ bt_ as_ bs_,
    st = mmG.St ck r s a b dn c k bz at_ bt_ as_ bs_ ∧ Wd N W AccW dn c k bz at_ bt_ as_ bs_

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mmG.init N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd]⟩

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz at_ bt_ as_ bs_ : LVec)
    (hw : Wd N W AccW dn c k bz at_ bt_ as_ bs_) :
    I N W AccW (mmG.next N W AccW ck r s a b dn c k bz at_ bt_ as_ bs_) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [Wd, mmG.comb_a_timetable, mmG.comb_b_timetable, h1, h2, h3, h4, h5, h6, h7, h8]

def Ready (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c k at_ bt_ as_ bs_,
    st = mmG.St ck r s a b (knownBit false) c k (knownBit false) at_ bt_ as_ bs_ ∧
    c.width = N * N * AccW ∧ k.width = 32 ∧
    at_.width = N * N * N * W ∧ bt_.width = N * N * N * W ∧
    as_.width = N * N * N * W ∧ bs_.width = N * N * N * W

def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b at_ bt_,
    st = mmG.St ck r s a b (knownBit false) (accC N W AccW A B t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at_ bt_
      (LVec.ofBitVec (ttA N W A >>> (t * W))) (LVec.ofBitVec (ttB N W B >>> (t * W))) ∧
    at_.width = N * N * N * W ∧ bt_.width = N * N * N * W

def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k at_ bt_ as_ bs_,
    st = mmG.St ck r s a b (knownBit true)
      (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k (knownBit false) at_ bt_ as_ bs_ ∧
    k.width = 32 ∧ at_.width = N * N * N * W ∧ bt_.width = N * N * N * W ∧
    as_.width = N * N * N * W ∧ bs_.width = N * N * N * W

theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz at_ bt_ as_ bs_ : LVec)
    (hw : Wd N W AccW dn c k bz at_ bt_ as_ bs_) :
    Ready N W AccW (mmG.next N W AccW ck (knownBit true) s a b dn c k bz at_ bt_ as_ bs_) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz
      (mmG.comb_a_timetable N W AccW ck (knownBit true) s a b dn c k bz at_ bt_ as_ bs_)
      (mmG.comb_b_timetable N W AccW ck (knownBit true) s a b dn c k bz at_ bt_ as_ bs_) as_ bs_) dn =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz
      (mmG.comb_a_timetable N W AccW ck (knownBit true) s a b dn c k bz at_ bt_ as_ bs_)
      (mmG.comb_b_timetable N W AccW ck (knownBit true) s a b dn c k bz at_ bt_ as_ bs_) as_ bs_) bz =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [hd, hb]
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, by simp [h2], by simp [h3],
    by simp [mmG.comb_a_timetable, h5], by simp [mmG.comb_b_timetable, h6], by simp [h7], by simp [h8]⟩

theorem next_idle {N W AccW : Nat} (ck a b dn c k at_ bt_ as_ bs_ : LVec) :
    ∃ at' bt',
      mmG.next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at_ bt_ as_ bs_ =
        mmG.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at' bt' as_ bs_ ∧
      at'.width = at_.width ∧ bt'.width = bt_.width := by
  rw [mmG_next_eq]
  have hp : mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      (mmG.comb_a_timetable N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at_ bt_ as_ bs_)
      (mmG.comb_b_timetable N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at_ bt_ as_ bs_)
      as_ bs_ = [] := by
    simp [mmG.p0Q]
  have hc : cellsQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false)
      (mmG.comb_a_timetable N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at_ bt_ as_ bs_)
      (mmG.comb_b_timetable N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) at_ bt_ as_ bs_)
      as_ bs_ = [] := by
    simp [cellsQ, mmG.g_time_colQ]
  rw [hp, hc]
  exact ⟨_, _, rfl, by simp [mmG.comb_a_timetable], by simp [mmG.comb_b_timetable]⟩

theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (Av Bv : BitVec (N * N * W)) (ck dn c k bz at_ bt_ as_ bs_ : LVec)
    (hw : Wd N W AccW dn c k bz at_ bt_ as_ bs_) :
    BusyAt N W AccW Av Bv 0
      (mmG.next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn c k bz at_ bt_ as_ bs_) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  rw [mmG_next_eq]
  rw [comb_a_timetable_known hN hW hA hN32 hW32 hA32 Av _ _ _ _ _ _ _ _ _ _ _ _ h5,
      comb_b_timetable_known hN hW hA hN32 hW32 hA32 Bv _ _ _ _ _ _ _ _ _ _ _ _ h6]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) dn = knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) bz = knownBit true := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l1]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  have hk : nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) k = LVec.ofBitVec (BitVec.ofNat 32 0) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h3, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h3])
  have has : nbaFold "a_stream" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) as_ = LVec.ofBitVec (ttA N W Av) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h7, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h7])
  have hbs : nbaFold "b_stream" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) bs_ = LVec.ofBitVec (ttB N W Bv) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h8, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h8])
  have hc : nbaFold "C" (cellsQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
      (LVec.ofBitVec (ttB N W Bv)) as_ bs_) c = accC N W AccW Av Bv 0 := by
    have hq : cellsQ N W AccW ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz (LVec.ofBitVec (ttA N W Av))
        (LVec.ofBitVec (ttB N W Bv)) as_ bs_ =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 0 (r / N) (r % N)))) := by
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp [mmG.g_time_colQ, psum, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h2]; rfl
  rw [hd, hb, hk, has, hbs, hc]
  unfold mmG.comb BusyAt
  simp only [Nat.zero_mul, BitVec.ushiftRight_zero]
  refine ⟨_, _, _, _, _, _, _, rfl, by simp [mmG.comb_a_timetable], by simp [mmG.comb_b_timetable]⟩

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
    have hq : (i * N + j) * N < N * N * N := by
      have := rowMajor_le (K := N) h1; omega
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
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b at_ bt_ : LVec)
    (hat : at_.width = N * N * N * W) (hbt : bt_.width = N * N * N * W) :
    ∃ at' bt',
      mmG.next N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
          (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at_ bt_
          (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) =
        mmG.St ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N)))
          (accC N W AccW Av Bv (t + 1)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
          (knownBit (decide (t + 1 ≠ N))) at' bt'
          (LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W))) (LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W))) ∧
      at'.width = N * N * N * W ∧ bt'.width = N * N * N * W := by
  have hW_toNat : (BitVec.ofNat 32 W).toNat = W := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [mmG_next_eq]
  let at1 := mmG.comb_a_timetable N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
    (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at_ bt_
    (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W)))
  let bt1 := mmG.comb_b_timetable N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
    (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at_ bt_
    (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W)))
  have hc : nbaFold "C" (cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
      (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
      (accC N W AccW Av Bv t) = accC N W AccW Av Bv (t + 1) := by
    have hq : cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))) =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) (r / N) (r % N)))) := by
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp only [mmG.g_time_colQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
        cell_acc_step hW Av Bv hi hj ht, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (accC_width ..)]; rfl
  have hctrl :
      nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
        (knownBit false) = knownBit (decide (t + 1 = N)) ∧
      nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
        (LVec.ofBitVec (BitVec.ofNat 32 t)) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
      nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
        (knownBit true) = knownBit (decide (t + 1 ≠ N)) ∧
      nbaFold "a_stream" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) = LVec.ofBitVec (ttA N W Av >>> ((t + 1) * W)) ∧
      nbaFold "b_stream" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) at1 bt1
        (LVec.ofBitVec (ttA N W Av >>> (t * W))) (LVec.ofBitVec (ttB N W Bv >>> (t * W))))
        (LVec.ofBitVec (ttB N W Bv >>> (t * W))) = LVec.ofBitVec (ttB N W Bv >>> ((t + 1) * W)) := by
    simp only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
      BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec,
      LVec.ofLogic_ofBool, decide_eq_true_eq,
      Lib.ofNat_eq_ofNat_sub_one_iff ht (by omega : N ≤ 2 ^ 32),
      LVec.width_ofBitVec, LVec.add_ofBitVec, LVec.shr_ofBitVec, hW_toNat,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, shiftRight_shiftRight, ← Nat.succ_mul]
    by_cases hf : t + 1 = N <;>
      simp [hf, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
        BitVec.ofNat_add_ofNat]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hctrl
  change ∃ at' bt', mmG.comb _ _ _ _ _ _ _ _ (nbaFold "done" _ _) (nbaFold "C" _ _) (nbaFold "k" _ _)
    (nbaFold "busy" _ _) at1 bt1 (nbaFold "a_stream" _ _) (nbaFold "b_stream" _ _) = _ ∧ _
  rw [hc, h1, h2, h3, h4, h5]
  refine ⟨_, _, rfl, by simp [mmG.comb_a_timetable, at1, hat], by simp [mmG.comb_b_timetable, bt1, hbt]⟩

/-! ## 5. Phase model -/

theorem St_inj {ck r s a b dn c k bz at_ bt_ as_ bs_ ck' r' s' a' b' dn' c' k' bz' at' bt' as' bs' : LVec}
    (h : mmG.St ck r s a b dn c k bz at_ bt_ as_ bs_ =
      mmG.St ck' r' s' a' b' dn' c' k' bz' at' bt' as' bs') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ at_ = at' ∧ bt_ = bt' ∧ as_ = as' ∧ bs_ = bs' := by
  simp only [mmG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz at_ bt_ as_ bs_,
    prev = mmG.St ck r s a b dn c k bz at_ bt_ as_ bs_ ∧
    Wd N W AccW dn c k bz at_ bt_ as_ bs_ ∧
    st = mmG.next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz at_ bt_ as_ bs_

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
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, at_, bt_, as_, bs_, rfl, hw⟩ hc
    obtain ⟨kk', hnext⟩ := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c kk bz at_ bt_ as_ bs_ k 32 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, at_, bt_, as_, bs_, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz at_ bt_ as_ bs_ hw
  Ready := Ready N W AccW
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, at_, bt_, as_, bs_, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, at_, bt_, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, at_, bt_, as_, bs_, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmG.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset _ _ _ _ dn c k bz at_ bt_ as_ bs_ hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N - 1, by omega, 0, by omega,
      next_start hN hW hA hN32 hW32 hA32 _ _ _ dn c k bz at_ bt_ as_ bs_ hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', at', bt', hb, hat, hbt⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨at1, bt1, hstep, hat1, hbt1⟩ :=
      next_step (AccW := AccW) hN hW hN32 hW32 x.1 x.2.1 (t := t) (by omega)
        (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) at_ bt_ hat hbt
    rw [hstep]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp, hat1, hbt1, by simp, by simp⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, _, _, rfl, hat1, hbt1⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', at', bt', as', bs', hb, h2, h3, h5, h6, h7, h8⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨at1, bt1, hidle, hat1, hbt1⟩ :=
      next_idle (N := N) (W := W) (AccW := AccW) (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
        (knownBit false) c k at_ bt_ as_ bs_
    rw [hidle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, h2, h3, hat1.trans h5, hbt1.trans h6, h7, h8⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', at', bt', as', bs', hb, h3, h5, h6, h7, h8⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    obtain ⟨at1, bt1, hidle, hat1, hbt1⟩ :=
      next_idle (N := N) (W := W) (AccW := AccW) (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
        (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) k at_ bt_ as_ bs_
    rw [hidle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, h3, hat1.trans h5, hbt1.trans h6, h7, h8⟩

/-! ## 6. Interface, discipline, and the three v2 rules -/

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmG.D N W AccW).processes.toList) :
    p = mmG.p0 N W AccW ∨
      (∃ i j t, i < N ∧ j < N ∧ t < N ∧
        (p = mmG.g_time_word N W AccW i j t ∨ p = mmG.g_time_word_1 N W AccW i j t)) ∨
      (∃ i j, i < N ∧ j < N ∧ p = mmG.g_time_col N W AccW i j) := by
  simp only [mmG.D, List.toList_toArray, mmG.procs, List.mem_cons, List.mem_flatMap, List.mem_append,
    List.mem_range, List.singleton_append, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | ⟨i, hi, j, hj, ⟨t, ht, rfl | rfl⟩ | rfl⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨i, j, t, hi, hj, ht, .inl rfl⟩)
  · exact .inr (.inl ⟨i, j, t, hi, hj, ht, .inr rfl⟩)
  · exact .inr (.inr ⟨i, j, hi, hj, rfl⟩)

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "a_timetable", "b_timetable", "a_stream", "b_stream"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmG.D, mmG.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_proc_mem hp with rfl | ⟨i, j, t, -, -, -, rfl | rfl⟩ | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmG.p0, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_time_word, edgeClock, asyncReset, processDataNames,
      lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.g_time_word_1, edgeClock, asyncReset, processDataNames,
      lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.g_time_col, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

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
    rcases mm_proc_mem hp with rfl | ⟨i, j, t, -, -, -, rfl | rfl⟩ | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, processDeps] at he
    · simp [mmG.g_time_word, processDeps, lhsTargets] at he; simp [he]
    · simp [mmG.g_time_word_1, processDeps, lhsTargets] at he; simp [he]
    · simp [mmG.g_time_col, processDeps] at he
  · intro o ho
    simp [mmG.D, mmG.decls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> simp

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl,
    -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    mmG.powerUp N W AccW hN hW hA hN32 hW32 hA32 st h
  exact ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem mm_noq (N W AccW : Nat) :
    (mmG.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mm_proc_mem hp with rfl | ⟨i, j, t, -, -, -, rfl | rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    simp [mmG.p0, mmG.g_time_word, mmG.g_time_word_1, mmG.g_time_col,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32) (fun σ => ⟨32, ?_⟩)
    (by rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, at_, bt_, as_, bs_, rfl, hw⟩
  obtain ⟨kk', hnext⟩ := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
    ck r s a b dn c k bz at_ bt_ as_ bs_ kk 32 (Nat.le_refl _)
  exact ⟨_, _, hnext, mmNext_I N W AccW _ _ _ _ _ dn c k bz at_ bt_ as_ bs_ hw⟩

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mm_proc_mem hp with rfl | ⟨i, j, t, hi, hj, ht, rfl | rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmG.p0, mmG.D, mmG.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hA' : (i * N + t) * W + W ≤ N * N * W := Lib.rowMajor_window_le hi ht
    simp [xsProc, xsLhs, xsWidth, sigWidth, mmG.g_time_word, mmG.D, mmG.decls, hA']
  · have hB' : (t * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le ht hj
    simp [xsProc, xsLhs, xsWidth, sigWidth, mmG.g_time_word_1, mmG.D, mmG.decls, hB']
  · have hC : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
    have hS : (i * N + j) * N * W + W ≤ N * N * N * W := by
      have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
      have hq : (i * N + j) * N < N * N * N := by have := rowMajor_le (K := N) h1; omega
      have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hq); rwa [Nat.succ_mul] at this
    have hS1 : (i * N + j) * N * W + W - 1 + 1 ≤ N * N * N * W := by omega
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_time_col, mmG.D, mmG.decls, LVec.allKnown_ofBitVec, hC, hS, hS1]

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
