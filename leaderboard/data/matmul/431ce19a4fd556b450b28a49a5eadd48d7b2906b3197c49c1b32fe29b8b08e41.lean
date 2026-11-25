-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Mirror, disjointness, and generated clock cycle -/

sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem mmG_disj (N W AccW : Nat) : (mmG.procs N W AccW).Pairwise ProcDisj := by
  have sepW : ∀ q q', q < q' → q * W + W ≤ q' * W := fun q q' h => by
    have := Nat.mul_le_mul_right W (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  have sepA : ∀ q q', q < q' → q * AccW + AccW ≤ q' * AccW := fun q q' h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  unfold mmG.procs
  refine List.Pairwise.cons (fun q hq => ?_) ?_
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨i, -, j, -, rfl⟩ := hq
    exact ProcDisj.of_all (by simp [mmG.p0, mmG.g_core, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · exact pairwise_rowMajor fun i j i' j' _ _ _ _ h => by
      have hW := sepW (i * N + j) (i' * N + j') h
      have hA := sepA (i * N + j) (i' * N + j') h
      exact ProcDisj.of_all (by simp [mmG.g_core, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)

sv_cycle mmG using mmG_disj N W AccW

/-! ## 2. Arithmetic and packing -/

def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r =>
    BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

def wRow (N W : Nat) (B : BitVec (N * N * W)) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV W (N * N) fun r =>
    (B >>> (t * (N * W))).extractLsb' ((r % N) * W) W)

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

theorem wRow_width (N W : Nat) (B : BitVec (N * N * W)) (t : Nat) :
    (wRow N W B t).width = N * N * W := by
  simp [wRow]

theorem wRow_extract {N W : Nat} (B : BitVec (N * N * W)) {i j t : Nat}
    (hi : i < N) (hj : j < N) :
    (wRow N W B t).extract ((i * N + j) * W) W =
      LVec.ofBitVec (B.extractLsb' ((t * N + j) * W) W) := by
  have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
  have hidx : t * (N * W) + j * W = (t * N + j) * W := by
    rw [← Nat.mul_assoc, ← Nat.add_mul]
  rw [wRow, extract_ofBitVec_packBV _ h1 rfl, Nat.mul_add_mod_of_lt hj,
    Lib.extractLsb'_ushiftRight, hidx]

theorem shiftRight_shiftRight {w : Nat} (x : BitVec w) (a b : Nat) :
    (x >>> a) >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1; omega

/-! ## 3. Helpers on `nbaFold` and `mmG.next` -/

@[simp] theorem nbaFold_width (n : String) : ∀ (q : NbaQueue2) (x : LVec),
    (nbaFold n q x).width = x.width
  | [], _ => rfl
  | u :: q, x => by
    rw [nbaFold_cons, nbaFold_width n q]
    split <;> simp

theorem nbaFold_append (n : String) (q₁ q₂ : NbaQueue2) (x : LVec) :
    nbaFold n (q₁ ++ q₂) x = nbaFold n q₂ (nbaFold n q₁ x) := by
  simp [nbaFold, List.foldl_append]

theorem nbaFold_eq_filter (n : String) : ∀ (q : NbaQueue2) (x : LVec),
    nbaFold n q x = nbaFold n (q.filter fun u => u.1 == n) x
  | [], _ => rfl
  | (m, off, v) :: q, x => by
    by_cases h : m = n
    · subst h; simp [nbaFold_cons_self, nbaFold_eq_filter m q]
    · have hne : (m == n) = false := beq_false_of_ne h
      simp [nbaFold_cons, h, hne, nbaFold_eq_filter n q]

def cellsQ (N W AccW : Nat) (ck r s a b dn c k bz ash bnx wc : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_coreQ N W AccW i j ck r s a b dn c k bz ash bnx wc

theorem p0Q_names (N W AccW : Nat) (ck r s a b dn c k bz ash bnx wc : LVec) :
    ∀ u ∈ mmG.p0Q N W AccW ck r s a b dn c k bz ash bnx wc,
      u.1 ∈ ["busy", "done", "k", "a_sh", "b_next"] := by
  intro u hu
  unfold mmG.p0Q at hu
  split at hu
  · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · split at hu
        · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
        · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
      · simp at hu

theorem cellsQ_names (N W AccW : Nat) (ck r s a b dn c k bz ash bnx wc : LVec) :
    ∀ u ∈ cellsQ N W AccW ck r s a b dn c k bz ash bnx wc,
      u.1 ∈ ["w_cur", "C"] := by
  intro u hu
  simp only [cellsQ, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  unfold mmG.g_coreQ at hu
  split at hu
  · simp at hu; subst hu; simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl <;> simp
    · split at hu
      · simp at hu; rcases hu with rfl | rfl <;> simp
      · simp at hu

theorem mmG_next_eq (N W AccW : Nat) (ck r s a b dn c k bz ash bnx wc : LVec) :
    let pQ := mmG.p0Q N W AccW ck r s a b dn c k bz ash bnx wc
    let cQ := cellsQ N W AccW ck r s a b dn c k bz ash bnx wc
    mmG.next N W AccW ck r s a b dn c k bz ash bnx wc =
      mmG.St ck r s a b
        (nbaFold "done" pQ dn) (nbaFold "C" cQ c) (nbaFold "k" pQ k) (nbaFold "busy" pQ bz)
        (nbaFold "a_sh" pQ ash) (nbaFold "b_next" pQ bnx) (nbaFold "w_cur" cQ wc) := by
  dsimp only [mmG.next]
  have hp := p0Q_names N W AccW ck r s a b dn c k bz ash bnx wc
  have hc := cellsQ_names N W AccW ck r s a b dn c k bz ash bnx wc
  change commitNba2 (mmG.St ck r s a b dn c k bz ash bnx wc)
      (mmG.p0Q N W AccW ck r s a b dn c k bz ash bnx wc ++
       cellsQ N W AccW ck r s a b dn c k bz ash bnx wc) = _
  rw [commitNba2_eq_map _ _ (by simp [mmG.St])]
  simp only [mmG.St, List.map_cons, List.map_nil, nbaFold_append]
  rw [nbaFold_of_names hp (by decide : "clk" ∉ _), nbaFold_of_names hc (by decide : "clk" ∉ _),
      nbaFold_of_names hp (by decide : "rst" ∉ _), nbaFold_of_names hc (by decide : "rst" ∉ _),
      nbaFold_of_names hp (by decide : "start" ∉ _), nbaFold_of_names hc (by decide : "start" ∉ _),
      nbaFold_of_names hp (by decide : "A" ∉ _), nbaFold_of_names hc (by decide : "A" ∉ _),
      nbaFold_of_names hp (by decide : "B" ∉ _), nbaFold_of_names hc (by decide : "B" ∉ _),
      nbaFold_of_names hc (by decide : "done" ∉ _),
      nbaFold_of_names hp (by decide : "C" ∉ _),
      nbaFold_of_names hc (by decide : "k" ∉ _),
      nbaFold_of_names hc (by decide : "busy" ∉ _),
      nbaFold_of_names hc (by decide : "a_sh" ∉ _),
      nbaFold_of_names hc (by decide : "b_next" ∉ _),
      nbaFold_of_names hp (by decide : "w_cur" ∉ _)]

/-! ## 4. Shape and one-cycle transitions -/

def Wd (N W AccW : Nat) (dn c k bz ash bnx wc : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  ash.width = N * N * W ∧ bnx.width = N * N * W ∧ wc.width = N * N * W

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bnx wc,
    st = mmG.St ck r s a b dn c k bz ash bnx wc ∧ Wd N W AccW dn c k bz ash bnx wc

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mmG.init N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd]⟩

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz ash bnx wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bnx wc) :
    I N W AccW (mmG.next N W AccW ck r s a b dn c k bz ash bnx wc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  rw [mmG_next_eq]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, h1, h2, h3, h4, h5, h6, h7]⟩

def Ready (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c k ash bnx wc,
    st = mmG.St ck r s a b (knownBit false) c k (knownBit false) ash bnx wc ∧
    c.width = N * N * AccW ∧ k.width = 32 ∧
    ash.width = N * N * W ∧ bnx.width = N * N * W ∧ wc.width = N * N * W

def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b,
    st = mmG.St ck r s a b (knownBit false) (accC N W AccW A B t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (A >>> (t * W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W))))
      (wRow N W B t)

def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k ash bnx wc,
    st = mmG.St ck r s a b (knownBit true)
      (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k (knownBit false) ash bnx wc ∧
    k.width = 32 ∧ ash.width = N * N * W ∧ bnx.width = N * N * W ∧ wc.width = N * N * W

theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz ash bnx wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bnx wc) :
    Ready N W AccW (mmG.next N W AccW ck (knownBit true) s a b dn c k bz ash bnx wc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz ash bnx wc) dn =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz ash bnx wc) bz =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [hd, hb]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp [h2], by simp [h3],
    by simp [h5], by simp [h6], by simp [h7]⟩

theorem next_idle {N W AccW : Nat} (ck a b dn c k ash bnx wc : LVec) :
    mmG.next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bnx wc =
      mmG.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bnx wc := by
  rw [mmG_next_eq]
  have hp : mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bnx wc = [] := by
    simp [mmG.p0Q]
  have hc : cellsQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) ash bnx wc = [] := by
    simp [cellsQ, mmG.g_coreQ]
  rw [hp, hc]; rfl

theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW32 : N * W < 2 ^ 32)
    (Av Bv : BitVec (N * N * W)) (ck dn c k bz ash bnx wc : LVec)
    (hw : Wd N W AccW dn c k bz ash bnx wc) :
    BusyAt N W AccW Av Bv 0
      (mmG.next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn c k bz ash bnx wc) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW32
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW32
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW',
      Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW32]
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) dn = knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) bz = knownBit true := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l1]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  have hk : nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) k =
      LVec.ofBitVec (BitVec.ofNat 32 0) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h3, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h3])
  have hash : nbaFold "a_sh" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) ash =
      LVec.ofBitVec (Av >>> (0 * W)) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h5, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
      Nat.zero_mul, BitVec.ushiftRight_zero]
    exact LVec.insertAt_zero_of_width_eq (by simp [h5])
  have hbnx : nbaFold "b_next" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) bnx =
      LVec.ofBitVec (Bv >>> ((0 + 1) * (N * W))) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h6, LVec.ofInt_eq_ofBitVec,
      BitVec.ofInt_natCast, LVec.mul_ofBitVec, LVec.shr_ofBitVec, hyNW,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, Nat.zero_add, Nat.one_mul]
    exact LVec.insertAt_zero_of_width_eq (by simp [h6])
  have hwc : nbaFold "w_cur" (cellsQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) wc = wRow N W Bv 0 := by
    rw [nbaFold_eq_filter]
    have hq : (cellsQ N W AccW ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc).filter (fun u => u.1 == "w_cur") =
      (List.range (N * N)).map fun r =>
        ("w_cur", r * W, LVec.ofBitVec ((Bv >>> (0 * (N * W))).extractLsb' ((r % N) * W) W)) := by
      simp only [cellsQ, List.filter_flatMap]
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      have hB' : j * W + W ≤ N * N * W := by
        simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
      simp [mmG.g_coreQ, LVec.extract_ofBitVec Bv hB', LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
        Nat.mul_add_mod_of_lt hj]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h7]; rfl
  have hc : nbaFold "C" (cellsQ N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc) c = accC N W AccW Av Bv 0 := by
    rw [nbaFold_eq_filter]
    have hq : (cellsQ N W AccW ck (knownBit false) (knownBit true)
        (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz ash bnx wc).filter (fun u => u.1 == "C") =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 0 (r / N) (r % N)))) := by
      simp only [cellsQ, List.filter_flatMap]
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp [mmG.g_coreQ, psum, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h2]; rfl
  rw [hd, hb, hk, hash, hbnx, hwc, hc]
  exact ⟨_, _, _, _, _, rfl⟩

theorem cell_acc_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {t i j : Nat} (hi : i < N) (hj : j < N) :
    let ash := LVec.ofBitVec (Av >>> (t * W))
    let wc := wRow N W Bv t
    let c := accC N W AccW Av Bv t
    ((((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        ((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[ash.extract (i * N * W + W - 1) 1]),
            ash.extract (i * N * W) W]).mul
          (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[wc.extract ((i * N + j) * W + W - 1) 1]),
            wc.extract ((i * N + j) * W) W]))).resizeU AccW).resizeU AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) i j)) := by
  dsimp only
  have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
  have hA' : i * N * W + W ≤ N * N * W := by
    simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
  have hexC : (accC N W AccW Av Bv t).extract ((i * N + j) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv t i j)) := by
    rw [accC, extract_ofBitVec_packBV _ h1 rfl, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
  have hexA : (LVec.ofBitVec (Av >>> (t * W))).extract (i * N * W) W =
      LVec.ofBitVec (Av.extractLsb' ((i * N + t) * W) W) := by
    have hidx : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_comm, ← Nat.add_mul]
    rw [LVec.extract_ofBitVec _ hA', Lib.extractLsb'_ushiftRight, hidx]
  have hexW : (wRow N W Bv t).extract ((i * N + j) * W) W =
      LVec.ofBitVec (Bv.extractLsb' ((t * N + j) * W) W) := wRow_extract Bv hi hj
  rw [hexC, LVec.sext_of_extract hW hexA, LVec.sext_of_extract hW hexW,
    LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec,
    LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend (by omega : AccW ≤ AccW + W),
    ← BitVec.ofInt_add, psum_succ]
  rfl

theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW32 : N * W < 2 ^ 32)
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b : LVec) :
    mmG.next N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W)))
        (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W))))
        (wRow N W Bv t) =
      mmG.St ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N)))
        (accC N W AccW Av Bv (t + 1)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
        (knownBit (decide (t + 1 ≠ N)))
        (LVec.ofBitVec (Av >>> ((t + 1) * W)))
        (LVec.ofBitVec (Bv >>> ((t + 2) * (N * W))))
        (wRow N W Bv (t + 1)) := by
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW32
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW32
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW',
      Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW32]
  rw [mmG_next_eq]
  have hwc : nbaFold "w_cur" (cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
      (wRow N W Bv t) = wRow N W Bv (t + 1) := by
    rw [nbaFold_eq_filter]
    have hq : (cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t)).filter
          (fun u => u.1 == "w_cur") =
      (List.range (N * N)).map fun r =>
        ("w_cur", r * W, LVec.ofBitVec ((Bv >>> ((t + 1) * (N * W))).extractLsb' ((r % N) * W) W)) := by
      simp only [cellsQ, List.filter_flatMap]
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      have hB' : j * W + W ≤ N * N * W := by
        simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
      simp [mmG.g_coreQ, LVec.extract_ofBitVec _ hB', LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
        Nat.mul_add_mod_of_lt hj]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (wRow_width ..)]; rfl
  have hc : nbaFold "C" (cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
      (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
      (accC N W AccW Av Bv t) = accC N W AccW Av Bv (t + 1) := by
    rw [nbaFold_eq_filter]
    have hq : (cellsQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t)).filter
          (fun u => u.1 == "C") =
      (List.range (N * N)).map fun r =>
        ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) (r / N) (r % N)))) := by
      simp only [cellsQ, List.filter_flatMap]
      refine flatMap_range_rowMajor _ fun i j hi hj => ?_
      simp only [mmG.g_coreQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
        List.filter_cons, beq_self_eq_true, show ("w_cur" == "C") = false from by decide,
        Bool.false_eq_true, List.filter_nil,
        cell_acc_step hN hW Av Bv hi hj, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
    rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (accC_width ..)]; rfl
  have hctrl :
      nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
        (knownBit false) = knownBit (decide (t + 1 = N)) ∧
      nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
        (LVec.ofBitVec (BitVec.ofNat 32 t)) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
      nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
        (knownBit true) = knownBit (decide (t + 1 ≠ N)) ∧
      nbaFold "a_sh" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
        (LVec.ofBitVec (Av >>> (t * W))) = LVec.ofBitVec (Av >>> ((t + 1) * W)) ∧
      nbaFold "b_next" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false)
        (accC N W AccW Av Bv t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) (wRow N W Bv t))
        (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W)))) = LVec.ofBitVec (Bv >>> ((t + 2) * (N * W))) := by
    simp only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
      BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.mul_ofBitVec, LVec.sub_ofBitVec,
      LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq,
      Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN'),
      LVec.width_ofBitVec, LVec.add_ofBitVec, LVec.shr_ofBitVec, hyW, hyNW,
      LVec.resizeU_ofBitVec, BitVec.setWidth_eq, shiftRight_shiftRight, ← Nat.succ_mul]
    by_cases hf : t + 1 = N <;>
      simp [hf, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
        BitVec.ofNat_add_ofNat]
    · exact congrArg (fun k => Bv >>> (k * (N * W))) (by omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hctrl
  rw [hwc, hc, h1, h2, h3, h4, h5]

/-! ## 5. Phase model -/

theorem St_inj {ck r s a b dn c k bz ash bnx wc ck' r' s' a' b' dn' c' k' bz' ash' bnx' wc' : LVec}
    (h : mmG.St ck r s a b dn c k bz ash bnx wc =
      mmG.St ck' r' s' a' b' dn' c' k' bz' ash' bnx' wc') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ ash = ash' ∧ bnx = bnx' ∧ wc = wc' := by
  simp only [mmG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ash bnx wc,
    prev = mmG.St ck r s a b dn c k bz ash bnx wc ∧
    Wd N W AccW dn c k bz ash bnx wc ∧
    st = mmG.next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz ash bnx wc

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hNW32 : N * W < 2 ^ 32) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hN32 hW32 hA32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bnx, wc, rfl, hw⟩ hc
    have hnext := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c kk bz ash bnx wc k 30 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, ash, bnx, wc, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bnx wc hw
  Ready := Ready N W AccW
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, ash, bnx, wc, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, ash, bnx, wc, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmG.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset _ _ _ _ dn c k bz ash bnx wc hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N - 1, by omega, 0, by omega,
      next_start hN hW hNW32 _ _ _ dn c k bz ash bnx wc hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', hb⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      next_step (AccW := AccW) hN hW hNW32 x.1 x.2.1 (t := t) (by omega)]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, rfl, by simp, by simp, by simp, wRow_width ..⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', ash', bnx', wc', hb, h2, h3, h5, h6, h7⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, h2, h3, h5, h6, h7⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', ash', bnx', wc', hb, h3, h5, h6, h7⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, h3, h5, h6, h7⟩

/-! ## 6. Interface, discipline, and the three v2 rules -/

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmG.D N W AccW).processes.toList) :
    p = mmG.p0 N W AccW ∨ (∃ i j, i < N ∧ j < N ∧ p = mmG.g_core N W AccW i j) := by
  simp only [mmG.D, List.toList_toArray, mmG.procs, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_range] at hp
  rcases hp with rfl | ⟨i, hi, j, hj, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨i, j, hi, hj, rfl⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "a_sh", "b_next", "w_cur"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmG.D, mmG.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmG.p0, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_core, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mmG.profile N W AccW hN hW hA hN32 hW32 hA32)))
    (by simp [mmG.D, mmG.decls, Design2.outputNames, Design2.inputNames])

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl,
    -, -, -, -, -, w6, w7, w8, w9, w10, w11, w12⟩ :=
    mmG.powerUp N W AccW hN hW hA hN32 hW32 hA32 st h
  exact ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl, w6, w7, w8, w9, w10, w11, w12⟩

theorem mm_noq (N W AccW : Nat) :
    (mmG.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mm_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩ <;>
    simp [mmG.p0, mmG.g_core, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32) (fun σ => ⟨30, ?_⟩)
    (by rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ash, bnx, wc, rfl, hw⟩
  exact ⟨_, _, mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c k bz ash bnx wc kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz ash bnx wc hw⟩

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mm_proc_mem hp with rfl | ⟨i, j, hi, hj, rfl⟩
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmG.p0, mmG.D, mmG.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hA' : i * N * W + W ≤ N * N * W := by
      simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
    have hB' : j * W + W ≤ N * N * W := by
      simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
    have hW' : (i * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le hi hj
    have hA1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
    have hW1 : (i * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
    have hC' : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_core, mmG.D, mmG.decls, LVec.allKnown_ofBitVec, hA', hB', hW', hA1, hW1, hC']

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hN32 : N < 2147483648 := by omega
  have hW32 : W < 2147483648 := by omega
  have hA32 : AccW < 2147483648 := by omega
  have hNW32 : N * W < 2 ^ 32 := by
    have : N * W ≤ 256 * 127 := Nat.mul_le_mul hN256 hW127
    omega
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases
    (mm_interface N W AccW hN hW hA hN32 hW32 hA32)
    (mm_disciplined N W AccW hN hW hA hN32 hW32 hA32)
    (mm_terminatesPU N W AccW hN hW hA hN32 hW32 hA32) hN
    (model N W AccW hN hW hA hN32 hW32 hA32 hNW32)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32)
    (mm_moore N W AccW hN hW hA hN32 hW32 hA32)
    (mm_xsafe N W AccW hN hW hA hN32 hW32 hA32)

end Submission
