-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Mirror, disjointness, and generated clock cycle -/

sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem pairwise_flatMap_range' {α : Type} {R : α → α → Prop} {s n : Nat} {f : Nat → List α}
    (h1 : ∀ i, s ≤ i → i < s + n → (f i).Pairwise R)
    (h2 : ∀ i i', s ≤ i → i < i' → i' < s + n → ∀ x ∈ f i, ∀ y ∈ f i', R x y) :
    ((List.range' s n).flatMap f).Pairwise R := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  exact pairwise_flatMap_range (fun k hk => h1 (s + k) (by omega) (by omega))
    (fun k k' hkk' hk' x hx y hy => h2 (s + k) (s + k') (by omega) (by omega) (by omega) x hx y hy)

theorem idx3_lt {N d i j d' i' j' : Nat} (hi : i < N) (hj : j < N)
    (h : d < d' ∨ (d = d' ∧ i * N + j < i' * N + j')) :
    d * N * N + i * N + j < d' * N * N + i' * N + j' := by
  rcases h with hd | ⟨rfl, hij⟩
  · have h1 : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
    have h2 := rowMajor_le (K := N * N) hd
    simp only [Nat.mul_assoc] at h2 ⊢; omega
  · omega

theorem mmG_disj (N W AccW : Nat) : (mmG.procs N W AccW).Pairwise ProcDisj := by
  have sepA : ∀ q q', q < q' → q * AccW + AccW ≤ q' * AccW := fun q q' h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  unfold mmG.procs
  refine List.Pairwise.cons (fun q hq => ?_) (List.pairwise_append.mpr ⟨?_, List.pairwise_append.mpr ⟨?_, ?_, ?_⟩, ?_⟩)
  · simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'] at hq
    rcases hq with ⟨d, -, i, -, j, -, rfl⟩ | ⟨d, -, i, -, j, -, rfl⟩ | ⟨i, -, j, -, rfl⟩
    · exact ProcDisj.of_all (by simp [mmG.p0, mmG.g_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · exact ProcDisj.of_all (by simp [mmG.p0, mmG.g_col_1, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · exact ProcDisj.of_all (by simp [mmG.p0, mmG.g_output_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · refine pairwise_flatMap_range (fun d _ => ?_) (fun d d' hdd' hd' => by omega)
    exact pairwise_rowMajor fun i j i' j' hi _ hj _ h => by
      have hA := sepA (d * N * N + i * N + j) (d * N * N + i' * N + j') (by omega)
      exact ProcDisj.of_all (by simp [mmG.g_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  · refine pairwise_flatMap_range' (fun d _ _ => ?_) (fun d d' _ hdd' _ p hp q hq => ?_)
    · exact pairwise_rowMajor fun i j i' j' hi _ hj _ h => by
        have hA := sepA (d * N * N + i * N + j) (d * N * N + i' * N + j') (by omega)
        exact ProcDisj.of_all (by simp [mmG.g_col_1, Process2.procWins, Stmt2.drvWins,
          Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp hq
      obtain ⟨i, hi, j, hj, rfl⟩ := hp; obtain ⟨i', _, j', _, rfl⟩ := hq
      have hA := sepA _ _ (idx3_lt (d := d) (d' := d') (i' := i') (j' := j') hi hj (.inl hdd'))
      exact ProcDisj.of_all (by simp [mmG.g_col_1, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  · exact pairwise_rowMajor fun i j i' j' _ _ _ _ h => by
      have hA := sepA (i * N + j) (i' * N + j') h
      exact ProcDisj.of_all (by simp [mmG.g_output_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  · intro p hp q hq
    simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'] at hp hq
    obtain ⟨d, -, i, -, j, -, rfl⟩ := hp; obtain ⟨i', -, j', -, rfl⟩ := hq
    exact ProcDisj.of_all (by simp [mmG.g_col_1, mmG.g_output_col, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · intro p hp q hq
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'] at hp hq
    obtain ⟨d, hd, i, hi, j, hj, rfl⟩ := hp
    rcases hq with ⟨d', hd', i', _, j', _, rfl⟩ | ⟨i', -, j', -, rfl⟩
    · have hA := sepA _ _ (idx3_lt (d := d) (d' := d') (i' := i') (j' := j') hi hj (.inl (by omega)))
      exact ProcDisj.of_all (by simp [mmG.g_col, mmG.g_col_1, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps] <;> omega)
    · exact ProcDisj.of_all (by simp [mmG.g_col, mmG.g_output_col, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])

sv_cycle mmG using mmG_disj N W AccW

/-! ## 2. Arithmetic and condition helpers -/

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

theorem psum_one (N W : Nat) {n : Nat} (A B : BitVec n) (i j : Nat) :
    psum N W A B 1 i j = Tasks.Matmul.entry W A (i * N + 0) * Tasks.Matmul.entry W B (0 * N + j) := by
  simp [psum]

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

theorem land_cond_false_left (x : LVec) :
    (LVec.ofLogic
      (if (SymBinOp.land == SymBinOp.land) = true then
        if ((knownBit false).isKnownZero || x.isKnownZero) = true then Logic.l0
        else if ((knownBit false).condTrue && x.condTrue) = true then Logic.l1 else Logic.lx
      else
        if ((knownBit false).condTrue || x.condTrue) = true then Logic.l1
        else if ((knownBit false).isKnownZero && x.isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue =
      false := by
  have heq : (SymBinOp.land == SymBinOp.land) = true := by decide
  have hl0 : (LVec.ofLogic Logic.l0).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  simp only [heq, isKnownZero_knownBit, Bool.not_false, Bool.true_or, ↓reduceIte, hl0]

theorem land_cond_knownBit (b1 b2 : Bool) :
    (LVec.ofLogic
      (if (SymBinOp.land == SymBinOp.land) = true then
        if ((knownBit b1).isKnownZero || (knownBit b2).isKnownZero) = true then Logic.l0
        else if ((knownBit b1).condTrue && (knownBit b2).condTrue) = true then Logic.l1 else Logic.lx
      else
        if ((knownBit b1).condTrue || (knownBit b2).condTrue) = true then Logic.l1
        else if ((knownBit b1).isKnownZero && (knownBit b2).isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue =
      (b1 && b2) := by
  have heq : (SymBinOp.land == SymBinOp.land) = true := by decide
  have hl0 : (LVec.ofLogic Logic.l0).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  have hl1 : (LVec.ofLogic Logic.l1).condTrue = true := by simp [LVec.ofLogic, LVec.condTrue]
  cases b1 <;> cases b2 <;>
    simp only [heq, condTrue_knownBit, isKnownZero_knownBit, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.not_true, Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false, hl0, hl1]

/-! ## 3. Queue splitting and `nbaFold` helpers -/

@[simp] theorem nbaFold_width (n : String) : ∀ (q : NbaQueue2) (x : LVec),
    (nbaFold n q x).width = x.width
  | [], _ => rfl
  | u :: q, x => by
    rw [nbaFold_cons, nbaFold_width n q]
    split <;> simp

theorem nbaFold_append (n : String) (q₁ q₂ : NbaQueue2) (x : LVec) :
    nbaFold n (q₁ ++ q₂) x = nbaFold n q₂ (nbaFold n q₁ x) := by
  simp [nbaFold, List.foldl_append]

def cube0Q (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) : NbaQueue2 :=
  (List.range 1).flatMap fun d => (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_colQ N W AccW d i j ck r s a b dn c k bz am bm ca

def cube1Q (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) : NbaQueue2 :=
  (List.range' 1 (N - 1)).flatMap fun d => (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_col_1Q N W AccW d i j ck r s a b dn c k bz am bm ca

def outQ (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    mmG.g_output_colQ N W AccW i j ck r s a b dn c k bz am bm ca

theorem p0Q_names (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ mmG.p0Q N W AccW ck r s a b dn c k bz am bm ca,
      u.1 ∈ ["busy", "done", "k", "A_mem", "B_mem"] := by
  intro u hu
  unfold mmG.p0Q at hu
  split at hu
  · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
  · split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · split at hu
        · simp at hu; rcases hu with rfl | rfl | rfl <;> simp
        · simp at hu; subst hu; simp
      · simp at hu

theorem g_colQ_names (N W AccW d i j : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ mmG.g_colQ N W AccW d i j ck r s a b dn c k bz am bm ca, u.1 ∈ ["cube_acc"] := by
  have haux : ∀ (c1 : Bool) (v1 : LVec) (u : String × Nat × LVec),
      u ∈ (if c1 = true then [("cube_acc", (d * N * N + i * N + j) * AccW, v1)] else []) →
      u.1 ∈ ["cube_acc"] := by
    intro c1 v1 u hu; cases c1 <;> simp at hu; subst hu; simp
  intro u hu; exact haux _ _ u hu

theorem g_col_1Q_names (N W AccW d i j : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ mmG.g_col_1Q N W AccW d i j ck r s a b dn c k bz am bm ca, u.1 ∈ ["cube_acc"] := by
  have haux : ∀ (c1 c2 : Bool) (v1 v2 : LVec) (u : String × Nat × LVec),
      u ∈ (if c1 = true then [("cube_acc", (d * N * N + i * N + j) * AccW, v1)]
           else if c2 = true then [("cube_acc", (d * N * N + i * N + j) * AccW, v2)] else []) →
      u.1 ∈ ["cube_acc"] := by
    intro c1 c2 v1 v2 u hu; cases c1 <;> cases c2 <;> simp at hu <;> (subst hu; simp)
  intro u hu; exact haux _ _ _ _ u hu

theorem g_output_colQ_names (N W AccW i j : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ mmG.g_output_colQ N W AccW i j ck r s a b dn c k bz am bm ca, u.1 ∈ ["C"] := by
  have haux : ∀ (c1 c2 : Bool) (v1 v2 : LVec) (u : String × Nat × LVec),
      u ∈ (if c1 = true then [("C", (i * N + j) * AccW, v1)]
           else if c2 = true then [("C", (i * N + j) * AccW, v2)] else []) →
      u.1 ∈ ["C"] := by
    intro c1 c2 v1 v2 u hu; cases c1 <;> cases c2 <;> simp at hu <;> (subst hu; simp)
  intro u hu; exact haux _ _ _ _ u hu

theorem cube0Q_names (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ cube0Q N W AccW ck r s a b dn c k bz am bm ca, u.1 ∈ ["cube_acc"] := by
  intro u hu
  simp only [cube0Q, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨d, -, i, -, j, -, hu⟩ := hu
  exact g_colQ_names N W AccW d i j ck r s a b dn c k bz am bm ca u hu

theorem cube1Q_names (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ cube1Q N W AccW ck r s a b dn c k bz am bm ca, u.1 ∈ ["cube_acc"] := by
  intro u hu
  simp only [cube1Q, List.mem_flatMap, List.mem_range, List.mem_range'] at hu
  obtain ⟨d, -, i, -, j, -, hu⟩ := hu
  exact g_col_1Q_names N W AccW d i j ck r s a b dn c k bz am bm ca u hu

theorem outQ_names (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ outQ N W AccW ck r s a b dn c k bz am bm ca, u.1 ∈ ["C"] := by
  intro u hu
  simp only [outQ, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  exact g_output_colQ_names N W AccW i j ck r s a b dn c k bz am bm ca u hu

theorem mmG_next_eq (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec) :
    let pQ := mmG.p0Q N W AccW ck r s a b dn c k bz am bm ca
    let c0Q := cube0Q N W AccW ck r s a b dn c k bz am bm ca
    let c1Q := cube1Q N W AccW ck r s a b dn c k bz am bm ca
    let oQ := outQ N W AccW ck r s a b dn c k bz am bm ca
    mmG.next N W AccW ck r s a b dn c k bz am bm ca =
      mmG.St ck r s a b
        (nbaFold "done" pQ dn) (nbaFold "C" oQ c) (nbaFold "k" pQ k) (nbaFold "busy" pQ bz)
        (nbaFold "A_mem" pQ am) (nbaFold "B_mem" pQ bm)
        (nbaFold "cube_acc" c1Q (nbaFold "cube_acc" c0Q ca)) := by
  dsimp only [mmG.next]
  change commitNba2 (mmG.St ck r s a b dn c k bz am bm ca)
    (mmG.p0Q N W AccW ck r s a b dn c k bz am bm ca ++
      (cube0Q N W AccW ck r s a b dn c k bz am bm ca ++
        (cube1Q N W AccW ck r s a b dn c k bz am bm ca ++
          outQ N W AccW ck r s a b dn c k bz am bm ca))) = _
  rw [commitNba2_eq_map _ _ (by simp [mmG.St])]
  simp only [mmG.St, List.map_cons, List.map_nil]
  have hp := p0Q_names N W AccW ck r s a b dn c k bz am bm ca
  have h0 := cube0Q_names N W AccW ck r s a b dn c k bz am bm ca
  have h1 := cube1Q_names N W AccW ck r s a b dn c k bz am bm ca
  have ho := outQ_names N W AccW ck r s a b dn c k bz am bm ca
  change [_, _, _, _, _, _, _, _, _, _, _, _] = [_, _, _, _, _, _, _, _, _, _, _, _]
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true]
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  have hfold : ∀ (n : String) (x : LVec),
      nbaFold n (mmG.p0Q N W AccW ck r s a b dn c k bz am bm ca ++
        (cube0Q N W AccW ck r s a b dn c k bz am bm ca ++
          (cube1Q N W AccW ck r s a b dn c k bz am bm ca ++
            outQ N W AccW ck r s a b dn c k bz am bm ca))) x =
      nbaFold n (outQ N W AccW ck r s a b dn c k bz am bm ca)
        (nbaFold n (cube1Q N W AccW ck r s a b dn c k bz am bm ca)
          (nbaFold n (cube0Q N W AccW ck r s a b dn c k bz am bm ca)
            (nbaFold n (mmG.p0Q N W AccW ck r s a b dn c k bz am bm ca) x))) := by
    intro n x; simp only [nbaFold_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide), nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide), nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide), nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide), nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide), nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names h0 (by decide), nbaFold_of_names h1 (by decide),
      nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names h0 (by decide),
      nbaFold_of_names h1 (by decide)]
  · rw [hfold, nbaFold_of_names h0 (by decide), nbaFold_of_names h1 (by decide),
      nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names h0 (by decide), nbaFold_of_names h1 (by decide),
      nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names h0 (by decide), nbaFold_of_names h1 (by decide),
      nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names h0 (by decide), nbaFold_of_names h1 (by decide),
      nbaFold_of_names ho (by decide)]
  · rw [hfold, nbaFold_of_names hp (by decide), nbaFold_of_names ho (by decide)]

/-! ## 4. Shape, cube invariant, and one-cycle transitions -/

def Wd (N W AccW : Nat) (dn c k bz am bm ca : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  am.width = N * N * W ∧ bm.width = N * N * W ∧ ca.width = N * N * N * AccW

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm ca,
    st = mmG.St ck r s a b dn c k bz am bm ca ∧ Wd N W AccW dn c k bz am bm ca

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mmG.init N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd]⟩

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz am bm ca : LVec)
    (hw : Wd N W AccW dn c k bz am bm ca) :
    I N W AccW (mmG.next N W AccW ck r s a b dn c k bz am bm ca) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  rw [mmG_next_eq]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, by simp [Wd, h1, h2, h3, h4, h5, h6, h7]⟩

def CubeOK (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (ca : LVec) : Prop :=
  ca.width = N * N * N * AccW ∧
  ∀ d i j, d ≤ t → d < N → i < N → j < N →
    ca.extract ((d * N * N + i * N + j) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (d + 1) i j))

def Ready (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c k am bm ca,
    st = mmG.St ck r s a b (knownBit false) c k (knownBit false) am bm ca ∧
    c.width = N * N * AccW ∧ k.width = 32 ∧
    am.width = N * N * W ∧ bm.width = N * N * W ∧ ca.width = N * N * N * AccW

def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b c ca,
    st = mmG.St ck r s a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec A) (LVec.ofBitVec B) ca ∧
    c.width = N * N * AccW ∧ CubeOK N W AccW A B t ca

def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k am bm ca,
    st = mmG.St ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B))
      k (knownBit false) am bm ca ∧
    k.width = 32 ∧ am.width = N * N * W ∧ bm.width = N * N * W ∧ ca.width = N * N * N * AccW

theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz am bm ca : LVec)
    (hw : Wd N W AccW dn c k bz am bm ca) :
    Ready N W AccW (mmG.next N W AccW ck (knownBit true) s a b dn c k bz am bm ca) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz am bm ca) dn =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit true) s a b dn c k bz am bm ca) bz =
      knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [hd, hb]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp [h2], by simp [h3], by simp [h5], by simp [h6], by simp [h7]⟩

theorem next_idle {N W AccW : Nat} (ck a b dn c k am bm ca : LVec) :
    mmG.next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca =
      mmG.St ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca := by
  rw [mmG_next_eq]
  have hp : mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca = [] := by
    simp [mmG.p0Q]
  have h0 : cube0Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca = [] := by
    simp only [cube0Q, mmG.g_colQ, lor_cond_knownBit]; simp
  have h1 : cube1Q N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca = [] := by
    simp only [cube1Q, mmG.g_col_1Q, lor_cond_knownBit]; simp
  have ho : outQ N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm ca = [] := by
    simp only [outQ, mmG.g_output_colQ, lor_cond_knownBit, land_cond_false_left]; simp
  rw [hp, h0, h1, ho]; rfl

theorem cube_prod_val {N W AccW : Nat} (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {d i j : Nat} (hd : d < N) (hi : i < N) (hj : j < N) :
    (((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Av).extract ((i * N + d) * W + W - 1) 1]),
          (LVec.ofBitVec Av).extract ((i * N + d) * W) W]).mul
        (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Bv).extract ((d * N + j) * W + W - 1) 1]),
          (LVec.ofBitVec Bv).extract ((d * N + j) * W) W])).resizeU AccW).resizeU AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (Tasks.Matmul.entry W Av (i * N + d) * Tasks.Matmul.entry W Bv (d * N + j))) := by
  have hexA : (LVec.ofBitVec Av).extract ((i * N + d) * W) W = LVec.ofBitVec (Av.extractLsb' ((i * N + d) * W) W) :=
    LVec.extract_ofBitVec Av (Lib.rowMajor_window_le hi hd)
  have hexB : (LVec.ofBitVec Bv).extract ((d * N + j) * W) W = LVec.ofBitVec (Bv.extractLsb' ((d * N + j) * W) W) :=
    LVec.extract_ofBitVec Bv (Lib.rowMajor_window_le hd hj)
  rw [LVec.sext_of_extract hW hexA, LVec.sext_of_extract hW hexB,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_mul_signExtend (by omega : AccW ≤ AccW + W)]
  rfl

theorem cube_acc_step {N W AccW : Nat} (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {d i j : Nat} (_hd1 : 1 ≤ d) (hd : d < N) (hi : i < N) (hj : j < N) {ca : LVec}
    (hprev : ca.extract (((d - 1) * N * N + i * N + j) * AccW) AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv d i j))) :
    ((((ca.extract (((d - 1) * N * N + i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        ((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Av).extract ((i * N + d) * W + W - 1) 1]),
            (LVec.ofBitVec Av).extract ((i * N + d) * W) W]).mul
          (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Bv).extract ((d * N + j) * W + W - 1) 1]),
            (LVec.ofBitVec Bv).extract ((d * N + j) * W) W]))).resizeU AccW).resizeU AccW =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (d + 1) i j)) := by
  have hexA : (LVec.ofBitVec Av).extract ((i * N + d) * W) W = LVec.ofBitVec (Av.extractLsb' ((i * N + d) * W) W) :=
    LVec.extract_ofBitVec Av (Lib.rowMajor_window_le hi hd)
  have hexB : (LVec.ofBitVec Bv).extract ((d * N + j) * W) W = LVec.ofBitVec (Bv.extractLsb' ((d * N + j) * W) W) :=
    LVec.extract_ofBitVec Bv (Lib.rowMajor_window_le hd hj)
  rw [hprev, LVec.sext_of_extract hW hexA, LVec.sext_of_extract hW hexB,
    LVec.resizeU_ofBitVec, LVec.mul_ofBitVec, LVec.add_ofBitVec,
    LVec.resizeU_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend (by omega : AccW ≤ AccW + W),
    ← BitVec.ofInt_add, psum_succ]
  rfl

theorem cube1Q_disj_layer0 {N W AccW i j : Nat} (hi : i < N) (hj : j < N)
    (ck r s a b dn c k bz am bm ca : LVec) :
    ∀ u ∈ cube1Q N W AccW ck r s a b dn c k bz am bm ca,
      u.1 ≠ "cube_acc" ∨ u.2.1 + u.2.2.width ≤ (i * N + j) * AccW ∨
        (i * N + j) * AccW + AccW ≤ u.2.1 := by
  intro u hu
  simp only [cube1Q, List.mem_flatMap, List.mem_range, List.mem_range'] at hu
  obtain ⟨d, hd, i', hi', j', hj', hu⟩ := hu
  have hlo : (i * N + j) * AccW + AccW ≤ (d * N * N + i' * N + j') * AccW := by
    have hlt := idx3_lt (N := N) (d := 0) (d' := d) (i' := i') (j' := j') hi hj (.inl (by omega))
    simp only [Nat.zero_mul, Nat.zero_add] at hlt
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt hlt)
    rwa [Nat.succ_mul] at this
  have haux : ∀ (c1 c2 : Bool) (v1 v2 : LVec),
      u ∈ (if c1 = true then [("cube_acc", (d * N * N + i' * N + j') * AccW, v1)]
           else if c2 = true then [("cube_acc", (d * N * N + i' * N + j') * AccW, v2)] else []) →
      u.2.1 = (d * N * N + i' * N + j') * AccW := by
    intro c1 c2 v1 v2 h; cases c1 <;> cases c2 <;> simp at h <;> (subst h; rfl)
  right; right
  rw [haux _ _ _ _ hu]
  exact hlo

theorem cube1Q_pairwise_disj {N AccW : Nat} (f : Nat → Nat → Nat → LVec)
    (hfw : ∀ d i j, (f d i j).width = AccW) :
    ((List.range' 1 (N - 1)).flatMap fun d => (List.range N).flatMap fun i =>
      (List.range N).map fun j => ("cube_acc", (d * N * N + i * N + j) * AccW, f d i j)).Pairwise
      NbaDisj := by
  have sepA : ∀ q q', q < q' → q * AccW + AccW ≤ q' * AccW := fun q q' h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  refine pairwise_flatMap_range' (fun d _ _ => ?_) (fun d d' _ hdd' _ u hu v hv => ?_)
  · refine pairwise_rowMajor fun i j i' j' hi _ hj _ h => ?_
    right; left
    rw [hfw]; exact sepA (d * N * N + i * N + j) (d * N * N + i' * N + j') (by omega)
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hu hv
    obtain ⟨i, hi, j, hj, rfl⟩ := hu; obtain ⟨i', _, j', _, rfl⟩ := hv
    right; left
    rw [hfw]; exact sepA _ _ (idx3_lt (i' := i') (j' := j') hi hj (.inl hdd'))

theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W)
    (Av Bv : BitVec (N * N * W)) (ck dn c k bz am bm ca : LVec)
    (hw : Wd N W AccW dn c k bz am bm ca) :
    BusyAt N W AccW Av Bv 0
      (mmG.next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
        dn c k bz am bm ca) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hw
  rw [mmG_next_eq]
  have hd : nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz am bm ca) dn = knownBit false := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz am bm ca) bz = knownBit true := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l1]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  have hk : nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz am bm ca) k = LVec.ofBitVec (BitVec.ofNat 32 0) := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h3, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h3])
  have ham : nbaFold "A_mem" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz am bm ca) am = LVec.ofBitVec Av := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h5, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h5])
  have hbm : nbaFold "B_mem" (mmG.p0Q N W AccW ck (knownBit false) (knownBit true)
      (LVec.ofBitVec Av) (LVec.ofBitVec Bv) dn c k bz am bm ca) bm = LVec.ofBitVec Bv := by
    simp (disch := decide) only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h6, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h6])
  have hc0 : cube0Q N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      dn c k bz am bm ca =
    (List.range (N * N)).map fun r =>
      ("cube_acc", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 1 (r / N) (r % N)))) := by
    unfold cube0Q
    simp only [List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine flatMap_range_rowMajor _ fun i j hi hj => ?_
    simp only [mmG.g_colQ, lor_cond_knownBit, Bool.false_or, ↓reduceIte]
    rw [cube_prod_val hW Av Bv hN hi hj]
    simp only [Nat.zero_mul, Nat.zero_add, psum_one, rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
  rw [hd, hb, hk, ham, hbm]
  refine ⟨_, _, _, _, _, _, _, rfl, by simp [h2], by simp [h7], ?_⟩
  intro d i j hd0 _ hi hj
  obtain rfl : d = 0 := by omega
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [SvGolf.Cycle.extract_nbaFold_of_disj _ _ (cube1Q_disj_layer0 hi hj _ _ _ _ _ _ _ _ _ _ _ _),
    hc0, nbaFold_map_insertEntries]
  have h1' : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
  have hca_le : N * N * AccW ≤ ca.width := by
    rw [h7]; exact Nat.mul_le_mul_right AccW (Nat.le_mul_of_pos_right (N * N) hN)
  rw [LVec.extract_insertEntries (fun _ => LVec.width_ofBitVec _) ca (N * N) hca_le _ h1',
    rowMajor_div hj, Nat.mul_add_mod_of_lt hj]

theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hN32 : N < 2147483648)
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b c ca : LVec)
    (hcw : c.width = N * N * AccW) (hca : CubeOK N W AccW Av Bv t ca) :
    let st' := mmG.next N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca
    if t + 1 = N then FinAt N W AccW Av Bv st' else BusyAt N W AccW Av Bv (t + 1) st' := by
  dsimp only
  rw [mmG_next_eq]
  have hc0 : cube0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca = [] := by
    simp only [cube0Q, mmG.g_colQ, lor_cond_knownBit]; simp
  have hctrl :
      nbaFold "done" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca)
        (knownBit false) = knownBit (decide (t + 1 = N)) ∧
      nbaFold "k" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) = LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
      nbaFold "busy" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca)
        (knownBit true) = knownBit (decide (t + 1 ≠ N)) ∧
      nbaFold "A_mem" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca)
        (LVec.ofBitVec Av) = LVec.ofBitVec Av ∧
      nbaFold "B_mem" (mmG.p0Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca)
        (LVec.ofBitVec Bv) = LVec.ofBitVec Bv := by
    simp only [mmG.p0Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
      BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec,
      LVec.ofLogic_ofBool, decide_eq_true_eq,
      Lib.ofNat_eq_ofNat_sub_one_iff ht (by omega : N ≤ 2 ^ 32),
      LVec.width_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    by_cases hf : t + 1 = N <;>
      simp [hf, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
        BitVec.ofNat_add_ofNat]
  obtain ⟨h1, h2, h3, h4, h5⟩ := hctrl
  rw [hc0, nbaFold_nil, h1, h2, h3, h4, h5]
  by_cases hf : t + 1 = N
  · rw [ite_eq_left hf]
    have hout : nbaFold "C" (outQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca) c =
        LVec.ofBitVec (Tasks.Matmul.product N W AccW Av Bv) := by
      have hq : outQ N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
          (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca =
        (List.range (N * N)).map fun r =>
          ("C", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv N (r / N) (r % N)))) := by
        refine flatMap_range_rowMajor _ fun i j hi hj => ?_
        have hprev := hca.2 (N - 1) i j (by omega) (by omega) hi hj
        rw [show N - 1 + 1 = N by omega] at hprev
        simp only [mmG.g_output_colQ, lor_cond_knownBit]
        simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte,
          LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat, LVec.sub_ofBitVec,
          LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool,
          Lib.ofNat_eq_ofNat_sub_one_iff ht (by omega : N ≤ 2 ^ 32), hf, decide_true]
        rw [show LVec.ofBitVec (BitVec.ofBool true) = knownBit true from rfl, land_cond_knownBit]
        simp only [Bool.and_self, ↓reduceIte, hprev, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
          rowMajor_div hj, Nat.mul_add_mod_of_lt hj]
      rw [hq, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ hcw, ← accC, accC_N]
    rw [hout]
    simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, by simp, by simp, by simp, by simp [hca.1]⟩
  · rw [ite_eq_right hf]
    simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
    refine ⟨_, _, _, _, _, _, _, rfl, by simp [hcw], by simp [hca.1], ?_⟩
    intro d i j hdt hdN hi hj
    by_cases hd0 : d = 0
    · subst hd0
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [SvGolf.Cycle.extract_nbaFold_of_disj _ _ (cube1Q_disj_layer0 hi hj _ _ _ _ _ _ _ _ _ _ _ _)]
      simpa using hca.2 0 i j (by omega) hdN hi hj
    · let val : Nat → Nat → Nat → LVec := fun d' i' j' =>
        ((((ca.extract (((d' - 1) * N * N + i' * N + j') * AccW) AccW).resizeU (AccW + W)).add
            ((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Av).extract ((i' * N + d') * W + W - 1) 1]),
                (LVec.ofBitVec Av).extract ((i' * N + d') * W) W]).mul
              (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[(LVec.ofBitVec Bv).extract ((d' * N + j') * W + W - 1) 1]),
                (LVec.ofBitVec Bv).extract ((d' * N + j') * W) W]))).resizeU AccW).resizeU AccW
      have hq1 : cube1Q N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) c
          (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv) ca =
        (List.range' 1 (N - 1)).flatMap fun d' => (List.range N).flatMap fun i' =>
          (List.range N).map fun j' => ("cube_acc", (d' * N * N + i' * N + j') * AccW, val d' i' j') := by
        unfold cube1Q
        refine CombView.flatMap_congr' fun d' _ => CombView.flatMap_congr' fun i' _ => ?_
        refine flatMap_range_singleton fun j' _ => ?_
        simp only [mmG.g_col_1Q, lor_cond_knownBit]
        simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, condTrue_knownBit, val]
      have hpw := cube1Q_pairwise_disj (N := N) (AccW := AccW) val (fun _ _ _ => LVec.width_resizeU ..)
      have hmem : ("cube_acc", (d * N * N + i * N + j) * AccW, val d i j) ∈
          (List.range' 1 (N - 1)).flatMap fun d' => (List.range N).flatMap fun i' =>
            (List.range N).map fun j' => ("cube_acc", (d' * N * N + i' * N + j') * AccW, val d' i' j') := by
        simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_range'_1]
        exact ⟨d, by omega, i, hi, j, hj, rfl⟩
      have hbound : (d * N * N + i * N + j) * AccW + (val d i j).width ≤ ca.width := by
        rw [hca.1, show (val d i j).width = AccW from LVec.width_resizeU ..]
        have hlt : d * N * N + i * N + j < N * N * N := by
          have h1' : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
          have h2' := rowMajor_le (K := N * N) hdN
          simp only [Nat.mul_assoc] at h2' ⊢; omega
        have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt hlt)
        rwa [Nat.succ_mul] at this
      have hex := SvGolf.Cycle.extract_nbaFold_of_mem (x := ca) hpw hmem hbound
      rw [show (val d i j).width = AccW from LVec.width_resizeU ..] at hex
      rw [hq1, hex]
      have hprev := hca.2 (d - 1) i j (by omega) (by omega) hi hj
      rw [show d - 1 + 1 = d by omega] at hprev
      exact cube_acc_step hW Av Bv (by omega) hdN hi hj hprev

/-! ## 5. Phase model -/

theorem St_inj {ck r s a b dn c k bz am bm ca ck' r' s' a' b' dn' c' k' bz' am' bm' ca' : LVec}
    (h : mmG.St ck r s a b dn c k bz am bm ca = mmG.St ck' r' s' a' b' dn' c' k' bz' am' bm' ca') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ am = am' ∧ bm = bm' ∧ ca = ca' := by
  simp only [mmG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm ca,
    prev = mmG.St ck r s a b dn c k bz am bm ca ∧
    Wd N W AccW dn c k bz am bm ca ∧
    st = mmG.next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz am bm ca

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
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, am, bm, ca, rfl, hw⟩ hc
    have hnext := mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c kk bz am bm ca k 30 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, am, bm, ca, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz am bm ca hw
  Ready := Ready N W AccW
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, am, bm, ca, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, c, ca, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, mmG.St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, am, bm, ca, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, mmG.St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset _ _ _ _ dn c k bz am bm ca hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N - 1, by omega, 0, by omega, next_start hN hW _ _ _ dn c k bz am bm ca hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', c', ca', hb, hcw, hca⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    have hstep := next_step hN hW hN32 x.1 x.2.1 (t := t) (by omega)
      (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b) c ca hcw hca
    by_cases hf : t + 1 = N
    · left; simpa [hf] using hstep
    · right; exact ⟨m - 1, by omega, t + 1, by omega, by simpa [hf] using hstep⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', am', bm', ca', hb, h2, h3, h5, h6, h7⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, h2, h3, h5, h6, h7⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', am', bm', ca', hb, h3, h5, h6, h7⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, h3, h5, h6, h7⟩

/-! ## 6. Interface, discipline, and the three v2 rules -/

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmG.D N W AccW).processes.toList) :
    p = mmG.p0 N W AccW ∨
      (∃ i j, i < N ∧ j < N ∧ p = mmG.g_col N W AccW 0 i j) ∨
      (∃ d i j, 1 ≤ d ∧ d < N ∧ i < N ∧ j < N ∧ p = mmG.g_col_1 N W AccW d i j) ∨
      (∃ i j, i < N ∧ j < N ∧ p = mmG.g_output_col N W AccW i j) := by
  simp only [mmG.D, List.toList_toArray, mmG.procs, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_map, List.mem_range, List.mem_range'] at hp
  rcases hp with rfl | ⟨d, hd, i, hi, j, hj, rfl⟩ | ⟨d, hd, i, hi, j, hj, rfl⟩ | ⟨i, hi, j, hj, rfl⟩
  · exact .inl rfl
  · obtain rfl : d = 0 := by omega
    exact .inr (.inl ⟨i, j, hi, hj, rfl⟩)
  · exact .inr (.inr (.inl ⟨d, i, j, by omega, by omega, hi, hj, rfl⟩))
  · exact .inr (.inr (.inr ⟨i, j, hi, hj, rfl⟩))

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "A_mem", "B_mem", "cube_acc"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmG.D, mmG.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩ | ⟨d, i, j, -, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmG.p0, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_col, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, mmG.g_col_1, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, mmG.g_output_col, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mmG.profile N W AccW hN hW hA hN32 hW32 hA32)))
    (by simp [mmG.D, mmG.decls, Design2.outputNames, Design2.inputNames])

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  obtain ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl,
    -, -, -, -, -, h6, h7, h8, h9, h10, h11, h12⟩ :=
    mmG.powerUp N W AccW hN hW hA hN32 hW32 hA32 st h
  exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl, h6, h7, h8, h9, h10, h11, h12⟩

theorem mm_noq (N W AccW : Nat) :
    (mmG.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mm_proc_mem hp with rfl | ⟨i, j, -, -, rfl⟩ | ⟨d, i, j, -, -, -, -, rfl⟩ | ⟨i, j, -, -, rfl⟩ <;>
    simp [mmG.p0, mmG.g_col, mmG.g_col_1, mmG.g_output_col,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32) (fun σ => ⟨30, ?_⟩)
    (by rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ca, rfl, hw⟩
  exact ⟨_, _, mmG.cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c k bz am bm ca kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz am bm ca hw⟩

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mmG.sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mm_proc_mem hp with rfl | ⟨i, j, hi, hj, rfl⟩ | ⟨d, i, j, hd1, hdN, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmG.p0, mmG.D, mmG.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hA' : i * N * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
    have hB' : j * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
    have hA1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
    have hB1 : j * W + W - 1 + 1 ≤ N * N * W := by omega
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_col, mmG.D, mmG.decls, hA', hB', hA1, hB1]
  · have hA' : (i * N + d) * W + W ≤ N * N * W := Lib.rowMajor_window_le hi hdN
    have hB' : (d * N + j) * W + W ≤ N * N * W := Lib.rowMajor_window_le hdN hj
    have hA1 : (i * N + d) * W + W - 1 + 1 ≤ N * N * W := by omega
    have hB1 : (d * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
    have hP : ((d - 1) * N * N + i * N + j) * AccW + AccW ≤ N * N * N * AccW := by
      have h1' : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
      have h2' := rowMajor_le (K := N * N) (show d - 1 < N by omega)
      rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h2'
      have hlt : (d - 1) * N * N + i * N + j < N * N * N := by omega
      have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt hlt)
      rwa [Nat.succ_mul] at this
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_col_1, mmG.D, mmG.decls, hA', hB', hA1, hB1, hP]
  · have hL : ((N - 1) * N * N + i * N + j) * AccW + AccW ≤ N * N * N * AccW := by
      have h1' : i * N + j < N * N := by have := rowMajor_le (K := N) hi; omega
      have h2' := rowMajor_le (K := N * N) (show N - 1 < N by omega)
      rw [← Nat.mul_assoc, ← Nat.mul_assoc] at h2'
      have hlt : (N - 1) * N * N + i * N + j < N * N * N := by omega
      have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt hlt)
      rwa [Nat.succ_mul] at this
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth,
      mmG.g_output_col, mmG.D, mmG.decls, LVec.ofInt, LVec.allKnown_ofBitVec, hL]

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
