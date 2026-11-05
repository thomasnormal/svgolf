import tasks.clmul.Spec

namespace ClmulArith

open SvGolf.Tasks.Clmul

/-- `bx f n`: the XOR of `f 0, …, f (n-1)`. -/
def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bx_trunc {f : Nat → Bool} {n m : Nat} (hnm : n ≤ m) (h : ∀ j, n ≤ j → j < m → f j = false) :
    bx f m = bx f n := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; rfl
    · simp only [bx]
      rw [ih (by omega) (fun j hj1 hj2 => h j hj1 (by omega)), h m (by omega) (by omega)]
      simp

theorem foldl_xor (f : Nat → Bool) (n : Nat) (acc : Bool) :
    (List.range n).foldl (fun acc i => acc ^^ f i) acc = (acc ^^ bx f n) := by
  induction n generalizing acc with
  | zero => simp [bx]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [bx]
    cases acc <;> cases bx f n <;> cases f n <;> rfl

/-- The Spec's double sum is the nested `bx`. -/
theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) :
    coeff N a b k =
      bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) N) N := by
  unfold coeff
  simp only [foldl_xor]
  simp [bx]

theorem bx_pair (i k : Nat) (x : Bool) (c : Nat → Bool) (n : Nat) :
    bx (fun j => decide (i + j = k) && x && c j) n = (decide (i ≤ k ∧ k - i < n) && x && c (k - i)) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    simp only [bx, ih]
    by_cases h : i + n = k
    · have h1 : k - i = n := by omega
      have h2 : ¬ (k - i < n) := by omega
      have h3 : i ≤ k ∧ k - i < n + 1 := by omega
      simp [h, h1, h2, h3]
    · have h4 : (decide (i ≤ k ∧ k - i < n + 1)) = (decide (i ≤ k ∧ k - i < n)) := by
        apply decide_eq_decide.mpr; omega
      have h5 : decide (i + n = k) = false := by simp [h]
      rw [h5, h4]; simp

theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [ofBits]
  | n + 1, f, k => by
    rw [ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp [BitVec.getLsbD_ofBool]
    | succ k => simp [BitVec.getLsbD_ofBool]


/-- The accumulator of rows `0 .. i`, read at column `j`: `XOR over t ≤ i` of `A t & B (i + j - t)`, a term
whose `B` index is `≥ N` being `0`. -/
def rowSum (N : Nat) (A B : Nat → Bool) (i j : Nat) : Bool :=
  bx (fun t => decide (i + j - t < N) && A t && B (i + j - t)) (i + 1)

/-- The array's equations over `Nat`-indexed Boolean functions. -/
structure View (N : Nat) (A B : Nat → Bool) (P : Nat → Bool) (r : Nat → Nat → Bool) : Prop where
  row0 : ∀ j, j < N → r 0 j = (A 0 && B j)
  row_def : ∀ i, 1 ≤ i → i < N → ∀ j, j + 1 < N → r i j = (r (i - 1) (j + 1) ^^ (A i && B j))
  row_top : ∀ i, 1 ≤ i → i < N → r i (N - 1) = (A i && B (N - 1))
  p_low : ∀ i, i < N → P i = r i 0
  p_high : ∀ m, m + 1 < N → P (N + m) = r (N - 1) (m + 1)

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

theorem rowSum_big {N : Nat} {A B : Nat → Bool} {i j : Nat} (hj : N ≤ j) : rowSum N A B i j = false := by
  unfold rowSum
  apply bx_false
  intro t ht
  have : ¬ (i + j - t < N) := by omega
  simp [this]

theorem rowSum_succ (N : Nat) (A B : Nat → Bool) (i j : Nat) :
    rowSum N A B (i + 1) j = (rowSum N A B i (j + 1) ^^ (decide (j < N) && A (i + 1) && B j)) := by
  have e : ∀ t, i + 1 + j - t = i + (j + 1) - t := fun t => by omega
  have e2 : i + 1 + j - (i + 1) = j := by omega
  unfold rowSum
  rw [bx_succ _ (i + 1)]
  congr 1
  · apply bx_congr
    intro t ht
    simp only [e]
  · simp only [e2]

theorem view_row {N : Nat} {A B : Nat → Bool} {P : Nat → Bool} {r : Nat → Nat → Bool}
    (hv : View N A B P r) :
    ∀ i, i < N → ∀ j, j < N → r i j = rowSum N A B i j := by
  intro i
  induction i with
  | zero =>
    intro hi j hj
    rw [hv.row0 j hj]
    simp [rowSum, bx, hj]
  | succ i ih =>
    intro hi j hj
    rw [rowSum_succ]
    by_cases hjN : j + 1 < N
    · rw [hv.row_def (i + 1) (by omega) hi j hjN]
      simp only [Nat.add_sub_cancel]
      rw [ih (by omega) (j + 1) hjN]
      simp [hj]
    · have hj' : j = N - 1 := by omega
      subst hj'
      rw [hv.row_top (i + 1) (by omega) hi, rowSum_big (N := N) (i := i) (j := N - 1 + 1) (by omega)]
      simp [hj]

theorem view_spec {N : Nat} (hN : 1 ≤ N) {A B : Nat → Bool} {P : Nat → Bool} {r : Nat → Nat → Bool}
    (hv : View N A B P r) :
    ∀ k, k < 2 * N - 1 →
      P k = bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) N) N := by
  intro k hk
  have inner : (fun i => bx (fun j => decide (i + j = k) && A i && B j) N)
      = (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) := by
    funext i
    exact bx_pair i k (A i) B N
  rw [inner]
  by_cases hkN : k < N
  · rw [hv.p_low k hkN, view_row hv k hkN 0 (by omega)]
    unfold rowSum
    rw [bx_trunc (f := fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) (n := k + 1) (m := N)
      (by omega) (fun j hj1 _ => by simp; omega)]
    apply bx_congr
    intro t ht
    have h1 : k + 0 - t = k - t := by omega
    have h2 : decide (k - t < N) = true := by simp; omega
    have h3 : decide (t ≤ k ∧ k - t < N) = true := by simp; omega
    rw [h1, h2, h3]
  · obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    rw [hv.p_high m (by omega), view_row hv (N - 1) (by omega) (m + 1) (by omega)]
    unfold rowSum
    have e : N - 1 + 1 = N := by omega
    rw [e]
    apply bx_congr
    intro t ht
    have e1 : N - 1 + (m + 1) = N + m := by omega
    rw [e1]
    have h3 : decide (t ≤ N + m ∧ N + m - t < N) = decide (N + m - t < N) := by
      apply decide_eq_decide.mpr; omega
    rw [h3]


/-! ## One level of Karatsuba -/

/-- The carry-less product of two `n`-bit operands, bit `k`: the double sum of the Spec. -/
def cl (n : Nat) (A B : Nat → Bool) (k : Nat) : Bool :=
  bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) n) n

theorem bx_add (f : Nat → Bool) (m n : Nat) :
    bx f (m + n) = (bx f m ^^ bx (fun t => f (m + t)) n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [← Nat.add_assoc, bx_succ, ih, bx_succ]
    cases bx f m <;> cases bx (fun t => f (m + t)) n <;> cases f (m + n) <;> rfl

theorem bx_xor (f g : Nat → Bool) (n : Nat) :
    bx (fun t => f t ^^ g t) n = (bx f n ^^ bx g n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [bx_succ, ih, bx_succ, bx_succ]
    cases bx f n <;> cases bx g n <;> cases f n <;> cases g n <;> rfl

theorem bx_and (c : Bool) (f : Nat → Bool) (n : Nat) :
    bx (fun t => c && f t) n = (c && bx f n) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    rw [bx_succ, ih, bx_succ]
    cases c <;> cases bx f n <;> cases f n <;> rfl

theorem cl_big {n : Nat} {A B : Nat → Bool} {k : Nat} (hk : 2 * n ≤ k + 1) : cl n A B k = false := by
  unfold cl
  apply bx_false
  intro i hi
  apply bx_false
  intro j hj
  have : ¬ (i + j = k) := by omega
  simp [this]

/-- A double sum shifted by `s`: only `k ≥ s` sees it, at `k - s`. -/
theorem cl_shift (n s k : Nat) (P Q : Nat → Bool) :
    bx (fun i => bx (fun j => decide (i + j + s = k) && P i && Q j) n) n =
      (decide (s ≤ k) && cl n P Q (k - s)) := by
  by_cases h : s ≤ k
  · have e : ∀ i j, decide (i + j + s = k) = decide (i + j = k - s) := by
      intro i j; apply decide_eq_decide.mpr; omega
    simp only [e, h, decide_true, Bool.true_and]
    rfl
  · have e : ∀ i j, decide (i + j + s = k) = false := by
      intro i j; simp; omega
    have h' : decide (s ≤ k) = false := by simp; omega
    simp only [e, h', Bool.false_and]
    apply bx_false; intro i hi; apply bx_false; intro j hj; rfl

theorem cl_sum (H : Nat) (X Y : Nat → Bool) (m : Nat) :
    cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) m =
      (cl H X Y m ^^ (cl H X (fun j => Y (H + j)) m ^^ (cl H (fun i => X (H + i)) Y m ^^
        cl H (fun i => X (H + i)) (fun j => Y (H + j)) m))) := by
  unfold cl
  have e : ∀ i j, (decide (i + j = m) && (X i ^^ X (H + i)) && (Y j ^^ Y (H + j))) =
      ((decide (i + j = m) && X i && Y j) ^^ ((decide (i + j = m) && X i && Y (H + j)) ^^
        ((decide (i + j = m) && X (H + i) && Y j) ^^ (decide (i + j = m) && X (H + i) && Y (H + j))))) := by
    intro i j
    cases decide (i + j = m) <;> cases X i <;> cases X (H + i) <;> cases Y j <;> cases Y (H + j) <;> rfl
  simp only [e, bx_xor]

theorem karatsuba (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) ^^
          ((decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) ^^
            (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)))))) := by
  have h1 : ∀ i, bx (fun j => decide (i + j = k) && X i && Y j) (H + H) =
      (bx (fun j => decide (i + j = k) && X i && Y j) H ^^
        bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) := fun i => bx_add _ H H
  have h2 : ∀ t, bx (fun j => decide (H + t + j = k) && X (H + t) && Y j) (H + H) =
      (bx (fun j => decide (H + t + j = k) && X (H + t) && Y j) H ^^
        bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) := fun t => bx_add _ H H
  have hA01 : bx (fun i => bx (fun u => decide (i + (H + u) = k) && X i && Y (H + u)) H) H =
      (decide (H ≤ k) && cl H X (fun j => Y (H + j)) (k - H)) := by
    have e : ∀ i u, decide (i + (H + u) = k) = decide (i + u + H = k) := by
      intro i u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k X (fun j => Y (H + j))
  have hA10 : bx (fun t => bx (fun u => decide (H + t + u = k) && X (H + t) && Y u) H) H =
      (decide (H ≤ k) && cl H (fun i => X (H + i)) Y (k - H)) := by
    have e : ∀ t u, decide (H + t + u = k) = decide (t + u + H = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H H k (fun i => X (H + i)) Y
  have hA11 : bx (fun t => bx (fun u => decide (H + t + (H + u) = k) && X (H + t) && Y (H + u)) H) H =
      (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))) := by
    have e : ∀ t u, decide (H + t + (H + u) = k) = decide (t + u + (H + H) = k) := by
      intro t u; apply decide_eq_decide.mpr; omega
    simp only [e]
    exact cl_shift H (H + H) k (fun i => X (H + i)) (fun j => Y (H + j))
  show bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) (H + H)) (H + H) = _
  rw [bx_add]
  simp only [h1, h2, bx_xor]
  rw [hA01, hA10, hA11]
  have hL : cl H X Y k = bx (fun i => bx (fun j => decide (i + j = k) && X i && Y j) H) H := rfl
  rw [hL]
  simp only [Bool.xor_assoc]

theorem karatsuba_full (H : Nat) (X Y : Nat → Bool) (k : Nat) :
    cl (H + H) X Y k =
      (cl H X Y k ^^
        ((decide (H ≤ k) && (cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (k - H) ^^
            cl H X Y (k - H) ^^ cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H))) ^^
          (decide (H + H ≤ k) && cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H))))) := by
  rw [karatsuba, cl_sum]
  generalize cl H X Y k = l0
  generalize cl H X Y (k - H) = l1
  generalize cl H X (fun j => Y (H + j)) (k - H) = a
  generalize cl H (fun i => X (H + i)) Y (k - H) = b
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - H) = h1
  generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (k - (H + H)) = h2
  generalize decide (H ≤ k) = c1
  generalize decide (H + H ≤ k) = c2
  cases l0 <;> cases l1 <;> cases a <;> cases b <;> cases h1 <;> cases h2 <;> cases c1 <;> cases c2 <;> rfl


theorem cl_congr {n : Nat} {A A' B B' : Nat → Bool} (hA : ∀ i, i < n → A i = A' i)
    (hB : ∀ j, j < n → B j = B' j) (k : Nat) : cl n A B k = cl n A' B' k := by
  unfold cl
  apply bx_congr
  intro i hi
  apply bx_congr
  intro j hj
  rw [hA i hi, hB j hj]

/-- Operands that vanish from `N` on: the sums over `M ≥ N` positions see only the first `N`. -/
theorem cl_trunc {N M : Nat} (hNM : N ≤ M) {A B : Nat → Bool} (hA : ∀ i, N ≤ i → A i = false)
    (hB : ∀ j, N ≤ j → B j = false) (k : Nat) : cl M A B k = cl N A B k := by
  unfold cl
  have inner : ∀ i, bx (fun j => decide (i + j = k) && A i && B j) M =
      bx (fun j => decide (i + j = k) && A i && B j) N := by
    intro i
    apply bx_trunc hNM
    intro j hj _
    rw [hB j hj]; simp
  simp only [inner]
  apply bx_trunc hNM
  intro i hi _
  rw [bx_false]
  intro j hj
  rw [hA i hi]; simp

theorem comb_spec {H : Nat} (hH : 1 ≤ H) {X Y : Nat → Bool} {PL PH PM PF : Nat → Bool}
    (hL : ∀ k, k < 2 * H - 1 → PL k = cl H X Y k)
    (hHh : ∀ k, k < 2 * H - 1 → PH k = cl H (fun i => X (H + i)) (fun j => Y (H + j)) k)
    (hM : ∀ k, k < 2 * H - 1 → PM k = cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) k)
    (c0 : ∀ i, i < H → PF i = PL i)
    (c1 : ∀ i, i + 1 < H → PF (H + i) = (PL (H + i) ^^ (PM i ^^ PL i ^^ PH i)))
    (c1' : PF (2 * H - 1) = (PM (H - 1) ^^ PL (H - 1) ^^ PH (H - 1)))
    (c2 : ∀ i, i + 1 < H → PF (2 * H + i) = (PH i ^^ (PM (H + i) ^^ PL (H + i) ^^ PH (H + i))))
    (c3 : ∀ i, i < H → PF (3 * H - 1 + i) = PH (H - 1 + i)) :
    ∀ k, k < 4 * H - 1 → PF k = cl (H + H) X Y k := by
  intro k hk
  rw [karatsuba_full]
  have big : ∀ (A B : Nat → Bool) m, 2 * H - 1 ≤ m → cl H A B m = false :=
    fun A B m hm => cl_big (by omega)
  by_cases h1 : k < H
  · have d1 : decide (H ≤ k) = false := by simp; omega
    have d2 : decide (H + H ≤ k) = false := by simp; omega
    rw [c0 k h1, hL k (by omega), d1, d2]; simp
  by_cases h2 : k < 2 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = H + i := ⟨k - H, by omega⟩
    have d1 : decide (H ≤ H + i) = true := by simp
    have d2 : decide (H + H ≤ H + i) = false := by simp; omega
    have e1 : H + i - H = i := by omega
    rw [c1 i (by omega), hL (H + i) h2, hL i (by omega), hHh i (by omega), hM i (by omega), d1, d2, e1]
    simp
  by_cases h3 : k = 2 * H - 1
  · subst h3
    have d1 : decide (H ≤ 2 * H - 1) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H - 1) = false := by simp; omega
    have e1 : 2 * H - 1 - H = H - 1 := by omega
    rw [c1', hM (H - 1) (by omega), hL (H - 1) (by omega), hHh (H - 1) (by omega), d1, d2, e1,
      big X Y (2 * H - 1) (by omega)]
    simp
  by_cases h4 : k < 3 * H - 1
  · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * H + i := ⟨k - 2 * H, by omega⟩
    have d1 : decide (H ≤ 2 * H + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 2 * H + i) = true := by simp; omega
    have e1 : 2 * H + i - H = H + i := by omega
    have e2 : 2 * H + i - (H + H) = i := by omega
    rw [c2 i (by omega), hHh i (by omega), hM (H + i) (by omega), hL (H + i) (by omega),
      hHh (H + i) (by omega), d1, d2, e1, e2, big X Y (2 * H + i) (by omega)]
    simp only [Bool.true_and, Bool.false_xor]
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) i = a
    generalize cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (H + i) = m
    generalize cl H X Y (H + i) = l
    generalize cl H (fun i => X (H + i)) (fun j => Y (H + j)) (H + i) = h
    cases a <;> cases m <;> cases l <;> cases h <;> rfl
  · obtain ⟨i, rfl⟩ : ∃ i, k = 3 * H - 1 + i := ⟨k - (3 * H - 1), by omega⟩
    have d1 : decide (H ≤ 3 * H - 1 + i) = true := by simp; omega
    have d2 : decide (H + H ≤ 3 * H - 1 + i) = true := by simp; omega
    have e1 : 3 * H - 1 + i - H = 2 * H - 1 + i := by omega
    have e2 : 3 * H - 1 + i - (H + H) = H - 1 + i := by omega
    have bm : cl H (fun i => X i ^^ X (H + i)) (fun j => Y j ^^ Y (H + j)) (2 * H - 1 + i) = false :=
      big _ _ _ (by omega)
    have bl : cl H X Y (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bh : cl H (fun i => X (H + i)) (fun j => Y (H + j)) (2 * H - 1 + i) = false := big _ _ _ (by omega)
    have bl0 : cl H X Y (3 * H - 1 + i) = false := big _ _ _ (by omega)
    rw [c3 i (by omega), hHh (H - 1 + i) (by omega), d1, d2, e1, e2, bm, bl, bh, bl0]
    simp

end ClmulArith
