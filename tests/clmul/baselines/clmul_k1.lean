import Submission.Design
import tasks.clmul.Spec
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Task `clmul`: one level of Karatsuba, proved for every `N ≥ 1` with the `sv_comb` tactics

The design is `clmul_k1.sv`: with `H = (N + 1) / 2`, the operands are zero-padded to `ap`, `bp` (`2H + 1` bits,
only the low `2H` read), three `H x H` carry-less arrays (the reference's row shape) compute
`L = aL (x) bL`, `Hh = aH (x) bH` and `M = (aL ^ aH) (x) (bL ^ bH)`, and the combination layer writes
`pf = L + x^H (M ^ L ^ Hh) + x^2H Hh`, of which `p` is the low `2N - 1` bits.

## Route

1. **Structure** (`k_struct`): `sv_structure` with a lexicographic key (`kKey`: padding first, then the rows of the
   three arrays by row index, then the combination layer, then the output bits).
2. **Ports** (`k_interface`): `sv_interface`.
3. **Equations** (in `solution`): `sv_equations`; coverage by `sv_cover`.
4. **Arithmetic** (`ClmulArith`, plain Lean): each array satisfies the reference's row invariant (`View`,
   `view_spec`); the one-level Karatsuba identity over coefficient functions (`karatsuba_full`) and the layout of the
   combination layer (`comb_spec`) give the `2H`-bit product of the padded operands; the padding is zero
   (`cl_trunc`), so its low `2N - 1` bits are the Spec's double sum (`coeff_eq`).
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.Clmul

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
  simp

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
      simp [h, h1, h3]
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
    | zero => simp
    | succ k => simp


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
  simp only [h1, bx_xor]
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


/-- Bit `k` of an `H x H` array's product: column 0 of row `k` for `k < H`, the top row from column 1 on. -/
def sel (H : Nat) (r : Nat → Nat → Bool) (k : Nat) : Bool :=
  if k < H then r k 0 else r (H - 1) (k - H + 1)

theorem sel_lo {H : Nat} {r : Nat → Nat → Bool} {k : Nat} (hk : k < H) : sel H r k = r k 0 := by
  simp [sel, hk]

theorem sel_hi {H : Nat} {r : Nat → Nat → Bool} {k : Nat} (hk : H ≤ k) :
    sel H r k = r (H - 1) (k - H + 1) := by
  have : ¬ k < H := by omega
  simp [sel, this]

end ClmulArith

/-! ## Structure -/

def kKey (N : Nat) : SiteId → Key
  | .fam "g_pin" _ _ => (0, 0, 0)
  | .fam "g_pz" _ _ => (0, 0, 0)
  | .fam "g_l0" _ _ => (1, 0, 0)
  | .fam "g_h0" _ _ => (1, 0, 0)
  | .fam "g_m0" _ _ => (1, 0, 0)
  | .fam "g_l" _ [i] => (1, i.toNat, 0)
  | .fam "g_h" _ [i] => (1, i.toNat, 0)
  | .fam "g_m" _ [i] => (1, i.toNat, 0)
  | .fam "g_lb" _ [i, _] => (1, i.toNat, 0)
  | .fam "g_hb" _ [i, _] => (1, i.toNat, 0)
  | .fam "g_mb" _ [i, _] => (1, i.toNat, 0)
  | .fam "g_out" _ _ => (3, 0, 0)
  | _ => (2, 0, N * 0)

set_option maxHeartbeats 0 in
theorem k_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by
  sv_structure (lexRank := kKey N)
  all_goals (intros; sv_rowmajor; first | omega | (simp; omega))

theorem k_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Clmul.task.Interface N (design.sem N) := by
  sv_interface

set_option maxHeartbeats 0 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha⟩ := k_struct N hN'
  refine CombTask.satisfiedAt_of_comb (k_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨H, hHdef⟩ : ∃ H, H = (N + 1) / 2 := ⟨_, rfl⟩
    have hH1 : 1 ≤ H := by omega
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    -- the padded operands
    have hap : ∀ i, i < 2 * H → st.boolAt "ap" i = x.getLsbD i := by
      intro i hi
      by_cases h : i < N
      · rw [eq_ap_g_pin_0 i h, ba i h]
      · obtain ⟨m, rfl⟩ : ∃ m, i = N + m := ⟨i - N, by omega⟩
        have := eq_ap_g_pz_0 m (by omega)
        rw [show ((N : Int) + (m : Int)).toNat = N + m by omega] at this
        rw [this]
        symm; exact BitVec.getLsbD_of_ge x (N + m) (by omega)
    have hbp : ∀ i, i < 2 * H → st.boolAt "bp" i = y.getLsbD i := by
      intro i hi
      by_cases h : i < N
      · rw [eq_bp_g_pin_1 i h, bb i h]
      · obtain ⟨m, rfl⟩ : ∃ m, i = N + m := ⟨i - N, by omega⟩
        have := eq_bp_g_pz_1 m (by omega)
        rw [show ((N : Int) + (m : Int)).toNat = N + m by omega] at this
        rw [this]
        symm; exact BitVec.getLsbD_of_ge y (N + m) (by omega)
    -- the three arrays, their products `sel H r`
    have vL : ClmulArith.View H (st.boolAt "ap") (st.boolAt "bp") (ClmulArith.sel H (st.cell "rl" H))
        (st.cell "rl" H) := by
      refine { row0 := ?_, row_def := ?_, row_top := ?_, p_low := ?_, p_high := ?_ }
      · sv_bridge eq_rl_g_l0_0
      · sv_bridge eq_rl_g_lb_0
      · sv_bridge eq_rl_g_l_1
      · intro i hi; exact ClmulArith.sel_lo hi
      · intro m hm
        rw [ClmulArith.sel_hi (by omega)]
        rw [show H + m - H + 1 = m + 1 by omega]
    have vH : ClmulArith.View H (fun i => st.boolAt "ap" (H + i)) (fun j => st.boolAt "bp" (H + j))
        (ClmulArith.sel H (st.cell "rh" H)) (st.cell "rh" H) := by
      refine { row0 := ?_, row_def := ?_, row_top := ?_, p_low := ?_, p_high := ?_ }
      · sv_bridge eq_rh_g_h0_0
      · sv_bridge eq_rh_g_hb_0
      · sv_bridge eq_rh_g_h_1
      · intro i hi; exact ClmulArith.sel_lo hi
      · intro m hm
        rw [ClmulArith.sel_hi (by omega)]
        rw [show H + m - H + 1 = m + 1 by omega]
    have vM : ClmulArith.View H (fun i => st.boolAt "ap" i ^^ st.boolAt "ap" (H + i))
        (fun j => st.boolAt "bp" j ^^ st.boolAt "bp" (H + j))
        (ClmulArith.sel H (st.cell "rm" H)) (st.cell "rm" H) := by
      refine { row0 := ?_, row_def := ?_, row_top := ?_, p_low := ?_, p_high := ?_ }
      · sv_bridge eq_rm_g_m0_0
      · sv_bridge eq_rm_g_mb_0
      · sv_bridge eq_rm_g_m_1
      · intro i hi; exact ClmulArith.sel_lo hi
      · intro m hm
        rw [ClmulArith.sel_hi (by omega)]
        rw [show H + m - H + 1 = m + 1 by omega]
    -- the combination layer, from the cells
    have d0 : ∀ i, i < H → st.boolAt "pf" i = st.cell "rl" H i 0 := by sv_bridge eq_pf_g_c0_0
    have d1 : ∀ i, i + 1 < H → st.boolAt "pf" (H + i) = (st.cell "rl" H (H - 1) (i + 1) ^^
        (st.cell "rm" H i 0 ^^ st.cell "rl" H i 0 ^^ st.cell "rh" H i 0)) := by
      sv_bridge eq_pf_g_c1_0
    have dm : st.boolAt "pf" (2 * H - 1) = (st.cell "rm" H (H - 1) 0 ^^ st.cell "rl" H (H - 1) 0 ^^
        st.cell "rh" H (H - 1) 0) := by
      sv_bridge (eq_pf_g_cm_0 0 (by omega))
    have d2 : ∀ i, i + 1 < H → st.boolAt "pf" (2 * H + i) = (st.cell "rh" H i 0 ^^
        (st.cell "rm" H (H - 1) (i + 1) ^^ st.cell "rl" H (H - 1) (i + 1) ^^ st.cell "rh" H (H - 1) (i + 1))) := by
      sv_bridge eq_pf_g_c2_0
    have d3 : ∀ i, i < H → st.boolAt "pf" (3 * H - 1 + i) = st.cell "rh" H (H - 1) i := by
      sv_bridge eq_pf_g_c3_0
    have sL := ClmulArith.view_spec hH1 vL
    have sH := ClmulArith.view_spec hH1 vH
    have sM := ClmulArith.view_spec hH1 vM
    have c0 : ∀ i, i < H → st.boolAt "pf" i = ClmulArith.sel H (st.cell "rl" H) i := by
      intro i hi
      rw [ClmulArith.sel_lo hi]; exact d0 i hi
    have c1 : ∀ i, i + 1 < H → st.boolAt "pf" (H + i) =
        (ClmulArith.sel H (st.cell "rl" H) (H + i) ^^ (ClmulArith.sel H (st.cell "rm" H) i ^^
          ClmulArith.sel H (st.cell "rl" H) i ^^ ClmulArith.sel H (st.cell "rh" H) i)) := by
      intro i hi
      rw [d1 i hi, ClmulArith.sel_hi (show H ≤ H + i by omega), ClmulArith.sel_lo (show i < H by omega),
        ClmulArith.sel_lo (show i < H by omega), ClmulArith.sel_lo (show i < H by omega),
        show H + i - H + 1 = i + 1 by omega]
    have c1' : st.boolAt "pf" (2 * H - 1) =
        (ClmulArith.sel H (st.cell "rm" H) (H - 1) ^^ ClmulArith.sel H (st.cell "rl" H) (H - 1) ^^
          ClmulArith.sel H (st.cell "rh" H) (H - 1)) := by
      rw [dm, ClmulArith.sel_lo (show H - 1 < H by omega), ClmulArith.sel_lo (show H - 1 < H by omega),
        ClmulArith.sel_lo (show H - 1 < H by omega)]
    have c2 : ∀ i, i + 1 < H → st.boolAt "pf" (2 * H + i) =
        (ClmulArith.sel H (st.cell "rh" H) i ^^ (ClmulArith.sel H (st.cell "rm" H) (H + i) ^^
          ClmulArith.sel H (st.cell "rl" H) (H + i) ^^ ClmulArith.sel H (st.cell "rh" H) (H + i))) := by
      intro i hi
      rw [d2 i hi, ClmulArith.sel_lo (show i < H by omega), ClmulArith.sel_hi (show H ≤ H + i by omega),
        ClmulArith.sel_hi (show H ≤ H + i by omega), ClmulArith.sel_hi (show H ≤ H + i by omega),
        show H + i - H + 1 = i + 1 by omega]
    have c3 : ∀ i, i < H → st.boolAt "pf" (3 * H - 1 + i) = ClmulArith.sel H (st.cell "rh" H) (H - 1 + i) := by
      intro i hi
      rw [d3 i hi]
      by_cases h0 : i = 0
      · subst h0
        rw [show H - 1 + 0 = H - 1 by omega, ClmulArith.sel_lo (show H - 1 < H by omega)]
      · rw [ClmulArith.sel_hi (show H ≤ H - 1 + i by omega), show H - 1 + i - H + 1 = i by omega]
    have hpf := ClmulArith.comb_spec hH1 (X := st.boolAt "ap") (Y := st.boolAt "bp")
      (PL := ClmulArith.sel H (st.cell "rl" H)) (PH := ClmulArith.sel H (st.cell "rh" H))
      (PM := ClmulArith.sel H (st.cell "rm" H)) (PF := st.boolAt "pf") (fun k hk => sL k hk)
      (fun k hk => sH k hk) (fun k hk => sM k hk) c0 c1 c1' c2 c3
    have hfinal : ∀ k, k < 2 * N - 1 → st.boolAt "p" k = coeff N x y k := by
      intro k hk
      rw [eq_p_g_out_0 k (by omega), hpf k (by omega)]
      rw [ClmulArith.cl_congr (A' := x.getLsbD) (B' := y.getLsbD) (fun i hi => hap i (by omega))
        (fun j hj => hbp j (by omega)) k]
      rw [ClmulArith.cl_trunc (N := N) (M := H + H) (by omega) (A := x.getLsbD) (B := y.getLsbD)
        (fun i hi => BitVec.getLsbD_of_ge x i hi) (fun j hj => BitVec.getLsbD_of_ge y j hj) k]
      exact (ClmulArith.coeff_eq N x y k).symm
    have hkp : ∀ k, k < 2 * N - 1 → KnownBit st "p" k := fun k hk => (known_p_g_out_0 k (by omega)).2
    obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_out_0 0 (by omega)
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N - 1) hvp (by omega) hkp]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, ClmulArith.getLsbD_ofBits, hfinal k hk]
    simp [hk]
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
