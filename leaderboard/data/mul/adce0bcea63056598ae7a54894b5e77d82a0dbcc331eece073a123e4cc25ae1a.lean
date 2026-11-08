import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Radix-4 Booth multiplier: the arithmetic (plain Lean, `CombLib` only)

Row `k` of the Booth tape is `niceK` (`k ≥ 1`) or `nice0` (`k = 0`), a function of the column
built from `decide`s; `rowA` is its magnitude-XOR-sign window. `booth_rows` is the identity
`Σ_k row_k = a·b + 2^(2K+N+1)` (as integers), which is `a·b` modulo `2^(2N)`.
-/

namespace BoothArith
open LeanModels.Sv.CombLib

/-! ## A `bfVal` toolkit -/

theorem bfVal_false {f : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = false) : bfVal f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]
    simp

theorem bfVal_lt (f : Nat → Bool) (n : Nat) : bfVal f n < 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, Nat.pow_succ]
    have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n := by
      rcases Bool.eq_false_or_eq_true (f n) with h | h <;> simp [h]
    omega

theorem bfVal_mod (f : Nat → Bool) {n m : Nat} (h : n ≤ m) : bfVal f m % 2 ^ n = bfVal f n := by
  obtain ⟨d, rfl⟩ : ∃ d, m = n + d := ⟨m - n, by omega⟩
  rw [bfVal_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bfVal_lt f n)]

/-- An OR of two functions with disjoint supports is a sum. -/
theorem bfVal_or {h f g : Nat → Bool} (n : Nat) (hfg : ∀ c, h c = (f c || g c))
    (hd : ∀ c, f c = true → g c = true → False) :
    bfVal h n = bfVal f n + bfVal g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih, hfg n]
    rcases Bool.eq_false_or_eq_true (f n) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (g n) with h2 | h2
    · exact (hd n h1 h2).elim
    all_goals (simp only [h1, h2, Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or,
      Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega)

theorem bfVal_pt (q n : Nat) (hn : q < n) : bfVal (fun j => decide (j = q)) n = 2 ^ q := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [bfVal]
    by_cases h : n = q
    · have h0 : bfVal (fun j => decide (j = q)) n = 0 :=
        bfVal_false (fun j hj => decide_eq_false (by omega))
      rw [h0, h]
      simp
    · rw [ih (by omega), decide_eq_false h]
      simp

theorem bfVal_ptc (y : Bool) (q n : Nat) (hn : q < n) :
    bfVal (fun c => y && decide (c = q)) n = y.toNat * 2 ^ q := by
  cases y
  · have h0 : bfVal (fun c => false && decide (c = q)) n = 0 := bfVal_false (fun _ _ => rfl)
    rw [h0]; simp
  · have h1 : bfVal (fun c => true && decide (c = q)) n = bfVal (fun c => decide (c = q)) n :=
      bfVal_congr (fun _ _ => rfl)
    rw [h1, bfVal_pt q n hn]; simp

theorem bfVal_not (f : Nat → Bool) (n : Nat) :
    bfVal (fun j => !f j) n + bfVal f n + 1 = 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, Nat.pow_succ]
    rcases Bool.eq_false_or_eq_true (f n) with h | h <;>
      simp only [h, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
        Nat.mul_one, Nat.mul_zero, Nat.add_zero] <;> omega

/-- A function supported on `[lo, lo + w)`, read at offset `lo`. -/
theorem bfVal_window (f : Nat → Bool) (lo w n : Nat) (hn : lo + w ≤ n)
    (hlo : ∀ c, c < lo → f c = false) (hhi : ∀ c, lo + w ≤ c → f c = false) :
    bfVal f n = 2 ^ lo * bfVal (fun j => f (lo + j)) w := by
  obtain ⟨r, rfl⟩ : ∃ r, n = lo + (w + r) := ⟨n - lo - w, by omega⟩
  have h3 : bfVal f lo = 0 := bfVal_false (fun j hj => hlo j hj)
  have h4 : bfVal (fun j => f (lo + (w + j))) r = 0 :=
    bfVal_false (fun j _ => hhi _ (by omega))
  rw [bfVal_split f lo (w + r), bfVal_split (fun j => f (lo + j)) w r, h3]
  simp only [h4, Nat.mul_zero, Nat.add_zero, Nat.zero_add]

/-! ## The magnitude `|d|·a` on `N+1` bits -/

theorem bfVal_mag {N : Nat} (a : BitVec N) (one two : Bool) (h12 : (one && two) = false) :
    bfVal (fun j => (one && a.getLsbD j) || (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))) (N + 1) =
      one.toNat * a.toNat + two.toNat * (2 * a.toNat) := by
  have ha : a.toNat < 2 ^ (N + 1) := by
    have h1 := a.isLt
    have h2 : 2 ^ N < 2 ^ (N + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hA : bfVal (fun j => a.getLsbD j) (N + 1) = a.toNat := by
    rw [bfVal_bv_mod a (N + 1), Nat.mod_eq_of_lt ha]
  have hB : bfVal (fun j => decide (1 ≤ j) && a.getLsbD (j - 1)) (N + 1) = 2 * a.toNat := by
    rw [bfVal_shift]
    have e : bfVal (fun j => decide (1 ≤ j + 1) && a.getLsbD (j + 1 - 1)) N = a.toNat := by
      rw [← bfVal_bv a]
      exact bfVal_congr (fun j _ => by simp)
    simp only [e]
    simp
  cases one <;> cases two
  · simp only [Bool.false_and, Bool.false_or]
    rw [bfVal_false (fun _ _ => rfl)]; simp
  · have e : bfVal (fun j => (false && a.getLsbD j) || (true && (decide (1 ≤ j) && a.getLsbD (j - 1))))
        (N + 1) = bfVal (fun j => decide (1 ≤ j) && a.getLsbD (j - 1)) (N + 1) :=
      bfVal_congr (fun _ _ => by simp)
    rw [e, hB]; simp
  · have e : bfVal (fun j => (true && a.getLsbD j) || (false && (decide (1 ≤ j) && a.getLsbD (j - 1))))
        (N + 1) = bfVal (fun j => a.getLsbD j) (N + 1) :=
      bfVal_congr (fun _ _ => by simp)
    rw [e, hA]; simp
  · simp at h12

/-! ## One Booth row -/

/-- The magnitude window of row `k`, XORed with the sign `s`: columns `2k .. 2k+N`. -/
def rowA (N : Nat) (a : BitVec N) (one two s : Bool) (k c : Nat) : Bool :=
  ((one && (decide (2 * k ≤ c) && a.getLsbD (c - 2 * k))) ||
    (two && (decide (2 * k + 1 ≤ c) && a.getLsbD (c - (2 * k + 1))))) ^^
  (s && (decide (2 * k ≤ c) && decide (c - 2 * k < N + 1)))

/-- Row `k ≥ 1`: the window, `~s` at `2k+N+1`, a constant one at `2k+N+2`, and the previous row's
two's-complement `+1`, `s'`, at `2k-2`. -/
def niceK (N : Nat) (a : BitVec N) (one two s s' : Bool) (k c : Nat) : Bool :=
  (((rowA N a one two s k c || (!s && decide (c = 2 * k + N + 1))) ||
    decide (c = 2 * k + N + 2)) || (s' && decide (c = 2 * k - 2)))

/-- Row `0`: the window, then `s s ~s` at `N+1 .. N+3`. -/
def nice0 (N : Nat) (a : BitVec N) (one two s : Bool) (c : Nat) : Bool :=
  (((rowA N a one two s 0 c || (s && decide (c = N + 1))) || (s && decide (c = N + 2))) ||
    (!s && decide (c = N + 3)))

theorem rowA_supp {N : Nat} (a : BitVec N) (one two s : Bool) (k c : Nat)
    (h : rowA N a one two s k c = true) : 2 * k ≤ c ∧ c < 2 * k + (N + 1) := by
  by_cases h1 : 2 * k ≤ c
  · by_cases h2 : c < 2 * k + (N + 1)
    · exact ⟨h1, h2⟩
    · exfalso
      have e1 : a.getLsbD (c - 2 * k) = false := BitVec.getLsbD_of_ge a _ (by omega)
      have e2 : a.getLsbD (c - (2 * k + 1)) = false := BitVec.getLsbD_of_ge a _ (by omega)
      have e3 : decide (c - 2 * k < N + 1) = false := decide_eq_false (by omega)
      simp only [rowA, e1, e2, e3, Bool.and_false, Bool.or_false, Bool.xor_false] at h <;>
        simp at h
  · exfalso
    have e1 : decide (2 * k ≤ c) = false := decide_eq_false h1
    have e2 : decide (2 * k + 1 ≤ c) = false := decide_eq_false (by omega)
    simp only [rowA, e1, e2, Bool.false_and, Bool.and_false, Bool.or_false, Bool.xor_false] at h <;>
      simp at h

theorem rowA_shift {N : Nat} (a : BitVec N) (one two s : Bool) (k j : Nat) (hj : j < N + 1) :
    rowA N a one two s k (2 * k + j) =
      (((one && a.getLsbD j) || (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))) ^^ s) := by
  have e1 : 2 * k + j - 2 * k = j := by omega
  have e2 : 2 * k + j - (2 * k + 1) = j - 1 := by omega
  have e3 : decide (2 * k ≤ 2 * k + j) = true := decide_eq_true (by omega)
  have e4 : decide (j < N + 1) = true := decide_eq_true hj
  have e5 : decide (2 * k + 1 ≤ 2 * k + j) = decide (1 ≤ j) := by
    by_cases hh : 1 ≤ j
    · rw [decide_eq_true hh, decide_eq_true (show 2 * k + 1 ≤ 2 * k + j by omega)]
    · rw [decide_eq_false hh, decide_eq_false (show ¬ (2 * k + 1 ≤ 2 * k + j) by omega)]
  simp only [rowA, e1, e2, e3, e4, e5, Bool.true_and, Bool.and_true]

theorem rowA_window {N : Nat} (a : BitVec N) (one two s : Bool) (k W : Nat) (hW : 2 * k + (N + 1) ≤ W) :
    bfVal (rowA N a one two s k) W =
      2 ^ (2 * k) * bfVal (fun j => ((one && a.getLsbD j) ||
        (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))) ^^ s) (N + 1) := by
  have hz : ∀ c, ¬(2 * k ≤ c ∧ c < 2 * k + (N + 1)) → rowA N a one two s k c = false := by
    intro c hc
    rcases Bool.eq_false_or_eq_true (rowA N a one two s k c) with h | h
    · exact absurd (rowA_supp a one two s k c h) hc
    · exact h
  rw [bfVal_window (rowA N a one two s k) (2 * k) (N + 1) W hW (fun c hc => hz c (by omega))
    (fun c hc => hz c (by omega))]
  congr 1
  exact bfVal_congr (fun j hj => rowA_shift a one two s k j hj)

/-- The window with sign `0`: the magnitude. -/
theorem rowA_val_f {N : Nat} (a : BitVec N) (one two : Bool) (h12 : (one && two) = false)
    (k W : Nat) (hW : 2 * k + (N + 1) ≤ W) :
    bfVal (rowA N a one two false k) W =
      2 ^ (2 * k) * (one.toNat * a.toNat + two.toNat * (2 * a.toNat)) := by
  rw [rowA_window a one two false k W hW, ← bfVal_mag a one two h12]
  congr 1
  exact bfVal_congr (fun j _ => Bool.xor_false _)

/-- The window with sign `1`: the complement of the magnitude on `N+1` bits. -/
theorem rowA_val_t {N : Nat} (a : BitVec N) (one two : Bool) (h12 : (one && two) = false)
    (k W : Nat) (hW : 2 * k + (N + 1) ≤ W) :
    bfVal (rowA N a one two true k) W + 2 ^ (2 * k) * (one.toNat * a.toNat + two.toNat * (2 * a.toNat))
      + 2 ^ (2 * k) = 2 ^ (2 * k) * 2 ^ (N + 1) := by
  rw [rowA_window a one two true k W hW, ← bfVal_mag a one two h12]
  have e : bfVal (fun j => ((one && a.getLsbD j) || (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))) ^^ true)
      (N + 1) = bfVal (fun j => !((one && a.getLsbD j) || (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))))
      (N + 1) := bfVal_congr (fun j _ => Bool.xor_true _)
  rw [e]
  have hn := bfVal_not (fun j => ((one && a.getLsbD j) || (two && (decide (1 ≤ j) && a.getLsbD (j - 1)))))
    (N + 1)
  rw [← hn, Nat.mul_add, Nat.mul_add, Nat.mul_one]

theorem niceK_val {N : Nat} (a : BitVec N) (one two s s' : Bool) (k : Nat) (hk : 1 ≤ k)
    (W : Nat) (hW : 2 * k + N + 3 ≤ W) :
    bfVal (niceK N a one two s s' k) W = bfVal (rowA N a one two s k) W +
      (!s).toNat * 2 ^ (2 * k + N + 1) + 2 ^ (2 * k + N + 2) + s'.toNat * 2 ^ (2 * k - 2) := by
  have hA := rowA_supp a one two s k
  have s1 : bfVal (fun c => rowA N a one two s k c || (!s && decide (c = 2 * k + N + 1))) W =
      bfVal (rowA N a one two s k) W + bfVal (fun c => !s && decide (c = 2 * k + N + 1)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      have := hA c h1
      simp at h2
      omega)
  have s2 : bfVal (fun c => (rowA N a one two s k c || (!s && decide (c = 2 * k + N + 1))) ||
      decide (c = 2 * k + N + 2)) W =
      bfVal (fun c => rowA N a one two s k c || (!s && decide (c = 2 * k + N + 1))) W +
      bfVal (fun c => decide (c = 2 * k + N + 2)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      simp only [Bool.or_eq_true] at h1
      simp at h2
      rcases h1 with h1 | h1
      · have := hA c h1
        omega
      · simp at h1
        omega)
  have s3 : bfVal (niceK N a one two s s' k) W =
      bfVal (fun c => (rowA N a one two s k c || (!s && decide (c = 2 * k + N + 1))) ||
        decide (c = 2 * k + N + 2)) W + bfVal (fun c => s' && decide (c = 2 * k - 2)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      simp only [Bool.or_eq_true] at h1
      simp at h2
      rcases h1 with (h1 | h1) | h1
      · have := hA c h1
        omega
      · simp at h1
        omega
      · simp at h1
        omega)
  rw [s3, s2, s1, bfVal_ptc (!s) (2 * k + N + 1) W (by omega), bfVal_pt (2 * k + N + 2) W (by omega),
    bfVal_ptc s' (2 * k - 2) W (by omega)]

theorem nice0_val {N : Nat} (a : BitVec N) (one two s : Bool) (W : Nat) (hW : N + 4 ≤ W) :
    bfVal (nice0 N a one two s) W = bfVal (rowA N a one two s 0) W +
      s.toNat * 2 ^ (N + 1) + s.toNat * 2 ^ (N + 2) + (!s).toNat * 2 ^ (N + 3) := by
  have hA := rowA_supp a one two s 0
  have s1 : bfVal (fun c => rowA N a one two s 0 c || (s && decide (c = N + 1))) W =
      bfVal (rowA N a one two s 0) W + bfVal (fun c => s && decide (c = N + 1)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      have := hA c h1
      simp at h2
      omega)
  have s2 : bfVal (fun c => (rowA N a one two s 0 c || (s && decide (c = N + 1))) ||
      (s && decide (c = N + 2))) W =
      bfVal (fun c => rowA N a one two s 0 c || (s && decide (c = N + 1))) W +
      bfVal (fun c => s && decide (c = N + 2)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      simp only [Bool.or_eq_true] at h1
      simp at h2
      rcases h1 with h1 | h1
      · have := hA c h1
        omega
      · simp at h1
        omega)
  have s3 : bfVal (nice0 N a one two s) W =
      bfVal (fun c => (rowA N a one two s 0 c || (s && decide (c = N + 1))) ||
        (s && decide (c = N + 2))) W + bfVal (fun c => !s && decide (c = N + 3)) W :=
    bfVal_or W (fun _ => rfl) (fun c h1 h2 => by
      simp only [Bool.or_eq_true] at h1
      simp at h2
      rcases h1 with (h1 | h1) | h1
      · have := hA c h1
        omega
      · simp at h1
        omega
      · simp at h1
        omega)
  rw [s3, s2, s1, bfVal_ptc s (N + 1) W (by omega), bfVal_ptc s (N + 2) W (by omega),
    bfVal_ptc (!s) (N + 3) W (by omega)]

/-! ## Row values as integers (the Booth digit `d = -2·s + b1 + b0`) -/

theorem rowK_int {N : Nat} (a : BitVec N) (k : Nat) (hk : 1 ≤ k) (s b1 b0 : Bool) (W : Nat)
    (hW : 2 * k + N + 3 ≤ W) :
    (bfVal (niceK N a (b1 ^^ b0) ((s && !b1 && !b0) || (!s && b1 && b0)) s b0 k) W : Int) =
      2 ^ (2 * k) * ((-2 * (s.toNat : Int) + b1.toNat + b0.toNat) * a.toNat)
        - (s.toNat : Int) * 2 ^ (2 * k) + (b0.toNat : Int) * 2 ^ (2 * k - 2)
        + 3 * (2 ^ (2 * k) * 2 ^ (N + 1)) := by
  have hW' : 2 * k + (N + 1) ≤ W := by omega
  have p1 : (2 : Nat) ^ (2 * k + N + 1) = 2 ^ (2 * k) * 2 ^ (N + 1) := Nat.pow_add 2 (2 * k) (N + 1)
  have p2 : (2 : Nat) ^ (2 * k + N + 2) = 2 * (2 ^ (2 * k) * 2 ^ (N + 1)) := by
    rw [Nat.pow_succ 2 (2 * k + N + 1), p1]; omega
  rw [niceK_val a _ _ s b0 k hk W hW, p1, p2]
  cases s
  · have hr := rowA_val_f a (b1 ^^ b0) ((false && !b1 && !b0) || (!false && b1 && b0))
      (by cases b1 <;> cases b0 <;> decide) k W hW'
    have hc := congrArg (fun z : Nat => (z : Int)) hr
    cases b1 <;> cases b0 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.toNat_true,
        Bool.toNat_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero,
        Nat.mul_one] at hc ⊢ <;>
      push_cast at hc ⊢ <;> grind
  · have hr := rowA_val_t a (b1 ^^ b0) ((true && !b1 && !b0) || (!true && b1 && b0))
      (by cases b1 <;> cases b0 <;> decide) k W hW'
    have hc := congrArg (fun z : Nat => (z : Int)) hr
    cases b1 <;> cases b0 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.toNat_true,
        Bool.toNat_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero,
        Nat.mul_one] at hc ⊢ <;>
      push_cast at hc ⊢ <;> grind

theorem row0_int {N : Nat} (a : BitVec N) (s b1 : Bool) (W : Nat) (hW : N + 4 ≤ W) :
    (bfVal (nice0 N a (b1 ^^ false) ((s && !b1 && !false) || (!s && b1 && false)) s) W : Int) =
      (-2 * (s.toNat : Int) + b1.toNat) * a.toNat - (s.toNat : Int) + 2 ^ (N + 3) := by
  have hW' : 2 * 0 + (N + 1) ≤ W := by omega
  rw [nice0_val a _ _ s W hW]
  have p2 : (2 : Nat) ^ (N + 2) = 2 * 2 ^ (N + 1) := by rw [Nat.pow_succ 2 (N + 1)]; omega
  have p3 : (2 : Nat) ^ (N + 3) = 4 * 2 ^ (N + 1) := by
    rw [Nat.pow_succ 2 (N + 2), Nat.pow_succ 2 (N + 1)]; omega
  have p3' : (2 : Int) ^ (N + 3) = 4 * 2 ^ (N + 1) := by
    rw [Int.pow_succ 2 (N + 2), Int.pow_succ 2 (N + 1)]; omega
  rw [p2, p3, p3']
  cases s
  · have hr := rowA_val_f a (b1 ^^ false) ((false && !b1 && !false) || (!false && b1 && false))
      (by cases b1 <;> decide) 0 W hW'
    have hc := congrArg (fun z : Nat => (z : Int)) hr
    cases b1 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.toNat_true,
        Bool.toNat_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero,
        Nat.mul_one, Nat.pow_zero] at hc ⊢ <;>
      push_cast at hc ⊢ <;> grind
  · have hr := rowA_val_t a (b1 ^^ false) ((true && !b1 && !false) || (!true && b1 && false))
      (by cases b1 <;> decide) 0 W hW'
    have hc := congrArg (fun z : Nat => (z : Int)) hr
    cases b1 <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.false_xor, Bool.true_xor, Bool.not_false,
        Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_and, Bool.true_and,
        Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or, Bool.toNat_true,
        Bool.toNat_false, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero,
        Nat.mul_one, Nat.pow_zero] at hc ⊢ <;>
      push_cast at hc ⊢ <;> grind

/-! ## The sum of the rows -/

def isum (F : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum F n + F n

/-- The Booth identity, row by row: after `n ≥ 1` rows the sum is `a` times the recoded prefix of
`b`, minus the pending `+1` of the last row, plus the telescoped sign-extension constants. -/
theorem booth_sum (a : Int) (bb : Nat → Bool) (F : Nat → Int) (N K : Nat)
    (hbb0 : bb 0 = false)
    (hF0 : F 0 = (-2 * ((bb 2).toNat : Int) + (bb 1).toNat) * a - (bb 2).toNat + 2 ^ (N + 3))
    (hFk : ∀ k, 1 ≤ k → k < K → F k =
      2 ^ (2 * k) * ((-2 * ((bb (2 * k + 2)).toNat : Int) + (bb (2 * k + 1)).toNat +
        (bb (2 * k)).toNat) * a)
        - ((bb (2 * k + 2)).toNat : Int) * 2 ^ (2 * k) + ((bb (2 * k)).toNat : Int) * 2 ^ (2 * k - 2)
        + 3 * (2 ^ (2 * k) * 2 ^ (N + 1))) :
    ∀ n, 1 ≤ n → n ≤ K → isum F n =
      a * ((bfVal (fun i => bb (i + 1)) (2 * n) : Int) - ((bb (2 * n)).toNat : Int) * 2 ^ (2 * n))
        - ((bb (2 * n)).toNat : Int) * 2 ^ (2 * n - 2) + 2 ^ (2 * n) * 2 ^ (N + 1) := by
  intro n hn1 hnK
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have hbN : bfVal (fun i => bb (i + 1)) (2 * (0 + 1)) = (bb 1).toNat + 2 * (bb 2).toNat := by
        show bfVal (fun i => bb (i + 1)) 0 + 2 ^ 0 * (bb (0 + 1)).toNat + 2 ^ 1 * (bb (1 + 1)).toNat = _
        simp [bfVal]
      have hb : (bfVal (fun i => bb (i + 1)) (2 * (0 + 1)) : Int) =
          ((bb 1).toNat : Int) + 2 * ((bb 2).toNat : Int) := by
        exact_mod_cast hbN
      have e1 : (2 : Int) ^ (2 * (0 + 1)) = 4 := rfl
      have e2 : (2 : Int) ^ (2 * (0 + 1) - 2) = 1 := rfl
      have e3 : (2 : Int) ^ (N + 3) = 4 * 2 ^ (N + 1) := by
        rw [Int.pow_succ 2 (N + 2), Int.pow_succ 2 (N + 1)]; omega
      have e4 : 2 * (0 + 1) = 2 := rfl
      show isum F 0 + F 0 = _
      rw [show isum F 0 = 0 from rfl, hF0, hb, e1, e2, e3, e4]
      grind
    · have ih := ih hpos (by omega)
      have hF := hFk n hpos (by omega)
      have hbN : bfVal (fun i => bb (i + 1)) (2 * (n + 1)) =
          bfVal (fun i => bb (i + 1)) (2 * n) + 2 ^ (2 * n) * (bb (2 * n + 1)).toNat +
            2 ^ (2 * n + 1) * (bb (2 * n + 2)).toNat := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
        rfl
      have hb : (bfVal (fun i => bb (i + 1)) (2 * (n + 1)) : Int) =
          (bfVal (fun i => bb (i + 1)) (2 * n) : Int) + 2 ^ (2 * n) * ((bb (2 * n + 1)).toNat : Int) +
            2 ^ (2 * n + 1) * ((bb (2 * n + 2)).toNat : Int) := by
        exact_mod_cast hbN
      have e5 : 2 * (n + 1) = 2 * n + 2 := by omega
      have e6 : 2 * n + 2 - 2 = 2 * n := by omega
      have q1 : (2 : Int) ^ (2 * n + 1) = 2 * 2 ^ (2 * n) := by
        rw [Int.pow_succ 2 (2 * n)]; omega
      have q2 : (2 : Int) ^ (2 * n + 2) = 4 * 2 ^ (2 * n) := by
        rw [Int.pow_succ 2 (2 * n + 1), Int.pow_succ 2 (2 * n)]; omega
      have q3 : (2 : Int) ^ (2 * n) = 4 * 2 ^ (2 * n - 2) := by
        obtain ⟨m, hm⟩ : ∃ m, 2 * n = m + 2 := ⟨2 * n - 2, by omega⟩
        rw [hm, show m + 2 - 2 = m by omega, Int.pow_succ 2 (m + 1), Int.pow_succ 2 m]
        omega
      simp only [isum]
      rw [ih, hF, hb, e5, e6, q1, q2]
      generalize (2 : Int) ^ (2 * n - 2) = Z at *
      rw [q3]
      grind

/-! ## The carry-save tape (as in the Wallace reference) -/

theorem csa_row (n : Nat) (x y z s cy sh : Nat → Bool)
    (hs : ∀ c < n + 1, s c = (x c ^^ y c ^^ z c))
    (hcy : ∀ c < n + 1, cy c = ((x c && y c) || (z c && (x c ^^ y c))))
    (hsh0 : sh 0 = false) (hsh : ∀ c, c + 1 < n + 1 → sh (c + 1) = cy c) :
    bfVal s (n + 1) + bfVal sh (n + 1) + 2 ^ (n + 1) * (cy n).toNat =
      bfVal x (n + 1) + bfVal y (n + 1) + bfVal z (n + 1) := by
  have key : ∀ m, m ≤ n + 1 →
      bfVal s m + 2 * bfVal cy m = bfVal x m + bfVal y m + bfVal z m := by
    intro m
    induction m with
    | zero => intro _; simp [bfVal]
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hfa := fullAdder_arith (x m) (y m) (z m)
      rw [← hs m (by omega), ← hcy m (by omega)] at hfa
      simp only [bfVal]
      have : 2 ^ m * ((s m).toNat + 2 * (cy m).toNat) =
          2 ^ m * ((x m).toNat + (y m).toNat + (z m).toNat) := by rw [hfa]
      generalize (s m).toNat = S0 at *
      generalize (cy m).toNat = C0 at *
      generalize (x m).toNat = X0 at *
      generalize (y m).toNat = Y0 at *
      generalize (z m).toNat = Z0 at *
      generalize 2 ^ m = P at *
      grind
  have hsh' : bfVal sh (n + 1) = 2 * bfVal cy n := by
    rw [bfVal_shift, hsh0]
    have : bfVal (fun j => sh (j + 1)) n = bfVal cy n :=
      bfVal_congr (fun j hj => hsh j (by omega))
    rw [this]; simp
  have hk := key (n + 1) (Nat.le_refl _)
  rw [hsh']
  simp only [bfVal, Nat.pow_succ] at hk ⊢
  generalize 2 ^ n = P at *
  generalize (cy n).toNat = C0 at *
  grind

def csum (V : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n + 1 => csum V s n + V (s + n)

theorem csum_front (V : Nat → Nat) (n : Nat) : ∀ s, csum V s (n + 1) = V s + csum V (s + 1) n := by
  induction n with
  | zero => intro s; simp [csum]
  | succ n ih =>
    intro s
    have e : s + 1 + n = s + (n + 1) := by omega
    have e2 : csum V (s + 1) (n + 1) = csum V (s + 1) n + V (s + 1 + n) := rfl
    rw [csum, ih s, e2, e]
    omega

theorem csum_front3 (V : Nat → Nat) (n s : Nat) :
    csum V s (n + 3) = V s + V (s + 1) + V (s + 2) + csum V (s + 3) n := by
  rw [csum_front, csum_front, csum_front]
  simp only [Nat.add_assoc, Nat.reduceAdd]

theorem csum_mod (V G : Nat → Nat) (M n : Nat) (h : ∀ k, k < n → V k = G k % M) :
    csum V 0 n % M = csum G 0 n % M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csum, Nat.zero_add]
    rw [Nat.add_mod, ih (fun k hk => h k (by omega)), h n (by omega), Nat.mod_mod, ← Nat.add_mod]

theorem csum_isum (G : Nat → Nat) (n : Nat) :
    (csum G 0 n : Int) = isum (fun k => (G k : Int)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [csum, isum, Nat.zero_add]
    push_cast
    rw [ih]


/-- **The carry-save tape, generically** (the Wallace reference's queue, `R ≥ 2` live rows of `W`
bits): adder `g < R-2` reads rows `3g, 3g+1, 3g+2` and appends its sum row at `R+2g` and its carry row
at `R+1+2g`; the two rows left at `3R-6`, `3R-5` have the sum of the `R` leaf rows modulo `2^W`.
Any design that writes its partial-product rows into rows `0 .. R-1` of such a tape only has to prove
the value of its leaves. -/
theorem tape_sum (W R : Nat) (hW : 1 ≤ W) (hR : 2 ≤ R) (T : Nat → Nat → Bool)
    (hsum : ∀ g, g < R - 2 → ∀ c, c < W →
      T (R + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar0 : ∀ g, g < R - 2 → T (R + 1 + 2 * g) 0 = false)
    (hcar : ∀ g, g < R - 2 → ∀ c, c < W - 1 →
      T (R + 1 + 2 * g) (c + 1) = ((T (3 * g) c && T (3 * g + 1) c) ||
        (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))) :
    (bfVal (T (3 * R - 6)) W + bfVal (T (3 * R - 5)) W) % 2 ^ W =
      csum (fun m => bfVal (T m) W) 0 R % 2 ^ W := by
  obtain ⟨n, hn⟩ : ∃ n, W = n + 1 := ⟨W - 1, by omega⟩
  let V : Nat → Nat := fun m => bfVal (T m) W
  have hcsa : ∀ g, g < R - 2 → ∃ q, V (R + 2 * g) + V (R + 1 + 2 * g) + 2 ^ W * q =
      V (3 * g) + V (3 * g + 1) + V (3 * g + 2) := by
    intro g hg
    have h := csa_row n (T (3 * g)) (T (3 * g + 1)) (T (3 * g + 2)) (T (R + 2 * g))
      (fun c => (T (3 * g) c && T (3 * g + 1) c) || (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))
      (T (R + 1 + 2 * g))
      (fun c hc => hsum g hg c (by omega)) (fun _ _ => rfl) (hcar0 g hg)
      (fun c hc => hcar g hg c (by omega))
    rw [← hn] at h
    exact ⟨_, by simp only [V]; omega⟩
  have hwin : ∀ g, g ≤ R - 2 → csum V (3 * g) (R - g) % 2 ^ W = csum V 0 R % 2 ^ W := by
    intro g
    induction g with
    | zero => intro _; simp
    | succ g ih =>
      intro hg
      have ih := ih (by omega)
      obtain ⟨q, hq⟩ := hcsa g (by omega)
      have e1 : csum V (3 * g) (R - g) = V (3 * g) + V (3 * g + 1) + V (3 * g + 2) +
          csum V (3 * g + 3) (R - 3 - g) := by
        rw [show R - g = (R - 3 - g) + 3 by omega, csum_front3]
      have e2 : csum V (3 * (g + 1)) (R - (g + 1)) =
          csum V (3 * g + 3) (R - 3 - g) + V (R + 2 * g) + V (R + 1 + 2 * g) := by
        rw [show R - (g + 1) = (R - 3 - g) + 2 by omega, show 3 * (g + 1) = 3 * g + 3 by omega]
        show csum V (3 * g + 3) (R - 3 - g + 1) + V (3 * g + 3 + (R - 3 - g + 1)) = _
        show csum V (3 * g + 3) (R - 3 - g) + V (3 * g + 3 + (R - 3 - g)) +
          V (3 * g + 3 + (R - 3 - g + 1)) = _
        rw [show 3 * g + 3 + (R - 3 - g) = R + 2 * g by omega,
          show 3 * g + 3 + (R - 3 - g + 1) = R + 1 + 2 * g by omega]
      rw [e1] at ih
      rw [e2]
      have h3 : (csum V (3 * g + 3) (R - 3 - g) + V (R + 2 * g) + V (R + 1 + 2 * g) +
          2 ^ W * q) % 2 ^ W =
          (V (3 * g) + V (3 * g + 1) + V (3 * g + 2) + csum V (3 * g + 3) (R - 3 - g)) % 2 ^ W := by
        congr 1; omega
      rw [Nat.add_mul_mod_self_left] at h3
      rw [h3, ih]
  have hlast := hwin (R - 2) (Nat.le_refl _)
  rw [show R - (R - 2) = 2 by omega] at hlast
  have e3 : csum V (3 * (R - 2)) 2 = V (3 * R - 6) + V (3 * R - 5) := by
    show csum V (3 * (R - 2)) 0 + V (3 * (R - 2) + 0) + V (3 * (R - 2) + 1) = _
    rw [show 3 * (R - 2) + 0 = 3 * R - 6 by omega, show 3 * (R - 2) + 1 = 3 * R - 5 by omega]
    simp [csum]
  rw [e3] at hlast
  exact hlast

/-! ## Gather reads of the padded vectors -/

theorem gat_ae {N : Nat} (a : BitVec N) (P lo x c : Nat) (h1 : P ≤ x ↔ lo ≤ c) (h2 : x - P = c - lo) :
    (decide (P ≤ x) && a.getLsbD (x - P)) = (decide (lo ≤ c) && a.getLsbD (c - lo)) := by
  by_cases h : lo ≤ c
  · have h' : P ≤ x := h1.mpr h
    simp [h, h', h2]
  · have h' : ¬ P ≤ x := fun hh => h (h1.mp hh)
    simp [h, h']

theorem gat_wm (P lo x c W : Nat) (h1 : P ≤ x ↔ lo ≤ c) (h2 : x - P = c - lo) :
    (decide (P ≤ x) && decide (x - P < W)) = (decide (lo ≤ c) && decide (c - lo < W)) := by
  by_cases h : lo ≤ c
  · have h' : P ≤ x := h1.mpr h
    simp [h, h', h2]
  · have h' : ¬ P ≤ x := fun hh => h (h1.mp hh)
    simp [h, h']

theorem gat_pt (P x c q : Nat) (h : x = P ↔ c = q) : decide (x = P) = decide (c = q) := by
  by_cases h' : c = q
  · have h'' : x = P := h.mpr h'
    simp [h', h'']
  · have h'' : ¬ x = P := fun hh => h' (h.mp hh)
    simp [h', h'']

/-! ## The whole multiplier -/

theorem booth_mul {N K P : Nat} (hN : 1 ≤ N) (hK1 : N + 2 ≤ 2 * K) (hK2 : 2 * K ≤ N + 3)
    (hP : P = 2 * N + 4)
    (a b : BitVec N) (p : BitVec (2 * N))
    (bb one two ng ae wm pt : Nat → Bool) (T : Nat → Nat → Bool) (C : Nat → Bool)
    (hbb0 : bb 0 = false)
    (hbb1 : ∀ k, k < N → bb (1 + k) = b.getLsbD k)
    (hbb2 : ∀ k, k < 2 * K - N → bb (N + 1 + k) = false)
    (hae1 : ∀ k, k < P → ae k = false)
    (hae2 : ∀ k, k < N → ae (P + k) = a.getLsbD k)
    (hae3 : ∀ k, k < N + 2 → ae (P + N + k) = false)
    (hwm1 : ∀ k, k < P → wm k = false)
    (hwm2 : ∀ k, k < N + 1 → wm (P + k) = true)
    (hwm3 : ∀ k, k < N + 1 → wm (P + N + 1 + k) = false)
    (hpt1 : ∀ k, k < P → pt k = false)
    (hpt2 : pt P = true)
    (hpt3 : ∀ k, k < 2 * N + 1 → pt (P + 1 + k) = false)
    (hng0 : ng 0 = false)
    (hone : ∀ k, k < K → one k = (bb (2 * k + 1) ^^ bb (2 * k)))
    (htwo : ∀ k, k < K → two k = ((bb (2 * k + 2) && !bb (2 * k + 1) && !bb (2 * k)) ||
      (!bb (2 * k + 2) && bb (2 * k + 1) && bb (2 * k))))
    (hng : ∀ k, k < K → ng (k + 1) = bb (2 * k + 2))
    (hr0 : ∀ c, c < 2 * N → T 0 c = ((((((one 0 && ae (c + P)) || (two 0 && ae (c + P - 1))) ^^
      (ng 1 && wm (c + P))) || (ng 1 && pt (c + P - N - 1))) || (ng 1 && pt (c + P - N - 2))) ||
      (!ng 1 && pt (c + P - N - 3))))
    (hrk : ∀ k, 1 ≤ k → k < K → ∀ c, c < 2 * N → T k c = ((((((one k && ae (c + P - 2 * k)) ||
      (two k && ae (c + P - 1 - 2 * k))) ^^ (ng (k + 1) && wm (c + P - 2 * k))) ||
      (!ng (k + 1) && pt (c + P - N - 1 - 2 * k))) || pt (c + P - N - 2 - 2 * k)) ||
      (ng k && pt (c + P + 2 - 2 * k))))
    (hcar0 : ∀ g, g < K - 2 → T (K + 1 + 2 * g) 0 = false)
    (hsum : ∀ g, g < K - 2 → ∀ c, c < 2 * N →
      T (K + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar : ∀ g, g < K - 2 → ∀ c, c < 2 * N - 1 →
      T (K + 1 + 2 * g) (c + 1) = ((T (3 * g) c && T (3 * g + 1) c) ||
        (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c))))
    (hC0 : C 0 = false)
    (hp : ∀ c, c < 2 * N → p.getLsbD c = (T (3 * K - 6) c ^^ T (3 * K - 5) c ^^ C c))
    (hC : ∀ c, c < 2 * N → C (c + 1) =
      ((T (3 * K - 6) c && T (3 * K - 5) c) || (C c && (T (3 * K - 6) c ^^ T (3 * K - 5) c)))) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  -- closed forms of the padded constant vectors
  have hAE : ∀ x, x < 4 * N + 6 → ae x = (decide (P ≤ x) && a.getLsbD (x - P)) := by
    intro x hx
    by_cases h1 : x < P
    · rw [hae1 x h1, decide_eq_false (show ¬ P ≤ x by omega)] <;> simp
    · by_cases h2 : x < P + N
      · obtain ⟨j, rfl⟩ : ∃ j, x = P + j := ⟨x - P, by omega⟩
        rw [hae2 j (by omega), decide_eq_true (show P ≤ P + j by omega), Nat.add_sub_cancel_left] <;>
          simp
      · obtain ⟨j, rfl⟩ : ∃ j, x = P + N + j := ⟨x - P - N, by omega⟩
        rw [hae3 j (by omega), decide_eq_true (show P ≤ P + N + j by omega),
          BitVec.getLsbD_of_ge a (P + N + j - P) (by omega)] <;> simp
  have hWM : ∀ x, x < 4 * N + 6 → wm x = (decide (P ≤ x) && decide (x - P < N + 1)) := by
    intro x hx
    by_cases h1 : x < P
    · rw [hwm1 x h1, decide_eq_false (show ¬ P ≤ x by omega)] <;> simp
    · by_cases h2 : x < P + N + 1
      · obtain ⟨j, rfl⟩ : ∃ j, x = P + j := ⟨x - P, by omega⟩
        rw [hwm2 j (by omega), decide_eq_true (show P ≤ P + j by omega),
          decide_eq_true (show P + j - P < N + 1 by omega)] <;> simp
      · obtain ⟨j, rfl⟩ : ∃ j, x = P + N + 1 + j := ⟨x - P - N - 1, by omega⟩
        rw [hwm3 j (by omega), decide_eq_true (show P ≤ P + N + 1 + j by omega),
          decide_eq_false (show ¬ (P + N + 1 + j - P < N + 1) by omega)] <;> simp
  have hPT : ∀ x, x < 4 * N + 6 → pt x = decide (x = P) := by
    intro x hx
    by_cases h1 : x < P
    · rw [hpt1 x h1, decide_eq_false (show ¬ x = P by omega)]
    · by_cases h2 : x = P
      · rw [h2, hpt2] <;> simp
      · obtain ⟨j, rfl⟩ : ∃ j, x = P + 1 + j := ⟨x - P - 1, by omega⟩
        rw [hpt3 j (by omega), decide_eq_false (show ¬ (P + 1 + j = P) by omega)]
  -- the rows in clean form
  have hT0 : ∀ c, c < 2 * N → T 0 c = nice0 N a (one 0) (two 0) (ng 1) c := by
    intro c hc
    unfold nice0 rowA
    rw [hr0 c hc, hAE (c + P) (by omega), hAE (c + P - 1) (by omega), hWM (c + P) (by omega),
      hPT (c + P - N - 1) (by omega), hPT (c + P - N - 2) (by omega),
      hPT (c + P - N - 3) (by omega),
      gat_ae a P (2 * 0) (c + P) c ⟨fun _ => by omega, fun _ => by omega⟩ (by omega),
      gat_ae a P (2 * 0 + 1) (c + P - 1) c ⟨fun _ => by omega, fun _ => by omega⟩ (by omega),
      gat_wm P (2 * 0) (c + P) c (N + 1) ⟨fun _ => by omega, fun _ => by omega⟩ (by omega),
      gat_pt P (c + P - N - 1) c (N + 1) ⟨fun _ => by omega, fun _ => by omega⟩,
      gat_pt P (c + P - N - 2) c (N + 2) ⟨fun _ => by omega, fun _ => by omega⟩,
      gat_pt P (c + P - N - 3) c (N + 3) ⟨fun _ => by omega, fun _ => by omega⟩]
  have hTk : ∀ k, 1 ≤ k → k < K → ∀ c, c < 2 * N →
      T k c = niceK N a (one k) (two k) (ng (k + 1)) (ng k) k c := by
    intro k hk1 hk2 c hc
    unfold niceK rowA
    rw [hrk k hk1 hk2 c hc, hAE (c + P - 2 * k) (by omega), hAE (c + P - 1 - 2 * k) (by omega),
      hWM (c + P - 2 * k) (by omega), hPT (c + P - N - 1 - 2 * k) (by omega),
      hPT (c + P - N - 2 - 2 * k) (by omega), hPT (c + P + 2 - 2 * k) (by omega),
      gat_ae a P (2 * k) (c + P - 2 * k) c ⟨fun _ => by omega, fun _ => by omega⟩ (by omega),
      gat_ae a P (2 * k + 1) (c + P - 1 - 2 * k) c ⟨fun _ => by omega, fun _ => by omega⟩
        (by omega),
      gat_wm P (2 * k) (c + P - 2 * k) c (N + 1) ⟨fun _ => by omega, fun _ => by omega⟩ (by omega),
      gat_pt P (c + P - N - 1 - 2 * k) c (2 * k + N + 1) ⟨fun _ => by omega, fun _ => by omega⟩,
      gat_pt P (c + P - N - 2 - 2 * k) c (2 * k + N + 2) ⟨fun _ => by omega, fun _ => by omega⟩,
      gat_pt P (c + P + 2 - 2 * k) c (2 * k - 2) ⟨fun _ => by omega, fun _ => by omega⟩]
  -- the encoder in terms of the bits of `bb`
  have hngk : ∀ k, 1 ≤ k → k < K → ng k = bb (2 * k) := by
    intro k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by omega]
    exact hng j (by omega)
  have h01 : one 0 = (bb 1 ^^ false) := by
    rw [hone 0 (by omega)]
    simp only [Nat.mul_zero, Nat.zero_add, hbb0]
  have h02 : two 0 = ((bb 2 && !bb 1 && !false) || (!bb 2 && bb 1 && false)) := by
    rw [htwo 0 (by omega)]
    simp only [Nat.mul_zero, Nat.zero_add, hbb0]
  have h03 : ng 1 = bb 2 := hng 0 (by omega)
  -- the row values
  let Gn : Nat → Nat := fun k => if k = 0 then bfVal (nice0 N a (one 0) (two 0) (ng 1)) (4 * N + 8)
    else bfVal (niceK N a (one k) (two k) (ng (k + 1)) (ng k) k) (4 * N + 8)
  let V : Nat → Nat := fun m => bfVal (T m) (2 * N)
  have hVG : ∀ k, k < K → V k = Gn k % 2 ^ (2 * N) := by
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      show bfVal (T 0) (2 * N) = (if 0 = 0 then _ else _) % 2 ^ (2 * N)
      rw [if_pos rfl, bfVal_mod _ (show 2 * N ≤ 4 * N + 8 by omega)]
      exact bfVal_congr (fun c hc => hT0 c hc)
    · show bfVal (T k) (2 * N) = (if k = 0 then _ else _) % 2 ^ (2 * N)
      rw [if_neg h0, bfVal_mod _ (show 2 * N ≤ 4 * N + 8 by omega)]
      exact bfVal_congr (fun c hc => hTk k (by omega) hk c hc)
  have hF0 : (Gn 0 : Int) = (-2 * ((bb 2).toNat : Int) + (bb 1).toNat) * (a.toNat : Int) -
      (bb 2).toNat + 2 ^ (N + 3) := by
    show ((if 0 = 0 then _ else _ : Nat) : Int) = _
    rw [if_pos rfl, h01, h02, h03]
    exact row0_int a (bb 2) (bb 1) (4 * N + 8) (by omega)
  have hFk : ∀ k, 1 ≤ k → k < K → (Gn k : Int) =
      2 ^ (2 * k) * ((-2 * ((bb (2 * k + 2)).toNat : Int) + (bb (2 * k + 1)).toNat +
        (bb (2 * k)).toNat) * (a.toNat : Int))
        - ((bb (2 * k + 2)).toNat : Int) * 2 ^ (2 * k) + ((bb (2 * k)).toNat : Int) * 2 ^ (2 * k - 2)
        + 3 * (2 ^ (2 * k) * 2 ^ (N + 1)) := by
    intro k hk1 hk2
    show ((if k = 0 then _ else _ : Nat) : Int) = _
    rw [if_neg (show ¬ (k = 0) by omega), hone k hk2, htwo k hk2, hng k hk2, hngk k hk1 hk2]
    exact rowK_int a k hk1 (bb (2 * k + 2)) (bb (2 * k + 1)) (bb (2 * k)) (4 * N + 8) (by omega)
  have hsumI := booth_sum (a.toNat : Int) bb (fun k => (Gn k : Int)) N K hbb0 hF0 hFk K
    (by omega) (Nat.le_refl K)
  have hbbK : bb (2 * K) = false := by
    have h := hbb2 (2 * K - N - 1) (by omega)
    rwa [show N + 1 + (2 * K - N - 1) = 2 * K by omega] at h
  have hB : bfVal (fun i => bb (i + 1)) (2 * K) = b.toNat := by
    have hs := bfVal_split (fun i => bb (i + 1)) N (2 * K - N)
    rw [show N + (2 * K - N) = 2 * K by omega] at hs
    rw [hs]
    have hlo : bfVal (fun i => bb (i + 1)) N = b.toNat := by
      rw [← bfVal_bv b]
      exact bfVal_congr (fun i hi => by rw [show i + 1 = 1 + i by omega]; exact hbb1 i hi)
    have hhi : bfVal (fun j => bb (N + j + 1)) (2 * K - N) = 0 :=
      bfVal_false (fun j hj => by rw [show N + j + 1 = N + 1 + j by omega]; exact hbb2 j hj)
    simp only [hlo, hhi, Nat.mul_zero, Nat.add_zero]
  rw [hbbK, hB] at hsumI
  simp only [Bool.toNat_false] at hsumI
  rw [← csum_isum] at hsumI
  have e : (2 : Int) ^ (2 * K) * 2 ^ (N + 1) = 2 ^ (2 * N) * 2 ^ (2 * K + 1 - N) := by
    rw [← Int.pow_add, ← Int.pow_add]; congr 1; omega
  have hGsum' : (csum Gn 0 K : Int) =
      ((a.toNat * b.toNat + 2 ^ (2 * N) * 2 ^ (2 * K + 1 - N) : Nat) : Int) := by
    rw [hsumI]; push_cast; grind
  have hGsum : csum Gn 0 K = a.toNat * b.toNat + 2 ^ (2 * N) * 2 ^ (2 * K + 1 - N) := by
    exact_mod_cast hGsum'
  have hbase : csum V 0 K % 2 ^ (2 * N) = (a.toNat * b.toNat) % 2 ^ (2 * N) := by
    rw [csum_mod V Gn (2 ^ (2 * N)) K hVG, hGsum, Nat.add_mul_mod_self_left]
  -- the tape (the generic `tape_sum`)
  have hlast : (bfVal (T (3 * K - 6)) (2 * N) + bfVal (T (3 * K - 5)) (2 * N)) % 2 ^ (2 * N) =
      (a.toNat * b.toNat) % 2 ^ (2 * N) :=
    (tape_sum (2 * N) K (by omega) (by omega) T hsum hcar0 hcar).trans hbase
  have hrip := ripple_row (2 * N) (T (3 * K - 6)) (T (3 * K - 5))
    (fun c => T (3 * K - 6) c ^^ T (3 * K - 5) c) p.getLsbD C
    (fun _ _ => rfl) (fun c hc => hp c hc) (fun c hc => hC c hc)
  rw [hC0, bfVal_bv] at hrip
  simp only [Bool.toNat_false, Nat.add_zero] at hrip
  have hlt : p.toNat < 2 ^ (2 * N) := p.isLt
  have hpv : p.toNat = (bfVal (T (3 * K - 6)) (2 * N) + bfVal (T (3 * K - 5)) (2 * N)) % 2 ^ (2 * N) := by
    have := sum_split hlt (t := bfVal (T (3 * K - 6)) (2 * N) + bfVal (T (3 * K - 5)) (2 * N))
      (q := (C (2 * N)).toNat) (by omega)
    exact this.1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hpv]
  exact hlast

end BoothArith

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## Structure: `sv_structure` -/

/-- The rank: `(stage, adder, phase)`. Inputs and the constant vectors, the encoder, the Booth rows,
the carry-save adders in order of `g`, the ripple adder column by column. -/
def boothKey : SiteId → Key
  | .plain _ => (0, 0, 0)
  | .fam "g_enc" _ _ => (1, 0, 0)
  | .fam "g_r0" _ _ => (2, 0, 0)
  | .fam "g_rc" _ _ => (2, 0, 0)
  | .fam "g_csa" _ [g] => (3, g.toNat, 0)
  | .fam "g_sum" _ [g, _] => (3, g.toNat, 0)
  | .fam "g_car" _ [g, _] => (3, g.toNat, 0)
  | .fam "g_fin" 0 [c] => (4, c.toNat, 1)
  | .fam "g_fin" _ [c] => (4, c.toNat, 0)
  | .fam _ _ _ => (4, 0, 0)

set_option maxHeartbeats 1000000 in
theorem booth_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := boothKey)
  -- `sv_rowmajor` leaves `True ∧ _` on the self-disjointness of the row-0 family `g_r0` (a constant
  -- row index in a column loop); `omega` does not read `True`
  all_goals (intros; sv_rowmajor; first | omega | (simp only [true_and, and_true] at *; omega) |
    (simp at *; omega))

/-! ## The ports -/

theorem booth_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface

/-! ## Equations, bridge, coverage -/

set_option maxHeartbeats 1000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := booth_struct N hN'
  refine CombTask.satisfiedAt_of_comb (booth_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_fin_0 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bbits : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i :=
      fun i hi => SvState.boolAt_ofBitVec hB hi
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N) hvp (by omega)
      (fun k hk => (known_p_g_fin_0 k (by omega)).2)]
    congr 2
    refine BoothArith.booth_mul (K := (N + 3) / 2) (P := 2 * N + 4) hN' (by omega) (by omega) rfl
      x y (XF.bv (2 * N) (st.boolAt "p")) (st.boolAt "bb") (st.boolAt "one") (st.boolAt "two")
      (st.boolAt "ng") (st.boolAt "ae") (st.boolAt "wm") (st.boolAt "pt") (st.cell "T" (2 * N))
      (st.boolAt "C") ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · sv_bridge eq_bb_plain_0
    · sv_bridge eq_bb_plain_1 with bbits
    · sv_bridge eq_bb_plain_2
    · sv_bridge eq_ae_plain_3
    · sv_bridge eq_ae_plain_4 with ba
    · sv_bridge eq_ae_plain_5
    · sv_bridge eq_wm_plain_6
    · sv_bridge eq_wm_plain_7
    · sv_bridge eq_wm_plain_8
    · sv_bridge eq_pt_plain_9
    · sv_bridge eq_pt_plain_10
    · sv_bridge eq_pt_plain_11
    · sv_bridge eq_ng_plain_12
    · sv_bridge eq_one_g_enc_0
    · sv_bridge eq_two_g_enc_1
    · sv_bridge eq_ng_g_enc_2
    · sv_bridge eq_T_g_r0_0
    · sv_bridge eq_T_g_rc_0
    · sv_bridge eq_T_g_csa_0
    · sv_bridge eq_T_g_sum_0
    · sv_bridge eq_T_g_car_0
    · sv_bridge eq_C_plain_13
    · sv_bridge eq_p_g_fin_0 with XF.getLsbD_bv
    · sv_bridge eq_C_g_fin_1
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | (intros; rfl) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
