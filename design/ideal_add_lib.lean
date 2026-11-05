/-! # Gate-level library for svGolf proofs (draft)

Plain Lean (core only; no `LeanModels.Sv`, no Mathlib). The value of a bit function, the
full-adder arithmetic, the ripple-row theorem shared by adders and multipliers, row-major
injectivity, and a lexicographic rank. -/

/-! ## Gate-level library: the value of a bit function -/

/-- `bfVal f n = Σ_{j<n} 2^j · f j`. -/
def bfVal (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => bfVal f n + 2 ^ n * (f n).toNat

theorem bfVal_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = g j) :
    bfVal f n = bfVal g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bfVal_testBit (x n : Nat) : bfVal (x.testBit) n = x % 2 ^ n := by
  induction n with
  | zero => simp [bfVal, Nat.mod_one]
  | succ n ih =>
    simp only [bfVal, ih]
    rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
    rcases h2 with h | h <;> simp [h]

theorem bfVal_bv {w : Nat} (x : BitVec w) : bfVal x.getLsbD w = x.toNat := by
  have : x.getLsbD = x.toNat.testBit := by funext i; rfl
  rw [this, bfVal_testBit, Nat.mod_eq_of_lt x.isLt]

theorem bfVal_shift (f : Nat → Bool) (n : Nat) :
    bfVal f (n + 1) = (f 0).toNat + 2 * bfVal (fun j => f (j + 1)) n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [bfVal, ih, bfVal]
    simp only [Nat.pow_succ]
    generalize (f (n + 1)).toNat = F
    generalize 2 ^ n = P
    grind

theorem bfVal_split (f : Nat → Bool) (m n : Nat) :
    bfVal f (m + n) = bfVal f m + 2 ^ m * bfVal (fun j => f (m + j)) n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [← Nat.add_assoc, bfVal, ih, bfVal, Nat.pow_add]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

theorem bfVal_and (x : Nat → Bool) (y : Bool) (n : Nat) :
    bfVal (fun j => x j && y) n = y.toNat * bfVal x n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    simp only [bfVal, ih]
    cases y <;> simp

/-- One full adder, as arithmetic: `sum + 2·carry = x + y + cin`. -/
theorem fullAdder_arith (x y c : Bool) :
    ((x ^^ y) ^^ c).toNat + 2 * ((x && y) || (c && (x ^^ y))).toNat =
      x.toNat + y.toNat + c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

/-- **A ripple row computes a sum.** `t j = x j ^^ y j`, `s j = t j ^^ c j`,
`c (j+1) = (x j && y j) || (c j && t j)` for `j < N` give
`Σ 2^j s_j + 2^N c_N = Σ 2^j x_j + Σ 2^j y_j + c_0`. -/
theorem ripple_row (N : Nat) (x y t s c : Nat → Bool)
    (ht : ∀ j < N, t j = (x j ^^ y j))
    (hs : ∀ j < N, s j = (t j ^^ c j))
    (hc : ∀ j < N, c (j + 1) = ((x j && y j) || (c j && t j))) :
    bfVal s N + 2 ^ N * (c N).toNat = bfVal x N + bfVal y N + (c 0).toNat := by
  suffices h : ∀ n ≤ N, bfVal s n + 2 ^ n * (c n).toNat = bfVal x n + bfVal y n + (c 0).toNat from
    h N (Nat.le_refl N)
  intro n
  induction n with
  | zero => intro _; simp [bfVal]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    have hfa := fullAdder_arith (x n) (y n) (c n)
    rw [← ht n (by omega)] at hfa
    rw [← hs n (by omega), ← hc n (by omega)] at hfa
    simp only [bfVal, Nat.pow_succ]
    generalize (s n).toNat = S at *
    generalize (c (n + 1)).toNat = C at *
    generalize (c n).toNat = C0 at *
    generalize (x n).toNat = X at *
    generalize (y n).toNat = Y at *
    generalize 2 ^ n = P at *
    -- ih : Σs + P*C0 = Σx + Σy + c0 ; hfa : S + 2*C = X + Y + C0
    have : P * (S + 2 * C) = P * (X + Y + C0) := by rw [hfa]
    simp only [Nat.mul_add, Nat.mul_assoc] at this ⊢
    omega

theorem bfVal_bv_mod {w : Nat} (x : BitVec w) (n : Nat) : bfVal x.getLsbD n = x.toNat % 2 ^ n := by
  have : x.getLsbD = x.toNat.testBit := by funext i; rfl
  rw [this, bfVal_testBit]


/-! ## Row-major windows and ranks -/

/-- A row-major index `i * W + j` with the column in range determines the row and the column.
The one nonlinear fact behind every 2-D window-disjointness goal. -/
theorem rowMajor_inj {W i j i' j' : Nat} (hj : j < W) (hj' : j' < W)
    (h : i * W + j = i' * W + j') : i = i' ∧ j = j' := by
  have hW : 0 < W := by omega
  have h1 : (i * W + j) / W = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hj, Nat.zero_add]
  have h2 : (i' * W + j') / W = i' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hj', Nat.zero_add]
  have hi : i = i' := by rw [← h1, ← h2, h]
  subst hi
  exact ⟨rfl, by omega⟩

/-- Lexicographic order on `(row, column)` pairs: a rank for 2-D dependencies. -/
def lexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem lexLt_wf : WellFounded lexLt := by
  have : lexLt = Prod.Lex (· < ·) (· < ·) := by
    funext p q; apply propext; rw [Prod.lex_def]; rfl
  rw [this]
  exact (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- Reading the previous row, or an earlier column of the same row, decreases `lexLt`. -/
theorem lexLt_prev_row {i j j' : Nat} : lexLt (i, j') (i + 1, j) := Or.inl (Nat.lt_succ_self i)
theorem lexLt_same_row {i j : Nat} : lexLt (i, j) (i, j + 1) := Or.inr ⟨rfl, Nat.lt_succ_self j⟩

/-! ## The bridge from a value equation to a `BitVec` equation -/

/-- If `s < 2^w` and `t = s + 2^w · q`, then `s = t mod 2^w` and `q = t / 2^w`. -/
theorem sum_split {w s q t : Nat} (hs : s < 2 ^ w) (ht : t = s + 2 ^ w * q) :
    s = t % 2 ^ w ∧ q = t / 2 ^ w := by
  subst ht
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hs, Nat.zero_add]

theorem BitVec.eq_ofNat_of_val {w : Nat} (x : BitVec w) {s t : Nat}
    (hx : x.toNat = s) (hs : s = t % 2 ^ w) : x = BitVec.ofNat w t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hx, hs]

theorem Bool.ofBool_eq_ofNat (b : Bool) : BitVec.ofBool b = BitVec.ofNat 1 b.toNat := by
  cases b <;> rfl

/-! # The adder on the bit-function library (draft)

The producer contract, in value form: the sum is a bit function, so no `BitVec.carry` lemma and
no `xor_assoc` step are needed. -/

structure AddView (N : Nat) (a b : BitVec N) (cin : Bool)
    (c s : Nat → Bool) (cout : Bool) : Prop where
  carry_zero : c 0 = cin
  carry_step : ∀ i < N, c (i + 1) =
    ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i)))
  sum_bit : ∀ i < N, s i = (a.getLsbD i ^^ b.getLsbD i ^^ c i)
  carry_out : cout = c N

/-- The adder, as a value equation: `Σ 2^j s_j + 2^N · cout = a + b + cin`. -/
theorem add_value {N : Nat} {a b : BitVec N} {cin : Bool} {c s : Nat → Bool} {cout : Bool}
    (hv : AddView N a b cin c s cout) :
    bfVal s N + 2 ^ N * cout.toNat = a.toNat + b.toNat + cin.toNat := by
  have hr := ripple_row N a.getLsbD b.getLsbD (fun i => a.getLsbD i ^^ b.getLsbD i) s c
    (fun _ _ => rfl) hv.sum_bit hv.carry_step
  rw [hv.carry_zero, bfVal_bv, bfVal_bv] at hr
  rw [hv.carry_out]
  exact hr

/-- The task statement's form, for an adder whose sum port is a `BitVec`. -/
theorem add_spec {N : Nat} {a b : BitVec N} {cin : Bool} {c : Nat → Bool}
    {sv : BitVec N} {cout : Bool} (hv : AddView N a b cin c sv.getLsbD cout) :
    sv = BitVec.ofNat N (a.toNat + b.toNat + cin.toNat) ∧
    BitVec.ofBool cout = BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N) := by
  have hval := add_value hv
  rw [bfVal_bv] at hval
  have ⟨h1, h2⟩ := sum_split sv.isLt hval.symm
  refine ⟨BitVec.eq_ofNat_of_val sv rfl h1, ?_⟩
  rw [Bool.ofBool_eq_ofNat, h2]
