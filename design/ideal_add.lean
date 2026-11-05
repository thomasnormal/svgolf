/-! The MATH of the ideal `add` proof, in plain Lean: what a player should be left with
after `sv_comb` has turned the design into its netlist equations. -/

theorem sum_eq_ofNat {N : Nat} (hN : 1 ≤ N) (x y : BitVec N) (ci : Bool) :
    x + y + (BitVec.ofBool ci).setWidth N =
      BitVec.ofNat N (x.toNat + y.toNat + (BitVec.ofBool ci).toNat) := by
  apply BitVec.eq_of_toNat_eq
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have hc : ci.toNat < 2 ^ N := by have := Bool.toNat_le ci; omega
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hc, Nat.mod_add_mod]

theorem carry_eq_ofNat {N : Nat} (t : Nat) (ht : t < 2 * 2 ^ N) :
    BitVec.ofBool (decide (2 ^ N ≤ t)) = BitVec.ofNat 1 (t / 2 ^ N) := by
  by_cases h : 2 ^ N ≤ t
  · have hq : t / 2 ^ N = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [h, hq]
  · have hq : t / 2 ^ N = 0 := Nat.div_eq_of_lt (by omega)
    simp [h, hq]

/-- THE IDEAL GOAL for `add_n.sv`, as `sv_comb` would leave it: the signals are Lean values,
the hypotheses are the SV's `assign`s transcribed one to one. -/
theorem ideal_add {N : Nat} (hN : 1 ≤ N) (a b : BitVec N) (cin : Bool)
    (c : Nat → Bool) (s : BitVec N) (cout : Bool)
    (hc0 : c 0 = cin)
    (hc : ∀ i < N, c (i + 1) = ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i))))
    (hs : ∀ i < N, s.getLsbD i = (a.getLsbD i ^^ b.getLsbD i ^^ c i))
    (hco : cout = c N) :
    s = BitVec.ofNat N (a.toNat + b.toNat + cin.toNat) ∧
    BitVec.ofBool cout = BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N) := by
  have hcar : ∀ k ≤ N, c k = BitVec.carry k a b cin := by
    intro k
    induction k with
    | zero => intro _; rw [hc0, BitVec.carry_zero]
    | succ k ih =>
      intro hk
      rw [hc k (by omega), ih (by omega), BitVec.carry_succ]
      generalize a.getLsbD k = x
      generalize b.getLsbD k = y
      generalize BitVec.carry k a b cin = z
      revert x y z; decide
  have hS : s = a + b + (BitVec.ofBool cin).setWidth N := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [hs i hi, hcar i (by omega), BitVec.getLsbD_add_add_bool hi, Bool.xor_assoc]
  have h2 : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
  have ht : a.toNat + b.toNat + cin.toNat < 2 * 2 ^ N := by
    have := a.isLt; have := b.isLt; have := Bool.toNat_le cin; omega
  refine ⟨?_, ?_⟩
  · have := sum_eq_ofNat hN a b cin
    simpa [BitVec.toNat_ofBool] using hS.trans this
  · rw [hco, hcar N (Nat.le_refl N), BitVec.carry_width]
    exact carry_eq_ofNat _ ht

/-- THE PRODUCER CONTRACT for `add_n.sv`: what `sv_equations` must deliver from the actual
`add_n.sem N` (settled signals read back as Lean values), one field per `assign` group. -/
structure AddNetlistView (N : Nat) (a b : BitVec N) (cin : Bool)
    (c : Nat → Bool) (s : BitVec N) (cout : Bool) : Prop where
  carry_zero : c 0 = cin
  carry_step : ∀ i < N, c (i + 1) =
    ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i)))
  sum_bit : ∀ i < N, s.getLsbD i = (a.getLsbD i ^^ b.getLsbD i ^^ c i)
  carry_out : cout = c N

/-- The consumer half, against the named contract. -/
theorem ideal_add_view {N : Nat} (hN : 1 ≤ N) {a b : BitVec N} {cin : Bool}
    {c : Nat → Bool} {s : BitVec N} {cout : Bool} (hv : AddNetlistView N a b cin c s cout) :
    s = BitVec.ofNat N (a.toNat + b.toNat + cin.toNat) ∧
    BitVec.ofBool cout = BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N) :=
  ideal_add hN a b cin c s cout hv.carry_zero hv.carry_step hv.sum_bit hv.carry_out
