import Spec

/-!
# Facts about the draft `keccak_round` statement (UNTRUSTED, kernel-checked like any proof)

What a proof of a design wants from `Spec.lean`: the encoding round trips, and the output bit
`k` of `task.fn` is the round formula at the bit's coordinates.
-/

namespace SvGolf.Tasks.KeccakRound

open SvGolf

theorem getLsbD_ofBits (n : Nat) (f : Nat → Bool) (k : Nat) :
    (ofBits n f).getLsbD k = (decide (k < n) && f k) := by
  induction n generalizing f k with
  | zero => simp [ofBits]
  | succ n ih =>
    rw [ofBits, BitVec.getLsbD_append]
    cases k with
    | zero => simp
    | succ k => simp [ih]

/-- The encoding is inverse on the coordinates a state has: `unpack (pack A) = A` in range. -/
theorem unpack_pack (W : Nat) (hW : 0 < W) (A : Bits) (x y z : Nat)
    (hx : x < 5) (hy : y < 5) (hz : z < W) :
    unpack W (pack W A) x y z = A x y z := by
  have hxy : 5 * y + x ≤ 24 := by omega
  have hm := Nat.mul_le_mul_left W hxy
  have hlt : W * (5 * y + x) + z < 25 * W := by omega
  have h1 : (W * (5 * y + x) + z) / W = 5 * y + x := by
    rw [Nat.mul_add_div hW, Nat.div_eq_of_lt hz]; simp
  have h2 : (W * (5 * y + x) + z) % W = z := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hz]
  have h3 : (5 * y + x) % 5 = x := by omega
  have h4 : (5 * y + x) / 5 = y := by omega
  simp only [unpack, pack, getLsbD_ofBits, h1, h2, h3, h4]
  simp [hlt]

/-- The other direction: `pack (unpack s) = s`. -/
theorem pack_unpack (W : Nat) (s : BitVec (25 * W)) : pack W (unpack W s) = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [pack, getLsbD_ofBits, unpack]
  have : W * (5 * (k / W / 5) + k / W % 5) + k % W = k := by
    have h := Nat.div_add_mod (k / W) 5
    have h' := Nat.div_add_mod k W
    rw [h]; exact h'
  simp [hk, this]

end SvGolf.Tasks.KeccakRound
