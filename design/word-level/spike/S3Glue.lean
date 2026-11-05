import LeanModels.Sv.CombProcEq
import LeanModels.Sv.CombLib

/-!
B2 spike, part 3 (scratch, no tree edit): the glue `CombWord` would contain, for a SYMBOLIC width `N`.
From bit equations `∀ k < w, g k = XF.addBits w f w f' k` to `BitVec` addition; zero extension.
-/

namespace LeanModels.Sv
namespace XF

/-- Zero extension of a bit function from `n` bits (what `Expr2.xfBits (.resize ..)` computes). -/
def zext (n : Nat) (f : Nat → Bool) : Nat → Bool := fun j => decide (j < n) && f j

theorem val_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ j, j < n → f j = g j) → val f n = val g n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [val]
      rw [val_congr (fun j hj => h j (by omega)), h n (by omega)]

theorem val_zext (n : Nat) (f : Nat → Bool) : ∀ m, n ≤ m → val (zext n f) m = val f n
  | 0, h => by
      obtain rfl : n = 0 := by omega
      rfl
  | m + 1, h => by
      by_cases hn : n ≤ m
      · simp only [val]
        rw [val_zext n f m hn]
        have : zext n f m = false := by simp [zext]; omega
        simp [this]
      · obtain rfl : n = m + 1 := by omega
        simp only [val]
        rw [val_congr (f := zext (m + 1) f) (g := f) (fun j hj => by simp [zext]; omega)]
        simp [zext]

theorem val_testBit (x : Nat) : ∀ n, val x.testBit n = x % 2 ^ n
  | 0 => by simp [val, Nat.mod_one]
  | n + 1 => by
      simp only [val, val_testBit x n]
      rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
      have h2 : x / 2 ^ n % 2 = 0 ∨ x / 2 ^ n % 2 = 1 := by omega
      rcases h2 with h | h <;> simp [h]

theorem toNat_bv (w : Nat) (f : Nat → Bool) : (bv w f).toNat = val f w := by
  unfold bv
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (val_lt f w)]

theorem bv_congr {w : Nat} {f g : Nat → Bool} (h : ∀ k, k < w → f k = g k) : bv w f = bv w g := by
  unfold bv; rw [val_congr h]

/-- `zext` then `bv`: the `setWidth` of the narrow vector. -/
theorem bv_zext {n m : Nat} (f : Nat → Bool) (h : n ≤ m) : bv m (zext n f) = (bv n f).setWidth m := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_zext n f m h, BitVec.toNat_setWidth, toNat_bv, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (val_lt f n) (Nat.pow_le_pow_right (by omega) h)

/-- **Addition glue.** The bit equations of a sum are `BitVec` addition. -/
theorem bv_addBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = addBits w f w f' k) :
    bv w g = bv w f + bv w f' := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bv, val_congr (g := (val f w + val f' w).testBit) h, val_testBit, BitVec.toNat_add,
    toNat_bv, toNat_bv]

/-- **Subtraction glue.** -/
theorem bv_subBits {w : Nat} {g f f' : Nat → Bool} (h : ∀ k, k < w → g k = subBits w f w f' k) :
    bv w g = bv w f - bv w f' := by
  apply BitVec.eq_of_toNat_eq
  have e : subBits w f w f' = (val f w + (2 ^ w - val f' w)).testBit := by
    funext k; simp [subBits]
  rw [toNat_bv, val_congr (g := (val f w + (2 ^ w - val f' w)).testBit) (fun k hk => by rw [h k hk, e]),
    val_testBit, BitVec.toNat_sub, toNat_bv, toNat_bv]
  congr 1
  omega

end XF
end LeanModels.Sv

#print axioms LeanModels.Sv.XF.bv_addBits
#print axioms LeanModels.Sv.XF.bv_subBits
#print axioms LeanModels.Sv.XF.bv_zext
