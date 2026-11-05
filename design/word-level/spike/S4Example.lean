import LeanModels.Sv.CombProcEq
import LeanModels.Sv.CombLib
import LeanModels.Sv.Comb2ConcatExample

/-!
B2 spike, part 4 (scratch, no tree edit): closed examples through the glue of part 3 (copied here, so the file
is self-contained): the equations are the ones the extended `sv_equations` would print (MOCKED by hand),
the statements are `add_final`-shaped, at a symbolic width `N`.
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

/-! ## Example 1: `assign y = a + b;` with all three signals `N` bits wide: no marker -/

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- `eq_y_1` as the extended `sv_equations` would print it (bare leaves, context width `N`). -/
theorem add_final {N : Nat} {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ey : ∀ k, k < N → st.boolAt "y" k = XF.addBits N (st.boolAt "a") N (st.boolAt "b") k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = N)
    (hky : ∀ k, k < N → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x + y)) := by
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_addBits ey, bv_of_lookup hA, bv_of_lookup hB]

/-! ## Example 2: `assign y = a + b;` with `y` one bit wider: the `Resize` markers are `XF.zext` -/

theorem add_wide_final {N : Nat} {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ey : ∀ k, k < N + 1 → st.boolAt "y" k =
      XF.addBits (N + 1) (XF.zext N (st.boolAt "a")) (N + 1) (XF.zext N (st.boolAt "b")) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = N + 1)
    (hky : ∀ k, k < N + 1 → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x.setWidth (N + 1) + y.setWidth (N + 1))) := by
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_addBits ey, XF.bv_zext _ (Nat.le_succ N), XF.bv_zext _ (Nat.le_succ N),
    bv_of_lookup hA, bv_of_lookup hB]

/-! ## Example 3: the note's `addw` (section 5.1): `t = a + b + cin; s = t[N-1:0]; cout = t[N]` -/

open Comb2ConcatExample in
theorem addw_final {N : Nat} {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (et : ∀ k, k < N + 1 → st.boolAt "t" k =
      XF.addBits (N + 1)
        (XF.addBits (N + 1) (XF.zext N (st.boolAt "a")) (N + 1) (XF.zext N (st.boolAt "b")))
        (N + 1) (XF.zext 1 (st.boolAt "cin")) k)
    (es : ∀ k, k < N → st.boolAt "s" k = st.boolAt "t" k)
    (eo : st.boolAt "cout" 0 = st.boolAt "t" N)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = N)
    (hks : ∀ k, k < N → KnownBit st "s" k)
    {vc : LVec} (hc : SvState.lookup st "cout" = some vc) (hcw : vc.width = 1)
    (hkc : KnownBit st "cout" 0) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool c0).setWidth N)) ∧
    SvState.lookup st "cout" = some (LVec.ofBitVec
      (BitVec.ofBool (decide (2 ^ N ≤ x.toNat + y.toNat + c0.toNat)))) := by
  have hCi1 : XF.bv 1 (st.boolAt "cin") = BitVec.ofBool c0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec hCi hi]
  -- (1) the (N+1)-bit sum, once
  have hT : XF.bv (N + 1) (st.boolAt "t") =
      x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool c0).setWidth (N + 1) := by
    rw [XF.bv_addBits et, XF.bv_addBits (fun k _ => rfl), XF.bv_zext _ (Nat.le_succ N),
      XF.bv_zext _ (Nat.le_succ N), XF.bv_zext _ (by omega : 1 ≤ N + 1),
      bv_of_lookup hA, bv_of_lookup hB, hCi1]
  -- (2) s and cout read the low N bits and the top bit of it
  have hsv := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  have hcv := SvState.lookup_eq_ofBitVec_bv hc hcw (fun k hk => by
    obtain rfl : k = 0 := by omega
    exact hkc)
  refine ⟨?_, ?_⟩
  · rw [hsv] at hs
    rw [hs, ← cadd_low, ← hT]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [XF.getLsbD_bv hi, es i hi, BitVec.getLsbD_extractLsb']
    simp only [Nat.zero_add]
    rw [XF.getLsbD_bv (by omega)]
    simp [hi]
  · rw [hcv] at hc
    rw [hc]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi, eo, ← cadd_carry, ← hT, XF.getLsbD_bv (by omega)]
    simp

end LeanModels.Sv

#print axioms LeanModels.Sv.add_final
#print axioms LeanModels.Sv.add_wide_final
#print axioms LeanModels.Sv.addw_final
