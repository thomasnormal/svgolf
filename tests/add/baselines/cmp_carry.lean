import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombWord

/-!
# A proof of `tests/add/baselines/cmp_carry.sv` for task `add`

The design computes every carry by itself, from the inputs, as a comparison of the low bits:

    c[0] = cin
    c[i] = (a[i-1:0] > ~b[i-1:0]) | ((a[i-1:0] == ~b[i-1:0]) & cin)     for 1 ≤ i ≤ N
    s[i] = a[i] ^ b[i] ^ c[i],   cout = c[N]

The proof is for every `N ≥ 1`. The structure, the ports and the equations come from the `sv_comb`
tactics, which read the comparisons as `decide (XF.val … > XF.val …)` and `XF.eqv` over the low `i`
bits. The arithmetic: the low `i` bits of `~b` have the value `2^i - 1 - B_i`, so the assign of `c[i]`
is `c[i] = [A_i + B_i + cin ≥ 2^i]` (`cmp_carry_val`), the carry into bit `i`. These carries satisfy
the ripple recurrence (`carry_val_succ`), so the equations are the library's `CombLib.AddView` and
`CombLib.add_spec` gives the sum. No carry reads another carry, so the rank is two levels.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## 1. Structure and ports -/

/-- `CombDesign` and `Acyclic` for every `N ≥ 1`. The carries `c[i]`, `i ≥ 1`, read only inputs, so
they share rank 0 with `c[0]`; the sum bits and `cout` read carries and get rank 1. -/
theorem cmp_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else 1)
    (fun l _ _ => if l = "g_c" then 0 else 1))
  all_goals (intros; omega)

theorem cmp_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 2. The arithmetic of one comparison -/

/-- A bit function and its complement add up to all ones. -/
theorem val_add_val_not (g : Nat → Bool) :
    ∀ w, XF.val g w + XF.val (fun x => !g x) w + 1 = 2 ^ w
  | 0 => rfl
  | w + 1 => by
    have ih := val_add_val_not g w
    simp only [XF.val, Nat.pow_succ]
    generalize XF.val g w = G at *
    generalize XF.val (fun x => !g x) w = H at *
    generalize 2 ^ w = P at *
    cases g w <;> simp <;> omega

/-- Equality of the low `w` bits is equality of their values. -/
theorem eqv_iff_val {w : Nat} {f g : Nat → Bool} :
    XF.eqv w f g = true ↔ XF.val f w = XF.val g w := by
  rw [XF.eqv_eq_true]
  constructor
  · intro h
    exact XF.val_congr_lt h
  · intro h k hk
    rw [← XF.testBit_val f w k hk, ← XF.testBit_val g w k hk, h]

/-- **The carry as a comparison.** `(f > ~g) | ((f == ~g) & ci)` over the low `w` bits is the carry
out of the `w`-bit sum `f + g + ci`. -/
theorem cmp_carry_val (f g : Nat → Bool) (ci : Bool) (w : Nat) :
    (decide (XF.val f w > XF.val (fun x => !g x) w) ||
        (XF.eqv w f (fun x => !g x) && ci)) =
      decide (2 ^ w ≤ XF.val f w + XF.val g w + ci.toNat) := by
  have h1 := val_add_val_not g w
  have h2 : XF.eqv w f (fun x => !g x) = decide (XF.val f w = XF.val (fun x => !g x) w) := by
    rw [Bool.eq_iff_iff, eqv_iff_val, decide_eq_true_iff]
  rw [h2]
  generalize XF.val f w = A at *
  generalize XF.val g w = G at *
  generalize XF.val (fun x => !g x) w = H at *
  generalize 2 ^ w = P at *
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff, GT.gt]
  cases ci <;> simp <;> omega

/-- One step of the carry, in numbers: with `A, G < P` and `C ≤ 1`, the sum of the next bits
`A + P·a + G + P·b + C` reaches `2P` exactly when `a ∧ b`, or `a ⊕ b` and `A + G + C` reaches `P`. -/
theorem carry_step_nat (A G C P : Nat) (fa gb : Bool) (hA : A < P) (hG : G < P) (hC : C ≤ 1) :
    decide (P * 2 ≤ A + P * fa.toNat + (G + P * gb.toNat) + C) =
      ((fa && gb) || (decide (P ≤ A + G + C) && (fa ^^ gb))) := by
  by_cases h : P ≤ A + G + C <;> cases fa <;> cases gb <;> simp [h] <;> omega

/-- **The ripple recurrence of the comparison carries.** The carry out of the `(i+1)`-bit sum is the
majority of bit `i` of the operands and the carry out of the `i`-bit sum. -/
theorem carry_val_succ (f g : Nat → Bool) (ci : Bool) (i : Nat) :
    decide (2 ^ (i + 1) ≤ XF.val f (i + 1) + XF.val g (i + 1) + ci.toNat) =
      ((f i && g i) || (decide (2 ^ i ≤ XF.val f i + XF.val g i + ci.toNat) && (f i ^^ g i))) := by
  have hc : ci.toNat ≤ 1 := by cases ci <;> decide
  simp only [XF.val, Nat.pow_succ]
  exact carry_step_nat _ _ _ _ _ _ (XF.val_lt f i) (XF.val_lt g i) hc

/-! ## 3. From the equations to the task's outputs -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- **The arithmetic.** From the four equations as `sv_equations` states them (the carry assign
with its comparison over the low `i` bits) and the knownness of `s` and `cout`: the task's outputs. -/
theorem cmp_final {N : Nat} {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (e0 : st.boolAt "c" 0 = st.boolAt "cin" 0)
    (ecmp : ∀ (i : Nat), 1 ≤ (i : Int) → (i : Int) < (N : Int) + 1 →
      st.boolAt "c" i =
        (decide (XF.val (fun x => st.boolAt "a" x) ((i : Int) + -1 + 1).toNat >
            XF.val (fun x => !st.boolAt "b" x) ((i : Int) + -1 + 1).toNat) ||
          (XF.eqv ((i : Int) + -1 + 1).toNat (fun x => st.boolAt "a" x)
            (fun x => !st.boolAt "b" x) && st.boolAt "cin" 0)))
    (esum : ∀ i, i < N → st.boolAt "s" i =
      (st.boolAt "a" i ^^ st.boolAt "b" i ^^ st.boolAt "c" i))
    (eout : st.boolAt "cout" 0 = st.boolAt "c" N)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = N)
    (hks : ∀ k, k < N → KnownBit st "s" k)
    {vc : LVec} (hc : SvState.lookup st "cout" = some vc) (hcw : vc.width = 1)
    (hkc : KnownBit st "cout" 0) :
    SvState.lookup st "s" = some (LVec.ofBitVec
        (BitVec.ofNat N (x.toNat + y.toNat + c0.toNat))) ∧
    SvState.lookup st "cout" = some (LVec.ofBitVec
        (BitVec.ofNat 1 ((x.toNat + y.toNat + c0.toNat) / 2 ^ N))) := by
  have hvs := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  have hvc := SvState.lookup_eq_ofBitVec_bv hc hcw (fun k hk => by
    obtain rfl : k = 0 := by omega
    exact hkc)
  rw [hvs] at hs
  rw [hvc] at hc
  have hxb : XF.bv 1 (st.boolAt "cout") = BitVec.ofBool (st.boolAt "cout" 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi]; simp
  have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
  have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
  have bci : st.boolAt "cin" 0 = c0 := by
    rw [SvState.boolAt_ofBitVec hCi (by omega)]; simp
  -- the invariant: every carry is the carry into its bit of `a + b + cin`
  have hcar : ∀ i, i ≤ N → st.boolAt "c" i =
      decide (2 ^ i ≤ XF.val (fun x => st.boolAt "a" x) i +
        XF.val (fun x => st.boolAt "b" x) i + c0.toNat) := by
    intro i hi
    cases i with
    | zero =>
      rw [e0, bci]
      cases c0 <;> rfl
    | succ j =>
      have h := ecmp (j + 1) (by omega) (by omega)
      rw [show ((((j + 1 : Nat) : Int) + -1 + 1).toNat) = j + 1 by omega, bci] at h
      rw [h, cmp_carry_val]
  have hv : AddView N x y c0 (fun i => st.boolAt "c" i) (XF.bv N (st.boolAt "s")).getLsbD
      (st.boolAt "cout" 0) := by
    refine ⟨by simpa [bci] using e0, fun i hi => ?_, fun i hi => ?_, by rw [eout]⟩
    · rw [hcar (i + 1) (by omega), hcar i (by omega), carry_val_succ, ba i hi, bb i hi]
    · rw [XF.getLsbD_bv hi, esum i hi, ba i hi, bb i hi]
  obtain ⟨h1, h2⟩ := add_spec hv
  rw [hs, h1, hc, hxb, h2]
  exact ⟨rfl, rfl⟩

/-! ## 4. The statement -/

/-- **The `add` statement for `cmp_carry.sv`**, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := cmp_struct N hN'
  refine CombTask.satisfiedAt_of_comb (cmp_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact cmp_final hA hB hCi eq_c_1 eq_c_2 eq_s_1 eq_cout_1 hvs
      (by omega) (fun k hk => (known_s_1 k hk).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
