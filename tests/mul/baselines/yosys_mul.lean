import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# The baseline `tests/mul/baselines/yosys_mul.sv`, proved for every `N` of task `mul`

The design is one continuous assign, `assign p = a * b;`, with `a`, `b` of `N` bits and `p` of `2N`
bits. It uses the run-time `*` that the task's banlist forbids, so it is not an entry: the official
check stops it at the `banlist` stage. This proof is checked by `check.py --lift-banlist`, which
runs every stage with only the task's operator banlist lifted; the statement it proves is the
task's own, `SvGolf.Tasks.Mul.Statement design.sem`, for every `N` with `1 ≤ N < 2^30`.

## Route

1. **Structure** (`yosys_struct`): one plain site, `p` from `a` and `b`; `sv_structure` with a
   constant rank leaves no goal.
2. **Ports** (`yosys_interface`): `sv_interface`.
3. **Equations** (in `solution`): `sv_equations` states the product at its context width. The
   assignment's context is `2N` bits, so slang zero-extends both factors to `2N` bits before the
   product (IEEE 1800-2017, 11.6 and 11.8.2), and the equation reads
   `st.boolAt "p" k = XF.mulBits (2N) (XF.zext N a) (2N) (XF.zext N b) k` for `k < 2N`
   (the widths printed as `(2 * ↑N + -1).natAbs + 1` and `(↑N + -1).natAbs + 1`).
4. **Arithmetic** (`yosys_final`): `XF.bv_mulBits` and `XF.bv_zext` give
   `p = x.setWidth (2N) * y.setWidth (2N)`, and that product never wraps, because
   `x * y < 2^N * 2^N = 2^(2N)` (`fn_eq_mul`, proved in the task's `Spec.lean`).
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## 1. Structure and ports -/

/-- `CombDesign` and `Acyclic` for every `N ≥ 1`: one site, so any constant rank orders its reads. -/
theorem yosys_struct (N : Nat) (_hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- The task's interface: exactly the ports `a`, `b` (`N` bits) and `p` (`2N` bits). -/
theorem yosys_interface (N : Nat) (_hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 2. The arithmetic -/

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- The printed equation of `p = a * b` (both factors zero-extended to the `2N`-bit context) and the
knownness of `p` give the task's output: the natural-number product as a `2N`-bit vector. -/
theorem yosys_final {W W2 N : Nat} (hW : W = N) (hW2 : W2 = 2 * N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ep : ∀ k, k < W2 → st.boolAt "p" k =
      XF.mulBits W2 (XF.zext W (st.boolAt "a")) W2 (XF.zext W (st.boolAt "b")) k)
    {vp : LVec} (hp : SvState.lookup st "p" = some vp) (hpw : vp.width = W2)
    (hkp : ∀ k, k < W2 → KnownBit st "p" k) :
    SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  subst hW hW2
  rw [SvState.lookup_eq_ofBitVec_bv hp hpw hkp] at hp
  rw [hp, XF.bv_mulBits ep, XF.bv_zext _ (by omega), XF.bv_zext _ (by omega), bv_of_lookup hA,
    bv_of_lookup hB]
  exact congrArg (fun z => some (LVec.ofBitVec z)) (SvGolf.Tasks.Mul.fn_eq_mul _ x y).symm

/-! ## 3. The statement -/

/-- **`assign p = a * b;` meets the `mul` statement, for every `N` with `1 ≤ N < 2^30`.** -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := yosys_struct N hN'
  refine CombTask.satisfiedAt_of_comb (yosys_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_1 0 (by omega)
    exact yosys_final (by omega) (by omega) hA hB eq_p_1 hvp hvpw (fun k hk => (known_p_1 k hk).2)
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | omega | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
