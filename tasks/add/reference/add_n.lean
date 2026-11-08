import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Reference solution for task `add`, proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1` (`N` stays a variable from the envelope to the conclusion; nothing is unrolled).
The design is `reference/add_n.sv`, a ripple-carry adder in one `generate for`. The same statement
is proved with no tactic in `reference/add_n_byhand.lean` (about four times as many code lines).

## Route

1. **Structure** (`add_struct`): `sv_structure` proves `CombDesign` and `Acyclic` of
   `design.sem N` in one theorem and returns only small arithmetic goals (declared ranges, one
   driver per bit, the rank decrease), each closed by `intros; omega`. The rank is the player's:
   carry-in 0, bit `i`'s two cells `i + 1`, carry-out `N + 1`.
2. **Ports** (`add_interface`): the task's statement also pins the port names, order and widths;
   `sv_interface` proves them from the `CombDesign` profile.
3. **Equations** (in `solution`): `CombTask.satisfiedAt_of_comb` reduces the statement to ONE
   settled-state lemma; `sv_equations` then derives, from the real semantics, the four equations of
   the netlist over `Bool`, the knownness of every driven bit (`known_*`) and the obligations it does
   not discharge (declared ranges, bit reads, coverage of every read, knownness of the inputs),
   closed by `omega`, `sv_cover` and `inKnown_ofBitVec`. The equations are used under their STABLE
   names, the target signal and the ordinal of the assign among those writing it: `eq_c_1`
   (`c[0] = cin`), `eq_c_2` (the carry cell), `eq_s_1`, `eq_cout_1`; the generated names
   (`eq_c_plain_0`, `eq_c_g_bit_1`, …, which depend on the block label and the position) are copies.
4. **Arithmetic** (`add_final`): the only mathematics. The equations are the library structure
   `CombLib.AddView`; `add_spec` (the ripple-row lemma, `bfVal`) turns it into the sum, and the
   port bridge `SvState.lookup_eq_ofBitVec_bv` turns the Boolean bits back into the ports' values.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## 1. Structure: `sv_structure` -/

/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from ONE round of obligations: the rank is the
player's. -/
theorem add_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

/-! ## 2. The ports (the task's `Interface`) -/

/-- The task's interface: exactly the ports `a`, `b`, `cin` and `s`, `cout`, in this order and with
these widths. -/
theorem add_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The arithmetic -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- **The player's arithmetic.** From the four equations of the netlist (as `sv_equations` states
them) and the knownness of `s` and `cout`: the task's outputs. -/
theorem add_final {N : Nat} {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (e0 : st.boolAt "c" 0 = st.boolAt "cin" 0)
    (estep : ∀ i, i < N → st.boolAt "c" (i + 1) =
      ((st.boolAt "a" i && st.boolAt "b" i) || (st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))))
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
  have hv : AddView N x y c0 (fun i => st.boolAt "c" i) (XF.bv N (st.boolAt "s")).getLsbD
      (st.boolAt "cout" 0) := by
    refine ⟨by simpa [bci] using e0, fun i hi => ?_, fun i hi => ?_, by rw [eout]⟩
    · simp only [estep i hi, ba i hi, bb i hi]
    · rw [XF.getLsbD_bv hi, esum i hi, ba i hi, bb i hi]
  obtain ⟨h1, h2⟩ := add_spec hv
  rw [hs, h1, hc, hxb, h2]
  exact ⟨rfl, rfl⟩

/-! ## 4. The statement -/

/-- **The reference solution**: the `add` statement, for every `N ≥ 1`. -/

theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := add_struct N hN'
  refine CombTask.satisfiedAt_of_comb (add_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact add_final hA hB hCi eq_c_1 eq_c_2 eq_s_1 eq_cout_1 hvs
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
