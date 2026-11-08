import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.ProcNoQualified

/-!
# Reference solution for task `add` with an `always_comb` carry cell (WP-G)

The design is `reference/add_proc.sv`: a ripple-carry adder whose carry cell is an `always_comb`
`if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];` inside the generate loop. This file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1` (`N` stays a variable from the envelope to the conclusion; nothing is unrolled), with the
`sv_comb` tactics, exactly like `reference/add_n.lean`. What differs is one fact about the design and one
lemma:

* **`design.sem N` is not a `CombDesign`** (`CombDesign.assign`: every process is a continuous assign), because
  it still contains the procedural process. What holds, and what the settle theory transfers to the design
  (`Runs2.lowerComb_iff`), is a statement about its LOWERING `d'` (`Design2.lowerComb`: each `always_comb` body
  replaced by the one continuous assign `assign {c[i+1]} = {…}` it computes). So the structure theorem is
  `∃ d', (design.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'`, the interface theorem takes
  `(hl : (design.sem N).lowerComb = some d')` (the ports of the instantiated design are the declarations of the
  summary, which only needs that the instantiation succeeded and lowers), and the equations are about `d'`.
* **`satisfiedAt_of_lowered`** (below, ten lines) is the bridge from the lowered design's settled-state lemma
  to the task's statement about `design.sem N`; it is `CombTask.satisfiedAt_of_comb` with the lowering
  theorems of `Comb2Proc.lean` (`Design2.lowerComb_phases`, `Terminates2.of_lowerComb_acyclic`,
  `Models2.of_combProc_inputs`). The last two also take `hnq`: no qualified (`unique`/`priority`) `case` in
  `design.sem N` itself, which `NoQ.sem_noQ` (`LeanModels/Sv/ProcNoQualified.lean`) gives for every `N` from one
  `decide` on the parametric design.

The tactics are the same (`sv_structure`, `sv_interface`, `sv_equations`); `sv_structure` returns one more
obligation, `noSelfRead_k` (no read of the carry cell's body overlaps the window it writes), closed by
`intros; omega` like the others. The equation of the carry cell is the body's own: an `if` on the first bit of
the condition (`eq_c_2`).
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## 0. The bridge from the lowered design -/

/-- A design that lowers has the declarations of its lowering. -/
theorem lowerComb_decls {d d' : Design2} (h : d.lowerComb = some d') : d'.decls = d.decls := by
  unfold Design2.lowerComb at h
  rcases hp : d.lowerProcs d.processes.toList with _ | ps
  · simp [hp] at h
  · simp only [hp, Option.map_some, Option.some.injEq] at h
    rw [← h]

/-- **The task's statement for a design that lowers**: the interface of the design, the comb profile and
acyclicity of its lowering, no qualified `case` in the design (`hnq`, from `NoQ.sem_noQ`), and ONE settled-state
lemma about the lowering give `SatisfiedAt`. -/
theorem satisfiedAt_of_lowered {t : CombTask} {N : Nat} {d d' : Design2}
    (hI : t.Interface N d) (hl : d.lowerComb = some d') (hd : CombDesign d') (ha : Acyclic d')
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hset : ∀ st, CombEqs d' st → StateShape d' st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  obtain ⟨hph, -, -⟩ := Design2.lowerComb_phases hl
  refine ⟨hI, ⟨unclocked_of_edgeIndices hph, ⟨d', hl, ha⟩, Terminates2.of_lowerComb_acyclic hl hd ha hnq⟩,
    ?_⟩
  apply Models2.of_combProc_inputs hl hd (hnq := hnq)
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  have hdec : d'.inputNames = d.inputNames := by simp [Design2.inputNames, lowerComb_decls hl]
  rw [hdec, ← inputPorts_map_fst, hI.1]
  exact hn

/-! ## 1. Structure: `sv_structure` -/

/-- `CombDesign` and `Acyclic` of the lowered design for every `N ≥ 1`, from ONE round of obligations: the
rank is the player's. `p[i]` has rank 0, the carry cell and the sum cell of bit `i` rank `i + 1`, the
carry-out `N + 1`. -/
theorem add_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (design.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
    (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
  all_goals (intros; omega)

/-! ## 2. The ports (the task's `Interface`) -/

theorem add_interface (N : Nat) (hN : 1 ≤ N) {d'} (hl : (design.sem N).lowerComb = some d') :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The arithmetic -/

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

/-- **The player's arithmetic.** From the five equations of the netlist (as `sv_equations` states them: the
carry cell's equation is the body's `if`) and the knownness of `s` and `cout`: the task's outputs. -/
theorem add_final {N : Nat} {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (e0 : st.boolAt "c" 0 = st.boolAt "cin" 0)
    (ep : ∀ i, i < N → st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i))
    (estep : ∀ i, i < N → st.boolAt "c" (i + 1) =
      if st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i)
    (esum : ∀ i, i < N → st.boolAt "s" i = (st.boolAt "p" i ^^ st.boolAt "c" i))
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
    · -- the carry cell: `if p then c else a` is the majority, for `p = a ^ b`
      have h1 := estep i hi
      rw [ep i hi, ba i hi, bb i hi] at h1
      simp only [h1]
      generalize x.getLsbD i = a
      generalize y.getLsbD i = b
      generalize st.boolAt "c" i = c
      cases a <;> cases b <;> cases c <;> decide
    · rw [XF.getLsbD_bv hi, esum i hi, ep i hi, ba i hi, bb i hi]
  obtain ⟨h1, h2⟩ := add_spec hv
  rw [hs, h1, hc, hxb, h2]
  exact ⟨rfl, rfl⟩

/-! ## 4. The statement -/

/-- **The reference solution**: the `add` statement, for every `N ≥ 1`. -/

theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨d', hl, hc, ha⟩ := add_struct N hN'
  refine satisfiedAt_of_lowered (add_interface N hN' hl) hl hc ha (NoQ.sem_noQ (by decide) _) ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact add_final hA hB hCi eq_c_1 eq_p_1 eq_c_2 eq_s_1 eq_cout_1 hvs
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
