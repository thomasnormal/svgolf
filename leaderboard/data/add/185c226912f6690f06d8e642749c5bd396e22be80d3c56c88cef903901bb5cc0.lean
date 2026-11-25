import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib.Prefix

/-!
# Task `add`: sparse-6 Kogge-Stone parallel-prefix adder

Proved for every `N` with `1 ≤ N < 2^20`:

1. **Arithmetic** (`SparseAddArith`):
   - `ksRec` / `ksRec_block`: Kogge-Stone prefix tree invariant over `(generate, propagate)` pairs.
   - `sparse6_adder`: for `Q = (N + 5) / 6`, `M = 6 * Q`, `L = clog2 (Q + 1)`, the 6-bit block
     generate/propagate ripple, `L`-level Kogge-Stone prefix tree, and 6-bit local carry ripple
     produce the exact canonical ripple carries `c_all[i]` for `0 ≤ i ≤ M`, hence the exact sum
     bits `s[i]` (`0 ≤ i < N`) and carry-out `cout = c_all[N]`.
2. **Structure & Ports** (`add_struct`, `add_interface`): `sv_structure` with lexicographic rank
   `addKey` proves `CombDesign`, `Acyclic`, and `SharedObl`; `sv_interface` checks the ports.
3. **Equations & End-to-end proof** (`solution`): `sv_equations` extracts the Boolean netlist
   equations and bit knownness; `add_spec` via `AddView` and `SvState.lookup_eq_ofBitVec_bv`
   close the proof.
-/

/-! ## 1. The arithmetic (plain Lean, `CombLib` and `Lib.Prefix` only) -/

namespace SparseAddArith
open LeanModels.Sv.CombLib LeanModels.Sv.Lib

/-- The Kogge-Stone recurrence on `(generate, propagate)` pairs. -/
def ksRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, k => pos k
  | l + 1, k => if 2 ^ l ≤ k then pgOp (ksRec pos l k) (ksRec pos l (k - 2 ^ l)) else ksRec pos l k

/-- After level `l`, position `k` holds the pair of the block `[k + 1 - 2^l, k]`. -/
theorem ksRec_block (pos : Nat → Bool × Bool) : ∀ l k, ksRec pos l k = pgBlock pos (k + 1 - 2 ^ l) k
  | 0, k => by rw [ksRec, Nat.pow_zero, Nat.add_sub_cancel, pgBlock_self]
  | l + 1, k => by
    have hP : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [ksRec, hP]
    split
    · rw [ksRec_block pos l k, ksRec_block pos l (k - 2 ^ l)]
      generalize 2 ^ l = Q at *
      have hc := pgBlock_combine pos (j := k + 1 - 2 * Q) (m := k - Q) (k := k) (by omega) (by omega)
      rw [show k - Q + 1 = k + 1 - Q by omega] at hc
      rw [show k - Q + 1 - Q = k + 1 - 2 * Q by omega]
      exact hc
    · rw [ksRec_block pos l k]
      generalize 2 ^ l = Q at *
      rw [show k + 1 - Q = 0 by omega, show k + 1 - 2 * Q = 0 by omega]

/-- The sparse-6 Kogge-Stone adder computes canonical ripple carries `c_all i` for all `i ≤ M`. -/
theorem sparse6_carries {Q M L : Nat} (hM : M = 6 * Q) (hL : Q + 1 ≤ 2 ^ L)
    (cin : Bool)
    (ap bp x p g c_all : Nat → Bool)
    (gg pp cc bg bp_g : Nat → Nat → Bool)
    (hx : ∀ i, i < M → x i = (ap i ^^ bp i))
    (hp : ∀ i, i < M → p i = (ap i ^^ bp i))
    (hg : ∀ i, i < M → g i = (ap i && bp i))
    (hgg0 : ∀ j, j < Q → gg j 0 = false)
    (hpp0 : ∀ j, j < Q → pp j 0 = true)
    (hgg : ∀ j, j < Q → ∀ t, t < 6 →
      gg j (t + 1) = (g (6 * j + t) || (p (6 * j + t) && gg j t)))
    (hpp : ∀ j, j < Q → ∀ t, t < 6 →
      pp j (t + 1) = (p (6 * j + t) && pp j t))
    (hbg00 : bg 0 0 = cin)
    (hbp00 : bp_g 0 0 = false)
    (hbg_blk : ∀ j, j < Q → bg 0 (j + 1) = gg j 6)
    (hbp_blk : ∀ j, j < Q → bp_g 0 (j + 1) = pp j 6)
    (hbg_op : ∀ l, l < L → ∀ j, j < Q + 1 → 2 ^ l ≤ j →
      bg (l + 1) j = (bg l j || (bp_g l j && bg l (j - 2 ^ l))))
    (hbp_op : ∀ l, l < L → ∀ j, j < Q + 1 → 2 ^ l ≤ j →
      bp_g (l + 1) j = (bp_g l j && bp_g l (j - 2 ^ l)))
    (hbg_pass : ∀ l, l < L → ∀ j, j < Q + 1 → ¬ 2 ^ l ≤ j →
      bg (l + 1) j = bg l j)
    (hbp_pass : ∀ l, l < L → ∀ j, j < Q + 1 → ¬ 2 ^ l ≤ j →
      bp_g (l + 1) j = bp_g l j)
    (hcc0 : ∀ j, j < Q → cc j 0 = bg L j)
    (hcc : ∀ j, j < Q → ∀ t, t < 6 →
      cc j (t + 1) = (if x (6 * j + t) = true then cc j t else ap (6 * j + t)))
    (hc_blk : ∀ j, j < Q → ∀ t, t < 6 → c_all (6 * j + t) = cc j t)
    (hc_M : c_all M = bg L Q) :
    ∀ i, i ≤ M → c_all i = rippleCarry ap bp cin i := by
  let rc : Nat → Bool := rippleCarry ap bp cin
  -- 1. Each 6-bit block computes the span `(G, P)` of its 6 bits.
  have h_span : ∀ j, j < Q → ∀ t, t ≤ 6 →
      (gg j t, pp j t) = pgSpan (addPos ap bp cin) (6 * j + 1) t := by
    intro j hj t
    induction t with
    | zero => intro _; rw [hgg0 j hj, hpp0 j hj]; rfl
    | succ t ih =>
      intro ht
      rw [hgg j hj t (by omega), hpp j hj t (by omega),
        hg (6 * j + t) (by omega), hp (6 * j + t) (by omega),
        pgSpan_succ, ← ih (by omega)]
      rw [show 6 * j + 1 + t = (6 * j + t) + 1 by omega, addPos_succ]
      rfl
  -- 2. Block-level positions for the Kogge-Stone prefix tree.
  let blkPos : Nat → Bool × Bool
    | 0 => (cin, false)
    | j + 1 => pgBlock (addPos ap bp cin) (6 * j + 1) (6 * (j + 1))
  have hblk_block : ∀ j, pgBlock blkPos 0 j = (rc (6 * j), false) := by
    intro j
    induction j with
    | zero =>
      rw [pgBlock_self]
      simp [blkPos, rc, rippleCarry_zero]
    | succ j ih =>
      rw [pgBlock_succ _ (Nat.zero_le _), ih]
      have h0 : (rc (6 * j), false) = pgBlock (addPos ap bp cin) 0 (6 * j) :=
        (pgBlock_addPos_zero ap bp cin (6 * j)).symm
      rw [h0]
      dsimp [blkPos]
      rw [pgBlock_combine (addPos ap bp cin) (j := 0) (m := 6 * j) (k := 6 * (j + 1))
        (by omega) (by omega)]
      exact pgBlock_addPos_zero ap bp cin (6 * (j + 1))
  -- 3. Kogge-Stone levels satisfy `ksRec blkPos`.
  have hlev : ∀ l, l ≤ L → ∀ j, j < Q + 1 → (bg l j, bp_g l j) = ksRec blkPos l j := by
    intro l
    induction l with
    | zero =>
      intro _ j hj
      cases j with
      | zero => rw [hbg00, hbp00]; rfl
      | succ j =>
        rw [hbg_blk j (by omega), hbp_blk j (by omega), h_span j (by omega) 6 (Nat.le_refl 6)]
        simp only [ksRec, blkPos, pgBlock, show 6 * (j + 1) + 1 - (6 * j + 1) = 6 by omega]
    | succ l ih =>
      intro hl j hj
      rw [ksRec]
      split
      · next hge =>
        rw [hbg_op l (by omega) j hj hge, hbp_op l (by omega) j hj hge,
          ← ih (by omega) j hj, ← ih (by omega) (j - 2 ^ l) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj)]
        rfl
      · next hge =>
        rw [hbg_pass l (by omega) j hj hge, hbp_pass l (by omega) j hj hge, ← ih (by omega) j hj]
  have hbg_L : ∀ j, j < Q + 1 → bg L j = rc (6 * j) := by
    intro j hj
    have h := hlev L (Nat.le_refl L) j hj
    rw [ksRec_block, show j + 1 - 2 ^ L = 0 by omega, hblk_block] at h
    exact (Prod.mk.inj h).1
  -- 4. Local carries inside each 6-bit block match `rc`.
  have hcc_eq : ∀ j, j < Q → ∀ t, t ≤ 6 → cc j t = rc (6 * j + t) := by
    intro j hj t
    induction t with
    | zero => intro _; rw [hcc0 j hj, hbg_L j (by omega), Nat.add_zero]
    | succ t ih =>
      intro ht
      rw [hcc j hj t (by omega), hx (6 * j + t) (by omega), ih (by omega)]
      rw [show 6 * j + (t + 1) = (6 * j + t) + 1 by omega]
      dsimp [rc]
      rw [rippleCarry_succ]
      generalize ap (6 * j + t) = a
      generalize bp (6 * j + t) = b
      generalize rippleCarry ap bp cin (6 * j + t) = r
      cases a <;> cases b <;> cases r <;> rfl
  -- 5. Combine block carries and top carry `c_all M`.
  intro i hi
  by_cases hlt : i < M
  · let j := i / 6
    let t := i % 6
    have hj : j < Q := by omega
    have ht : t < 6 := by omega
    have heq : 6 * j + t = i := by omega
    have h := hc_blk j hj t ht
    rw [hcc_eq j hj t (by omega), heq] at h
    exact h
  · have hiM : i = M := by omega
    rw [hiM, hc_M, hbg_L Q (by omega), hM]

end SparseAddArith

/-! ## 2. Structure, interface, and end-to-end proof -/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
  LeanModels.Sv.Lib SvGolf

/-- Lexicographic rank certificate `(stage, order, phase)` for `solutions_asap7/add/solution.sv`. -/
def addKey : SiteId → Key
  | .plain 2 => (3, 0, 0)
  | .plain 3 => (3, 0, 0)
  | .plain 4 => (5, 0, 0)
  | .plain 5 => (7, 0, 0)
  | .plain _ => (0, 0, 0)
  | .fam "g_pad" _ _ => (0, 0, 0)
  | .fam "g_pg" _ _ => (1, 0, 0)
  | .fam "g_blk" 0 _ => (2, 0, 0)
  | .fam "g_blk" 1 _ => (2, 0, 0)
  | .fam "g_blk" _ _ => (3, 0, 0)
  | .fam "g_rip" _ [_, t] => (2, t.toNat + 1, 0)
  | .fam "g_node" _ [l, _] => (4, l.toNat, 0)
  | .fam "g_loc" _ _ => (5, 0, 0)
  | .fam "g_lc" 0 [_, t] => (6, t.toNat, 0)
  | .fam "g_lc" _ [_, t] => (6, t.toNat, 1)
  | .fam "g_sum" _ _ => (7, 0, 0)
  | .fam _ _ _ => (8, 0, 0)

set_option maxHeartbeats 2000000 in
theorem add_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  have hQ : (1 : Int) ≤ ((N : Int) + 6 - 1) / 6 := by omega
  sv_structure (lexRank := addKey)
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

theorem add_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface

/-- A 1-bit vector is the `ofBool` of its only bit. -/
theorem bv1_eq_ofBool (v : BitVec 1) : v = BitVec.ofBool (v.getLsbD 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

set_option maxHeartbeats 2000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  have hR : N < 2 ^ 20 := hN.2
  have hQ0 : (1 : Int) ≤ ((N : Int) + 6 - 1) / 6 := by omega
  obtain ⟨hc, ha, hso⟩ := add_struct N hN' hR
  refine CombTask.satisfiedAt_of_comb (add_interface N hN' hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ci, ⟨⟩⟩ := v
  obtain ⟨c0, rfl⟩ : ∃ c0, ci = BitVec.ofBool c0 := ⟨_, bv1_eq_ofBool ci⟩
  simp only [SvGolf.Tasks.Add.task, HoldAll_cons, HoldAll_nil, and_true, BitVec.toNat_ofBool]
    at hv ⊢
  obtain ⟨hA, hB, hCi⟩ := hv
  sv_equations
  · let Q : Nat := (N + 5) / 6
    let M : Nat := 6 * Q
    let L : Nat := clog2 (Q + 1)
    let bgW : Int := ((N : Int) + 6 - 1) / 6 + 1
    have hQc : (Q : Int) = ((N : Int) + 6 - 1) / 6 := by dsimp [Q]; omega
    have hMc : (M : Int) = 6 * (((N : Int) + 6 - 1) / 6) := by dsimp [M]; omega
    have hLc : clog2 (((N : Int) + 6 - 1) / 6 + 1).toNat = L := by
      rw [← hQc]; dsimp [L]
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have bci : st.boolAt "cin" 0 = c0 := by
      rw [SvState.boolAt_ofBitVec hCi (by omega)]; simp
    have hap : ∀ i, i < N → st.boolAt "ap" i = x.getLsbD i := by
      intro i hi
      rw [eq_ap_plain_0 i (by omega), ba i hi]
    have hbp : ∀ i, i < N → st.boolAt "bp" i = y.getLsbD i := by
      intro i hi
      rw [eq_bp_plain_1 i (by omega), bb i hi]
    have hcall : ∀ i, i ≤ M → st.boolAt "c_all" i =
        rippleCarry (st.boolAt "ap") (st.boolAt "bp") c0 i := by
      refine SparseAddArith.sparse6_carries (Q := Q) (M := M) (L := L) rfl
        (le_two_pow_clog2 (Q + 1)) c0
        (st.boolAt "ap") (st.boolAt "bp") (st.boolAt "x") (st.boolAt "p") (st.boolAt "g")
        (st.boolAt "c_all")
        (st.cell "gg" 7) (st.cell "pp" 7) (st.cell "cc" 7)
        (st.cell "bg" bgW) (st.cell "bp_g" bgW)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro i hi; exact eq_x_g_pg_0 i (by omega)
      · intro i hi; exact eq_p_g_pg_1 i (by omega)
      · intro i hi; exact eq_g_g_pg_2 i (by omega)
      · intro j hj; exact eq_gg_g_blk_0 j (by omega)
      · intro j hj; exact eq_pp_g_blk_1 j (by omega)
      · intro j hj t ht
        have h := eq_gg_g_rip_0 j (by omega) t (by omega)
        simpa [SvState.cell, show (6 * (j : Int) + (t : Int)).toNat = 6 * j + t by omega,
          show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega] using h
      · intro j hj t ht
        have h := eq_pp_g_rip_1 j (by omega) t (by omega)
        simpa [SvState.cell, show (6 * (j : Int) + (t : Int)).toNat = 6 * j + t by omega,
          show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega] using h
      · simpa [SvState.cell, rmN, bci] using eq_bg_plain_2
      · simpa [SvState.cell, rmN] using eq_bp_g_plain_3
      · intro j hj
        simpa [SvState.cell, rmN] using eq_bg_g_blk_3 j (by omega)
      · intro j hj
        simpa [SvState.cell, rmN] using eq_bp_g_2 j (by omega)
      · intro l hl j hj hge
        have hp2 : ((2 ^ l : Nat) : Int) = (2 : Int) ^ l := by push_cast; rfl
        have h := eq_bg_g_node_0 l (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((l + 1 : Nat) : Int) = (l : Int) + 1 by omega,
          show ((j - 2 ^ l : Nat) : Int) = (j : Int) + -1 * (2 : Int) ^ l by omega] using h
      · intro l hl j hj hge
        have hp2 : ((2 ^ l : Nat) : Int) = (2 : Int) ^ l := by push_cast; rfl
        have h := eq_bp_g_3 l (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((l + 1 : Nat) : Int) = (l : Int) + 1 by omega,
          show ((j - 2 ^ l : Nat) : Int) = (j : Int) + -1 * (2 : Int) ^ l by omega] using h
      · intro l hl j hj hge
        have hp2 : ((2 ^ l : Nat) : Int) = (2 : Int) ^ l := by push_cast; rfl
        have h := eq_bg_g_node_2 l (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((l + 1 : Nat) : Int) = (l : Int) + 1 by omega] using h
      · intro l hl j hj hge
        have hp2 : ((2 ^ l : Nat) : Int) = (2 : Int) ^ l := by push_cast; rfl
        have h := eq_bp_g_4 l (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((l + 1 : Nat) : Int) = (l : Int) + 1 by omega] using h
      · intro j hj
        have h := eq_cc_g_loc_0 j (by omega)
        simpa [SvState.cell, bgW, hLc] using h
      · intro j hj t ht
        have h := eq_cc_g_lc_0 j (by omega) t (by omega)
        simpa [SvState.cell, show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega,
          show (6 * (j : Int) + (t : Int)).toNat = 6 * j + t by omega] using h
      · intro j hj t ht
        have h := eq_c_all_g_lc_1 j (by omega) t (by omega)
        simpa [SvState.cell, show (6 * (j : Int) + (t : Int)).toNat = 6 * j + t by omega] using h
      · simpa [SvState.cell, bgW, hLc, ← hQc, show (6 * (Q : Int)).toNat = M by omega,
          show clog2 (Q + 1) = L from rfl] using eq_c_all_plain_4
    obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_sum_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_5
    have hvs' := SvState.lookup_eq_ofBitVec_bv (W := N) hvs (by omega)
      (fun k hk => (known_s_g_sum_0 k (by omega)).2)
    have hvc' := SvState.lookup_eq_ofBitVec_bv hvc hvcw (fun k hk => by
      obtain rfl : k = 0 := by omega
      exact hkc)
    rw [hvs'] at hvs
    rw [hvc'] at hvc
    have hxb : XF.bv 1 (st.boolAt "cout") = BitVec.ofBool (st.boolAt "cout" 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      obtain rfl : i = 0 := by omega
      rw [XF.getLsbD_bv hi]; simp
    have hv_add : AddView N x y c0 (fun i => st.boolAt "c_all" i)
        (XF.bv N (st.boolAt "s")).getLsbD (st.boolAt "cout" 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hcall 0 (by omega), rippleCarry_zero]
      · intro i hi
        rw [hcall (i + 1) (by omega), hcall i (by omega), rippleCarry_succ, hap i hi, hbp i hi]
      · intro i hi
        rw [XF.getLsbD_bv hi, eq_s_g_sum_0 i (by omega), eq_x_g_pg_0 i (by omega), hap i hi, hbp i hi]
      · exact eq_cout_plain_5
    obtain ⟨h1, h2⟩ := add_spec hv_add
    rw [hvs, h1, hvc, hxb, h2]
    exact ⟨rfl, rfl⟩
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  case inputsKnown_3 => exact inKnown_ofBitVec hCi (by omega)
  case cover_11 =>
    intro i hi0 hiN
    refine ⟨⟨i.toNat, by omega, by omega, by omega⟩,
      Or.inr ⟨i.toNat / 6, by omega, i.toNat % 6, by omega, by omega, by omega⟩⟩
  all_goals first
    | (intros; omega)
    | (intros; rfl)
    | sv_cover
    | (by_cases hNM : N = 6 * ((N + 5) / 6)
       · left; omega
       · right; exact ⟨N / 6, by omega, N % 6, by omega, by omega⟩)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
