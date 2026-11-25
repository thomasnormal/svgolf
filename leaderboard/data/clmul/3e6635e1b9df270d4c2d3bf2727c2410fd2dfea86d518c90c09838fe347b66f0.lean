import Submission.Design
import tasks.clmul.Spec
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.Clmul

namespace TreeArith

def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem foldl_xor (f : Nat → Bool) (n : Nat) (acc : Bool) :
    (List.range n).foldl (fun acc i => acc ^^ f i) acc = (acc ^^ bx f n) := by
  induction n generalizing acc with
  | zero => simp [bx]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    simp only [bx]
    cases acc <;> cases bx f n <;> cases f n <;> rfl

theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) :
    coeff N a b k =
      bx (fun i => bx (fun j => decide (i + j = k) && a.getLsbD i && b.getLsbD j) N) N := by
  unfold coeff
  simp only [foldl_xor]
  simp

theorem bx_pair (i k : Nat) (x : Bool) (c : Nat → Bool) (n : Nat) :
    bx (fun j => decide (i + j = k) && x && c j) n = (decide (i ≤ k ∧ k - i < n) && x && c (k - i)) := by
  induction n with
  | zero => simp [bx]
  | succ n ih =>
    simp only [bx, ih]
    by_cases h : i + n = k
    · have h1 : k - i = n := by omega
      have h2 : ¬ (k - i < n) := by omega
      have h3 : i ≤ k ∧ k - i < n + 1 := by omega
      simp [h, h1, h3]
    · have h4 : (decide (i ≤ k ∧ k - i < n + 1)) = (decide (i ≤ k ∧ k - i < n)) := by
        apply decide_eq_decide.mpr; omega
      have h5 : decide (i + n = k) = false := by simp [h]
      rw [h5, h4]; simp

theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [ofBits]
  | n + 1, f, k => by
    rw [ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp
    | succ k => simp

def wx (f : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => wx f s n ^^ f (s + n)

theorem wx_succ (f : Nat → Bool) (s n : Nat) : wx f s (n + 1) = (wx f s n ^^ f (s + n)) := rfl

theorem wx_one (f : Nat → Bool) (s : Nat) : wx f s 1 = f s := by
  show (false ^^ f s) = f s
  cases f s <;> rfl

theorem wx_front (f : Nat → Bool) (s : Nat) : ∀ n, wx f s (n + 1) = (f s ^^ wx f (s + 1) n)
  | 0 => by
    show (false ^^ f s) = (f s ^^ false)
    cases f s <;> rfl
  | n + 1 => by
    rw [wx_succ f s (n + 1), wx_front f s n, wx_succ f (s + 1) n, show s + (n + 1) = s + 1 + n by omega]
    cases f s <;> cases wx f (s + 1) n <;> cases f (s + 1 + n) <;> rfl

theorem wx_bx (f : Nat → Bool) : ∀ n, wx f 0 n = bx f n
  | 0 => rfl
  | n + 1 => by rw [wx_succ, bx_succ, wx_bx f n, Nat.zero_add]

theorem wx_window {N : Nat} (c : Nat → Bool)
    (h : ∀ g, g + 1 < N → c (N + g) = (c (2 * g) ^^ c (2 * g + 1))) :
    ∀ g, g + 1 ≤ N → wx c (2 * g) (N - g) = wx c 0 N := by
  intro g
  induction g with
  | zero => intro _; first | rfl | simp
  | succ g ih =>
    intro hg
    obtain ⟨n, hn⟩ : ∃ n, N - g = n + 1 + 1 := ⟨N - g - 2, by omega⟩
    have hn' : N - (g + 1) = n + 1 := by omega
    rw [← ih (by omega), hn, hn', wx_front c (2 * g) (n + 1), wx_front c (2 * g + 1) n,
      wx_succ c (2 * (g + 1)) n, show 2 * (g + 1) = 2 * g + 1 + 1 by omega,
      show 2 * g + 1 + 1 + n = N + g by omega, h g (by omega)]
    cases c (2 * g) <;> cases c (2 * g + 1) <;> cases wx c (2 * g + 1 + 1) n <;> rfl

theorem col_root {N : Nat} (hN : 1 ≤ N) (c : Nat → Bool)
    (h : ∀ g, g + 1 < N → c (N + g) = (c (2 * g) ^^ c (2 * g + 1))) :
    c (2 * N - 2) = bx c N := by
  have hw := wx_window c h (N - 1) (by omega)
  rw [show N - (N - 1) = 1 by omega, wx_one, show 2 * (N - 1) = 2 * N - 2 by omega, wx_bx] at hw
  exact hw

/-- Unified leaves for any column `k < 2 * N - 1`: `a[t] & be[k + N - t]` equals the Spec's term `t`. -/
theorem all_leaves {N : Nat} (A B be G : Nat → Bool) (k : Nat) (hk : k < 2 * N - 1)
    (hbe1 : ∀ x, x < N → be x = false)
    (hbe2 : ∀ x, x < N → be (N + x) = B x)
    (hbe3 : ∀ x, x < N → be (2 * N + x) = false)
    (hG : ∀ t, t < N → G t = (A t && be (k + N - t))) :
    bx G N = bx (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) N := by
  apply bx_congr
  intro t ht
  rw [hG t ht]
  by_cases h1 : t ≤ k
  · by_cases h2 : k - t < N
    · rw [show k + N - t = N + (k - t) by omega, hbe2 (k - t) h2]
      have hd : decide (t ≤ k ∧ k - t < N) = true := by simp; omega
      rw [hd]; simp
    · rw [show k + N - t = 2 * N + (k - t - N) by omega, hbe3 (k - t - N) (by omega)]
      have hd : decide (t ≤ k ∧ k - t < N) = false := by simp; omega
      rw [hd]; simp
  · rw [hbe1 (k + N - t) (by omega)]
    have hd : decide (t ≤ k ∧ k - t < N) = false := by simp; omega
    rw [hd]; simp

theorem tree_spec {N : Nat} (hN : 1 ≤ N) (A B be P : Nat → Bool) (T : Nat → Nat → Bool)
    (hbe1 : ∀ x, x < N → be x = false)
    (hbe2 : ∀ x, x < N → be (N + x) = B x)
    (hbe3 : ∀ x, x < N → be (2 * N + x) = false)
    (hleaf : ∀ t, t < N → ∀ k, k < 2 * N - 1 → T t k = (A t && be (k + N - t)))
    (hnode : ∀ g, g + 1 < N → ∀ k, k < 2 * N - 1 → T (N + g) k = (T (2 * g) k ^^ T (2 * g + 1) k))
    (hp : ∀ k, k < 2 * N - 1 → P k = T (2 * N - 2) k) :
    ∀ k, k < 2 * N - 1 → P k = bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) N) N := by
  intro k hk
  have inner : (fun i => bx (fun j => decide (i + j = k) && A i && B j) N)
      = (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) := by
    funext i
    exact bx_pair i k (A i) B N
  rw [inner, hp k hk, col_root hN (fun r => T r k) (fun g hg => hnode g hg k hk)]
  exact all_leaves A B be (fun r => T r k) k hk hbe1 hbe2 hbe3 (fun t ht => hleaf t ht k hk)

end TreeArith

/-- Rank: plain `be` slices (0..2) -> stage 0; leaves `g_col` -> stage 1;
    XOR nodes `g_node` (index `g`) -> stage 2, order `g`; plain `p` (3) -> stage 3. -/
def treeKey : SiteId → Key
  | .plain p => if p < 3 then (0, 0, 0) else (3, 0, 0)
  | .fam "g_col" _ _ => (1, 0, 0)
  | .fam "g_node" _ [g] => (2, g.toNat, 0)
  | .fam _ _ _ => (3, 0, 0)

set_option maxHeartbeats 1000000 in
theorem tree_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := treeKey)
  all_goals (intros; sv_rowmajor; omega)

theorem tree_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Clmul.task.Interface N (design.sem N) := by
  sv_interface

set_option maxHeartbeats 1000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  have hR : N < 2 ^ 20 := hN.2
  obtain ⟨hc, ha, hso⟩ := tree_struct N hN' hR
  refine CombTask.satisfiedAt_of_comb (tree_interface N hN' hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_1 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have hkp : ∀ k, k < 2 * N - 1 → KnownBit st "p" k := fun k hk => (known_p_1 k (by omega)).2
    have hbits := TreeArith.tree_spec hN' x.getLsbD y.getLsbD (st.boolAt "be")
      (st.boolAt "p") (st.cell "T" (2 * (N : Int) - 1))
      (by sv_bridge eq_be_1)
      (by sv_bridge eq_be_2 with bb)
      (by sv_bridge eq_be_3)
      (by sv_bridge eq_T_1 with ba)
      (by sv_bridge eq_T_2)
      (by sv_bridge eq_p_1)
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N - 1) hvp (by omega) hkp]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, TreeArith.getLsbD_ofBits, hbits k hk, ← TreeArith.coeff_eq]
    simp [hk]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
