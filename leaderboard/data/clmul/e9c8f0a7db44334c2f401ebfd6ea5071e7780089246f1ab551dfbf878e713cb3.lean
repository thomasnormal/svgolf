import Submission.Design
import tasks.clmul.Spec
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Task `clmul`: the schoolbook product with a balanced XOR tree per column, proved with the `sv_comb` tactics

The design (`clmul_tree.sv`) is one 2-D packed array `T` of `2N-1` columns by `2N-1` positions, a TAPE per
output column `k`: positions `0 .. N-1` are the column's partial products, zero-padded to `N` leaves
(lower columns `k < N`: `T[k][t] = a[t] & be[k - t + N]`; upper columns `N + k`:
`T[N+k][t] = ae[t + k + 1] & b[N-1-t]`, with the padded copies `be = {b, N zero bits}` and
`ae = {N zero bits, a}`); XOR node `g` (`g = 0 .. N-2`) writes position `N + g` from positions `2g` and
`2g + 1`; the root is position `2N-2` and is the output bit `p[k]`.

## Route

1. **Arithmetic** (`TreeArith`, plain Lean): `wx_window`, the live window `[2g, N + g)` of a column XORs to
   the XOR of its `N` leaves for every `g ≤ N - 1` (node `g` takes positions `2g`, `2g + 1` off the front of
   the window and appends their XOR at its back), so the root is the XOR of the leaves (`col_root`); the
   leaves of a column are the Spec's terms (`lower_leaves`, `upper_leaves`); `tree_spec` assembles them.
   The XOR helpers `bx`, `bx_congr`, `bx_trunc`, `bx_false`, `foldl_xor`, `coeff_eq`, `bx_pair` and
   `getLsbD_ofBits` are those of the task's reference proof.
2. **Structure** (`tree_struct`): `sv_structure` with the lexicographic key `(stage, node, 0)` (`treeKey`).
3. **Ports** (`tree_interface`): `sv_interface`.
4. **Equations, bridge and coverage** (`solution`): `sv_equations`, one `sv_bridge` per fact of
   `tree_spec`, `sv_cover` for the reads of the tape (a leaf when the position is below `N`, else node
   `position - N`).
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.Clmul

/-! ## 1. The arithmetic: plain Lean, no ls-sv -/

namespace TreeArith

/-- `bx f n`: the XOR of `f 0, …, f (n-1)`. -/
def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_congr {f g : Nat → Bool} {n : Nat} (h : ∀ j, j < n → f j = g j) : bx f n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bx]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bx_trunc {f : Nat → Bool} {n m : Nat} (hnm : n ≤ m) (h : ∀ j, n ≤ j → j < m → f j = false) :
    bx f m = bx f n := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hn : n = m + 1
    · subst hn; rfl
    · simp only [bx]
      rw [ih (by omega) (fun j hj1 hj2 => h j hj1 (by omega)), h m (by omega) (by omega)]
      simp

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

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

/-- The Spec's double sum is the nested `bx`. -/
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

theorem fx (b : Bool) : (false ^^ b) = b := by cases b <;> rfl

/-! ### Windows of a column's tape -/

/-- `wx f s n`: the XOR of `f s, …, f (s + n - 1)`, a window of the tape. -/
def wx (f : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => wx f s n ^^ f (s + n)

theorem wx_succ (f : Nat → Bool) (s n : Nat) : wx f s (n + 1) = (wx f s n ^^ f (s + n)) := rfl

theorem wx_one (f : Nat → Bool) (s : Nat) : wx f s 1 = f s := by
  show (false ^^ f s) = f s
  cases f s <;> rfl

/-- Peel the first term off a window. -/
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

/-- A window read with a shifted function. -/
theorem wx_eq_bx (f g : Nat → Bool) (s n : Nat) (h : ∀ t, t < n → g t = f (s + t)) :
    wx f s n = bx g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wx_succ, bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]

/-- Split an XOR at `m`. -/
theorem bx_split (f : Nat → Bool) (m n : Nat) : bx f (m + n) = (bx f m ^^ wx f m n) := by
  induction n with
  | zero =>
    show bx f m = (bx f m ^^ false)
    cases bx f m <;> rfl
  | succ n ih =>
    show bx f (m + n + 1) = (bx f m ^^ wx f m (n + 1))
    rw [bx_succ, ih, wx_succ]
    cases bx f m <;> cases wx f m n <;> cases f (m + n) <;> rfl

/-- **The window invariant** of one column: with node `g` (`g + 1 < N`) at position `N + g` the XOR of
positions `2g` and `2g + 1`, the window `[2g, N + g)` XORs to the leaves `[0, N)`, for every `g ≤ N - 1`. -/
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

/-- The root of a column's tree is the XOR of its `N` leaves. -/
theorem col_root {N : Nat} (hN : 1 ≤ N) (c : Nat → Bool)
    (h : ∀ g, g + 1 < N → c (N + g) = (c (2 * g) ^^ c (2 * g + 1))) :
    c (2 * N - 2) = bx c N := by
  have hw := wx_window c h (N - 1) (by omega)
  rw [show N - (N - 1) = 1 by omega, wx_one, show 2 * (N - 1) = 2 * N - 2 by omega, wx_bx] at hw
  exact hw

/-- The leaves of a lower column `k < N`: `a[t] & be[k - t + N]` is the Spec's term `t`. -/
theorem lower_leaves {N : Nat} (A B be G : Nat → Bool) (k : Nat) (hk : k < N)
    (hbe1 : ∀ x, x < N → be x = false) (hbe2 : ∀ x, x < N → be (N + x) = B x)
    (hG : ∀ t, t < N → G t = (A t && be (k + N - t))) :
    bx G N = bx (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) N := by
  apply bx_congr
  intro t ht
  rw [hG t ht]
  by_cases h : t ≤ k
  · rw [show k + N - t = N + (k - t) by omega, hbe2 (k - t) (by omega)]
    have hd : decide (t ≤ k ∧ k - t < N) = true := by simp; omega
    rw [hd]
    all_goals simp
  · rw [hbe1 (k + N - t) (by omega)]
    have hd : decide (t ≤ k ∧ k - t < N) = false := by simp; omega
    rw [hd]
    all_goals simp

/-- The leaves of an upper column `N + k` (`k + 1 < N`): `ae[t + k + 1] & b[N-1-t]` is the Spec's term
`t + k + 1`; the leaves `t ≥ N - 1 - k` and the Spec's terms `i ≤ k` are zero. -/
theorem upper_leaves {N : Nat} (A B ae G : Nat → Bool) (k : Nat) (hk : k + 1 < N)
    (hae1 : ∀ x, x < N → ae x = A x) (hae2 : ∀ x, x < N → ae (N + x) = false)
    (hG : ∀ t, t < N → G t = (ae (t + k + 1) && B (N - 1 - t))) :
    bx G N = bx (fun i => decide (i ≤ N + k ∧ N + k - i < N) && A i && B (N + k - i)) N := by
  have h1 : bx G N = bx G (N - 1 - k) := by
    refine bx_trunc (by omega) ?_
    intro t ht1 ht2
    rw [hG t ht2, show t + k + 1 = N + (t + k + 1 - N) by omega, hae2 (t + k + 1 - N) (by omega)]
    all_goals simp
  have h2 := bx_split (fun i => decide (i ≤ N + k ∧ N + k - i < N) && A i && B (N + k - i))
    (k + 1) (N - 1 - k)
  rw [show k + 1 + (N - 1 - k) = N by omega] at h2
  have h3 : bx (fun i => decide (i ≤ N + k ∧ N + k - i < N) && A i && B (N + k - i)) (k + 1) = false := by
    apply bx_false
    intro i hi
    have hd : decide (i ≤ N + k ∧ N + k - i < N) = false := by simp; omega
    simp [hd]
  rw [h1, h2, h3, fx]
  symm
  apply wx_eq_bx
  intro t ht
  rw [hG t (by omega), hae1 (t + k + 1) (by omega)]
  have hd : decide (k + 1 + t ≤ N + k ∧ N + k - (k + 1 + t) < N) = true := by simp; omega
  show (A (t + k + 1) && B (N - 1 - t)) =
    (decide (k + 1 + t ≤ N + k ∧ N + k - (k + 1 + t) < N) && A (k + 1 + t) && B (N + k - (k + 1 + t)))
  rw [hd, show N + k - (k + 1 + t) = N - 1 - t by omega, show k + 1 + t = t + k + 1 by omega]
  all_goals simp

/-- **The whole multiplier**, from the equations of the tape as clean Boolean facts. -/
theorem tree_spec {N : Nat} (hN : 1 ≤ N) (A B ae be P : Nat → Bool) (T : Nat → Nat → Bool)
    (hae1 : ∀ x, x < N → ae x = A x) (hae2 : ∀ x, x < N → ae (N + x) = false)
    (hbe1 : ∀ x, x < N → be x = false) (hbe2 : ∀ x, x < N → be (N + x) = B x)
    (hll : ∀ k, k < N → ∀ t, t < N → T k t = (A t && be (k + N - t)))
    (hhl : ∀ k, k + 1 < N → ∀ t, t < N → T (N + k) t = (ae (t + k + 1) && B (N - 1 - t)))
    (hnode : ∀ k, k < 2 * N - 1 → ∀ g, g + 1 < N → T k (N + g) = (T k (2 * g) ^^ T k (2 * g + 1)))
    (hp : ∀ k, k < 2 * N - 1 → P k = T k (2 * N - 2)) :
    ∀ k, k < 2 * N - 1 → P k = bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) N) N := by
  intro k hk
  have inner : (fun i => bx (fun j => decide (i + j = k) && A i && B j) N)
      = (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) := by
    funext i
    exact bx_pair i k (A i) B N
  rw [inner, hp k hk, col_root hN (T k) (hnode k hk)]
  by_cases hkN : k < N
  · exact lower_leaves A B be (T k) k hkN hbe1 hbe2 (hll k hkN)
  · obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    exact upper_leaves A B ae (T (N + m)) m (by omega) hae1 hae2 (hhl m (by omega))

end TreeArith

/-! ## 2. Structure: `sv_structure` -/

/-- The rank: `(stage, node, 0)`. The padded copies `ae`, `be` first, then the leaves, then the XOR nodes in
order of `g` (node `g` reads positions `2g`, `2g + 1`: a leaf, or node `2g - N < g`), the outputs last. -/
def treeKey : SiteId → Key
  | .plain _ => (0, 0, 0)
  | .fam "g_ll" _ _ => (1, 0, 0)
  | .fam "g_hl" _ _ => (1, 0, 0)
  | .fam "g_node" _ [_, g] => (2, g.toNat, 0)
  | .fam _ _ _ => (3, 0, 0)

set_option maxHeartbeats 1000000 in
/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from the lexicographic key. -/
theorem tree_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := treeKey)
  all_goals (intros; sv_rowmajor; omega)

/-! ## 3. The ports -/

theorem tree_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Clmul.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 4. The statement: bridge and arithmetic; `sv_cover` closes the coverage -/

set_option maxHeartbeats 1000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := tree_struct N hN'
  refine CombTask.satisfiedAt_of_comb (tree_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_col_1 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have hkp : ∀ k, k < 2 * N - 1 → KnownBit st "p" k := fun k hk => (known_p_g_col_1 k (by omega)).2
    have hbits := TreeArith.tree_spec hN' x.getLsbD y.getLsbD (st.boolAt "ae") (st.boolAt "be")
      (st.boolAt "p") (st.cell "T" (2 * (N : Int) - 1))
      (by sv_bridge eq_ae_plain_0 with ba) (by sv_bridge eq_ae_plain_1)
      (by sv_bridge eq_be_plain_2) (by sv_bridge eq_be_plain_3 with bb)
      (by sv_bridge eq_T_g_ll_0 with ba) (by sv_bridge eq_T_g_hl_0 with bb)
      (by sv_bridge eq_T_g_node_0) (by sv_bridge eq_p_g_col_1)
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N - 1) hvp (by omega) hkp]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, TreeArith.getLsbD_ofBits, hbits k hk, ← TreeArith.coeff_eq]
    simp [hk]
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

end Submission
