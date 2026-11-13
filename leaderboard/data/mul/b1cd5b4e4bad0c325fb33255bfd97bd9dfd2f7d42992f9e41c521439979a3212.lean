import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# A carry-save tree multiplier with TWO-ROW leaves for task `mul`, proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. The design is `mul_tree_h.sv`: the `N` partial-product rows are taken
two at a time, `H = ceil(N/2)` leaves (nodes `H-1 .. 2H-2` of a binary HEAP, node `k` having the
children `2k+1`, `2k+2`, the root node 0), each leaf a carry-save pair `(S, C) = (pp[2j], pp[2j+1])`;
EVERY internal node is a 4:2 compressor, two stacked rows of full adders, on its children's pairs; the
root's two rows go through a ripple-carry adder.

The new thing is the **localparam**: `localparam integer H = (N + 1) / 2;` (the number of leaves, not
an affine function of `N`). The `sv_comb` tactics read a localparam as one more named constant of `N`
(PROVING.md, section 4); its definition is inlined into every obligation as `(↑N + 1) / 2`, which
`omega` knows (floor division by a literal). That one line replaces what the single-row heap of
`mul_tree.sv` needs four extra loops and a constant select (`th`/`nth`) for.

## Route (the file is in this order)

1. **Arithmetic** (`HeapArith`, plain Lean, no ls-sv): `csa_row`, `node_sum`, `lane_gated` as in
   `mul_tree.lean`, and `heap_mul`: the sums over the CUT `{t, …, 2t}` of the heap are invariant
   modulo `2^(2N)` while `t` runs from `H-1` (the leaves: `a · b` exactly, two rows per leaf, `b`
   zero-extended) down to `0` (the root). There is no pairing case: every internal node compresses.
2. **Structure** (`tree_struct`): `sv_structure` (`CombDesign ∧ Acyclic`); the goals compare 2-D windows and close
   by `intros; sv_rowmajor; omega`, with `H` inlined. The rank is a lexicographic key `(stage, node
   order, phase)` (`treeKey`).
3. **Ports** (`tree_interface`): `sv_interface`; the valuation of a design that has localparams
   (`Summary.val`) is the tactic's business.
4. **Equations, bridge and coverage** (`solution`): the printed equations of `sv_equations` (with
   `((N : Int) + 1) / 2` in the place of `H`) are bridged to the clean facts of `heap_mul` one
   `sv_bridge eq_x` per fact (the `Int` index forms of the netlist against the `Nat` indices of the
   arithmetic: congruence and `omega`).
5. **Coverage** (`solution`, the same theorem): the coverage goals of `sv_equations` are the heap reads;
   the closing `all_goals … sv_cover` proves them, solving the writer from the read.
-/

/-! ## 1. The arithmetic (plain Lean, `CombLib` only)

The heap-indexed 4:2 carry-save tree multiplier with two-row leaves: `heap_mul` proves `p = a * b` from
the netlist equations as clean Boolean facts about bit functions; nothing here mentions a design or a
state. -/
namespace HeapArith
open LeanModels.Sv.CombLib

theorem bfVal_false {f : Nat → Bool} {n : Nat} (h : ∀ j < n, f j = false) : bfVal f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bfVal]
    rw [ih (fun j hj => h j (by omega)), h n (by omega)]
    simp

/-- A row of 3:2 counters, the carry row shifted one column: column `c` of `s`/`cy`, with
`sh (c+1) = cy c`. The top carry `cy (W-1)` is dropped from `sh`. -/
theorem csa_row (n : Nat) (x y z s cy sh : Nat → Bool)
    (hs : ∀ c < n + 1, s c = (x c ^^ y c ^^ z c))
    (hcy : ∀ c < n + 1, cy c = ((x c && y c) || (z c && (x c ^^ y c))))
    (hsh0 : sh 0 = false) (hsh : ∀ c, c + 1 < n + 1 → sh (c + 1) = cy c) :
    bfVal s (n + 1) + bfVal sh (n + 1) + 2 ^ (n + 1) * (cy n).toNat =
      bfVal x (n + 1) + bfVal y (n + 1) + bfVal z (n + 1) := by
  have key : ∀ m, m ≤ n + 1 →
      bfVal s m + 2 * bfVal cy m = bfVal x m + bfVal y m + bfVal z m := by
    intro m
    induction m with
    | zero => intro _; simp [bfVal]
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hfa := fullAdder_arith (x m) (y m) (z m)
      rw [← hs m (by omega), ← hcy m (by omega)] at hfa
      simp only [bfVal]
      have : 2 ^ m * ((s m).toNat + 2 * (cy m).toNat) =
          2 ^ m * ((x m).toNat + (y m).toNat + (z m).toNat) := by rw [hfa]
      generalize (s m).toNat = S0 at *
      generalize (cy m).toNat = C0 at *
      generalize (x m).toNat = X0 at *
      generalize (y m).toNat = Y0 at *
      generalize (z m).toNat = Z0 at *
      generalize 2 ^ m = P at *
      grind
  have hsh' : bfVal sh (n + 1) = 2 * bfVal cy n := by
    rw [bfVal_shift, hsh0]
    have : bfVal (fun j => sh (j + 1)) n = bfVal cy n :=
      bfVal_congr (fun j hj => hsh j (by omega))
    rw [this]; simp
  have hk := key (n + 1) (Nat.le_refl _)
  rw [hsh']
  simp only [bfVal, Nat.pow_succ] at hk ⊢
  generalize 2 ^ n = P at *
  generalize (cy n).toNat = C0 at *
  grind

/-- A 4:2 compressor node: two stacked rows of counters, on a window of `n+1` columns, preserves
the sum exactly up to the two dropped top carries. -/
theorem node_sum (n : Nat) (SL CL SR CR S C X Y : Nat → Bool)
    (hX : ∀ c < n + 1, X c = (SL c ^^ CL c ^^ SR c))
    (hY0 : Y 0 = false)
    (hY : ∀ c, c + 1 < n + 1 → Y (c + 1) = ((SL c && CL c) || (SR c && (SL c ^^ CL c))))
    (hS : ∀ c < n + 1, S c = (X c ^^ Y c ^^ CR c))
    (hC0 : C 0 = false)
    (hC : ∀ c, c + 1 < n + 1 → C (c + 1) = ((X c && Y c) || (CR c && (X c ^^ Y c)))) :
    ∃ q, bfVal S (n + 1) + bfVal C (n + 1) + 2 ^ (n + 1) * q =
      (bfVal SL (n + 1) + bfVal CL (n + 1)) + (bfVal SR (n + 1) + bfVal CR (n + 1)) := by
  have h1 := csa_row n SL CL SR X (fun c => (SL c && CL c) || (SR c && (SL c ^^ CL c))) Y
    hX (fun _ _ => rfl) hY0 hY
  have h2 := csa_row n X Y CR S (fun c => (X c && Y c) || (CR c && (X c ^^ Y c))) C
    hS (fun _ _ => rfl) hC0 hC
  refine ⟨(((SL n && CL n) || (SR n && (SL n ^^ CL n))).toNat) +
    ((X n && Y n) || (CR n && (X n ^^ Y n))).toNat, ?_⟩
  simp only [Nat.mul_add] at h1 h2 ⊢
  generalize 2 ^ (n + 1) = P at *
  omega


/-! ### The leaves: a gated, shifted copy of `a` -/

/-- The zero-padded copy `ae` of `a`, read at offset `2N-1-r`, is `a` shifted left by `r`
(for `r ≤ N`: nothing is cut off). -/
theorem lane_val {N : Nat} (hN : 1 ≤ N) (a : BitVec N) (ae : Nat → Bool)
    (h1 : ∀ k, k < 2 * N - 1 → ae k = false)
    (h2 : ∀ k, k < N → ae (2 * N - 1 + k) = a.getLsbD k)
    (h3 : ∀ k, k < N → ae (3 * N - 1 + k) = false)
    (r : Nat) (hr : r ≤ N) :
    bfVal (fun c => ae (c + (2 * N - 1 - r))) (2 * N) = a.toNat * 2 ^ r := by
  have hs1 := bfVal_split (fun c => ae (c + (2 * N - 1 - r))) r (2 * N - r)
  rw [show r + (2 * N - r) = 2 * N by omega] at hs1
  rw [hs1]
  have hlow : bfVal (fun c => ae (c + (2 * N - 1 - r))) r = 0 :=
    bfVal_false (fun j hj => h1 _ (by omega))
  rw [hlow]
  have hs2 := bfVal_split (fun j => ae (r + j + (2 * N - 1 - r))) N (N - r)
  rw [show N + (N - r) = 2 * N - r by omega] at hs2
  rw [hs2]
  have hmid : bfVal (fun j => ae (r + j + (2 * N - 1 - r))) N = a.toNat := by
    rw [← bfVal_bv a]
    exact bfVal_congr (fun j hj => by
      have : r + j + (2 * N - 1 - r) = 2 * N - 1 + j := by omega
      rw [this]; exact h2 j hj)
  have hhigh : bfVal (fun j => (fun j => ae (r + j + (2 * N - 1 - r))) (N + j)) (N - r) = 0 :=
    bfVal_false (fun j hj => by
      show ae (r + (N + j) + (2 * N - 1 - r)) = false
      have : r + (N + j) + (2 * N - 1 - r) = 3 * N - 1 + j := by omega
      rw [this]; exact h3 j (by omega))
  rw [hmid, hhigh]
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  rw [Nat.mul_comm]

/-- The value of a gated lane. -/
theorem lane_gated {N : Nat} (hN : 1 ≤ N) (a : BitVec N) (ae : Nat → Bool)
    (h1 : ∀ k, k < 2 * N - 1 → ae k = false)
    (h2 : ∀ k, k < N → ae (2 * N - 1 + k) = a.getLsbD k)
    (h3 : ∀ k, k < N → ae (3 * N - 1 + k) = false)
    (r : Nat) (g : Bool) (hg : g = true → r ≤ N) :
    bfVal (fun c => ae (c + (2 * N - 1 - r)) && g) (2 * N) = g.toNat * (a.toNat * 2 ^ r) := by
  rw [bfVal_and]
  cases g with
  | false => simp
  | true => simp only [Bool.toNat_true]; rw [lane_val hN a ae h1 h2 h3 r (hg rfl)]

/-! ### Sums over a stretch of heap nodes -/

def csum (V : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, n + 1 => csum V s n + V (s + n)

theorem csum_front (V : Nat → Nat) (n : Nat) : ∀ s, csum V s (n + 1) = V s + csum V (s + 1) n := by
  induction n with
  | zero => intro s; simp [csum]
  | succ n ih =>
    intro s
    have e : s + 1 + n = s + (n + 1) := by omega
    have e2 : csum V (s + 1) (n + 1) = csum V (s + 1) n + V (s + 1 + n) := rfl
    rw [csum, ih s, e2, e]
    omega

/-- Leaves: `csum` of the leaf values is `a · b`, two rows (two bits of `b`) per leaf. -/
theorem csum_leaves2 (H : Nat) (a : Nat) (g : Nat → Bool) (V : Nat → Nat)
    (hV : ∀ j, j < H → V (H - 1 + j) =
      (g (2 * j)).toNat * (a * 2 ^ (2 * j)) + (g (2 * j + 1)).toNat * (a * 2 ^ (2 * j + 1))) :
    ∀ n, n ≤ H → csum V (H - 1) n = a * bfVal g (2 * n) := by
  intro n
  induction n with
  | zero => intro _; simp [csum, bfVal]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    rw [csum, ih, hV n (by omega), show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [bfVal, Nat.pow_succ]
    generalize 2 ^ (2 * n) = P
    generalize (g (2 * n)).toNat = B0
    generalize (g (2 * n + 1)).toNat = B1
    generalize bfVal g (2 * n) = F
    grind

/-- **The whole multiplier**, from the equations of the netlist as clean Boolean facts. `H` is the
number of leaves, `N ≤ 2H ≤ N + 1`: leaf `j` of the heap (node `H - 1 + j`) holds the rows `2j`, `2j+1`
of the partial products. -/
theorem heap_mul {N H : Nat} (hN : 1 ≤ N) (hH1 : N ≤ 2 * H) (hH2 : 2 * H ≤ N + 1)
    (a b : BitVec N) (p : BitVec (2 * N))
    (ae bb : Nat → Bool) (S C X Y : Nat → Nat → Bool) (R : Nat → Bool)
    (hae1 : ∀ k, k < 2 * N - 1 → ae k = false)
    (hae2 : ∀ k, k < N → ae (2 * N - 1 + k) = a.getLsbD k)
    (hae3 : ∀ k, k < N → ae (3 * N - 1 + k) = false)
    (hbb1 : ∀ k, k < N → bb k = b.getLsbD k)
    (hbb2 : ∀ k, N ≤ k → k < 2 * H → bb k = false)
    (hleafS : ∀ j, j < H → ∀ c, c < 2 * N →
      S (H - 1 + j) c = (ae (c + (2 * N - 1 - 2 * j)) && bb (2 * j)))
    (hleafC : ∀ j, j < H → ∀ c, c < 2 * N →
      C (H - 1 + j) c = (ae (c + (2 * N - 1 - (2 * j + 1))) && bb (2 * j + 1)))
    (hY0 : ∀ k, k < H - 1 → Y k 0 = false)
    (hC0 : ∀ k, k < H - 1 → C k 0 = false)
    (hX : ∀ k, k < H - 1 → ∀ c, c < 2 * N →
      X k c = (S (2 * k + 1) c ^^ C (2 * k + 1) c ^^ S (2 * k + 2) c))
    (hS : ∀ k, k < H - 1 → ∀ c, c < 2 * N → S k c = (X k c ^^ Y k c ^^ C (2 * k + 2) c))
    (hY : ∀ k, k < H - 1 → ∀ c, c < 2 * N - 1 →
      Y k (c + 1) = ((S (2 * k + 1) c && C (2 * k + 1) c) ||
        (S (2 * k + 2) c && (S (2 * k + 1) c ^^ C (2 * k + 1) c))))
    (hC : ∀ k, k < H - 1 → ∀ c, c < 2 * N - 1 →
      C k (c + 1) = ((X k c && Y k c) || (C (2 * k + 2) c && (X k c ^^ Y k c))))
    (hR0 : R 0 = false)
    (hp : ∀ c, c < 2 * N → p.getLsbD c = (S 0 c ^^ C 0 c ^^ R c))
    (hR : ∀ c, c < 2 * N → R (c + 1) =
      ((S 0 c && C 0 c) || (R c && (S 0 c ^^ C 0 c)))) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * N = n + 1 := ⟨2 * N - 1, by omega⟩
  let V : Nat → Nat := fun m => bfVal (S m) (2 * N) + bfVal (C m) (2 * N)
  -- the leaves: two shifted, gated copies of `a` per leaf
  have hleaf : ∀ j, j < H → V (H - 1 + j) =
      (bb (2 * j)).toNat * (a.toNat * 2 ^ (2 * j)) +
        (bb (2 * j + 1)).toNat * (a.toNat * 2 ^ (2 * j + 1)) := by
    intro j hj
    have e1 : bfVal (S (H - 1 + j)) (2 * N) =
        bfVal (fun c => ae (c + (2 * N - 1 - 2 * j)) && bb (2 * j)) (2 * N) :=
      bfVal_congr (fun c hc => hleafS j hj c hc)
    have e2 : bfVal (C (H - 1 + j)) (2 * N) =
        bfVal (fun c => ae (c + (2 * N - 1 - (2 * j + 1))) && bb (2 * j + 1)) (2 * N) :=
      bfVal_congr (fun c hc => hleafC j hj c hc)
    show bfVal (S (H - 1 + j)) (2 * N) + bfVal (C (H - 1 + j)) (2 * N) = _
    rw [e1, e2, lane_gated hN a ae hae1 hae2 hae3 (2 * j) (bb (2 * j)) (fun hg => by
        by_cases h : N ≤ 2 * j
        · rw [hbb2 (2 * j) h (by omega)] at hg; exact absurd hg (by simp)
        · omega),
      lane_gated hN a ae hae1 hae2 hae3 (2 * j + 1) (bb (2 * j + 1)) (fun hg => by
        by_cases h : N ≤ 2 * j + 1
        · rw [hbb2 (2 * j + 1) h (by omega)] at hg; exact absurd hg (by simp)
        · omega)]
  -- `b`, zero-extended, is the gate bits
  have hbv : bfVal bb (2 * H) = b.toNat := by
    have hs := bfVal_split bb N (2 * H - N)
    rw [show N + (2 * H - N) = 2 * H by omega] at hs
    rw [hs]
    have h1 : bfVal bb N = b.toNat := by
      rw [← bfVal_bv b]; exact bfVal_congr (fun j hj => hbb1 j hj)
    have h2 : bfVal (fun j => bb (N + j)) (2 * H - N) = 0 :=
      bfVal_false (fun j hj => hbb2 (N + j) (by omega) (by omega))
    rw [h1, h2]; simp
  have hleaves : csum V (H - 1) H = a.toNat * b.toNat := by
    rw [csum_leaves2 H a.toNat bb V hleaf H (Nat.le_refl H), hbv]
  -- the nodes: every internal node is a 4:2 compressor
  have hnode : ∀ k, k < H - 1 → ∃ q, V k + 2 ^ (2 * N) * q = V (2 * k + 1) + V (2 * k + 2) := by
    intro k hk
    obtain ⟨q, hq⟩ := node_sum n (S (2 * k + 1)) (C (2 * k + 1)) (S (2 * k + 2)) (C (2 * k + 2))
      (S k) (C k) (X k) (Y k)
      (fun c hc => hX k hk c (by omega)) (hY0 k hk)
      (fun c hc => hY k hk c (by omega))
      (fun c hc => hS k hk c (by omega))
      (hC0 k hk)
      (fun c hc => hC k hk c (by omega))
    rw [← hn] at hq
    exact ⟨q, by simp only [V]; omega⟩
  -- the cut sums
  have hcut : ∀ t, t < H - 1 → ∃ q, csum V t (t + 1) + 2 ^ (2 * N) * q = csum V (t + 1) (t + 2) := by
    intro t ht
    obtain ⟨q, hq⟩ := hnode t ht
    refine ⟨q, ?_⟩
    have f1 : csum V t (t + 1) = V t + csum V (t + 1) t := csum_front V t t
    have f2 : csum V (t + 1) (t + 2) = csum V (t + 1) t + V (t + 1 + t) + V (t + 1 + (t + 1)) := rfl
    rw [f1, f2, show t + 1 + t = 2 * t + 1 by omega, show t + 1 + (t + 1) = 2 * t + 2 by omega]
    omega
  have hdown : ∀ d, d ≤ H - 1 → csum V (H - 1 - d) (H - 1 - d + 1) % 2 ^ (2 * N) =
      (a.toNat * b.toNat) % 2 ^ (2 * N) := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [show H - 1 - 0 + 1 = H by omega, Nat.sub_zero, hleaves]
    | succ d ih =>
      intro hd
      have ih := ih (by omega)
      obtain ⟨q, hq⟩ := hcut (H - 1 - (d + 1)) (by omega)
      rw [show H - 1 - (d + 1) + 1 = H - 1 - d by omega,
        show H - 1 - (d + 1) + 2 = H - 1 - d + 1 by omega] at hq
      rw [← ih, ← hq, Nat.add_mul_mod_self_left, show H - 1 - (d + 1) + 1 = H - 1 - d by omega]
  have hroot := hdown (H - 1) (Nat.le_refl _)
  rw [Nat.sub_self, show (0 : Nat) + 1 = 1 from rfl] at hroot
  have hV0 : csum V 0 1 = V 0 := by simp [csum]
  rw [hV0] at hroot
  -- the final adder
  have hrip := ripple_row (2 * N) (S 0) (C 0) (fun c => S 0 c ^^ C 0 c) p.getLsbD R
    (fun _ _ => rfl) (fun c hc => hp c hc) (fun c hc => hR c hc)
  rw [hR0, bfVal_bv] at hrip
  simp only [Bool.toNat_false, Nat.add_zero] at hrip
  have hlt : p.toNat < 2 ^ (2 * N) := p.isLt
  have hpv : p.toNat = V 0 % 2 ^ (2 * N) := by
    have := sum_split hlt (t := V 0) (q := (R (2 * N)).toNat) (by simp only [V]; omega)
    exact this.1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hpv, hroot]

end HeapArith

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf


/-! ## 2. Structure: `sv_structure` -/

/-- The rank: `(stage, node order, phase)`. Inputs and constants first, then the leaves, then the
internal nodes from the last (deepest, highest heap index) to the root, in two phases (the first row of
counters, then the second), then the ripple final adder column by column. `H = (N + 1) / 2` is the
number of leaves. -/
def treeKey (N : Nat) : SiteId → Key
  | .plain _ => (0, 0, 0)
  | .fam "g_lc" _ _ => (1, 0, 0)
  | .fam "g_node" _ [k] => (2, (N + 1) / 2 - 1 - k.toNat, 0)
  | .fam "g_col" 0 [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 1)
  | .fam "g_col" _ [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 2)
  | .fam "g_car" 0 [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 1)
  | .fam "g_car" _ [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 2)
  | .fam "g_fin" 0 [c] => (3, c.toNat, 1)
  | .fam "g_fin" _ [c] => (3, c.toNat, 0)
  | .fam _ _ _ => (3, 0, 0)

set_option maxHeartbeats 1000000 in
/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from the lexicographic key: ONE application of the
soundness theorem and one round of obligations for both. -/
theorem tree_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := treeKey N)
  all_goals (intros; sv_rowmajor; omega)

/-! ## 3. The ports (the task's `Interface`)

`sv_interface`, for a design with a localparam: the valuation is `Summary.val` (the parameters zipped
with the arguments, then the localparams evaluated over them), which the tactic unfolds itself. -/

theorem tree_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface


/-! ## 4. Bridge, equations and coverage of the heap reads

Every cell the tree reads must have a writer. The heap rows `[0, H-1)` are written by the node loop,
the rows `[H-1, 2H-1)` by the leaf loop; a carry row is also written in column 0 by its own assign.
`sv_cover` closes these coverage goals itself (it solves the writer's loop indices from the read's row
and column and walks the disjunction of writers, `CombCover.lean`); the number of leaves `H` is
`((N : Int) + 1) / 2`, which `omega` reads. -/

set_option maxHeartbeats 600000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := tree_struct N hN'
  refine CombTask.satisfiedAt_of_comb (tree_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_fin_0 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N) hvp (by omega)
      (fun k hk => (known_p_g_fin_0 k (by omega)).2)]
    congr 2
    refine HeapArith.heap_mul (H := (N + 1) / 2) hN' (by omega) (by omega) x y
      (XF.bv (2 * N) (st.boolAt "p")) (st.boolAt "ae") (st.boolAt "bb") (st.cell "S" (2 * N))
      (st.cell "C" (2 * N)) (st.cell "X" (2 * N)) (st.cell "Y" (2 * N)) (st.boolAt "R")
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · sv_bridge eq_ae_plain_0
    · sv_bridge eq_ae_plain_1 with ba
    · sv_bridge eq_ae_plain_2
    · sv_bridge eq_bb_plain_3 with bb
    · intro k hk1 hk2
      sv_bridge (eq_bb_plain_4 (k - N) (by omega))
    · sv_bridge eq_S_g_lc_0
    · sv_bridge eq_C_g_lc_1
    · sv_bridge eq_Y_g_node_0
    · sv_bridge eq_C_g_node_1
    · sv_bridge eq_X_g_col_0
    · sv_bridge eq_S_g_col_1
    · sv_bridge eq_Y_g_car_0
    · sv_bridge eq_C_g_car_1
    · sv_bridge eq_R_plain_7
    · sv_bridge eq_p_g_fin_0 with XF.getLsbD_bv
    · sv_bridge eq_R_g_fin_1
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | (intros; rfl) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
