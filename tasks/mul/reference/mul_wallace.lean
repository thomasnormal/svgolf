import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Reference solution 4 for task `mul`: a Wallace-tree multiplier (a tape of rows, 3:2 carry-save adders), proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. The design is `reference/mul_wallace.sv`: ONE 2-D packed array `T`, the TAPE, of
`3N-1` rows of `2N` bits. Rows `0 .. N-1` are the partial products (row `j` is `a · b[j] · 2^j`),
row `N` is an all-zero dummy row, so `N+1` rows are live at the start. Carry-save adder number `g`
(`g = 0 .. N-2`) reads the three oldest live rows `3g`, `3g+1`, `3g+2` and APPENDS the sum row
`x ^ y ^ z` at position `N+1+2g` and the carry row `maj(x, y, z) << 1` at position `N+2+2g`; after
the `N-1` adders two rows remain, at positions `3N-3` and `3N-2`, and a `2N`-bit ripple-carry
adder adds them. This is Wallace's reduction by groups of three rows, in its queue form (the live
rows shrink by a factor 2/3 per level). There is no stage loop, no localparam, no division and no
conditional generate: every index is affine in `N` and the genvars (`3*g+k`, `N+1+2*g`, `N+2+2*g`),
so the existing fragment of `sv_structure` / `sv_equations` reads the design as it is.

## Route (the file is in this order)

1. **Arithmetic** (`TapeArith`, plain Lean, no ls-sv): `csa_row` (a row of 3:2 counters with the
   carry row shifted by one column preserves the column-weighted sum, up to the dropped top carry),
   `lane_gated` (a partial-product row is the shifted `a`, gated by a bit of `b`), and `tape_mul`:
   the sum modulo `2^(2N)` of the LIVE window `[3g, N+1+2g)` of the tape (`csum V (3g) (N+1-g)`) is
   `a · b` for every `g ≤ N-1`, by induction on `g`: at `g = 0` the window is the partial products
   and the dummy row, and adder `g` replaces its first three rows by the two rows appended at its
   far end, which `csa_row` shows to have the same sum modulo `2^(2N)`. At `g = N-1` the window is
   the two last rows, and the final adder is `ripple_row` of the library.
2. **Structure** (`tape_struct`): `sv_structure` (`CombDesign ∧ Acyclic`); the goals compare 2-D windows and
   close by `intros; sv_rowmajor; omega`. The rank is a lexicographic key `(stage, adder)` of each
   site identity (`tapeKey`): inputs, constants and the dummy row, the partial products, the adders
   in order of `g` (an adder reads only rows below `N+1+2g`, which earlier adders wrote), the ripple
   adder column by column. `tape_struct` needs `maxHeartbeats 1000000`.
3. **Ports** (`tape_interface`): `sv_interface`.
4. **Equations, bridge and coverage** (`solution`): the printed equations of `sv_equations` are bridged to
   the clean facts of `tape_mul` one `sv_bridge eq_x` per fact (the `Int` index forms of the netlist
   against the `Nat` indices of the arithmetic: congruence and `omega`).
5. **Coverage** (`solution`, the same theorem): the coverage goals of `sv_equations` are the reads of the
   tape (a row `3g+k` or `3N-3`, `3N-2` at a column) and of the carry chain `K`; the closing
   `all_goals … sv_cover` proves them, solving the writer from the read (a partial product, the dummy
   row, or a sum or carry row of adder `(r-N-1)/2`).
-/

/-! ## 1. The arithmetic (plain Lean, `CombLib` only)

The Wallace tape multiplier: `tape_mul` proves `p = a * b` from the netlist equations as clean Boolean
facts about bit functions; nothing here mentions a design or a state. -/
namespace TapeArith
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


/-! ### Sums over a stretch of tape rows -/

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

/-- Three rows off the front. -/
theorem csum_front3 (V : Nat → Nat) (n s : Nat) :
    csum V s (n + 3) = V s + V (s + 1) + V (s + 2) + csum V (s + 3) n := by
  rw [csum_front, csum_front, csum_front]
  simp only [Nat.add_assoc, Nat.reduceAdd]

/-- Leaves: the first `N` rows hold the partial products, one row per bit of `b`. -/
theorem csum_leaves (a : Nat) (g : Nat → Bool) (V : Nat → Nat) (N : Nat)
    (hV : ∀ j, j < N → V j = (g j).toNat * (a * 2 ^ j)) :
    ∀ n, n ≤ N → csum V 0 n = a * bfVal g n := by
  intro n
  induction n with
  | zero => intro _; simp [csum, bfVal]
  | succ n ih =>
    intro hn
    have ih := ih (by omega)
    rw [csum, ih, Nat.zero_add, hV n (by omega)]
    simp only [bfVal]
    generalize 2 ^ n = P
    generalize (g n).toNat = B0
    generalize bfVal g n = F
    grind

/-- **The whole multiplier**, from the equations of the tape as clean Boolean facts. -/
theorem tape_mul {N : Nat} (hN : 1 ≤ N) (a b : BitVec N) (p : BitVec (2 * N))
    (ae : Nat → Bool) (T : Nat → Nat → Bool) (K : Nat → Bool)
    (hae1 : ∀ k, k < 2 * N - 1 → ae k = false)
    (hae2 : ∀ k, k < N → ae (2 * N - 1 + k) = a.getLsbD k)
    (hae3 : ∀ k, k < N → ae (3 * N - 1 + k) = false)
    (hleaf : ∀ j, j < N → ∀ c, c < 2 * N → T j c = (ae (c + (2 * N - 1 - j)) && b.getLsbD j))
    (hdum : ∀ c, c < 2 * N → T N c = false)
    (hsum : ∀ g, g < N - 1 → ∀ c, c < 2 * N →
      T (N + 1 + 2 * g) c = (T (3 * g) c ^^ T (3 * g + 1) c ^^ T (3 * g + 2) c))
    (hcar0 : ∀ g, g < N - 1 → T (N + 2 + 2 * g) 0 = false)
    (hcar : ∀ g, g < N - 1 → ∀ c, c < 2 * N - 1 →
      T (N + 2 + 2 * g) (c + 1) = ((T (3 * g) c && T (3 * g + 1) c) ||
        (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c))))
    (hK0 : K 0 = false)
    (hp : ∀ c, c < 2 * N → p.getLsbD c = (T (3 * N - 3) c ^^ T (3 * N - 2) c ^^ K c))
    (hK : ∀ c, c < 2 * N → K (c + 1) =
      ((T (3 * N - 3) c && T (3 * N - 2) c) || (K c && (T (3 * N - 3) c ^^ T (3 * N - 2) c)))) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * N = n + 1 := ⟨2 * N - 1, by omega⟩
  let V : Nat → Nat := fun m => bfVal (T m) (2 * N)
  -- the leaves: one shifted copy of `a` per bit of `b`
  have hleafV : ∀ j, j < N → V j = (b.getLsbD j).toNat * (a.toNat * 2 ^ j) := by
    intro j hj
    show bfVal (T j) (2 * N) = _
    have e1 : bfVal (T j) (2 * N) =
        bfVal (fun c => ae (c + (2 * N - 1 - j)) && b.getLsbD j) (2 * N) :=
      bfVal_congr (fun c hc => hleaf j hj c hc)
    rw [e1, lane_gated hN a ae hae1 hae2 hae3 j (b.getLsbD j) (fun _ => by omega)]
  have hdumV : V N = 0 := bfVal_false (fun c hc => hdum c hc)
  have hbase : csum V 0 (N + 1) = a.toNat * b.toNat := by
    show csum V 0 N + V (0 + N) = _
    rw [csum_leaves a.toNat b.getLsbD V N hleafV N (Nat.le_refl N), bfVal_bv, Nat.zero_add, hdumV]
    rfl
  -- one carry-save adder: rows 3g, 3g+1, 3g+2 are replaced by the two appended rows
  have hcsa : ∀ g, g < N - 1 → ∃ q, V (N + 1 + 2 * g) + V (N + 2 + 2 * g) + 2 ^ (2 * N) * q =
      V (3 * g) + V (3 * g + 1) + V (3 * g + 2) := by
    intro g hg
    have h := csa_row n (T (3 * g)) (T (3 * g + 1)) (T (3 * g + 2)) (T (N + 1 + 2 * g))
      (fun c => (T (3 * g) c && T (3 * g + 1) c) || (T (3 * g + 2) c && (T (3 * g) c ^^ T (3 * g + 1) c)))
      (T (N + 2 + 2 * g))
      (fun c hc => hsum g hg c (by omega)) (fun _ _ => rfl) (hcar0 g hg)
      (fun c hc => hcar g hg c (by omega))
    rw [← hn] at h
    exact ⟨_, by simp only [V]; omega⟩
  -- the invariant: the live window `[3g, N+1+2g)` sums to `a * b` modulo `2^(2N)`
  have hwin : ∀ g, g ≤ N - 1 → csum V (3 * g) (N + 1 - g) % 2 ^ (2 * N) =
      (a.toNat * b.toNat) % 2 ^ (2 * N) := by
    intro g
    induction g with
    | zero => intro _; simpa using congrArg (· % 2 ^ (2 * N)) hbase
    | succ g ih =>
      intro hg
      have ih := ih (by omega)
      obtain ⟨q, hq⟩ := hcsa g (by omega)
      have e1 : csum V (3 * g) (N + 1 - g) = V (3 * g) + V (3 * g + 1) + V (3 * g + 2) +
          csum V (3 * g + 3) (N - 2 - g) := by
        rw [show N + 1 - g = (N - 2 - g) + 3 by omega, csum_front3]
      have e2 : csum V (3 * (g + 1)) (N + 1 - (g + 1)) =
          csum V (3 * g + 3) (N - 2 - g) + V (N + 1 + 2 * g) + V (N + 2 + 2 * g) := by
        rw [show N + 1 - (g + 1) = (N - 2 - g) + 2 by omega, show 3 * (g + 1) = 3 * g + 3 by omega]
        show csum V (3 * g + 3) (N - 2 - g + 1) + V (3 * g + 3 + (N - 2 - g + 1)) = _
        show csum V (3 * g + 3) (N - 2 - g) + V (3 * g + 3 + (N - 2 - g)) +
          V (3 * g + 3 + (N - 2 - g + 1)) = _
        rw [show 3 * g + 3 + (N - 2 - g) = N + 1 + 2 * g by omega,
          show 3 * g + 3 + (N - 2 - g + 1) = N + 2 + 2 * g by omega]
      rw [e1] at ih
      rw [e2]
      have h3 : (csum V (3 * g + 3) (N - 2 - g) + V (N + 1 + 2 * g) + V (N + 2 + 2 * g) +
          2 ^ (2 * N) * q) % 2 ^ (2 * N) =
          (V (3 * g) + V (3 * g + 1) + V (3 * g + 2) + csum V (3 * g + 3) (N - 2 - g)) % 2 ^ (2 * N) := by
        congr 1; omega
      rw [Nat.add_mul_mod_self_left] at h3
      rw [h3, ih]
  -- the last window: the two remaining rows, at positions `3N-3` and `3N-2`
  have hlast := hwin (N - 1) (Nat.le_refl _)
  rw [show N + 1 - (N - 1) = 2 by omega] at hlast
  have e3 : csum V (3 * (N - 1)) 2 = V (3 * N - 3) + V (3 * N - 2) := by
    show csum V (3 * (N - 1)) 0 + V (3 * (N - 1) + 0) + V (3 * (N - 1) + 1) = _
    rw [show 3 * (N - 1) + 0 = 3 * N - 3 by omega, show 3 * (N - 1) + 1 = 3 * N - 2 by omega]
    simp [csum]
  rw [e3] at hlast
  -- the final adder
  have hrip := ripple_row (2 * N) (T (3 * N - 3)) (T (3 * N - 2))
    (fun c => T (3 * N - 3) c ^^ T (3 * N - 2) c) p.getLsbD K
    (fun _ _ => rfl) (fun c hc => hp c hc) (fun c hc => hK c hc)
  rw [hK0, bfVal_bv] at hrip
  simp only [Bool.toNat_false, Nat.add_zero] at hrip
  have hlt : p.toNat < 2 ^ (2 * N) := p.isLt
  have hpv : p.toNat = (V (3 * N - 3) + V (3 * N - 2)) % 2 ^ (2 * N) := by
    have := sum_split hlt (t := V (3 * N - 3) + V (3 * N - 2)) (q := (K (2 * N)).toNat)
      (by simp only [V]; omega)
    exact this.1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hpv, hlast]

end TapeArith
namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf


/-! ## 2. Structure: `sv_structure` -/

/-- The rank: `(stage, adder, phase)`. -/
def tapeKey : SiteId → Key
  | .plain _ => (0, 0, 0)
  | .fam "g_lc" _ _ => (1, 0, 0)
  | .fam "g_csa" _ [g] => (2, g.toNat, 0)
  | .fam "g_sum" _ [g, _] => (2, g.toNat, 0)
  | .fam "g_car" _ [g, _] => (2, g.toNat, 0)
  | .fam "g_fin" 0 [c] => (3, c.toNat, 1)
  | .fam "g_fin" _ [c] => (3, c.toNat, 0)
  | .fam _ _ _ => (3, 0, 0)

set_option maxHeartbeats 1000000 in
/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from the lexicographic key: ONE application of the
soundness theorem and one round of obligations for both. -/
theorem tape_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := tapeKey)
  all_goals (intros; sv_rowmajor; omega)


/-! ## 3. The ports -/

theorem tape_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface


/-! ## 4. Bridge, equations and coverage of the tape reads

Every cell the design reads must have a writer. A read of the tape `T` at row `r`, column `c` is
written by one of five assigns: the partial-product loop (a row `r < N`), the dummy row `r = N`,
the sum row of an adder (`r = N+1+2g`), or the carry row of an adder (`r = N+2+2g`: column 0 by its
own assign, columns `c ≥ 1` by the carry loop). `sv_cover` closes these coverage goals itself: it
solves the adder index from the read's row (`g := (r - N - 1) / 2`, the parity is part of the
condition it hands to `omega`) and walks the disjunction of writers (`CombCover.lean`). -/

set_option maxHeartbeats 500000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN
  obtain ⟨hc, ha, hso⟩ := tape_struct N hN'
  refine CombTask.satisfiedAt_of_comb (tape_interface N hN' hc) hc ha ?_
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
    refine TapeArith.tape_mul hN' x y (XF.bv (2 * N) (st.boolAt "p")) (st.boolAt "ae")
      (st.cell "T" (2 * N)) (st.boolAt "K") ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · sv_bridge eq_ae_plain_0
    · sv_bridge eq_ae_plain_1 with ba
    · sv_bridge eq_ae_plain_2
    · sv_bridge eq_T_g_lc_0 with bb
    · sv_bridge eq_T_plain_3
    · sv_bridge eq_T_g_sum_0
    · sv_bridge eq_T_g_csa_0
    · sv_bridge eq_T_g_car_0
    · sv_bridge eq_K_plain_4
    · sv_bridge eq_p_g_fin_0 with XF.getLsbD_bv
    · sv_bridge eq_K_g_fin_1
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | (intros; rfl) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
