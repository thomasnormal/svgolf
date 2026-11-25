import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.Lib.Prefix

/-!
# Task `mul`: 4:2 carry-save heap multiplier with hybrid ripple + sparse-5 Kogge-Stone final adder

Proved for every `N` with `1 ≤ N < 2^20`:

1. **Arithmetic** (`HeapArith`):
   - `hybrid_adder_bits`: the hybrid final adder (low `M = 3N/4` ripple bits, `FQ = (2N - M - 1)/5`
     5-bit blocks with Kogge-Stone block-prefix over `FL = $clog2(FQ + 1)` levels and local
     carry ripple, and `FR = 2N - M - 5*FQ` tail late-carry ripple bits) produces the exact same
     sum bits as a canonical `2N`-bit ripple-carry adder on `(S[0], C[0])`.
   - `heap_mul0` / `heap_mul_hybrid`: the two-row-per-leaf 4:2 compressor heap reduces the
     `N` partial-product rows to `(S[0], C[0])` invariant modulo `2^(2N)`, and the hybrid final
     adder sums `(S[0], C[0])` modulo `2^(2N)` to `a * b`.
2. **Structure & Ports** (`mul_struct`, `mul_interface`): `sv_structure` with lexicographic rank
   `mulKey N` proves `CombDesign`, `Acyclic`, and `SharedObl`; `sv_interface` checks the ports.
3. **Equations, bridge, and coverage** (`solution`): `sv_equations` extracts the Boolean netlist
   equations and bit knownness; `sv_bridge` and direct cast lemmas connect them to
   `heap_mul_hybrid`; `sv_cover` closes all read-coverage obligations.
-/

/-! ## 1. The arithmetic (plain Lean, `CombLib` and `Lib.Prefix` only) -/

namespace HeapArith
open LeanModels.Sv.CombLib LeanModels.Sv.Lib

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

/-- The zero-padded copy `ae` of `a`, read at offset `2N-1-r`, is `a` shifted left by `r`. -/
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

/-- The Kogge-Stone recurrence on (generate, propagate) pairs. -/
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

/-- The hybrid final adder (low ripple `M` bits + `FQ` sparse-5 Kogge-Stone blocks + `FR` tail
late-carry ripple bits) produces the exact sum bits of a canonical `W`-bit ripple-carry adder on
`(s0, c0)` with carry-in `false`. -/
theorem hybrid_adder_bits {W M U FQ FR FL : Nat}
    (hMU : M + U = W) (hU : 5 * FQ + FR = U) (hFL : FQ + 1 ≤ 2 ^ FL)
    (s0 c0 pout R fp fg Rt : Nat → Bool)
    (fgg fpp fcc bg bp : Nat → Nat → Bool)
    (hR0 : R 0 = false)
    (hR : ∀ c, c < M → R (c + 1) = (if (c0 c ^^ s0 c) = true then R c else s0 c))
    (hp_lo : ∀ c, c < M → pout c = (s0 c ^^ (c0 c ^^ R c)))
    (hfp : ∀ c, c < U → fp c = (s0 (M + c) ^^ c0 (M + c)))
    (hfg : ∀ c, c < U → fg c = (s0 (M + c) && c0 (M + c)))
    (hfgg0 : ∀ j, j < FQ → fgg j 0 = false)
    (hfpp0 : ∀ j, j < FQ → fpp j 0 = true)
    (hfgg : ∀ j, j < FQ → ∀ t, t < 5 →
      fgg j (t + 1) = (fg (5 * j + t) || (fp (5 * j + t) && fgg j t)))
    (hfpp : ∀ j, j < FQ → ∀ t, t < 5 →
      fpp j (t + 1) = (fp (5 * j + t) && fpp j t))
    (hbg00 : bg 0 0 = R M)
    (hbp00 : bp 0 0 = false)
    (hbg_blk : ∀ j, j < FQ → bg 0 (j + 1) = fgg j 5)
    (hbp_blk : ∀ j, j < FQ → bp 0 (j + 1) = fpp j 5)
    (hbg_op : ∀ fl, fl < FL → ∀ j, j < FQ + 1 → 2 ^ fl ≤ j →
      bg (fl + 1) j = (bg fl j || (bp fl j && bg fl (j - 2 ^ fl))))
    (hbp_op : ∀ fl, fl < FL → ∀ j, j < FQ + 1 → 2 ^ fl ≤ j →
      bp (fl + 1) j = (bp fl j && bp fl (j - 2 ^ fl)))
    (hbg_pass : ∀ fl, fl < FL → ∀ j, j < FQ + 1 → ¬ 2 ^ fl ≤ j →
      bg (fl + 1) j = bg fl j)
    (hbp_pass : ∀ fl, fl < FL → ∀ j, j < FQ + 1 → ¬ 2 ^ fl ≤ j →
      bp (fl + 1) j = bp fl j)
    (hfcc0 : ∀ j, j < FQ → fcc j 0 = bg FL j)
    (hfcc : ∀ j, j < FQ → ∀ t, t < 5 →
      fcc j (t + 1) = (if fp (5 * j + t) = true then fcc j t else s0 (M + 5 * j + t)))
    (hp_blk : ∀ j, j < FQ → ∀ t, t < 5 →
      pout (M + 5 * j + t) = (s0 (M + 5 * j + t) ^^ (c0 (M + 5 * j + t) ^^ fcc j t)))
    (hRt0 : Rt 0 = bg FL FQ)
    (hRt : ∀ t, t < FR →
      Rt (t + 1) = (if fp (5 * FQ + t) = true then Rt t else s0 (M + 5 * FQ + t)))
    (hp_tail : ∀ t, t < FR →
      pout (M + 5 * FQ + t) = (s0 (M + 5 * FQ + t) ^^ (c0 (M + 5 * FQ + t) ^^ Rt t))) :
    ∀ c, c < W → pout c = (s0 c ^^ c0 c ^^ rippleCarry s0 c0 false c) := by
  let rc : Nat → Bool := rippleCarry s0 c0 false
  -- 1. Low ripple carries match `rc`.
  have hR_eq : ∀ c, c ≤ M → R c = rc c := by
    intro c
    induction c with
    | zero => intro _; rw [hR0]; rfl
    | succ c ih =>
      intro hc
      rw [hR c (by omega), ih (by omega)]
      dsimp [rc]
      rw [rippleCarry_succ]
      generalize s0 c = a; generalize c0 c = b; generalize rippleCarry s0 c0 false c = r
      cases a <;> cases b <;> cases r <;> rfl
  -- 2. Each 5-bit block computes the span `(G, P)` of its 5 bits.
  have hf_span : ∀ j, j < FQ → ∀ t, t ≤ 5 →
      (fgg j t, fpp j t) = pgSpan (addPos s0 c0 false) (M + 5 * j + 1) t := by
    intro j hj t
    induction t with
    | zero => intro _; rw [hfgg0 j hj, hfpp0 j hj]; rfl
    | succ t ih =>
      intro ht
      rw [hfgg j hj t (by omega), hfpp j hj t (by omega),
        hfg (5 * j + t) (by omega), hfp (5 * j + t) (by omega),
        pgSpan_succ, ← ih (by omega)]
      rw [show M + 5 * j + 1 + t = (M + (5 * j + t)) + 1 by omega, addPos_succ]
      rfl
  -- 3. Block-level positions for Kogge-Stone prefix.
  let blkPos : Nat → Bool × Bool
    | 0 => (rc M, false)
    | j + 1 => pgBlock (addPos s0 c0 false) (M + 5 * j + 1) (M + 5 * (j + 1))
  have hblk_block : ∀ j, pgBlock blkPos 0 j = (rc (M + 5 * j), false) := by
    intro j
    induction j with
    | zero =>
      rw [pgBlock_self]
      simp [blkPos]
    | succ j ih =>
      rw [pgBlock_succ _ (Nat.zero_le _), ih]
      have h0 : (rc (M + 5 * j), false) = pgBlock (addPos s0 c0 false) 0 (M + 5 * j) :=
        (pgBlock_addPos_zero s0 c0 false (M + 5 * j)).symm
      rw [h0]
      dsimp [blkPos]
      rw [pgBlock_combine (addPos s0 c0 false) (j := 0) (m := M + 5 * j) (k := M + 5 * (j + 1))
        (by omega) (by omega)]
      exact pgBlock_addPos_zero s0 c0 false (M + 5 * (j + 1))
  -- 4. Kogge-Stone levels satisfy `ksRec blkPos`.
  have hlev : ∀ fl, fl ≤ FL → ∀ j, j < FQ + 1 → (bg fl j, bp fl j) = ksRec blkPos fl j := by
    intro fl
    induction fl with
    | zero =>
      intro _ j hj
      cases j with
      | zero =>
        rw [hbg00, hbp00, hR_eq M (Nat.le_refl M)]
        rfl
      | succ j =>
        rw [hbg_blk j (by omega), hbp_blk j (by omega), hf_span j (by omega) 5 (Nat.le_refl 5)]
        simp only [ksRec, blkPos, pgBlock, show M + 5 * (j + 1) + 1 - (M + 5 * j + 1) = 5 by omega]
    | succ fl ih =>
      intro hfl j hj
      rw [ksRec]
      split
      · next hg =>
        rw [hbg_op fl (by omega) j hj hg, hbp_op fl (by omega) j hj hg,
          ← ih (by omega) j hj, ← ih (by omega) (j - 2 ^ fl) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hj)]
        rfl
      · next hg =>
        rw [hbg_pass fl (by omega) j hj hg, hbp_pass fl (by omega) j hj hg, ← ih (by omega) j hj]
  have hbg_FL : ∀ j, j < FQ + 1 → bg FL j = rc (M + 5 * j) := by
    intro j hj
    have h := hlev FL (Nat.le_refl FL) j hj
    rw [ksRec_block, show j + 1 - 2 ^ FL = 0 by omega, hblk_block] at h
    exact (Prod.mk.inj h).1
  -- 5. Local carries inside each 5-bit block match `rc`.
  have hfcc_eq : ∀ j, j < FQ → ∀ t, t ≤ 5 → fcc j t = rc (M + 5 * j + t) := by
    intro j hj t
    induction t with
    | zero => intro _; rw [hfcc0 j hj, hbg_FL j (by omega), Nat.add_zero]
    | succ t ih =>
      intro ht
      rw [hfcc j hj t (by omega), hfp (5 * j + t) (by omega), ih (by omega)]
      rw [show M + 5 * j + (t + 1) = (M + 5 * j + t) + 1 by omega,
        show M + (5 * j + t) = M + 5 * j + t by omega]
      dsimp [rc]
      rw [rippleCarry_succ]
      generalize s0 (M + 5 * j + t) = a
      generalize c0 (M + 5 * j + t) = b
      generalize rippleCarry s0 c0 false (M + 5 * j + t) = r
      cases a <;> cases b <;> cases r <;> rfl
  -- 6. Tail carries match `rc`.
  have hRt_eq : ∀ t, t ≤ FR → Rt t = rc (M + 5 * FQ + t) := by
    intro t
    induction t with
    | zero => intro _; rw [hRt0, hbg_FL FQ (by omega), Nat.add_zero]
    | succ t ih =>
      intro ht
      rw [hRt t (by omega), hfp (5 * FQ + t) (by omega), ih (by omega)]
      rw [show M + 5 * FQ + (t + 1) = (M + 5 * FQ + t) + 1 by omega,
        show M + (5 * FQ + t) = M + 5 * FQ + t by omega]
      dsimp [rc]
      rw [rippleCarry_succ]
      generalize s0 (M + 5 * FQ + t) = a
      generalize c0 (M + 5 * FQ + t) = b
      generalize rippleCarry s0 c0 false (M + 5 * FQ + t) = r
      cases a <;> cases b <;> cases r <;> rfl
  -- 7. Combine low, middle blocks, and tail.
  intro c hc
  by_cases h1 : c < M
  · rw [hp_lo c h1, hR_eq c (by omega)]
    dsimp [rc]
    generalize s0 c = a; generalize c0 c = b; generalize rippleCarry s0 c0 false c = r
    cases a <;> cases b <;> cases r <;> rfl
  · by_cases h2 : c < M + 5 * FQ
    · let j := (c - M) / 5
      let t := (c - M) % 5
      have hj : j < FQ := by omega
      have ht : t < 5 := by omega
      have heq : M + 5 * j + t = c := by omega
      have h := hp_blk j hj t ht
      rw [heq, hfcc_eq j hj t (by omega), heq] at h
      rw [h]
      dsimp [rc]
      generalize s0 c = a; generalize c0 c = b; generalize rippleCarry s0 c0 false c = r
      cases a <;> cases b <;> cases r <;> rfl
    · let t := c - (M + 5 * FQ)
      have ht : t < FR := by omega
      have heq : M + 5 * FQ + t = c := by omega
      have h := hp_tail t ht
      rw [heq, hRt_eq t (by omega), heq] at h
      rw [h]
      dsimp [rc]
      generalize s0 c = a; generalize c0 c = b; generalize rippleCarry s0 c0 false c = r
      cases a <;> cases b <;> cases r <;> rfl

/-- **The whole multiplier**, assuming the final adder produces canonical ripple-carry sum bits
of `(S 0, C 0)`. -/
theorem heap_mul0 {N H : Nat} (hN : 1 ≤ N) (hH1 : N ≤ 2 * H) (hH2 : 2 * H ≤ N + 1)
    (a b : BitVec N) (p : BitVec (2 * N))
    (ae bb : Nat → Bool) (S C X Y : Nat → Nat → Bool)
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
    (hp : ∀ c, c < 2 * N → p.getLsbD c = (S 0 c ^^ C 0 c ^^ rippleCarry (S 0) (C 0) false c)) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  obtain ⟨n, hn⟩ : ∃ n, 2 * N = n + 1 := ⟨2 * N - 1, by omega⟩
  let V : Nat → Nat := fun m => bfVal (S m) (2 * N) + bfVal (C m) (2 * N)
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
  have hrip := ripple_row (2 * N) (S 0) (C 0) (fun c => S 0 c ^^ C 0 c) p.getLsbD
    (rippleCarry (S 0) (C 0) false) (fun _ _ => rfl) (fun c hc => hp c hc) (fun _ _ => rfl)
  rw [rippleCarry_zero, bfVal_bv] at hrip
  simp only [Bool.toNat_false, Nat.add_zero] at hrip
  have hlt : p.toNat < 2 ^ (2 * N) := p.isLt
  have hpv : p.toNat = V 0 % 2 ^ (2 * N) := by
    have := sum_split hlt (t := V 0) (q := (rippleCarry (S 0) (C 0) false (2 * N)).toNat)
      (by simp only [V]; omega)
    exact this.1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, hpv, hroot]

/-- `heap_mul_hybrid` with the exact gate forms of `solutions_asap7/mul/solution.sv`. -/
theorem heap_mul_hybrid {N H : Nat} (hN : 1 ≤ N) (hH1 : N ≤ 2 * H) (hH2 : 2 * H ≤ N + 1)
    (a b : BitVec N) (p : BitVec (2 * N))
    (ae bb : Nat → Bool) (S C X Y : Nat → Nat → Bool)
    (hae1 : ∀ k, k < 2 * N - 1 → ae k = false)
    (hae2 : ∀ k, k < N → ae (2 * N - 1 + k) = a.getLsbD k)
    (hae3 : ∀ k, k < N → ae (3 * N - 1 + k) = false)
    (hbb1 : ∀ k, k < N → bb k = b.getLsbD k)
    (hbb2 : ∀ k, N ≤ k → k < 2 * H → bb k = false)
    (hleafS : ∀ j, j < H → ∀ c, c < 2 * N →
      S (H - 1 + j) c = (bb (2 * j) && ae (c + (2 * N - 1 - 2 * j))))
    (hleafC : ∀ j, j < H → ∀ c, c < 2 * N →
      C (H - 1 + j) c = (ae (c + (2 * N - 1 - (2 * j + 1))) && bb (2 * j + 1)))
    (hY0 : ∀ k, k < H - 1 → Y k 0 = false)
    (hC0 : ∀ k, k < H - 1 → C k 0 = false)
    (hX : ∀ k, k < H - 1 → ∀ c, c < 2 * N →
      X k c = ((S (2 * k + 2) c ^^ C (2 * k + 1) c) ^^ S (2 * k + 1) c))
    (hS : ∀ k, k < H - 1 → ∀ c, c < 2 * N → S k c = ((X k c ^^ C (2 * k + 2) c) ^^ Y k c))
    (hY : ∀ k, k < H - 1 → ∀ c, c < 2 * N - 1 →
      Y k (c + 1) = (if (S (2 * k + 2) c ^^ C (2 * k + 1) c) = true then S (2 * k + 1) c else C (2 * k + 1) c))
    (hC : ∀ k, k < H - 1 → ∀ c, c < 2 * N - 1 →
      C k (c + 1) = (if (Y k c ^^ C (2 * k + 2) c) = true then X k c else C (2 * k + 2) c))
    (hp : ∀ c, c < 2 * N → p.getLsbD c = (S 0 c ^^ C 0 c ^^ rippleCarry (S 0) (C 0) false c)) :
    p = BitVec.ofNat (2 * N) (a.toNat * b.toNat) := by
  refine heap_mul0 hN hH1 hH2 a b p ae bb S C X Y hae1 hae2 hae3 hbb1 hbb2 ?_ hleafC hY0 hC0
    ?_ ?_ ?_ ?_ hp
  · intro j hj c hc
    rw [hleafS j hj c hc]; exact Bool.and_comm _ _
  · intro k hk c hc
    rw [hX k hk c hc]
    generalize S (2 * k + 1) c = s1; generalize C (2 * k + 1) c = c1; generalize S (2 * k + 2) c = s2
    cases s1 <;> cases c1 <;> cases s2 <;> decide
  · intro k hk c hc
    rw [hS k hk c hc]
    generalize X k c = x; generalize Y k c = y; generalize C (2 * k + 2) c = c2
    cases x <;> cases y <;> cases c2 <;> decide
  · intro k hk c hc
    rw [hY k hk c hc]
    generalize S (2 * k + 1) c = s1; generalize C (2 * k + 1) c = c1; generalize S (2 * k + 2) c = s2
    cases s1 <;> cases c1 <;> cases s2 <;> decide
  · intro k hk c hc
    rw [hC k hk c hc]
    generalize X k c = x; generalize Y k c = y; generalize C (2 * k + 2) c = c2
    cases x <;> cases y <;> cases c2 <;> decide

end HeapArith

/-! ## 2. Structure, interface, and end-to-end proof -/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
  LeanModels.Sv.Lib SvGolf

/-- Lexicographic rank certificate `(stage, order, phase)` for `solutions_asap7/mul/solution.sv`. -/
def mulKey (N : Nat) : SiteId → Key
  | .plain 8 => (5, 0, 0)
  | .plain 13 => (7, 0, 0)
  | .plain _ => (0, 0, 0)
  | .fam "g_lc" _ _ => (1, 0, 0)
  | .fam "g_node" _ [k] => (2, (N + 1) / 2 - 1 - k.toNat, 0)
  | .fam "g_col" 0 [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 1)
  | .fam "g_col" _ [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 2)
  | .fam "g_car" 0 [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 1)
  | .fam "g_car" _ [k, _] => (2, (N + 1) / 2 - 1 - k.toNat, 2)
  | .fam "g_fin_lo" 0 [c] => (3, c.toNat, 1)
  | .fam "g_fin_lo" _ [c] => (3, c.toNat, 0)
  | .fam "g_fpg" _ _ => (3, 0, 0)
  | .fam "g_fblk" 0 _ => (4, 0, 0)
  | .fam "g_fblk" 1 _ => (4, 0, 0)
  | .fam "g_fblk" _ _ => (5, 0, 0)
  | .fam "g_frip" _ [_, t] => (4, t.toNat + 1, 0)
  | .fam "g_fnd" _ [fl, _] => (6, fl.toNat, 0)
  | .fam "g_floc" _ _ => (7, 0, 0)
  | .fam "g_flc" 0 [_, t] => (8, t.toNat, 0)
  | .fam "g_flc" _ [_, t] => (8, t.toNat, 1)
  | .fam "g_ftail" 0 [t] => (8, t.toNat, 0)
  | .fam "g_ftail" _ [t] => (8, t.toNat, 1)
  | .fam _ _ _ => (9, 0, 0)

set_option maxHeartbeats 2000000 in
theorem mul_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  have hM : (0 : Int) ≤ 3 * (N : Int) / 4 := by omega
  have hFQ : (0 : Int) ≤ (2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5 := by omega
  sv_structure (lexRank := mulKey N)
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

theorem mul_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface

set_option maxHeartbeats 2000000 in
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  have hR : N < 2 ^ 20 := hN.2
  have hM0 : (0 : Int) ≤ 3 * (N : Int) / 4 := by omega
  have hFQ0 : (0 : Int) ≤ (2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5 := by omega
  obtain ⟨hc, ha, hso⟩ := mul_struct N hN' hR
  refine CombTask.satisfiedAt_of_comb (mul_interface N hN' hR hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · let M : Nat := (3 * N) / 4
    let U : Nat := 2 * N - M
    let FQ : Nat := (U - 1) / 5
    let FR : Nat := U - 5 * FQ
    let FL : Nat := clog2 (FQ + 1)
    let bgW : Int := (2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5 + 1
    have hMc : (M : Int) = 3 * (N : Int) / 4 := by dsimp [M]
    have hUc : (U : Int) = 2 * (N : Int) - 3 * (N : Int) / 4 := by dsimp [U]; omega
    have hFQc : (FQ : Int) = (2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5 := by
      have : ((U - 1 : Nat) : Int) = 2 * (N : Int) - 3 * (N : Int) / 4 - 1 := by omega
      rw [← this]; dsimp [FQ]
    have hFRc : (FR : Int) = 2 * (N : Int) - 3 * (N : Int) / 4 - 5 * ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5) := by
      omega
    have hFLc : clog2 ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5 + 1).toNat = FL := by
      rw [← hFQc]; dsimp [FL]
    -- Every output bit of `p` is known, and `p` has width `2 * N`.
    have hknown_p : ∀ k, k < 2 * N →
        (∃ vp, st.lookup "p" = some vp ∧ vp.width = (2 * (N : Int) + -1).natAbs + 1) ∧
          KnownBit st "p" k := by
      intro k hk
      by_cases h1 : k < M
      · exact known_p_g_fin_lo_0 k (by omega)
      · by_cases h2 : k < M + 5 * FQ
        · have h := known_p_g_flc_1 ((k - M) / 5) (by omega) ((k - M) % 5) (by omega)
          rwa [show (3 * (N : Int) / 4 + (5 * (((k - M) / 5 : Nat) : Int) + (((k - M) % 5 : Nat) : Int))).toNat = k by omega] at h
        · have h := known_p_g_ftail_1 (k - (M + 5 * FQ)) (by omega)
          rwa [show (3 * (N : Int) / 4 + (5 * ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5) + ((k - (M + 5 * FQ) : Nat) : Int))).toNat = k by omega] at h
    obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := hknown_p 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N) hvp (by omega)
      (fun k hk => (hknown_p k hk).2)]
    congr 2
    -- Prove the hybrid final adder computes canonical ripple-carry sum bits on `(S[0], C[0])`.
    have hS0 : st.cell "S" (2 * N) 0 = st.boolAt "S" := funext fun c => by simp [SvState.cell, rmN]
    have hC0 : st.cell "C" (2 * N) 0 = st.boolAt "C" := funext fun c => by simp [SvState.cell, rmN]
    have hadd : ∀ c, c < 2 * N →
        st.boolAt "p" c =
          (st.boolAt "S" c ^^ st.boolAt "C" c ^^
            rippleCarry (st.boolAt "S") (st.boolAt "C") false c) := by
      refine HeapArith.hybrid_adder_bits (W := 2 * N) (M := M) (U := U) (FQ := FQ) (FR := FR)
        (FL := FL) (by omega) (by omega) (le_two_pow_clog2 (FQ + 1))
        (st.boolAt "S") (st.boolAt "C") (st.boolAt "p") (st.boolAt "R")
        (st.boolAt "fp") (st.boolAt "fg") (st.boolAt "Rt")
        (st.cell "fgg" 6) (st.cell "fpp" 6) (st.cell "fcc" 6)
        (st.cell "bg" bgW) (st.cell "bp" bgW)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · exact eq_R_plain_7
      · intro c hc; exact eq_R_g_fin_lo_1 c (by omega)
      · intro c hc; exact eq_p_g_fin_lo_0 c (by omega)
      · intro c hc
        have h := eq_fp_g_fpg_0 c (by omega)
        rwa [show (3 * (N : Int) / 4 + (c : Int)).toNat = M + c by omega] at h
      · intro c hc
        have h := eq_fg_g_fpg_1 c (by omega)
        rwa [show (3 * (N : Int) / 4 + (c : Int)).toNat = M + c by omega] at h
      · intro j hj; exact eq_fgg_g_fblk_0 j (by omega)
      · intro j hj; exact eq_fpp_g_fblk_1 j (by omega)
      · intro j hj t ht
        have h := eq_fgg_g_frip_0 j (by omega) t (by omega)
        simpa [SvState.cell, show (5 * (j : Int) + (t : Int)).toNat = 5 * j + t by omega,
          show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega] using h
      · intro j hj t ht
        have h := eq_fpp_g_frip_1 j (by omega) t (by omega)
        simpa [SvState.cell, show (5 * (j : Int) + (t : Int)).toNat = 5 * j + t by omega,
          show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega] using h
      · simpa [SvState.cell, rmN, show (3 * (N : Int) / 4).toNat = M by omega] using eq_bg_plain_8
      · simpa [SvState.cell, rmN] using eq_bp_plain_9
      · intro j hj
        simpa [SvState.cell, rmN] using eq_bg_g_fblk_3 j (by omega)
      · intro j hj
        simpa [SvState.cell, rmN] using eq_bp_g_fblk_4 j (by omega)
      · intro fl hfl j hj hg
        have hp2 : ((2 ^ fl : Nat) : Int) = (2 : Int) ^ fl := by push_cast; rfl
        have h := eq_bg_g_fnd_0 fl (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((fl + 1 : Nat) : Int) = (fl : Int) + 1 by omega,
          show ((j - 2 ^ fl : Nat) : Int) = (j : Int) + -1 * (2 : Int) ^ fl by omega] using h
      · intro fl hfl j hj hg
        have hp2 : ((2 ^ fl : Nat) : Int) = (2 : Int) ^ fl := by push_cast; rfl
        have h := eq_bp_g_fnd_1 fl (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((fl + 1 : Nat) : Int) = (fl : Int) + 1 by omega,
          show ((j - 2 ^ fl : Nat) : Int) = (j : Int) + -1 * (2 : Int) ^ fl by omega] using h
      · intro fl hfl j hj hg
        have hp2 : ((2 ^ fl : Nat) : Int) = (2 : Int) ^ fl := by push_cast; rfl
        have h := eq_bg_g_fnd_2 fl (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((fl + 1 : Nat) : Int) = (fl : Int) + 1 by omega] using h
      · intro fl hfl j hj hg
        have hp2 : ((2 ^ fl : Nat) : Int) = (2 : Int) ^ fl := by push_cast; rfl
        have h := eq_bp_g_fnd_3 fl (by omega) j (by omega) (by omega)
        simpa [SvState.cell, bgW, show ((fl + 1 : Nat) : Int) = (fl : Int) + 1 by omega] using h
      · intro j hj
        have h := eq_fcc_g_floc_0 j (by omega)
        simpa [SvState.cell, bgW, hFLc] using h
      · intro j hj t ht
        have h := eq_fcc_g_flc_0 j (by omega) t (by omega)
        simpa [SvState.cell, show ((t + 1 : Nat) : Int) = (t : Int) + 1 by omega,
          show (5 * (j : Int) + (t : Int)).toNat = 5 * j + t by omega,
          show (3 * (N : Int) / 4 + (5 * (j : Int) + (t : Int))).toNat = M + 5 * j + t by omega] using h
      · intro j hj t ht
        have h := eq_p_g_flc_1 j (by omega) t (by omega)
        simpa [SvState.cell,
          show (3 * (N : Int) / 4 + (5 * (j : Int) + (t : Int))).toNat = M + 5 * j + t by omega] using h
      · simpa [SvState.cell, bgW, hFLc, ← hFQc] using eq_Rt_plain_13
      · intro t ht
        have h := eq_Rt_g_ftail_0 t (by omega)
        simpa [show (5 * ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5) + (t : Int)).toNat = 5 * FQ + t by omega,
          show (3 * (N : Int) / 4 + (5 * ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5) + (t : Int))).toNat = M + 5 * FQ + t by omega] using h
      · intro t ht
        have h := eq_p_g_ftail_1 t (by omega)
        simpa [show (3 * (N : Int) / 4 + (5 * ((2 * (N : Int) - 3 * (N : Int) / 4 - 1) / 5) + (t : Int))).toNat = M + 5 * FQ + t by omega] using h
    -- Plug into the 4:2 compressor heap theorem.
    refine HeapArith.heap_mul_hybrid (H := (N + 1) / 2) hN' (by omega) (by omega) x y
      (XF.bv (2 * N) (st.boolAt "p")) (st.boolAt "ae") (st.boolAt "bb") (st.cell "S" (2 * N))
      (st.cell "C" (2 * N)) (st.cell "X" (2 * N)) (st.cell "Y" (2 * N))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
    · intro c hc
      rw [XF.getLsbD_bv hc, hS0, hC0]
      exact hadd c hc
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | (intros; rfl) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
