import LeanModels.Sv.Lib.Prefix
import LeanModels.Sv.CombView
import LeanModels.Sv.CombLib

/-!
# The Sklansky adder's mathematics: section `SklCore` of the future reference proof

The design is `tests/add/baselines/add_n_sklansky.sv`, in its natural form (a conditional generate inside the level
loop, the partner index `((i >> l) << l) - 1`). Positions `0 … N`: position `0` carries the carry in
(`g[0][0] = cin`, `p[0][0] = 0`), position `k + 1` is bit `k` (`g[0][k+1] = a[k] & b[k]`,
`p[0][k+1] = a[k] ^ b[k]`); level `l + 1` at position `i` is, when bit `l` of `i` is set (`((i >> l) & 1) == 1`),
the combination of `(l, i)` with its partner `(l, ((i >> l) << l) - 1)`, and `(l, i)` otherwise; after
`L = $clog2(N + 1)` levels `g[L][i]` is the carry into bit `i`, `s[i] = x[i] ^ g[L][i]` with `x[i] = a[i] ^ b[i]`,
and `cout = g[L][N]`.

This file is the part of the proof that does not depend on how ls-sv prints the netlist: it is waiting for ls-sv's
guarded generate families (equations `∀ l i, guard → g (l+1) i = …`) and nonlinear genvar indices (handed to the proof
as obligations). When they land, this section moves into the reference's own file
(`tasks/add/reference/add_n_sklansky.lean`, beside a copy of the design) and the glue is one application of
`skl_addView` to the equations `sv_equations` prints, followed by `CombLib.add_spec`, as in `reference/add_n.lean`.
It lives here until then because `tasks/add/reference/` holds proved pairs `<stem>.sv` + `<stem>.lean` only
(`tests/run.py`, step `layout`).

## Contents

1. Aligned blocks: `(i >>> l) <<< l` is `i` with its low `l` bits cleared (`shl_shr`), and one level's arithmetic
   (`aligned_odd`, `aligned_even`): when bit `l` of `i` is set, the aligned block of size `2^(l+1)` holding `i` is the
   one of size `2^l` holding the partner below the one of size `2^l` holding `i`; otherwise the two blocks of `i`
   coincide.
2. The recurrence `sklRec pos l i`, exactly as the source denotes it (over any position function `pos`; the adder's
   is `Lib.addPos a b cin`), and THE BLOCK INVARIANT `sklRec_block`: after level `l`, position `i` holds the pair of the
   aligned block `[(i >>> l) <<< l, i]` (`Lib.pgBlock`), which is `[0, i]` once `i < 2^l` (`sklRec_top`).
3. The end result over the adder's positions (`skl_carry`, `skl_carry_clog2`): at level `L = clog2 (N + 1)` every
   position `i ≤ N` holds `(carry into bit i, false)` (`Lib.rippleCarry`).
4. The equations' side (`sklRec_of_eqs`, `skl_block_of_eqs`, `skl_adder`, `skl_addView`): any two level-by-position
   bit functions `g p` that satisfy the netlist's equations (stated per `(l, i)`, the guard a hypothesis) ARE the
   recurrence at every level `l ≤ L` and position `i ≤ N`; hence the carries, the sum and the carry out, and the
   library's `CombLib.AddView`, from which `CombLib.add_spec` gives the task's `s` and `cout`. The guard and the
   partner index are parameters (`G`, `q`) with one bridge hypothesis each, so the glue can pass them in whatever
   spelling ls-sv prints; `skl_addView_nat` is the instance at the source's own spelling.

For every `N` (the task's `1 ≤ N` is not needed). No `sorry`, `native_decide` or `bv_decide`; the axioms are pinned
at the end (`[propext, Quot.sound]`, and `Classical.choice` through `CombLib.add_spec` and `guard_iff_testBit`).

Measured (2026-11-05, LEAN_NUM_THREADS=2, nice 19): the file elaborates in 5.3 s wall; per declaration (a dev copy
wrapping each one in an `IO.getNumHeartbeats` counter, `Elab.async false`), in thousands of heartbeats (the unit of
`maxHeartbeats`, default 200000): `aligned_odd` 1682, `block_op` 1001, `sklRec_of_eqs` 917, `skl_addView` 774,
`aligned_even` 502, `skl_adder` 485, every other theorem under 400; the two `decide` checks 3210 (`N = 3`, exhaustive)
and 1255 (`N = 16` corners); the whole section about 12660. No option is set.
-/

section SklCore

namespace SvGolf.AddSklansky

open LeanModels.Sv LeanModels.Sv.Lib LeanModels.Sv.CombLib

/-! ## 1. Aligned blocks -/

/-- The start of the aligned block of size `2^l` that holds position `i`, as the source writes it: `i` with its low
`l` bits cleared. -/
theorem shl_shr (l i : Nat) : (i >>> l) <<< l = i / 2 ^ l * 2 ^ l := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-- The source's guard `((i >> l) & 1) == 1`, bit `l` of `i`, in its three spellings. -/
theorem guard_iff_and (l i : Nat) : (i >>> l) % 2 = 1 ↔ (i >>> l) &&& 1 = 1 := by
  rw [Nat.and_one_is_mod]

theorem guard_iff_testBit (l i : Nat) : (i >>> l) % 2 = 1 ↔ i.testBit l = true := by
  rw [Nat.testBit, Nat.and_comm, Nat.and_one_is_mod, bne_iff_ne]
  omega

theorem guard_iff_div (l i : Nat) : (i >>> l) % 2 = 1 ↔ i / 2 ^ l % 2 = 1 := by
  rw [Nat.shiftRight_eq_div_pow]

/-- One level of aligned blocks at a position whose bit `l` is set, with `P = 2^l`: the block of size `2P` holding
`i` starts `P` below the block of size `P` holding `i`, and it is the block of size `P` holding the partner (the
position just below `i`'s block). -/
theorem aligned_odd {i P : Nat} (hP : 0 < P) (hq : i / P % 2 = 1) :
    i / (P * 2) * (P * 2) + P = i / P * P ∧ (i / P * P - 1) / P * P = i / (P * 2) * (P * 2) := by
  rw [← Nat.div_div_eq_div_mul]
  generalize i / P = q at *
  obtain ⟨Q, rfl⟩ : ∃ Q, q = 2 * Q + 1 := ⟨q / 2, by omega⟩
  have h2 : (2 * Q + 1) / 2 = Q := by omega
  have e1 : (2 * Q + 1) * P = 2 * (Q * P) + P := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : Q * (P * 2) = 2 * (Q * P) := by rw [← Nat.mul_assoc, Nat.mul_comm (Q * P) 2]
  have e3 : (2 * (Q * P) + P - 1) / P = 2 * Q := by
    rw [show 2 * (Q * P) + P - 1 = (P - 1) + 2 * Q * P by rw [Nat.mul_assoc]; omega,
      Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  rw [h2, e1, e2, e3]
  exact ⟨rfl, Nat.mul_assoc 2 Q P⟩

/-- One level of aligned blocks at a position whose bit `l` is clear, with `P = 2^l`: the blocks of size `P` and
`2P` holding `i` start at the same position. -/
theorem aligned_even {i P : Nat} (hq : ¬ i / P % 2 = 1) : i / (P * 2) * (P * 2) = i / P * P := by
  rw [← Nat.div_div_eq_div_mul]
  generalize i / P = q at *
  obtain ⟨Q, rfl⟩ : ∃ Q, q = 2 * Q := ⟨q / 2, by omega⟩
  rw [show 2 * Q / 2 = Q by omega, Nat.mul_comm P 2, ← Nat.mul_assoc, Nat.mul_comm Q 2]

/-- An aligned block starts at or below its position. -/
theorem shl_shr_le (l i : Nat) : (i >>> l) <<< l ≤ i := by
  rw [shl_shr]
  exact Nat.div_mul_le_self i (2 ^ l)

/-- Under the guard, the block of `i` does not start at `0`: the partner `((i >>> l) <<< l) - 1` is a real position
(so the `Nat` subtraction is the source's), and it lies below `i`. -/
theorem shl_shr_pos {l i : Nat} (hg : (i >>> l) % 2 = 1) : 1 ≤ (i >>> l) <<< l := by
  rw [guard_iff_div] at hg
  obtain ⟨h1, -⟩ := aligned_odd (Nat.two_pow_pos l) hg
  rw [shl_shr, ← h1]
  have := Nat.two_pow_pos l
  omega

theorem partner_lt {l i : Nat} (hg : (i >>> l) % 2 = 1) : ((i >>> l) <<< l) - 1 < i := by
  have h1 := shl_shr_pos hg
  have h2 := shl_shr_le l i
  omega

/-- Below `2^l`, the aligned block starts at `0`. -/
theorem shl_shr_of_lt {l i : Nat} (hi : i < 2 ^ l) : (i >>> l) <<< l = 0 := by
  rw [shl_shr, Nat.div_eq_of_lt hi, Nat.zero_mul]

/-! ## 2. The recurrence and its block invariant -/

/-- **The Sklansky recurrence**, as the source denotes it: level `0` is the positions `pos`; level `l + 1` at
position `i` combines `(l, i)` with its partner `(l, ((i >>> l) <<< l) - 1)` when bit `l` of `i` is set, and is
`(l, i)` otherwise. For the adder, `pos = addPos a b cin` (position `0` is `(cin, false)`, position `k + 1` is
`(a k && b k, a k ^^ b k)`). -/
def sklRec (pos : Nat → Bool × Bool) : Nat → Nat → Bool × Bool
  | 0, i => pos i
  | l + 1, i =>
    if (i >>> l) % 2 = 1 then pgOp (sklRec pos l i) (sklRec pos l (((i >>> l) <<< l) - 1))
    else sklRec pos l i

theorem sklRec_zero (pos : Nat → Bool × Bool) (i : Nat) : sklRec pos 0 i = pos i := rfl

theorem sklRec_succ (pos : Nat → Bool × Bool) (l i : Nat) :
    sklRec pos (l + 1) i =
      if (i >>> l) % 2 = 1 then pgOp (sklRec pos l i) (sklRec pos l (((i >>> l) <<< l) - 1))
      else sklRec pos l i := rfl

/-- One level on blocks, the combining arm: the aligned block of size `2^l` holding `i`, above the one holding the
partner, is the aligned block of size `2^(l+1)` holding `i`. -/
theorem block_op (f : Nat → Bool × Bool) {l i : Nat} (hg : (i >>> l) % 2 = 1) :
    pgOp (pgBlock f ((i >>> l) <<< l) i)
        (pgBlock f (((((i >>> l) <<< l) - 1) >>> l) <<< l) (((i >>> l) <<< l) - 1)) =
      pgBlock f ((i >>> (l + 1)) <<< (l + 1)) i := by
  have hpos := shl_shr_pos hg
  have hle := shl_shr_le l i
  rw [guard_iff_div] at hg
  obtain ⟨h1, h2⟩ := aligned_odd (Nat.two_pow_pos l) hg
  rw [shl_shr l (((i >>> l) <<< l) - 1), shl_shr (l + 1), Nat.pow_succ]
  rw [shl_shr] at hpos hle ⊢
  rw [h2]
  have hP := Nat.two_pow_pos l
  generalize i / 2 ^ l * 2 ^ l = b at *
  generalize i / (2 ^ l * 2) * (2 ^ l * 2) = c at *
  have := pgBlock_combine f (j := c) (m := b - 1) (k := i) (by omega) (by omega)
  rw [show b - 1 + 1 = b by omega] at this
  exact this

/-- One level on blocks, the passing arm: when bit `l` of `i` is clear, the aligned blocks of size `2^l` and
`2^(l+1)` holding `i` are the same. -/
theorem block_pass (f : Nat → Bool × Bool) {l i : Nat} (hg : ¬ (i >>> l) % 2 = 1) :
    pgBlock f ((i >>> l) <<< l) i = pgBlock f ((i >>> (l + 1)) <<< (l + 1)) i := by
  rw [guard_iff_div] at hg
  rw [shl_shr, shl_shr, Nat.pow_succ, aligned_even hg]

/-- **The block invariant.** After level `l`, position `i` holds the (generate, propagate) pair of the aligned block
from `(i >>> l) <<< l` to `i`. -/
theorem sklRec_block (pos : Nat → Bool × Bool) :
    ∀ l i, sklRec pos l i = pgBlock pos ((i >>> l) <<< l) i
  | 0, i => by
    rw [sklRec_zero, Nat.shiftRight_zero, Nat.shiftLeft_zero, pgBlock_self]
  | l + 1, i => by
    rw [sklRec_succ]
    by_cases hg : (i >>> l) % 2 = 1
    · rw [if_pos hg, sklRec_block pos l i, sklRec_block pos l, block_op pos hg]
    · rw [if_neg hg, sklRec_block pos l i, block_pass pos hg]

/-- Once `i < 2^l`, the block reaches position `0`: position `i` holds the pair of `[0, i]`. -/
theorem sklRec_top (pos : Nat → Bool × Bool) {l i : Nat} (hi : i < 2 ^ l) :
    sklRec pos l i = pgBlock pos 0 i := by
  rw [sklRec_block, shl_shr_of_lt hi]

/-! ## 3. The end result over the adder's positions -/

/-- At any level `L` with `i < 2^L`, position `i` holds the carry into bit `i` (and propagates nothing). -/
theorem skl_carry (a b : Nat → Bool) (cin : Bool) {L i : Nat} (hi : i < 2 ^ L) :
    sklRec (addPos a b cin) L i = (rippleCarry a b cin i, false) := by
  rw [sklRec_top _ hi, pgBlock_addPos_zero]

/-- **At level `L = clog2 (N + 1)`, every position `i ≤ N` holds the carry into bit `i`.** -/
theorem skl_carry_clog2 (a b : Nat → Bool) (cin : Bool) {N i : Nat} (hi : i ≤ N) :
    sklRec (addPos a b cin) (clog2 (N + 1)) i = (rippleCarry a b cin i, false) :=
  skl_carry a b cin (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hi) (CombView.le_two_pow_clog2 (N + 1)))

/-! ## 4. The equations' side

The netlist's equations as `sv_equations` is expected to print them once ls-sv takes guarded generate families: one
hypothesis per generate site, quantified over the level `l < L` and the position `i < N + 1`, the guard of the
conditional generate a hypothesis (the `g_op` arm) or its negation (the `g_pass` arm). `G l i` is the guard as
printed and `q l i` the partner index as printed; `hG` and `hq` say they are the source's `(i >>> l) % 2 = 1` and
`((i >>> l) <<< l) - 1`. -/

/-- **The netlist is the recurrence.** Bit functions `g p` (level, position) that satisfy the equations agree with
`sklRec (addPos a b cin)` at every level `l ≤ L` and position `i ≤ N`. -/
theorem sklRec_of_eqs {N L : Nat} {a b : Nat → Bool} {cin : Bool} {g p : Nat → Nat → Bool}
    {G : Nat → Nat → Prop} {q : Nat → Nat → Nat}
    (hG : ∀ l, l < L → ∀ i, i < N + 1 → (G l i ↔ (i >>> l) % 2 = 1))
    (hq : ∀ l, l < L → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 → q l i = ((i >>> l) <<< l) - 1)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < L → ∀ i, i < N + 1 → G l i → g (l + 1) i = (g l i || (p l i && g l (q l i))))
    (hpop : ∀ l, l < L → ∀ i, i < N + 1 → G l i → p (l + 1) i = (p l i && p l (q l i)))
    (hgpass : ∀ l, l < L → ∀ i, i < N + 1 → ¬ G l i → g (l + 1) i = g l i)
    (hppass : ∀ l, l < L → ∀ i, i < N + 1 → ¬ G l i → p (l + 1) i = p l i) :
    ∀ l, l ≤ L → ∀ i, i ≤ N → (g l i, p l i) = sklRec (addPos a b cin) l i := by
  intro l
  induction l with
  | zero =>
    intro _ i hi
    cases i with
    | zero => rw [sklRec_zero, hg0, hp0, addPos_zero]
    | succ k => rw [sklRec_zero, hgin k (by omega), hpin k (by omega), addPos_succ]
  | succ l ih =>
    intro hl i hi
    have hlL : l < L := by omega
    have hiN : i < N + 1 := by omega
    rw [sklRec_succ]
    by_cases hb : (i >>> l) % 2 = 1
    · have hGi : G l i := (hG l hlL i hiN).mpr hb
      have hpart : ((i >>> l) <<< l) - 1 ≤ N := by have := partner_lt hb; omega
      rw [if_pos hb, hgop l hlL i hiN hGi, hpop l hlL i hiN hGi, hq l hlL i hiN hb,
        ← ih (by omega) i hi, ← ih (by omega) _ hpart]
      rfl
    · have hGi : ¬ G l i := fun h => hb ((hG l hlL i hiN).mp h)
      rw [if_neg hb, hgpass l hlL i hiN hGi, hppass l hlL i hiN hGi, ← ih (by omega) i hi]

/-- **The block invariant, on the netlist**: after level `l ≤ L`, position `i ≤ N` holds the (generate, propagate)
pair of the aligned block `[(i >>> l) <<< l, i]` of the adder's positions. -/
theorem skl_block_of_eqs {N L : Nat} {a b : Nat → Bool} {cin : Bool} {g p : Nat → Nat → Bool}
    {G : Nat → Nat → Prop} {q : Nat → Nat → Nat}
    (hG : ∀ l, l < L → ∀ i, i < N + 1 → (G l i ↔ (i >>> l) % 2 = 1))
    (hq : ∀ l, l < L → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 → q l i = ((i >>> l) <<< l) - 1)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < L → ∀ i, i < N + 1 → G l i → g (l + 1) i = (g l i || (p l i && g l (q l i))))
    (hpop : ∀ l, l < L → ∀ i, i < N + 1 → G l i → p (l + 1) i = (p l i && p l (q l i)))
    (hgpass : ∀ l, l < L → ∀ i, i < N + 1 → ¬ G l i → g (l + 1) i = g l i)
    (hppass : ∀ l, l < L → ∀ i, i < N + 1 → ¬ G l i → p (l + 1) i = p l i)
    {l i : Nat} (hl : l ≤ L) (hi : i ≤ N) :
    (g l i, p l i) = pgBlock (addPos a b cin) ((i >>> l) <<< l) i := by
  rw [sklRec_of_eqs hG hq hg0 hp0 hgin hpin hgop hpop hgpass hppass l hl i hi, sklRec_block]

/-- **The end result, on the netlist** (`L = clog2 (N + 1)`): `g[L][i]` is the carry into bit `i` for every `i ≤ N`,
so `s[i] = a[i] ^ b[i] ^ carry_i` and `cout` is the carry out of bit `N - 1`. -/
theorem skl_adder {N : Nat} {a b : Nat → Bool} {cin : Bool} {g p : Nat → Nat → Bool}
    {G : Nat → Nat → Prop} {q : Nat → Nat → Nat}
    (hG : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (G l i ↔ (i >>> l) % 2 = 1))
    (hq : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 → q l i = ((i >>> l) <<< l) - 1)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → G l i →
      g (l + 1) i = (g l i || (p l i && g l (q l i))))
    (hpop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → G l i → p (l + 1) i = (p l i && p l (q l i)))
    (hgpass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ G l i → g (l + 1) i = g l i)
    (hppass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ G l i → p (l + 1) i = p l i)
    {x s : Nat → Bool} {cout : Bool}
    (hx : ∀ i, i < N → x i = (a i ^^ b i))
    (hs : ∀ i, i < N → s i = (x i ^^ g (clog2 (N + 1)) i))
    (hcout : cout = g (clog2 (N + 1)) N) :
    (∀ i, i ≤ N → g (clog2 (N + 1)) i = rippleCarry a b cin i) ∧
      (∀ i, i < N → s i = (a i ^^ b i ^^ rippleCarry a b cin i)) ∧
      cout = rippleCarry a b cin N := by
  have hc : ∀ i, i ≤ N → g (clog2 (N + 1)) i = rippleCarry a b cin i := by
    intro i hi
    have h := sklRec_of_eqs hG hq hg0 hp0 hgin hpin hgop hpop hgpass hppass (clog2 (N + 1))
      (Nat.le_refl _) i hi
    rw [skl_carry_clog2 a b cin hi, Prod.mk.injEq] at h
    exact h.1
  refine ⟨hc, fun i hi => ?_, ?_⟩
  · rw [hs i hi, hx i hi, hc i (by omega)]
  · rw [hcout, hc N (Nat.le_refl N)]

/-- **The adder view** (`CombLib.AddView`, the input of `CombLib.add_spec`): with the operand bit functions `a b`
equal to the bits of `A B : BitVec N` and `cin = c0`, the netlist's carries `g[L][·]`, its sum `s` and its carry out
`cout` form the ripple adder's view of `A + B + c0`. The glue: `add_spec (skl_addView …)`. -/
theorem skl_addView {N : Nat} {A B : BitVec N} {c0 : Bool} {a b : Nat → Bool} {cin : Bool}
    {g p : Nat → Nat → Bool} {G : Nat → Nat → Prop} {q : Nat → Nat → Nat}
    (ha : ∀ i, i < N → a i = A.getLsbD i) (hb : ∀ i, i < N → b i = B.getLsbD i) (hcin : cin = c0)
    (hG : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (G l i ↔ (i >>> l) % 2 = 1))
    (hq : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 → q l i = ((i >>> l) <<< l) - 1)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → G l i →
      g (l + 1) i = (g l i || (p l i && g l (q l i))))
    (hpop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → G l i → p (l + 1) i = (p l i && p l (q l i)))
    (hgpass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ G l i → g (l + 1) i = g l i)
    (hppass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ G l i → p (l + 1) i = p l i)
    {x s : Nat → Bool} {cout : Bool}
    (hx : ∀ i, i < N → x i = (a i ^^ b i))
    (hs : ∀ i, i < N → s i = (x i ^^ g (clog2 (N + 1)) i))
    (hcout : cout = g (clog2 (N + 1)) N) :
    AddView N A B c0 (g (clog2 (N + 1))) s cout := by
  obtain ⟨hc, hsum, -⟩ := skl_adder hG hq hg0 hp0 hgin hpin hgop hpop hgpass hppass hx hs hcout
  have hab : ∀ n, n ≤ N → rippleCarry a b cin n = rippleCarry A.getLsbD B.getLsbD c0 n := by
    intro n hn
    rw [hcin]
    exact rippleCarry_congr fun k hk => ⟨ha k (by omega), hb k (by omega)⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_, hcout⟩
  · rw [hc 0 (Nat.zero_le _), rippleCarry_zero, hcin]
  · rw [hc (i + 1) (by omega), hc i (by omega), hab (i + 1) (by omega), hab i (by omega), rippleCarry_succ]
  · rw [hsum i hi, ha i hi, hb i hi, hc i (by omega), hab i (by omega)]

/-- `skl_addView` at the source's own spelling of the guard (`(i >>> l) % 2 = 1`) and of the partner index
(`((i >>> l) <<< l) - 1`). -/
theorem skl_addView_nat {N : Nat} {A B : BitVec N} {c0 : Bool} {a b : Nat → Bool} {cin : Bool}
    {g p : Nat → Nat → Bool}
    (ha : ∀ i, i < N → a i = A.getLsbD i) (hb : ∀ i, i < N → b i = B.getLsbD i) (hcin : cin = c0)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 →
      g (l + 1) i = (g l i || (p l i && g l (((i >>> l) <<< l) - 1))))
    (hpop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 →
      p (l + 1) i = (p l i && p l (((i >>> l) <<< l) - 1)))
    (hgpass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ (i >>> l) % 2 = 1 → g (l + 1) i = g l i)
    (hppass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ (i >>> l) % 2 = 1 → p (l + 1) i = p l i)
    {x s : Nat → Bool} {cout : Bool}
    (hx : ∀ i, i < N → x i = (a i ^^ b i))
    (hs : ∀ i, i < N → s i = (x i ^^ g (clog2 (N + 1)) i))
    (hcout : cout = g (clog2 (N + 1)) N) :
    AddView N A B c0 (g (clog2 (N + 1))) s cout :=
  skl_addView (G := fun l i => (i >>> l) % 2 = 1) (q := fun l i => ((i >>> l) <<< l) - 1) ha hb hcin
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => rfl) hg0 hp0 hgin hpin hgop hpop hgpass hppass hx hs hcout

/-- The task's outputs, from the netlist's equations at the source's spelling: `s = (A + B + c0) mod 2^N`,
`cout = (A + B + c0) / 2^N` (`CombLib.add_spec`). -/
theorem skl_spec_nat {N : Nat} {A B : BitVec N} {c0 : Bool} {a b : Nat → Bool} {cin : Bool}
    {g p : Nat → Nat → Bool}
    (ha : ∀ i, i < N → a i = A.getLsbD i) (hb : ∀ i, i < N → b i = B.getLsbD i) (hcin : cin = c0)
    (hg0 : g 0 0 = cin) (hp0 : p 0 0 = false)
    (hgin : ∀ i, i < N → g 0 (i + 1) = (a i && b i))
    (hpin : ∀ i, i < N → p 0 (i + 1) = (a i ^^ b i))
    (hgop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 →
      g (l + 1) i = (g l i || (p l i && g l (((i >>> l) <<< l) - 1))))
    (hpop : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → (i >>> l) % 2 = 1 →
      p (l + 1) i = (p l i && p l (((i >>> l) <<< l) - 1)))
    (hgpass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ (i >>> l) % 2 = 1 → g (l + 1) i = g l i)
    (hppass : ∀ l, l < clog2 (N + 1) → ∀ i, i < N + 1 → ¬ (i >>> l) % 2 = 1 → p (l + 1) i = p l i)
    {x : Nat → Bool} {S : BitVec N} {cout : Bool}
    (hx : ∀ i, i < N → x i = (a i ^^ b i))
    (hs : ∀ i, i < N → S.getLsbD i = (x i ^^ g (clog2 (N + 1)) i))
    (hcout : cout = g (clog2 (N + 1)) N) :
    S = BitVec.ofNat N (A.toNat + B.toNat + c0.toNat) ∧
      BitVec.ofBool cout = BitVec.ofNat 1 ((A.toNat + B.toNat + c0.toNat) / 2 ^ N) :=
  add_spec (skl_addView_nat ha hb hcin hg0 hp0 hgin hpin hgop hpop hgpass hppass hx hs hcout)

/-! ## Non-vacuity: the recurrence at small widths

`sklRec (addPos a b cin)` evaluated by the kernel (`decide`) against `a + b + cin`, exhaustively at `N = 3`
(`L = 2`) and at the scoring point's two hardest corners for `N = 16` (`L = 5`). -/

/-- The recurrence's sum and carry out at width `N`, as numbers. -/
def sklSum (N : Nat) (A B : Nat) (c : Bool) : Nat :=
  let L := clog2 (N + 1)
  let pos := addPos A.testBit B.testBit c
  (List.range N).foldr (fun i acc => acc + 2 ^ i * ((A.testBit i ^^ B.testBit i ^^ (sklRec pos L i).1)).toNat)
    (2 ^ N * ((sklRec pos L N).1).toNat)

example : ∀ A, A < 8 → ∀ B, B < 8 → ∀ c : Bool, sklSum 3 A B c = A + B + c.toNat := by decide

example : sklSum 16 0xFFFF 0x0001 false = 0x10000 ∧ sklSum 16 0xFFFF 0xFFFF true = 0x1FFFF ∧
    sklSum 16 0xAAAA 0x5555 true = 0x10000 := by decide

end SvGolf.AddSklansky

end SklCore

/-! ## Axiom pins -/

/-- info: 'SvGolf.AddSklansky.sklRec_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SvGolf.AddSklansky.sklRec_block

/-- info: 'SvGolf.AddSklansky.skl_addView' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SvGolf.AddSklansky.skl_addView

/-- info: 'SvGolf.AddSklansky.skl_spec_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SvGolf.AddSklansky.skl_spec_nat
