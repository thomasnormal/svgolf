import Submission.Design
import LeanModels.Sv.CombLib
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import SvGolf.Comb
import LeanModels.Sv.Comb2
import LeanModels.Sv.Known2

/-!
# Task `mul`: a parametric Dadda multiplier with a ripple-carry final adder, for every `N`

`theorem Submission.solution : Submission.Goal` for every `N` with `1 ≤ N < 2^30`.

## The design

Columns `k = 0 .. 2N-1`; `T[s][k][i]` is bit `i` of column `k` before stage `s`. Stage 0 holds the
partial products (column `k`, bit `i` is `a[k-i-lo] & b[i+lo]`, `lo = max(0, k-N+1)`). There are
`S` stages, `S` the number of Dadda heights `d(0) = 2`, `d(r+1) = d(r) + ⌊d(r)/2⌋` below `N`; stage `s`
reduces every column to at most `t = d(S-1-s)` bits with `f` full adders and `h ≤ 1` half adders per
column, whose counts are closed forms in `N`, `s`, `k`. The two rows left are added by a ripple-carry
adder.

## The proof

1. **Arithmetic** (plain Lean): the weighted sum `Σ_k 2^k · (bits of column k)` is `a * b` for the
   partial products (`ldg_zero`) and is unchanged by every stage (`step_ledger`: a full adder is
   `x + y + z = s + 2c`, a half adder `x + y = s + 2c`, every other bit keeps its weight; the column
   counts satisfy a few linear identities, `id_*`, decided by `omega` region by region). After the
   last stage at most two bits are left per column (`final_rows`); the ripple-carry adder adds them
   (`ripple_final`).
2. **The design at symbolic `N`**: the header expressions evaluate to the closed forms (`eT_eval`,
   `eF_eval`, ...), the generate nest expands to the cell lists `ppProcs`, `stProcs`, `finProcs`
   (`gens_expand`), and `instantiate2` gives `dM N` (`d_instantiate2`).
3. **Comb profile and acyclicity**: every process is a slice assign; the write windows are pairwise
   disjoint (`dWs_pairwise`); the rank of a window is twice its stage band (`T`), plus one (`SM`, `CY`),
   then the final-adder carries in order (`rkW`, `dProcs_reads`). The one-driver guard passes, so
   `design.sem N = dM N` (`sem_eq`).
4. **The settled state**: by induction over the stages every cell of `T`, `SM`, `CY` holds the bit
   model `tv`/`smB`/`cyB` of part 1 (`cells_pp`, `cells_step`), then the carries of the final adder
   by induction over the columns (`cells_K`), and the output bits (`cells_P`, `dadda_settled`).
   `CombTask.satisfiedAt_of_comb` turns this into the statement (`solution`).

Nothing is unrolled at a fixed width; `N`, the inputs and every index stay symbolic. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

/-!
# Dadda multiplier: the arithmetic (plain Lean)

The column-compression ledger: the weighted sum `Σ_k 2^k · (bits of column k)` is the product
`a * b` before the first stage and is unchanged by every stage, because a full adder turns three
bits of weight `2^k` into a sum of weight `2^k` and a carry of weight `2^(k+1)`
(`x + y + z = s + 2c`), a half adder two (`x + y = s + 2c`), and every bit no adder uses moves on
with its weight. After the last stage every column holds at most two bits.
-/

namespace Submission

open LeanModels.Sv.CombLib


/-! ## 1. Finite sums -/

/-- `nsum f n = f 0 + … + f (n - 1)`. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum f n + f n

@[simp] theorem nsum_zero (f : Nat → Nat) : nsum f 0 = 0 := rfl

theorem nsum_succ (f : Nat → Nat) (n : Nat) : nsum f (n + 1) = nsum f n + f n := rfl

theorem nsum_congr {f g : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = g i) : nsum f n = nsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsum_succ, nsum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem nsum_add (f g : Nat → Nat) (n : Nat) :
    nsum (fun i => f i + g i) n = nsum f n + nsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [nsum_succ, ih]; omega

theorem nsum_mul (c : Nat) (f : Nat → Nat) (n : Nat) :
    nsum (fun i => c * f i) n = c * nsum f n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [nsum_succ, ih, Nat.mul_add]

theorem nsum_eq_zero {f : Nat → Nat} {n : Nat} (h : ∀ i < n, f i = 0) : nsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem nsum_split (f : Nat → Nat) (m n : Nat) :
    nsum f (m + n) = nsum f m + nsum (fun i => f (m + i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, nsum_succ, ih, nsum_succ]; omega

theorem nsum_front (f : Nat → Nat) (n : Nat) :
    nsum f (n + 1) = f 0 + nsum (fun i => f (i + 1)) n := by
  induction n with
  | zero => simp [nsum]
  | succ n ih => rw [nsum_succ, ih, nsum_succ]; omega

theorem nsum_triple (f : Nat → Nat) (n : Nat) :
    nsum f (3 * n) = nsum (fun q => f (3 * q) + f (3 * q + 1) + f (3 * q + 2)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 * n + 2 + 1 by omega, nsum_succ, nsum_succ, nsum_succ, ih, nsum_succ]
    rw [show 3 * n + 2 = 3 * n + 1 + 1 by omega]
    omega

theorem nsum_swap (g : Nat → Nat → Nat) (m n : Nat) :
    nsum (fun k => nsum (fun i => g k i) m) n = nsum (fun i => nsum (fun k => g k i) n) m := by
  induction n with
  | zero => simp only [nsum_zero]; exact (nsum_eq_zero (fun _ _ => rfl)).symm
  | succ n ih =>
    rw [nsum_succ, ih]
    simp only [nsum_succ]
    rw [nsum_add]

theorem nsum_two (f : Nat → Nat) : nsum f 2 = f 0 + f 1 := by simp [nsum]

theorem nsum_one (f : Nat → Nat) : nsum f 1 = f 0 := by simp [nsum]

theorem nsum_split3 (F : Nat → Nat) (a b c : Nat) :
    nsum F (a + (b + c)) =
      nsum F a + nsum (fun i => F (a + i)) b + nsum (fun j => F (a + b + j)) c := by
  rw [nsum_split F a (b + c), nsum_split (fun i => F (a + i)) b c, ← Nat.add_assoc]
  congr 1
  apply nsum_congr
  intro i _
  rw [Nat.add_assoc]

/-- Zero terms past `m` do not count. -/
theorem nsum_extend (f : Nat → Nat) {m n : Nat} (hmn : m ≤ n) (h0 : ∀ i, m ≤ i → i < n → f i = 0) :
    nsum f n = nsum f m := by
  obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
  rw [nsum_split, nsum_eq_zero (fun i hi => h0 (m + i) (by omega) (by omega)), Nat.add_zero]

/-- Zero terms below `m` do not count. -/
theorem nsum_shift_zero (f : Nat → Nat) {m n : Nat} (h0 : ∀ i < m, f i = 0) :
    nsum f (m + n) = nsum (fun i => f (m + i)) n := by
  rw [nsum_split, nsum_eq_zero h0, Nat.zero_add]

/-- A weighted bit sum is `bfVal`. -/
theorem bfVal_eq_nsum (f : Nat → Bool) (n : Nat) :
    bfVal f n = nsum (fun j => 2 ^ j * (f j).toNat) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bfVal, nsum_succ, ih]

theorem bfVal_lt (f : Nat → Bool) (n : Nat) : bfVal f n < 2 ^ n := by
  induction n with
  | zero => simp [bfVal]
  | succ n ih =>
    rw [bfVal, Nat.pow_succ]
    have := Bool.toNat_le (f n)
    have h2 : 2 ^ n * (f n).toNat ≤ 2 ^ n * 1 := Nat.mul_le_mul_left _ this
    omega

/-! ## 2. The Dadda heights and the number of stages -/

/-- `d(0) = 2`, `d(r+1) = d(r) + ⌊d(r) / 2⌋`: the 52 heights below `2^31`. -/
def ddTab : List Nat :=
  [2, 3, 4, 6, 9, 13, 19, 28, 42, 63, 94, 141, 211, 316, 474, 711, 1066, 1599, 2398, 3597, 5395,
   8092, 12138, 18207, 27310, 40965, 61447, 92170, 138255, 207382, 311073, 466609, 699913, 1049869,
   1574803, 2362204, 3543306, 5314959, 7972438, 11958657, 17937985, 26906977, 40360465, 60540697,
   90811045, 136216567, 204324850, 306487275, 459730912, 689596368, 1034394552, 1551591828]

def dd (r : Nat) : Nat := ddTab.getD r 0

theorem dd_succ_all : ∀ r, r < 51 → dd (r + 1) = dd r + dd r / 2 := by decide

theorem dd_ge_two_all : ∀ r, r < 52 → 2 ≤ dd r := by decide

theorem dd_zero : dd 0 = 2 := rfl

theorem dd_51 : 2 ^ 30 ≤ dd 51 := by decide

theorem dd_lt_succ {r : Nat} (hr : r < 51) : dd r < dd (r + 1) := by
  have h1 := dd_succ_all r hr
  have h2 := dd_ge_two_all r (by omega)
  omega

/-- The number of stages: the Dadda heights below `N`. -/
def nst (N : Nat) : Nat := nsum (fun r => if dd r < N then 1 else 0) 51

/-- An antitone indicator counts a prefix. -/
theorem count_prefix (P : Nat → Prop) [DecidablePred P] (hP : ∀ r, P (r + 1) → P r) :
    ∀ n, (nsum (fun r => if P r then 1 else 0) n ≤ n) ∧
      ∀ r < n, (P r ↔ r < nsum (fun r => if P r then 1 else 0) n) := by
  have anti : ∀ d r, P (r + d) → P r := by
    intro d
    induction d with
    | zero => intro r h; exact h
    | succ d ih => intro r h; exact ih r (hP (r + d) (by rw [← Nat.add_assoc] at h; exact h))
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hle, hiff⟩ := ih
    rw [nsum_succ]
    by_cases hn : P n
    · have hall : ∀ r, r ≤ n → P r := fun r hr => anti (n - r) r (by rwa [Nat.add_sub_of_le hr])
      have hcn : nsum (fun r => if P r then 1 else 0) n = n := by
        have hlt : ∀ r < n, r < nsum (fun r => if P r then 1 else 0) n :=
          fun r hr => (hiff r hr).mp (hall r (by omega))
        rcases n with _ | n
        · simp
        · have := hlt n (by omega); omega
      rw [if_pos hn, hcn]
      exact ⟨by omega, fun r hr => ⟨fun _ => by omega, fun _ => hall r (by omega)⟩⟩
    · rw [if_neg hn, Nat.add_zero]
      refine ⟨by omega, fun r hr => ?_⟩
      rcases Nat.lt_or_ge r n with h | h
      · exact hiff r h
      · obtain rfl : r = n := by omega
        exact ⟨fun h => absurd h hn, fun h => by omega⟩

theorem nst_spec (N : Nat) : nst N ≤ 51 ∧ ∀ r < 51, (dd r < N ↔ r < nst N) := by
  have hP : ∀ r, (r + 1 < 51 ∧ dd (r + 1) < N) → (r < 51 ∧ dd r < N) := by
    intro r ⟨h1, h2⟩
    exact ⟨by omega, Nat.lt_trans (dd_lt_succ (by omega)) h2⟩
  obtain ⟨hle, hiff⟩ := count_prefix (fun r => r < 51 ∧ dd r < N) hP 51
  have heq : nsum (fun r => if (r < 51 ∧ dd r < N) then 1 else 0) 51 = nst N := by
    unfold nst
    apply nsum_congr
    intro i hi
    by_cases h : dd i < N
    · simp [hi, h]
    · simp [h]
  rw [heq] at hle hiff
  refine ⟨hle, fun r hr => ?_⟩
  rw [← hiff r hr]
  exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩

theorem nst_le (N : Nat) : nst N ≤ 51 := (nst_spec N).1

theorem nst_iff {N r : Nat} (hr : r < 51) : dd r < N ↔ r < nst N := (nst_spec N).2 r hr

theorem nst_eq_zero {N : Nat} (h : N ≤ 2) : nst N = 0 := by
  have h0 : ¬ (0 < nst N) := fun h' => by
    have := (nst_iff (N := N) (r := 0) (by omega)).mpr h'
    rw [dd_zero] at this
    omega
  omega

theorem le_two_of_nst {N : Nat} (h : nst N = 0) : N ≤ 2 := by
  have := (nst_iff (N := N) (r := 0) (by omega))
  rw [dd_zero, h] at this
  rcases Nat.lt_or_ge 2 N with h2 | h2
  · exact absurd (this.mp h2) (Nat.lt_irrefl 0)
  · exact h2

/-- The target of stage `s`: `d(S - 1 - s)`. -/
def tS (N s : Nat) : Nat := dd (nst N - 1 - s)

/-- The height bound before stage `s`: `N` at the first stage, `d(S - s) = t + ⌊t / 2⌋` after. -/
def uS (N s : Nat) : Nat := if s = 0 then N else tS N s + tS N s / 2

/-- What a stage needs of its two numbers. -/
structure Stg (N s t u : Nat) : Prop where
  t2 : 2 ≤ t
  tu : t < u
  uN : u ≤ N
  u3 : 2 * u ≤ 3 * t
  first : s = 0 → u = N

theorem stg_of {N s : Nat} (hN : N < 2 ^ 30) (hs : s < nst N) : Stg N s (tS N s) (uS N s) := by
  have hle := nst_le N
  have hr : nst N - 1 - s < nst N := by omega
  have hbelow : dd (nst N - 1 - s) < N := (nst_iff (by omega)).mpr hr
  have h2 := dd_ge_two_all (nst N - 1 - s) (by omega)
  unfold uS tS
  by_cases h0 : s = 0
  · subst h0
    rw [if_pos rfl]
    simp only [Nat.sub_zero] at *
    have htop : N ≤ dd (nst N) := by
      by_cases h51 : nst N < 51
      · exact Nat.le_of_not_lt (fun h => Nat.lt_irrefl _ ((nst_iff h51).mp h))
      · have : nst N = 51 := by omega
        rw [this]; have := dd_51; omega
    have hsucc := dd_succ_all (nst N - 1) (by omega)
    rw [show nst N - 1 + 1 = nst N by omega] at hsucc
    exact ⟨h2, hbelow, Nat.le_refl _, by omega, fun _ => rfl⟩
  · rw [if_neg h0]
    have hsucc := dd_succ_all (nst N - 1 - s) (by omega)
    have hb2 : dd (nst N - 1 - s + 1) < N :=
      (nst_iff (by omega)).mpr (by omega)
    rw [hsucc] at hb2
    exact ⟨h2, by omega, by omega, by omega, fun h => absurd h h0⟩

theorem uS_prev {N s : Nat} (hs : s < nst N) (h1 : 1 ≤ s) : uS N s = tS N (s - 1) := by
  have hle := nst_le N
  unfold uS tS
  rw [if_neg (by omega)]
  have hsucc := dd_succ_all (nst N - 1 - s) (by omega)
  rw [show nst N - 1 - (s - 1) = nst N - 1 - s + 1 by omega, hsucc]

theorem tS_last {N : Nat} (h : 1 ≤ nst N) : tS N (nst N - 1) = 2 := by
  unfold tS
  rw [show nst N - 1 - (nst N - 1) = 0 by omega]
  rfl

/-! ## 3. The schedule of one column (closed forms) -/

/-- `1` if `p`, else `0`. -/
def ind (p : Prop) [Decidable p] : Nat := if p then 1 else 0

theorem ind_spec (p : Prop) [Decidable p] : (p ∧ ind p = 1) ∨ (¬ p ∧ ind p = 0) := by
  unfold ind
  by_cases h : p
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

def mF (N k : Nat) : Nat := min k (2 * N - k)
def mF' (N k : Nat) : Nat := min k (2 * N + 1 - k)
/-- Full adders of column `k`. -/
def fF (N s t u k : Nat) : Nat := (min (mF N k) u - t) - ind (s = 0 ∧ k = N)
/-- Half adders of column `k` (0 or 1). -/
def hF (N s t u k : Nat) : Nat := ind ((t ≤ k ∧ k < u) ∨ (s = 0 ∧ k = N))
/-- Carries into column `k`. -/
def cF (N t u k : Nat) : Nat := min (mF' N k) u - t
/-- Height of column `k` after a stage with target `t`. -/
def HnF (N t k : Nat) : Nat := if k ≤ 2 * N - t then min (k + 1) t else 2 * N - 1 - k
/-- Height of column `k` of the partial products. -/
def H0F (N k : Nat) : Nat := min (k + 1) (2 * N - 1 - k)
/-- Height of column `k` before a stage. -/
def HbF (N s u k : Nat) : Nat := if s = 0 then H0F N k else HnF N u k

theorem HnF_spec (N t k : Nat) :
    (k ≤ 2 * N - t ∧ HnF N t k = min (k + 1) t) ∨ (¬ k ≤ 2 * N - t ∧ HnF N t k = 2 * N - 1 - k) := by
  unfold HnF
  by_cases h : k ≤ 2 * N - t
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

theorem HbF_spec (N s u k : Nat) :
    (s = 0 ∧ HbF N s u k = min (k + 1) (2 * N - 1 - k)) ∨
      (s ≠ 0 ∧ k ≤ 2 * N - u ∧ HbF N s u k = min (k + 1) u) ∨
      (s ≠ 0 ∧ ¬ k ≤ 2 * N - u ∧ HbF N s u k = 2 * N - 1 - k) := by
  unfold HbF
  by_cases h : s = 0
  · exact Or.inl ⟨h, by rw [if_pos h]; rfl⟩
  · rw [if_neg h]
    rcases HnF_spec N u k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h, h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h, h1, h2⟩)

/-- The regions of a column index between the stage's thresholds. -/
theorem kregion (N t u k : Nat) :
    k < t ∨ (t ≤ k ∧ k < u) ∨ (u ≤ k ∧ k < N) ∨ k = N ∨ (N < k ∧ k ≤ 2 * N - u) ∨
      (2 * N - u < k ∧ k ≤ 2 * N - t) ∨ 2 * N - t < k := by
  omega

section ids

variable {N s t u : Nat} (hst : Stg N s t u)
include hst

set_option hygiene false in
/-- Every identity, region by region: the stage's facts in context, the column index placed between
the thresholds, every `min` and `if` decided by `omega`, then the linear goal. -/
macro "dsolve" k:term : tactic => `(tactic| (
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  try unfold fF
  try unfold hF
  try unfold cF
  try unfold HbF
  try unfold H0F
  try unfold HnF
  try unfold mF
  try unfold mF'
  try unfold ind
  rcases kregion N t u $k with h | h | h | h | h | h | h <;>
    rcases Nat.eq_zero_or_pos s with h0 | h0 <;>
    simp (disch := omega) only [Nat.min_eq_left, Nat.min_eq_right, if_pos, if_neg] <;> omega))

theorem id_reads {k : Nat} (hk : k < 2 * N) : 3 * fF N s t u k + 2 * hF N s t u k ≤ HbF N s u k := by
  dsolve k

theorem id_carry0 : cF N t u 0 = 0 := by
  have := hst.t2
  unfold cF mF'
  omega

theorem id_carry {k : Nat} (hk : k + 1 < 2 * N) : cF N t u (k + 1) = fF N s t u k + hF N s t u k := by
  dsolve k

theorem id_height {k : Nat} (hk : k < 2 * N) :
    cF N t u k + fF N s t u k + hF N s t u k +
      (HbF N s u k - (3 * fF N s t u k + 2 * hF N s t u k)) = HnF N t k := by
  dsolve k

theorem id_slots {k : Nat} (hk : k < 2 * N) : fF N s t u k + hF N s t u k ≤ u - t + 1 := by
  dsolve k

theorem id_top_f : fF N s t u (2 * N - 1) = 0 := by
  dsolve (2 * N - 1)

theorem id_top_h : hF N s t u (2 * N - 1) = 0 := by
  dsolve (2 * N - 1)

theorem id_top : fF N s t u (2 * N - 1) = 0 ∧ hF N s t u (2 * N - 1) = 0 :=
  ⟨id_top_f hst, id_top_h hst⟩

theorem id_Hb_le {k : Nat} : HbF N s u k ≤ N := by
  dsolve k

omit hst in
theorem id_h_le {k : Nat} : hF N s t u k ≤ 1 := by
  have := ind_spec ((t ≤ k ∧ k < u) ∨ (s = 0 ∧ k = N))
  unfold hF
  omega

end ids

theorem HnF_le (N t k : Nat) : HnF N t k ≤ t := by
  have := HnF_spec N t k
  omega

theorem add_congr' {a b c d : Nat} (h1 : a = b) (h2 : c = d) : a + c = b + d := by rw [h1, h2]

/-! ## 4. The model of the bits -/

/-- The `b` offset of column `k`'s partial products: `max(0, k - N + 1)`. -/
def loF (N k : Nat) : Nat := k - (N - 1)

/-- Stage 0: the partial products of column `k`, zeros above the column's height. -/
def T0 (N : Nat) (A B : Nat → Bool) (k i : Nat) : Bool :=
  if i < H0F N k then A (k - i - loF N k) && B (i + loF N k) else false

/-- The sum of adder `q` of column `k` in a stage (`false` above the adders). -/
def smB (N s t u : Nat) (T : Nat → Nat → Bool) (k q : Nat) : Bool :=
  if q < u - t + 1 then
    if q < fF N s t u k then (T k (3 * q) ^^ T k (3 * q + 1)) ^^ T k (3 * q + 2)
    else if q < fF N s t u k + hF N s t u k then T k (3 * q) ^^ T k (3 * q + 1)
    else false
  else false

/-- The carry of adder `q` of column `k` in a stage. -/
def cyB (N s t u : Nat) (T : Nat → Nat → Bool) (k q : Nat) : Bool :=
  if q < u - t + 1 then
    if q < fF N s t u k then
      (T k (3 * q) && T k (3 * q + 1)) || (T k (3 * q + 2) && (T k (3 * q) ^^ T k (3 * q + 1)))
    else if q < fF N s t u k + hF N s t u k then T k (3 * q) && T k (3 * q + 1)
    else false
  else false

/-- Column `k` after a stage: carries in, sums, the bits no adder used, zeros. -/
def stepT (N s t u : Nat) (T : Nat → Nat → Bool) (k i : Nat) : Bool :=
  if i < t then
    if i < cF N t u k then cyB N s t u T (k - 1) i
    else if i < cF N t u k + fF N s t u k + hF N s t u k then smB N s t u T k (i - cF N t u k)
    else if i < HnF N t k then T k (i - cF N t u k + 2 * fF N s t u k + hF N s t u k)
    else false
  else false

/-- The bits before stage `s`. -/
def tv (N : Nat) (A B : Nat → Bool) : Nat → Nat → Nat → Bool
  | 0 => T0 N A B
  | s + 1 => stepT N s (tS N s) (uS N s) (tv N A B s)

/-- The height of the columns before stage `s`. -/
def Hs (N s k : Nat) : Nat := if s = 0 then H0F N k else HnF N (tS N (s - 1)) k

/-! ## 5. One column through one stage -/

theorem col_new (T Tn cy sm : Nat → Bool) (c f h Hb Hn t : Nat)
    (hH : c + f + h + (Hb - (3 * f + 2 * h)) = Hn) (hHt : Hn ≤ t)
    (hTn : ∀ i, Tn i = if i < t then (if i < c then cy i else if i < c + f + h then sm (i - c)
      else if i < Hn then T (i - c + 2 * f + h) else false) else false) :
    nsum (fun i => (Tn i).toNat) Hn =
      nsum (fun i => (cy i).toNat) c + nsum (fun q => (sm q).toNat) (f + h) +
        nsum (fun j => (T (3 * f + 2 * h + j)).toNat) (Hb - (3 * f + 2 * h)) := by
  rw [← hH, show c + f + h + (Hb - (3 * f + 2 * h)) = c + ((f + h) + (Hb - (3 * f + 2 * h))) by omega,
    nsum_split3]
  refine add_congr' (add_congr' ?_ ?_) ?_
  · apply nsum_congr
    intro i hi
    have c1 : i < t := by omega
    simp only [hTn, c1, hi, ite_true]
  · apply nsum_congr
    intro q hq
    have c1 : c + q < t := by omega
    have c2 : ¬ c + q < c := by omega
    have c3 : c + q < c + f + h := by omega
    simp only [hTn, c1, c2, c3, ite_true, ite_false, Nat.add_sub_cancel_left]
  · apply nsum_congr
    intro j hj
    have c1 : c + (f + h) + j < t := by omega
    have c2 : ¬ c + (f + h) + j < c := by omega
    have c3 : ¬ c + (f + h) + j < c + f + h := by omega
    have c5 : c + (f + h) + j < Hn := by omega
    simp only [hTn, c1, c2, c3, c5, ite_true, ite_false]
    all_goals rw [show c + (f + h) + j - c + 2 * f + h = 3 * f + 2 * h + j by omega]

theorem ha_arith (x y : Bool) : (x ^^ y).toNat + 2 * (x && y).toNat = x.toNat + y.toNat := by
  cases x <;> cases y <;> decide

theorem col_old (T sm cy : Nat → Bool) (f h w Hb : Nat) (hh : h ≤ 1) (hw : f + h ≤ w)
    (hR : 3 * f + 2 * h ≤ Hb)
    (hsm : ∀ q, sm q = if q < w then (if q < f then (T (3 * q) ^^ T (3 * q + 1)) ^^ T (3 * q + 2)
      else if q < f + h then T (3 * q) ^^ T (3 * q + 1) else false) else false)
    (hcy : ∀ q, cy q = if q < w then (if q < f then
        (T (3 * q) && T (3 * q + 1)) || (T (3 * q + 2) && (T (3 * q) ^^ T (3 * q + 1)))
      else if q < f + h then T (3 * q) && T (3 * q + 1) else false) else false) :
    nsum (fun i => (T i).toNat) Hb =
      nsum (fun q => (sm q).toNat) (f + h) + 2 * nsum (fun q => (cy q).toNat) (f + h) +
        nsum (fun j => (T (3 * f + 2 * h + j)).toNat) (Hb - (3 * f + 2 * h)) := by
  obtain ⟨R, rfl⟩ : ∃ R, Hb = 3 * f + 2 * h + R := ⟨Hb - (3 * f + 2 * h), by omega⟩
  rw [Nat.add_sub_cancel_left, nsum_split (fun i => (T i).toNat) (3 * f + 2 * h) R,
    nsum_split (fun i => (T i).toNat) (3 * f) (2 * h), nsum_triple]
  refine add_congr' ?_ rfl
  rw [← nsum_mul, ← nsum_add, nsum_split (fun q => (sm q).toNat + 2 * (cy q).toNat) f h]
  refine add_congr' ?_ ?_
  · apply nsum_congr
    intro q hq
    have c1 : q < w := by omega
    simp only [hsm, hcy, c1, hq, ite_true]
    have := fullAdder_arith (T (3 * q)) (T (3 * q + 1)) (T (3 * q + 2))
    omega
  · rcases (show h = 0 ∨ h = 1 by omega) with rfl | rfl
    · rfl
    · rw [show 2 * 1 = 2 from rfl, nsum_two, nsum_one]
      have c1 : f < w := by omega
      have c2 : ¬ f < f := Nat.lt_irrefl f
      have c3 : f < f + 1 := Nat.lt_succ_self f
      simp only [Nat.add_zero, hsm, hcy, c1, c2, c3, ite_true, ite_false]
      have := ha_arith (T (3 * f)) (T (3 * f + 1))
      omega

/-! ## 6. The ledger is unchanged by a stage -/

/-- The weighted sum of the columns, column `k` holding the bits below `H k`. -/
def ldg (N : Nat) (H : Nat → Nat) (T : Nat → Nat → Bool) : Nat :=
  nsum (fun k => 2 ^ k * nsum (fun i => (T k i).toNat) (H k)) (2 * N)

theorem ldg_congr {N : Nat} {H H' : Nat → Nat} {T T' : Nat → Nat → Bool}
    (hH : ∀ k < 2 * N, H k = H' k) (hT : ∀ k < 2 * N, ∀ i < H k, T k i = T' k i) :
    ldg N H T = ldg N H' T' := by
  unfold ldg
  apply nsum_congr
  intro k hk
  rw [← hH k hk]
  congr 1
  apply nsum_congr
  intro i hi
  rw [hT k hk i hi]

theorem step_ledger {N s t u : Nat} (hN : 1 ≤ N) (hst : Stg N s t u) (T : Nat → Nat → Bool) :
    ldg N (HnF N t) (stepT N s t u T) = ldg N (HbF N s u) T := by
  -- the per-column parts
  let SMs : Nat → Nat := fun k =>
    nsum (fun q => (smB N s t u T k q).toNat) (fF N s t u k + hF N s t u k)
  let CYs : Nat → Nat := fun k =>
    nsum (fun q => (cyB N s t u T k q).toNat) (fF N s t u k + hF N s t u k)
  let R : Nat → Nat := fun k =>
    nsum (fun j => (T k (3 * fF N s t u k + 2 * hF N s t u k + j)).toNat)
      (HbF N s u k - (3 * fF N s t u k + 2 * hF N s t u k))
  let CYp : Nat → Nat := fun k => nsum (fun i => (cyB N s t u T (k - 1) i).toNat) (cF N t u k)
  have hnew : ∀ k < 2 * N, nsum (fun i => (stepT N s t u T k i).toNat) (HnF N t k) =
      CYp k + SMs k + R k := by
    intro k hk
    exact col_new (T k) (stepT N s t u T k) (cyB N s t u T (k - 1)) (smB N s t u T k)
      (cF N t u k) (fF N s t u k) (hF N s t u k) (HbF N s u k) (HnF N t k) t
      (id_height hst hk) (HnF_le N t k) (fun i => rfl)
  have hold : ∀ k < 2 * N, nsum (fun i => (T k i).toNat) (HbF N s u k) =
      SMs k + 2 * CYs k + R k := by
    intro k hk
    exact col_old (T k) (smB N s t u T k) (cyB N s t u T k) (fF N s t u k) (hF N s t u k)
      (u - t + 1) (HbF N s u k) id_h_le (id_slots hst hk) (id_reads hst hk)
      (fun q => rfl) (fun q => rfl)
  have hp0 : CYp 0 = 0 := by
    show nsum _ (cF N t u 0) = 0
    rw [id_carry0 hst]; rfl
  have hp1 : ∀ k, k + 1 < 2 * N → CYp (k + 1) = CYs k := by
    intro k hk
    show nsum _ (cF N t u (k + 1)) = _
    rw [id_carry hst hk]
    rfl
  obtain ⟨M, hM⟩ : ∃ M, 2 * N = M + 1 := ⟨2 * N - 1, by omega⟩
  have htop : CYs M = 0 := by
    show nsum _ (fF N s t u M + hF N s t u M) = 0
    have ht := id_top hst
    rw [show 2 * N - 1 = M by omega] at ht
    rw [ht.1, ht.2]; rfl
  have L1 : ldg N (HnF N t) (stepT N s t u T) =
      nsum (fun k => 2 ^ k * CYp k) (2 * N) + nsum (fun k => 2 ^ k * (SMs k + R k)) (2 * N) := by
    unfold ldg
    rw [← nsum_add]
    apply nsum_congr
    intro k hk
    rw [hnew k hk]
    simp only [Nat.mul_add]
    omega
  have L2 : ldg N (HbF N s u) T =
      nsum (fun k => 2 ^ k * (2 * CYs k)) (2 * N) + nsum (fun k => 2 ^ k * (SMs k + R k)) (2 * N) := by
    unfold ldg
    rw [← nsum_add]
    apply nsum_congr
    intro k hk
    rw [hold k hk]
    simp only [Nat.mul_add]
    omega
  rw [L1, L2]
  refine add_congr' ?_ rfl
  rw [hM, nsum_front (fun k => 2 ^ k * CYp k) M, nsum_succ (fun k => 2 ^ k * (2 * CYs k)) M, hp0,
    htop]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  apply nsum_congr
  intro k hk
  rw [hp1 k (by omega), Nat.pow_succ, Nat.mul_assoc]

/-! ## 7. Stage 0: the partial products hold the product -/

theorem ldg_zero (N : Nat) (hN : 1 ≤ N) (A B : Nat → Bool) :
    ldg N (H0F N) (T0 N A B) = bfVal A N * bfVal B N := by
  -- the partial product of column `k` with `b` index `j`
  let P : Nat → Nat → Nat := fun k j => if j ≤ k ∧ k - j < N then (A (k - j) && B j).toNat else 0
  have hcol : ∀ k < 2 * N, nsum (fun i => (T0 N A B k i).toNat) (H0F N k) = nsum (P k) N := by
    intro k hk
    by_cases hkN : k < N
    · have hH : H0F N k = k + 1 := by unfold H0F; omega
      have hlo : loF N k = 0 := by unfold loF; omega
      rw [nsum_extend (P k) (m := k + 1) (by omega) (fun i hi _ => by
        show (if i ≤ k ∧ k - i < N then _ else 0) = 0
        rw [if_neg (by omega)]), hH]
      apply nsum_congr
      intro i hi
      have c1 : i < H0F N k := by omega
      have c2 : i ≤ k ∧ k - i < N := by omega
      show (if i < H0F N k then _ else false).toNat = if i ≤ k ∧ k - i < N then _ else 0
      rw [if_pos c1, if_pos c2, hlo, Nat.sub_zero, Nat.add_zero]
    · have hH : H0F N k = 2 * N - 1 - k := by unfold H0F; omega
      have e := nsum_shift_zero (P k) (m := k - (N - 1)) (n := 2 * N - 1 - k) (fun i hi => by
        show (if i ≤ k ∧ k - i < N then _ else 0) = 0
        rw [if_neg (by omega)])
      rw [show k - (N - 1) + (2 * N - 1 - k) = N by omega] at e
      rw [e, hH]
      apply nsum_congr
      intro i hi
      have c1 : i < H0F N k := by omega
      have c2 : k - (N - 1) + i ≤ k ∧ k - (k - (N - 1) + i) < N := by omega
      show (if i < H0F N k then _ else false).toNat =
        if k - (N - 1) + i ≤ k ∧ k - (k - (N - 1) + i) < N then _ else 0
      rw [if_pos c1, if_pos c2]
      unfold loF
      rw [show k - i - (k - (N - 1)) = k - (k - (N - 1) + i) by omega, Nat.add_comm i]
  have hL : ldg N (H0F N) (T0 N A B) = nsum (fun k => nsum (fun j => 2 ^ k * P k j) N) (2 * N) := by
    unfold ldg
    apply nsum_congr
    intro k hk
    rw [hcol k hk, nsum_mul]
  rw [hL, nsum_swap (fun k j => 2 ^ k * P k j)]
  -- one `b` bit: its row of partial products
  have hrow : ∀ j < N, nsum (fun k => 2 ^ k * P k j) (2 * N) =
      2 ^ j * (B j).toNat * bfVal A N := by
    intro j hj
    have e1 := nsum_shift_zero (fun k => 2 ^ k * P k j) (m := j) (n := 2 * N - j) (fun i hi => by
      show 2 ^ i * (if j ≤ i ∧ i - j < N then _ else 0) = 0
      rw [if_neg (by omega), Nat.mul_zero])
    rw [show j + (2 * N - j) = 2 * N by omega] at e1
    rw [e1, nsum_extend _ (m := N) (by omega) (fun i hi1 hi2 => by
      show 2 ^ (j + i) * (if j ≤ j + i ∧ j + i - j < N then _ else 0) = 0
      rw [if_neg (by omega), Nat.mul_zero]), bfVal_eq_nsum, ← nsum_mul]
    apply nsum_congr
    intro i hi
    show 2 ^ (j + i) * (if j ≤ j + i ∧ j + i - j < N then _ else 0) = _
    rw [if_pos (show j ≤ j + i ∧ j + i - j < N by omega), show j + i - j = i by omega, Nat.pow_add]
    cases A i <;> cases B j <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [nsum_congr hrow, bfVal_eq_nsum B N, ← nsum_mul]
  exact nsum_congr (fun j _ => Nat.mul_comm _ _)

/-! ## 8. Every stage keeps the product; the last leaves two rows -/

theorem tv_zero {N : Nat} (A B : Nat → Bool) (hN : N < 2 ^ 30) :
    ∀ s, s ≤ nst N → ∀ k i, k < 2 * N → Hs N s k ≤ i → tv N A B s k i = false := by
  intro s hs k i hk hi
  cases s with
  | zero =>
    have c1 : ¬ i < H0F N k := by simp [Hs] at hi; omega
    show (if i < H0F N k then _ else false) = false
    rw [if_neg c1]
  | succ s =>
    have hst := stg_of hN (show s < nst N by omega)
    have hh := id_height hst hk
    have hi' : HnF N (tS N s) k ≤ i := by simpa [Hs] using hi
    show stepT N s (tS N s) (uS N s) (tv N A B s) k i = false
    unfold stepT
    have c1 : ¬ i < cF N (tS N s) (uS N s) k := by omega
    have c2 : ¬ i < cF N (tS N s) (uS N s) k + fF N s (tS N s) (uS N s) k +
        hF N s (tS N s) (uS N s) k := by omega
    have c3 : ¬ i < HnF N (tS N s) k := by omega
    simp only [c1, c2, c3, ite_false, ite_self]

theorem tv_ledger {N : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 30) (A B : Nat → Bool) :
    ∀ s, s ≤ nst N → ldg N (Hs N s) (tv N A B s) = bfVal A N * bfVal B N := by
  intro s
  induction s with
  | zero =>
    intro _
    rw [← ldg_zero N hN1 A B]
    exact ldg_congr (fun k _ => by simp [Hs]) (fun k _ i _ => rfl)
  | succ s ih =>
    intro hs
    have hst := stg_of hN (show s < nst N by omega)
    have e1 : ldg N (Hs N (s + 1)) (tv N A B (s + 1)) =
        ldg N (HnF N (tS N s)) (stepT N s (tS N s) (uS N s) (tv N A B s)) :=
      ldg_congr (fun k _ => by simp [Hs]) (fun k _ i _ => rfl)
    have e2 : ldg N (HbF N s (uS N s)) (tv N A B s) = ldg N (Hs N s) (tv N A B s) := by
      apply ldg_congr _ (fun k _ i _ => rfl)
      intro k _
      unfold HbF Hs
      by_cases h0 : s = 0
      · simp [h0]
      · rw [if_neg h0, if_neg h0, uS_prev (by omega) (by omega)]
    rw [e1, step_ledger hN1 hst, e2, ih (by omega)]

/-- **The two rows left after the last stage add up to the product.** -/
theorem final_rows {N : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 30) (A B : Nat → Bool) :
    bfVal (fun k => tv N A B (nst N) k 0) (2 * N) + bfVal (fun k => tv N A B (nst N) k 1) (2 * N) =
      bfVal A N * bfVal B N := by
  rw [← tv_ledger hN1 hN A B (nst N) (Nat.le_refl _)]
  unfold ldg
  rw [bfVal_eq_nsum, bfVal_eq_nsum, ← nsum_add]
  apply nsum_congr
  intro k hk
  have hle : Hs N (nst N) k ≤ 2 := by
    unfold Hs
    split
    · have := le_two_of_nst (by assumption)
      unfold H0F
      omega
    · exact Nat.le_trans (HnF_le _ _ _) (Nat.le_of_eq (tS_last (by omega)))
  have hz := tv_zero A B hN (nst N) (Nat.le_refl _) k
  rcases (show Hs N (nst N) k = 0 ∨ Hs N (nst N) k = 1 ∨ Hs N (nst N) k = 2 by omega) with h | h | h
  · rw [h, hz 0 hk (by omega), hz 1 hk (by omega)]
    simp
  · rw [h, hz 1 hk (by omega), nsum_one]
    simp
  · rw [h, nsum_two, Nat.mul_add]

/-! ## 9. The final ripple-carry adder -/

theorem ripple_final (n : Nat) (x y p K : Nat → Bool) (hK0 : K 0 = false)
    (hp : ∀ k < n, p k = ((x k ^^ y k) ^^ K k))
    (hK : ∀ k < n, K (k + 1) = ((x k && y k) || (K k && (x k ^^ y k))))
    (hv : bfVal x n + bfVal y n < 2 ^ n) : bfVal p n = bfVal x n + bfVal y n := by
  have h := ripple_row n x y (fun j => x j ^^ y j) p K (fun j _ => rfl) hp hK
  rw [hK0] at h
  have hb := bfVal_lt p n
  cases hKn : K n
  · rw [hKn] at h
    simp at h
    omega
  · rw [hKn] at h
    simp at h
    omega

end Submission

/-! # The envelope's vocabulary: the design's expressions, templates and generate tree -/

namespace Submission

open LeanModels.Sv

/-! ## 1. Expression vocabulary -/

abbrev gv (n : String) : PExpr := .genvarRef n
abbrev pr (n : String) : PExpr := .paramRef n none
abbrev ii (v : Int) : PExpr := .int v
abbrev eAdd (a b : PExpr) : PExpr := .binary (.m0 .add) a b
abbrev eSub (a b : PExpr) : PExpr := .binary (.m0 .sub) a b
abbrev eMul (a b : PExpr) : PExpr := .binary .mul a b
abbrev eSlt (a b : PExpr) : PExpr := .binary .slt a b
abbrev eSle (a b : PExpr) : PExpr := .binary .sle a b
abbrev eSgt (a b : PExpr) : PExpr := .binary .sgt a b
abbrev eSge (a b : PExpr) : PExpr := .binary .sge a b
abbrev eEq (a b : PExpr) : PExpr := .binary (.m0 .eq) a b
abbrev eLand (a b : PExpr) : PExpr := .binary .land a b
abbrev eLor (a b : PExpr) : PExpr := .binary .lor a b
abbrev eShr (a b : PExpr) : PExpr := .binary .shr a b
abbrev eTer (c a b : PExpr) : PExpr := .ternary c a b
abbrev eAnd (a b : PExpr) : PExpr := .binary (.m0 .and) a b
abbrev eOr (a b : PExpr) : PExpr := .binary (.m0 .or) a b
abbrev eXor (a b : PExpr) : PExpr := .binary (.m0 .xor) a b
abbrev lit0 : LVec := { bits := #[Logic.l0] }

/-- `for (g = init; g < bound; g++)`. -/
abbrev gFor (lab g : String) (init bound : PExpr) (rc : Nat) (body : List GenItem) : GenItem :=
  .genFor (some lab) g init (eSlt (gv g) bound) (.unary .inc (gv g)) (some rc) body

/-- `2 * N`. -/
abbrev e2N : PExpr := eMul (ii 2) (pr "N")

/-! ## 2. The header expressions -/

/-- `S - 1 - s`, the index of the stage's target in the height table. -/
abbrev eR : PExpr := eSub (eSub (pr "S") (ii 1)) (gv "s")

/-- One group of the table: `(R == j) ? d(j) : … : d(j + c)`. -/
def chainE : Nat → Nat → PExpr
  | j, 0 => ii (dd j)
  | j, c + 1 => eTer (eEq eR (ii j)) (ii (dd j)) (chainE (j + 1) c)

/-- The table in groups of eight: `(R < 8g + 8) ? group g : …`. -/
def gchE : Nat → Nat → PExpr
  | _, 0 => chainE 48 2
  | g, n + 1 => eTer (eSlt eR (ii (8 * g + 8))) (chainE (8 * g) 7) (gchE (g + 1) n)

/-- The target `t` of stage `s`. -/
abbrev eT : PExpr := gchE 0 6

/-- `u = (s == 0) ? N : t + (t >> 1)`. -/
abbrev eU : PExpr := eTer (eEq (gv "s") (ii 0)) (pr "N") (eAdd (gv "t") (eShr (gv "t") (ii 1)))

/-- `(k <= N) ? k : 2N - k`. -/
abbrev eMk : PExpr := eTer (eSle (gv "k") (pr "N")) (gv "k") (eSub e2N (gv "k"))
/-- `(k <= N) ? k : 2N + 1 - k`. -/
abbrev eMk' : PExpr := eTer (eSle (gv "k") (pr "N")) (gv "k") (eSub (eAdd e2N (ii 1)) (gv "k"))
/-- `(x < u) ? x : u`. -/
abbrev eMinU (x : PExpr) : PExpr := eTer (eSlt x (gv "u")) x (gv "u")
/-- `(x > t) ? x - t : 0`. -/
abbrev ePosT (x : PExpr) : PExpr := eTer (eSgt x (gv "t")) (eSub x (gv "t")) (ii 0)
/-- `(s == 0) ? ((k == N) ? 1 : 0) : 0`: the first stage's column `N`. -/
abbrev eFirst : PExpr := eTer (eEq (gv "s") (ii 0)) (eTer (eEq (gv "k") (pr "N")) (ii 1) (ii 0)) (ii 0)

abbrev eF : PExpr := eSub (ePosT (eMinU eMk)) eFirst
abbrev eH : PExpr := eTer (eSge (gv "k") (gv "t")) (eTer (eSlt (gv "k") (gv "u")) (ii 1) eFirst) eFirst
abbrev eC : PExpr := ePosT (eMinU eMk')

/-- The height of column `k` of the partial products: `(k < N) ? k + 1 : 2N - 1 - k`. -/
abbrev eH0 : PExpr := eTer (eSlt (gv "k") (pr "N")) (eAdd (gv "k") (ii 1)) (eSub (eSub e2N (ii 1)) (gv "k"))
/-- The `b` offset of column `k`: `(k >= N) ? k - N + 1 : 0`. -/
abbrev eLo : PExpr := eTer (eSge (gv "k") (pr "N")) (eAdd (eSub (gv "k") (pr "N")) (ii 1)) (ii 0)
/-- The height after a stage: `(k <= 2N - t) ? ((k < t) ? k + 1 : t) : 2N - 1 - k`. -/
abbrev eHn : PExpr :=
  eTer (eSle (gv "k") (eSub e2N (gv "t"))) (eTer (eSlt (gv "k") (gv "t")) (eAdd (gv "k") (ii 1)) (gv "t"))
    (eSub (eSub e2N (ii 1)) (gv "k"))

/-! ## 3. The templates -/

/-- `T[s][k][i]`-style cell. -/
abbrev cell (n : String) (a b c : PExpr) : PExpr := .arrayElem n [a, b, c]

def ppAndT : PProcess :=
  .assignL (.arrayElem "T" [ii 0, gv "k", gv "i"])
    (eAnd (.bitSel (.ident "a") (eSub (eSub (gv "k") (gv "i")) eLo))
      (.bitSel (.ident "b") (eAdd (gv "i") eLo)))
def ppZeroT : PProcess := .assignL (.arrayElem "T" [ii 0, gv "k", gv "i"]) (.lit lit0)

abbrev tq0 : PExpr := cell "T" (gv "s") (gv "k") (eMul (ii 3) (gv "q"))
abbrev tq1 : PExpr := cell "T" (gv "s") (gv "k") (eAdd (eMul (ii 3) (gv "q")) (ii 1))
abbrev tq2 : PExpr := cell "T" (gv "s") (gv "k") (eAdd (eMul (ii 3) (gv "q")) (ii 2))

def faSmT : PProcess := .assignL (.arrayElem "SM" [gv "s", gv "k", gv "q"]) (eXor (eXor tq0 tq1) tq2)
def faCyT : PProcess :=
  .assignL (.arrayElem "CY" [gv "s", gv "k", gv "q"]) (eOr (eAnd tq0 tq1) (eAnd tq2 (eXor tq0 tq1)))
def haSmT : PProcess := .assignL (.arrayElem "SM" [gv "s", gv "k", gv "q"]) (eXor tq0 tq1)
def haCyT : PProcess := .assignL (.arrayElem "CY" [gv "s", gv "k", gv "q"]) (eAnd tq0 tq1)
def noSmT : PProcess := .assignL (.arrayElem "SM" [gv "s", gv "k", gv "q"]) (.lit lit0)
def noCyT : PProcess := .assignL (.arrayElem "CY" [gv "s", gv "k", gv "q"]) (.lit lit0)
/-- `u - t + 1`, the adder slots of a column. -/
abbrev eW : PExpr := eAdd (eSub (gv "u") (gv "t")) (ii 1)
def smPartT : PProcess := .assignL (.arrayPart "SM" [gv "s", gv "k"] .range (eSub (pr "NP") (ii 1)) eW) (.fill .l0)
def cyPartT : PProcess := .assignL (.arrayPart "CY" [gv "s", gv "k"] .range (eSub (pr "NP") (ii 1)) eW) (.fill .l0)
abbrev tNext : PLhs := .arrayElem "T" [eAdd (gv "s") (ii 1), gv "k", gv "i"]
def carT : PProcess := .assignL tNext (cell "CY" (gv "s") (eSub (gv "k") (ii 1)) (gv "i"))
def sumT : PProcess := .assignL tNext (cell "SM" (gv "s") (gv "k") (eSub (gv "i") (gv "c")))
def keepT : PProcess :=
  .assignL tNext (cell "T" (gv "s") (gv "k") (eAdd (eAdd (eSub (gv "i") (gv "c")) (eMul (ii 2) (gv "f"))) (gv "h")))
def zeroT : PProcess := .assignL tNext (.lit lit0)
def tPartT : PProcess :=
  .assignL (.arrayPart "T" [eAdd (gv "s") (ii 1), gv "k"] .range (eSub (pr "NP") (ii 1)) (gv "t")) (.fill .l0)

abbrev tS0 : PExpr := cell "T" (pr "S") (gv "k") (ii 0)
abbrev tS1 : PExpr := cell "T" (pr "S") (gv "k") (ii 1)
abbrev kK : PExpr := .bitSel (.ident "K") (gv "k")
def finPT : PProcess := .assignL (.bitSel "p" (gv "k")) (eXor (eXor tS0 tS1) kK)
def finKT : PProcess :=
  .assignL (.bitSel "K" (eAdd (gv "k") (ii 1))) (eOr (eAnd tS0 tS1) (eAnd kK (eXor tS0 tS1)))

def smRowT : PProcess := .assignL (.arrayElem "SM" [pr "S"]) (.fill .l0)
def cyRowT : PProcess := .assignL (.arrayElem "CY" [pr "S"]) (.fill .l0)
def k0T : PProcess := .assignL (.arrayElem "K" [ii 0]) (.lit lit0)

/-! ## 4. The generate tree -/

abbrev proc (p : PProcess) : GenItem := .process p

def ppGen : GenItem :=
  gFor "g_pp" "k" (ii 0) e2N 32
    [gFor "g_bit" "i" (ii 0) (pr "NP") 16
      [.genIf (eSlt (gv "i") eH0) [proc ppAndT] [proc ppZeroT]]]

/-- The body of one adder slot `q`. -/
def addGen : GenItem :=
  .genIf (eSlt (gv "q") (gv "f")) [proc faSmT, proc faCyT]
    [.genIf (eSlt (gv "q") (eAdd (gv "f") (gv "h"))) [proc haSmT, proc haCyT] [proc noSmT, proc noCyT]]

/-- The body of one bit `i` after the stage. -/
def bitGen : GenItem :=
  .genIf (eSlt (gv "i") (gv "c")) [proc carT]
    [.genIf (eSlt (gv "i") (eAdd (eAdd (gv "c") (gv "f")) (gv "h"))) [proc sumT]
      [.genIf (eSlt (gv "i") eHn) [proc keepT] [proc zeroT]]]

/-- The body of one column under its `f`, `h`, `c`. -/
def colBody : List GenItem :=
  [gFor "g_add" "q" (ii 0) eW 4 [addGen], proc smPartT, proc cyPartT,
   gFor "g_bit" "i" (ii 0) (gv "t") 13 [bitGen], proc tPartT]

def colGen : GenItem :=
  gFor "g_col" "k" (ii 0) e2N 32
    [gFor "g_f" "f" eF (eAdd eF (ii 1)) 1
      [gFor "g_h" "h" eH (eAdd eH (ii 1)) 1
        [gFor "g_c" "c" eC (eAdd eC (ii 1)) 1 colBody]]]

def stGen : GenItem :=
  gFor "g_st" "s" (ii 0) (pr "S") 6
    [gFor "g_t" "t" eT (eAdd eT (ii 1)) 1
      [gFor "g_u" "u" eU (eAdd eU (ii 1)) 1 [colGen]]]

def finGen : GenItem := gFor "g_fin" "k" (ii 0) e2N 32 [proc finPT, proc finKT]

end Submission

/-! # Constant evaluation of the header expressions (the INT class, symbolic genvars) -/

namespace Submission

open LeanModels.Sv

section ev

variable {E : IEnv}

theorem ev_add {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary (.m0 .add) l r) = (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a + b)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]

theorem ev_sub {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary (.m0 .sub) l r) = (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a - b)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]

theorem ev_mul {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary .mul l r) = (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a * b)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]

/-- Reading a decided comparison: the bind of two decided evaluations. -/
theorem ev_cmp_aux {x y : Except String Int} {f : Int → Int → Except String Int} {g : Int → Int → Int}
    (h : ∀ a b, f a b = .ok (g a b)) :
    (x >>= fun a => y >>= fun b => f a b) = (x >>= fun a => y >>= fun b => .ok (g a b)) := by
  cases x <;> cases y <;> simp [Gen2.except_ok_bind, Gen2.except_error_bind, h]

theorem ev_slt {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary .slt l r) =
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a < b then 1 else 0)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]
  apply ev_cmp_aux
  intro a b
  by_cases h : a < b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem ev_sle {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary .sle l r) =
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a ≤ b then 1 else 0)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]
  apply ev_cmp_aux
  intro a b
  by_cases h : a ≤ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem ev_sgt {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary .sgt l r) =
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a > b then 1 else 0)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]
  apply ev_cmp_aux
  intro a b
  by_cases h : a > b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem ev_sge {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary .sge l r) =
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a ≥ b then 1 else 0)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]
  apply ev_cmp_aux
  intro a b
  by_cases h : a ≥ b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem ev_eq {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) :
    evalInt E (.binary (.m0 .eq) l r) =
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a = b then 1 else 0)) := by
  simp only [evalInt, hl, hr, Bool.and_self, if_true]
  apply ev_cmp_aux
  intro a b
  by_cases h : a = b
  · subst h; rw [if_pos rfl, beq_self_eq_true]; rfl
  · rw [if_neg h, beq_false_of_ne h]; rfl

theorem ev_ternary {c t e : PExpr} (ht : t.isInt E = true) (he : e.isInt E = true) :
    evalInt E (.ternary c t e) =
      (evalInt E c >>= fun cv => if cv = 0 then evalInt E e else evalInt E t) := by
  simp only [evalInt, ht, he, Bool.and_self, if_true]
  cases evalInt E c with
  | error _ => rfl
  | ok cv =>
    simp only [Gen2.except_ok_bind]
    by_cases h : cv = 0 <;> simp [h]

theorem ev_shr {l r : PExpr} (hl : l.isInt E = true) (hr : r.isInt E = true) {a b : Int}
    (hla : evalInt E l = .ok a) (hrb : evalInt E r = .ok b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    evalInt E (.binary .shr l r) = .ok (a.tdiv ((2 : Int) ^ b.toNat)) := by
  have ha' : ¬ a < 0 := by omega
  have hb' : ¬ b < 0 := by omega
  simp [evalInt, hl, hr, hla, hrb, ha', hb', Gen2.except_ok_bind]

theorem ev_int (v : Int) : evalInt E (.int v) = .ok v := rfl

theorem ev_gv {n : String} : evalInt E (.genvarRef n) =
    match E.vals.lookup n with
    | some v => .ok v
    | none => .error s!"genvar '{n}' outside its loop" := rfl

theorem ev_pr {n : String} {v : Int} (h : E.vals.lookup n = some v) : evalInt E (.paramRef n none) = .ok v :=
  evalInt_paramRef_of h

end ev

section evu

variable {E : IEnv}

/-! Unconditional forms (the INT test left to `simp`). -/

theorem evu_add (l r : PExpr) : evalInt E (.binary (.m0 .add) l r) =
    if l.isInt E && r.isInt E then (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a + b))
    else evalSized E (.binary (.m0 .add) l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]; simp only [evalInt, h, if_true]
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_sub (l r : PExpr) : evalInt E (.binary (.m0 .sub) l r) =
    if l.isInt E && r.isInt E then (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a - b))
    else evalSized E (.binary (.m0 .sub) l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]; simp only [evalInt, h, if_true]
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_mul (l r : PExpr) : evalInt E (.binary .mul l r) =
    if l.isInt E && r.isInt E then (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (a * b))
    else evalSized E (.binary .mul l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]; simp only [evalInt, h, if_true]
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_slt (l r : PExpr) : evalInt E (.binary .slt l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a < b then 1 else 0))
    else evalSized E (.binary .slt l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_slt hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_sle (l r : PExpr) : evalInt E (.binary .sle l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a ≤ b then 1 else 0))
    else evalSized E (.binary .sle l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_sle hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_sgt (l r : PExpr) : evalInt E (.binary .sgt l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a > b then 1 else 0))
    else evalSized E (.binary .sgt l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_sgt hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_sge (l r : PExpr) : evalInt E (.binary .sge l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a ≥ b then 1 else 0))
    else evalSized E (.binary .sge l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_sge hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_eq (l r : PExpr) : evalInt E (.binary (.m0 .eq) l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b => .ok (if a = b then 1 else 0))
    else evalSized E (.binary (.m0 .eq) l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_eq hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_ternary (c t e : PExpr) : evalInt E (.ternary c t e) =
    if t.isInt E && e.isInt E then
      (evalInt E c >>= fun cv => if cv = 0 then evalInt E e else evalInt E t)
    else evalSized E (.ternary c t e) := by
  by_cases h : t.isInt E && e.isInt E
  · rw [if_pos h]
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    exact ev_ternary hl hr
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

theorem evu_pr (n : String) : evalInt E (.paramRef n none) =
    match E.vals.lookup n with
    | some v => .ok v
    | none =>
        match E.nvals.lookup n with
        | some (v, _, _) => .ok v
        | none => .error s!"unbound parameter '{n}'" := rfl

theorem evu_shr (l r : PExpr) : evalInt E (.binary .shr l r) =
    if l.isInt E && r.isInt E then
      (evalInt E l >>= fun a => evalInt E r >>= fun b =>
        if a < 0 then .error "'>>' of a negative constant (width-dependent)"
        else if b < 0 then .error "shift by a negative amount"
        else .ok (a.tdiv ((2 : Int) ^ b.toNat)))
    else evalSized E (.binary .shr l r) := by
  by_cases h : l.isInt E && r.isInt E
  · rw [if_pos h]; simp only [evalInt, h, if_true]
  · rw [if_neg h]; simp only [evalInt, h, if_false, Bool.false_eq_true]

/-! Generate conditions (`evalGenGuard`). -/

theorem evg_slt (l r : PExpr) : evalGenGuard E (.binary .slt l r) =
    (evalGenGuard E l >>= fun a => evalGenGuard E r >>= fun b => .ok (if a < b then 1 else 0)) := by
  simp only [evalGenGuard]
  apply ev_cmp_aux
  intro a b
  by_cases h : a < b
  · rw [if_pos h, decide_eq_true h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

theorem evg_add (l r : PExpr) : evalGenGuard E (.binary (.m0 .add) l r) =
    (evalGenGuard E l >>= fun a => evalGenGuard E r >>= fun b => .ok (a + b)) := by
  simp only [evalGenGuard]

theorem evg_gv (n : String) : evalGenGuard E (.genvarRef n) =
    match E.vals.lookup n with
    | some v => .ok v
    | none => .error s!"genvar '{n}' outside its loop" := rfl

theorem evg_ternary (c t e : PExpr) : evalGenGuard E (.ternary c t e) = evalInt E (.ternary c t e) := rfl

end evu

/-- The simp set that evaluates an INT-class header expression. -/
macro "ev_simp" : tactic => `(tactic| simp [gv, pr, ii, eAdd, eSub, eMul, eSlt, eSle, eSgt, eSge, eEq,
      eTer, eShr, e2N, eR, eU, eMk, eMk', eMinU, ePosT, eFirst, eF, eH, eC, eH0, eLo, eHn, eW,
      evu_add, evu_sub, evu_mul, evu_slt, evu_sle, evu_sgt, evu_sge, evu_eq, evu_ternary, evu_shr, ev_int,
      ev_gv, evu_pr, evg_slt, evg_add, evg_gv, evg_ternary, IEnv.bindVal, List.lookup, Gen2.except_ok_bind])

set_option hygiene false in
/-- `ev_simp` with the parameter lookups `hN`, `hS`, `hNP` of the context. -/
macro "ev_simpE" : tactic => `(tactic| simp [gv, pr, ii, eAdd, eSub, eMul, eSlt, eSle, eSgt, eSge, eEq,
      eTer, eShr, e2N, eR, eU, eMk, eMk', eMinU, ePosT, eFirst, eF, eH, eC, eH0, eLo, eHn, eW,
      evu_add, evu_sub, evu_mul, evu_slt, evu_sle, evu_sgt, evu_sge, evu_eq, evu_ternary, evu_shr, ev_int,
      ev_gv, evu_pr, evg_slt, evg_add, evg_gv, evg_ternary, IEnv.bindVal, List.lookup, Gen2.except_ok_bind, hN, hS, hNP])

/-- Decide every `if` and `min` by `omega` in a fixed region of the column index, then the linear goal. -/
macro "region_close" N:term "," t:term "," u:term "," k:term "," s:term : tactic => `(tactic| (
  rcases kregion $N $t $u $k with h | h | h | h | h | h | h <;>
    rcases Nat.eq_zero_or_pos $s with h0 | h0 <;>
    (repeat (any_goals (first
      | simp (disch := omega) only [if_pos, if_neg, Nat.min_eq_left, Nat.min_eq_right, Gen2.except_ok_bind,
          Except.ok.injEq]
      | split))) <;>
    omega))

/-! ## The environment of the generate nest -/

def NPn (N : Nat) : Nat := if N < 2 then 2 else N

/-- What the header and index expressions read from the environment. -/
structure DEnv (E : IEnv) (N : Nat) : Prop where
  hN : E.vals.lookup "N" = some (N : Int)
  hS : E.vals.lookup "S" = some (nst N : Int)
  hNP : E.vals.lookup "NP" = some (NPn N : Int)

abbrev stEnv (E : IEnv) (s : Nat) : IEnv := E.bindVal "s" (s : Int)
abbrev tEnv (E : IEnv) (s t : Nat) : IEnv := (stEnv E s).bindVal "t" (t : Int)
abbrev uEnv (E : IEnv) (s t u : Nat) : IEnv := (tEnv E s t).bindVal "u" (u : Int)
abbrev cEnv (E : IEnv) (s t u k : Nat) : IEnv := (uEnv E s t u).bindVal "k" (k : Int)
abbrev fEnv (E : IEnv) (s t u k f : Nat) : IEnv := (cEnv E s t u k).bindVal "f" (f : Int)
abbrev hEnv (E : IEnv) (s t u k f h : Nat) : IEnv := (fEnv E s t u k f).bindVal "h" (h : Int)
abbrev ccEnv (E : IEnv) (s t u k f h c : Nat) : IEnv := (hEnv E s t u k f h).bindVal "c" (c : Int)

/-! ## The height table -/

section chain

variable {env : IEnv} {r : Nat}

theorem chainE_isInt : ∀ c j, (chainE j c).isInt env = true
  | 0, _ => rfl
  | c + 1, j => by
    simp only [chainE, eTer, ii, PExpr.isInt, Bool.true_and]
    exact chainE_isInt c (j + 1)

theorem gchE_isInt : ∀ n g, (gchE g n).isInt env = true
  | 0, _ => chainE_isInt 2 48
  | n + 1, g => by
    simp only [gchE, eTer, PExpr.isInt]
    rw [chainE_isInt, gchE_isInt n (g + 1)]
    rfl

theorem chainE_eval (hR : evalInt env eR = .ok (r : Int)) (hRi : eR.isInt env = true) :
    ∀ c j, j ≤ r → r ≤ j + c → evalInt env (chainE j c) = .ok (dd r : Int)
  | 0, j, h1, h2 => by
    obtain rfl : r = j := by omega
    rfl
  | c + 1, j, h1, h2 => by
    simp only [chainE, eTer, eEq, ii]
    rw [ev_ternary rfl (chainE_isInt c (j + 1)), ev_eq hRi rfl, hR]
    simp only [Gen2.except_ok_bind, ev_int]
    by_cases hrj : r = j
    · subst hrj
      simp
    · rw [if_neg (by omega : ¬ ((r : Int) = (j : Int))), if_pos rfl]
      exact chainE_eval hR hRi c (j + 1) (by omega) (by omega)

theorem gchE_eval (hR : evalInt env eR = .ok (r : Int)) (hRi : eR.isInt env = true) :
    ∀ n g, g + n = 6 → 8 * g ≤ r → r ≤ 50 → evalInt env (gchE g n) = .ok (dd r : Int)
  | 0, g, h1, h2, h3 => by
    rw [gchE]
    exact chainE_eval hR hRi 2 48 (by omega) (by omega)
  | n + 1, g, h1, h2, h3 => by
    simp only [gchE, eTer, eSlt, ii]
    rw [ev_ternary (chainE_isInt 7 (8 * g)) (gchE_isInt n (g + 1)), ev_slt hRi rfl, hR]
    simp only [Gen2.except_ok_bind, ev_int]
    have h10 : ¬ ((1 : Int) = 0) := by decide
    by_cases hr : r < 8 * g + 8
    · have hc : (r : Int) < 8 * (g : Int) + 8 := by omega
      simp only [hc, ite_true, h10, ite_false]
      exact chainE_eval hR hRi 7 (8 * g) (by omega) (by omega)
    · have hc : ¬ ((r : Int) < 8 * (g : Int) + 8) := by omega
      simp only [hc, ite_false, ite_true]
      exact gchE_eval hR hRi n (g + 1) (by omega) (by omega) h3

end chain

section heads

variable {E : IEnv} {N : Nat} (hE : DEnv E N)
include hE

set_option hygiene false in
/-- The three parameter lookups, by name, for `ev_simpE`. -/
local macro "dfs" : tactic => `(tactic| (have hN := hE.hN; have hS := hE.hS; have hNP := hE.hNP))

theorem eR_eval {s : Nat} (hs : s < nst N) (w : Int) :
    (evalInt (stEnv E s) eR = .ok ((nst N - 1 - s : Nat) : Int) ∧ eR.isInt (stEnv E s) = true) ∧
      (evalInt ((stEnv E s).bindVal "t" w) eR = .ok ((nst N - 1 - s : Nat) : Int) ∧
        eR.isInt ((stEnv E s).bindVal "t" w) = true) := by
  dfs
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ev_simpE <;> omega

/-- The target of stage `s` is `d(S - 1 - s)`. -/
theorem eT_eval {s : Nat} (hs : s < nst N) (w : Int) :
    evalInt (stEnv E s) eT = .ok (tS N s : Int) ∧
      evalInt ((stEnv E s).bindVal "t" w) eT = .ok (tS N s : Int) := by
  have hle := nst_le N
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := eR_eval hE hs w
  exact ⟨gchE_eval h1 h2 6 0 rfl (by omega) (by omega), gchE_eval h3 h4 6 0 rfl (by omega) (by omega)⟩

theorem eU_eval {s : Nat} (hs : s < nst N) (w : Int) :
    evalInt (tEnv E s (tS N s)) eU = .ok (uS N s : Int) ∧
      evalInt ((tEnv E s (tS N s)).bindVal "u" w) eU = .ok (uS N s : Int) := by
  have h2 := dd_ge_two_all (nst N - 1 - s) (by have := nst_le N; omega)
  dfs
  unfold uS
  constructor <;> ev_simpE <;> (repeat' split) <;> (try simp only [Gen2.except_ok_bind, Except.ok.injEq]) <;>
    (try simp only [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg _)]) <;> unfold tS at * <;> omega

theorem eF_eval {s t u k : Nat} (hst : Stg N s t u) (hk : k < 2 * N) (w : Int) :
    evalInt (cEnv E s t u k) eF = .ok (fF N s t u k : Int) ∧
      evalInt ((cEnv E s t u k).bindVal "f" w) eF = .ok (fF N s t u k : Int) := by
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  dfs
  constructor <;> ev_simpE <;> unfold fF ind mF <;> region_close N, t, u, k, s

theorem eH_eval {s t u k f : Nat} (hst : Stg N s t u) (hk : k < 2 * N) (w : Int) :
    evalInt (fEnv E s t u k f) eH = .ok (hF N s t u k : Int) ∧
      evalInt ((fEnv E s t u k f).bindVal "h" w) eH = .ok (hF N s t u k : Int) := by
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  dfs
  constructor <;> ev_simpE <;> unfold hF ind <;> region_close N, t, u, k, s

theorem eC_eval {s t u k f h : Nat} (hst : Stg N s t u) (hk : k < 2 * N) (w : Int) :
    evalInt (hEnv E s t u k f h) eC = .ok (cF N t u k : Int) ∧
      evalInt ((hEnv E s t u k f h).bindVal "c" w) eC = .ok (cF N t u k : Int) := by
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  dfs
  constructor <;> ev_simpE <;> unfold cF mF' <;> region_close N, t, u, k, s

/-- The keep guard reads the height after the stage. -/
theorem eHn_guard {s t u k f h c i : Nat} (hst : Stg N s t u) (hk : k < 2 * N) :
    evalGenGuard ((ccEnv E s t u k f h c).bindVal "i" (i : Int)) (eSlt (gv "i") eHn) =
      .ok (if i < HnF N t k then 1 else 0) := by
  have := hst.t2; have := hst.tu; have := hst.uN; have := hst.u3; have := hst.first
  dfs
  ev_simpE
  unfold HnF
  region_close N, t, u, k, s

end heads

end Submission

/-! # Instantiation: generate loops, array windows, the process vocabulary -/

namespace Submission

open LeanModels.Sv

/-! ## 1. Generate loops -/

section loops

variable {E : IEnv} {elems : List (String × Nat)} {F : Nat}

/-- A one-iteration loop `for (g = X; g < X + 1; g++)` runs its body once, at `g = X`. -/
theorem expand_one {lab g : String} {init X : PExpr} {rc : Nat} {body : List GenItem} {v : Int}
    {ps : List Process2} (hi : evalInt E init = .ok v)
    (hXi : ∀ w : Int, X.isInt (E.bindVal g w) = true) (hX : ∀ w : Int, evalInt (E.bindVal g w) X = .ok v)
    (hF : 1 < F) (hb : expandList2 (E.bindVal g v) elems F body = .ok ps) :
    (gFor lab g init (eAdd X (ii 1)) rc body).expand2 E elems F = .ok ps := by
  have h := GenItem.expand2_genFor_ascending_flatMap (env := E) (elems := elems) (F := F)
    (label := some lab) (g := g) (initE := init) (e := eAdd X (ii 1)) (rc := some rc) (body := body)
    (i0 := v) (N := v + 1) (f := fun _ => ps) hi
    (fun w => by simp only [eAdd, ii, PExpr.isInt, SymBinOp.intArith, hXi w, Bool.and_self])
    (fun w => by rw [ev_add (hXi w) rfl, hX w]; rfl) (by omega)
    (fun w h1 h2 => by obtain rfl : w = v := by omega
                       exact hb)
  rw [h, show (v + 1 - v).toNat = 1 by omega]
  simp [intRange]

/-- A counted loop `for (g = 0; g < X; g++)` with `X = n`: the bodies at `g = 0 … n - 1`, in order. -/
theorem expand_count {lab g : String} {X : PExpr} {rc : Nat} {body : List GenItem} {n : Nat}
    {f : Nat → List Process2} (hXi : ∀ w : Int, X.isInt (E.bindVal g w) = true)
    (hX : ∀ w : Int, evalInt (E.bindVal g w) X = .ok (n : Int)) (hF : n < F)
    (hb : ∀ j, j < n → expandList2 (E.bindVal g (j : Int)) elems F body = .ok (f j)) :
    (gFor lab g (ii 0) X rc body).expand2 E elems F = .ok ((List.range n).flatMap f) := by
  have h := GenItem.expand2_genFor_ascending_flatMap (env := E) (elems := elems) (F := F)
    (label := some lab) (g := g) (initE := ii 0) (e := X) (rc := some rc) (body := body)
    (i0 := 0) (N := (n : Int)) (f := fun w => f w.toNat) rfl hXi hX (by omega)
    (fun w h1 h2 => by
      obtain ⟨j, rfl⟩ : ∃ j : Nat, w = (j : Int) := ⟨w.toNat, by omega⟩
      rw [Int.toNat_natCast]
      exact hb j (by omega))
  rw [h, intRange_zero, List.flatMap_map]
  simp only [Int.sub_zero, Int.toNat_natCast]

end loops

/-! ## 2. Array windows -/

/-- The flat offset of cell `[s][k][i]` of a `[S:0][2N-1:0][P-1:0]` array. -/
def ofs (N P s k i : Nat) : Nat := s * (2 * N * P) + k * P + i

section windows

variable {E : IEnv}

theorem walk3 {am bm cm : Int} {ie je ke : PExpr} {i j k : Int}
    (ham : 0 ≤ am) (hbm : 0 ≤ bm) (hcm : 0 ≤ cm)
    (hi : evalInt E ie = .ok i) (hi0 : 0 ≤ i) (hia : i ≤ am)
    (hj : evalInt E je = .ok j) (hj0 : 0 ≤ j) (hjb : j ≤ bm)
    (hk : evalInt E ke = .ok k) (hk0 : 0 ≤ k) (hkc : k ≤ cm) :
    walkIndices E [(am, 0), (bm, 0), (cm, 0)] [ie, je, ke] =
      .ok (i * ((dimsStride [(bm, 0), (cm, 0)] : Nat) : Int) +
        (j * ((dimsStride [(cm, 0)] : Nat) : Int) + (k * ((dimsStride [] : Nat) : Int) + 0)), true, []) :=
  walkIndices_desc0_cons ham hi hi0 hia
    (walkIndices_desc0_cons hbm hj hj0 hjb (walkIndices_desc0_cons hcm hk hk0 hkc (walkIndices_nil [])))

theorem stride2 {N P : Nat} (hN : 1 ≤ N) (hP : 1 ≤ P) :
    ((dimsStride [(2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)] : Nat) : Int) = 2 * (N : Int) * (P : Int) := by
  simp only [dimsStride_cons, dimsStride_nil, Nat.mul_one]
  have h1 := dimCount_desc0 (show (0 : Int) ≤ 2 * (N : Int) - 1 by omega)
  have h2 := dimCount_desc0 (show (0 : Int) ≤ (P : Int) - 1 by omega)
  push_cast
  rw [h1, h2]
  simp only [Int.sub_add_cancel]

theorem stride1 {P : Nat} (hP : 1 ≤ P) :
    ((dimsStride [((P : Int) - 1, 0)] : Nat) : Int) = (P : Int) := by
  simp only [dimsStride_cons, dimsStride_nil, Nat.mul_one]
  rw [dimCount_desc0 (show (0 : Int) ≤ (P : Int) - 1 by omega)]
  omega

/-- **A cell `n[s][k][i]` of a `[S:0][2N-1:0][P-1:0]` array**: the one-bit window at `ofs`. -/
theorem win3 {n : String} {N P S s k i : Nat} {ie je ke : PExpr}
    (hd : E.dims.lookup n = some [((S : Int), 0), (2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hi : evalInt E ie = .ok (s : Int)) (hs : s ≤ S)
    (hj : evalInt E je = .ok (k : Int)) (hk : k < 2 * N)
    (hk' : evalInt E ke = .ok (i : Int)) (hi' : i < P) :
    arrayElemWindow E n [ie, je, ke] = .ok ((ofs N P s k i : Nat), 1, true) := by
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walk3 (by omega) (by omega) (by omega) hi (by omega) (by omega) hj (by omega) (by omega) hk'
      (by omega) (by omega)), stride2 hN hP, stride1 hP]
  have e : (s : Int) * (2 * (N : Int) * (P : Int)) + ((k : Int) * (P : Int) +
      ((i : Int) * ((dimsStride [] : Nat) : Int) + 0)) = ((ofs N P s k i : Nat) : Int) := by
    unfold ofs
    simp only [dimsStride_nil]
    push_cast
    omega
  rw [e]
  rfl

theorem tgt3 {elems : List (String × Nat)} {n : String} {N P S s k i : Nat} {ie je ke : PExpr}
    (hd : E.dims.lookup n = some [((S : Int), 0), (2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hi : evalInt E ie = .ok (s : Int)) (hs : s ≤ S)
    (hj : evalInt E je = .ok (k : Int)) (hk : k < 2 * N)
    (hk' : evalInt E ke = .ok (i : Int)) (hi' : i < P) :
    instLhs2 E elems (.arrayElem n [ie, je, ke]) = .ok (.slice n (ofs N P s k i) 1, 1) := by
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange (win3 hd hN hP hi hs hj hk hk' hi'),
    Int.toNat_natCast]

theorem rd3 {elems : List (String × Nat)} {n : String} {N P S s k i : Nat} {ie je ke : PExpr}
    (hd : E.dims.lookup n = some [((S : Int), 0), (2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hi : evalInt E ie = .ok (s : Int)) (hs : s ≤ S)
    (hj : evalInt E je = .ok (k : Int)) (hk : k < 2 * N)
    (hk' : evalInt E ke = .ok (i : Int)) (hi' : i < P) :
    fitExpr2 E elems (some 1) (.arrayElem n [ie, je, ke]) = .slice (.ident n) (ofs N P s k i) 1 := by
  have hw := win3 hd hN hP hi hs hj hk hk' hi'
  rw [fitExpr2_arrayElem_of hw, arrayElemRead_of_inRange hw, Int.toNat_natCast]

/-- The bits `[P-1 : w]` of row `n[s][k]`. -/
theorem part3 {n : String} {N P S s k w : Nat} {ie je a b : PExpr}
    (hd : E.dims.lookup n = some [((S : Int), 0), (2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (hN : 1 ≤ N) (hP : 1 ≤ P)
    (hi : evalInt E ie = .ok (s : Int)) (hs : s ≤ S)
    (hj : evalInt E je = .ok (k : Int)) (hk : k < 2 * N)
    (ha : evalInt E a = .ok ((P : Int) - 1)) (hb : evalInt E b = .ok (w : Int)) (hw : w < P) :
    arrayPartTarget E n [ie, je] .range a b = .ok (.slice n (ofs N P s k w) (P - w), P - w) := by
  have hwalk := walkIndices_desc0_cons (env := E) (ds := [(2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (show (0 : Int) ≤ (S : Int) by omega) hi (by omega) (by omega)
    (walkIndices_desc0_cons (show (0 : Int) ≤ 2 * (N : Int) - 1 by omega) hj (by omega) (by omega)
      (walkIndices_nil (env := E) [((P : Int) - 1, 0)]))
  have hP0 : (0 : Int) ≤ (P : Int) - 1 := by omega
  have hg := arrayPartGeom_range_of (arrayDims_of hd) hwalk ha hb
    (by rw [labelOffset_desc0 hP0, labelOffset_desc0 hP0]; omega)
  have hc := dimCount_desc0 hP0
  rw [arrayPartTarget_of_inRange hg (by rw [labelOffset_desc0 hP0]; omega)
    (by rw [labelOffset_desc0 hP0]; omega)]
  rw [labelOffset_desc0 hP0, labelOffset_desc0 hP0, stride2 hN hP, stride1 hP]
  have e1 : ((s : Int) * (2 * (N : Int) * (P : Int)) + ((k : Int) * (P : Int) + 0) +
      (w : Int) * (((dimsStride [] : Nat)) : Int)).toNat = ofs N P s k w := by
    have e : (s : Int) * (2 * (N : Int) * (P : Int)) + ((k : Int) * (P : Int) + 0) +
        (w : Int) * (((dimsStride [] : Nat)) : Int) = ((ofs N P s k w : Nat) : Int) := by
      unfold ofs
      simp only [dimsStride_nil]
      push_cast
      omega
    rw [e, Int.toNat_natCast]
  have e2 : ((P : Int) - 1 - (w : Int) + 1).toNat * dimsStride [] = P - w := by
    simp only [dimsStride_nil, Nat.mul_one]
    omega
  rw [e1, e2]

/-- The whole row `n[S]` of a `[S:0][2N-1:0][P-1:0]` array. -/
theorem row3 {elems : List (String × Nat)} {n : String} {N P S : Nat} {ie : PExpr}
    (hd : E.dims.lookup n = some [((S : Int), 0), (2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (hN : 1 ≤ N) (hP : 1 ≤ P) (hi : evalInt E ie = .ok (S : Int)) :
    instLhs2 E elems (.arrayElem n [ie]) = .ok (.slice n (S * (2 * N * P)) (2 * N * P), 2 * N * P) := by
  have hwalk := walkIndices_desc0_cons (env := E) (ds := [(2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
    (show (0 : Int) ≤ (S : Int) by omega) hi (by omega) (Int.le_refl _)
    (walkIndices_nil (env := E) [(2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)])
  have hwin := arrayElemWindow_of (arrayDims_of hd) hwalk
  have e : dimsStride [(2 * (N : Int) - 1, 0), ((P : Int) - 1, 0)] = 2 * N * P := by
    have := stride2 hN hP
    have h2 : ((2 * N * P : Nat) : Int) = 2 * (N : Int) * (P : Int) := by push_cast; rfl
    omega
  rw [instLhs2_arrayElem, arrayElemTarget_of_inRange hwin, e]
  have e2 : ((S : Int) * ((2 * N * P : Nat) : Int) + 0).toNat = S * (2 * N * P) := by
    rw [Int.add_zero, ← Int.natCast_mul, Int.toNat_natCast]
  rw [e2]

/-- A cell of a 1-D vector `[M:0]`. -/
theorem win1 {n : String} {M j : Nat} {ie : PExpr}
    (hd : E.dims.lookup n = some [((M : Int), 0)]) (hi : evalInt E ie = .ok (j : Int)) (hj : j ≤ M) :
    arrayElemWindow E n [ie] = .ok ((j : Nat), 1, true) := by
  rw [arrayElemWindow_of (arrayDims_of hd)
    (walkIndices_desc0_cons (show (0 : Int) ≤ (M : Int) by omega) hi (by omega) (by omega)
      (walkIndices_nil (env := E) []))]
  simp

end windows

end Submission

/-! # The instantiated processes, template by template -/

namespace Submission

open LeanModels.Sv

/-! ## 1. The vocabulary -/

abbrev rd (n : String) (o : Nat) : Expr2 := .slice (.ident n) o 1
abbrev wr (n : String) (o : Nat) (e : Expr2) : Process2 := .assign (.slice n o 1) e
abbrev zeros (w : Nat) : Expr2 := .lit (LVec.replicate w .l0)

/-- A cell of `T`, `SM` or `CY`. -/
abbrev cl (N s k i : Nat) : Nat := ofs N (NPn N) s k i
abbrev rT (N s k j : Nat) : Expr2 := rd "T" (cl N s k j)

def ppAndP (N k i : Nat) : Process2 :=
  wr "T" (cl N 0 k i) (.binary .and (rd "a" (k - i - loF N k)) (rd "b" (i + loF N k)))
def ppZeroP (N k i : Nat) : Process2 := wr "T" (cl N 0 k i) (.lit lit0)
def faSmP (N s k q : Nat) : Process2 :=
  wr "SM" (cl N s k q) (.binary .xor (.binary .xor (rT N s k (3 * q)) (rT N s k (3 * q + 1))) (rT N s k (3 * q + 2)))
def faCyP (N s k q : Nat) : Process2 :=
  wr "CY" (cl N s k q) (.binary .or (.binary .and (rT N s k (3 * q)) (rT N s k (3 * q + 1)))
    (.binary .and (rT N s k (3 * q + 2)) (.binary .xor (rT N s k (3 * q)) (rT N s k (3 * q + 1)))))
def haSmP (N s k q : Nat) : Process2 := wr "SM" (cl N s k q) (.binary .xor (rT N s k (3 * q)) (rT N s k (3 * q + 1)))
def haCyP (N s k q : Nat) : Process2 := wr "CY" (cl N s k q) (.binary .and (rT N s k (3 * q)) (rT N s k (3 * q + 1)))
def noSmP (N s k q : Nat) : Process2 := wr "SM" (cl N s k q) (.lit lit0)
def noCyP (N s k q : Nat) : Process2 := wr "CY" (cl N s k q) (.lit lit0)
def smPartP (N s k w : Nat) : Process2 := .assign (.slice "SM" (cl N s k w) (NPn N - w)) (zeros (NPn N - w))
def cyPartP (N s k w : Nat) : Process2 := .assign (.slice "CY" (cl N s k w) (NPn N - w)) (zeros (NPn N - w))
def carP (N s k i : Nat) : Process2 := wr "T" (cl N (s + 1) k i) (rd "CY" (cl N s (k - 1) i))
def sumP (N s k i c : Nat) : Process2 := wr "T" (cl N (s + 1) k i) (rd "SM" (cl N s k (i - c)))
def keepP (N s k i c f h : Nat) : Process2 := wr "T" (cl N (s + 1) k i) (rT N s k (i - c + 2 * f + h))
def zeroP (N s k i : Nat) : Process2 := wr "T" (cl N (s + 1) k i) (.lit lit0)
def tPartP (N s k t : Nat) : Process2 := .assign (.slice "T" (cl N (s + 1) k t) (NPn N - t)) (zeros (NPn N - t))
def finPP (N k : Nat) : Process2 :=
  wr "p" k (.binary .xor (.binary .xor (rT N (nst N) k 0) (rT N (nst N) k 1)) (rd "K" k))
def finKP (N k : Nat) : Process2 :=
  wr "K" (k + 1) (.binary .or (.binary .and (rT N (nst N) k 0) (rT N (nst N) k 1))
    (.binary .and (rd "K" k) (.binary .xor (rT N (nst N) k 0) (rT N (nst N) k 1))))
def smRowP (N : Nat) : Process2 :=
  .assign (.slice "SM" (nst N * (2 * N * NPn N)) (2 * N * NPn N)) (zeros (2 * N * NPn N))
def cyRowP (N : Nat) : Process2 :=
  .assign (.slice "CY" (nst N * (2 * N * NPn N)) (2 * N * NPn N)) (zeros (2 * N * NPn N))
def k0P : Process2 := wr "K" 0 (.lit lit0)

/-! ## 2. What the templates read from their environment -/

structure DIn (E : IEnv) (elems : List (String × Nat)) (N : Nat) : Prop where
  env : DEnv E N
  hT : E.dims.lookup "T" = some [((nst N : Int), 0), (2 * (N : Int) - 1, 0), ((NPn N : Int) - 1, 0)]
  hSM : E.dims.lookup "SM" = some [((nst N : Int), 0), (2 * (N : Int) - 1, 0), ((NPn N : Int) - 1, 0)]
  hCY : E.dims.lookup "CY" = some [((nst N : Int), 0), (2 * (N : Int) - 1, 0), ((NPn N : Int) - 1, 0)]
  hK : E.dims.lookup "K" = some [(2 * (N : Int), 0)]
  ha : elems.lookup "a" = some 1
  hb : elems.lookup "b" = some 1
  hp : elems.lookup "p" = some 1
  hKe : elems.lookup "K" = some 1

theorem NPn_pos (N : Nat) : 1 ≤ NPn N := by unfold NPn; split <;> omega
theorem NPn_ge (N : Nat) : N ≤ NPn N := by unfold NPn; split <;> omega
theorem NPn_two (N : Nat) : 2 ≤ NPn N := by unfold NPn; split <;> omega

/-- The environment of bit `i` of column `k` of the partial products. -/
abbrev pEnv (E : IEnv) (k i : Nat) : IEnv := (E.bindVal "k" (k : Int)).bindVal "i" (i : Int)

section tpl

variable {E : IEnv} {elems : List (String × Nat)} {N : Nat} (hD : DIn E elems N)
include hD

set_option hygiene false in
/-- Evaluate an index expression with the parameter lookups of `hD`, deciding the `if`s by `omega`. -/
local macro "evc" : tactic =>
  `(tactic| (have hN := hD.env.hN; have hS := hD.env.hS; have hNP := hD.env.hNP; ev_simpE
             all_goals (repeat (any_goals (first
               | simp (disch := omega) only [if_pos, if_neg, Except.ok.injEq, Gen2.except_ok_bind]
               | split)))
             all_goals omega))

/-- The column `k`, bit `i` of the partial products. -/
theorem ppAnd_inst {k i : Nat} (hk : k < 2 * N) (hi : i < H0F N k) :
    instProcess2 (pEnv E k i) elems ppAndT = ppAndP N k i := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hPN := NPn_ge N
  have hH : H0F N k ≤ N := by unfold H0F; omega
  have hH' : H0F N k = min (k + 1) (2 * N - 1 - k) := rfl
  have e0 : evalInt (pEnv E k i) (ii 0) = .ok ((0 : Nat) : Int) := rfl
  have ek : evalInt (pEnv E k i) (gv "k") = .ok (k : Int) := rfl
  have ei : evalInt (pEnv E k i) (gv "i") = .ok (i : Int) := rfl
  have ea : evalInt (pEnv E k i) (eSub (eSub (gv "k") (gv "i")) eLo) = .ok ((k - i - loF N k : Nat) : Int) := by
    unfold loF; evc
  have eb : evalInt (pEnv E k i) (eAdd (gv "i") eLo) = .ok ((i + loF N k : Nat) : Int) := by
    unfold loF; evc
  rw [ppAndT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP e0 (Nat.zero_le _)
      ek hk ei (by omega)),
    fitExpr2_binary, instExpr2_and, fitExpr2_bitSel_ident hD.ha ea (by omega),
    fitExpr2_bitSel_ident hD.hb eb (by omega)]
  simp only [Int.toNat_natCast, Nat.mul_one]
  rfl

theorem ppZero_inst {k i : Nat} (hk : k < 2 * N) (hi : i < NPn N) :
    instProcess2 (pEnv E k i) elems ppZeroT = ppZeroP N k i := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have e0 : evalInt (pEnv E k i) (ii 0) = .ok ((0 : Nat) : Int) := rfl
  have ek : evalInt (pEnv E k i) (gv "k") = .ok (k : Int) := rfl
  have ei : evalInt (pEnv E k i) (gv "i") = .ok (i : Int) := rfl
  rw [ppZeroT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP e0 (Nat.zero_le _)
      ek hk ei hi), fitExpr2_lit, if_pos (show lit0.width = 1 from rfl)]
  rfl

/-- The environment of adder slot `q`. -/
abbrev qEnv (E : IEnv) (s t u k f h c q : Nat) : IEnv := (ccEnv E s t u k f h c).bindVal "q" (q : Int)
/-- The environment of bit `i` after a stage. -/
abbrev iEnv (E : IEnv) (s t u k f h c i : Nat) : IEnv := (ccEnv E s t u k f h c).bindVal "i" (i : Int)

omit hD in
theorem fit_fill (env : IEnv) (w : Nat) : fitExpr2 env elems (some w) (.fill .l0) = zeros w := by
  rw [fitExpr2_of_not_rigid w rfl]
  simp only [instExpr2]

section stage

variable {s t u k f h c : Nat} (hs : s < nst N) (hk : k < 2 * N)
include hs hk

section slot

variable {q : Nat}

/-- The index facts of adder slot `q`. -/
structure QFacts (G : IEnv) (s k q : Nat) : Prop where
  es : evalInt G (gv "s") = .ok (s : Int)
  ek : evalInt G (gv "k") = .ok (k : Int)
  eq : evalInt G (gv "q") = .ok (q : Int)
  e0 : evalInt G (eMul (ii 3) (gv "q")) = .ok ((3 * q : Nat) : Int)
  e1 : evalInt G (eAdd (eMul (ii 3) (gv "q")) (ii 1)) = .ok ((3 * q + 1 : Nat) : Int)
  e2 : evalInt G (eAdd (eMul (ii 3) (gv "q")) (ii 2)) = .ok ((3 * q + 2 : Nat) : Int)

omit hD hs hk in
theorem qfacts : QFacts (qEnv E s t u k f h c q) s k q :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem faSm_inst (hq : 3 * q + 2 < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems faSmT = faSmP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  rw [faSmT, instProcess2_assignL _ (tgt3 (n := "SM") (by exact hD.hSM) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq (by omega)),
    fitExpr2_binary, instExpr2_xor, fitExpr2_binary, instExpr2_xor,
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e0 (by omega),
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e1 (by omega),
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e2 (by omega)]
  rfl

theorem faCy_inst (hq : 3 * q + 2 < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems faCyT = faCyP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  have r0 := rd3 (elems := elems) (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e0 (by omega)
  have r1 := rd3 (elems := elems) (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e1 (by omega)
  have r2 := rd3 (elems := elems) (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e2 (by omega)
  rw [faCyT, instProcess2_assignL _ (tgt3 (n := "CY") (by exact hD.hCY) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq (by omega)),
    fitExpr2_binary, instExpr2_or, fitExpr2_binary, instExpr2_and, fitExpr2_binary, instExpr2_and,
    fitExpr2_binary, instExpr2_xor, r0, r1, r2]
  rfl

theorem haSm_inst (hq : 3 * q + 1 < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems haSmT = haSmP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  rw [haSmT, instProcess2_assignL _ (tgt3 (n := "SM") (by exact hD.hSM) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq (by omega)),
    fitExpr2_binary, instExpr2_xor,
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e0 (by omega),
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e1 (by omega)]
  rfl

theorem haCy_inst (hq : 3 * q + 1 < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems haCyT = haCyP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  rw [haCyT, instProcess2_assignL _ (tgt3 (n := "CY") (by exact hD.hCY) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq (by omega)),
    fitExpr2_binary, instExpr2_and,
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e0 (by omega),
    rd3 (n := "T") (by exact hD.hT) hN1 hP Q.es (by omega) Q.ek hk Q.e1 (by omega)]
  rfl

theorem noSm_inst (hq : q < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems noSmT = noSmP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  rw [noSmT, instProcess2_assignL _ (tgt3 (n := "SM") (by exact hD.hSM) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq hq), fitExpr2_lit, if_pos (show lit0.width = 1 from rfl)]
  rfl

theorem noCy_inst (hq : q < NPn N) :
    instProcess2 (qEnv E s t u k f h c q) elems noCyT = noCyP N s k q := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have Q := qfacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (q := q)
  rw [noCyT, instProcess2_assignL _ (tgt3 (n := "CY") (by exact hD.hCY) hN1 hP Q.es (by omega)
      Q.ek hk Q.eq hq), fitExpr2_lit, if_pos (show lit0.width = 1 from rfl)]
  rfl

end slot

theorem smPart_inst (hst : Stg N s t u) :
    instProcess2 (ccEnv E s t u k f h c) elems smPartT = smPartP N s k (u - t + 1) := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hPN := NPn_ge N
  have := hst.t2; have := hst.tu; have := hst.uN
  have es : evalInt (ccEnv E s t u k f h c) (gv "s") = .ok (s : Int) := rfl
  have ek : evalInt (ccEnv E s t u k f h c) (gv "k") = .ok (k : Int) := rfl
  have ea : evalInt (ccEnv E s t u k f h c) (eSub (pr "NP") (ii 1)) = .ok ((NPn N : Int) - 1) := by evc
  have eb0 : evalInt (ccEnv E s t u k f h c) eW = .ok ((u : Int) - (t : Int) + 1) := rfl
  have eb : evalInt (ccEnv E s t u k f h c) eW = .ok ((u - t + 1 : Nat) : Int) := by
    rw [eb0]; congr 1; omega
  rw [smPartT, instProcess2_assignL _ (by
      rw [instLhs2_arrayPart]
      exact part3 hD.hSM hN1 hP es (by omega) ek hk ea eb (by omega)), fit_fill]
  rfl

theorem cyPart_inst (hst : Stg N s t u) :
    instProcess2 (ccEnv E s t u k f h c) elems cyPartT = cyPartP N s k (u - t + 1) := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hPN := NPn_ge N
  have := hst.t2; have := hst.tu; have := hst.uN
  have es : evalInt (ccEnv E s t u k f h c) (gv "s") = .ok (s : Int) := rfl
  have ek : evalInt (ccEnv E s t u k f h c) (gv "k") = .ok (k : Int) := rfl
  have ea : evalInt (ccEnv E s t u k f h c) (eSub (pr "NP") (ii 1)) = .ok ((NPn N : Int) - 1) := by evc
  have eb0 : evalInt (ccEnv E s t u k f h c) eW = .ok ((u : Int) - (t : Int) + 1) := rfl
  have eb : evalInt (ccEnv E s t u k f h c) eW = .ok ((u - t + 1 : Nat) : Int) := by
    rw [eb0]; congr 1; omega
  rw [cyPartT, instProcess2_assignL _ (by
      rw [instLhs2_arrayPart]
      exact part3 hD.hCY hN1 hP es (by omega) ek hk ea eb (by omega)), fit_fill]
  rfl

theorem tPart_inst (hst : Stg N s t u) :
    instProcess2 (ccEnv E s t u k f h c) elems tPartT = tPartP N s k t := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hPN := NPn_ge N
  have := hst.t2; have := hst.tu; have := hst.uN
  have es : evalInt (ccEnv E s t u k f h c) (eAdd (gv "s") (ii 1)) = .ok ((s + 1 : Nat) : Int) := rfl
  have ek : evalInt (ccEnv E s t u k f h c) (gv "k") = .ok (k : Int) := rfl
  have ea : evalInt (ccEnv E s t u k f h c) (eSub (pr "NP") (ii 1)) = .ok ((NPn N : Int) - 1) := by evc
  have eb : evalInt (ccEnv E s t u k f h c) (gv "t") = .ok (t : Int) := rfl
  rw [tPartT, instProcess2_assignL _ (by
      rw [instLhs2_arrayPart]
      exact part3 hD.hT hN1 hP es (by omega) ek hk ea eb (by omega)), fit_fill]
  rfl

section bit

variable {i : Nat}

/-- The index facts of bit `i` after a stage. -/
structure IFacts (G : IEnv) (s k i : Nat) : Prop where
  es : evalInt G (gv "s") = .ok (s : Int)
  es1 : evalInt G (eAdd (gv "s") (ii 1)) = .ok ((s + 1 : Nat) : Int)
  ek : evalInt G (gv "k") = .ok (k : Int)
  ei : evalInt G (gv "i") = .ok (i : Int)

omit hD hs hk in
theorem ifacts : IFacts (iEnv E s t u k f h c i) s k i := ⟨rfl, rfl, rfl, rfl⟩

theorem car_inst (hk1 : 1 ≤ k) (hi : i < NPn N) :
    instProcess2 (iEnv E s t u k f h c i) elems carT = carP N s k i := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have I := ifacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (i := i)
  have ek0 : evalInt (iEnv E s t u k f h c i) (eSub (gv "k") (ii 1)) = .ok ((k : Int) - 1) := rfl
  have ek1 : evalInt (iEnv E s t u k f h c i) (eSub (gv "k") (ii 1)) = .ok ((k - 1 : Nat) : Int) := by
    rw [ek0]; congr 1; omega
  rw [carT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP I.es1 (by omega)
      I.ek hk I.ei hi),
    rd3 (n := "CY") (by exact hD.hCY) hN1 hP I.es (by omega) ek1 (by omega) I.ei hi]
  rfl

theorem sum_inst (hic : c ≤ i) (hi : i < NPn N) :
    instProcess2 (iEnv E s t u k f h c i) elems sumT = sumP N s k i c := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have I := ifacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (i := i)
  have eic0 : evalInt (iEnv E s t u k f h c i) (eSub (gv "i") (gv "c")) = .ok ((i : Int) - (c : Int)) := rfl
  have eic : evalInt (iEnv E s t u k f h c i) (eSub (gv "i") (gv "c")) = .ok ((i - c : Nat) : Int) := by
    rw [eic0]; congr 1; omega
  rw [sumT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP I.es1 (by omega)
      I.ek hk I.ei hi),
    rd3 (n := "SM") (by exact hD.hSM) hN1 hP I.es (by omega) I.ek hk eic (by omega)]
  rfl

theorem keep_inst (hic : c ≤ i) (hi : i < NPn N) (hj : i - c + 2 * f + h < NPn N) :
    instProcess2 (iEnv E s t u k f h c i) elems keepT = keepP N s k i c f h := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have I := ifacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (i := i)
  have ej : evalInt (iEnv E s t u k f h c i)
      (eAdd (eAdd (eSub (gv "i") (gv "c")) (eMul (ii 2) (gv "f"))) (gv "h")) =
        .ok ((i - c + 2 * f + h : Nat) : Int) := by
    have ej0 : evalInt (iEnv E s t u k f h c i)
        (eAdd (eAdd (eSub (gv "i") (gv "c")) (eMul (ii 2) (gv "f"))) (gv "h")) =
          .ok ((i : Int) - (c : Int) + 2 * (f : Int) + (h : Int)) := rfl
    rw [ej0]; congr 1; omega
  rw [keepT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP I.es1 (by omega)
      I.ek hk I.ei hi),
    rd3 (n := "T") (by exact hD.hT) hN1 hP I.es (by omega) I.ek hk ej hj]
  rfl

theorem zero_inst (hi : i < NPn N) :
    instProcess2 (iEnv E s t u k f h c i) elems zeroT = zeroP N s k i := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have I := ifacts (E := E) (s := s) (t := t) (u := u) (k := k) (f := f) (h := h) (c := c) (i := i)
  rw [zeroT, instProcess2_assignL _ (tgt3 (n := "T") (by exact hD.hT) hN1 hP I.es1 (by omega)
      I.ek hk I.ei hi), fitExpr2_lit, if_pos (show lit0.width = 1 from rfl)]
  rfl

end bit

end stage

section fin

variable {k : Nat} (hk : k < 2 * N)
include hk

theorem finP_inst : instProcess2 (E.bindVal "k" (k : Int)) elems finPT = finPP N k := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hP2 := NPn_two N
  have eS : evalInt (E.bindVal "k" (k : Int)) (pr "S") = .ok (nst N : Int) := by evc
  have ek : evalInt (E.bindVal "k" (k : Int)) (gv "k") = .ok (k : Int) := rfl
  have e0 : evalInt (E.bindVal "k" (k : Int)) (ii 0) = .ok ((0 : Nat) : Int) := rfl
  have e1 : evalInt (E.bindVal "k" (k : Int)) (ii 1) = .ok ((1 : Nat) : Int) := rfl
  rw [finPT, instProcess2_assignL _ (instLhs2_bitSel hD.hp ek (by omega)),
    fitExpr2_binary, instExpr2_xor, fitExpr2_binary, instExpr2_xor,
    rd3 (n := "T") (by exact hD.hT) hN1 hP eS (Nat.le_refl _) ek hk e0 (by omega),
    rd3 (n := "T") (by exact hD.hT) hN1 hP eS (Nat.le_refl _) ek hk e1 (by omega),
    fitExpr2_bitSel_ident hD.hKe ek (by omega)]
  simp only [Int.toNat_natCast, Nat.mul_one]
  rfl

theorem finK_inst : instProcess2 (E.bindVal "k" (k : Int)) elems finKT = finKP N k := by
  have hN1 : 1 ≤ N := by omega
  have hP := NPn_pos N
  have hP2 := NPn_two N
  have eS : evalInt (E.bindVal "k" (k : Int)) (pr "S") = .ok (nst N : Int) := by evc
  have ek : evalInt (E.bindVal "k" (k : Int)) (gv "k") = .ok (k : Int) := rfl
  have ek1 : evalInt (E.bindVal "k" (k : Int)) (eAdd (gv "k") (ii 1)) = .ok ((k + 1 : Nat) : Int) := rfl
  have e0 : evalInt (E.bindVal "k" (k : Int)) (ii 0) = .ok ((0 : Nat) : Int) := rfl
  have e1 : evalInt (E.bindVal "k" (k : Int)) (ii 1) = .ok ((1 : Nat) : Int) := rfl
  have r0 := rd3 (elems := elems) (n := "T") (by exact hD.hT) hN1 hP eS (Nat.le_refl _) ek hk e0 (by omega)
  have r1 := rd3 (elems := elems) (n := "T") (by exact hD.hT) hN1 hP eS (Nat.le_refl _) ek hk e1 (by omega)
  rw [finKT, instProcess2_assignL _ (instLhs2_bitSel hD.hKe ek1 (by omega)),
    fitExpr2_binary, instExpr2_or, fitExpr2_binary, instExpr2_and, fitExpr2_binary, instExpr2_and,
    fitExpr2_binary, instExpr2_xor, r0, r1, fitExpr2_bitSel_ident hD.hKe ek (by omega)]
  simp only [Int.toNat_natCast, Nat.mul_one]
  rfl

end fin

theorem smRow_inst (hN1 : 1 ≤ N) : instProcess2 E elems smRowT = smRowP N := by
  have eS : evalInt E (pr "S") = .ok (nst N : Int) := by evc
  rw [smRowT, instProcess2_assignL _ (row3 hD.hSM hN1 (NPn_pos N) eS), fit_fill]
  rfl

theorem cyRow_inst (hN1 : 1 ≤ N) : instProcess2 E elems cyRowT = cyRowP N := by
  have eS : evalInt E (pr "S") = .ok (nst N : Int) := by evc
  rw [cyRowT, instProcess2_assignL _ (row3 hD.hCY hN1 (NPn_pos N) eS), fit_fill]
  rfl

theorem k0_inst : instProcess2 E elems k0T = k0P := by
  have hK : E.dims.lookup "K" = some [(((2 * N : Nat) : Int), 0)] := by rw [hD.hK]; push_cast; rfl
  have e0 : evalInt E (ii 0) = .ok ((0 : Nat) : Int) := rfl
  rw [k0T, instProcess2_assignL _ (by
      rw [instLhs2_arrayElem, arrayElemTarget_of_inRange (win1 hK e0 (Nat.zero_le _))]),
    fitExpr2_lit, if_pos (show lit0.width = 1 from rfl)]
  rfl

end tpl

end Submission

/-! # The generate expansion at symbolic `N` -/

namespace Submission

open LeanModels.Sv

/-! ## 1. The expanded process lists -/

def addCell (N s k f h q : Nat) : List Process2 :=
  if q < f then [faSmP N s k q, faCyP N s k q]
  else if q < f + h then [haSmP N s k q, haCyP N s k q] else [noSmP N s k q, noCyP N s k q]

def bitCell (N s t k c f h i : Nat) : List Process2 :=
  if i < c then [carP N s k i]
  else if i < c + f + h then [sumP N s k i c]
  else if i < HnF N t k then [keepP N s k i c f h] else [zeroP N s k i]

/-- Column `k` of stage `s`: the adder slots, the zero tails of `SM` and `CY`, the bits after the stage, the
zero tail of `T`. -/
def colProcs (N s t u k : Nat) : List Process2 :=
  ((List.range (u - t + 1)).flatMap fun q => addCell N s k (fF N s t u k) (hF N s t u k) q) ++
    ([smPartP N s k (u - t + 1)] ++ ([cyPartP N s k (u - t + 1)] ++
      (((List.range t).flatMap fun i => bitCell N s t k (cF N t u k) (fF N s t u k) (hF N s t u k) i) ++
        [tPartP N s k t])))

def stProcs (N : Nat) : List Process2 :=
  (List.range (nst N)).flatMap fun s => (List.range (2 * N)).flatMap fun k => colProcs N s (tS N s) (uS N s) k

def ppCell (N k i : Nat) : List Process2 := if i < H0F N k then [ppAndP N k i] else [ppZeroP N k i]

def ppProcs (N : Nat) : List Process2 :=
  (List.range (2 * N)).flatMap fun k => (List.range (NPn N)).flatMap fun i => ppCell N k i

def finProcs (N : Nat) : List Process2 := (List.range (2 * N)).flatMap fun k => [finPP N k, finKP N k]

/-! ## 2. The environment facts survive genvar bindings -/

theorem DEnv.bind {E : IEnv} {N : Nat} (h : DEnv E N) (g : String) (h1 : "N" ≠ g) (h2 : "S" ≠ g)
    (h3 : "NP" ≠ g) (v : Int) : DEnv (E.bindVal g v) N where
  hN := by rw [vals_lookup_bindVal_ne v h1]; exact h.hN
  hS := by rw [vals_lookup_bindVal_ne v h2]; exact h.hS
  hNP := by rw [vals_lookup_bindVal_ne v h3]; exact h.hNP

theorem DIn.bind {E : IEnv} {elems : List (String × Nat)} {N : Nat} (h : DIn E elems N) (g : String)
    (h1 : "N" ≠ g) (h2 : "S" ≠ g) (h3 : "NP" ≠ g) (v : Int) : DIn (E.bindVal g v) elems N :=
  ⟨h.env.bind g h1 h2 h3 v, h.hT, h.hSM, h.hCY, h.hK, h.ha, h.hb, h.hp, h.hKe⟩

theorem ev_pN {G : IEnv} {N : Nat} (h : DEnv G N) : evalInt G (pr "N") = .ok (N : Int) :=
  evalInt_paramRef_of h.hN
theorem ev_pS {G : IEnv} {N : Nat} (h : DEnv G N) : evalInt G (pr "S") = .ok (nst N : Int) :=
  evalInt_paramRef_of h.hS
theorem ev_pNP {G : IEnv} {N : Nat} (h : DEnv G N) : evalInt G (pr "NP") = .ok (NPn N : Int) :=
  evalInt_paramRef_of h.hNP
theorem isInt_pN {G : IEnv} {N : Nat} (h : DEnv G N) : (pr "N").isInt G = true := isInt_paramRef_of h.hN
theorem isInt_pS {G : IEnv} {N : Nat} (h : DEnv G N) : (pr "S").isInt G = true := isInt_paramRef_of h.hS
theorem isInt_pNP {G : IEnv} {N : Nat} (h : DEnv G N) : (pr "NP").isInt G = true := isInt_paramRef_of h.hNP

theorem ev_2N {G : IEnv} {N : Nat} (h : DEnv G N) : evalInt G e2N = .ok ((2 * N : Nat) : Int) := by
  rw [e2N, ev_mul rfl (isInt_pN h), ev_int, ev_pN h]
  push_cast
  rfl

theorem isInt_2N {G : IEnv} {N : Nat} (h : DEnv G N) : e2N.isInt G = true := by
  simp only [e2N, eMul, ii, PExpr.isInt, SymBinOp.intArith, h.hN, Option.isSome_some, Bool.and_self]

/-! ## 3. One adder slot, one bit -/

/-- `expandList2` of plain process items. -/
theorem expand_procs {env : IEnv} {elems : List (String × Nat)} {F : Nat} (ps : List PProcess) :
    expandList2 env elems F (ps.map GenItem.process) = .ok (ps.map (instProcess2 env elems)) :=
  expandList2_processes ps

theorem guard_lt {G : IEnv} {a b : String} {x y : Nat} (ha : G.vals.lookup a = some (x : Int))
    (hb : G.vals.lookup b = some (y : Int)) :
    evalGenGuard G (eSlt (gv a) (gv b)) = .ok (if (x : Int) < (y : Int) then 1 else 0) := by
  rw [eSlt, gv, evg_slt, evg_gv, evg_gv, ha, hb]
  rfl

section cells

variable {E : IEnv} {elems : List (String × Nat)} {N F : Nat} (hD : DIn E elems N)
include hD

theorem add_expand {s t u k q : Nat} (hst : Stg N s t u) (hs : s < nst N) (hk : k < 2 * N)
    (c : Nat) (hq : q < u - t + 1) :
    expandList2 (qEnv E s t u k (fF N s t u k) (hF N s t u k) c q) elems F [addGen] =
      .ok (addCell N s k (fF N s t u k) (hF N s t u k) q) := by
  have hr := id_reads hst hk
  have hb := id_Hb_le hst (k := k)
  have hh := id_h_le (N := N) (s := s) (t := t) (u := u) (k := k)
  have hPN := NPn_ge N
  have hw := hst.uN
  have := hst.t2
  apply expandList2_singleton_ok
  rw [addGen]
  have g1 := guard_lt (G := qEnv E s t u k (fF N s t u k) (hF N s t u k) c q) (a := "q") (b := "f") rfl rfl
  by_cases h1 : q < fF N s t u k
  · rw [GenItem.expand2_genIf_of_ne g1 (by rw [if_pos (by omega)]; decide)]
    rw [show [proc faSmT, proc faCyT] = [faSmT, faCyT].map GenItem.process from rfl, expand_procs]
    simp only [List.map_cons, List.map_nil, addCell, if_pos h1]
    rw [faSm_inst hD hs hk (by omega), faCy_inst hD hs hk (by omega)]
  · rw [GenItem.expand2_genIf_of_eq (by rw [g1, if_neg (by omega)])]
    apply expandList2_singleton_ok
    have g2 : evalGenGuard (qEnv E s t u k (fF N s t u k) (hF N s t u k) c q) (eSlt (gv "q") (eAdd (gv "f") (gv "h"))) =
        .ok (if (q : Int) < (fF N s t u k : Int) + (hF N s t u k : Int) then 1 else 0) := by
      rw [eSlt, evg_slt, gv, evg_gv, eAdd, evg_add, gv, evg_gv, evg_gv]
      rfl
    by_cases h2 : q < fF N s t u k + hF N s t u k
    · rw [GenItem.expand2_genIf_of_ne g2 (by rw [if_pos (by omega)]; decide)]
      rw [show [proc haSmT, proc haCyT] = [haSmT, haCyT].map GenItem.process from rfl, expand_procs]
      simp only [List.map_cons, List.map_nil, addCell, if_neg h1, if_pos h2]
      rw [haSm_inst hD hs hk (by omega), haCy_inst hD hs hk (by omega)]
    · rw [GenItem.expand2_genIf_of_eq (by rw [g2, if_neg (by omega)])]
      rw [show [proc noSmT, proc noCyT] = [noSmT, noCyT].map GenItem.process from rfl, expand_procs]
      simp only [List.map_cons, List.map_nil, addCell, if_neg h1, if_neg h2]
      rw [noSm_inst hD hs hk (by omega), noCy_inst hD hs hk (by omega)]

theorem bit_expand {s t u k i : Nat} (hst : Stg N s t u) (hs : s < nst N) (hk : k < 2 * N) (hi : i < t) :
    expandList2 (iEnv E s t u k (fF N s t u k) (hF N s t u k) (cF N t u k) i) elems F [bitGen] =
      .ok (bitCell N s t k (cF N t u k) (fF N s t u k) (hF N s t u k) i) := by
  have hr := id_reads hst hk
  have hb := id_Hb_le hst (k := k)
  have hht := id_height hst hk
  have hc0 := id_carry0 hst
  have hPN := NPn_ge N
  have hw := hst.uN
  have := hst.tu
  apply expandList2_singleton_ok
  rw [bitGen]
  have g1 := guard_lt (G := iEnv E s t u k (fF N s t u k) (hF N s t u k) (cF N t u k) i) (a := "i") (b := "c") rfl rfl
  by_cases h1 : i < cF N t u k
  · rw [GenItem.expand2_genIf_of_ne g1 (by rw [if_pos (by omega)]; decide)]
    rw [show [proc carT] = [carT].map GenItem.process from rfl, expand_procs]
    simp only [List.map_cons, List.map_nil, bitCell, if_pos h1]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    rw [car_inst hD hs hk hk1 (by omega)]
  · rw [GenItem.expand2_genIf_of_eq (by rw [g1, if_neg (by omega)])]
    apply expandList2_singleton_ok
    have g2 : evalGenGuard (iEnv E s t u k (fF N s t u k) (hF N s t u k) (cF N t u k) i)
        (eSlt (gv "i") (eAdd (eAdd (gv "c") (gv "f")) (gv "h"))) =
        .ok (if (i : Int) < (cF N t u k : Int) + (fF N s t u k : Int) + (hF N s t u k : Int) then 1 else 0) := by
      rw [eSlt, evg_slt, gv, evg_gv, eAdd, evg_add, eAdd, evg_add, gv, evg_gv, evg_gv, evg_gv]
      rfl
    by_cases h2 : i < cF N t u k + fF N s t u k + hF N s t u k
    · rw [GenItem.expand2_genIf_of_ne g2 (by rw [if_pos (by omega)]; decide)]
      rw [show [proc sumT] = [sumT].map GenItem.process from rfl, expand_procs]
      simp only [List.map_cons, List.map_nil, bitCell, if_neg h1, if_pos h2]
      rw [sum_inst hD hs hk (by omega) (by omega)]
    · rw [GenItem.expand2_genIf_of_eq (by rw [g2, if_neg (by omega)])]
      apply expandList2_singleton_ok
      have g3 := eHn_guard hD.env (f := fF N s t u k) (h := hF N s t u k) (c := cF N t u k) (i := i) hst hk
      by_cases h3 : i < HnF N t k
      · rw [GenItem.expand2_genIf_of_ne g3 (by rw [if_pos h3]; decide)]
        rw [show [proc keepT] = [keepT].map GenItem.process from rfl, expand_procs]
        simp only [List.map_cons, List.map_nil, bitCell, if_neg h1, if_neg h2, if_pos h3]
        rw [keep_inst hD hs hk (by omega) (by omega) (by omega)]
      · rw [GenItem.expand2_genIf_of_eq (by rw [g3, if_neg h3])]
        rw [show [proc zeroT] = [zeroT].map GenItem.process from rfl, expand_procs]
        simp only [List.map_cons, List.map_nil, bitCell, if_neg h1, if_neg h2, if_neg h3]
        rw [zero_inst hD hs hk (by omega)]

/-! ## 4. One column, one stage -/

theorem col_expand {s t u k : Nat} (hst : Stg N s t u) (hs : s < nst N) (hk : k < 2 * N) (hFu : 2 * N + 60 < F) :
    expandList2 (ccEnv E s t u k (fF N s t u k) (hF N s t u k) (cF N t u k)) elems F colBody =
      .ok (colProcs N s t u k) := by
  have := hst.t2; have := hst.tu; have := hst.uN
  rw [colBody]
  refine expandList2_cons_ok ?_ (expandList2_cons_ok ?_ (expandList2_cons_ok ?_
    (expandList2_cons_ok ?_ (expandList2_singleton_ok ?_))))
  · refine expand_count (n := u - t + 1) (fun _ => rfl) (fun w => ?_) (by omega)
      (fun q hq => add_expand hD hst hs hk _ hq)
    have e0 : evalInt ((ccEnv E s t u k (fF N s t u k) (hF N s t u k) (cF N t u k)).bindVal "q" w) eW =
        .ok ((u : Int) - (t : Int) + 1) := rfl
    rw [e0]
    congr 1
    omega
  · rw [GenItem.expand2_process, smPart_inst hD hs hk hst]
  · rw [GenItem.expand2_process, cyPart_inst hD hs hk hst]
  · exact expand_count (n := t) (fun _ => rfl) (fun _ => rfl) (by omega)
      (fun i hi => bit_expand hD hst hs hk hi)
  · rw [GenItem.expand2_process, tPart_inst hD hs hk hst]

omit hD in
theorem isInt_eF {G : IEnv} (h : DEnv G N) : eF.isInt G = true := by
  simp [eF, ePosT, eMinU, eMk, eFirst, eTer, eSub, eAdd, eMul, eSgt, eSlt, eSle, eEq, e2N, gv, pr, ii,
    PExpr.isInt, SymBinOp.intArith, h.hN]

omit hD in
theorem isInt_eH {G : IEnv} (h : DEnv G N) : eH.isInt G = true := by
  simp [eH, eFirst, eTer, eSge, eSlt, eEq, gv, pr, ii, PExpr.isInt]

omit hD in
theorem isInt_eC {G : IEnv} (h : DEnv G N) : eC.isInt G = true := by
  simp [eC, ePosT, eMinU, eMk', eTer, eSub, eAdd, eMul, eSgt, eSlt, eSle, e2N, gv, pr, ii,
    PExpr.isInt, SymBinOp.intArith, h.hN]

/-- One column of a stage: the one-iteration loops naming `f`, `h`, `c`, then the column's body. -/
theorem colGen_expand {s t u : Nat} (hst : Stg N s t u) (hs : s < nst N) (hFu : 2 * N + 60 < F) :
    colGen.expand2 (uEnv E s t u) elems F = .ok ((List.range (2 * N)).flatMap fun k => colProcs N s t u k) := by
  have hDu : DIn (uEnv E s t u) elems N :=
    ((hD.bind "s" (by decide) (by decide) (by decide) _).bind "t" (by decide) (by decide) (by decide) _).bind "u"
      (by decide) (by decide) (by decide) _
  refine expand_count (n := 2 * N) (fun w => isInt_2N (hDu.env.bind "k" (by decide) (by decide) (by decide) w))
    (fun w => ev_2N (hDu.env.bind "k" (by decide) (by decide) (by decide) w)) (by omega) (fun k hk => ?_)
  apply expandList2_singleton_ok
  have hc := hDu.env.bind "k" (by decide) (by decide) (by decide) (k : Int)
  refine expand_one (eF_eval hD.env hst hk 0).1
    (fun w => isInt_eF (hc.bind "f" (by decide) (by decide) (by decide) w)) (fun w => (eF_eval hD.env hst hk w).2)
    (by omega) ?_
  apply expandList2_singleton_ok
  have hf := hc.bind "f" (by decide) (by decide) (by decide) (fF N s t u k : Int)
  refine expand_one (eH_eval hD.env hst hk 0).1
    (fun w => isInt_eH (hf.bind "h" (by decide) (by decide) (by decide) w)) (fun w => (eH_eval hD.env hst hk w).2)
    (by omega) ?_
  apply expandList2_singleton_ok
  have hh := hf.bind "h" (by decide) (by decide) (by decide) (hF N s t u k : Int)
  refine expand_one (eC_eval hD.env hst hk 0).1
    (fun w => isInt_eC (hh.bind "c" (by decide) (by decide) (by decide) w)) (fun w => (eC_eval hD.env hst hk w).2)
    (by omega) ?_
  exact col_expand hD hst hs hk (by omega)

omit hD in
theorem isInt_eT {G : IEnv} (h : DEnv G N) : eT.isInt G = true := gchE_isInt 6 0

omit hD in
theorem isInt_eU {G : IEnv} (h : DEnv G N) : eU.isInt G = true := by
  simp [eU, eTer, eEq, eAdd, eShr, gv, pr, ii, PExpr.isInt, SymBinOp.intArith, h.hN]

/-- The stages. -/
theorem stGen_expand (hN : N < 2 ^ 30) (hFu : 2 * N + 60 < F) :
    stGen.expand2 E elems F = .ok (stProcs N) := by
  have hle := nst_le N
  refine expand_count (n := nst N) (fun w => isInt_pS (hD.env.bind "s" (by decide) (by decide) (by decide) w))
    (fun w => ev_pS (hD.env.bind "s" (by decide) (by decide) (by decide) w)) (by omega) (fun s hs => ?_)
  apply expandList2_singleton_ok
  have h1 := hD.env.bind "s" (by decide) (by decide) (by decide) (s : Int)
  refine expand_one (eT_eval hD.env hs 0).1 (fun w => isInt_eT (h1.bind "t" (by decide) (by decide) (by decide) w))
    (fun w => (eT_eval hD.env hs w).2) (by omega) ?_
  apply expandList2_singleton_ok
  have h2 := h1.bind "t" (by decide) (by decide) (by decide) (tS N s : Int)
  refine expand_one (eU_eval hD.env hs 0).1 (fun w => isInt_eU (h2.bind "u" (by decide) (by decide) (by decide) w))
    (fun w => (eU_eval hD.env hs w).2) (by omega) ?_
  exact expandList2_singleton_ok (colGen_expand hD (stg_of hN hs) hs hFu)

/-! ## 5. The partial products and the final adder -/

theorem ppGuard {k i : Nat} (hk : k < 2 * N) :
    evalGenGuard (pEnv E k i) (eSlt (gv "i") eH0) = .ok (if i < H0F N k then 1 else 0) := by
  have hN := hD.env.hN; have hS := hD.env.hS; have hNP := hD.env.hNP
  ev_simpE
  unfold H0F
  all_goals (repeat (any_goals (first
    | simp (disch := omega) only [if_pos, if_neg, Except.ok.injEq, Gen2.except_ok_bind, Nat.min_eq_left,
        Nat.min_eq_right]
    | split)))
  all_goals omega

theorem ppGen_expand (hFu : 2 * N + 60 < F) :
    ppGen.expand2 E elems F = .ok (ppProcs N) := by
  refine expand_count (n := 2 * N) (fun w => isInt_2N (hD.env.bind "k" (by decide) (by decide) (by decide) w))
    (fun w => ev_2N (hD.env.bind "k" (by decide) (by decide) (by decide) w)) (by omega) (fun k hk => ?_)
  apply expandList2_singleton_ok
  have h1 := hD.env.bind "k" (by decide) (by decide) (by decide) (k : Int)
  refine expand_count (n := NPn N) (fun w => isInt_pNP (h1.bind "i" (by decide) (by decide) (by decide) w))
    (fun w => ev_pNP (h1.bind "i" (by decide) (by decide) (by decide) w)) (by unfold NPn; split <;> omega)
    (fun i hi => ?_)
  apply expandList2_singleton_ok
  have hH : H0F N k ≤ N := by unfold H0F; omega
  have hPN := NPn_ge N
  by_cases h2 : i < H0F N k
  · rw [GenItem.expand2_genIf_of_ne (ppGuard hD hk) (by rw [if_pos h2]; decide)]
    rw [show [proc ppAndT] = [ppAndT].map GenItem.process from rfl, expand_procs]
    simp only [List.map_cons, List.map_nil, ppCell, if_pos h2]
    rw [ppAnd_inst hD hk h2]
  · rw [GenItem.expand2_genIf_of_eq (by rw [ppGuard hD hk, if_neg h2])]
    rw [show [proc ppZeroT] = [ppZeroT].map GenItem.process from rfl, expand_procs]
    simp only [List.map_cons, List.map_nil, ppCell, if_neg h2]
    rw [ppZero_inst hD hk hi]

theorem finGen_expand (hFu : 2 * N + 60 < F) :
    finGen.expand2 E elems F = .ok (finProcs N) := by
  refine expand_count (n := 2 * N) (fun w => isInt_2N (hD.env.bind "k" (by decide) (by decide) (by decide) w))
    (fun w => ev_2N (hD.env.bind "k" (by decide) (by decide) (by decide) w)) (by omega) (fun k hk => ?_)
  rw [show [proc finPT, proc finKT] = [finPT, finKT].map GenItem.process from rfl, expand_procs]
  simp only [List.map_cons, List.map_nil]
  rw [finP_inst hD hk, finK_inst hD hk]

theorem gens_expand (hN : N < 2 ^ 30) (hFu : 2 * N + 60 < F) :
    expandList2 E elems F [ppGen, stGen, finGen] = .ok (ppProcs N ++ (stProcs N ++ finProcs N)) :=
  expandList2_cons_ok (ppGen_expand hD hFu)
    (expandList2_cons_ok (stGen_expand hD hN hFu) (expandList2_singleton_ok (finGen_expand hD hFu)))

end cells

end Submission

/-! # The envelope's shape, pinned by `rfl` -/

namespace Submission

open LeanModels.Sv

theorem d_generates : design.pdesign.generates = [ppGen, stGen, finGen] := rfl

theorem d_processes : design.pdesign.processes = [smRowT, cyRowT, k0T] := rfl

theorem d_others : design.pdesign.others = [] := rfl

end Submission

/-! # `instantiate2` at symbolic `N` -/

namespace Submission

open LeanModels.Sv

/-! ## 1. The localparams -/

/-- `(N > d(r)) ? 1 : 0`. -/
abbrev gtE (r : Nat) : PExpr := eTer (eSgt (pr "N") (ii (dd r))) (ii 1) (ii 0)

/-- `S = ((N > d0) ? 1 : 0) + … + ((N > d(n)) ? 1 : 0)`, left-nested. -/
def sumE : Nat → PExpr
  | 0 => gtE 0
  | n + 1 => eAdd (sumE n) (gtE (n + 1))

/-- `NP = (N < 2) ? 2 : N`. -/
abbrev npE : PExpr := eTer (eSlt (pr "N") (ii 2)) (ii 2) (pr "N")

abbrev intTy : PType := .packed [{ msb := .int 31, lsb := .int 0 }] (some 32)

def lpS : PLocalParam := { name := "S", expr := sumE 50, resolved? := some 6, type? := some intTy, signed? := none }
def lpNP : PLocalParam := { name := "NP", expr := npE, resolved? := some 16, type? := some intTy, signed? := none }

theorem d_locals : design.pdesign.localParams = [lpS, lpNP] := rfl

theorem sumE_isInt (env : IEnv) : ∀ n, (sumE n).isInt env = true
  | 0 => rfl
  | n + 1 => by
    simp only [sumE, eAdd, PExpr.isInt, SymBinOp.intArith, Bool.true_and]
    rw [sumE_isInt env n]
    rfl

theorem sumE_eval {env : IEnv} {N : Nat} (hN : env.vals.lookup "N" = some (N : Int)) :
    ∀ n, evalInt env (sumE n) = .ok ((nsum (fun r => if dd r < N then 1 else 0) (n + 1) : Nat) : Int) := by
  have hg : ∀ r, evalInt env (gtE r) = .ok (if dd r < N then 1 else 0) := by
    intro r
    rw [gtE, eTer, ev_ternary rfl rfl, eSgt, ev_sgt (isInt_paramRef_of hN) rfl, evalInt_paramRef_of hN]
    simp only [Gen2.except_ok_bind, ii, ev_int]
    by_cases h : dd r < N
    · rw [if_pos (by omega : (N : Int) > (dd r : Int)), if_pos h]
      rfl
    · rw [if_neg (by omega : ¬ ((N : Int) > (dd r : Int))), if_neg h]
      rfl
  intro n
  induction n with
  | zero =>
    rw [sumE, hg]
    simp only [nsum, Nat.zero_add]
    split <;> rfl
  | succ n ih =>
    rw [sumE, eAdd, ev_add (sumE_isInt env n) rfl, ih, hg, nsum_succ (n := n + 1)]
    simp only [Gen2.except_ok_bind]
    split <;> simp

/-! ## 2. The parameter environment -/

def env0 (N : Nat) : IEnv := { vals := [("N", (N : Int))] }

def dScope (N : Nat) : IEnv :=
  { vals := [("NP", (NPn N : Int)), ("S", (nst N : Int)), ("N", (N : Int))],
    pwidths := [("N", 32), ("S", 32), ("NP", 32)] }

def dEnv (N : Nat) : IEnv := { dScope N with dims := dimTable (dScope N) design.pdesign.decls }

/-- An `int` localparam over an INT-class expression binds its mathematical value. -/
theorem bindLocal_int (env : IEnv) (nm : String) (e : PExpr) (r : Option Int) (v : Int)
    (hi : e.isInt env = true) (he : evalInt env e = .ok v) (h32 : env.int32 = false) :
    bindLocal env { name := nm, expr := e, resolved? := r, type? := some intTy, signed? := none } =
      .ok (env.bindVal nm v) := by
  have hd : declConstType env (some intTy) none = .ok none := rfl
  unfold bindLocal
  simp only [hd, evalIntTarget, hi, he, h32, Gen2.except_ok_bind, if_true, if_false, Bool.false_eq_true]

theorem bindLocal_S (N : Nat) :
    bindLocal (env0 N) lpS = .ok ((env0 N).bindVal "S" (nst N : Int)) :=
  bindLocal_int _ _ _ _ _ (sumE_isInt _ 50) (sumE_eval (N := N) rfl 50) rfl

theorem npE_eval (N : Nat) : evalInt ((env0 N).bindVal "S" (nst N : Int)) npE = .ok (NPn N : Int) := by
  rw [npE, eTer, ev_ternary rfl rfl, eSlt, ev_slt rfl rfl]
  show (Except.ok (if (N : Int) < 2 then (1 : Int) else 0) >>= fun cv =>
    if cv = 0 then evalInt _ (pr "N") else evalInt _ (ii 2)) = _
  unfold NPn
  by_cases h2 : N < 2
  · rw [if_pos (by omega : (N : Int) < 2), if_pos h2]
    rfl
  · rw [if_neg (by omega : ¬ ((N : Int) < 2)), if_neg h2]
    rfl

theorem bindLocal_NP (N : Nat) :
    bindLocal ((env0 N).bindVal "S" (nst N : Int)) lpNP =
      .ok (((env0 N).bindVal "S" (nst N : Int)).bindVal "NP" (NPn N : Int)) :=
  bindLocal_int _ _ _ _ _ rfl (npE_eval N) rfl

theorem d_paramEnv (N : Nat) : design.pdesign.paramEnv2 [(N : Int)] = .ok (dEnv N) := by
  have hL : bindLocals (env0 N) design.pdesign.localParams =
      .ok (((env0 N).bindVal "S" (nst N : Int)).bindVal "NP" (NPn N : Int)) := by
    rw [d_locals]
    simp only [bindLocals, bindLocal_S, bindLocal_NP]
  have hP : bindParamsRes {} design.pdesign.params [(N : Int)] = .ok (env0 N) := rfl
  unfold PDesign.paramEnv2
  rw [show bindPackageParams {} design.pdesign.packageParams = .ok {} from rfl, Res.ok_bind,
    show bindPackageEnums {} design.pdesign.enums = .ok {} from rfl, Res.ok_bind, hP, Res.ok_bind, hL,
    Res.ok_bind]
  rfl

/-! ## 3. Declarations, element widths, geometry -/

def dDecls (N : Nat) : List Decl :=
  [{ name := "a", width := N, isInput := true },
   { name := "b", width := N, isInput := true },
   { name := "p", width := 2 * N, isOutput := true },
   { name := "T", width := (nst N + 1) * (2 * N * NPn N) },
   { name := "SM", width := (nst N + 1) * (2 * N * NPn N) },
   { name := "CY", width := (nst N + 1) * (2 * N * NPn N) },
   { name := "K", width := 2 * N + 1 }]

theorem d_decls {N : Nat} (hN : 1 ≤ N) : buildDecls (dEnv N) design.pdesign.decls = .ok (dDecls N) := by
  have hv1 : ((N : Int) - 1).natAbs + 1 = N := by omega
  have hv2 : (2 * (N : Int) - 1).natAbs + 1 = 2 * N := by omega
  have hP := NPn_pos N
  have hv3 : ((NPn N : Int) - 1).natAbs + 1 = NPn N := by omega
  have hv5 : (2 * (N : Int)).natAbs + 1 = 2 * N + 1 := by omega
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt, dEnv, dScope,
    List.lookup, Gen2.except_ok_bind, dDecls, hv1, hv2, hv3, hv5, Nat.mul_assoc]

def dElemsL (N : Nat) : List (String × Nat) :=
  [("a", 1), ("b", 1), ("p", 1), ("T", 2 * N * NPn N), ("SM", 2 * N * NPn N), ("CY", 2 * N * NPn N), ("K", 1)]

theorem d_elems {N : Nat} (hN : 1 ≤ N) : buildElems (dEnv N) design.pdesign.decls = .ok (dElemsL N) := by
  have hv2 : (2 * (N : Int) - 1).natAbs + 1 = 2 * N := by omega
  have hP := NPn_pos N
  have hv3 : ((NPn N : Int) - 1).natAbs + 1 = NPn N := by omega
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, dEnv, dScope,
    List.lookup, dElemsL, Gen2.except_ok_bind, Gen2.except_pure, PType.elemWidth, hv2, hv3]

theorem dims3 (N : Nat) (n : String)
    (hl : design.pdesign.packedDims.lookup n = some
      [{ msb := .paramRef "S" none, lsb := .int 0 },
       { msb := .binary (.m0 .sub) (.binary .mul (.int 2) (.paramRef "N" none)) (.int 1), lsb := .int 0 },
       { msb := .binary (.m0 .sub) (.paramRef "NP" none) (.int 1), lsb := .int 0 }]) :
    (dEnv N).dims.lookup n = some [((nst N : Int), 0), (2 * (N : Int) - 1, 0), ((NPn N : Int) - 1, 0)] := by
  refine PDesign.dimTable_lookup_of (env := dScope N) hl (fun ws => ?_)
  simp [evalDims, evalInt, List.lookup, dScope, Gen2.except_ok_bind]

theorem dEnvOk {N : Nat} (decls : List Decl) : DIn ((dEnv N).withDecls decls) (dElemsL N) N where
  env := ⟨rfl, rfl, rfl⟩
  hT := by simpa using dims3 N "T" rfl
  hSM := by simpa using dims3 N "SM" rfl
  hCY := by simpa using dims3 N "CY" rfl
  hK := by
    have : (dEnv N).dims.lookup "K" = some [(2 * (N : Int), 0)] := by
      refine PDesign.dimTable_lookup_of (env := dScope N)
        (rfl : design.pdesign.packedDims.lookup "K" =
          some [{ msb := .binary .mul (.int 2) (.paramRef "N" none), lsb := .int 0 }]) (fun ws => ?_)
      simp [evalDims, evalInt, List.lookup, dScope, Gen2.except_ok_bind]
    simpa using this
  ha := rfl
  hb := rfl
  hp := rfl
  hKe := rfl

/-! ## 4. The instantiated design -/

def dProcs (N : Nat) : List Process2 :=
  [smRowP N, cyRowP N, k0P] ++ (ppProcs N ++ (stProcs N ++ finProcs N))

def dM (N : Nat) : Design2 :=
  design.pdesign.assemble2 (dEnv N) (dDecls N) (dElemsL N) (ppProcs N ++ (stProcs N ++ finProcs N))

theorem d_instantiate2 {N : Nat} (hN : 1 ≤ N) (h30 : N < 2 ^ 30) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) = .ok (dM N) := by
  have hF : 2 * N + 60 < PDesign.surfaceFuel [(N : Int)] := by
    have : 2 * (N + 2) ≤ (N + 2) * (N + 2) := Nat.mul_le_mul_right _ (by omega)
    have e : PDesign.surfaceFuel [(N : Int)] = (N + 2) * (N + 2) + 64 := by
      simp [PDesign.surfaceFuel]
    rw [e]
    omega
  exact PDesign.instantiate2_of_ok rfl (d_paramEnv N) (d_decls hN) (d_elems hN)
    (by rw [d_generates]; exact gens_expand (dEnvOk (dDecls N)) h30 hF)

theorem dM_processes {N : Nat} (hN : 1 ≤ N) : (dM N).processes.toList = dProcs N := by
  have hD := dEnvOk (N := N) (dDecls N)
  rw [dM, PDesign.assemble2_processes, d_processes, d_others]
  simp only [List.map_cons, List.map_nil, List.append_nil]
  rw [smRow_inst hD hN, cyRow_inst hD hN, k0_inst hD]
  rfl

theorem dM_decls (N : Nat) : (dM N).decls.toList = dDecls N := PDesign.assemble2_decls ..

end Submission

/-! # The comb profile and acyclicity of the instantiated design -/

namespace Submission

open LeanModels.Sv

/-! ## 1. Every process, by kind -/

/-- The schedule numbers of column `k` of stage `s`. -/
abbrev tC (N s : Nat) : Nat := tS N s
abbrev uC (N s : Nat) : Nat := uS N s
abbrev wC (N s : Nat) : Nat := uS N s - tS N s + 1
abbrev fC (N s k : Nat) : Nat := fF N s (tS N s) (uS N s) k
abbrev hC (N s k : Nat) : Nat := hF N s (tS N s) (uS N s) k
abbrev cC (N s k : Nat) : Nat := cF N (tS N s) (uS N s) k
abbrev HnC (N s k : Nat) : Nat := HnF N (tS N s) k

theorem mem_addCell {N s k f h q : Nat} {p : Process2} (hp : p ∈ addCell N s k f h q) :
    (q < f ∧ (p = faSmP N s k q ∨ p = faCyP N s k q)) ∨
      (f ≤ q ∧ q < f + h ∧ (p = haSmP N s k q ∨ p = haCyP N s k q)) ∨
      (f + h ≤ q ∧ (p = noSmP N s k q ∨ p = noCyP N s k q)) := by
  unfold addCell at hp
  split at hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inl ⟨by assumption, hp⟩
  · split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      exact Or.inr (Or.inl ⟨by omega, by assumption, hp⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      exact Or.inr (Or.inr ⟨by omega, hp⟩)

theorem mem_bitCell {N s t k c f h i : Nat} {p : Process2} (hp : p ∈ bitCell N s t k c f h i) :
    (i < c ∧ p = carP N s k i) ∨ (c ≤ i ∧ i < c + f + h ∧ p = sumP N s k i c) ∨
      (c + f + h ≤ i ∧ i < HnF N t k ∧ p = keepP N s k i c f h) ∨
      (c + f + h ≤ i ∧ HnF N t k ≤ i ∧ p = zeroP N s k i) := by
  unfold bitCell at hp
  split at hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    exact Or.inl ⟨by assumption, hp⟩
  · split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      exact Or.inr (Or.inl ⟨by omega, by assumption, hp⟩)
    · split at hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        exact Or.inr (Or.inr (Or.inl ⟨by omega, by assumption, hp⟩))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hp⟩))

/-- **Every process of the multiplier**, by kind. -/
theorem dProcs_forall {N : Nat} {P : Process2 → Prop}
    (h1 : P (smRowP N)) (h2 : P (cyRowP N)) (h3 : P k0P)
    (hpa : ∀ k i, k < 2 * N → i < H0F N k → P (ppAndP N k i))
    (hpz : ∀ k i, k < 2 * N → H0F N k ≤ i → i < NPn N → P (ppZeroP N k i))
    (hfs : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → q < fC N s k → P (faSmP N s k q))
    (hfc : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → q < fC N s k → P (faCyP N s k q))
    (hhs : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → fC N s k ≤ q → q < fC N s k + hC N s k →
      P (haSmP N s k q))
    (hhc : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → fC N s k ≤ q → q < fC N s k + hC N s k →
      P (haCyP N s k q))
    (hns : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → fC N s k + hC N s k ≤ q → P (noSmP N s k q))
    (hnc : ∀ s k q, s < nst N → k < 2 * N → q < wC N s → fC N s k + hC N s k ≤ q → P (noCyP N s k q))
    (hsp : ∀ s k, s < nst N → k < 2 * N → P (smPartP N s k (wC N s)))
    (hcp : ∀ s k, s < nst N → k < 2 * N → P (cyPartP N s k (wC N s)))
    (hcar : ∀ s k i, s < nst N → k < 2 * N → i < tC N s → i < cC N s k → P (carP N s k i))
    (hsum : ∀ s k i, s < nst N → k < 2 * N → i < tC N s → cC N s k ≤ i →
      i < cC N s k + fC N s k + hC N s k → P (sumP N s k i (cC N s k)))
    (hkeep : ∀ s k i, s < nst N → k < 2 * N → i < tC N s → cC N s k + fC N s k + hC N s k ≤ i →
      i < HnC N s k → P (keepP N s k i (cC N s k) (fC N s k) (hC N s k)))
    (hzero : ∀ s k i, s < nst N → k < 2 * N → i < tC N s → HnC N s k ≤ i → P (zeroP N s k i))
    (htp : ∀ s k, s < nst N → k < 2 * N → P (tPartP N s k (tC N s)))
    (hfp : ∀ k, k < 2 * N → P (finPP N k)) (hfk : ∀ k, k < 2 * N → P (finKP N k)) :
    ∀ p ∈ dProcs N, P p := by
  intro p hp
  simp only [dProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl) | hp | hp | hp
  · exact h1
  · exact h2
  · exact h3
  · simp only [ppProcs, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨k, hk, i, hi, hm⟩ := hp
    unfold ppCell at hm
    split at hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      exact hpa k i hk (by assumption)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      exact hpz k i hk (by omega) hi
  · simp only [stProcs, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨s, hs, k, hk, hm⟩ := hp
    simp only [colProcs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hm
    rcases hm with ⟨q, hq, hm⟩ | rfl | rfl | ⟨i, hi, hm⟩ | rfl
    · rcases mem_addCell hm with ⟨h, rfl | rfl⟩ | ⟨h, h', rfl | rfl⟩ | ⟨h, rfl | rfl⟩
      · exact hfs s k q hs hk hq h
      · exact hfc s k q hs hk hq h
      · exact hhs s k q hs hk hq h h'
      · exact hhc s k q hs hk hq h h'
      · exact hns s k q hs hk hq h
      · exact hnc s k q hs hk hq h
    · exact hsp s k hs hk
    · exact hcp s k hs hk
    · rcases mem_bitCell hm with ⟨h, rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, h', rfl⟩ | ⟨h, h', rfl⟩
      · exact hcar s k i hs hk hi h
      · exact hsum s k i hs hk hi h h'
      · exact hkeep s k i hs hk hi h h'
      · exact hzero s k i hs hk hi h'
    · exact htp s k hs hk
  · simp only [finProcs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    obtain ⟨k, hk, rfl | rfl⟩ := hp
    · exact hfp k hk
    · exact hfk k hk

/-- The write window of a process. -/
def winOf : Process2 → Win
  | .assign (.slice n lo w) _ => (n, lo, w)
  | _ => ("", 0, 0)

/-- The right-hand side of an assign. -/
def rhsOf : Process2 → Expr2
  | .assign _ e => e
  | _ => .lit ⟨#[]⟩

/-- The arrays a process may write. -/
abbrev dNames : List String := ["T", "SM", "CY", "K", "p"]

/-- Every process is an assign to a slice of one of the driven arrays. -/
theorem dProcs_shape {N : Nat} : ∀ p ∈ dProcs N,
    ∃ n lo w e, p = .assign (.slice n lo w) e ∧ n ∈ dNames := by
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;>
    exact ⟨_, _, _, _, rfl, by decide⟩

/-! ## 2. The windows -/

/-- Row-major order of the cells: a cell of an earlier row ends where a later row begins. -/
theorem ofs_le {N P s k lo len s' k' lo' : Nat} (hlex : s * (2 * N) + k < s' * (2 * N) + k')
    (hlen : lo + len ≤ P) : ofs N P s k lo + len ≤ ofs N P s' k' lo' := by
  have h := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hlex)
  unfold ofs
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul, Nat.mul_assoc] at h ⊢
  omega

/-- The bands of the arrays: stage `s` of an array is bits `[s·B, (s+1)·B)`, `B = 2N·P`. -/
theorem ofs_div {N P s k i : Nat} (hk : k < 2 * N) (hi : i < P) : ofs N P s k i / (2 * N * P) = s := by
  have h := ofs_le (N := N) (P := P) (s := s) (k := k) (lo := i) (len := P - i) (s' := s + 1) (k' := 0)
    (lo' := 0) (by rw [Nat.add_mul]; omega) (by omega)
  have h0 : ofs N P (s + 1) 0 0 = (s + 1) * (2 * N * P) := by unfold ofs; simp
  apply Nat.div_eq_of_lt_le
  · unfold ofs; omega
  · rw [← h0]; omega

/-! ## 2. The window list -/

def colWs (N s k : Nat) : List Win :=
  ((List.range (wC N s)).flatMap fun q => [("SM", cl N s k q, 1), ("CY", cl N s k q, 1)]) ++
    ([("SM", cl N s k (wC N s), NPn N - wC N s)] ++ ([("CY", cl N s k (wC N s), NPn N - wC N s)] ++
      (((List.range (tC N s)).flatMap fun i => [("T", cl N (s + 1) k i, 1)]) ++
        [("T", cl N (s + 1) k (tC N s), NPn N - tC N s)])))

def ppWs (N : Nat) : List Win :=
  (List.range (2 * N)).flatMap fun k => (List.range (NPn N)).flatMap fun i => [("T", cl N 0 k i, 1)]
def stWs (N : Nat) : List Win := (List.range (nst N)).flatMap fun s => (List.range (2 * N)).flatMap (colWs N s)
def finWs (N : Nat) : List Win := (List.range (2 * N)).flatMap fun k => [("p", k, 1), ("K", k + 1, 1)]
def dWs (N : Nat) : List Win :=
  [("SM", nst N * (2 * N * NPn N), 2 * N * NPn N), ("CY", nst N * (2 * N * NPn N), 2 * N * NPn N), ("K", 0, 1)] ++
    (ppWs N ++ (stWs N ++ finWs N))

theorem addCell_winOf (N s k f h q : Nat) :
    (addCell N s k f h q).map winOf = [("SM", cl N s k q, 1), ("CY", cl N s k q, 1)] := by
  unfold addCell; split
  · rfl
  · split <;> rfl

theorem bitCell_winOf (N s t k c f h i : Nat) :
    (bitCell N s t k c f h i).map winOf = [("T", cl N (s + 1) k i, 1)] := by
  unfold bitCell; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem ppCell_winOf (N k i : Nat) : (ppCell N k i).map winOf = [("T", cl N 0 k i, 1)] := by
  unfold ppCell; split <;> rfl

theorem dProcs_winOf (N : Nat) : (dProcs N).map winOf = dWs N := by
  simp only [dProcs, dWs, ppProcs, stProcs, finProcs, colProcs, colWs, ppWs, stWs, finWs, List.map_append,
    List.map_flatMap, List.map_cons, List.map_nil, addCell_winOf, bitCell_winOf, ppCell_winOf]
  rfl

/-! ## 3. One driver per bit -/

/-- A window of column `k` of stage `s`: `SM`/`CY` row `(s, k)` or `T` row `(s + 1, k)`. -/
def CW (N s k : Nat) (w : Win) : Prop :=
  ∃ lo len, lo + len ≤ NPn N ∧ 0 < len ∧
    (w = ("SM", ofs N (NPn N) s k lo, len) ∨ w = ("CY", ofs N (NPn N) s k lo, len) ∨
      w = ("T", ofs N (NPn N) (s + 1) k lo, len))

theorem mem_colWs {N s k : Nat} (hs : s < nst N) (hN : N < 2 ^ 30) {w : Win} (hw : w ∈ colWs N s k) :
    CW N s k w := by
  have hst := stg_of hN hs
  have := hst.t2; have := hst.tu; have := hst.uN
  have hPN := NPn_ge N
  have e2 : wC N s = uS N s - tS N s + 1 := rfl
  have e3 : tC N s = tS N s := rfl
  simp only [colWs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with ⟨q, hq, rfl | rfl⟩ | rfl | rfl | ⟨i, hi, rfl⟩ | rfl
  · exact ⟨q, 1, by omega, by omega, Or.inl rfl⟩
  · exact ⟨q, 1, by omega, by omega, Or.inr (Or.inl rfl)⟩
  · exact ⟨_, _, by omega, by omega, Or.inl rfl⟩
  · exact ⟨_, _, by omega, by omega, Or.inr (Or.inl rfl)⟩
  · exact ⟨i, 1, by omega, by omega, Or.inr (Or.inr rfl)⟩
  · exact ⟨_, _, by omega, by omega, Or.inr (Or.inr rfl)⟩

/-- Windows of two different columns never overlap. -/
theorem CW_cross {N s k s' k' : Nat} {w w' : Win} (hk : k < 2 * N) (hk' : k' < 2 * N)
    (hlex : s * (2 * N) + k < s' * (2 * N) + k') (h : CW N s k w) (h' : CW N s' k' w') :
    Win.overlaps w w' = false := by
  obtain ⟨lo, len, hl, -, hw⟩ := h
  obtain ⟨lo', len', hl', -, hw'⟩ := h'
  have hlex1 : (s + 1) * (2 * N) + k < (s' + 1) * (2 * N) + k' := by
    rw [Nat.add_mul, Nat.add_mul]; omega
  have e1 := ofs_le (N := N) (P := NPn N) (lo' := lo') hlex hl
  have e2 := ofs_le (N := N) (P := NPn N) (lo' := lo') hlex1 hl
  rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
    rw [Win.overlaps_eq_false] <;> first | (left; decide) | (right; right; omega)

/-- Two cells of one row. -/
theorem row_local {n : String} {N P s k lo len lo' len' : Nat} (h : lo + len ≤ lo' ∨ lo' + len' ≤ lo) :
    Win.overlaps (n, ofs N P s k lo, len) (n, ofs N P s k lo', len') = false := by
  rw [Win.overlaps_eq_false]
  unfold ofs
  omega

/-- Disjoint by name, or two cells of one row. -/
macro "wclose" : tactic => `(tactic| first
  | (rw [Win.overlaps_eq_false]; left; decide)
  | (apply row_local; omega))

theorem pairwise_pair' {a b : Win} (h : Win.overlaps a b = false) :
    [a, b].Pairwise fun a b => Win.overlaps a b = false := by
  simp [h]

theorem colWs_pairwise {N s k : Nat} (hs : s < nst N) (hN : N < 2 ^ 30) :
    (colWs N s k).Pairwise fun a b => Win.overlaps a b = false := by
  have hst := stg_of hN hs
  have := hst.t2; have := hst.tu; have := hst.uN
  have hPN := NPn_ge N
  have e2 : wC N s = uS N s - tS N s + 1 := rfl
  have e3 : tC N s = tS N s := rfl
  unfold colWs
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · apply pairwise_flatMap_range
    · intro q _; exact pairwise_pair' (by wclose)
    · intro q q' hqq' _ a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> wclose
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
    · rw [List.pairwise_append]
      refine ⟨List.pairwise_singleton _ _, ?_, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
        · apply pairwise_flatMap_range
          · intro i _; exact List.pairwise_singleton _ _
          · intro i i' hii' _ a ha b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
            subst ha; subst hb; wclose
        · intro a ha b hb
          simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at ha hb
          obtain ⟨i, hi, rfl⟩ := ha
          subst hb; wclose
      · intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        subst ha
        simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
          or_false] at hb
        rcases hb with ⟨i, hi, rfl⟩ | rfl <;> wclose
    · intro a ha b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | ⟨i, hi, rfl⟩ | rfl <;> wclose
  · intro a ha b hb
    simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at ha
    obtain ⟨q, hq, rfl | rfl⟩ := ha <;>
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hb <;>
    rcases hb with rfl | rfl | ⟨i, hi, rfl⟩ | rfl <;> wclose

theorem dWs_pairwise {N : Nat} (hN1 : 1 ≤ N) (hN : N < 2 ^ 30) :
    (dWs N).Pairwise fun a b => Win.overlaps a b = false := by
  have hle := nst_le N
  have hPN := NPn_ge N
  have hP := NPn_pos N
  have hrow : ofs N (NPn N) (nst N) 0 0 = nst N * (2 * N * NPn N) := by unfold ofs; simp
  unfold dWs
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · simp [Win.overlaps_eq_false]
  · rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- the partial products
      apply pairwise_flatMap_range
      · intro k _
        apply pairwise_flatMap_range
        · intro i _; exact List.pairwise_singleton _ _
        · intro i i' hii' _ a ha b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
          subst ha; subst hb; wclose
      · intro k k' hkk' hk' a ha b hb
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at ha hb
        obtain ⟨i, hi, rfl⟩ := ha
        obtain ⟨i', hi', rfl⟩ := hb
        rw [Win.overlaps_eq_false]; right; right
        exact ofs_le (by omega) (by omega)
    · rw [List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · -- the stages
        apply pairwise_flatMap_range
        · intro s hs
          apply pairwise_flatMap_range
          · intro k _; exact colWs_pairwise hs hN
          · intro k k' hkk' hk' a ha b hb
            exact CW_cross (by omega) hk' (by omega) (mem_colWs hs hN ha) (mem_colWs hs hN hb)
        · intro s s' hss' hs' a ha b hb
          simp only [List.mem_flatMap, List.mem_range] at ha hb
          obtain ⟨k, hk, ha⟩ := ha
          obtain ⟨k', hk', hb⟩ := hb
          have hlex : s * (2 * N) + k < s' * (2 * N) + k' := by
            have := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt hss')
            rw [Nat.succ_eq_add_one, Nat.add_mul] at this
            omega
          exact CW_cross hk hk' hlex (mem_colWs (by omega) hN ha) (mem_colWs hs' hN hb)
      · -- the final adder
        apply pairwise_flatMap_range
        · intro k _; exact pairwise_pair' (by rw [Win.overlaps_eq_false]; left; decide)
        · intro k k' hkk' _ a ha b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rw [Win.overlaps_eq_false] <;>
            first | (left; decide) | omega
      · intro a ha b hb
        simp only [stWs, List.mem_flatMap, List.mem_range] at ha
        obtain ⟨s, hs, k, hk, ha⟩ := ha
        obtain ⟨lo, len, -, -, hw⟩ := mem_colWs hs hN ha
        simp only [finWs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hb
        obtain ⟨k', hk', rfl | rfl⟩ := hb <;> rcases hw with rfl | rfl | rfl <;>
          (rw [Win.overlaps_eq_false]; left; decide)
    · intro a ha b hb
      simp only [ppWs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at ha
      obtain ⟨k, hk, i, hi, rfl⟩ := ha
      simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · simp only [stWs, List.mem_flatMap, List.mem_range] at hb
        obtain ⟨s, hs, k', hk', hb⟩ := hb
        obtain ⟨lo, len, hl, -, hw⟩ := mem_colWs hs hN hb
        rcases hw with rfl | rfl | rfl
        · rw [Win.overlaps_eq_false]; left; decide
        · rw [Win.overlaps_eq_false]; left; decide
        · rw [Win.overlaps_eq_false]; right; right
          exact ofs_le (by rw [Nat.add_mul]; omega) (by omega)
      · simp only [finWs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hb
        obtain ⟨k', hk', rfl | rfl⟩ := hb <;> (rw [Win.overlaps_eq_false]; left; decide)
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [List.mem_append] at hb
    rcases hb with hb | hb | hb
    · simp only [ppWs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hb
      obtain ⟨k, hk, i, hi, rfl⟩ := hb
      rcases ha with rfl | rfl | rfl <;> (rw [Win.overlaps_eq_false]; left; decide)
    · simp only [stWs, List.mem_flatMap, List.mem_range] at hb
      obtain ⟨s, hs, k, hk, hb⟩ := hb
      obtain ⟨lo, len, hl, -, hw⟩ := mem_colWs hs hN hb
      have e := ofs_le (N := N) (P := NPn N) (s := s) (k := k) (lo := lo) (len := len) (s' := nst N) (k' := 0)
        (lo' := 0) (by
          have := Nat.mul_le_mul_right (2 * N) (Nat.succ_le_of_lt hs)
          rw [Nat.succ_eq_add_one, Nat.add_mul] at this
          omega) hl
      rw [hrow] at e
      rcases ha with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl <;> rw [Win.overlaps_eq_false] <;>
        first | (left; decide) | (right; left; exact e)
    · simp only [finWs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hb
      obtain ⟨k, hk, rfl | rfl⟩ := hb <;> rcases ha with rfl | rfl | rfl <;> rw [Win.overlaps_eq_false] <;>
        first | (left; decide) | omega

/-! ## 4. The comb profile -/

/-- The sizes of a stage against the column height `NP`. -/
theorem stg_bounds {N s : Nat} (h30 : N < 2 ^ 30) (hs : s < nst N) :
    tC N s < NPn N ∧ wC N s < NPn N ∧ tC N s = tS N s ∧ wC N s = uS N s - tS N s + 1 := by
  have hst := stg_of h30 hs
  have := hst.t2; have := hst.tu; have := hst.uN
  have := NPn_ge N
  exact ⟨by show tS N s < NPn N; omega, by show uS N s - tS N s + 1 < NPn N; omega, rfl, rfl⟩

section comb

variable {N : Nat}

theorem dM_getElem?_of_mem (hN1 : 1 ≤ N) {p : Process2} (h : p ∈ dProcs N) :
    ∃ k : Nat, (dM N).processes[k]? = some p := by
  rw [← dM_processes hN1, List.mem_iff_getElem?] at h
  obtain ⟨k, hk⟩ := h
  rw [Array.getElem?_toList] at hk
  exact ⟨k, hk⟩

theorem dM_mem_of_getElem? (hN1 : 1 ≤ N) {k : Nat} {p : Process2} (h : (dM N).processes[k]? = some p) :
    p ∈ dProcs N := by
  rw [← dM_processes hN1, List.mem_iff_getElem?]
  exact ⟨k, by rw [Array.getElem?_toList]; exact h⟩

theorem dProcs_wins : ∀ p ∈ dProcs N, ∀ t e, p = .assign t e →
    t.windows? (dM N) = some [winOf p] ∧ t.wins (dM N) = [winOf p] := by
  intro p hp t e hpe
  obtain ⟨n, lo, w, e', rfl, -⟩ := dProcs_shape p hp
  simp only [Process2.assign.injEq] at hpe
  obtain ⟨rfl, -⟩ := hpe
  exact ⟨rfl, by simp [winOf, Lhs2.wins, Lhs2.windows?, Lhs2.window?]⟩

theorem dM_writes (hN1 : 1 ≤ N) {j : Nat} {w : Win} (h : (dM N).Writes j w) :
    ∃ p, (dM N).processes[j]? = some p ∧ p ∈ dProcs N ∧ w = winOf p := by
  obtain ⟨t, e, hp, hw⟩ := h
  have hm := dM_mem_of_getElem? hN1 hp
  obtain ⟨-, hws⟩ := dProcs_wins _ hm t e rfl
  rw [hws, List.mem_singleton] at hw
  exact ⟨_, hp, hm, hw⟩

theorem dProcs_pairwise (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) :
    (dProcs N).Pairwise fun p q => Win.overlaps (winOf p) (winOf q) = false := by
  have h := dWs_pairwise hN1 h30
  rw [← dProcs_winOf, List.pairwise_map] at h
  exact h

theorem dM_disjoint (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) :
    ∀ i j wi wj, i ≠ j → (dM N).Writes i wi → (dM N).Writes j wj → Win.overlaps wi wj = false := by
  intro i j wi wj hij hi hj
  obtain ⟨p, hp, -, rfl⟩ := dM_writes hN1 hi
  obtain ⟨q, hq, -, rfl⟩ := dM_writes hN1 hj
  have hpw := dProcs_pairwise hN1 h30
  rw [← dM_processes hN1, List.pairwise_iff_getElem] at hpw
  rw [← Array.getElem?_toList, List.getElem?_eq_some_iff] at hp hq
  obtain ⟨hil, hp⟩ := hp
  obtain ⟨hjl, hq⟩ := hq
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have := hpw i j hil hjl h
    rw [hp, hq] at this
    exact this
  · have := hpw j i hjl hil h
    rw [hp, hq] at this
    rw [Win.overlaps_comm]
    exact this

theorem dM_declWidth (n : String) :
    (dM N).declWidth n = ((dDecls N).find? fun dc => dc.name == n).map Decl.width := by
  simp only [Design2.declWidth, dM_decls]

/-- A cell window ends inside its array. -/
theorem cell_le {s k i len : Nat} (hs : s ≤ nst N) (hk : k < 2 * N) (h : i + len ≤ NPn N) :
    ofs N (NPn N) s k i + len ≤ (nst N + 1) * (2 * N * NPn N) := by
  have e := ofs_le (N := N) (P := NPn N) (s := s) (k := k) (lo := i) (len := len) (s' := nst N + 1) (k' := 0)
    (lo' := 0) (by rw [Nat.add_mul]; have := Nat.mul_le_mul_right (2 * N) hs; omega) h
  have h0 : ofs N (NPn N) (nst N + 1) 0 0 = (nst N + 1) * (2 * N * NPn N) := by unfold ofs; simp
  omega

theorem dProcs_inWidth (h30 : N < 2 ^ 30) : ∀ p ∈ dProcs N,
    ∃ dw, (dM N).declWidth (winOf p).1 = some dw ∧ (winOf p).2.1 + (winOf p).2.2 ≤ dw := by
  have hPN := NPn_ge N
  have hP := NPn_pos N
  have wT : (dM N).declWidth "T" = some ((nst N + 1) * (2 * N * NPn N)) := by simp [dM_declWidth, dDecls]
  have wSM : (dM N).declWidth "SM" = some ((nst N + 1) * (2 * N * NPn N)) := by simp [dM_declWidth, dDecls]
  have wCY : (dM N).declWidth "CY" = some ((nst N + 1) * (2 * N * NPn N)) := by simp [dM_declWidth, dDecls]
  have wK : (dM N).declWidth "K" = some (2 * N + 1) := by simp [dM_declWidth, dDecls]
  have wp : (dM N).declWidth "p" = some (2 * N) := by simp [dM_declWidth, dDecls]
  have hrow : nst N * (2 * N * NPn N) + 2 * N * NPn N = (nst N + 1) * (2 * N * NPn N) := by
    rw [Nat.add_mul, Nat.one_mul]
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨_, wSM, by simp only [winOf, smRowP]; omega⟩
  · exact ⟨_, wCY, by simp only [winOf, cyRowP]; omega⟩
  · exact ⟨_, wK, by simp only [winOf, k0P]; omega⟩
  · intro k i hk hi
    have : H0F N k ≤ N := by unfold H0F; omega
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) 0 k i + 1 ≤ _
    exact cell_le (Nat.zero_le _) hk (by omega)
  · intro k i hk _ hi
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) 0 k i + 1 ≤ _
    exact cell_le (Nat.zero_le _) hk (by omega)
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨_, wSM, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨_, wCY, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k q hs hk hq _ _
    have hb := stg_bounds h30 hs
    refine ⟨_, wSM, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k q hs hk hq _ _
    have hb := stg_bounds h30 hs
    refine ⟨_, wCY, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨_, wSM, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨_, wCY, ?_⟩
    show ofs N (NPn N) s k q + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨_, wSM, ?_⟩
    show ofs N (NPn N) s k (wC N s) + (NPn N - wC N s) ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨_, wCY, ?_⟩
    show ofs N (NPn N) s k (wC N s) + (NPn N - wC N s) ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k i hs hk hi _
    have hb := stg_bounds h30 hs
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) (s + 1) k i + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k i hs hk hi _ _
    have hb := stg_bounds h30 hs
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) (s + 1) k i + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k i hs hk hi _ _
    have hb := stg_bounds h30 hs
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) (s + 1) k i + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k i hs hk hi _
    have hb := stg_bounds h30 hs
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) (s + 1) k i + 1 ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨_, wT, ?_⟩
    show ofs N (NPn N) (s + 1) k (tC N s) + (NPn N - tC N s) ≤ _
    exact cell_le (by omega) hk (by omega)
  · intro k hk
    exact ⟨_, wp, by simp only [winOf, finPP]; omega⟩
  · intro k hk
    exact ⟨_, wK, by simp only [winOf, finKP]; omega⟩

theorem dProcs_rhsFree : ∀ p ∈ dProcs N, (rhsOf p).unsupportedFree = true := by
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

/-- Every declared name. -/
abbrev dAll : List String := ["a", "b", "p", "T", "SM", "CY", "K"]

theorem dProcs_rhsDeclared : ∀ p ∈ dProcs N, ((rhsOf p).idents.all fun x => x ∈ dAll) = true := by
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> intros <;> rfl

theorem dProcs_winForm : ∀ p ∈ dProcs N, ∃ n lo w, winOf p = (n, lo, w) ∧ n ∈ dNames := by
  intro p hp
  obtain ⟨n, lo, w, e, rfl, hn⟩ := dProcs_shape p hp
  exact ⟨n, lo, w, rfl, hn⟩

theorem dM_inputNames : (dM N).inputNames.toList = ["a", "b"] := by
  simp [Design2.inputNames, dM_decls, dDecls]

theorem dM_comb (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : CombDesign (dM N) where
  nodup := by
    rw [dM_decls]
    simp only [dDecls, List.map_cons, List.map_nil]
    decide
  assign := by
    intro j p hp
    have hm := dM_mem_of_getElem? hN1 hp
    obtain ⟨n, lo, w, e, rfl, -⟩ := dProcs_shape p hm
    exact ⟨_, _, _, rfl, (dProcs_wins _ hm _ _ rfl).1⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨p, -, hm, hw⟩ := dM_writes hN1 h
    obtain ⟨dw, hdw, hle⟩ := dProcs_inWidth h30 p hm
    rw [← hw] at hdw hle
    exact ⟨dw, hdw, hle⟩
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨p, -, hm, hw⟩ := dM_writes hN1 h
    obtain ⟨n', lo', w', hwf, hn'⟩ := dProcs_winForm p hm
    rw [hwf] at hw
    simp only [Prod.mk.injEq] at hw
    obtain ⟨rfl, -, -⟩ := hw
    rw [dM_inputNames]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn' ⊢
    rcases hn' with rfl | rfl | rfl | rfl | rfl <;> decide
  disjoint := dM_disjoint hN1 h30
  selfDisjoint := by
    intro j t e hp
    obtain ⟨n, lo, w, e', h, -⟩ := dProcs_shape _ (dM_mem_of_getElem? hN1 hp)
    simp only [Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    exact dProcs_rhsFree _ (dM_mem_of_getElem? hN1 hp)
  rhsDeclared := by
    intro j t e hp x hx
    have h := List.all_eq_true.mp (dProcs_rhsDeclared _ (dM_mem_of_getElem? hN1 hp)) x hx
    rw [dM_decls]
    simpa [dAll, dDecls] using h
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [dM_decls] at hdc
    simp [dDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [dM_decls] at hdc
    simp [dDecls] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## 5. Acyclicity: the stage is the rank -/

abbrev BB (N : Nat) : Nat := 2 * N * NPn N


/-- The rank of a window: `T` of band `s` ranks `2s`, `SM`/`CY` of band `s` rank `2s + 1`, `K[j]` ranks
`2S + 2 + j`, the outputs last. -/
def rkW (N : Nat) (w : Win) : Nat :=
  if w.1 = "T" then 2 * (w.2.1 / BB N) else if w.1 = "SM" ∨ w.1 = "CY" then 2 * (w.2.1 / BB N) + 1
  else if w.1 = "K" then 2 * nst N + 2 + w.2.1 else 2 * nst N + 2 * N + 4

theorem BB_pos (hN1 : 1 ≤ N) : 0 < BB N := by
  have := NPn_pos N
  show 0 < 2 * N * NPn N
  exact Nat.mul_pos (by omega) this

/-- A cell window lies in one band. -/
theorem cell_band {s k lo len : Nat} (hk : k < 2 * N) (h : lo + len ≤ NPn N) (hlo : lo < NPn N) :
    ofs N (NPn N) s k lo / BB N = s ∧ ofs N (NPn N) s k lo + len ≤ (s + 1) * BB N := by
  refine ⟨ofs_div hk hlo, ?_⟩
  have e := ofs_le (N := N) (P := NPn N) (s := s) (k := k) (lo := lo) (len := len) (s' := s + 1) (k' := 0)
    (lo' := 0) (by rw [Nat.add_mul]; omega) h
  have h0 : ofs N (NPn N) (s + 1) 0 0 = (s + 1) * (2 * N * NPn N) := by unfold ofs; simp
  show ofs N (NPn N) s k lo + len ≤ (s + 1) * (2 * N * NPn N)
  omega

/-- The windows of the arrays lie in bands; the carries of the final adder are single bits. -/
theorem dProcs_band (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : ∀ q ∈ dProcs N,
    ((winOf q).1 = "T" ∨ (winOf q).1 = "SM" ∨ (winOf q).1 = "CY" →
      (winOf q).2.1 + (winOf q).2.2 ≤ ((winOf q).2.1 / BB N + 1) * BB N) ∧
    ((winOf q).1 = "K" → (winOf q).2.2 = 1) := by
  have hPN := NPn_ge N
  have hB := BB_pos hN1
  have hrow : nst N * BB N / BB N = nst N := Nat.mul_div_cancel _ hB
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨fun _ => ?_, fun h => by simp [winOf, smRowP] at h⟩
    show nst N * BB N + BB N ≤ (nst N * BB N / BB N + 1) * BB N
    rw [hrow, Nat.add_mul, Nat.one_mul]
    exact Nat.le_refl _
  · refine ⟨fun _ => ?_, fun h => by simp [winOf, cyRowP] at h⟩
    show nst N * BB N + BB N ≤ (nst N * BB N / BB N + 1) * BB N
    rw [hrow, Nat.add_mul, Nat.one_mul]
    exact Nat.le_refl _
  · exact ⟨fun h => by simp [winOf, k0P] at h, fun _ => rfl⟩
  · intro k i hk hi
    have : H0F N k ≤ N := by unfold H0F; omega
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := 0) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) 0 k i + 1 ≤ (ofs N (NPn N) 0 k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro k i hk _ hi
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := 0) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) 0 k i + 1 ≤ (ofs N (NPn N) 0 k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _ _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _ _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k q hs hk hq _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := q) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k q + 1 ≤ (ofs N (NPn N) s k q / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := (wC N s)) (len := (NPn N - wC N s)) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k (wC N s) + (NPn N - wC N s) ≤ (ofs N (NPn N) s k (wC N s) / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := s) (k := k) (lo := (wC N s)) (len := (NPn N - wC N s)) (by omega) (by omega) (by omega)
    show ofs N (NPn N) s k (wC N s) + (NPn N - wC N s) ≤ (ofs N (NPn N) s k (wC N s) / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k i hs hk hi _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := (s + 1)) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) (s + 1) k i + 1 ≤ (ofs N (NPn N) (s + 1) k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k i hs hk hi _ _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := (s + 1)) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) (s + 1) k i + 1 ≤ (ofs N (NPn N) (s + 1) k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k i hs hk hi _ _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := (s + 1)) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) (s + 1) k i + 1 ≤ (ofs N (NPn N) (s + 1) k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k i hs hk hi _
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := (s + 1)) (k := k) (lo := i) (len := 1) (by omega) (by omega) (by omega)
    show ofs N (NPn N) (s + 1) k i + 1 ≤ (ofs N (NPn N) (s + 1) k i / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro s k hs hk
    have hb := stg_bounds h30 hs
    refine ⟨fun _ => ?_, fun h => by simp [winOf, ppAndP, ppZeroP, faSmP, faCyP, haSmP, haCyP, noSmP, noCyP, smPartP, cyPartP, carP, sumP, keepP, zeroP, tPartP] at h⟩
    obtain ⟨h1, h2⟩ := cell_band (s := (s + 1)) (k := k) (lo := (tC N s)) (len := (NPn N - tC N s)) (by omega) (by omega) (by omega)
    show ofs N (NPn N) (s + 1) k (tC N s) + (NPn N - tC N s) ≤ (ofs N (NPn N) (s + 1) k (tC N s) / BB N + 1) * BB N
    rw [h1]; exact h2
  · intro k hk
    exact ⟨fun h => by simp [winOf, finPP] at h, fun h => by simp [winOf, finPP] at h⟩
  · intro k hk
    exact ⟨fun h => by simp [winOf, finKP] at h, fun _ => rfl⟩

theorem rk_cell {n : String} {s k lo len : Nat} (hk : k < 2 * N) (hlo : lo < NPn N) :
    rkW N (n, ofs N (NPn N) s k lo, len) =
      if n = "T" then 2 * s else if n = "SM" ∨ n = "CY" then 2 * s + 1
      else if n = "K" then 2 * nst N + 2 + ofs N (NPn N) s k lo else 2 * nst N + 2 * N + 4 := by
  unfold rkW
  simp only [ofs_div hk hlo]

/-- **What a read sees**: a read of bit `o` of a driven array is written by a process of the rank of `o`'s band. -/
theorem read_rank (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) {q : Process2} (hq : q ∈ dProcs N) {n : String} {o : Nat}
    (hov : (ReadWin.win n o 1).overlaps (winOf q) = true) :
    n ∈ dNames ∧ (n = "T" → rkW N (winOf q) = 2 * (o / BB N)) ∧
      (n = "SM" ∨ n = "CY" → rkW N (winOf q) = 2 * (o / BB N) + 1) ∧
      (n = "K" → rkW N (winOf q) = 2 * nst N + 2 + o) := by
  obtain ⟨n', lo', w', hwf, hn'⟩ := dProcs_winForm q hq
  obtain ⟨hb1, hb2⟩ := dProcs_band hN1 h30 q hq
  rw [hwf] at hov hb1 hb2
  rw [ReadWin.overlaps_win_one] at hov
  obtain ⟨rfl, h1, h2⟩ := hov
  have hB := BB_pos hN1 (N := N)
  have hdiv : n = "T" ∨ n = "SM" ∨ n = "CY" → o / BB N = lo' / BB N := by
    intro hn
    have hb := hb1 hn
    simp only at hb
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_trans (Nat.div_mul_le_self lo' (BB N)) h1
    · omega
  refine ⟨hn', fun hn => ?_, fun hn => ?_, fun hn => ?_⟩
  · subst hn
    rw [hwf, rkW, if_pos rfl, hdiv (Or.inl rfl)]
  · rw [hwf, rkW, if_neg (by rcases hn with rfl | rfl <;> simp), if_pos hn, hdiv (Or.inr hn)]
  · subst hn
    have := hb2 rfl
    simp only at this
    subst this
    rw [hwf, rkW, if_neg (by simp), if_neg (by simp), if_pos rfl]
    simp only
    omega

theorem dProcs_reads (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : ∀ p ∈ dProcs N, ∀ r ∈ (rhsOf p).reads,
    ∀ q ∈ dProcs N, r.overlaps (winOf q) = true → rkW N (winOf q) < rkW N (winOf p) := by
  have hPN := NPn_ge N
  have hP2 := NPn_two N
  have hB := BB_pos hN1 (N := N)
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro r hr
    simp [rhsOf, smRowP, Expr2.reads] at hr
  · intro r hr
    simp [rhsOf, cyRowP, Expr2.reads] at hr
  · intro r hr
    simp [rhsOf, k0P, Expr2.reads] at hr
  · intro k i hk hi r hr q' hq' hov
    simp [rhsOf, ppAndP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;> (have := (read_rank hN1 h30 hq' hov).1; simp at this)
  · intro k i hk _ hi r hr
    simp [rhsOf, ppZeroP, Expr2.reads] at hr
  · intro s k q hs hk hq hf r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, faSmP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("SM", ofs N (NPn N) s k q, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k q hs hk hq hf r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, faCyP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("CY", ofs N (NPn N) s k q, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k q hs hk hq hf hfh r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, haSmP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("SM", ofs N (NPn N) s k q, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k q hs hk hq hf hfh r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, haCyP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("CY", ofs N (NPn N) s k q, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k q hs hk hq _ r hr
    simp [rhsOf, noSmP, Expr2.reads] at hr
  · intro s k q hs hk hq _ r hr
    simp [rhsOf, noCyP, Expr2.reads] at hr
  · intro s k hs hk r hr
    simp [rhsOf, smPartP, Expr2.reads] at hr
  · intro s k hs hk r hr
    simp [rhsOf, cyPartP, Expr2.reads] at hr
  · intro s k i hs hk hi hic r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    simp [rhsOf, carP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("T", ofs N (NPn N) (s + 1) k i, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k i hs hk hi hic hicf r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, sumP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("T", ofs N (NPn N) (s + 1) k i, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k i hs hk hi hicf hih r hr q' hq' hov
    have hst := stg_of h30 hs
    have hb := stg_bounds h30 hs
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hht := id_height hst hk
    have hc0 := id_carry0 hst
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    have hnl := HnF_le N (tS N s) k
    have e1 : fC N s k = fF N s (tS N s) (uS N s) k := rfl
    have e2 : hC N s k = hF N s (tS N s) (uS N s) k := rfl
    have e3 : cC N s k = cF N (tS N s) (uS N s) k := rfl
    have e4 : HnC N s k = HnF N (tS N s) k := rfl
    have e5 : HbF N s (uS N s) k ≤ N := hbl
    simp [rhsOf, keepP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("T", ofs N (NPn N) (s + 1) k i, 1)
       first | rw [hT rfl] | rw [hS (Or.inl rfl)] | rw [hS (Or.inr rfl)]
       simp (disch := omega) only [rk_cell, ofs_div]
       simp
       try omega)
  · intro s k i hs hk hi _ r hr
    simp [rhsOf, zeroP, Expr2.reads] at hr
  · intro s k hs hk r hr
    simp [rhsOf, tPartP, Expr2.reads] at hr
  · intro k hk r hr q' hq' hov
    simp [rhsOf, finPP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("p", k, 1)
       first | rw [hT rfl] | rw [hK rfl]
       try simp (disch := omega) only [ofs_div]
       simp [rkW]
       try omega)
  · intro k hk r hr q' hq' hov
    simp [rhsOf, finKP, Expr2.reads, Expr2.sliceReads] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      (obtain ⟨hn, hT, hS, hK⟩ := read_rank hN1 h30 hq' hov
       show _ < rkW N ("K", k + 1, 1)
       first | rw [hT rfl] | rw [hK rfl]
       try simp (disch := omega) only [ofs_div]
       simp [rkW]
       try omega)

end comb

end Submission

/-! # Acyclicity, the family member, the settled state, the statement -/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombLib SvGolf

/-! ## 1. Acyclicity: the rank of a process is the rank of its write window -/

/-- The rank certificate. -/
def dRank (N : Nat) (j : Nat) : Nat :=
  match (dM N).processes[j]? with
  | some p => rkW N (winOf p)
  | none => 0

section fam

variable {N : Nat}

theorem dM_acyclic (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : Acyclic (dM N) := by
  refine ⟨dRank N, ?_⟩
  intro i j ti ei tj ej wj hi hj hw ⟨r, hr, hov⟩
  have hmi := dM_mem_of_getElem? hN1 hi
  have hmj := dM_mem_of_getElem? hN1 hj
  obtain ⟨-, hws⟩ := dProcs_wins _ hmj tj ej rfl
  rw [hws, List.mem_singleton] at hw
  subst hw
  have hri : dRank N i = rkW N (winOf (.assign ti ei)) := by simp only [dRank, hi]
  have hrj : dRank N j = rkW N (winOf (.assign tj ej)) := by simp only [dRank, hj]
  rw [hri, hrj]
  exact dProcs_reads hN1 h30 _ hmi r hr _ hmj hov

/-! ## 2. `design.sem N` is the instantiated design -/

/-- Every write window is positive. -/
theorem dProcs_pos (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : ∀ p ∈ dProcs N, 0 < (winOf p).2.2 := by
  have hP := NPn_pos N
  have hB : 0 < 2 * N * NPn N := Nat.mul_pos (by omega) hP
  refine dProcs_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hB
  · exact hB
  · exact Nat.one_pos
  all_goals first
    | (intros; exact Nat.one_pos)
    | (intro s k hs hk
       have hb := stg_bounds h30 hs
       simp only [winOf, smPartP, cyPartP, tPartP]
       omega)

theorem dM_pos (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : ∀ i n lo w, (dM N).Writes i (n, lo, w) → 0 < w := by
  intro i n lo w h
  obtain ⟨p, -, hm, hw⟩ := dM_writes hN1 h
  have := dProcs_pos hN1 h30 p hm
  rw [← hw] at this
  exact this

/-- **`design.sem N` is `dM N`** for every `N` in range (the one-driver guard passes: the comb profile). -/
theorem sem_eq (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) : design.sem N = dM N := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  exact PDesign.instantiateGD2_of_combDesign (d_instantiate2 hN1 h30) (dM_comb hN1 h30) (dM_pos hN1 h30)

end fam

/-! ## 3. Reading windows of a settled state -/

section Gates

variable {st : SvState}

theorem eval_sliceK {n : String} {u : LVec} {lo w : Nat} {x : BitVec w}
    (h : SvState.lookup st n = some u) (hk : u.extract lo w = LVec.ofBitVec x) :
    evalPure2 st (.slice (.ident n) lo w) = .ok (LVec.ofBitVec x) := by
  simp only [evalPure2_slice, evalPure2_ident_of_lookup h, Pure2.res_ok_bind, Pure2.res_pure_eq, hk]

theorem eval_bitK {n : String} {w : Nat} {x : BitVec w} {i : Nat}
    (h : SvState.lookup st n = some (LVec.ofBitVec x)) (hi : i < w) :
    evalPure2 st (.slice (.ident n) i 1) = .ok (LVec.ofBitVec (BitVec.ofBool (x.getLsbD i))) :=
  evalPure2_bit_ofBitVec (evalPure2_ident_ofBitVec h) hi

theorem eval_lit0 : evalPure2 st (.lit lit0) = .ok (LVec.ofBitVec (BitVec.ofBool false)) := by
  have h : lit0 = LVec.replicate 1 .l0 := by first | rfl | decide
  rw [evalPure2_lit, h, LVec.replicate_l0]
  rfl

theorem eval_zeros (w : Nat) : evalPure2 st (zeros w) = .ok (LVec.ofBitVec (0#w)) := by
  simp only [zeros, evalPure2_lit, LVec.replicate_l0]

end Gates

theorem LVec_extract_extract (v : LVec) {lo w j k : Nat} (h : j + k ≤ w) :
    (v.extract lo w).extract j k = v.extract (lo + j) k := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  have hji : j + i < w := by omega
  simp only [LVec.getD_extract, hi, hji, if_true, Nat.add_assoc]

theorem readback {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo w : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo w) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {wv : Nat} {x : BitVec wv}
    (he : evalPure2 st e = .ok (LVec.ofBitVec x)) :
    u.extract lo w = LVec.ofBitVec (x.setWidth w) := by
  obtain ⟨old, hold, hext⟩ := CombEqs.extract_slice heqs hk he
  rw [hu, Option.some.injEq] at hold
  subst hold
  rw [hext, LVec.resizeU_ofBitVec]

theorem readback1 {d : Design2} {st : SvState} (heqs : CombEqs d st) {k : Nat} {n : String}
    {lo : Nat} {e : Expr2} (hk : d.processes[k]? = some (.assign (.slice n lo 1) e))
    {u : LVec} (hu : SvState.lookup st n = some u) {b : Bool}
    (he : evalPure2 st e = .ok (LVec.ofBitVec (BitVec.ofBool b))) :
    u.extract lo 1 = LVec.ofBitVec (BitVec.ofBool b) := by
  rw [readback heqs hk hu he, BitVec.setWidth_eq]

/-- Bit `o` of `u` is the known bit `b`. -/
abbrev Bt (u : LVec) (o : Nat) (b : Bool) : Prop := u.extract o 1 = LVec.ofBitVec (BitVec.ofBool b)

/-! ## 4. Where the processes are -/

section mem

variable {N : Nat}

theorem mem_dProcs_pp {k i : Nat} (hk : k < 2 * N) (hi : i < NPn N) {p : Process2}
    (hp : p ∈ ppCell N k i) : p ∈ dProcs N := by
  unfold dProcs ppProcs
  exact List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hp⟩⟩))

theorem mem_dProcs_col {s k : Nat} (hs : s < nst N) (hk : k < 2 * N) {p : Process2}
    (hp : p ∈ colProcs N s (tS N s) (uS N s) k) : p ∈ dProcs N := by
  unfold dProcs stProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hp⟩⟩)))

theorem mem_dProcs_finP {k : Nat} (hk : k < 2 * N) : finPP N k ∈ dProcs N := by
  unfold dProcs finProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_self⟩)))

theorem mem_dProcs_finK {k : Nat} (hk : k < 2 * N) : finKP N k ∈ dProcs N := by
  unfold dProcs finProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_of_mem _ List.mem_cons_self⟩)))

theorem mem_dProcs_k0 : k0P ∈ dProcs N := by
  unfold dProcs
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem mem_dProcs_smRow : smRowP N ∈ dProcs N := by
  unfold dProcs
  exact List.mem_append_left _ List.mem_cons_self

theorem mem_dProcs_cyRow : cyRowP N ∈ dProcs N := by
  unfold dProcs
  exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

variable {s t u k : Nat}

theorem mem_col_add {q : Nat} (hq : q < u - t + 1) {p : Process2}
    (hp : p ∈ addCell N s k (fF N s t u k) (hF N s t u k) q) : p ∈ colProcs N s t u k := by
  unfold colProcs
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hp⟩)

theorem mem_col_smPart : smPartP N s k (u - t + 1) ∈ colProcs N s t u k := by
  unfold colProcs
  exact List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)

theorem mem_col_cyPart : cyPartP N s k (u - t + 1) ∈ colProcs N s t u k := by
  unfold colProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self))

theorem mem_col_bit {i : Nat} (hi : i < t) {p : Process2}
    (hp : p ∈ bitCell N s t k (cF N t u k) (fF N s t u k) (hF N s t u k) i) : p ∈ colProcs N s t u k := by
  unfold colProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hp⟩))))

theorem mem_col_tPart : tPartP N s k t ∈ colProcs N s t u k := by
  unfold colProcs
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    List.mem_cons_self)))

end mem

/-! ## 5. The settled state, cell by cell -/

section settled

variable {N : Nat} {st : SvState}

/-- A 1-bit cell assign, read back. -/
theorem rb1 (hN1 : 1 ≤ N) (heqs : CombEqs (dM N) st) {n : String} {lo : Nat} {e : Expr2}
    (hp : Process2.assign (.slice n lo 1) e ∈ dProcs N) {u : LVec} (hu : SvState.lookup st n = some u)
    {b : Bool} (he : evalPure2 st e = .ok (LVec.ofBitVec (BitVec.ofBool b))) : Bt u lo b := by
  obtain ⟨k, hk⟩ := dM_getElem?_of_mem hN1 hp
  exact readback1 heqs hk hu he

/-- A zero part, read back bit by bit. -/
theorem rbZ (hN1 : 1 ≤ N) (heqs : CombEqs (dM N) st) {n : String} {lo w : Nat}
    (hp : Process2.assign (.slice n lo w) (zeros w) ∈ dProcs N) {u : LVec}
    (hu : SvState.lookup st n = some u) : ∀ j < w, Bt u (lo + j) false := by
  obtain ⟨k, hk⟩ := dM_getElem?_of_mem hN1 hp
  have h := readback heqs hk hu (eval_zeros w)
  intro j hj
  show u.extract (lo + j) 1 = _
  rw [← LVec_extract_extract u (lo := lo) (w := w) (j := j) (k := 1) (by omega), h, BitVec.setWidth_eq,
    LVec.extract_one_ofBitVec _ hj]
  simp

/-- Stage 0: the partial products. -/
theorem cells_pp (hN1 : 1 ≤ N) (heqs : CombEqs (dM N) st) {uT : LVec}
    (hT : SvState.lookup st "T" = some uT) {x y : BitVec N}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ k < 2 * N, ∀ i < NPn N, Bt uT (cl N 0 k i) (tv N x.getLsbD y.getLsbD 0 k i) := by
  intro k hk i hi
  show Bt uT (cl N 0 k i) (T0 N x.getLsbD y.getLsbD k i)
  unfold T0
  by_cases h : i < H0F N k
  · rw [if_pos h]
    have hm : ppAndP N k i ∈ dProcs N := mem_dProcs_pp hk hi (by simp [ppCell, h])
    have hj1 : k - i - loF N k < N := by unfold H0F at h; unfold loF; omega
    have hj2 : i + loF N k < N := by unfold H0F at h; unfold loF; omega
    have he := evalPure2_and_ofBitVec (eval_bitK ha hj1) (eval_bitK hb hj2)
    rw [BitVec.ofBool_and_ofBool] at he
    exact rb1 hN1 heqs hm hT he
  · rw [if_neg h]
    have hm : ppZeroP N k i ∈ dProcs N := mem_dProcs_pp hk hi (by simp [ppCell, h])
    exact rb1 hN1 heqs hm hT eval_lit0

/-- One stage: the sums and carries of stage `s`, then the columns after it. -/
theorem cells_step (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) (heqs : CombEqs (dM N) st) {uT uSM uCY : LVec}
    (hT : SvState.lookup st "T" = some uT) (hSM : SvState.lookup st "SM" = some uSM)
    (hCY : SvState.lookup st "CY" = some uCY) {A B : Nat → Bool} {s : Nat} (hs : s < nst N)
    (ih : ∀ k < 2 * N, ∀ i < NPn N, Bt uT (cl N s k i) (tv N A B s k i)) :
    ∀ k < 2 * N, ∀ i < NPn N, Bt uT (cl N (s + 1) k i) (tv N A B (s + 1) k i) := by
  have hst := stg_of h30 hs
  have hbd := stg_bounds h30 hs
  have hPN := NPn_ge N
  have hP2 := NPn_two N
  -- the sums of the stage
  have hsm : ∀ k < 2 * N, ∀ q < NPn N,
      Bt uSM (cl N s k q) (smB N s (tS N s) (uS N s) (tv N A B s) k q) := by
    intro k hk q hq
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    unfold smB
    by_cases hw : q < uS N s - tS N s + 1
    · rw [if_pos hw]
      by_cases h1 : q < fF N s (tS N s) (uS N s) k
      · rw [if_pos h1]
        have hm : faSmP N s k q ∈ dProcs N :=
          mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1]))
        have he := evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec
          (eval_sliceK hT (ih k hk (3 * q) (by omega))) (eval_sliceK hT (ih k hk (3 * q + 1) (by omega))))
          (eval_sliceK hT (ih k hk (3 * q + 2) (by omega)))
        simp only [BitVec.ofBool_xor_ofBool] at he
        exact rb1 hN1 heqs hm hSM he
      · rw [if_neg h1]
        by_cases h2 : q < fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
        · rw [if_pos h2]
          have hm : haSmP N s k q ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1, h2]))
          have he := evalPure2_xor_ofBitVec
            (eval_sliceK hT (ih k hk (3 * q) (by omega))) (eval_sliceK hT (ih k hk (3 * q + 1) (by omega)))
          simp only [BitVec.ofBool_xor_ofBool] at he
          exact rb1 hN1 heqs hm hSM he
        · rw [if_neg h2]
          have hm : noSmP N s k q ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1, h2]))
          exact rb1 hN1 heqs hm hSM eval_lit0
    · rw [if_neg hw]
      have hm : smPartP N s k (uS N s - tS N s + 1) ∈ dProcs N := mem_dProcs_col hs hk mem_col_smPart
      have h := rbZ hN1 heqs hm hSM (q - (uS N s - tS N s + 1)) (by omega)
      have e : cl N s k (uS N s - tS N s + 1) + (q - (uS N s - tS N s + 1)) = cl N s k q := by
        simp only [cl, ofs]; omega
      rw [← e]
      exact h
  -- the carries of the stage
  have hcy : ∀ k < 2 * N, ∀ q < NPn N,
      Bt uCY (cl N s k q) (cyB N s (tS N s) (uS N s) (tv N A B s) k q) := by
    intro k hk q hq
    have hr3 := id_reads hst hk
    have hbl := id_Hb_le hst (k := k)
    have hhl := id_h_le (N := N) (s := s) (t := tS N s) (u := uS N s) (k := k)
    unfold cyB
    by_cases hw : q < uS N s - tS N s + 1
    · rw [if_pos hw]
      by_cases h1 : q < fF N s (tS N s) (uS N s) k
      · rw [if_pos h1]
        have hm : faCyP N s k q ∈ dProcs N :=
          mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1]))
        have e0 := eval_sliceK hT (ih k hk (3 * q) (by omega))
        have e1 := eval_sliceK hT (ih k hk (3 * q + 1) (by omega))
        have e2 := eval_sliceK hT (ih k hk (3 * q + 2) (by omega))
        have he := evalPure2_or_ofBitVec (evalPure2_and_ofBitVec e0 e1)
          (evalPure2_and_ofBitVec e2 (evalPure2_xor_ofBitVec e0 e1))
        simp only [BitVec.ofBool_xor_ofBool, BitVec.ofBool_and_ofBool, BitVec.ofBool_or_ofBool] at he
        exact rb1 hN1 heqs hm hCY he
      · rw [if_neg h1]
        by_cases h2 : q < fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
        · rw [if_pos h2]
          have hm : haCyP N s k q ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1, h2]))
          have he := evalPure2_and_ofBitVec
            (eval_sliceK hT (ih k hk (3 * q) (by omega))) (eval_sliceK hT (ih k hk (3 * q + 1) (by omega)))
          simp only [BitVec.ofBool_and_ofBool] at he
          exact rb1 hN1 heqs hm hCY he
        · rw [if_neg h2]
          have hm : noCyP N s k q ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_add hw (by simp [addCell, h1, h2]))
          exact rb1 hN1 heqs hm hCY eval_lit0
    · rw [if_neg hw]
      have hm : cyPartP N s k (uS N s - tS N s + 1) ∈ dProcs N := mem_dProcs_col hs hk mem_col_cyPart
      have h := rbZ hN1 heqs hm hCY (q - (uS N s - tS N s + 1)) (by omega)
      have e : cl N s k (uS N s - tS N s + 1) + (q - (uS N s - tS N s + 1)) = cl N s k q := by
        simp only [cl, ofs]; omega
      rw [← e]
      exact h
  -- the columns after the stage
  intro k hk i hi
  have hr3 := id_reads hst hk
  have hbl := id_Hb_le hst (k := k)
  have hht := id_height hst hk
  have hc0 := id_carry0 hst
  have hnl := HnF_le N (tS N s) k
  show Bt uT (cl N (s + 1) k i) (stepT N s (tS N s) (uS N s) (tv N A B s) k i)
  unfold stepT
  by_cases ht : i < tS N s
  · rw [if_pos ht]
    by_cases h1 : i < cF N (tS N s) (uS N s) k
    · rw [if_pos h1]
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · omega
        · exact h
      have hm : carP N s k i ∈ dProcs N := mem_dProcs_col hs hk (mem_col_bit ht (by simp [bitCell, h1]))
      exact rb1 hN1 heqs hm hT (eval_sliceK hCY (hcy (k - 1) (by omega) i (by omega)))
    · rw [if_neg h1]
      by_cases h2 : i < cF N (tS N s) (uS N s) k + fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k
      · rw [if_pos h2]
        have hm : sumP N s k i (cF N (tS N s) (uS N s) k) ∈ dProcs N :=
          mem_dProcs_col hs hk (mem_col_bit ht (by simp [bitCell, h1, h2]))
        exact rb1 hN1 heqs hm hT (eval_sliceK hSM (hsm k hk (i - cF N (tS N s) (uS N s) k) (by omega)))
      · rw [if_neg h2]
        by_cases h3 : i < HnF N (tS N s) k
        · rw [if_pos h3]
          have hm : keepP N s k i (cF N (tS N s) (uS N s) k) (fF N s (tS N s) (uS N s) k)
              (hF N s (tS N s) (uS N s) k) ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_bit ht (by simp [bitCell, h1, h2, h3]))
          exact rb1 hN1 heqs hm hT (eval_sliceK hT (ih k hk (i - cF N (tS N s) (uS N s) k +
            2 * fF N s (tS N s) (uS N s) k + hF N s (tS N s) (uS N s) k) (by omega)))
        · rw [if_neg h3]
          have hm : zeroP N s k i ∈ dProcs N :=
            mem_dProcs_col hs hk (mem_col_bit ht (by simp [bitCell, h1, h2, h3]))
          exact rb1 hN1 heqs hm hT eval_lit0
  · rw [if_neg ht]
    have hm : tPartP N s k (tS N s) ∈ dProcs N := mem_dProcs_col hs hk mem_col_tPart
    have h := rbZ hN1 heqs hm hT (i - tS N s) (by omega)
    have e : cl N (s + 1) k (tS N s) + (i - tS N s) = cl N (s + 1) k i := by
      simp only [cl, ofs]; omega
    rw [← e]
    exact h

/-- The carries of the final adder. -/
def kc (N : Nat) (A B : Nat → Bool) : Nat → Bool
  | 0 => false
  | k + 1 => (tv N A B (nst N) k 0 && tv N A B (nst N) k 1) ||
      (kc N A B k && (tv N A B (nst N) k 0 ^^ tv N A B (nst N) k 1))

theorem cells_K (hN1 : 1 ≤ N) (heqs : CombEqs (dM N) st) {uT uK : LVec}
    (hT : SvState.lookup st "T" = some uT) (hK : SvState.lookup st "K" = some uK) {A B : Nat → Bool}
    (hS : ∀ k < 2 * N, ∀ i < NPn N, Bt uT (cl N (nst N) k i) (tv N A B (nst N) k i)) :
    ∀ k ≤ 2 * N, Bt uK k (kc N A B k) := by
  have hP2 := NPn_two N
  intro k
  induction k with
  | zero => intro _; exact rb1 hN1 heqs mem_dProcs_k0 hK eval_lit0
  | succ k ih =>
    intro hk
    have e0 := eval_sliceK hT (hS k (by omega) 0 (by omega))
    have e1 := eval_sliceK hT (hS k (by omega) 1 (by omega))
    have eK := eval_sliceK hK (ih (by omega))
    have he := evalPure2_or_ofBitVec (evalPure2_and_ofBitVec e0 e1)
      (evalPure2_and_ofBitVec eK (evalPure2_xor_ofBitVec e0 e1))
    simp only [BitVec.ofBool_xor_ofBool, BitVec.ofBool_and_ofBool, BitVec.ofBool_or_ofBool] at he
    exact rb1 hN1 heqs (mem_dProcs_finK (by omega)) hK he

theorem cells_P (hN1 : 1 ≤ N) (heqs : CombEqs (dM N) st) {uT uK uP : LVec}
    (hT : SvState.lookup st "T" = some uT) (hK : SvState.lookup st "K" = some uK)
    (hP : SvState.lookup st "p" = some uP) {A B : Nat → Bool}
    (hS : ∀ k < 2 * N, ∀ i < NPn N, Bt uT (cl N (nst N) k i) (tv N A B (nst N) k i))
    (hKc : ∀ k ≤ 2 * N, Bt uK k (kc N A B k)) :
    ∀ k < 2 * N, Bt uP k ((tv N A B (nst N) k 0 ^^ tv N A B (nst N) k 1) ^^ kc N A B k) := by
  have hP2 := NPn_two N
  intro k hk
  have e0 := eval_sliceK hT (hS k hk 0 (by omega))
  have e1 := eval_sliceK hT (hS k hk 1 (by omega))
  have eK := eval_sliceK hK (hKc k (by omega))
  have he := evalPure2_xor_ofBitVec (evalPure2_xor_ofBitVec e0 e1) eK
  simp only [BitVec.ofBool_xor_ofBool] at he
  exact rb1 hN1 heqs (mem_dProcs_finP hk) hP he

end settled

/-- Two bit functions with the same value agree below the width. -/
theorem bfVal_inj {f g : Nat → Bool} : ∀ n, bfVal f n = bfVal g n → ∀ j < n, f j = g j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    have h1 := bfVal_lt f n
    have h2 := bfVal_lt g n
    rw [bfVal, bfVal] at h
    have hfn : f n = g n ∧ bfVal f n = bfVal g n := by
      cases hf : f n <;> cases hg : g n <;> simp [hf, hg] at h ⊢ <;> omega
    rcases Nat.lt_or_ge j n with hj' | hj'
    · exact bfVal_inj n hfn.2 j hj'
    · obtain rfl : j = n := by omega
      exact hfn.1

section top

variable {N : Nat}

/-- **The settled state** (every `N` in range): known `x y` on `a b` give the `2N`-bit product on `p`. -/
theorem dadda_settled (hN1 : 1 ≤ N) (h30 : N < 2 ^ 30) {st : SvState} (heqs : CombEqs (dM N) st)
    (hs : StateShape (dM N) st) {x y : BitVec N}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  have drv : ∀ {p : Process2} {n : String} {lo w : Nat} {e : Expr2}, p ∈ dProcs N →
      p = .assign (.slice n lo w) e → Driven (dM N) n := by
    intro p n lo w e hp he
    obtain ⟨k, hk⟩ := dM_getElem?_of_mem hN1 hp
    subst he
    exact ⟨k, lo, w, _, _, hk, by simp⟩
  have hk0 : 0 < 2 * N := by omega
  have hH0 : 0 < H0F N 0 := by unfold H0F; omega
  obtain ⟨uT, hT, -⟩ := hs.driven "T"
    (drv (mem_dProcs_pp hk0 (NPn_pos N) (p := ppAndP N 0 0) (by simp [ppCell, hH0])) rfl)
  obtain ⟨uSM, hSM, -⟩ := hs.driven "SM" (drv mem_dProcs_smRow rfl)
  obtain ⟨uCY, hCY, -⟩ := hs.driven "CY" (drv mem_dProcs_cyRow rfl)
  obtain ⟨uK, hK, -⟩ := hs.driven "K" (drv mem_dProcs_k0 rfl)
  obtain ⟨uP, hP, hPw⟩ := hs.driven "p" (drv (mem_dProcs_finP hk0) rfl)
  have hcells : ∀ s ≤ nst N, ∀ k < 2 * N, ∀ i < NPn N,
      Bt uT (cl N s k i) (tv N x.getLsbD y.getLsbD s k i) := by
    intro s
    induction s with
    | zero => intro _; exact cells_pp hN1 heqs hT ha hb
    | succ s ih => intro hs'; exact cells_step hN1 h30 heqs hT hSM hCY (by omega) (ih (by omega))
  have hS := hcells (nst N) (Nat.le_refl _)
  have hKc := cells_K hN1 heqs hT hK hS
  have hpb := cells_P hN1 heqs hT hK hP hS hKc
  -- the arithmetic
  have hrows := final_rows hN1 h30 x.getLsbD y.getLsbD
  rw [bfVal_bv, bfVal_bv] at hrows
  have hlt : x.toNat * y.toNat < 2 ^ (2 * N) := by
    rw [Nat.two_mul, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt x.isLt y.isLt
  have hrip := ripple_final (2 * N) (fun k => tv N x.getLsbD y.getLsbD (nst N) k 0)
    (fun k => tv N x.getLsbD y.getLsbD (nst N) k 1)
    (fun k => (tv N x.getLsbD y.getLsbD (nst N) k 0 ^^ tv N x.getLsbD y.getLsbD (nst N) k 1) ^^
      kc N x.getLsbD y.getLsbD k)
    (kc N x.getLsbD y.getLsbD) rfl (fun _ _ => rfl) (fun _ _ => rfl) (by rw [hrows]; exact hlt)
  rw [hrows] at hrip
  have hPv : bfVal (BitVec.ofNat (2 * N) (x.toNat * y.toNat)).getLsbD (2 * N) = x.toNat * y.toNat := by
    rw [bfVal_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hbits := bfVal_inj (2 * N) (hrip.trans hPv.symm)
  -- assemble `p`
  have wp : (dM N).declWidth "p" = some (2 * N) := by simp [dM_declWidth, dDecls]
  rw [wp, Option.some.injEq] at hPw
  rw [hP]
  congr 1
  apply LVec.eq_ofBitVec_of_extract_one hPw.symm
  intro j hj
  rw [← hbits j hj]
  exact hpb j hj

theorem dadda_interface : SvGolf.Tasks.Mul.task.Interface N (dM N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, dM_decls, dDecls, SvGolf.Tasks.Mul.task]

end top

/-- **The solution**: the `mul` statement for every `N` in range. -/
theorem solution : Goal := by
  intro N hN
  have hN1 : 1 ≤ N := hN.1
  have h30 : N < 2 ^ 30 := hN.2
  show SvGolf.Tasks.Mul.task.SatisfiedAt N (design.sem N)
  rw [sem_eq hN1 h30]
  refine CombTask.satisfiedAt_of_comb dadda_interface (dM_comb hN1 h30) (dM_acyclic hN1 h30) ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  exact dadda_settled hN1 h30 heqs hs hv.1 hv.2

end Submission
