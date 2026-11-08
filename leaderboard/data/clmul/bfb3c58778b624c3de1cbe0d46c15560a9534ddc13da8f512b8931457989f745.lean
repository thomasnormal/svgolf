import Submission.Design
import tasks.clmul.Spec
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Reference solution for task `clmul`, proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. The design is `reference/clmul_n.sv`, the carry-less array multiplier: one 2-D signal `r`
(`N` rows of `N` bits), four `generate for` loops (the first row, the other rows with an inner loop, the low
output bits, the high output bits), the shape of `mul_n` with XOR where `mul_n` has a full adder.

## Route

1. **Structure** (`clmul_struct`): `sv_structure` proves `CombDesign ∧ Acyclic` in one theorem; the rank is a
   lexicographic key `(row, 0, 0)` of each site identity (`clmulKey`: a row depends on the row above only, the
   output bits come after every row); the goals it leaves are closed by `intros; sv_rowmajor; omega`. The key
   goes through a partial classifier of the five site families (`clmulFamily?`), and `clmul_sites_classified`
   proves it covers every site, so a change to the generated layout fails loudly instead of taking a default.
2. **Ports** (`clmul_interface`): `sv_interface`.
3. **Equations** (in `solution`): `sv_equations` derives the five equations (`eq_r_g_row0_0`, `eq_r_g_bit_0`,
   `eq_r_g_row_1`, `eq_p_g_lo_0`, `eq_p_g_hi_0`) and the knownness of every driven bit; the obligations close by
   `intros; omega` and `sv_cover`.
4. **Arithmetic and bridge**: the five equations are the fields of `View`, over the cells `st.cell "r" N i j` of
   the 2-D signal; each field is one `sv_bridge`. `view_spec` is the mathematics: the row invariant
   `r i j = XOR over t ≤ i of A t & B (i + j - t)` (`view_row`, an induction on the row) and the collapse of the
   Spec's double sum (`bx_pair`), then `getLsbD_ofBits` and `coeff_eq` turn the bit statement into the Spec's
   `BitVec`.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf
open SvGolf.Tasks.Clmul

/-! ## 0. The arithmetic: plain Lean, no ls-sv -/

namespace ClmulArith



/-- `bx f n`: the XOR of `f 0, …, f (n-1)`. -/
def bx (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => bx f n ^^ f n

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


/-- The accumulator of rows `0 .. i`, read at column `j`: `XOR over t ≤ i` of `A t & B (i + j - t)`, a term
whose `B` index is `≥ N` being `0`. -/
def rowSum (N : Nat) (A B : Nat → Bool) (i j : Nat) : Bool :=
  bx (fun t => decide (i + j - t < N) && A t && B (i + j - t)) (i + 1)

/-- The array's equations over `Nat`-indexed Boolean functions. -/
structure View (N : Nat) (A B : Nat → Bool) (P : Nat → Bool) (r : Nat → Nat → Bool) : Prop where
  row0 : ∀ j, j < N → r 0 j = (A 0 && B j)
  row_def : ∀ i, 1 ≤ i → i < N → ∀ j, j + 1 < N → r i j = (r (i - 1) (j + 1) ^^ (A i && B j))
  row_top : ∀ i, 1 ≤ i → i < N → r i (N - 1) = (A i && B (N - 1))
  p_low : ∀ i, i < N → P i = r i 0
  p_high : ∀ m, m + 1 < N → P (N + m) = r (N - 1) (m + 1)

theorem bx_succ (f : Nat → Bool) (n : Nat) : bx f (n + 1) = (bx f n ^^ f n) := rfl

theorem bx_false {f : Nat → Bool} {n : Nat} (h : ∀ t, t < n → f t = false) : bx f n = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bx_succ, ih (fun t ht => h t (by omega)), h n (by omega)]; rfl

theorem rowSum_big {N : Nat} {A B : Nat → Bool} {i j : Nat} (hj : N ≤ j) : rowSum N A B i j = false := by
  unfold rowSum
  apply bx_false
  intro t ht
  have : ¬ (i + j - t < N) := by omega
  simp [this]

theorem rowSum_succ (N : Nat) (A B : Nat → Bool) (i j : Nat) :
    rowSum N A B (i + 1) j = (rowSum N A B i (j + 1) ^^ (decide (j < N) && A (i + 1) && B j)) := by
  have e : ∀ t, i + 1 + j - t = i + (j + 1) - t := fun t => by omega
  have e2 : i + 1 + j - (i + 1) = j := by omega
  unfold rowSum
  rw [bx_succ _ (i + 1)]
  congr 1
  · apply bx_congr
    intro t ht
    simp only [e]
  · simp only [e2]

theorem view_row {N : Nat} {A B : Nat → Bool} {P : Nat → Bool} {r : Nat → Nat → Bool}
    (hv : View N A B P r) :
    ∀ i, i < N → ∀ j, j < N → r i j = rowSum N A B i j := by
  intro i
  induction i with
  | zero =>
    intro hi j hj
    rw [hv.row0 j hj]
    simp [rowSum, bx, hj]
  | succ i ih =>
    intro hi j hj
    rw [rowSum_succ]
    by_cases hjN : j + 1 < N
    · rw [hv.row_def (i + 1) (by omega) hi j hjN]
      simp only [Nat.add_sub_cancel]
      rw [ih (by omega) (j + 1) hjN]
      simp [hj]
    · have hj' : j = N - 1 := by omega
      subst hj'
      rw [hv.row_top (i + 1) (by omega) hi, rowSum_big (N := N) (i := i) (j := N - 1 + 1) (by omega)]
      simp [hj]

theorem view_spec {N : Nat} (hN : 1 ≤ N) {A B : Nat → Bool} {P : Nat → Bool} {r : Nat → Nat → Bool}
    (hv : View N A B P r) :
    ∀ k, k < 2 * N - 1 →
      P k = bx (fun i => bx (fun j => decide (i + j = k) && A i && B j) N) N := by
  intro k hk
  have inner : (fun i => bx (fun j => decide (i + j = k) && A i && B j) N)
      = (fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) := by
    funext i
    exact bx_pair i k (A i) B N
  rw [inner]
  by_cases hkN : k < N
  · rw [hv.p_low k hkN, view_row hv k hkN 0 (by omega)]
    unfold rowSum
    rw [bx_trunc (f := fun i => decide (i ≤ k ∧ k - i < N) && A i && B (k - i)) (n := k + 1) (m := N)
      (by omega) (fun j hj1 _ => by simp; omega)]
    apply bx_congr
    intro t ht
    have h1 : k + 0 - t = k - t := by omega
    have h2 : decide (k - t < N) = true := by simp; omega
    have h3 : decide (t ≤ k ∧ k - t < N) = true := by simp; omega
    rw [h1, h2, h3]
  · obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
    rw [hv.p_high m (by omega), view_row hv (N - 1) (by omega) (m + 1) (by omega)]
    unfold rowSum
    have e : N - 1 + 1 = N := by omega
    rw [e]
    apply bx_congr
    intro t ht
    have e1 : N - 1 + (m + 1) = N + m := by omega
    rw [e1]
    have h3 : decide (t ≤ N + m ∧ N + m - t < N) = decide (N + m - t < N) := by
      apply decide_eq_decide.mpr; omega
    rw [h3]


end ClmulArith

/-! ## 1. Structure: `sv_structure` -/

/-- The five site families of the design, one per generated assign. -/
inductive ClmulFamily where
  | row0  -- r[0][j] = a[0] & b[j]
  | bit   -- r[i][j] = r[i-1][j+1] ^ (a[i] & b[j])
  | row   -- r[i][N-1] = a[i] & b[N-1]
  | lo    -- p[i] = r[i][0]
  | hi    -- p[N+m] = r[N-1][m+1]

/-- The partial classifier, on a site's static key (`idKey`: the label of its innermost block, the position of its
assign in that block, its number of loop indices). Every family is named; anything else is `none`, never a default
rank, and `clmul_sites_classified` proves no site of the design is `none`. -/
def clmulFamily? : String × Nat × Nat → Option ClmulFamily
  | ("g_row0", 0, 1) => some .row0
  | ("g_bit", 0, 2) => some .bit
  | ("g_row", 1, 1) => some .row
  | ("g_lo", 0, 1) => some .lo
  | ("g_hi", 0, 1) => some .hi
  | _ => none

/-- A site's loop indices, outermost first. -/
def siteIdx : SiteId → List Int
  | .plain _ => []
  | .fam _ _ idx => idx

/-- A family's key at the member's loop indices: a lexicographic `(row, 0, 0)`. The first row reads only the
inputs; row `i` (the outer index of `g_bit`, the index of `g_row`) reads row `i - 1` (`r[i-1][j+1]`); the output
bits read the rows, so they come last. -/
def ClmulFamily.key (N : Nat) (idx : List Int) : ClmulFamily → Key
  | .row0 => (0, 0, 0)
  | .bit | .row => ((idx.headD 0).toNat, 0, 0)
  | .lo | .hi => (N, 0, 0)

/-- The rank: the key of the site's family. The `none` arm is unreachable (`clmul_sites_classified`). -/
def clmulKey (N : Nat) (s : SiteId) : Key :=
  match clmulFamily? (idKey s) with
  | some f => f.key N (siteIdx s)
  | none => (N + 1, 0, 0)

/-- **Site coverage**: every located site of the design is in a named family, at every valuation of its loop
indices. A change to the generated layout (a renamed block, a moved or added assign) fails here. -/
theorem clmul_sites_classified :
    ∀ s, design.pdesign.summary = .ok s → ∀ ls ∈ s.lsites, ∀ σ, (clmulFamily? (idKey (ls.id σ))).isSome := by
  intro s hs ls hls σ
  have h : (match design.pdesign.summary with
      | .ok s => s.lsites.all fun ls => (clmulFamily? ls.key).isSome
      | .error _ => false) = true := by decide
  simp only [hs, List.all_eq_true] at h
  rw [idKey_id]
  exact h ls hls

/-! The diagnostic for the same fact: the static keys of the unclassified sites. If the layout changes, this
names the sites that `clmul_sites_classified` fails on. -/

/-- info: [] -/
#guard_msgs in
#eval match design.pdesign.summary with
  | .ok s => (s.lsites.map LSite.key).filter fun k => (clmulFamily? k).isNone
  | .error e => [(e, 0, 0)]

set_option maxHeartbeats 400000 in
/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from the lexicographic key. -/
theorem clmul_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := clmulKey N)
  all_goals (intros; sv_rowmajor; first | omega | (simp [clmulFamily?, idKey, ClmulFamily.key, siteIdx] <;> omega))

/-! ## 2. The ports (the task's `Interface`) -/

/-- The task's interface: exactly the ports `a`, `b` (`N` bits) and `p` (`2N-1` bits). -/
theorem clmul_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Clmul.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The statement: bridge and arithmetic; `sv_cover` closes the coverage -/

set_option maxHeartbeats 400000 in
/-- **The reference solution**: the `clmul` statement, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := clmul_struct N hN'
  refine CombTask.satisfiedAt_of_comb (clmul_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Clmul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_lo_0 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have hkp : ∀ k, k < 2 * N - 1 → KnownBit st "p" k := by
      intro k hk
      by_cases h : k < N
      · exact (known_p_g_lo_0 k h).2
      · obtain ⟨m, rfl⟩ : ∃ m, k = N + m := ⟨k - N, by omega⟩
        have := (known_p_g_hi_0 m (by omega)).2
        rwa [show ((N : Int) + (m : Int)).toNat = N + m by omega] at this
    have hview : ClmulArith.View N x.getLsbD y.getLsbD (st.boolAt "p") (st.cell "r" N) := by
      refine { row0 := ?_, row_def := ?_, row_top := ?_, p_low := ?_, p_high := ?_ }
      · sv_bridge eq_r_g_row0_0 with ba, bb
      · sv_bridge eq_r_g_bit_0 with ba, bb
      · sv_bridge eq_r_g_row_1 with ba, bb
      · sv_bridge eq_p_g_lo_0
      · sv_bridge eq_p_g_hi_0
    have hbits := ClmulArith.view_spec hN' hview
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N - 1) hvp (by omega) hkp]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, ClmulArith.getLsbD_ofBits, hbits k hk, ← ClmulArith.coeff_eq]
    simp [hk]
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
