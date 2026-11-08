import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# Reference solution for task `mul`, proved with the `sv_comb` tactics

This is a submission file like any player's `Solution.lean`. The checker generates the module
`Submission.Design` (`Submission.design`, `Submission.Goal`); this file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N ≥ 1`. The design is `reference/mul_n.sv`, an `N × N → 2N` array multiplier: 2-D
signals `pp`, `s`, `c`, `t`, nested `generate for` loops, a part-select target and a concatenation.
The same statement is proved with no tactic in `reference/mul_n_byhand.lean` (about six times as
many code lines).

## Route

1. **Structure** (`mul_struct`): `sv_structure` proves `CombDesign ∧ Acyclic` in one theorem;
   the goals it leaves compare 2-D windows, which are row-major offsets `r * W + c`, so they are
   closed by `intros; sv_rowmajor; omega` (`sv_rowmajor` rewrites those comparisons into
   lexicographic ones with the library lemma `rmN_lt_iff`). The rank is a lexicographic key
   `(row, column, phase)` of each site identity (`mulKey`). `mul_struct` needs
   `maxHeartbeats 400000` (the default 200000 times out in `simp`).
2. **Ports** (`mul_interface`): the statement pins the port names, order and widths; `sv_interface`
   proves them from the `CombDesign` profile (see `add_n.lean`).
3. **Equations** (in `solution`): `sv_equations` derives the eleven equations of the 2-D netlist
   (`eq_pp_g_pp_j_0`, `eq_t_g_bit_0`, ..., the row stride hidden inside `rmN W i j`), the knownness
   of every driven bit and the obligations. The one-dimensional and simple ones close by
   `intros; omega`; the six COVERAGE goals of the nested 2-D reads (`cover_2`, `cover_4` to
   `cover_8`: "the cell this assign reads is written by some assign") are closed by `sv_cover`, which
   solves the writer's loop indices from the read's row and column and walks the disjunction of
   writers (`CombCover.lean`).
4. **Arithmetic and bridge** (in `solution`): the equations are the library structure
   `CombLib.MulNetlistView` (one field per group of assigns), over the cells `st.cell "s" W i j` of the
   2-D signals. Each field is one `sv_bridge eq_x`: the printed equation has the netlist's `Int` index
   forms (`rmN W (↑i + -1) (↑j + 1)`), the field has `Nat` indices (`s (i - 1) (j + 1)`), and
   `sv_bridge` closes the difference by congruence and `omega`. `ideal_mul_view` (the ripple-row lemma
   and the row induction) proves `p = a * b`, and the port bridge turns the Boolean bits into the
   port's value.
-/

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

/-! ## 1. Structure: `sv_structure` -/

/-- The rank: a lexicographic key `(row, column, phase)` of each site identity. Partial products and
the zero rows come first; within a row, column by column: the propagate `t`, the carry `c`, then the
sum `s`; the row's top bit after its last column; the outputs last. -/
def mulKey (N : Nat) : SiteId → Key
  | .plain 0 => (0, 0, 1)                 -- s[0] = {1'b0, pp[0]}
  | .plain 1 => (0, 0, 0)                 -- c[0] = '0
  | .plain 2 => (0, 0, 0)                 -- t[0] = '0
  | .plain _ => (N, 0, 1)                 -- p[2*N-1:N] = s[N-1][N:1]
  | .fam "g_pp_j" _ _ => (0, 0, 0)        -- pp[i][j] = a[j] & b[i]
  | .fam "g_row" 0 [i] => (i.toNat, 0, 0) -- c[i][0] = 1'b0
  | .fam "g_row" _ [i] => (i.toNat, N, 0) -- s[i][N] = c[i][N]
  | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat, 1)   -- t[i][j]
  | .fam "g_bit" 1 [i, j] => (i.toNat, j.toNat, 3)   -- s[i][j]
  | .fam "g_bit" _ [i, j] => (i.toNat, j.toNat, 2)   -- c[i][j+1]
  | .fam _ _ _ => (N, 0, 0)               -- p[i] = s[i][0]

set_option maxHeartbeats 400000 in
/-- `CombDesign` and `Acyclic` for every `N ≥ 1`, from the lexicographic key: ONE application of the
soundness theorem and one round of obligations for both. -/
theorem mul_struct (N : Nat) (hN : 1 ≤ N) :
    CombDesign (design.sem N) ∧ Acyclic (design.sem N) ∧ SharedObl design.pdesign [N] := by
  sv_structure (lexRank := mulKey N)
  all_goals (intros; sv_rowmajor; omega)

/-! ## 2. The ports (the task's `Interface`) -/

/-- The task's interface: exactly the ports `a`, `b` (`N` bits) and `p` (`2N` bits). -/
theorem mul_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by
  sv_interface

/-! ## 3. The statement: bridge and arithmetic; `sv_cover` closes the coverage -/

set_option maxHeartbeats 400000 in
/-- **The reference solution**: the `mul` statement, for every `N ≥ 1`. -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  obtain ⟨hc, ha, hso⟩ := mul_struct N hN'
  refine CombTask.satisfiedAt_of_comb (mul_interface N hN' hc) hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_out_0 0 (by omega)
    have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    have hkp : ∀ k, k < 2 * N → KnownBit st "p" k := by
      intro k hk
      by_cases h : k < N
      · exact (known_p_g_out_0 k h).2
      · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
        exact (known_p_plain_3 j (by omega)).2
    rw [hvp, SvState.lookup_eq_ofBitVec_bv (W := 2 * N) hvp (by omega) hkp]
    congr 2
    refine ideal_mul_view hN' (pp := st.cell "pp" N) (t := st.cell "t" N)
      (s := st.cell "s" ((N : Int) + 1)) (c := st.cell "c" ((N : Int) + 1))
      { pp_def := ?_, s0 := ?_, s0_top := ?_, c0 := ?_, t0 := ?_, ci0 := ?_, t_def := ?_, s_def := ?_,
        c_def := ?_, s_top := ?_, p_low := ?_, p_high := ?_ }
    · sv_bridge eq_pp_g_pp_j_0 with ba, bb
    · sv_bridge eq_s_plain_0 with if_pos
    · sv_bridge (eq_s_plain_0 N (by omega)) with if_neg
    · sv_bridge eq_c_plain_1
    · sv_bridge eq_t_plain_2
    · sv_bridge eq_c_g_row_0
    · sv_bridge eq_t_g_bit_0
    · sv_bridge eq_s_g_bit_1
    · sv_bridge eq_c_g_bit_2
    · sv_bridge eq_s_g_row_2
    · sv_bridge eq_p_g_out_0 with XF.getLsbD_bv
    · sv_bridge eq_p_plain_3 with XF.getLsbD_bv
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  all_goals first | (intros; omega) | sv_cover

/--
info: 'Submission.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

end Submission
