import SvGolf.LoadSv
import SvGolf.Comb
import tasks.clmul.Spec
import LeanModels.Sv.Loop2Clmul
import LoopTaskE

/-!
# The nested procedural `clmul` satisfies the task statement (WS3, G-L3) — *provisional over `run2`*

The design is `tests/clmul/attacks/proc_nested_for.sv`, loaded through svGolf's own extraction path
(`load_sv`, the task's probe points): one `always_comb`, `p = '0` and the nest
`for i, for j: p[i+j] = p[i+j] ^ (a[i] & b[j])`, retained as `For` nodes. This file is the svGolf
end of the loop proof (`LeanModels/Sv/Loop2Clmul.lean` is the rest of the design-specific part,
`LeanModels/Sv/Loop2.lean` the generic library):

1. `sem N` is the single-process design `clmulBody` over the declarations `a`, `b`, `p`
   (`sem_eq`, one `sv_loop_sem` call: plan item A).
2. Its rows (`sv_loop_rows`) and Bridge S as a task lemma (`CombTask.satisfiedAt_of_loop`,
   `../LoopTask.lean`, plan item C): what remains is the per-state arithmetic.
3. The Spec's `coeff` is the rows' double sum (`coeff_eq`, the reference's collapse).

**Status: provisional over `run2`.** `statement` is the `clmul` `Statement` for every `N ≥ 1`
(after master's `c64ebdac`, which derives the loop fuel from the header: `clmul_loops`).

Build: `cd svgolf && lake env lean design/loop/g1/ClmulNested.lean` (this directory is in no
library).
-/

namespace SvGolf.Design.LoopG1

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Loop2.Clmul LeanModels.Sv.XorSum LeanModels.Sv.Kernel SvGolf
  SvGolf.Tasks.Clmul

load_sv clmulNested from "tests/clmul/attacks/proc_nested_for.sv"

/-! ## 1. `sem N` at symbolic `N` -/

/-- **`sem N` is the single `always_comb` loop process**, for every `N ≥ 1` (`sv_loop_sem`: the
comb chain's declaration stage, the loop instantiated, the guard and the one-driver rule). -/
theorem sem_eq (N : Nat) (h1 : 1 ≤ N) :
    clmulNested.sem N = ⟨clmulNested.pdesign.name, clmulDecls N (2 * N - 1),
      #[.alwaysComb (clmulBody N (2 * N - 1))]⟩ := by
  sv_loop_sem [clmulBody, clmulTrip, tripExpr]

/-! ## 2–3. Bridge S, and the Spec's double sum -/

/-- The Spec's double sum is `cx` (the reference's collapse). -/
theorem coeff_eq (N : Nat) (a b : BitVec N) (k : Nat) : coeff N a b k = cx N a b N k := by
  unfold coeff cx
  simp only [foldl_xor]
  simp

theorem getLsbD_ofBits : ∀ (n : Nat) (f : Nat → Bool) (k : Nat),
    (ofBits n f).getLsbD k = (decide (k < n) && f k)
  | 0, f, k => by simp [ofBits]
  | n + 1, f, k => by
    rw [ofBits, BitVec.getLsbD_append, getLsbD_ofBits n]
    cases k with
    | zero => simp
    | succ k => simp

/-- **The arithmetic** (no backend): from the trips' recurrence (`sv_loop_rows`), the body's meaning
on a state holding known `a` and `b` holds their product: one trip on known values flips bit `i + j`
by `a[i] & b[j]`, so the inner rows add `XOR_j [i + j = m] a[i] b[j]` and the outer rows the double
sum `cx`, which is the Spec's `coeff`. -/
theorem out (N : Nat) (hN : 1 ≤ N) : ∀ st, Loop.LoopInv (clmulNested.sem N) st → ∀ v,
    HoldAll st (task.inputs N) v →
      HoldAll (st.set "p" ((clmulBody N (2 * N - 1)).step "p" st (sig st "p"))) (task.outputs N)
        (task.fn N v) := by
  intro st hinv v hv
  sv_loop_rows (body := clmulBody N (2 * N - 1)) [clmulTrip, tripExpr]
  rw [body_step]
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  have ha : sig st "a" = .ofBitVec x := by simp [sig, hv.1]
  have hb : sig st "b" = .ofBitVec y := by simp [sig, hv.2]
  have hw : (sig st "p").width = 2 * N - 1 :=
    hinv.2 { name := "p", width := 2 * N - 1, isOutput := true } (by rw [sem_eq N hN]; simp [clmulDecls]) rfl
  -- one trip on known values: bit `i + j` flips by `a[i] & b[j]`
  have trip : ∀ (z : BitVec (2 * N - 1)) i j, i < N → j < N → row_in st i j = .ofBitVec z →
      ∃ z' : BitVec (2 * N - 1), row_in st i (j + 1) = .ofBitVec z' ∧ ∀ m, m < 2 * N - 1 →
        z'.getLsbD m = if m = i + j then (z.getLsbD m ^^ (x.getLsbD i && y.getLsbD j))
          else z.getLsbD m := by
    intro z i j hi hj hz
    rw [row_in_step, hz, ha, hb, andBit_known x y hi hj]
    exact xorBit_known z (by omega) _
  -- the inner rows of outer trip `i`, then the outer rows
  have inner : ∀ i, i < N → ∀ z : BitVec (2 * N - 1), row st i = .ofBitVec z → ∀ l, l ≤ N →
      ∃ z' : BitVec (2 * N - 1), row_in st i l = .ofBitVec z' ∧ ∀ m, m < 2 * N - 1 →
        z'.getLsbD m = (z.getLsbD m ^^ bx (fun j => decide (i + j = m) && x.getLsbD i && y.getLsbD j) l) := by
    intro i hi z hz l
    induction l with
    | zero => exact fun _ => ⟨z, by rw [row_in_init, hz], fun m _ => by simp [bx]⟩
    | succ l ih =>
        intro hl
        obtain ⟨z1, h1, b1⟩ := ih (by omega)
        obtain ⟨z2, h2, b2⟩ := trip z1 i l hi (by omega) h1
        refine ⟨z2, h2, fun m hm => ?_⟩
        rw [b2 m hm, b1 m hm]
        simp only [bx]
        by_cases h : m = i + l
        · subst h; simp
        · rw [if_neg h]; simp [show ¬ i + l = m by omega]
  have outer : ∀ k, k ≤ N → ∃ z : BitVec (2 * N - 1), row st k = .ofBitVec z ∧
      ∀ m, m < 2 * N - 1 → z.getLsbD m = cx N x y k m := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨0#(2 * N - 1), by rw [row_init, hw]; simp, fun m _ => by simp [cx, bx]⟩
    | succ k ih =>
        intro hk
        obtain ⟨z1, h1, b1⟩ := ih (by omega)
        obtain ⟨z2, h2, b2⟩ := inner k (by omega) z1 h1 N (Nat.le_refl N)
        exact ⟨z2, by rw [row_next]; exact h2, fun m hm => by rw [b2 m hm, b1 m hm]; rfl⟩
  obtain ⟨z, hz, bz⟩ := outer N (Nat.le_refl N)
  rw [CombGuard.lookup_set_self, hz]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [bz k hk, getLsbD_ofBits, coeff_eq]
  simp [hk]

/-- **The `clmul` task at every `N`** (*provisional over `run2`*): the loop process (`sem_eq`),
Bridge S for a fragment body (`CombTask.satisfiedAt_of_frag`), and `out`. -/
theorem statement : Statement clmulNested.sem := fun N hN => by
  have h := sem_eq N hN
  exact Loop.CombTask.satisfiedAt_of_frag
    (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, clmulDecls, task]) (by rw [h]; rfl)
    (by rw [h]; simp [clmulDecls]) (by rw [h]; simp [clmulDecls]) (by rw [h]; simp [clmulDecls])
    (by rw [h]; sv_frag_ok [clmulTrip, tripExpr, clmulDecls]) (out N hN)

/-- **The `clmul` task over E-core-0 at every `N`** (*derived from E*, Task v2 convention, the E
elaboration of `sem N`): the loop process (`sem_eq`), the single-process slot and the body over E
(`CombTask.satisfiedAt_obs_of_frag`), and `out`. No `run2` in the chain. -/
theorem statement_E0 (ty : Nat → Prop) :
    task.Statement_obs ty Obs_E0 (fun _ => True) fun N => Elab.ofDesign2 (clmulNested.sem N) :=
  fun N hN _ => by
    have h := sem_eq N hN
    exact Loop.CombTask.satisfiedAt_obs_of_frag (W := 2 * N - 1)
      (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, clmulDecls, task]) (by rw [h]; rfl)
      (by rw [h]; simp [clmulDecls]) (by rw [h]; simp [clmulDecls]) (by rw [h]; simp [clmulDecls])
      (by rw [h]; simp [Design2.declWidth, clmulDecls]) (by rw [h]; simp [Design2.inputNames, clmulDecls])
      (by rw [h]; sv_frag_ok [clmulBody, clmulTrip, tripExpr, clmulDecls]) (by simp [task]) (out N hN)

#pin_axioms sem_eq coeff_eq getLsbD_ofBits out statement statement_E0

end SvGolf.Design.LoopG1
