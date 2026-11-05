import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.Loop2Frag
import LeanModels.Sv.Known2
import LoopTaskE

/-!
# A priority encoder over `N` bits, for every `N` (WS3 loop-shape sizing, design (a)) — *provisional over `run2`*

`prienc.sv`: one `always_comb`, `y = '0; for (int i = 1; i <= N; i++) if (a[i-1]) y = i;` — a
one-level loop with an `if` in the body and a `<=` header against the parameter. The spec is local
(`spec`, not a task, nothing trusted): `y` is the bit length of `a` (`log2 a + 1`, and `0` for
`a = 0`), on 32 bits.

1. `sem N` is the loop process (`sem_eq`, one `sv_loop_sem`; the header `i <= N` from `1`).
2. Its rows (`sv_loop_rows`): `row_step` is the plain equation
   `row st (k + 1) = if ((sig st "a").extract k 1).condTrue = true then
     (LVec.ofInt 32 (1 + k)).resizeU (row st k).width else row st k`.
3. Bridge S as a task lemma, then the arithmetic: row `k` is one plus the highest set index below
   `k` (`hi`), and at `k = N` that is the bit length.

Build: `compile-loop.sh` (this directory is in no library).
-/

namespace SvGolf.Design.LoopG2.PriEnc

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Kernel SvGolf

load_sv prienc from "design/loop/g2/prienc.sv" (top := "prienc") (probes := "N=1;N=8")

/-- **The local spec**: `y` is the bit length of `a`, on 32 bits. -/
def spec : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N)]
  outputs _ := [("y", 32)]
  fn _ := fun (a, ()) => (BitVec.ofNat 32 (if a.toNat = 0 then 0 else a.toNat.log2 + 1), ())

/-- Trip `k` of the instantiated loop (iterator value `1 + k`): `if (a[k]) y = 1 + k`. -/
def trip (k : Nat) : Stmt2 :=
  .ifStmt (.slice (.ident "a") k 1)
    (.blockingAssign (.ident "y") (.lit (LVec.ofInt 32 (1 + (k : Int))))) none

def body (N : Nat) : Stmt2 := initLoop "y" (LVec.replicate 32 .l0) N trip

def decls (N : Nat) : Array Decl :=
  #[{ name := "a", width := N, isInput := true }, { name := "y", width := 32, isOutput := true }]

theorem sem_eq (N : Nat) (h1 : 1 ≤ N) :
    prienc.sem N = ⟨prienc.pdesign.name, decls N, #[.alwaysComb (body N)]⟩ := by
  sv_loop_sem [body, trip]

/-- One plus the highest set index of `x` below `k`, `0` when there is none. -/
def hi {N : Nat} (x : BitVec N) : Nat → Nat
  | 0 => 0
  | k + 1 => if x.getLsbD k then k + 1 else hi x k

theorem hi_spec {N : Nat} (x : BitVec N) : ∀ k, (hi x k = 0 ∧ ∀ i, i < k → x.getLsbD i = false) ∨
    ∃ h, hi x k = h + 1 ∧ h < k ∧ x.getLsbD h = true ∧ ∀ i, h < i → i < k → x.getLsbD i = false
  | 0 => .inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1 => by
      by_cases hk : x.getLsbD k
      · exact .inr ⟨k, by simp [hi, hk], by omega, hk, fun i _ _ => by omega⟩
      · have hk' : ∀ i, i < k + 1 → (i < k → x.getLsbD i = false) → x.getLsbD i = false :=
          fun i hi hl => if h : i < k then hl h else by rw [show i = k by omega]; simpa using hk
        rcases hi_spec x k with ⟨h0, hz⟩ | ⟨h, h1, h2, h3, h4⟩
        · exact .inl ⟨by simp [hi, hk, h0], fun i hi => hk' i hi (hz i)⟩
        · exact .inr ⟨h, by simp [hi, hk, h1], by omega, h3, fun i hi hi' => hk' i hi' (h4 i hi)⟩

/-- At `k = N`, `hi` is the bit length. -/
theorem hi_eq {N : Nat} (x : BitVec N) :
    hi x N = if x.toNat = 0 then 0 else x.toNat.log2 + 1 := by
  rcases hi_spec x N with ⟨h0, hz⟩ | ⟨h, h1, h2, h3, h4⟩
  · have : x = 0#N := BitVec.eq_of_getLsbD_eq fun i hi => by simp [hz i hi]
    rw [h0]; simp [this]
  · have hge : 2 ^ h ≤ x.toNat := Nat.ge_two_pow_of_testBit (by simpa [BitVec.testBit_toNat] using h3)
    have hne : x.toNat ≠ 0 := by have := Nat.one_le_two_pow (n := h); omega
    rw [if_neg hne, h1, (Nat.log2_eq_iff hne).mpr ⟨hge, Nat.lt_pow_two_of_testBit _ fun i hi => ?_⟩]
    rw [BitVec.testBit_toNat]
    by_cases hiN : i < N
    · exact h4 i (by omega) hiN
    · exact BitVec.getLsbD_of_ge x i (by omega)

/-- **The arithmetic** (no backend): the body's meaning on a state holding a known `a`. -/
theorem out (N : Nat) (hN : 1 ≤ N) : ∀ st, Loop.LoopInv (prienc.sem N) st → ∀ v,
    HoldAll st (spec.inputs N) v →
      HoldAll (st.set "y" ((body N).step "y" st (sig st "y"))) (spec.outputs N) (spec.fn N v) := by
  intro st hinv v hv
  sv_loop_rows (body := body N) [trip]
  rw [body_step]
  obtain ⟨x, ⟨⟩⟩ := v
  simp only [spec, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  have ha : sig st "a" = .ofBitVec x := by simp [sig, hv]
  have hw : (sig st "y").width = 32 :=
    hinv.2 { name := "y", width := 32, isOutput := true } (by rw [sem_eq N hN]; simp [decls]) rfl
  have rows : ∀ k, k ≤ N → row st k = .ofBitVec (BitVec.ofNat 32 (hi x k)) := by
    intro k
    induction k with
    | zero => intro _; rw [row_init, hw]; simp [hi]
    | succ k ih =>
        intro hk
        rw [row_step, ih (by omega), ha, LVec.extract_one_ofBitVec x (by omega), hi]
        cases x.getLsbD k
        · simp
        · simp [LVec.ofInt]
          apply BitVec.eq_of_toNat_eq
          simp only [show ∀ a b : Int, a.emod b = a % b from fun _ _ => rfl]
          simp
          omega
  rw [CombGuard.lookup_set_self, rows N (Nat.le_refl N), hi_eq]

/-- The task at every `N` (*provisional over `run2`*). -/
theorem statement : spec.Statement prienc.sem := fun N hN => by
  have h := sem_eq N hN
  exact Loop.CombTask.satisfiedAt_of_frag
    (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, decls, spec]) (by rw [h]; rfl)
    (by rw [h]; simp [decls]) (by rw [h]; simp [decls]) (by rw [h]; simp [decls])
    (by rw [h]; sv_frag_ok [trip, decls]) (out N hN)

/-- **The task over E-core-0 at every `N`** (*derived from E*, Task v2 convention, the E elaboration
of `sem N`; `CombTask.satisfiedAt_obs_of_frag`). No `run2` in the chain. -/
theorem statement_E0 (ty : Nat → Prop) :
    spec.Statement_obs ty Obs_E0 (fun _ => True) fun N => Elab.ofDesign2 (prienc.sem N) :=
  fun N hN _ => by
    have h := sem_eq N hN
    exact Loop.CombTask.satisfiedAt_obs_of_frag (W := 32)
      (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, decls, spec]) (by rw [h]; rfl)
      (by rw [h]; simp [decls]) (by rw [h]; simp [decls]) (by rw [h]; simp [decls])
      (by rw [h]; simp [Design2.declWidth, decls]) (by rw [h]; simp [Design2.inputNames, decls])
      (by rw [h]; sv_frag_ok [body, trip, decls]) (by simp [spec]) (out N hN)

#pin_axioms sem_eq hi_spec hi_eq out statement statement_E0

end SvGolf.Design.LoopG2.PriEnc
