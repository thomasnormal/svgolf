import SvGolf.LoadSv
import SvGolf.Comb
import LeanModels.Sv.Loop2Frag
import LeanModels.Sv.Known2
import LoopTaskE

/-!
# Population count over `N` bits, for every `N` (WS3 loop-shape sizing, design (b)) — *provisional over `run2`*

`popcnt.sv`: one `always_comb`, `cnt = '0; for (int i = 0; i < N; i++) cnt = cnt + a[i];` — a
one-level arithmetic accumulator, the accumulator 32 bits wide. The spec is local (`spec`, not a task,
nothing trusted): `cnt` is the number of set bits of `a`, on 32 bits.

1. `sem N` is the loop process (`sem_eq`, one `sv_loop_sem`).
2. Its rows (`sv_loop_rows`): `row_step` is the plain equation
   `row st (k + 1) = ((row st k).add (((sig st "a").extract k 1).resizeU 32)).resizeU (row st k).width`.
3. Bridge S as a task lemma (`Loop.CombTask.satisfiedAt_of_loop`), then the arithmetic: row `k`
   holds the count of the set bits below `k`.

Build: `compile-loop.sh` (this directory is in no library).
-/

namespace SvGolf.Design.LoopG2.PopCount

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Kernel SvGolf

load_sv popcnt from "design/loop/g2/popcnt.sv" (top := "popcnt") (probes := "N=1;N=8")

/-- **The local spec**: `cnt` is the number of set bits of `a`, on 32 bits. -/
def spec : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N)]
  outputs _ := [("cnt", 32)]
  fn N := fun (a, ()) => (BitVec.ofNat 32 ((List.range N).countP fun i => a.getLsbD i), ())

/-- Trip `k` of the instantiated loop: `cnt = cnt + a[k]`. -/
def trip (k : Nat) : Stmt2 :=
  .blockingAssign (.ident "cnt") (.binary .add (.ident "cnt") (.resize 32 (.slice (.ident "a") k 1)))

def body (N : Nat) : Stmt2 := initLoop "cnt" (LVec.replicate 32 .l0) N trip

def decls (N : Nat) : Array Decl :=
  #[{ name := "a", width := N, isInput := true }, { name := "cnt", width := 32, isOutput := true }]

theorem sem_eq (N : Nat) (h1 : 1 ≤ N) :
    popcnt.sem N = ⟨popcnt.pdesign.name, decls N, #[.alwaysComb (body N)]⟩ := by
  sv_loop_sem [body, trip]

/-- **The arithmetic** (no backend): the body's meaning on a state holding a known `a`. -/
theorem out (N : Nat) (hN : 1 ≤ N) : ∀ st, Loop.LoopInv (popcnt.sem N) st → ∀ v,
    HoldAll st (spec.inputs N) v →
      HoldAll (st.set "cnt" ((body N).step "cnt" st (sig st "cnt"))) (spec.outputs N) (spec.fn N v) := by
  intro st hinv v hv
  sv_loop_rows (body := body N) [trip]
  rw [body_step]
  obtain ⟨x, ⟨⟩⟩ := v
  simp only [spec, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  have ha : sig st "a" = .ofBitVec x := by simp [sig, hv]
  have hw : (sig st "cnt").width = 32 :=
    hinv.2 { name := "cnt", width := 32, isOutput := true } (by rw [sem_eq N hN]; simp [decls]) rfl
  have rows : ∀ k, k ≤ N →
      row st k = .ofBitVec (BitVec.ofNat 32 ((List.range k).countP fun i => x.getLsbD i)) := by
    intro k
    induction k with
    | zero => intro _; rw [row_init, hw]; simp
    | succ k ih =>
        intro hk
        rw [row_step, ih (by omega), ha, LVec.extract_one_ofBitVec x (by omega)]
        simp only [LVec.resizeU_ofBitVec, evalBinOp_add, LVec.add_ofBitVec, LVec.width_ofBitVec,
          List.range_succ, List.countP_append]
        congr 1
        apply BitVec.eq_of_toNat_eq
        by_cases hb : x.getLsbD k <;> simp [hb] <;> omega
  rw [CombGuard.lookup_set_self, rows N (Nat.le_refl N)]

/-- The task at every `N` (*provisional over `run2`*). -/
theorem statement : spec.Statement popcnt.sem := fun N hN => by
  have h := sem_eq N hN
  exact Loop.CombTask.satisfiedAt_of_frag
    (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, decls, spec]) (by rw [h]; rfl)
    (by rw [h]; simp [decls]) (by rw [h]; simp [decls]) (by rw [h]; simp [decls])
    (by rw [h]; sv_frag_ok [trip, decls]) (out N hN)

/-- **The task over E-core-0 at every `N`** (*derived from E*, Task v2 convention, the E elaboration
of `sem N`; `CombTask.satisfiedAt_obs_of_frag`). No `run2` in the chain. -/
theorem statement_E0 (ty : Nat → Prop) :
    spec.Statement_obs ty Obs_E0 (fun _ => True) fun N => Elab.ofDesign2 (popcnt.sem N) :=
  fun N hN _ => by
    have h := sem_eq N hN
    exact Loop.CombTask.satisfiedAt_obs_of_frag (W := 32)
      (by rw [h]; simp [CombTask.Interface, inputPorts, outputPorts, decls, spec]) (by rw [h]; rfl)
      (by rw [h]; simp [decls]) (by rw [h]; simp [decls]) (by rw [h]; simp [decls])
      (by rw [h]; simp [Design2.declWidth, decls]) (by rw [h]; simp [Design2.inputNames, decls])
      (by rw [h]; sv_frag_ok [body, trip, decls]) (by simp [spec]) (out N hN)

#pin_axioms sem_eq out statement statement_E0

end SvGolf.Design.LoopG2.PopCount
