-- MAINTAINER PORT (2026-11-16): the svGolf maintainers' port of the player's proof to the checker at Proglib 4fcda4c8 (Lean v4.35.0); the design is the player's, byte for byte, and the player's own proof is in the record this one replaces (the repository's history). The lines below say what changed versus the player's file.
-- pin2 port (Proglib 32756c0b, Lean v4.35.0): the hand-written stages of instantiate2 (the parameter environment, now at the exact 32-bit int values) replaced by sv_mirror's generated instantiation (band_sem_eq through SvGolf.Cycle.sem_eq_of_mirror, to the generated mirror), and the range premise hR : N < 2 ^ 31 threaded to band_proc and its users; the rest of the proof unchanged.
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import SvGolf.Cycle

/-!
# One AND gate per bit for task `_example`, LOCALPARAM variant: the proof

This is a submission file like any player's `Solution.lean`. The checker
generates the module `Submission.Design`, which loads the player's envelope as
`Submission.design` and names the statement to prove `Submission.Goal`
(`SvGolf.Tasks.Example.Statement Submission.design.sem`). This file proves

    theorem Submission.solution : Submission.Goal

for EVERY `N` of the task's range (`1 ≤ N < 2^31`), for `band_lp.sv`: the design of `band.lean`
(`assign y = a & b;`) with a header localparam `W = N` that sizes the ports
and a body localparam `MSB = W - 1`. The only difference from `band.lean` is
the parameter environment (`bandScope`): the localparams are bound after `N`,
each to its value at symbolic `N`, and the port widths read `W`. It is a
regression for the checker (localparams are not task parameters).

Route (the `Examples/system-verilog/ripple_add` recipe, copied here because
svGolf does not import `Examples`):

1. **The design at symbolic `N`** (`band_sem_processes`, `band_sem_decls`):
   `instantiate2` split into its stages by `PDesign.instantiate2_of_ok`, the
   one-driver guard of `name.sem` discharged by `driversOk` on the (closed)
   process list.
2. **The comb profile and acyclicity** (`band_comb`, `band_acyclic`): one
   whole-signal assign; it reads `a`, `b`, which no process writes.
3. **The settled state** (`band_settled`): in a solution of the equations,
   known `a b : BitVec N` give `y = a &&& b` (`CombEqs.lookup_ident` and the
   `Known2` calculus).
4. **The statement** (`solution`): `CombTask.satisfiedAt_of_comb`
   (`SvGolf/Comb.lean`) reduces it to the interface and step 3.
-/

namespace Submission

open LeanModels.Sv SvGolf

/-! ## 1. The design at symbolic `N` -/

/-- The one process: `assign y = a & b;`. -/
def andProc : Process2 := .assign (.ident "y") (.binary .and (.ident "a") (.ident "b"))

/-- The instantiated declarations at raw port width `w` (`|N - 1| + 1`). -/
def bandDecls (w : Nat) : List Decl :=
  [{ name := "a", width := w, isInput := true },
   { name := "b", width := w, isInput := true },
   { name := "y", width := w, isOutput := true }]

/-- Every declaration is 1-D: element width 1. -/
def bandElems : List (String × Nat) := [("a", 1), ("b", 1), ("y", 1)]

-- (port) The instantiation, generated (`SvGolf.Cycle`'s `sv_mirror`): the parameter environment at the exact 32-bit
-- `int` values of `N`, `W = N` and `MSB = W - 1`, the declarations and the one process.
sv_mirror bandG := design (N : Nat) (hN : 1 ≤ N) (hN32 : N < 2147483648)

/-- The one-driver rule: closed data, decided. -/
theorem band_driversOk :
    driversOk design.pdesign.declNames design.pdesign.inputNames [andProc] = true := by
  decide

/-- `design.sem N` is the generated mirror (its one-driver guard and its alias guard pass), for `N` below `2^31`. -/
theorem band_sem_eq (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 31) : design.sem N = bandG.D N :=
  SvGolf.Cycle.sem_eq_of_mirror (bandG.instantiate N hN hR) rfl
    (by simpa [bandG.D, bandG.procs, bandG.p0, andProc] using band_driversOk)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by simp [bandG.D, bandG.procs, bandG.p0, SvGolf.Cycle.notComb]))

theorem band_sem_processes (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 31) :
    (design.sem N).processes.toList = [andProc] := by
  rw [band_sem_eq N hN hR]
  rfl

theorem band_sem_decls (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 31) : (design.sem N).decls.toList = bandDecls N := by
  rw [band_sem_eq N hN hR]
  rfl

/-! ## 2. Comb profile and acyclicity -/

theorem band_proc {N j : Nat} {p : Process2} (hN : 1 ≤ N) (hR : N < 2 ^ 31) :
    (design.sem N).processes[j]? = some p ↔ j = 0 ∧ p = andProc := by
  rw [← Array.getElem?_toList, band_sem_processes N hN hR]
  match j with
  | 0 => simp [eq_comm]
  | _ + 1 => simp

theorem band_declWidth_y {N : Nat} (hN : 1 ≤ N) (hR : N < 2 ^ 31) : (design.sem N).declWidth "y" = some N := by
  simp [Design2.declWidth, band_sem_decls N hN hR, bandDecls]

theorem band_writes {N : Nat} (hN : 1 ≤ N) (hR : N < 2 ^ 31) {j : Nat} {wn : Win} :
    (design.sem N).Writes j wn ↔ j = 0 ∧ wn = ("y", 0, N) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := (band_proc hN hR).mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Lhs2.wins, Lhs2.windows?, Lhs2.window?, band_declWidth_y hN hR] at hw
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, _, (band_proc hN hR).mpr ⟨rfl, rfl⟩,
      by simp [Lhs2.wins, Lhs2.windows?, Lhs2.window?, band_declWidth_y hN hR]⟩

theorem band_comb {N : Nat} (hN : 1 ≤ N) (hR : N < 2 ^ 31) : CombDesign (design.sem N) where
  nodup := by
    rw [band_sem_decls N hN hR]
    simp [bandDecls]
  assign := by
    intro j p hp
    obtain ⟨rfl, rfl⟩ := (band_proc hN hR).mp hp
    exact ⟨_, _, [("y", 0, N)], rfl, by
      simp [Lhs2.windows?, Lhs2.window?, band_declWidth_y hN hR]⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨-, h⟩ := (band_writes hN hR).mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, band_declWidth_y hN hR, by omega⟩
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨-, h⟩ := (band_writes hN hR).mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    simp [Design2.inputNames, band_sem_decls N hN hR, bandDecls]
  disjoint := by
    intro i j wi wj hij hi hj
    obtain ⟨rfl, -⟩ := (band_writes hN hR).mp hi
    obtain ⟨rfl, -⟩ := (band_writes hN hR).mp hj
    exact absurd rfl hij
  selfDisjoint := by
    intro j t e hp
    obtain ⟨-, h⟩ := (band_proc hN hR).mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    obtain ⟨-, h⟩ := (band_proc hN hR).mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro j t e hp
    obtain ⟨-, h⟩ := (band_proc hN hR).mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.idents, band_sem_decls N hN hR, bandDecls]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [band_sem_decls N hN hR] at hdc
    simp [bandDecls] at hdc
    rcases hdc with rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [band_sem_decls N hN hR] at hdc
    simp [bandDecls] at hdc
    rcases hdc with rfl | rfl | rfl <;> rfl

/-- Rank 0 for the one process: it reads `a` and `b`, which nothing writes. -/
theorem band_acyclic {N : Nat} (hN : 1 ≤ N) (hR : N < 2 ^ 31) : Acyclic (design.sem N) := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  obtain ⟨rfl, h⟩ := (band_proc hN hR).mp hi
  simp only [andProc, Process2.assign.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨-, rfl⟩ := (band_writes hN hR).mp ⟨tj, ej, hj, hw⟩
  simp [Expr2.reads, ReadWin.overlaps] at hex

/-! ## 3. The settled state -/

/-- In every shaped solution of the design's equations, known `a`, `b` give
`y = a &&& b`. -/
theorem band_settled {N : Nat} (hN : 1 ≤ N) (hR : N < 2 ^ 31) {st : SvState} (heqs : CombEqs (design.sem N) st)
    (hs : StateShape (design.sem N) st) {x z : BitVec N}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec z)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x &&& z)) := by
  have hy := CombEqs.lookup_ident (band_comb hN hR) heqs hs ((band_proc hN hR).mpr ⟨rfl, rfl⟩)
    (evalPure2_and_ofBitVec (evalPure2_ident_ofBitVec ha) (evalPure2_ident_ofBitVec hb))
    (band_declWidth_y hN hR)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hy
  exact hy

/-! ## 4. The statement -/

theorem band_interface (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 31) :
    SvGolf.Tasks.Example.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, band_sem_decls N hN hR, bandDecls,
    SvGolf.Tasks.Example.task]

/-- **The solution**: the `_example` statement, for every `N` in range (`1 ≤ N < 2^31`). -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  have hR : N < 2 ^ 31 := hN.2
  refine CombTask.satisfiedAt_of_comb (band_interface N hN' hR) (band_comb hN' hR) (band_acyclic hN' hR) ?_
  intro st heqs hs v hv
  obtain ⟨x, z, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Example.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  exact band_settled hN' hR heqs hs hv.1 hv.2

end Submission
