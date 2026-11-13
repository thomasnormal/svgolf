import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

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

/-- The declaration scope: `N`, then the localparams `W = N` and
`MSB = W - 1` (each binding is consed on), all declared `int` (32 bits). -/
def bandScope (N : Int) : IEnv :=
  { vals := [("MSB", N - 1), ("W", N), ("N", N)],
    pwidths := [("N", 32), ("W", 32), ("MSB", 32)] }

/-- The parameter environment (scope plus packed geometry). -/
def bandEnv (N : Int) : IEnv :=
  { bandScope N with dims := dimTable (bandScope N) design.pdesign.decls }

theorem band_paramEnv (N : Int) : design.pdesign.paramEnv2 [N] = .ok (bandEnv N) := rfl

theorem band_buildDecls (N : Int) :
    buildDecls (bandEnv N) design.pdesign.decls = .ok (bandDecls ((N - 1).natAbs + 1)) := by
  simp [design.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    bandEnv, bandScope, List.lookup, bandDecls, Gen2.except_ok_bind]

theorem band_buildElems (N : Int) :
    buildElems (bandEnv N) design.pdesign.decls = .ok bandElems := by
  simp [design.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, bandEnv,
    bandScope, List.lookup, bandElems, Gen2.except_ok_bind]

theorem band_static (N : Nat) (w : Nat) :
    design.pdesign.processes.map
        (instProcess2 ((bandEnv N).withDecls (bandDecls w)) bandElems) = [andProc] := by
  sv2_inst_simp [design.pdesign, bandEnv, bandScope, bandDecls, bandElems, andProc, dimTable,
    dimTableStep, PType.width_packed_cons, PDim.width]

theorem band_instantiate2 (N : Nat) :
    design.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (design.pdesign.assemble2 (bandEnv N) (bandDecls (((N : Int) - 1).natAbs + 1))
        bandElems []) :=
  PDesign.instantiate2_of_ok rfl (band_paramEnv N) (band_buildDecls N) (band_buildElems N)
    (by rw [show design.pdesign.generates = [] from rfl, expandList2_nil])

theorem band_processes (N : Nat) :
    (design.pdesign.instantiateD2 [(N : Int)]).processes.toList = [andProc] := by
  rw [PDesign.instantiateD2_of_ok (band_instantiate2 N), PDesign.assemble2_processes, band_static]
  rfl

/-- The one-driver rule: closed data, decided. -/
theorem band_driversOk :
    driversOk design.pdesign.declNames design.pdesign.inputNames [andProc] = true := by
  decide

/-- `design.sem N` is the instantiated design (its one-driver guard passes). -/
theorem band_sem_eq (N : Nat) : design.sem N = design.pdesign.instantiateD2 [(N : Int)] := by
  show design.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [band_processes]
  exact band_driversOk

theorem band_sem_processes (N : Nat) : (design.sem N).processes.toList = [andProc] := by
  rw [band_sem_eq]
  exact band_processes N

theorem band_sem_decls (N : Nat) (hN : 1 ≤ N) : (design.sem N).decls.toList = bandDecls N := by
  rw [band_sem_eq, PDesign.instantiateD2_of_ok (band_instantiate2 N), PDesign.assemble2_decls]
  have hw : ((N : Int) - 1).natAbs + 1 = N := by omega
  rw [hw]

/-! ## 2. Comb profile and acyclicity -/

theorem band_proc {N j : Nat} {p : Process2} :
    (design.sem N).processes[j]? = some p ↔ j = 0 ∧ p = andProc := by
  rw [← Array.getElem?_toList, band_sem_processes]
  match j with
  | 0 => simp [eq_comm]
  | _ + 1 => simp

theorem band_declWidth_y {N : Nat} (hN : 1 ≤ N) : (design.sem N).declWidth "y" = some N := by
  simp [Design2.declWidth, band_sem_decls N hN, bandDecls]

theorem band_writes {N : Nat} (hN : 1 ≤ N) {j : Nat} {wn : Win} :
    (design.sem N).Writes j wn ↔ j = 0 ∧ wn = ("y", 0, N) := by
  constructor
  · rintro ⟨t, e, hp, hw⟩
    obtain ⟨rfl, h⟩ := band_proc.mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Lhs2.wins, Lhs2.windows?, Lhs2.window?, band_declWidth_y hN] at hw
    exact ⟨rfl, hw⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, _, band_proc.mpr ⟨rfl, rfl⟩,
      by simp [Lhs2.wins, Lhs2.windows?, Lhs2.window?, band_declWidth_y hN]⟩

theorem band_comb {N : Nat} (hN : 1 ≤ N) : CombDesign (design.sem N) where
  nodup := by
    rw [band_sem_decls N hN]
    simp [bandDecls]
  assign := by
    intro j p hp
    obtain ⟨rfl, rfl⟩ := band_proc.mp hp
    exact ⟨_, _, [("y", 0, N)], rfl, by
      simp [Lhs2.windows?, Lhs2.window?, band_declWidth_y hN]⟩
  inWidth := by
    intro j n lo w h
    obtain ⟨-, h⟩ := (band_writes hN).mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, band_declWidth_y hN, by omega⟩
  notInput := by
    rintro n ⟨j, lo, w, h⟩
    obtain ⟨-, h⟩ := (band_writes hN).mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    simp [Design2.inputNames, band_sem_decls N hN, bandDecls]
  disjoint := by
    intro i j wi wj hij hi hj
    obtain ⟨rfl, -⟩ := (band_writes hN).mp hi
    obtain ⟨rfl, -⟩ := (band_writes hN).mp hj
    exact absurd rfl hij
  selfDisjoint := by
    intro j t e hp
    obtain ⟨-, h⟩ := band_proc.mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Lhs2.wins_pairwise_of_leaf (fun _ h => by cases h) _
  rhsFree := by
    intro j t e hp
    obtain ⟨-, h⟩ := band_proc.mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  rhsDeclared := by
    intro j t e hp
    obtain ⟨-, h⟩ := band_proc.mp hp
    simp only [andProc, Process2.assign.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Expr2.idents, band_sem_decls N hN, bandDecls]
  initWidth := by
    intro n _ dc hdc _ v hv
    rw [band_sem_decls N hN] at hdc
    simp [bandDecls] at hdc
    rcases hdc with rfl | rfl | rfl <;> cases hv
  inFourState := by
    intro dc hdc _
    rw [band_sem_decls N hN] at hdc
    simp [bandDecls] at hdc
    rcases hdc with rfl | rfl | rfl <;> rfl

/-- Rank 0 for the one process: it reads `a` and `b`, which nothing writes. -/
theorem band_acyclic {N : Nat} (hN : 1 ≤ N) : Acyclic (design.sem N) := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw hex
  obtain ⟨rfl, h⟩ := band_proc.mp hi
  simp only [andProc, Process2.assign.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨-, rfl⟩ := (band_writes hN).mp ⟨tj, ej, hj, hw⟩
  simp [Expr2.reads, ReadWin.overlaps] at hex

/-! ## 3. The settled state -/

/-- In every shaped solution of the design's equations, known `a`, `b` give
`y = a &&& b`. -/
theorem band_settled {N : Nat} (hN : 1 ≤ N) {st : SvState} (heqs : CombEqs (design.sem N) st)
    (hs : StateShape (design.sem N) st) {x z : BitVec N}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec z)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x &&& z)) := by
  have hy := CombEqs.lookup_ident (band_comb hN) heqs hs (band_proc.mpr ⟨rfl, rfl⟩)
    (evalPure2_and_ofBitVec (evalPure2_ident_ofBitVec ha) (evalPure2_ident_ofBitVec hb))
    (band_declWidth_y hN)
  rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq] at hy
  exact hy

/-! ## 4. The statement -/

theorem band_interface (N : Nat) (hN : 1 ≤ N) :
    SvGolf.Tasks.Example.task.Interface N (design.sem N) := by
  simp [CombTask.Interface, inputPorts, outputPorts, band_sem_decls N hN, bandDecls,
    SvGolf.Tasks.Example.task]

/-- **The solution**: the `_example` statement, for every `N` in range (`1 ≤ N < 2^31`). -/
theorem solution : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN.1
  refine CombTask.satisfiedAt_of_comb (band_interface N hN') (band_comb hN') (band_acyclic hN') ?_
  intro st heqs hs v hv
  obtain ⟨x, z, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Example.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  exact band_settled hN' heqs hs hv.1 hv.2

end Submission
