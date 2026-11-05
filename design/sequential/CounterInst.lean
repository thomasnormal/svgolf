import CounterCycle
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# The counter's instantiation at symbolic `N` (SPIKE, 2026-11-03)

`CounterCycle.lean` proves the sequential statement for the hand-built family `cntD`, and checks
`cntD N = cnt.sem N` only by `#guard` at seven concrete `N`. This file closes that gap: for EVERY
`N ≥ 1`, the design `load_sv` (and `load_design_sv2`) produces from `cnt.sv` IS `cntD N`
(`cnt_sem_eq`), so `cnt_statement` holds of the loaded family itself (`cnt_statement_sem`).

Route: the add reference's (`tasks/add/reference/add_n_byhand.lean`, section 1c): `instantiate2`
split by `PDesign.instantiate2_of_ok` into the parameter, declaration, element-width and generate
stages, each computed at symbolic `N` by `simp`; the static `always_ff` process lowered by the
`sv2_inst_simp` recipe; the one-driver guard of `instantiateGD2` discharged. The only new piece
compared to the combinational references is the lowering of an `always_ff` body (`instStmt2` on
`if`/nonblocking assignments), which turns out to be the same `simp` recipe.
-/

namespace SvGolf.Seq.Counter

open LeanModels.Sv

/-! ## The stages of `instantiate2` at symbolic `N` -/

/-- The declaration scope: `N` bound, its declared type `int` 32 bits. -/
def cntScope (N : Int) : IEnv := { vals := [("N", N)], pwidths := [("N", 32)] }

/-- The parameter environment (scope plus the packed-geometry table). -/
def cntEnv (N : Int) : IEnv :=
  { cntScope N with dims := dimTable (cntScope N) cntSv.pdesign.decls }

/-- The declarations at the raw width `w = |N-1| + 1` of `q`. -/
def cntDeclsRaw (w : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true },
   { name := "rst", width := 1, isInput := true },
   { name := "en", width := 1, isInput := true },
   { name := "q", width := w, isOutput := true }]

/-- Every declaration is 1-D: element width 1. -/
def cntElems : List (String × Nat) := [("clk", 1), ("rst", 1), ("en", 1), ("q", 1)]

/-- The counter's process at register width `w`. -/
def cntProc (w : Nat) : Process2 :=
  .alwaysFF "clk"
    (.ifStmt (.ident "rst")
      (.nbaAssign (.ident "q") (.lit (LVec.replicate w .l0)))
      (some (.ifStmt (.ident "en")
        (.nbaAssign (.ident "q")
          (.binary .add (.ident "q") (.resize w (.lit ⟨#[.l1]⟩))))
        none)))

theorem cnt_paramEnv (N : Int) : cntSv.pdesign.paramEnv2 [N] = .ok (cntEnv N) := by
  rfl

theorem cnt_decls (N : Int) :
    buildDecls (cntEnv N) cntSv.pdesign.decls = .ok (cntDeclsRaw ((N - 1).natAbs + 1)) := by
  simp [cntSv.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    cntEnv, cntScope, List.lookup, cntDeclsRaw, Gen2.except_ok_bind]

theorem cnt_elems (N : Int) : buildElems (cntEnv N) cntSv.pdesign.decls = .ok cntElems := by
  simp [cntSv.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, cntEnv,
    cntScope, List.lookup, cntElems, Gen2.except_ok_bind]

/-- The static process: the `always_ff` body lowered at register width `w ≥ 1` (the `+ 1'b1`
operand is widened to `w`: `fitExpr2`'s one inserted node). -/
theorem cnt_static (N : Nat) (w : Nat) (hw : 1 ≤ w) :
    cntSv.pdesign.processes.map
        (instProcess2 ((cntEnv N).withDecls (cntDeclsRaw w)) cntElems) = [cntProc w] := by
  sv2_inst_simp [instStmt2, cntSv.pdesign, cntEnv, cntScope, cntDeclsRaw, cntElems, cntProc,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, hw]

theorem cnt_gens (N : Nat) (w : Nat) :
    expandList2 ((cntEnv N).withDecls (cntDeclsRaw w)) cntElems
      (PDesign.surfaceFuel [(N : Int)]) cntSv.pdesign.generates = .ok [] := by
  rw [show cntSv.pdesign.generates = [] from rfl, expandList2_nil]

theorem cnt_instantiate2 (N : Nat) :
    cntSv.pdesign.instantiate2 [(N : Int)] (PDesign.surfaceFuel [(N : Int)]) =
      .ok (cntSv.pdesign.assemble2 (cntEnv N) (cntDeclsRaw (((N : Int) - 1).natAbs + 1))
        cntElems []) :=
  PDesign.instantiate2_of_ok rfl (cnt_paramEnv N) (cnt_decls N) (cnt_elems N) (cnt_gens N _)

/-! ## The loaded family is `cntD`, for every `N ≥ 1` -/

theorem cnt_processes (N : Nat) :
    (cntSv.pdesign.instantiateD2 [(N : Int)]).processes.toList =
      [cntProc (((N : Int) - 1).natAbs + 1)] := by
  rw [PDesign.instantiateD2_of_ok (cnt_instantiate2 N), PDesign.assemble2_processes,
    cnt_static N _ (by omega)]
  simp [cntSv.pdesign]

/-- The one-driver rule: one procedural process writes `q`, nothing else drives anything. -/
theorem cnt_driversOk (w : Nat) :
    driversOk cntSv.pdesign.declNames cntSv.pdesign.inputNames [cntProc w] = true := by
  rfl

theorem cnt_sem_eq_inst (N : Nat) :
    cntSv.sem N = cntSv.pdesign.instantiateD2 [(N : Int)] := by
  show cntSv.pdesign.instantiateGD2 [(N : Int)] = _
  apply PDesign.instantiateGD2_of_driversOk
  rw [cnt_processes]
  exact cnt_driversOk _

/-- **The loaded design is the hand-built family, for every `N ≥ 1`.** -/
theorem cnt_sem_eq (N : Nat) (hN : 1 ≤ N) : cntSv.sem N = cntD N := by
  have hw : ((N : Int) - 1).natAbs + 1 = N := by omega
  rw [cnt_sem_eq_inst, PDesign.instantiateD2_of_ok (cnt_instantiate2 N), hw]
  simp only [PDesign.assemble2, cnt_static N N hN, cntD, cntProc]
  simp [cntSv.pdesign, cntDeclsRaw]

/-- **The counter's statement holds of the loaded family**, for every `N` in range. -/
theorem cnt_statement_sem : cntTask.Statement cntSv.sem := fun N hN => by
  rw [cnt_sem_eq N hN]
  exact cnt_statement N hN

#print axioms cnt_sem_eq
#print axioms cnt_statement_sem

end SvGolf.Seq.Counter
