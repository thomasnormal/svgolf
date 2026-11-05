import SvGolf.Comb
import SvGolf.LoadSv
import tasks._example.Spec
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# Task `_example`: the negative designs do NOT satisfy the statement

Kernel-checked refutations, one per design in this directory that the
statement must reject (`README.md` lists them all, with the banlist case).
They are the non-vacuity evidence for `tasks/_example/Spec.lean`: each
targets one way a weaker statement could be satisfied without computing
`a &&& b`, and each is refuted at the smallest width, `N = 1`.

* a wrong function (`or_gate.sv`) and a design that reads an undriven net
  (`reads_x.sv`) are refuted by ONE concrete run whose snapshot disagrees
  with the task (`CombTask.not_computes_of_counterexample`; the run of the
  instantiated design is evaluated by `decide +kernel`, standard axioms only);
* a wrong output width (`wide_out.sv`) and a hidden extra input
  (`extra_in.sv`) are refuted by the interface conjunct, on the instantiated
  declarations.

The kernel cannot evaluate `PDesign.instantiate2` itself (the declaration
width stage does not reduce), so each design is first instantiated at
`N = 1` by the symbolic route of the reference proof (`sem1_eq`,
`decls1_eq`: `PDesign.instantiate2_of_ok`, `simp` on the stages), and only
the run of the resulting hand-readable `Design2` is evaluated.

The designs are loaded with `load_sv` (`SvGolf/LoadSv.lean`): extracted at
elaboration time by svGolf's one extraction path (the source gate, then the
pinned extractor with the task's probe points, as `check.py` does) into a
cache under `.lake/envelopes/`; paths are relative to the `svgolf/` package
root, the working directory of `lake build`.
-/

namespace SvGolf.Tasks.Example.Negative

open LeanModels.Sv SvGolf

load_sv orGate from "tests/_example/negative/or_gate.sv"
load_sv wideOut from "tests/_example/negative/wide_out.sv"
load_sv extraIn from "tests/_example/negative/extra_in.sv"
load_sv readsX from "tests/_example/negative/reads_x.sv"

/-! ## Instantiation at `N = 1` -/

/-- The parameter environment at `N = 1` (an `int` parameter `N`). -/
def envAt1 (pd : PDesign) : IEnv :=
  { vals := [("N", 1)], pwidths := [("N", 32)],
    dims := dimTable { vals := [("N", 1)], pwidths := [("N", 32)] } pd.decls }

/-- The declarations of `pd.instantiateGD2 [1]` (no generate items): the
driver guard keeps the declarations. -/
theorem decls1_eq {pd : PDesign} {decls : List Decl} {elems : List (String × Nat)}
    (harity : [(1 : Int)].length = pd.params.length) (h1 : pd.paramEnv2 [1] = .ok (envAt1 pd))
    (h2 : buildDecls (envAt1 pd) pd.decls = .ok decls)
    (h3 : buildElems (envAt1 pd) pd.decls = .ok elems) (h4 : pd.generates = []) :
    (pd.instantiateGD2 [1]).decls.toList = decls := by
  rw [PDesign.instantiateGD2_eq_driverGuard, PDesign.instantiateD2_of_ok
    (PDesign.instantiate2_of_ok harity h1 h2 h3 (by rw [h4, expandList2_nil]))]
  unfold PDesign.driverGuard Design2.driverGuard
  split <;> simp

/-- The whole of `pd.instantiateGD2 [1]` (no generate items, no loud
`others`, the one-driver rule holds): name, declarations, processes. -/
theorem sem1_eq {pd : PDesign} {decls : List Decl} {elems : List (String × Nat)}
    {procs : List Process2}
    (harity : [(1 : Int)].length = pd.params.length) (h1 : pd.paramEnv2 [1] = .ok (envAt1 pd))
    (h2 : buildDecls (envAt1 pd) pd.decls = .ok decls)
    (h3 : buildElems (envAt1 pd) pd.decls = .ok elems) (h4 : pd.generates = [])
    (h5 : pd.processes.map (instProcess2 ((envAt1 pd).withDecls decls) elems) = procs)
    (h6 : pd.others = []) (hok : driversOk pd.declNames pd.inputNames procs = true) :
    pd.instantiateGD2 [1] = { name := pd.name, decls := decls.toArray, processes := procs.toArray } := by
  have hi := PDesign.instantiate2_of_ok (F := PDesign.surfaceFuel [1]) harity h1 h2 h3
    (by rw [h4, expandList2_nil])
  have hD : pd.assemble2 (envAt1 pd) decls elems [] =
      { name := pd.name, decls := decls.toArray, processes := procs.toArray } := by
    simp [PDesign.assemble2, h5, h6]
  have hok' : driversOk pd.declNames pd.inputNames (pd.instantiateD2 [1]).processes.toList = true := by
    rw [PDesign.instantiateD2_of_ok hi, hD]
    simpa using hok
  rw [PDesign.instantiateGD2_of_driversOk hok', PDesign.instantiateD2_of_ok hi, hD]

/-- The 1-bit ports `a`, `b` (inputs) and `y` (output). -/
def abyDecls : List Decl :=
  [{ name := "a", width := 1, isInput := true },
   { name := "b", width := 1, isInput := true },
   { name := "y", width := 1, isOutput := true }]

/-- Every declaration 1-D (element width 1), for the given names. -/
def elems1 (names : List String) : List (String × Nat) := names.map (·, 1)

/-! ## Wrong function: `y = a | b` -/

/-- `or_gate` at `N = 1`. -/
def orD : Design2 :=
  { name := "band", decls := abyDecls.toArray,
    processes := #[.assign (.ident "y") (.binary .or (.ident "a") (.ident "b"))] }

theorem orGate_sem1 : orGate.sem 1 = orD := by
  show orGate.pdesign.instantiateGD2 [1] = _
  refine (sem1_eq (elems := elems1 ["a", "b", "y"]) rfl rfl ?_ ?_ rfl ?_ rfl (by decide)).trans rfl
  · simp [orGate.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, abyDecls, Gen2.except_ok_bind]
  · simp [orGate.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [orGate.pdesign, envAt1, abyDecls, elems1, dimTable, dimTableStep,
      PType.width_packed_cons, PDim.width]

/-- `y = a | b` is not `a &&& b`: at `N = 1`, `a = 1`, `b = 0` the snapshot
has `y = 1`. -/
theorem orGate_refuted : ¬ Statement orGate.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [orGate_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (1#1, 0#1, ())) (by simp [task]) (by decide +kernel) hc

/-! ## Reads an undriven net: `y = a & b & ~z` -/

/-- `reads_x` at `N = 1` (`z` is an undriven internal net). -/
def readsXD : Design2 :=
  { name := "band",
    decls := (abyDecls ++ [({ name := "z", width := 1 } : Decl)]).toArray,
    processes := #[.assign (.ident "y")
      (.binary .and (.binary .and (.ident "a") (.ident "b")) (.unary .bnot (.ident "z")))] }

theorem readsX_sem1 : readsX.sem 1 = readsXD := by
  show readsX.pdesign.instantiateGD2 [1] = _
  refine (sem1_eq (elems := elems1 ["a", "b", "y", "z"]) rfl rfl ?_ ?_ rfl ?_ rfl (by decide)).trans rfl
  · simp [readsX.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, abyDecls, Gen2.except_ok_bind]
  · simp [readsX.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [readsX.pdesign, envAt1, abyDecls, elems1, dimTable, dimTableStep,
      PType.width_packed_cons, PDim.width, rigidMax2, selfWidth2]

/-- An undriven net reads `x`: at `N = 1`, `a = b = 1`, `y = 1 & 1 & ~x = x`. -/
theorem readsX_refuted : ¬ Statement readsX.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [readsX_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (1#1, 1#1, ())) (by simp [task]) (by decide +kernel) hc

/-! ## Wrong output width: `output logic [N:0] y` -/

theorem wideOut_decls1 :
    (wideOut.sem 1).decls.toList =
      [{ name := "a", width := 1, isInput := true }, { name := "b", width := 1, isInput := true },
       { name := "y", width := 2, isOutput := true }] := by
  show (wideOut.pdesign.instantiateGD2 [1]).decls.toList = _
  refine decls1_eq (elems := elems1 ["a", "b", "y"]) rfl rfl ?_ ?_ rfl
  · simp [wideOut.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, Gen2.except_ok_bind]
  · simp [wideOut.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, elems1, Gen2.except_ok_bind]

/-- An `N+1`-bit output port fails the interface: at `N = 1` the output
ports are `[("y", 2)]`, the task's `[("y", 1)]`. -/
theorem wideOut_refuted : ¬ Statement wideOut.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hi := h.1.2
    simp [outputPorts, wideOut_decls1, task] at hi

/-! ## Hidden extra input `en` -/

theorem extraIn_decls1 :
    (extraIn.sem 1).decls.toList =
      [{ name := "a", width := 1, isInput := true }, { name := "b", width := 1, isInput := true },
       { name := "en", width := 1, isInput := true }, { name := "y", width := 1, isOutput := true }] := by
  show (extraIn.pdesign.instantiateGD2 [1]).decls.toList = _
  refine decls1_eq (elems := elems1 ["a", "b", "en", "y"]) rfl rfl ?_ ?_ rfl
  · simp [extraIn.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, Gen2.except_ok_bind]
  · simp [extraIn.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, elems1, Gen2.except_ok_bind]

/-- A hidden input `en` fails the interface: the input ports are
`[("a", 1), ("b", 1), ("en", 1)]`, the task's `[("a", 1), ("b", 1)]`. -/
theorem extraIn_refuted : ¬ Statement extraIn.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hi := h.1.1
    simp [inputPorts, extraIn_decls1, task] at hi

/-! Axiom pins: standard axioms only (`decide +kernel` is kernel evaluation,
not native code). -/

/--
info: 'SvGolf.Tasks.Example.Negative.orGate_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms orGate_refuted

/--
info: 'SvGolf.Tasks.Example.Negative.readsX_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms readsX_refuted

/--
info: 'SvGolf.Tasks.Example.Negative.wideOut_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wideOut_refuted

/--
info: 'SvGolf.Tasks.Example.Negative.extraIn_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms extraIn_refuted

end SvGolf.Tasks.Example.Negative
