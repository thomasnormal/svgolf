import SvGolf.Comb
import SvGolf.LoadSv
import tasks.add.Spec
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# Task `add`: the negative designs do NOT satisfy the statement

Kernel-checked refutations, one per Lean-level design in this directory
(`README.md` lists them all, with the banlist case). Each targets one way a
design could look right without meeting the statement, and each is refuted
at the smallest width, `N = 1`:

* four WRONG FUNCTIONS, each by ONE concrete run whose snapshot disagrees
  with the task (`CombTask.not_computes_of_counterexample`; the run of the
  instantiated design is evaluated by `decide +kernel`):
  - `no_cin.sv`, the carry in ignored (`noCin_refuted`);
  - `cout_off.sv`, the carry out taken one bit too low (`coutOff_refuted`);
  - `carry_bug.sv`, a wrong carry gate (`carryBug_refuted`);
  - `only_n16.sv`, a ripple adder at `N = 16` only, so correct at the
    scoring point (`onlyN16_refuted`);
* two INTERFACE TRICKS, by the interface conjunct on the instantiated
  declarations:
  - `wide_s.sv`, one `(N+1)`-bit output `s = {cout, sum}` (`wideS_refuted`);
  - `cin_name.sv`, the carry in renamed `ci` (`cinName_refuted`).

`decide +kernel` gets stuck on `PDesign.instantiate2` itself (measured on
this task's reference: `(design.sem 1).processes.size = 4` does not
reduce), so each functional negative is first
instantiated at `N = 1` by the symbolic route of the reference proof
(`semAt1_eq`: `PDesign.instantiate2_of_ok`, `simp` on the stages, the
generate loop through `GenItem.expand2_genFor_ascending_processes`, the
generate-if through `GenItem.expand2_genIf_of_eq`), and only the run of the
resulting hand-readable `Design2` is evaluated. The interface refutations
need only the declaration stage (`decls_or_nil`: whatever the generate
expansion does, the instantiated declarations are the declaration stage's,
or none at all).

The designs are loaded with `load_sv` (`SvGolf/LoadSv.lean`): extracted at
elaboration time by svGolf's one extraction path (the source gate, then the
pinned extractor with the task's probe points, as `check.py` does) into a
cache under `.lake/envelopes/`; paths are relative to the `svgolf/` package
root, the working directory of `lake build`.
-/

namespace SvGolf.Tasks.Add.Negative

open LeanModels.Sv SvGolf

load_sv noCin from "tests/add/negative/no_cin.sv"
load_sv coutOff from "tests/add/negative/cout_off.sv"
load_sv carryBug from "tests/add/negative/carry_bug.sv"
load_sv onlyN16 from "tests/add/negative/only_n16.sv"
load_sv wideS from "tests/add/negative/wide_s.sv"
load_sv cinName from "tests/add/negative/cin_name.sv"
-- `dead_clock.sv` and `dead_clock_tied.sv` are no longer loaded here: since WP-Q0 (2026-10-30) the loader itself
-- refuses a clock that is not an input port (`Clock:source`, LeanModels/Sv/ClockGuard2.lean), so there is no
-- `deadClock.sem` to refute; the designs are rejected at the `fourstate` / `design` stages (tests/expected.json).
-- The generic lemma `not_satisfiedAt_of_clocked` below (a clocked process falsifies the statement) stays.

/-! ## Instantiation at `N = 1` -/

/-- The parameter environment at `N = 1` (an `int` parameter `N`). -/
def envAt1 (pd : PDesign) : IEnv :=
  { vals := [("N", 1)], pwidths := [("N", 32)],
    dims := dimTable { vals := [("N", 1)], pwidths := [("N", 32)] } pd.decls }

/-- The whole of `pd.instantiateGD2 [1]` (no loud `others`, the one-driver
rule holds): name, declarations, and the static processes followed by the
generate expansion. -/
theorem semAt1_eq {pd : PDesign} {decls : List Decl} {elems : List (String × Nat)}
    {gens procs : List Process2}
    (harity : [(1 : Int)].length = pd.params.length) (h1 : pd.paramEnv2 [1] = .ok (envAt1 pd))
    (h2 : buildDecls (envAt1 pd) pd.decls = .ok decls)
    (h3 : buildElems (envAt1 pd) pd.decls = .ok elems)
    (h4 : expandList2 ((envAt1 pd).withDecls decls) elems (PDesign.surfaceFuel [1])
      pd.generates = .ok gens)
    (h5 : pd.processes.map (instProcess2 ((envAt1 pd).withDecls decls) elems) ++ gens = procs)
    (h6 : pd.others = []) (hok : driversOk pd.declNames pd.inputNames procs = true) :
    pd.instantiateGD2 [1] =
      { name := pd.name, decls := decls.toArray, processes := procs.toArray } := by
  have hi := PDesign.instantiate2_of_ok (F := PDesign.surfaceFuel [1]) harity h1 h2 h3 h4
  have hD : pd.assemble2 (envAt1 pd) decls elems gens =
      { name := pd.name, decls := decls.toArray, processes := procs.toArray } := by
    simp [PDesign.assemble2, ← h5, h6]
  have hok' : driversOk pd.declNames pd.inputNames
      (pd.instantiateD2 [1]).processes.toList = true := by
    rw [PDesign.instantiateD2_of_ok hi, hD]
    simpa using hok
  rw [PDesign.instantiateGD2_of_driversOk hok', PDesign.instantiateD2_of_ok hi, hD]

/-- **Declarations without the generate expansion**: the instantiated
declarations are the declaration stage's when the instantiation succeeds,
and empty (the loud error design) when it does not; the one-driver guard
never changes them. -/
theorem decls_or_nil {pd : PDesign} {args : List Int} {env : IEnv} {decls : List Decl}
    (h1 : pd.paramEnv2 args = .ok env) (h2 : buildDecls env pd.decls = .ok decls) :
    (pd.instantiateGD2 args).decls.toList = decls ∨
      (pd.instantiateGD2 args).decls.toList = [] := by
  rw [PDesign.instantiateGD2_eq_driverGuard]
  have hdg : ∀ m : Design2, (pd.driverGuard m).decls = m.decls := by
    intro m
    unfold PDesign.driverGuard Design2.driverGuard
    split <;> rfl
  rw [hdg]
  unfold PDesign.instantiateD2
  split
  · rename_i m hm
    obtain ⟨env', decls', _, _, h1', h2', _, _, _, hd, _⟩ := PDesign.instantiate2_processes hm
    rw [h1] at h1'
    cases h1'
    rw [h2] at h2'
    cases h2'
    exact Or.inl hd
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- The ripple family's generate loop `for (i = 0; i < N; i++)` over plain
process templates `ts`, at `N = 1`: the templates at `i = 0`. -/
theorem rippleGen1 {pd : PDesign} {decls : List Decl} {elems : List (String × Nat)}
    {ts : List PProcess} {rc : Option Nat}
    (hg : pd.generates =
      [.genFor (some "g_bit") "i" (.int 0) (.binary .slt (.genvarRef "i") (.paramRef "N" none))
        (.unary .inc (.genvarRef "i")) rc (ts.map GenItem.process)]) :
    expandList2 ((envAt1 pd).withDecls decls) elems (PDesign.surfaceFuel [1]) pd.generates =
      .ok (ts.map (instProcess2 (((envAt1 pd).withDecls decls).bindVal "i" 0) elems)) := by
  rw [hg]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genFor_ascending_processes (N := 1) (evalInt_int 0)
    (fun i => by simp [envAt1, List.lookup])
    (fun i => by simp [evalInt, envAt1, List.lookup])
    (by simp [PDesign.surfaceFuel])]
  simp [intRange]

/-! ## The ripple vocabulary at `N = 1` -/

/-- The 1-bit ports `a`, `b`, `cin` (inputs), `s`, `cout` (outputs), and the
2-bit carry chain `c`. -/
def rippleDecls1 : List Decl :=
  [{ name := "a", width := 1, isInput := true },
   { name := "b", width := 1, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := 1, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := 2 }]

/-- Every declaration 1-D (element width 1), for the given names. -/
def elems1 (names : List String) : List (String × Nat) := names.map (·, 1)

/-- The ripple element table. -/
def rippleElems1 : List (String × Nat) := elems1 ["a", "b", "cin", "s", "cout", "c"]

/-- The sum-bit template `assign s[i] = a[i] ^ b[i] ^ c[i];`. -/
def sumT : PProcess :=
  .assignL (.bitSel "s" (.genvarRef "i"))
    (.binary (.m0 .xor)
      (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.bitSel (.ident "c") (.genvarRef "i")))

/-- The carry template `assign c[i+1] = (a[i] & b[i]) | (c[i] & (a[i] ^ b[i]));`. -/
def carryT : PProcess :=
  .assignL (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1)))
    (.binary (.m0 .or)
      (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.binary (.m0 .and) (.bitSel (.ident "c") (.genvarRef "i"))
        (.binary (.m0 .xor) (.bitSel (.ident "a") (.genvarRef "i"))
          (.bitSel (.ident "b") (.genvarRef "i")))))

/-- `carry_bug.sv`'s carry template `assign c[i+1] = (a[i] & b[i]) | (c[i] & a[i]);`. -/
def carryBugT : PProcess :=
  .assignL (.bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1)))
    (.binary (.m0 .or)
      (.binary (.m0 .and) (.bitSel (.ident "a") (.genvarRef "i"))
        (.bitSel (.ident "b") (.genvarRef "i")))
      (.binary (.m0 .and) (.bitSel (.ident "c") (.genvarRef "i"))
        (.bitSel (.ident "a") (.genvarRef "i"))))

/-- `c[0] = cin`. -/
def cinProc : Process2 := .assign (.slice "c" 0 1) (.ident "cin")

/-- `s[0] = a[0] ^ b[0] ^ c[0]`. -/
def sum0 : Process2 :=
  .assign (.slice "s" 0 1)
    (.binary .xor (.binary .xor (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1))
      (.slice (.ident "c") 0 1))

/-- `c[1] = (a[0] & b[0]) | (c[0] & (a[0] ^ b[0]))`. -/
def carry0 : Process2 :=
  .assign (.slice "c" 1 1)
    (.binary .or (.binary .and (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1))
      (.binary .and (.slice (.ident "c") 0 1)
        (.binary .xor (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1))))

/-- `c[1] = (a[0] & b[0]) | (c[0] & a[0])` (`carry_bug.sv`). -/
def carryBug0 : Process2 :=
  .assign (.slice "c" 1 1)
    (.binary .or (.binary .and (.slice (.ident "a") 0 1) (.slice (.ident "b") 0 1))
      (.binary .and (.slice (.ident "c") 0 1) (.slice (.ident "a") 0 1)))

/-- `cout = c[k]`. -/
def coutAt (k : Nat) : Process2 := .assign (.ident "cout") (.slice (.ident "c") k 1)

/-- A design of the ripple family at `N = 1`, with the given processes. -/
def ripple1 (procs : List Process2) : Design2 :=
  { name := "add_n", decls := rippleDecls1.toArray, processes := procs.toArray }

/-- The task's input names are distinct (for `not_computes_of_counterexample`). -/
theorem inputs_nodup : ((task.inputs 1).map Prod.fst).Nodup := by
  simp [task]

/-- A 1-bit constant `0` (`1'b0`). -/
def lit0 : Expr2 := .lit { bits := #[Logic.l0] }

/-! ## `no_cin.sv`: the carry in ignored (`c[0] = 1'b0`) -/

/-- `no_cin` at `N = 1`. -/
def noCinD : Design2 := ripple1 [.assign (.slice "c" 0 1) lit0, coutAt 1, sum0, carry0]

theorem noCin_sem1 : noCin.sem 1 = noCinD := by
  show noCin.pdesign.instantiateGD2 [1] = _
  refine (semAt1_eq (decls := rippleDecls1) (elems := rippleElems1) rfl (by rfl) ?_ ?_
    (rippleGen1 (ts := [sumT, carryT]) rfl) ?_ rfl (by decide)).trans rfl
  · simp [noCin.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, rippleDecls1, Gen2.except_ok_bind]
  · simp [noCin.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, rippleElems1, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [noCin.pdesign, envAt1, rippleDecls1, rippleElems1, elems1, sumT, carryT,
      sum0, carry0, coutAt, lit0, LVec.width, dimTable, dimTableStep, PType.width_packed_cons, PDim.width]

/-- Ignoring the carry in is wrong: at `N = 1`, `a = 0`, `b = 0`, `cin = 1`
the snapshot has `s = 0`, the task says `s = 1`. -/
theorem noCin_refuted : ¬ Statement noCin.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [noCin_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (0#1, 0#1, 1#1, ())) inputs_nodup (by decide +kernel) hc

/-! ## `cout_off.sv`: the carry out one bit too low (`cout = c[N-1]`) -/

/-- `cout_off` at `N = 1`: `cout = c[0]`. -/
def coutOffD : Design2 := ripple1 [cinProc, coutAt 0, sum0, carry0]

theorem coutOff_sem1 : coutOff.sem 1 = coutOffD := by
  show coutOff.pdesign.instantiateGD2 [1] = _
  refine (semAt1_eq (decls := rippleDecls1) (elems := rippleElems1) rfl (by rfl) ?_ ?_
    (rippleGen1 (ts := [sumT, carryT]) rfl) ?_ rfl (by decide)).trans rfl
  · simp [coutOff.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, rippleDecls1, Gen2.except_ok_bind]
  · simp [coutOff.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, rippleElems1, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [coutOff.pdesign, envAt1, rippleDecls1, rippleElems1, elems1, sumT, carryT,
      sum0, carry0, coutAt, cinProc, dimTable, dimTableStep, PType.width_packed_cons, PDim.width]

/-- The off-by-one carry out is wrong: at `N = 1`, `a = 1`, `b = 1`,
`cin = 0` the snapshot has `cout = c[0] = 0`, the task says `cout = 1`. -/
theorem coutOff_refuted : ¬ Statement coutOff.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [coutOff_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (1#1, 1#1, 0#1, ())) inputs_nodup (by decide +kernel) hc

/-! ## `carry_bug.sv`: a wrong carry gate (`(a & b) | (c & a)`) -/

/-- `carry_bug` at `N = 1`. -/
def carryBugD : Design2 := ripple1 [cinProc, coutAt 1, sum0, carryBug0]

theorem carryBug_sem1 : carryBug.sem 1 = carryBugD := by
  show carryBug.pdesign.instantiateGD2 [1] = _
  refine (semAt1_eq (decls := rippleDecls1) (elems := rippleElems1) rfl (by rfl) ?_ ?_
    (rippleGen1 (ts := [sumT, carryBugT]) rfl) ?_ rfl (by decide)).trans rfl
  · simp [carryBug.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, rippleDecls1, Gen2.except_ok_bind]
  · simp [carryBug.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, rippleElems1, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [carryBug.pdesign, envAt1, rippleDecls1, rippleElems1, elems1, sumT,
      carryBugT, sum0, carryBug0, coutAt, cinProc, dimTable, dimTableStep,
      PType.width_packed_cons, PDim.width]

/-- The wrong carry gate is wrong: at `N = 1`, `a = 0`, `b = 1`, `cin = 1`
the snapshot has `cout = 0`, the task says `cout = 1`. -/
theorem carryBug_refuted : ¬ Statement carryBug.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [carryBug_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (0#1, 1#1, 1#1, ())) inputs_nodup (by decide +kernel) hc

/-! ## `only_n16.sv`: a ripple adder at `N = 16` only

`generate if (N == 16)` the ripple chain, `else` the carry-free `s = a ^ b`,
`cout = 1'b0`. At the scoring point it is the reference; the statement's
`∀ N` is what rejects it. -/

/-- `only_n16` at `N = 1`: the static `c[0] = cin`, then the else branch. -/
def onlyN16D : Design2 :=
  ripple1 [cinProc, .assign (.ident "s") (.binary .xor (.ident "a") (.ident "b")),
    .assign (.ident "cout") lit0]

/-- The generate-if at `N = 1` takes its else branch. -/
theorem onlyN16_gen1 :
    expandList2 ((envAt1 onlyN16.pdesign).withDecls rippleDecls1) rippleElems1
        (PDesign.surfaceFuel [1]) onlyN16.pdesign.generates =
      .ok [.assign (.ident "s") (.binary .xor (.ident "a") (.ident "b")),
        .assign (.ident "cout") lit0] := by
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genIf_of_eq (by rfl)]
  sv2_inst_simp [expandList2_cons, GenItem.expand2_process, rippleDecls1, rippleElems1, elems1,
    lit0, LVec.width]

theorem onlyN16_sem1 : onlyN16.sem 1 = onlyN16D := by
  show onlyN16.pdesign.instantiateGD2 [1] = _
  refine (semAt1_eq (decls := rippleDecls1) (elems := rippleElems1) rfl (by rfl) ?_ ?_
    onlyN16_gen1 ?_ rfl (by decide)).trans rfl
  · simp [onlyN16.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
      envAt1, List.lookup, rippleDecls1, Gen2.except_ok_bind]
  · simp [onlyN16.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, envAt1,
      List.lookup, rippleElems1, elems1, Gen2.except_ok_bind]
  · sv2_inst_simp [onlyN16.pdesign, envAt1, rippleDecls1, rippleElems1, elems1, cinProc, lit0,
      dimTable, dimTableStep, PType.width_packed_cons, PDim.width]

/-- Correct at `N = 16` is not correct: at `N = 1`, `a = 0`, `b = 0`,
`cin = 1` the snapshot has `s = 0`, the task says `s = 1`. -/
theorem onlyN16_refuted : ¬ Statement onlyN16.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [onlyN16_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (0#1, 0#1, 1#1, ())) inputs_nodup (by decide +kernel) hc

/-! ## `wide_s.sv`: one `(N+1)`-bit output `s = {cout, sum}` -/

/-- `wide_s`'s declaration stage at `N = 1`: `s` is 2 bits, no `cout`. -/
def wideSDecls1 : List Decl :=
  [{ name := "a", width := 1, isInput := true },
   { name := "b", width := 1, isInput := true },
   { name := "cin", width := 1, isInput := true },
   { name := "s", width := 2, isOutput := true },
   { name := "c", width := 2 }]

/-- A 2-bit `s` and no `cout` fail the interface: at `N = 1` the output
ports are `[("s", 2)]` (or none, were the instantiation to fail), the task's
`[("s", 1), ("cout", 1)]`. -/
theorem wideS_refuted : ¬ Statement wideS.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hi := h.1.2
    have hd : buildDecls (envAt1 wideS.pdesign) wideS.pdesign.decls = .ok wideSDecls1 := by
      simp [wideS.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
        envAt1, List.lookup, wideSDecls1, Gen2.except_ok_bind]
    have h' : (wideS.sem 1).decls.toList = wideSDecls1 ∨ (wideS.sem 1).decls.toList = [] :=
      decls_or_nil (args := [1]) (by rfl) hd
    rcases h' with h' | h' <;> simp [outputPorts, h', wideSDecls1, task] at hi

/-! ## `cin_name.sv`: the carry in renamed `ci` -/

/-- `cin_name`'s declaration stage at `N = 1`: inputs `a`, `b`, `ci`. -/
def cinNameDecls1 : List Decl :=
  [{ name := "a", width := 1, isInput := true },
   { name := "b", width := 1, isInput := true },
   { name := "ci", width := 1, isInput := true },
   { name := "s", width := 1, isOutput := true },
   { name := "cout", width := 1, isOutput := true },
   { name := "c", width := 2 }]

/-- A carry in named `ci` fails the interface: at `N = 1` the input ports are
`[("a", 1), ("b", 1), ("ci", 1)]` (or none), the task's
`[("a", 1), ("b", 1), ("cin", 1)]`. -/
theorem cinName_refuted : ¬ Statement cinName.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hi := h.1.1
    have hd : buildDecls (envAt1 cinName.pdesign) cinName.pdesign.decls = .ok cinNameDecls1 := by
      simp [cinName.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
        envAt1, List.lookup, cinNameDecls1, Gen2.except_ok_bind]
    have h' : (cinName.sem 1).decls.toList = cinNameDecls1 ∨
        (cinName.sem 1).decls.toList = [] :=
      decls_or_nil (args := [1]) (by rfl) hd
    rcases h' with h' | h' <;> simp [inputPorts, h', cinNameDecls1, task] at hi

/-! ## Clocked designs: `dead_clock.sv`, `dead_clock_tied.sv`

A correct ripple adder into internal signals, with the outputs REGISTERED
by `always_ff @(posedge clk)` on a clock nothing drives (`dead_clock.sv`) or
one tied to `1'b0` (`dead_clock_tied.sv`). ls-sv runs every edge-phase
process once per cycle whatever its clock holds, so every ls-sv snapshot
carries the right `{cout, s}` and `Computes` HOLDS; every simulator and
Yosys see a clock that never rises (`x` outputs, 0 GE). The `Unclocked`
half of conjunct 2 is what rejects them, and the refutation below does not
look at the function at all: ANY family whose envelope has a top-level
clocked process fails EVERY combinational task at EVERY parameter point
(`not_satisfiedAt_of_clocked`). If the instantiation succeeds, the clocked
template lowers to an edge-phase process of the design (the one-driver
guard only appends a loud process); if it fails, the loud error design
never completes a run (`errorDesign_not_terminates`). -/

/-- A clocked process template: `always_ff`, `always @(posedge …)`, or an
async-reset block. -/
def clockedB : PProcess → Bool
  | .alwaysFF .. | .alwaysPlain .. | .alwaysFFR .. => true
  | _ => false

/-- A clocked template lowers to an edge-phase process. -/
theorem isEdgePhase_instProcess2 {env : IEnv} {elems : List (String × Nat)} {p : PProcess}
    (h : clockedB p = true) : (instProcess2 env elems p).isEdgePhase = true := by
  cases p <;> simp_all [clockedB, instProcess2, Process2.isEdgePhase]

/-- The loud error design (a refused instantiation) never completes a
one-cycle run: its only process is `unsupported`, scheduled in the comb
phase. -/
theorem errorDesign_not_terminates (n msg : String) :
    ¬ Terminates2 (Design2.errorDesign n msg) := by
  intro h
  obtain ⟨tr, fuel, hr⟩ := h σ_src [[]]
  cases fuel with
  | zero =>
      have h0 : run2 (Design2.errorDesign n msg) σ_src 0 [[]] = .timeout := rfl
      rw [h0] at hr
      cases hr
  | succ f =>
      obtain ⟨e, he⟩ : ∃ e, run2 (Design2.errorDesign n msg) σ_src (f + 1) [[]] = .unsupported e :=
        ⟨_, rfl⟩
      rw [he] at hr
      cases hr

/-- **A family with a top-level clocked process meets no combinational
task**, at any parameter point. -/
theorem not_satisfiedAt_of_clocked {t : CombTask} {N : Nat} {pd : PDesign} {args : List Int}
    (hc : pd.processes.any clockedB = true) : ¬ t.SatisfiedAt N (pd.instantiateGD2 args) := by
  rintro ⟨-, ⟨hu, -, ht⟩, -⟩
  obtain ⟨p, hp, hpc⟩ := List.any_eq_true.mp hc
  rw [PDesign.instantiateGD2_eq_driverGuard] at hu ht
  cases hi : pd.instantiate2 args (PDesign.surfaceFuel args) with
  | ok m =>
      rw [PDesign.instantiateD2_of_ok hi] at hu
      obtain ⟨env, decls, elems, gens, -, -, -, -, hprocs, -, -⟩ :=
        PDesign.instantiate2_processes hi
      have hm : instProcess2 (env.withDecls decls) elems p ∈ m.processes.toList := by
        rw [hprocs]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hp))
      have hg : instProcess2 (env.withDecls decls) elems p ∈ (pd.driverGuard m).processes.toList := by
        unfold PDesign.driverGuard Design2.driverGuard
        split
        · exact hm
        · simp [hm]
      have := hu _ hg
      rw [isEdgePhase_instProcess2 hpc] at this
      cases this
  | timeout =>
      simp only [PDesign.instantiateD2, hi, PDesign.driverGuard,
        Design2.errorDesign_driverGuard] at ht
      exact errorDesign_not_terminates _ _ ht
  | unsupported msg =>
      simp only [PDesign.instantiateD2, hi, PDesign.driverGuard,
        Design2.errorDesign_driverGuard] at ht
      exact errorDesign_not_terminates _ _ ht

/-! ## Axiom pins

Standard axioms only (`decide +kernel` is kernel evaluation, not native
code; no `native_decide`, no `bv_decide`). -/

/--
info: 'SvGolf.Tasks.Add.Negative.noCin_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms noCin_refuted

/--
info: 'SvGolf.Tasks.Add.Negative.coutOff_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms coutOff_refuted

/--
info: 'SvGolf.Tasks.Add.Negative.carryBug_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms carryBug_refuted

/--
info: 'SvGolf.Tasks.Add.Negative.onlyN16_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms onlyN16_refuted

/--
info: 'SvGolf.Tasks.Add.Negative.wideS_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wideS_refuted

/--
info: 'SvGolf.Tasks.Add.Negative.cinName_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cinName_refuted

end SvGolf.Tasks.Add.Negative
