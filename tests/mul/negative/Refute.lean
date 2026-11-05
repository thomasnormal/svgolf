import SvGolf.Comb
import SvGolf.LoadSv
import tasks.mul.Spec
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# Task `mul`: the negative designs do NOT satisfy the statement

Evidence that `tasks/mul/Spec.lean` rejects the wrong multipliers in this
directory (`README.md` lists them all, with the banlist case `mul_star.sv`
and the `check.py` stage each fails at).

* **`narrow_out.sv`** (the output is `2N-1` bits): refuted by the interface
  conjunct at `N = 1`, a kernel-checked theorem (`narrowOut_refuted`). At
  `N = 1` this design computes every product correctly (`a * b ≤ 1`), so the
  interface conjunct is the only thing that rejects it there. The proof
  needs only the declaration stage of the instantiation: `gd2_decls` shows
  that the instantiated declarations are the declaration stage's result or
  empty (an instantiation that fails is the error design), and both differ
  from the task's ports.
* **`only_n16.sv`** (the reference multiplier at the scoring point `N = 16`,
  `p = 0` elsewhere): refuted at `N = 1` by one concrete run, a
  kernel-checked theorem (`onlyN16_refuted`): the design is instantiated at
  `N = 1` symbolically (the generate-if takes its else branch,
  `GenItem.expand2_genIf_of_eq`), then the one-cycle run on `a = b = 1` is
  evaluated by `decide +kernel` and holds `p = 0`, not `1`.
* **`top_shift.sv`** (wrong bit: the top half is `s[N-1][N-1:0]` instead of
  `[N:1]`) and **`drop_carry.sv`** (off-by-one carry: every adder row drops
  its carry-out): refuted by concrete counterexample runs evaluated by Lean's
  interpreter (`#guard` below, `N = 1` and `N = 2`), plus kernel-checked
  theorems `topShift_refuted_of_run` / `dropCarry_refuted_of_run` that turn
  those evaluations into `¬ Statement`. The evaluations are NOT kernel
  checked: the generate expansion does not reduce by `rfl` or
  `decide +kernel` (measured: `expandList2 … = .ok …` is not
  definitionally checkable, and `Res`/`Process2` have no `DecidableEq`), and
  instantiating these loops symbolically would repeat the reference proof's
  Part 1 per design. Verilator agrees on both counterexamples (`README.md`).

The designs are loaded with `load_sv` (`SvGolf/LoadSv.lean`): extracted at
elaboration time by svGolf's one extraction path (the source gate, then the
pinned extractor with the task's probe points, as `check.py` does) into a
cache under `.lake/envelopes/`; paths are relative to the `svgolf/` package
root, the working directory of `lake build`.
-/

namespace SvGolf.Tasks.Mul.Negative

open LeanModels.Sv SvGolf

load_sv narrowOut from "tests/mul/negative/narrow_out.sv"
load_sv onlyN16 from "tests/mul/negative/only_n16.sv"
load_sv topShift from "tests/mul/negative/top_shift.sv"
load_sv dropCarry from "tests/mul/negative/drop_carry.sv"

/-! ## Instantiation helpers -/

/-- The parameter environment at `N = n` (an `int` parameter `N`). -/
def envAt (pd : PDesign) (n : Int) : IEnv :=
  { vals := [("N", n)], pwidths := [("N", 32)],
    dims := dimTable { vals := [("N", n)], pwidths := [("N", 32)] } pd.decls }

/-- **The declarations of `instantiateGD2`**: the declaration stage's result
when the whole instantiation succeeds (the one-driver guard keeps the
declarations), none when it fails (the error design). -/
theorem gd2_decls {pd : PDesign} {args : List Int} {env : IEnv} {decls : List Decl}
    (h1 : pd.paramEnv2 args = .ok env) (h2 : buildDecls env pd.decls = .ok decls) :
    (pd.instantiateGD2 args).decls.toList = decls ∨ (pd.instantiateGD2 args).decls.toList = [] := by
  unfold PDesign.instantiateGD2 PDesign.instantiateG2
  cases hi : pd.instantiate2 args (PDesign.surfaceFuel args) with
  | ok m =>
    obtain ⟨-, env', decls', elems, gens, h1', h2', -, -, rfl⟩ :=
      PDesign.instantiate2_eq_ok_iff.mp hi
    rw [h1, Res.ok.injEq] at h1'
    subst h1'
    rw [h2, Res.ok.injEq] at h2'
    subst h2'
    left
    simp only [Res.ok_bind]
    unfold PDesign.driverGuard Design2.driverGuard
    split <;> simp
  | timeout => right; simp [Res.timeout_bind, Design2.errorDesign]
  | unsupported msg => right; simp [Res.unsupported_bind, Design2.errorDesign]

/-! ## Interface: `output logic [2*N-2:0] p` -/

/-- The declaration stage of `narrow_out` at `N = 1`: `p` is ONE bit. -/
theorem narrowOut_buildDecls :
    buildDecls (envAt narrowOut.pdesign 1) narrowOut.pdesign.decls =
      .ok [{ name := "a", width := 1, isInput := true }, { name := "b", width := 1, isInput := true },
        { name := "p", width := 1, isOutput := true }, { name := "full", width := 2 },
        { name := "pp", width := 1 }, { name := "s", width := 2 }, { name := "c", width := 2 },
        { name := "t", width := 1 }] := by
  simp [narrowOut.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    envAt, List.lookup, Gen2.except_ok_bind]

/-- A `2N-1`-bit output fails the interface: at `N = 1` the output ports are
`[("p", 1)]` (or none, were the instantiation to fail), the task's
`[("p", 2)]`. -/
theorem narrowOut_refuted : ¬ Statement narrowOut.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hi := h.1.2
    change outputPorts (narrowOut.pdesign.instantiateGD2 [1]) = _ at hi
    rcases gd2_decls (args := [1]) rfl narrowOut_buildDecls with hd | hd <;>
      simp [outputPorts, hd, task] at hi


/-! ## Works only at the scoring point: `if (N == 16) … else p = '0` -/

/-- The declarations of `only_n16` at `N = 1`. -/
def decls1 : List Decl :=
  [{ name := "a", width := 1, isInput := true }, { name := "b", width := 1, isInput := true },
   { name := "p", width := 2, isOutput := true }, { name := "pp", width := 1 },
   { name := "s", width := 2 }, { name := "c", width := 2 }, { name := "t", width := 1 }]

/-- Element widths of `only_n16` at `N = 1`. -/
def elems1 : List (String × Nat) :=
  [("a", 1), ("b", 1), ("p", 1), ("pp", 1), ("s", 2), ("c", 2), ("t", 1)]

private theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem onlyN16_buildDecls :
    buildDecls (envAt onlyN16.pdesign 1) onlyN16.pdesign.decls = .ok decls1 := by
  simp [onlyN16.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    envAt, List.lookup, Gen2.except_ok_bind, decls1]

theorem onlyN16_buildElems :
    buildElems (envAt onlyN16.pdesign 1) onlyN16.pdesign.decls = .ok elems1 := by
  simp [onlyN16.pdesign, buildElems, PType.width_packed_cons, PType.elemWidth, PDim.width, evalInt,
    envAt, List.lookup, Gen2.except_ok_bind, elems1, List.foldlM_cons, except_pure]

/-- `p = '0` at `N = 1` (a 2-bit zero). -/
def zeroP : Process2 := .assign (.ident "p") (.lit (LVec.replicate 2 .l0))

/-- The generate stage at `N = 1`: the condition `N == 16` is `0`, so the
generate-if expands its else branch, `assign p = '0;`. -/
theorem onlyN16_gens :
    expandList2 ((envAt onlyN16.pdesign 1).withDecls decls1) elems1 (PDesign.surfaceFuel [1])
      onlyN16.pdesign.generates = .ok [zeroP] := by
  obtain ⟨thenB, hg⟩ : ∃ thenB, onlyN16.pdesign.generates =
      [.genIf (.binary (.m0 .eq) (.paramRef "N" none) (.int 16)) thenB
        [.process (.assign "p" (.fill .l0))]] := ⟨_, rfl⟩
  rw [hg]
  apply expandList2_singleton_ok
  rw [GenItem.expand2_genIf_of_eq (by first | rfl | simp [evalInt, envAt, IEnv.withDecls])]
  rw [expandList2_singleton_ok (GenItem.expand2_process _)]
  sv2_inst_simp [envAt, decls1, elems1, zeroP, dimTable, dimTableStep, PType.width_packed_cons,
    PDim.width, onlyN16.pdesign]

/-- `only_n16` at `N = 1`: the declarations, and the one process `p = '0`. -/
def onlyD : Design2 :=
  { name := onlyN16.pdesign.name, decls := decls1.toArray, processes := #[zeroP] }

theorem onlyN16_sem1 : onlyN16.sem 1 = onlyD := by
  show onlyN16.pdesign.instantiateGD2 [1] = _
  have hi := PDesign.instantiate2_of_ok (d := onlyN16.pdesign) (args := [1])
    (F := PDesign.surfaceFuel [1]) (env := envAt onlyN16.pdesign 1) rfl rfl onlyN16_buildDecls
    onlyN16_buildElems onlyN16_gens
  have hp : onlyN16.pdesign.processes = [] := rfl
  have ho : onlyN16.pdesign.others = [] := rfl
  have hD : onlyN16.pdesign.assemble2 (envAt onlyN16.pdesign 1) decls1 elems1 [zeroP] = onlyD := by
    simp [PDesign.assemble2, onlyD, hp, ho]
  have hok : driversOk onlyN16.pdesign.declNames onlyN16.pdesign.inputNames
      (onlyN16.pdesign.instantiateD2 [1]).processes.toList = true := by
    rw [PDesign.instantiateD2_of_ok hi, hD]
    decide
  rw [PDesign.instantiateGD2_of_driversOk hok, PDesign.instantiateD2_of_ok hi, hD]

/-- Correct only at `N = 16`: at `N = 1`, `a = b = 1`, the snapshot has
`p = 0`, the task says `1`. One concrete run, evaluated by the kernel. -/
theorem onlyN16_refuted : ¬ Statement onlyN16.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun h => by
    have hc := h.2.2
    rw [onlyN16_sem1] at hc
    exact CombTask.not_computes_of_counterexample (σ := σ_src) (fuel := 64)
      (v := (1#1, 1#1, ())) (by simp [task]) (by decide +kernel) hc

/-! ## The two loop bugs: interpreter-checked counterexamples

`top_shift.sv` (the top half of `p` one bit too low) and `drop_carry.sv`
(every adder row drops its carry-out). Each theorem below is
kernel-checked and says: IF the concrete run's outputs differ from the task
(`CombTask.counterexample … = true`), THEN the statement fails. The
hypothesis is then checked by `#guard`, i.e. by Lean's interpreter running
the compiled `instantiateGD2` and `run2`, NOT by the kernel (which cannot
evaluate the generate expansion; see the module docstring). -/

/-- `top_shift`: refuted at `N = 1` by `a = b = 1`, given the run's value. -/
theorem topShift_refuted_of_run
    (h : task.counterexample 1 (topShift.sem 1) σ_src 256 (1#1, 1#1, ()) = true) :
    ¬ Statement topShift.sem :=
  CombTask.not_statement_of (N := 1) (by simp [task]) fun hs =>
    CombTask.not_computes_of_counterexample (by simp [task]) h hs.2.2

/-- `drop_carry`: refuted at `N = 2` by `a = b = 3`, given the run's value. -/
theorem dropCarry_refuted_of_run
    (h : task.counterexample 2 (dropCarry.sem 2) σ_src 256 (3#2, 3#2, ()) = true) :
    ¬ Statement dropCarry.sem :=
  CombTask.not_statement_of (N := 2) (by simp [task]) fun hs =>
    CombTask.not_computes_of_counterexample (by simp [task]) h hs.2.2

/-! The hypotheses, by the interpreter: both runs complete and disagree with
the task. -/

#guard task.counterexample 1 (topShift.sem 1) σ_src 256 (1#1, 1#1, ())
#guard task.counterexample 2 (dropCarry.sem 2) σ_src 256 (3#2, 3#2, ())

/-! … and the values they produce: `1 * 1` gives `p = 3` (`0b11`), `3 * 3`
gives `p = 1` (`0b0001`, the row carry is lost), as Verilator does. -/

#guard (match run2 (topShift.sem 1) σ_src 256 [entryOf (task.inputs 1) (1#1, 1#1, ())] with
  | .ok [st] => SvState.lookup st "p" == some (LVec.ofBitVec (3#2))
  | _ => false)
#guard (match run2 (dropCarry.sem 2) σ_src 256 [entryOf (task.inputs 2) (3#2, 3#2, ())] with
  | .ok [st] => SvState.lookup st "p" == some (LVec.ofBitVec (1#4))
  | _ => false)

/-! Axiom pins: standard axioms only (`decide +kernel` is kernel evaluation,
not native code). -/

/--
info: 'SvGolf.Tasks.Mul.Negative.narrowOut_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms narrowOut_refuted

/--
info: 'SvGolf.Tasks.Mul.Negative.onlyN16_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms onlyN16_refuted

/--
info: 'SvGolf.Tasks.Mul.Negative.topShift_refuted_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms topShift_refuted_of_run

/--
info: 'SvGolf.Tasks.Mul.Negative.dropCarry_refuted_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dropCarry_refuted_of_run

end SvGolf.Tasks.Mul.Negative
