import SvGolf.Comb
import SvGolf.LoadSv
import tasks.clmul.Spec
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# Task `clmul`: the negative designs do NOT satisfy the statement

Evidence that `tasks/clmul/Spec.lean` rejects the wrong carry-less multipliers in this directory
(`README.md` lists them all, with the two banlist cases and the `check.py` stage each fails at).

Every refutation below has the same shape as the `mul` ones (`tests/mul/negative/Refute.lean`): a
kernel-checked theorem saying "IF this concrete run's outputs differ from the task
(`CombTask.counterexample … = true`), or IF the design's ports differ from the task's, THEN the statement
fails", and a `#guard` checking the hypothesis by Lean's interpreter running the compiled
`instantiateGD2` and `run2` (NOT by the kernel: the generate expansion does not reduce by `rfl` or
`decide +kernel`, measured for `mul`). The values the runs produce are pinned too (`#guard`s at the end),
and Verilator agrees on every counterexample (`README.md`, `tests/clmul/validate/sim.py --bad`).

* **`top_shift.sv`**, **`drop_top.sv`**, **`or_accumulate.sv`** (wrong bit, dropped term, wrong gate):
  wrong at `N = 2`, `a = b = 3`.
* **`reversed_p.sv`** (the reflected output orientation): right at `N = 1`, wrong at `N = 2`,
  `a = b = 1`.
* **`only_n16.sv`** (the reference at the scoring point, `p = 0` elsewhere): wrong at `N = 1`.
* **`wide_out.sv`** (`p` has 2N bits, a constant-zero top bit): refuted by the interface conjunct at
  `N = 1`.

The designs are loaded with `load_sv` (`SvGolf/LoadSv.lean`): extracted at elaboration time by svGolf's one
extraction path into a cache under `.lake/envelopes/`; paths are relative to the `svgolf/` package root.
-/

namespace SvGolf.Tasks.Clmul.Negative

open LeanModels.Sv SvGolf

load_sv topShift from "tests/clmul/negative/top_shift.sv"
load_sv dropTop from "tests/clmul/negative/drop_top.sv"
load_sv orAccumulate from "tests/clmul/negative/or_accumulate.sv"
load_sv reversedP from "tests/clmul/negative/reversed_p.sv"
load_sv onlyN16 from "tests/clmul/negative/only_n16.sv"
load_sv wideOut from "tests/clmul/negative/wide_out.sv"

/-! ## The two kinds of refutation -/

/-- A concrete run that disagrees with the task refutes the statement at that `N`. -/
theorem refuted_of_run {sem : Nat → Design2} (N : Nat) (hN : task.inRange N) (v : BitVec N × BitVec N × Unit)
    (h : task.counterexample N (sem N) σ_src 256 v = true) : ¬ Statement sem :=
  CombTask.not_statement_of (N := N) hN fun hs =>
    CombTask.not_computes_of_counterexample (by simp [task]) h hs.2.2

/-- A design whose output ports differ from the task's at some `N` fails the interface conjunct. -/
theorem refuted_of_ports {sem : Nat → Design2} (N : Nat) (hN : task.inRange N)
    (h : (outputPorts (sem N) != task.outputs N) = true) : ¬ Statement sem :=
  CombTask.not_statement_of (N := N) hN fun hs => by
    have hi := hs.1.2
    rw [hi] at h
    simp at h

/-! ## Wrong bit, dropped term, wrong gate: `N = 2`, `a = b = 3` -/

theorem topShift_refuted
    (h : task.counterexample 2 (topShift.sem 2) σ_src 256 (3#2, 3#2, ()) = true) :
    ¬ Statement topShift.sem := refuted_of_run 2 (by simp [task]) _ h

theorem dropTop_refuted
    (h : task.counterexample 2 (dropTop.sem 2) σ_src 256 (3#2, 3#2, ()) = true) :
    ¬ Statement dropTop.sem := refuted_of_run 2 (by simp [task]) _ h

theorem orAccumulate_refuted
    (h : task.counterexample 2 (orAccumulate.sem 2) σ_src 256 (3#2, 3#2, ()) = true) :
    ¬ Statement orAccumulate.sem := refuted_of_run 2 (by simp [task]) _ h

/-- The reflected orientation: right at `N = 1`, wrong at `N = 2`, `a = b = 1`. -/
theorem reversedP_refuted
    (h : task.counterexample 2 (reversedP.sem 2) σ_src 256 (1#2, 1#2, ()) = true) :
    ¬ Statement reversedP.sem := refuted_of_run 2 (by simp [task]) _ h

/-- Works only at the scoring point: at `N = 1` it gives `p = 0` for `a = b = 1`. -/
theorem onlyN16_refuted
    (h : task.counterexample 1 (onlyN16.sem 1) σ_src 256 (1#1, 1#1, ()) = true) :
    ¬ Statement onlyN16.sem := refuted_of_run 1 (by simp [task]) _ h

/-- A 2N-bit `p`: at `N = 1` the output port is 2 bits, the task's is 1. -/
theorem wideOut_refuted
    (h : (outputPorts (wideOut.sem 1) != task.outputs 1) = true) : ¬ Statement wideOut.sem :=
  refuted_of_ports 1 (by simp [task]) h

/-! The hypotheses, by the interpreter: every run completes and disagrees with the task. -/

#guard task.counterexample 2 (topShift.sem 2) σ_src 256 (3#2, 3#2, ())
#guard task.counterexample 2 (dropTop.sem 2) σ_src 256 (3#2, 3#2, ())
#guard task.counterexample 2 (orAccumulate.sem 2) σ_src 256 (3#2, 3#2, ())
#guard task.counterexample 2 (reversedP.sem 2) σ_src 256 (1#2, 1#2, ())
#guard task.counterexample 1 (onlyN16.sem 1) σ_src 256 (1#1, 1#1, ())
#guard outputPorts (wideOut.sem 1) != task.outputs 1

/-! … and the values they produce: `(x+1)(x+1) = x^2+1` is `0b101`; `top_shift` and `drop_top` give
`0b001`, `or_accumulate` `0b111` (the OR saturates), `reversed_p` puts `a = b = 1`'s `0b001` at the top,
`0b100`, and `only_n16` gives `0` at `N = 1`. The task's own value is `0b101`, `0b001`, `0b1`. -/

private def runP (d : Design2) (N : Nat) (a b : BitVec N) : Option LVec :=
  match run2 d σ_src 256 [entryOf (task.inputs N) (a, b, ())] with
  | .ok [st] => SvState.lookup st "p"
  | _ => none

#guard runP (topShift.sem 2) 2 3#2 3#2 == some (LVec.ofBitVec (0b001#3))
#guard runP (dropTop.sem 2) 2 3#2 3#2 == some (LVec.ofBitVec (0b001#3))
#guard runP (orAccumulate.sem 2) 2 3#2 3#2 == some (LVec.ofBitVec (0b111#3))
#guard runP (reversedP.sem 2) 2 1#2 1#2 == some (LVec.ofBitVec (0b100#3))
#guard runP (onlyN16.sem 1) 1 1#1 1#1 == some (LVec.ofBitVec (0#1))
#guard (task.fn 2 (3#2, 3#2, ())).1 == 0b101#3

/-! Axiom pins: standard axioms only. -/

/--
info: 'SvGolf.Tasks.Clmul.Negative.topShift_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms topShift_refuted

/--
info: 'SvGolf.Tasks.Clmul.Negative.dropTop_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dropTop_refuted

/--
info: 'SvGolf.Tasks.Clmul.Negative.orAccumulate_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms orAccumulate_refuted

/--
info: 'SvGolf.Tasks.Clmul.Negative.reversedP_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms reversedP_refuted

/--
info: 'SvGolf.Tasks.Clmul.Negative.onlyN16_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms onlyN16_refuted

/--
info: 'SvGolf.Tasks.Clmul.Negative.wideOut_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms wideOut_refuted

end SvGolf.Tasks.Clmul.Negative
