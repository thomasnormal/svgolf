import SvGolf.Comb
import SvGolf.LoadSv
import tasks.fdivp.Spec
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen

/-!
# Task `fdivp`: the negative designs do NOT satisfy the statement

Evidence that `tasks/fdivp/Spec.lean` rejects the wrong designs of this directory (`README.md` lists them all, with the
banlist case `div_op.sv` and the `check.py` stage each fails at).

Every refutation below has the shape of `clmul`'s (`tests/clmul/negative/Refute.lean`): a kernel-checked theorem saying
"IF this concrete run's outputs differ from the task (`CombTask.counterexample … = true`), or IF the design's ports differ
from the task's, at ONE format `(W, P)` in range, THEN the statement fails", and a `#guard` checking the hypothesis by
Lean's interpreter running the compiled `instantiateGD2` and `run2` (NOT by the kernel: the generate expansion does not
reduce by `rfl` or `decide +kernel`, measured for `mul`). It replaces the kernel refutations of the former 16-bit
task's `Refute.lean` (`constNan_refuted`, `rmPin_refuted`, `inexactFlag_refuted`), at the smallest format `(2, 2)`.

* **`const_nan.sv`** (`q` = the canonical quiet NaN always): at `(2, 2)`, `1 / 1` (`0b0010 / 0b0010`) is `1`
  (`0b0010`), the design gives the NaN `0b0111`.
* **`rm_pin.sv`** (an extra input `rtz`), **`status_flag.sv`** (an extra output `inexact`), **`wide_q.sv`** (a
  `W + P + 1`-bit `q`): refuted by the interface conjunct at `(2, 2)`.

The designs are loaded with `load_sv` (`SvGolf/LoadSv.lean`): extracted at elaboration time by svGolf's one extraction
path into a cache under `.lake/envelopes/`; paths are relative to the `svgolf/` package root.
-/

namespace SvGolf.Tasks.FdivP.Negative

open LeanModels.Sv SvGolf

load_sv constNan from "tests/fdivp/negative/const_nan.sv"
load_sv rmPin from "tests/fdivp/negative/rm_pin.sv"
load_sv statusFlag from "tests/fdivp/negative/status_flag.sv"
load_sv wideQ from "tests/fdivp/negative/wide_q.sv"

/-! ## The two kinds of refutation -/

/-- A concrete run that disagrees with the task at one format in range refutes the statement. -/
theorem refuted_of_run {sem : Nat → Nat → Design2} (W P : Nat) (hr : inRange W P)
    (v : BitVec (W + P) × BitVec (W + P) × Unit)
    (h : (task W P).counterexample 0 (sem W P) σ_src 256 v = true) : ¬ Statement sem :=
  fun hs => CombTask.not_computes_of_counterexample (by simp [task]) h (hs W P hr).2.2

/-- A design whose input or output ports differ from the task's at one format in range fails the interface
conjunct. -/
theorem refuted_of_ports {sem : Nat → Nat → Design2} (W P : Nat) (hr : inRange W P)
    (h : (inputPorts (sem W P) != (task W P).inputs 0 || outputPorts (sem W P) != (task W P).outputs 0) = true) :
    ¬ Statement sem := fun hs => by
  have hi := (hs W P hr).1
  rw [hi.1, hi.2] at h
  simp at h

/-! ## `const_nan.sv`: `1 / 1` at `(2, 2)` -/

theorem constNan_refuted
    (h : (task 2 2).counterexample 0 (constNan.sem 2 2) σ_src 256 (0b0010#4, 0b0010#4, ()) = true) :
    ¬ Statement constNan.sem := refuted_of_run 2 2 ⟨by decide, by decide⟩ _ h

/-! ## The interface: an extra input, an extra output, a wider `q` -/

theorem rmPin_refuted
    (h : (inputPorts (rmPin.sem 2 2) != (task 2 2).inputs 0 ||
      outputPorts (rmPin.sem 2 2) != (task 2 2).outputs 0) = true) :
    ¬ Statement rmPin.sem := refuted_of_ports 2 2 ⟨by decide, by decide⟩ h

theorem statusFlag_refuted
    (h : (inputPorts (statusFlag.sem 2 2) != (task 2 2).inputs 0 ||
      outputPorts (statusFlag.sem 2 2) != (task 2 2).outputs 0) = true) :
    ¬ Statement statusFlag.sem := refuted_of_ports 2 2 ⟨by decide, by decide⟩ h

theorem wideQ_refuted
    (h : (inputPorts (wideQ.sem 2 2) != (task 2 2).inputs 0 ||
      outputPorts (wideQ.sem 2 2) != (task 2 2).outputs 0) = true) :
    ¬ Statement wideQ.sem := refuted_of_ports 2 2 ⟨by decide, by decide⟩ h

/-! The hypotheses, by the interpreter: the run completes and disagrees with the task; the ports differ. -/

#guard (task 2 2).counterexample 0 (constNan.sem 2 2) σ_src 256 (0b0010#4, 0b0010#4, ())
#guard (inputPorts (rmPin.sem 2 2) != (task 2 2).inputs 0 || outputPorts (rmPin.sem 2 2) != (task 2 2).outputs 0)
#guard (inputPorts (statusFlag.sem 2 2) != (task 2 2).inputs 0 ||
  outputPorts (statusFlag.sem 2 2) != (task 2 2).outputs 0)
#guard (inputPorts (wideQ.sem 2 2) != (task 2 2).inputs 0 || outputPorts (wideQ.sem 2 2) != (task 2 2).outputs 0)

/-- info: 'SvGolf.Tasks.FdivP.Negative.constNan_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constNan_refuted

/-- info: 'SvGolf.Tasks.FdivP.Negative.wideQ_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wideQ_refuted

end SvGolf.Tasks.FdivP.Negative
