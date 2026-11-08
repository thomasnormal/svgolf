import SvGolf.Task

/-!
# Task `_example`: N-bit bitwise AND (TRUSTED)

The toy task that exercises the svGolf pipeline end to end. It is not a real
challenge: the optimum (N two-input AND gates, depth 1) is obvious.

Module (port order as written; `N` is the module's only parameter):

```systemverilog
module band #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0] y
);
```

Statement: for every `N` with `1 ≤ N < 2^31` (the values an `int` parameter
holds), the design has exactly the ports `a`, `b` (inputs, `N` bits) and `y`
(output, `N` bits), no process is clocked, there is no combinational loop,
every run terminates, and in
every cycle whose stimulus drives `a` and `b` with known values the
snapshot's `y` is `a &&& b`.
-/

namespace SvGolf.Tasks.Example

open SvGolf

/-- The task: inputs `a b : BitVec N`, output `y = a &&& b`, for `1 ≤ N < 2^31`. -/
def task : CombTask where
  inRange N := 1 ≤ N ∧ N < 2 ^ 31
  inputs N := [("a", N), ("b", N)]
  outputs N := [("y", N)]
  fn _ := fun (a, b, ()) => (a &&& b, ())

/-- **The challenge statement.** A submission proves
`SvGolf.Tasks.Example.Statement Submission.design.sem`. -/
abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement

/-! Sanity checks on the statement's data (closed, by `decide`). -/

/-- The scoring point `N = 16` is in range. -/
example : task.inRange 16 := by simp [task]

/-- The range ends below `2^31`, the values an `int` parameter holds. -/
example : task.inRange (2 ^ 31 - 1) ∧ ¬ task.inRange (2 ^ 31) := by simp [task]

/-- The input names are distinct (the non-vacuity theorem
`CombTask.SatisfiedAt.exists_run` needs it), at every `N`. -/
example (N : Nat) : ((task.inputs N).map Prod.fst).Nodup := by
  simp [task]

/-- The function on a concrete value: `0b1100 &&& 0b1010 = 0b1000`. -/
example : (task.fn 4 (0b1100#4, 0b1010#4, ())).1 = 0b1000#4 := by decide

end SvGolf.Tasks.Example
