import SvGolf.Task
import tasks.fdivp.IEEE754

/-!
# Task `fdivp` (trusted statement): IEEE 754 division, PARAMETRIC in the format

The variant of the statement that needs NO change to `SvGolf/Task.lean` (`design/fdiv-param/TASK.md`
explains the choice of this form, "Option C", and `design/fdiv-param/Task.lean.patch` is the unapplied
`CombTask2` alternative): the two-parameter family is a family of fixed-size `CombTask`s, one per `(W, P)`,
and the statement quantifies over the pairs with `CombTask.StatementFixed` at each.

Module (two parameters, in this order; port order as written):

```systemverilog
module fdiv #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a,
  input  logic [W+P-1:0] b,
  output logic [W+P-1:0] q
);
```

`W` is the width of the biased-exponent field and `P` the precision (the significand digits
including the implicit leading bit), so the trailing significand has `P - 1` bits and a pattern
has `1 + W + (P - 1) = W + P` bits: binary16 is `W = 5, P = 11`, bfloat16 `W = 8, P = 8`,
binary32 `W = 8, P = 24`, binary64 `W = 11, P = 53`.

Statement: for every `W ≥ 2` and `P ≥ 2` (the spec's own well-formedness `Format.hw`, `Format.hp`)
with `W + P + 1 < 2^31` (so that the widths `W + P` and `W + P + 1`, `int` expressions of the module,
stay below `2^31`, the values an `int` holds), the design has exactly the ports `a`, `b`
(inputs, `W + P` bits) and `q` (output, `W + P` bits), no process is clocked, there is no
combinational loop, every run terminates, and in every cycle whose stimulus drives `a` and
`b` with known values the snapshot's `q` is `SvGolf.IEEE754.divide ⟨W, P⟩ .roundTiesToEven a b`,
the trusted spec of `svgolf/tasks/fdivp/IEEE754.lean` at that format. `REVIEW.md` lists the modelling choices.
-/

namespace SvGolf.Tasks.FdivP

open SvGolf SvGolf.IEEE754

/-- The storage width of the format `⟨W, P⟩`: `1 + W + (P - 1) = W + P`. -/
theorem k_eq (W P : Nat) (hP : 1 ≤ P) : 1 + W + (P - 1) = W + P := by omega

/-- **The function of the task**: `divide ⟨W, P⟩ .roundTiesToEven` on `(W + P)`-bit patterns,
for `2 ≤ W` and `2 ≤ P` (the spec's `Format` requires both). The `BitVec.cast`s only transport a
pattern along the equation `Format.k = W + P` (they leave `toNat` unchanged:
`fdivBits_toNat`); outside the range the function is `0`, which no statement looks at. -/
def fdivBits (W P : Nat) (a b : BitVec (W + P)) : BitVec (W + P) :=
  if h : 2 ≤ W ∧ 2 ≤ P then
    let f : Format := ⟨W, P, h.1, h.2⟩
    have hk : f.k = W + P := k_eq W P (by omega)
    (divide f .roundTiesToEven (a.cast hk.symm) (b.cast hk.symm)).cast hk
  else 0#(W + P)

/-- The task at the format `⟨W, P⟩`, as a fixed-size `CombTask` (its own parameter is ignored and
taken at `0`, as in `CombTask.StatementFixed`): inputs `a b : BitVec (W + P)`, output
`q = fdivBits W P a b`. -/
def task (W P : Nat) : CombTask where
  inRange K := K = 0
  inputs _ := [("a", W + P), ("b", W + P)]
  outputs _ := [("q", W + P)]
  fn _ := fun (a, b, ()) => (fdivBits W P a b, ())

/-- Which parameter pairs the statement covers: the spec's own `Format` well-formedness, and
`W + P + 1 < 2^31`, so that the port width `W + P` and the exponent width `W + P + 1` a design computes
in (the ports' `[W+P-1:0]` and a `localparam integer EW = W + P + 1`, evaluated as `int`s) stay below
`2^31`, the values an `int` holds. -/
def inRange (W P : Nat) : Prop := 2 ≤ W ∧ 2 ≤ P ∧ W + P + 1 < 2 ^ 31

/-- **The challenge statement** for the two-parameter design family
`Submission.design.sem : Nat → Nat → Design2`: at every `W, P ≥ 2` in range the design satisfies the
fixed-size task at that format. A submission proves
`SvGolf.Tasks.FdivP.Statement Submission.design.sem`. -/
abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) : Prop :=
  ∀ W P, inRange W P → (task W P).StatementFixed (sem W P)

/-! Sanity checks on the statement's data (closed, by `decide`/`rfl`). -/

/-- binary16, bfloat16-like and binary32 are in range. -/
example : inRange 5 11 ∧ inRange 8 8 ∧ inRange 8 24 := by
  simp [inRange]

/-- The range ends where `W + P + 1` reaches `2^31`, the first value an `int` does not hold. -/
example : inRange (2 ^ 31 - 4) 2 ∧ ¬ inRange (2 ^ 31 - 3) 2 ∧ inRange 2 (2 ^ 31 - 4) ∧
    ¬ inRange 2 (2 ^ 31 - 3) := by
  simp [inRange]

/-- The input names are distinct (the non-vacuity theorem `CombTask.SatisfiedAt.exists_run`
needs it), at every parameter pair. -/
example (W P : Nat) : (((task W P).inputs 0).map Prod.fst).Nodup := by
  simp [task]

/-- The casts do not change values. -/
theorem fdivBits_toNat (W P : Nat) (h : 2 ≤ W ∧ 2 ≤ P) (a b : BitVec (W + P)) :
    (fdivBits W P a b).toNat =
      (divide ⟨W, P, h.1, h.2⟩ .roundTiesToEven
        (a.cast (k_eq W P (by omega)).symm) (b.cast (k_eq W P (by omega)).symm)).toNat := by
  simp [fdivBits, h]

/-- Golden vectors of the spec through the task's function: `1 / 3 = 0x3555` in binary16,
`1 / 3 = 0x3EAAAAAB` in binary32, and bfloat16-like `(8, 8)`: `1 / 3 = 0x3EAB`. -/
example : ((task 5 11).fn 0 (0x3C00#16, 0x4200#16, ())).1 = 0x3555#16 := by decide
example : ((task 8 24).fn 0 (0x3F800000#32, 0x40400000#32, ())).1 = 0x3EAAAAAB#32 := by decide
example : ((task 8 8).fn 0 (0x3F80#16, 0x4040#16, ())).1 = 0x3EAB#16 := by decide
/-- `0 / 0` is the canonical NaN of the format (`0x7E00` in binary16). -/
example : ((task 5 11).fn 0 (0x0000#16, 0x0000#16, ())).1 = 0x7E00#16 := by decide
/-- The smallest formats are in range: `W = 2, P = 2` is 4 bits. -/
example : ((task 2 2).fn 0 (0b0011#4, 0b0100#4, ())).1 = fdivBits 2 2 0b0011#4 0b0100#4 := rfl

end SvGolf.Tasks.FdivP
