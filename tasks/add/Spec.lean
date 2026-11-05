import SvGolf.Task

/-!
# Task `add`: N-bit adder with carry in and carry out (TRUSTED)

The warm-up challenge. Module (port order as written; `N` is the module's
only parameter):

```systemverilog
module add_n #(parameter int N = 16) (
  input  logic [N-1:0] a, b,
  input  logic         cin,
  output logic [N-1:0] s,
  output logic         cout
);
```

Statement: for every `N ≥ 1`, the design has exactly the input ports `a`,
`b` (`N` bits) and `cin` (1 bit), in that order, and exactly the output
ports `s` (`N` bits) and `cout` (1 bit), in that order; every run
terminates; and in every cycle whose stimulus drives `a`, `b`, `cin` with
known values, the snapshot holds `{cout, s} = a + b + cin`: with
`t = a + b + cin` computed in the natural numbers, `s = t mod 2^N` and
`cout = t / 2^N` (which is 0 or 1).

The banned run-time operators (`+ - * / % **`) are listed in `task.json`
and enforced by the checker's banlist stage, not here.
-/

namespace SvGolf.Tasks.Add

open SvGolf

/-- The task: inputs `a b : BitVec N`, `cin : BitVec 1`; outputs
`s = (a + b + cin) mod 2^N` and `cout = (a + b + cin) / 2^N`, the sum taken
in `Nat`; for `N ≥ 1`. -/
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N), ("cin", 1)]
  outputs N := [("s", N), ("cout", 1)]
  fn N := fun (a, b, cin, ()) =>
    let t := a.toNat + b.toNat + cin.toNat
    (BitVec.ofNat N t, BitVec.ofNat 1 (t / 2 ^ N), ())

/-- **The challenge statement.** A submission proves
`SvGolf.Tasks.Add.Statement Submission.design.sem`. -/
abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement

/-! ## Sanity checks on the statement's data

They are proved, so they add nothing to the trusted base; they are here so
that a reader can see the statement means what the prose says. -/

/-- The scoring point `N = 16` is in range. -/
example : task.inRange 16 := by simp [task]

/-- The input names are distinct (the non-vacuity theorem
`CombTask.SatisfiedAt.exists_run` needs it), at every `N`. -/
example (N : Nat) : ((task.inputs N).map Prod.fst).Nodup := by
  simp [task]

/-- `0xFFFF + 0x0001 + 0 = 0x1_0000`: `s = 0`, `cout = 1`. -/
example : (task.fn 16 (0xFFFF#16, 0x0001#16, 0#1, ())).1 = 0#16 ∧
    (task.fn 16 (0xFFFF#16, 0x0001#16, 0#1, ())).2.1 = 1#1 := by decide

/-- `0xFFFF + 0xFFFF + 1 = 0x1_FFFF`: `s = 0xFFFF`, `cout = 1`. -/
example : (task.fn 16 (0xFFFF#16, 0xFFFF#16, 1#1, ())).1 = 0xFFFF#16 ∧
    (task.fn 16 (0xFFFF#16, 0xFFFF#16, 1#1, ())).2.1 = 1#1 := by decide

/-- `3 + 4 + 1 = 8` at `N = 4`: no carry out. -/
example : (task.fn 4 (3#4, 4#4, 1#1, ())).1 = 8#4 ∧
    (task.fn 4 (3#4, 4#4, 1#1, ())).2.1 = 0#1 := by decide

/-- **The arithmetic reading of `fn`**, at every `N`: `cout · 2^N + s` is
exactly `a + b + cin` in the natural numbers (so `{cout, s}` is the
`(N+1)`-bit sum, and nothing is lost to the 1-bit width of `cout`). -/
theorem fn_arith (N : Nat) (a b : BitVec N) (cin : BitVec 1) :
    (task.fn N (a, b, cin, ())).2.1.toNat * 2 ^ N + (task.fn N (a, b, cin, ())).1.toNat =
      a.toNat + b.toNat + cin.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc : cin.toNat < 2 := cin.isLt
  have hp := Nat.two_pow_pos N
  have hq : (a.toNat + b.toNat + cin.toNat) / 2 ^ N < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp]
    omega
  simp only [task, BitVec.toNat_ofNat, Nat.pow_one, Nat.mod_eq_of_lt hq]
  exact Nat.div_add_mod' _ _

end SvGolf.Tasks.Add
