import SvGolf.Task

/-!
# Task `mul`: N-bit unsigned multiplier (TRUSTED)

The main svGolf challenge. Module (port order as written; `N` is the
module's only parameter):

```systemverilog
module mul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-1:0] p
);
```

Statement: for every `N ≥ 1`, the design has exactly the ports `a`, `b`
(inputs, `N` bits) and `p` (output, `2N` bits), no process is clocked, every
run terminates, and in every cycle whose stimulus drives `a` and `b` with
known values the snapshot's `p` is the FULL product `a * b`: the
natural-number product of the two unsigned inputs, as a `2N`-bit vector.
Nothing is truncated: the product of two `N`-bit numbers is below `2^(2N)`
(`fn_toNat` below), so `p` carries it exactly.

Run-time `+ - * / % **` are banned (`task.json`), so the circuit has to be
built from bitwise logic; constant arithmetic (parameter expressions, genvar
indices such as `s[i-1][j+1]`) is fine.
-/

namespace SvGolf.Tasks.Mul

open SvGolf

/-- The task: inputs `a b : BitVec N`, output `p = a * b` on `2N` bits, for
`N ≥ 1`. -/
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N)]
  fn N := fun (a, b, ()) => (BitVec.ofNat (2 * N) (a.toNat * b.toNat), ())

/-- **The challenge statement.** A submission proves
`SvGolf.Tasks.Mul.Statement Submission.design.sem`. -/
abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement

/-! Sanity checks on the statement's data. -/

/-- The scoring point `N = 16` (and the reported points 8 and 32) are in range. -/
example : task.inRange 16 ∧ task.inRange 8 ∧ task.inRange 32 := by simp [task]

/-- The input names are distinct (the non-vacuity theorem
`CombTask.SatisfiedAt.exists_run` needs it), at every `N`. -/
example (N : Nat) : ((task.inputs N).map Prod.fst).Nodup := by
  simp [task]

/-- **No truncation**: the output is exactly the natural-number product. -/
theorem fn_toNat (N : Nat) (a b : BitVec N) :
    (task.fn N (a, b, ())).1.toNat = a.toNat * b.toNat := by
  show (BitVec.ofNat (2 * N) (a.toNat * b.toNat)).toNat = a.toNat * b.toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [Nat.two_mul, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt

/-- The same function, read as `BitVec` multiplication at double width. -/
theorem fn_eq_mul (N : Nat) (a b : BitVec N) :
    (task.fn N (a, b, ())).1 = a.setWidth (2 * N) * b.setWidth (2 * N) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : ∀ x : BitVec N, x.toNat < 2 ^ (2 * N) := fun x =>
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  rw [fn_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (hlt a), Nat.mod_eq_of_lt (hlt b), Nat.mod_eq_of_lt]
  rw [Nat.two_mul, Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt

/-- Concrete values: `15 * 15 = 225` at `N = 4`, `255 * 255 = 65025` at
`N = 8`, `3 * 3 = 9` at `N = 2` (the top bit is used). -/
example : (task.fn 4 (15#4, 15#4, ())).1 = 225#8 := by decide
example : (task.fn 8 (255#8, 255#8, ())).1 = 65025#16 := by decide
example : (task.fn 2 (3#2, 3#2, ())).1 = 9#4 := by decide

end SvGolf.Tasks.Mul
