import SvGolf.Task

/-!
# DRAFT task `clmul`: N-bit carry-less multiplier (polynomial product over GF(2))

**UNTRUSTED DRAFT** (week-2 task study, WP-T0), not part of the `tasks` library.

Module (port order as written; `N` is the module's only parameter):

```systemverilog
module clmul_n #(parameter int N = 16) (
  input  logic [N-1:0]   a, b,
  output logic [2*N-2:0] p
);
```

Statement: for every `N >= 1`, the design has exactly the ports `a`, `b` (inputs, `N` bits) and `p`
(output, `2N-1` bits), no process is clocked, every run terminates, and in every cycle whose stimulus
drives `a` and `b` with known values the snapshot's `p` is the coefficient vector of the product
of the two polynomials over GF(2) that `a` and `b` encode (bit `i` is the coefficient of `x^i`):
`p_k = XOR over i + j = k of (a_i AND b_j)`, for `0 <= k <= 2N-2`. The product of two polynomials of
degree below `N` has degree at most `2N-2`, so `p` loses nothing.

The same bits are the unsigned product `a * b` with every carry dropped (`PCLMULQDQ`, the GHASH
core, the polynomial multiplication of every binary-field and CRC/BCH construction).
-/

namespace SvGolf.Tasks.Clmul

open SvGolf

/-- The `n`-bit vector whose bit `k` (from the least significant end) is `f k`. -/
def ofBits : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => ofBits n (fun k => f (k + 1)) ++ BitVec.ofBool (f 0)

/-- Coefficient `k` of the product polynomial: the XOR of `a_i b_j` over `i + j = k`. -/
def coeff (N : Nat) (a b : BitVec N) (k : Nat) : Bool :=
  (List.range N).foldl (fun acc i => acc ^^ (decide (i ≤ k) && a.getLsbD i && b.getLsbD (k - i))) false

/-- The task: inputs `a b : BitVec N`, output `p = a (x) b` on `2N-1` bits, for `N ≥ 1`. -/
def task : CombTask where
  inRange N := 1 ≤ N
  inputs N := [("a", N), ("b", N)]
  outputs N := [("p", 2 * N - 1)]
  fn N := fun (a, b, ()) => (ofBits (2 * N - 1) (coeff N a b), ())

/-- **The challenge statement.** A submission proves `SvGolf.Tasks.Clmul.Statement Submission.design.sem`. -/
abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement

/-! ## Sanity checks (closed; `decide +kernel` is kernel evaluation, no axiom) -/

example : task.inRange 16 ∧ task.inRange 64 := by simp [task]

example (N : Nat) : ((task.inputs N).map Prod.fst).Nodup := by simp [task]

/-- `(x + 1)^2 = x^2 + 1` over GF(2), at `N = 2`. -/
example : (task.fn 2 (0b11#2, 0b11#2, ())).1 = 0b101#3 := by decide

/-- `(x^2 + 1)(x + 1) = x^3 + x^2 + x + 1`, at `N = 3` (five output bits). -/
example : (task.fn 3 (0b101#3, 0b011#3, ())).1 = 0b01111#5 := by decide

/-- `(1 + x + ... + x^15)^2 = 1 + x^2 + ... + x^30` over GF(2), at `N = 16` (31 output bits). -/
example : (task.fn 16 (0xffff#16, 0xffff#16, ())).1 = 0x55555555#31 := by decide +kernel

/-- FIPS 197 Section 4.2 (2001 edition: `{57} * {83} = {c1}`; 2023 edition, Eq. (4.7): `{57} * {13} = {fe}`): the unreduced
products are `0x2b79` and `0x0589`; reduced modulo `x^8+x^4+x^3+x+1` (`0x11b`) they give those bytes
(`validate.py` does the reduction). -/
example : (task.fn 8 (0x57#8, 0x83#8, ())).1 = 0x2b79#15 := by decide +kernel
example : (task.fn 8 (0x57#8, 0x13#8, ())).1 = 0x0589#15 := by decide +kernel

end SvGolf.Tasks.Clmul
