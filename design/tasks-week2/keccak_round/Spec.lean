import SvGolf.Task

/-!
# DRAFT task `keccak_round`: one round of Keccak-p on 25 lanes of `W` bits

**UNTRUSTED DRAFT** (week-2 task study, WP-T0): lives under `svgolf/design/tasks-week2/`, is not part
of the `tasks` library, and becomes trusted only if the lead and the maintainers adopt it and move it to
`svgolf/tasks/keccak_round/Spec.lean`.

Module (port order as written; `W` is the module's only parameter; a 2-D packed port such as
`logic [24:0][W-1:0]` has the same flat width `25*W`, so a design may declare the ports either way):

```systemverilog
module keccak_round #(parameter int W = 16) (
  input  logic [25*W-1:0] a,    // the state: bit W*(x+5*y)+z is A[x][y][z]  (FIPS 202, 3.1.2)
  input  logic [W-1:0]    rc,   // the round constant RC[i_r], lane width W (an input, not a table)
  output logic [25*W-1:0] y     // iota(chi(pi(rho(theta(a)))), rc)
);
```

Statement: for every `W >= 1` the design has exactly the ports `a`, `rc` (inputs, `25*W` and `W`
bits) and `y` (output, `25*W` bits), no process is clocked, every run terminates, and in every
cycle whose stimulus drives `a` and `rc` with known values the snapshot's `y` is
`iota rc (chi (pi (rho (theta A))))` for the state `A` that `a` encodes, with the five step
mappings written out below exactly as FIPS 202 Section 3.2 states them (Algorithms 1 to 4 and 6;
Algorithm 5, the round-constant LFSR, is deliberately NOT part of the statement: `rc` is an input).

For `W` in `{1, 2, 4, 8, 16, 32, 64}` this is the round of Keccak-f[25W] (Keccak-p[25W, nr] for any
round count `nr`: the constants differ per round, the round function does not). For other `W`
the same formulas define the natural extension (rotations are by the offset mod `W`); the task
asks for it, so the proof must hold "for every lane width".

The step mappings are written bit by bit, in FIPS 202's own coordinates, on purpose: a reader
checks them against the standard line by line, with no lane arithmetic in between. `pack`/`unpack`
are the only encoding, and `SpecFacts.lean` proves they are inverse to each other.

Sources of truth used to cross-check this file (none of them is trusted by the checker):
* `oracle.py` (two independent Python implementations, bit-level and lane-level, which agree);
* the Keccak team's XKCP intermediate values `KeccakF-{200,400,800,1600}-IntermediateValues.txt`
  (every round and step, widths 8, 16, 32, 64), reproduced below as `decide +kernel` examples;
* Python's `hashlib.sha3_256`/`sha3_512` (the 24-round composition of the lane oracle matches them).
-/

namespace SvGolf.Tasks.KeccakRound

open SvGolf

/-! ## Bits and the flat encoding -/

/-- A state as FIPS 202 sees it: `A x y z` is the bit in column `x`, row `y`, depth `z`.
Only `x, y < 5` and `z < W` are ever read. -/
abbrev Bits := Nat → Nat → Nat → Bool

/-- The `n`-bit vector whose bit `k` (counted from the least significant end) is `f k`. -/
def ofBits : (n : Nat) → (Nat → Bool) → BitVec n
  | 0, _ => 0#0
  | n + 1, f => ofBits n (fun k => f (k + 1)) ++ BitVec.ofBool (f 0)

/-- The state a flat `25*W`-bit vector encodes: `A[x][y][z]` is bit `W*(5*y+x)+z` (FIPS 202, 3.1.2:
lane `(x, y)` is lane number `x + 5*y`, its bit `z` is bit `W*(x+5*y)+z` of the string). -/
def unpack (W : Nat) (s : BitVec (25 * W)) : Bits :=
  fun x y z => s.getLsbD (W * (5 * y + x) + z)

/-- The flat vector of a state (the inverse encoding). -/
def pack (W : Nat) (A : Bits) : BitVec (25 * W) :=
  ofBits (25 * W) fun k => A (k / W % 5) (k / W / 5) (k % W)

/-! ## The five step mappings (FIPS 202, Section 3.2), lane width `W` -/

/-- Algorithm 1, the column parities `C[x][z]`. -/
def colPar (A : Bits) (x z : Nat) : Bool :=
  A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z

/-- theta: `A'[x][y][z] = A[x][y][z] xor C[x-1][z] xor C[x+1][z-1]`, `x` mod 5, `z` mod `W`. -/
def theta (W : Nat) (A : Bits) : Bits := fun x y z =>
  A x y z ^^ colPar A ((x + 4) % 5) z ^^ colPar A ((x + 1) % 5) ((z + W - 1) % W)

/-- Algorithm 2's walk: `walk t` is the lane `(x, y)` that gets the offset `(t+1)(t+2)/2`;
it starts at `(1, 0)` and moves `(x, y) <- (y, (2x + 3y) mod 5)`. -/
def walk : Nat → Nat × Nat
  | 0 => (1, 0)
  | t + 1 => ((walk t).2, (2 * (walk t).1 + 3 * (walk t).2) % 5)

/-- The (unreduced) rho offset of lane `(x, y)`: `0` for `(0, 0)`, else `(t+1)(t+2)/2` for the `t < 24`
with `walk t = (x, y)`. -/
def rhoOffset (x y : Nat) : Nat :=
  match (List.range 24).find? (fun t => walk t == (x, y)) with
  | some t => (t + 1) * (t + 2) / 2
  | none => 0

/-- rho: `A'[x][y][z] = A[x][y][z - offset(x,y)]`, `z` mod `W` (the offset is reduced mod `W`). -/
def rho (W : Nat) (A : Bits) : Bits := fun x y z =>
  A x y ((z + W - rhoOffset x y % W) % W)

/-- pi: `A'[x][y][z] = A[(x + 3y) mod 5][x][z]`. -/
def pi (A : Bits) : Bits := fun x y z => A ((x + 3 * y) % 5) x z

/-- chi: `A'[x][y][z] = A[x][y][z] xor ((A[x+1][y][z] xor 1) and A[x+2][y][z])`. -/
def chi (A : Bits) : Bits := fun x y z =>
  A x y z ^^ (!A ((x + 1) % 5) y z && A ((x + 2) % 5) y z)

/-- iota with round constant `rc`: `A'[0][0][z] = A[0][0][z] xor rc[z]`, the other lanes unchanged. -/
def iota (W : Nat) (rc : BitVec W) (A : Bits) : Bits := fun x y z =>
  if x = 0 ∧ y = 0 then A x y z ^^ rc.getLsbD z else A x y z

/-- One round: `Rnd(A, i_r) = iota(chi(pi(rho(theta(A)))), i_r)` (FIPS 202, Section 3.3). -/
def round (W : Nat) (rc : BitVec W) (A : Bits) : Bits :=
  iota W rc (chi (pi (rho W (theta W A))))

/-! ## The task -/

/-- The task: inputs `a : BitVec (25*W)`, `rc : BitVec W`; output `y = pack (round rc (unpack a))`;
for `W >= 1`. -/
def task : CombTask where
  inRange W := 1 ≤ W
  inputs W := [("a", 25 * W), ("rc", W)]
  outputs W := [("y", 25 * W)]
  fn W := fun (a, rc, ()) => (pack W (round W rc (unpack W a)), ())

/-- **The challenge statement.** A submission proves
`SvGolf.Tasks.KeccakRound.Statement Submission.design.sem`. -/
abbrev Statement : (Nat → LeanModels.Sv.Design2) → Prop := task.Statement

/-! ## Sanity checks on the statement's data (closed; `decide +kernel` is kernel evaluation, no axiom) -/

/-- The scoring points `W = 16` (Keccak-f[400]) and `W = 64` (Keccak-f[1600]) are in range. -/
example : task.inRange 16 ∧ task.inRange 64 := by simp [task]

/-- The input names are distinct (the non-vacuity theorem `CombTask.SatisfiedAt.exists_run`
needs it), at every `W`. -/
example (W : Nat) : ((task.inputs W).map Prod.fst).Nodup := by simp [task]

/-- The rho offsets this file derives from Algorithm 2's walk equal the table of the Keccak
reference / XKCP (`RhoOffset` unreduced, lane `x + 5y`): two sources, one function. -/
def rhoTable : List Nat :=
  [0, 1, 190, 28, 91, 36, 300, 6, 55, 276, 3, 10, 171, 153, 231, 105, 45, 15, 21, 136, 210, 66, 253, 120, 78]

example : ∀ i : Fin 25, rhoOffset (i.val % 5) (i.val / 5) = rhoTable.getD i.val 0 := by decide +kernel

/-- Zero state: every step but iota is trivial, so the round just writes `rc` into lane `(0, 0)`. -/
example : (task.fn 16 (0#400, 0x8082#16, ())).1 = 0x8082#400 := by decide +kernel

/-- xkcp KeccakF-200-IntermediateValues example 0 round 1. -/
theorem xkcp_w8_round1 :
    (task.fn 8 (0x00000000000000000000000000000000000000000000000001#200,
      0x82#8, ())).1 =
      0x04000500010010040014000000020220200000009001801083#200 := by
  decide +kernel

/-- xkcp KeccakF-400-IntermediateValues example 0 round 2. -/
theorem xkcp_w16_round2 :
    (task.fn 16 (0x0004000001040000010000001000040000001400000002020000020000020020200000002020000090000001800010008083#400,
      0x808a#16, ())).1 =
      0x7c604849b62eef02b5850fa2295b66d24f4e247855170a194acc8984095b5ae593e1eb3382c1eb628d59d91034f002fcc46c#400 := by
  decide +kernel

/-- oracle (no published vector at this width). -/
theorem oracle_w4 :
    (task.fn 4 (0x999dd251de512148239292d22#100,
      0x8#4, ())).1 =
      0x4b340a5986d398e3c6bdcdb29#100 := by
  decide +kernel


end SvGolf.Tasks.KeccakRound
