import tasks.clmul.Spec

/-!
# Task `clmul`: the Lean spec's table, for `validate.py`

Prints one line `N a b p` (decimal) for EVERY pair `(a, b)` of `N`-bit inputs at `N = 1 .. 7`, and for a fixed
list of corner/sample pairs at larger `N`, computed by the TRUSTED `task.fn` (through Lean's interpreter).
`validate.py` compares every line with the independent Python oracle and with Kronecker substitution.
Run by `lake env lean --run tests/clmul/validate/Dump.lean` from `svgolf/`.
-/

open SvGolf.Tasks.Clmul in
def row (N : Nat) (a b : Nat) : String :=
  let r := (task.fn N (BitVec.ofNat N a, BitVec.ofNat N b, ())).1
  s!"{N} {a} {b} {r.toNat}"

/-- Deterministic sample pairs at width `N`: corners, then a linear-congruential walk. -/
def samples (N : Nat) : List (Nat × Nat) :=
  let top := 2 ^ N - 1
  let rec walk (k : Nat) (x y : Nat) : List (Nat × Nat) :=
    match k with
    | 0 => []
    | k + 1 =>
      let x' := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
      let y' := (y * 2862933555777941757 + 3037000493) % 2 ^ 64
      (x' % 2 ^ N, y' % 2 ^ N) :: walk k x' y'
  [(0, 0), (top, top), (top, 0), (0, top), (1, top), (top, 1), (2 ^ (N - 1), top), (top / 3, top / 5)]
    ++ walk 24 (N + 1) (3 * N + 7)

def main : IO Unit := do
  for N in [1, 2, 3, 4, 5, 6, 7] do
    for a in List.range (2 ^ N) do
      for b in List.range (2 ^ N) do
        IO.println (row N a b)
  for N in [8, 9, 12, 13, 16, 17, 24, 31, 32, 33, 48, 64] do
    for (a, b) in samples N do
      IO.println (row N a b)
