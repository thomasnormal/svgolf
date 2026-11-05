import LeanModels.Sv.Ingest2
import SvGolf.LoadSv
import SvGolf.Comb
import tasks.mul.Spec

/-!
Validation tooling, not part of any library: ls-sv `run2` on the reference
envelope against `a * b`, exhaustive at N = 1..5 and pseudo-random (plus
corners) at N = 8 and 16, by Lean's interpreter. Each `#eval` prints
`(vectors, disagreements)`. Run from `svgolf/` (through the slot wrapper):

    lake env lean tests/mul/validate/RunAgree.lean

Measured 2026-10-28: N = 1..5 exhaustive (1364 vectors) and 303 + 43 random
vectors at N = 8, 16, no disagreement (about 3 minutes).
-/

open LeanModels.Sv SvGolf SvGolf.Tasks.Mul

load_sv ref from "tasks/mul/reference/mul_n.sv"

def agreeAt (N : Nat) (a b : Nat) : Bool :=
  !(task.counterexample N (ref.sem N) σ_src 4096 (BitVec.ofNat N a, BitVec.ofNat N b, ()))
  && (match run2 (ref.sem N) σ_src 4096 [entryOf (task.inputs N) (BitVec.ofNat N a, BitVec.ofNat N b, ())] with
      | .ok [_] => true | _ => false)

def exhaustive (N : Nat) : Nat × Nat :=
  let all := (List.range (2 ^ N)).flatMap fun a => (List.range (2 ^ N)).map fun b => agreeAt N a b
  (all.length, (all.filter (· == false)).length)

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def randomRuns (N k : Nat) : Nat × Nat := Id.run do
  let mut s := 12345 + N
  let mut bad := 0
  for _ in [0:k] do
    s := lcg s; let a := s % 2 ^ N
    s := lcg s; let b := s % 2 ^ N
    if !agreeAt N a b then bad := bad + 1
  -- corners
  for (a, b) in [(2 ^ N - 1, 2 ^ N - 1), (2 ^ N - 1, 1), (0, 2 ^ N - 1)] do
    if !agreeAt N a b then bad := bad + 1
  return (k + 3, bad)

#eval (List.range 5).map fun i => (i + 1, exhaustive (i + 1))
#eval randomRuns 8 300
#eval randomRuns 16 40
