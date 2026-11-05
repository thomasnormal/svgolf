import SvGolf.TaskSeq

/-!
# Task `sorter`: a streaming sorter of N unsigned W-bit values
# (DRAFT of TRUSTED text, for review, 2026-11-04; contract C8 of `design/sequential/CONTRACT.md`)

Module (port order as written; `N`, `W` are the module's parameters, in this order):

```systemverilog
module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
```

**Protocol** (`StreamTask`, `SvGolf/TaskSeq.lean`; C1, C2, C8): synchronous active-high reset `rst`;
claims from the cycle after its release; `start` a one-cycle pulse raised only when the design is
idle (no transaction yet, or the previous one's `N` outputs emitted); after a `start`, `in_valid`
is 1 for exactly the `N` cycles beginning the cycle after it (no gaps), carrying the values
`x[0] .. x[N-1]` on `in_data`, and 0 otherwise. There is no output backpressure.

**Guarantee.** `out_valid` is KNOWN at every cycle after the release, and 0 before the first
`start`. From each `start` to the next, `out_valid` is 1 on exactly `N` cycles, all at most `lat`
cycles after the edge that samples `start`, and the `out_data` values on those cycles, in order,
are the input values sorted ascending as unsigned numbers, duplicates kept. `out_data` is cared
about only where `out_valid` = 1; the valid cycles may have gaps.

The declared latency `lat` is the submission's; the checker pins its value at the scoring point and
the score uses it. Run-time operators are not banned.

**Range.** `N, W ≥ 1` and `N·W < 2^31`: the parameters are `int`, and a design that buffers the whole
stream declares `N·W` bits; every such width must stay in the 32-bit range, where a real elaboration
and ls-sv's unbounded constant tier agree (`PDesign.int32Agrees`; Task v2 decision 1).
-/

namespace SvGolf.Tasks.Sorter

open SvGolf

/-- The parameters `(N, W)`. -/
abbrev Params := Nat × Nat

/-- Insert `a` into an ascending list (unsigned order), before the first element it is `≤` to. -/
def insertAsc {W : Nat} (a : BitVec W) : List (BitVec W) → List (BitVec W)
  | [] => [a]
  | b :: bs => if a.toNat ≤ b.toNat then a :: b :: bs else b :: insertAsc a bs

/-- Insertion sort, ascending, unsigned: `List.insertionSort (· ≤ ·)` (C8), written out here
because the trusted text imports no Mathlib (structural recursion: the kernel evaluates it). -/
def sortAsc {W : Nat} : List (BitVec W) → List (BitVec W)
  | [] => []
  | a :: as => insertAsc a (sortAsc as)

/-- **The task** (C8). -/
def task : StreamTask Params where
  inRange p := 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 * p.2 < 2 ^ 31
  clk := "clk"
  rst := "rst"
  start := "start"
  inValid := "in_valid"
  inData := "in_data"
  outValid := "out_valid"
  outData := "out_data"
  width p := p.2
  count p := p.1
  spec _ xs := sortAsc xs

/-- **The challenge statement**, for the two-parameter design family `sem N W` and the latency
function `lat N W`. -/
abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) (lat : Nat → Nat → Nat) : Prop :=
  task.Statement (fun p => sem p.1 p.2) (fun p => lat p.1 p.2)

/-! ## Sanity checks on the statement's data (proved; they add nothing to the trusted base) -/

/-- Duplicates kept, unsigned order. -/
example : sortAsc [3#4, 15#4, 0#4, 3#4, 8#4] = [0#4, 3#4, 3#4, 8#4, 15#4] := by decide

/-- A typical point is in range; the 32-bit bound excludes `N·W ≥ 2^31`. -/
example : task.inRange (8, 8) ∧ ¬ task.inRange (2 ^ 16, 2 ^ 15) := by
  simp [task]

/-- The port names are distinct. -/
example : ["clk", "rst", "start", "in_valid", "in_data"].Nodup ∧
    ["out_valid", "out_data"].Nodup := by
  decide

end SvGolf.Tasks.Sorter
