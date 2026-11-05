# Task `matmul`: N×N signed matrix multiplication, clocked

**Preview, not ranked yet.** The statement is being revised to cover the outputs on the wire and unknown
values at reset; submissions are not ranked until then.

Multiply two `N × N` matrices of signed `W`-bit entries, with every sum wrapping at `AccW` bits. This is the
first CLOCKED task. The design has a clock, a reset and a handshake: it reads `A` and `B` when `start` is
pulsed, and raises `done` when `C` holds the product. The proof covers every `N, W, AccW ≥ 1`, and it also
proves the cycle count: the score is that count times the clock period, beside the area. So the task is the
schedule: how many multipliers, how many cycles, and how short a cycle.

Status (PLAN4.md, section 1):

```
trusted statement: complete (txtask-v1)   run2 proof: complete (lat = N)   checker: tx-family
post-synthesis: tx-family                  E transport: pending (Gate 4)   attacks: 6, all rejected at solution
```

## The circuit

Write a module with exactly this header. Port names, directions, widths and order matter, and so do the
parameter names and their order:

```systemverilog
module matmul #(parameter int N = 4, parameter int W = 8, parameter int AccW = 32) (
  input  logic                 clk, rst,
  input  logic                 start,
  input  logic [N*N*W-1:0]     A, B,
  output logic                 done,
  output logic [N*N*AccW-1:0]  C
);
```

The matrices are flat, row-major, least significant entry first: entry `(i, k)` of `A` is
`A[(i*N+k)*W +: W]`, and `B` is laid out the same way. Entry `(i, j)` of `C` is `C[(i*N+j)*AccW +: AccW]`.

The entries of `A` and `B` are two's complement. The products are sign-extended, and

    C[i][j] = (sum over k < N of A[i][k] * B[k][j])  mod 2^AccW,

computed exactly in the integers and then reduced, so `C` holds two's-complement `AccW`-bit entries and
every summation order is legal. Overflow wraps, as GPU accumulators do (ruled 11/03). Examples:
- `[[-1, 2], [3, 4]] · [[5, 6], [7, 0]] = [[9, -6], [43, 18]]`. At `W = 4`, `AccW = 8` that is
  `A = 16'h432F`, `B = 16'h0765`, `C = 32'h122BFA09`.
- `[[-8]] · [[-8]] = 64`: `8'h40` at `AccW = 8`, and `0` at `AccW = 6` (`W = 4`).

## The handshake

The clock is `clk`, rising edge. Below, "entry `c`" is the inputs of cycle `c`, and "snapshot `c`" is the
state after cycle `c`'s edge.
- **Reset.** `rst` is synchronous and active high, held for at least one cycle. Nothing is claimed while it
  is 1 or before the first reset, and the checker starts the design from a random state. Claims begin at
  the first entry after `rst` falls.
- **Start.** `start` is a one-cycle pulse. The environment raises it only when the design is idle: no
  transaction since the release, or the last one has shown `done` = 1. The earliest legal starts are the
  first entry after the release, and the entry right after the snapshot that first shows `done`
  (back-to-back).
- **Operands.** `A` and `B` are held from the start entry through the entry whose edge first shows `done`.
  Outside that window they are free: any known values, which the claim ignores.
- **Done.** `done` is known in every snapshot after the release. It first shows 1 within `lat` cycles of
  the start: at snapshot `s + d` with `d ≤ lat`, where `s` is the snapshot right after the edge that
  samples `start` (so a `done` already visible there has `d = 0`). Early completion and data-dependent
  latency are legal.
- **Hold.** From that snapshot until the next start, `done` = 1 and `C` = `A·B` for the transaction's
  operands. `C` matters only there; elsewhere it is free. If a design keeps `done` = 1 in the snapshot of a
  back-to-back start, that counts as the new transaction finishing at once, so `C` must already be the new
  product there.

The latency function `lat N W AccW ≥ 1` is the submission's own, defined in its Lean file. The number
scored is `n = lat 4 8 32`.

## The statement (`Spec.lean`, trusted)

```lean
def task : TxTask Params where
  inRange p := 1 ≤ p.1 ∧ 1 ≤ p.2.1 ∧ 1 ≤ p.2.2 ∧
    p.1 * p.1 * p.2.1 < 2 ^ 31 ∧ p.1 * p.1 * p.2.2 < 2 ^ 31
  clk := "clk"
  rst := "rst"
  start := "start"
  operands p := [("A", p.1 * p.1 * p.2.1), ("B", p.1 * p.1 * p.2.1)]
  done := "done"
  payload p := [("C", p.1 * p.1 * p.2.2)]
  result p := fun (a, b, ()) => (product p.1 p.2.1 p.2.2 a b, ())

abbrev Statement (sem : Nat → Nat → Nat → LeanModels.Sv.Design2) (lat : Nat → Nat → Nat → Nat) :
    Prop :=
  task.Statement (fun p => sem p.1 p.2.1 p.2.2) (fun p => lat p.1 p.2.1 p.2.2)
```

`product` is the sum above: an `Int` dot product of the sign-extended entries (`BitVec.toInt`), then
`BitVec.ofInt AccW`, packed row-major. For every point in range, the statement asks for:
- exactly these ports;
- every run terminates;
- the clock discipline (`ClockedBy`): `clk` an input, every flop clocked by it, nothing reading it as data;
- `lat ≥ 1`;
- in every run, from every reset release and up to any later cycle, if the environment kept the handshake
  above, the design kept its side.

`SvGolf/TaskSeq.lean` defines `TxTask`. `design/sequential/CONTRACT.md` is the decision log, C1 to C10,
with the formal reading of each item. `REVIEW.md` is the statement's review: what it says, why it cannot be
met vacuously, and the open points. The text is frozen as the git tag `txtask-v1`. A change is a version bump,
never an edit.

## Rules for this task

* **No banned operators** (C6, ruled 11/03). `*` is allowed: the score prices it.
* **Clocked source rules** (PLAN4.md Gate 2 step 2): exactly one clock and one edge
  (`always_ff @(posedge clk)`); synchronous reset only; no `initial`, no initializer on state, no
  `always_latch`, no `negedge`, no delays, waits, forks or other event controls; no blocking assignment in
  an `always_ff`. Each is refused at the source gate.
* **Parameter range** (C10): `N·N·W < 2^31` and `N·N·AccW < 2^31`, so every width and index expression stays
  in the 32-bit `int` range.
* **Probe points**: the extractor cross-checks the design at `(N, W, AccW)` = `(1, 1, 1)`, `(2, 3, 5)`,
  `(3, 4, 8)` and the scoring point `(4, 8, 32)`. Mind `N = 1`, and `W = 1`, where an entry is 0 or -1.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`allow_bv_decide: false`). No `native_decide`,
  no `sorry`. Proof time limit: 120 s, the one limit of every task.
* **Scoring at `(4, 8, 32)`** (C7, sky130 ruling of 11/03): area is sky130 A0' µm², flops (`dfxtp_1`)
  included. Time is `n` × the register-to-register period in ps from the pinned liberty, which already
  includes the flop's clock-to-Q and setup. Both are taken on the netlist REPAIRED by buffering only (a buffer
  tree on every net over its driver's limits, flop Q nets, inputs and output bits included; `sky130_a0_v2`,
  11/04), every input driven by the default `sky130_fd_sc_hd__buf_8` (`sky130_a0_v3`); a design the repair cannot
  make electrically legal is rejected at stage `ppa`. The reference: 87,173.6064 µm², period 10,696 ps, time
  42,784 ps, every load pin read per edge (`sky130_a0_v3`; 6 buffers on 5 nets: busy's flop Q 1 x `buf_4`,
  NOR(busy, start) and NOR(rst, .) 1 x `buf_8` each, one more control net 2 x `buf_4`, the input `start` 1 x
  `buf_12`; `tests/expected.json`). Before the per-edge loads it was 10,705 ps and 42,820 ps under v2's `buf_1` and
  v3's `buf_8` alike (5 buffers, the third control net 1 x `buf_8`, the same area); the unrepaired v1 netlist read
  48,079 ps from extrapolated tables, and duplicating one control flop was then a 4.4× time shortcut that loses
  under v2: 43,560 ps). The leaderboard keeps the Pareto frontier of (area, time). On a
  tie in both, the earlier record stands. NAND2 gate equivalents and unit depth are extra columns. One
  submission declares one latency: the same design with another `n` is a separate record. Every number can be reproduced bit for bit: score/PPA.md, "Reproduce a score"
  (`ppa.py --seq` for a clocked task).
* **Special cases are legal but do not pay.** A design may treat `N = 4` specially, but it must still be
  correct, and proved, for every `N`.
* **Post-synthesis check** (`task.json` `postsynth`) at `(2, 4, 8)` and `(4, 8, 32)`. For each of 3 seeds:
  a random initial state, one reset cycle, then `oracle.py`'s 24 transactions. The netlist must agree with
  ls-sv cycle by cycle, on `done` everywhere and on `C` wherever `done` = 1. Its `C` must also be `good`
  for the oracle, so a bug shared by the design and ls-sv is still caught. `done` must first rise within
  `n`. An x or z on `done` after the release, or on `C` while `done` = 1, rejects.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

A file `solution.sv` with the module above, and a Lean file `Solution.lean`. The Lean file defines the
latency function `Submission.lat : Nat → Nat → Nat → Nat`, declares `n` with a header line
`-- svgolf-latency: n`, and proves `Submission.Goal`. That goal is
`SvGolf.Tasks.Matmul.Statement design.sem Submission.lat ∧ Submission.lat 4 8 32 = n`, for the design the
checker extracts from `solution.sv`:

```bash
python3.12 check.py tasks/matmul solution.sv Solution.lean
```

The `tx-family` kind is Gate 2's checker work, in progress. The names above follow its current draft;
`svgolf/README.md` will have the final ones.

## The reference (`reference/matmul_g1.sv`)

`N²` multiply-accumulate units and one step counter `k`. `start` captures `A` and `B` into shift registers
and clears `C`. At step `k`, unit `(i, j)` adds `A[i][k]·B[k][j]`, both operands sign-extended to `AccW`
bits, and the register's width does the wrap. Each step shifts `A` by one entry and `B` by one row, so every
select is static. `done` rises after the `N`-th step and stays 1, with `C` held, until the next `start`.
There are only flip-flops, all written by nonblocking assignments.

**Timing**, MEASURED (iverilog, 11/03, at the five probe and post-synthesis points, 3 seeds × 24
transactions each): `done` first shows 1 exactly `N` snapshots after the start edge (`d = N`), holds with
`C` unchanged through every gap, and `C` is `good` on all 360 transactions. So the reference meets `lat = N`
by the contract's count. PLAN4.md's figure `N + 1` is also a valid bound, but it scores `n = 5` instead of
`4`. The proof declares `lat = N`.

**Proof**: `reference/matmul_g1.lean`, accepted by `check.py` (`n = 4`): the loaded family is the hand-built
one at every in-range point, one cycle is G0's clock step, the invariant on `k` gives the product after `N`
busy cycles, and `TxTask.satisfiedAt_of_phases` (`SvGolf/Seq.lean`) turns the phases into the statement.

## The oracle (`oracle.py`)

This is the task's own evaluator: Python integers only, independent of ls-sv, and not part of the trusted
statement. It provides:
- `good(params, txn, result)`: whether `result["C"]` is the product of the transaction's operands.
- `txns(params, seed)`: a deterministic list of 24 transactions. Each one carries the operands `A` and `B`
  (flat ints), a `gap` and the `free` operand values for those gap entries.
  - `gap` counts the idle entries before the start: from the release for the first transaction, otherwise
    from the entry after the previous `done`. 0 is the earliest legal start.
  - The first transaction is the zero matrix, at gap 0, 1 or `N + 3` (seed mod 3).
  - Then come seven corners in a seeded order: all-min², the largest dot product, which wraps; min·max, the
    most negative; max²; all -1; the identity on either side; a min/max checkerboard.
  - Then random transactions: a quarter of the entries are extremes. Half the gaps are 0 (back-to-back), and
    one in eight is `N + 3`, a hold longer than the reference's latency.
- `mismatch(params, txn, result)`: the first wrong entry, for reports.
- `oracle(params, inputs)`: the comb tasks' shape.

`python3 oracle.py` runs the self-test in 0.16 s, MEASURED. It checks:
- `Spec.lean`'s examples, and a second formulation of the product on all 600 generated transactions;
- that the lists are deterministic (and, measured separately, byte-identical under CPython 3.9, 3.12 and
  3.15);
- that the transactions reach both extremes, back-to-back starts after a nonzero result, gaps, and a long
  hold;
- that at both post-synthesis points, every seed has a transaction that tells apart each wrong arithmetic
  from the attack list below (unsigned product, missing sign extension, a 2W-bit accumulator, off-by-one
  `k`, `B·A`, `Cᵀ`) and an accumulator not cleared on start.

In simulation, MEASURED as above, reference variants with the accumulator cleared only by reset, `done` one
cycle early, or unsigned operands each fail `good` on 20 to 23 of the 24 transactions of every seed, at both
points.

## Attack designs (`tests/matmul/attacks/`, Gate 3 step 4, to come)

Each one looks correct but is wrong for some `N, W, AccW`, and each must fail at the `solution` stage:
off-by-one `k`, an unsigned product, a missing sign extension, `done` one cycle early, the accumulator not
cleared on start, `AccW` truncated to `2W`.

## Scores

To come with Gate 3 step 6: the reference at `(4, 8, 32)`, with `(2, 4, 8)` reported alongside.
