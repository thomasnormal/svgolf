# Task `sorter`: a streaming sorter of N unsigned W-bit values, clocked

**Preview, not ranked yet.** The statement is being revised to cover the outputs on the wire and unknown
values at reset; submissions are not ranked until then.

Take `N` unsigned `W`-bit values, one per cycle, and give them back in ascending order, one per cycle,
duplicates kept. This is svGolf's second clocked task, after `matmul`, and its first STREAM task: the
values arrive over `N` cycles rather than all at once, and leave the same way. The proof covers every
`N, W ≥ 1`, and it proves the cycle count too: the score is that count times the clock period, beside the
area. So the task is the schedule: how many cells or comparators, how many cycles, and how short a cycle.

Status (PLAN4.md, section 1):

```
trusted statement: complete (txtask-v1)   run2 proof: complete (lat = 2N)   checker: stream-family
post-synthesis: stream-family              E transport: pending (Gate 4)   attacks: 7, all rejected at solution
```

## The circuit

Write a module with exactly this header. Port names, directions, widths and order matter, and so do the
parameter names and their order:

```systemverilog
module sorter #(parameter int N = 8, parameter int W = 8) (
  input  logic         clk, rst,
  input  logic         start, in_valid,
  input  logic [W-1:0] in_data,
  output logic         out_valid,
  output logic [W-1:0] out_data
);
```

The values are unsigned. The output is the input sorted ascending, with every duplicate kept: `3, 15, 0, 3, 8`
comes out as `0, 3, 3, 8, 15` (`W = 4`). Equal values are interchangeable, so the order among them is not
observable.

## The handshake

The clock is `clk`, rising edge. Below, "entry `c`" is the inputs of cycle `c`, and "snapshot `c`" is the
state after cycle `c`'s edge.
- **Reset.** `rst` is synchronous and active high, held for at least one cycle. Nothing is claimed while it
  is 1 or before the first reset, and the checker starts the design from a random state. Claims begin at
  the first entry after `rst` falls.
- **Start.** `start` is a one-cycle pulse. The environment raises it only when the design is idle: no
  transaction since the release, or the previous one's `N` outputs have all been shown. The earliest legal
  starts are the first entry after the release, and the entry right after the snapshot that shows the
  previous transaction's `N`-th output (back-to-back).
- **Input.** After a start at entry `s`, `in_valid` = 1 at exactly the entries `s+1 .. s+N`, with the values
  on `in_data`, and 0 at every other entry: no gaps, no backpressure. `in_data` is known at every entry, but
  outside those `N` entries it is free, and the claim ignores it.
- **Output.** `out_valid` is known at every snapshot after the release, and 0 until the first start. From
  each start to the next, `out_valid` = 1 at exactly `N` snapshots, not necessarily consecutive, all at
  most `lat` cycles after the start: at snapshot `s + d` with `d ≤ lat`. On those snapshots, in order,
  `out_data` shows the sorted values. `out_data` matters only there.

The latency function `lat N W ≥ 1` is the submission's own, defined in its Lean file. The number scored is
`n = lat 8 8`. No design can do better than `lat = 2N - 1`: the smallest value depends on the last input,
sampled at entry `s+N`, so the first output is at snapshot `s+N` at the earliest, and the `N`-th at `s+2N-1`.

## The statement (`Spec.lean`, trusted)

```lean
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

abbrev Statement (sem : Nat → Nat → LeanModels.Sv.Design2) (lat : Nat → Nat → Nat) : Prop :=
  task.Statement (fun p => sem p.1 p.2) (fun p => lat p.1 p.2)
```

`sortAsc` is insertion sort, ascending, unsigned (`List.insertionSort (· ≤ ·)` written out, because the
trusted text imports no Mathlib). For every point in range, the statement asks for: exactly these ports;
every run terminates; the clock discipline (`ClockedBy`); `lat ≥ 1`; and, in every run, from every reset
release and up to any later cycle, if the environment kept the handshake above, the design kept its side.
`SvGolf/TaskSeq.lean` defines `StreamTask`; `design/sequential/CONTRACT.md` is the decision log (C8, and
interpretation points 6 and 7); `REVIEW.md` is the statement's review. The text is frozen as the git tag
`txtask-v1`. A change is a version bump, never an edit.

## Rules for this task

* **No task-specific banned operators.** Comparisons are the task. Run-time `/ % **` are banned, as in every
  task (since 2026-11-06; the svGolf README, "Rules").
* **Clocked source rules**: one clock and one edge (`always_ff @(posedge clk)`); synchronous reset only; no
  `initial`, no initializer on state, no `always_latch`, no `negedge`, no delays or other event controls;
  no blocking assignment in an `always_ff` (a `for` loop index inside one is a blocking assignment too).
* **Parameter range** (C10): `N·W < 2^31`.
* **Probe points**: `(N, W)` = `(1, 1)`, `(1, 8)`, `(2, 1)`, `(2, 4)`, `(3, 1)`, `(3, 4)`, `(4, 8)` and the
  scoring point `(8, 8)`. Mind `N = 1`, where the one value comes straight back, and `W = 1`.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`allow_bv_decide: false`). No `sorry`.
* **Scoring at `(8, 8)`** (C7): area is sky130 A0' µm², flops included; time is `n` × the
  register-to-register period, both on the netlist repaired by buffering only (`sky130_a0_v2`: buffer trees on every
  net over its driver's limits, nothing resized; a netlist the repair cannot make legal is rejected), every input driven
  by the default `sky130_fd_sc_hd__buf_8` (`sky130_a0_v3`). The task is an unranked preview; svGolf's one
  ranked number is area x time (decided 11/05), and the Pareto frontier of (area, time), NAND2 gate equivalents and
  unit depth are exploration columns. Every number can be reproduced bit for bit: score/PPA.md, "Reproduce a score" (`ppa.py --seq` for a clocked task). Eight byte-wide
  values: small enough that post-synthesis and ls-sv traces are cheap, large enough that an `O(N)` cell
  array, a sorting network behind serial-parallel buffers, and the latency/area trade between them all show.
* **Post-synthesis check** (`task.json` `postsynth`, the proposal for the stream kind) at `(3, 4)` and
  `(8, 8)`: per seed a random start state, one reset cycle, then `oracle.py`'s transactions with idleness
  observed; the netlist must agree with ls-sv on `out_valid` everywhere and `out_data` where valid, and each
  transaction's emitted values must be `good`.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the block; the
  record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

A file `solution.sv` with the module above, and a Lean file `Solution.lean` that defines
`Submission.lat : Nat → Nat → Nat`, declares `n` with a header line `-- svgolf-latency: n`, and proves
`Submission.Goal`, that is `SvGolf.Tasks.Sorter.Statement design.sem Submission.lat ∧ Submission.lat 8 8 = n`
for the design the checker extracts from `solution.sv` (`check.py`'s kind `stream-family`):

```bash
python3.12 check.py tasks/sorter solution.sv Solution.lean
```

Without a proof, `check.py --unproved --latency n tasks/sorter solution.sv` runs every other stage, the
clocked post-synthesis check included, against the latency you mean to claim.

## The reference (`reference/sorter_ins.sv`)

The insertion-cell array ("cell sort"), ADAPTED from a real-world design: `andrewpeck/cell-sort`
(https://github.com/andrewpeck/cell-sort, commit `cfc46709`, MIT, © 2024-2025 Andrew Peck). The file header
keeps the license notice and lists every change with its reason. `N` cells, cell `N-1` on top. On an input
`x`, each cell takes its upper neighbour's value when `x` beats that value, else `x` when `x` beats its own,
else holds (upstream's rule, kept); the top cell is never pushed into. When `in_valid` = 0 every cell takes
its upper neighbour's value and the top takes 0, so the minimum leaves through cell 0, one per cycle (new:
upstream outputs all cells in parallel). A one-bit token per cell, shifted down every cycle with `in_valid`
entering at the top, makes `out_valid` = `in_valid` delayed by `N` (new). `start` is not read: under the
rely, `in_valid` = 1 exactly at the `N` entries after each start. Only flip-flops, all written by
nonblocking assignments; three process shapes (cells `0 .. N-2` as a generate family, the top cell, the
output register).

**Invariant** (the header has it in full): reading the cells bottom-up, after `t` inputs of a transaction
they hold `[0]^(N-t) ++ sortAsc [x_{t-1}, .., x_0]`, and each insert is `tail ∘ insertAsc x` (ties land
where `insertAsc` puts them). After the `j`-th drain step they hold `S[j..N) ++ [0]^j` and `out_data` shows
`S[j-1]`, `S` the sorted values. After the last output the state is the reset state again, so back-to-back
starts need nothing.

**Timing**, MEASURED (Icarus 12, `tests/sorter/sim.py`, all eight probe points × 3 seeds × 24 transactions,
plus a transaction aborted by a mid-stream reset): `out_valid` = 1 exactly at snapshots `s+N+1 .. s+2N`,
consecutive, for every transaction, so `lat = 2N`, attained by every transaction: tight for this design, one
cycle above the task's bound `2N - 1` (the output is registered). `out_valid` is never x or z after the
release (Icarus starts every register at x) and is 0 before the first start.

**Upstream candidates** (searched 11/03; the original was run unchanged through the source gate and the
extractor first): `andrewpeck/cell-sort` (MIT; chosen), `Poofjunior/fpga_fast_serial_sort` (the 2015 cell
sort with a streaming drain, but no license: not usable), `realise-lab/hwpq` `register_array`/
`systolic_array` (BSD-3, priority queues with 0 as the empty marker), `Weiyet/RTLStructLib` `List/sorter.sv`
(MIT, an FSM insertion sort over a parallel input, `O(N²)` cycles), `doelab/sort-verilog` (MIT, fixed-size
generated sorting networks). What the pipeline refused in the unchanged originals: unpacked arrays (ports,
nets, variables and element-select targets: the dominant real-world idiom, in every candidate), the
unconditional `generate begin : name … end` block wrapping a loop, module instances in genvar-dependent
generate-if branches, `for` loops in `always_ff` (the loop index is a blocking assignment to the gate),
asynchronous resets, `priority case`, `` `resetall ``, and upstream's own defects (a corrupted first line in
`unit_cell.sv`, a net assigned in `always_ff`).

**Proof**: `reference/sorter_ins.lean`, accepted by `check.py` (`n = 16`; `lat = 2N` at every `N, W ≥ 1`).
The loaded family is the hand-built one (`so_sem_eq`; the cell family is empty at `N = 1`); one cycle is
G0's clock step over the FF-only profile, committed register by register, the reset's write last
(`so_cycle`, `next_reset`); a load is `tail ∘ insertAsc x` on the ascending cells (`hw_ins`) and insertions
commute (`sort_snoc`), so the invariant (`at_step`) gives the cells, the token delay line and the output
`j` cycles after a start; `StreamTask.satisfiedAt_of_phases` (`SvGolf/Seq.lean`) turns the two phases
(`Ready`, the all-zero state, and `At ys j`) into the statement. PROVING.md section 19 walks through it.

## The oracle (`oracle.py`)

The task's own evaluator: Python integers and `sorted()`, independent of ls-sv, and not part of the trusted
statement. `good(params, txn, result)` is `result["out"] == sorted(txn["xs"])`; `sort_asc` transcribes
`Spec.lean`'s `sortAsc` and the self-test checks the two agree. `txns(params, seed)` gives 24 transactions,
each with the values `xs`, a `gap` (idle entries before the start, from the release or from the entry after
the previous transaction's last output; 0 is back-to-back) and `free` values for `in_data` on the entries
with `in_valid` = 0. Ten corners come first (all 0, all `2^W - 1`, all equal, ascending, descending,
alternating extremes, one max among zeros, one zero among maxes, a duplicate pair, two repeated values),
then random values, a quarter of them extremes. `python3 oracle.py` runs the self-test (MEASURED 0.07 s,
960 transactions over the probe points × 5 seeds): the Spec example, `sorted` = `sortAsc`, determinism,
coverage, and that `good` rejects a dropped duplicate, a reversed order, a short or long stream.

## Attack designs (`tests/sorter/attacks/`, MEASURED)

Seven designs, each the reference with one change, correct-looking and wrong for some `N, W`; each is
rejected at the `solution` stage with the reference's proof, and each is also rejected by the clocked
post-synthesis check alone (`check.py --unproved --latency 16`), so none is merely different
(`tests/expected.json` has the messages and the first failing transaction of each):

| attack | the change | wrong for | where the proof fails |
|---|---|---|---|
| `token_self` | the token shift reads the cell's own token (`tok[k] <= tok[k]`): no value is ever emitted | `N ≥ 2` | `cell_inst` |
| `missing_else` | the cell's second test lost its `else`: both writes fire, the input wins | `N ≥ 2` | `cell_inst` |
| `push_own_value` | the neighbour push compares the cell's own value | `N ≥ 2` | `cell_inst` |
| `early_valid` | the token enters with the start: `out_valid` one cycle early, one value too many | every `N` | `so_static` |
| `reset_keeps_cells` | the reset leaves cells `0 .. N-2`: the first transaction mixes in their old values | `N ≥ 2` | `cell_inst` |
| `top_not_drained` | the drain does not clear the top cell: a stale maximum in the next transaction | every `N` | `so_static` |
| `signed_order` | signed comparisons: values with the top bit set are lost | every `N, W` | `so_static`, `cell_inst` |

They come from the mutants of `tests/sorter/sim.py` (Icarus, every probe point), with two replaced: the
loop bound `k < N-2` leaves cell `N-2` and its token undriven, which `check.py` refuses at the `fourstate`
stage before any proof (Yosys `check`: used but no driver), and `out_valid <= tok[N > 1 ? 1 : 0]` gives a
netlist with a `1'hx` constant, which the post-synthesis check refuses on every vector (measured when the
`stream-family` checker landed, 9584c55f). Two mutants are
EQUIVALENT and pass the simulation, as they must: `>=` for `>` everywhere, and `>=` in the neighbour push
only. Equal values are interchangeable, so no tie rule is observable, and they are not attacks: the
statement holds for them.

## Scores

MEASURED by `check.py` (the clocked score, `tests/expected.json`; 2026-11-04, three cold runs; the period again
after the per-edge loads, `tests/run.py --update-scores`) at the scoring point `(8, 8)`: area **5512.79 µm²**
(sky130 A0′, 713 cells including 81 `dfxtp_1` flops: 64 cell bits, 8 tokens, the 9-bit output register), time
**16 × 2523 ps = 40,368 ps** (`n = 16`; the register-to-register period over an 11-cell critical path, every load
pin read per edge; 2510 ps before the per-edge loads, as under `sky130_a0_v1`; under `sky130_a0_v2`, whose `buf_1` input
drive made an input path the critical one, 2621 ps). Extra columns: 1288.8 GE, unit depth 15. With `score.py --seq` at
`(3, 4)`: 239.3 GE, 20 flops, depth 10, `n = 6`.
