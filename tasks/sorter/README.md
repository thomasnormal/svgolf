# Task `sorter`: a streaming sorter of N unsigned W-bit values, clocked

Take `N` unsigned `W`-bit values, one per cycle, and give them back in ascending order, one per cycle,
duplicates kept. This is svGolf's STREAM task, one of its three clocked tasks (with the arbiter and
`matmul`): the values arrive over `N` cycles rather than all at once, and leave the same way. The proof covers every
`N, W ≥ 1` with `N·W < 2^31`, and it proves the cycle count too: the score is the area times that count
times the clock period. So the task is the schedule: how many cells or comparators, how many cycles, and how
short a cycle. The task's state (statement, checker, reference, ranking) is under "Status", after "Proving a
new design".

Labels: **MEASURED** = run (command or file named); **DERIVED** = a hand argument given here; **JUDGED** =
opinion.

| file | what |
|---|---|
| [`Spec.lean`](Spec.lean) | trusted text: the task (`task`, `sortAsc`, `Statement`) |
| [`../../SvGolf/TaskSeq.lean`](../../SvGolf/TaskSeq.lean) | trusted text: the kind `StreamTask`, the handshake, and the clocked statements' rules 1 to 3 and `StreamTask.StatementV2` (its Status lists every declaration the statement reaches, final since 2026-11-08, amended 2026-11-09) |
| [`task.json`](task.json) | `stream-family`, status `ready`, the probe points, the scoring point, the post-synthesis block |
| [`oracle.py`](oracle.py) | the post-synthesis transactions (`txns`) and the task's own evaluator (`good`) |
| [`reference/sorter_ins.sv`](reference/sorter_ins.sv) | the reference: an insertion-cell array, adapted from a real-world design (provenance in its header) |
| [`reference/sorter_ins.lean`](reference/sorter_ins.lean) | its proof, for every `N, W` in range (untrusted, checked like a submission) |
| [`../../SvGolf/SeqV2.lean`](../../SvGolf/SeqV2.lean), [`../../SvGolf/Seq.lean`](../../SvGolf/Seq.lean) | the svGolf proof library for transaction and stream tasks: the reduction `StreamTask.satisfiedAtV2_of_phases`, the phase model `StreamTask.PhaseModel`, `combDeps_of_ffOnly`, `TerminatesPU.of_invariant`, `powerUp_cons` |
| [`REVIEW.md`](REVIEW.md) | the statement's review: v2 first, the v1 history after it |
| [`../../tests/sorter/`](../../tests/sorter/) | `attacks/` (8), `tb.sv` + `sim.py` (a simulation of the reference and its hand mutants, Icarus) |

## Proving a new design

A new sorter is your own `solution.sv` (the header below; run-time `/ % **` are banned) and a `Solution.lean`
that proves it, with the latency it claims, for every `N, W ≥ 1` with `N·W < 2^31`. Any schedule is allowed:
an insertion array, a sorting network behind serial-parallel buffers, a merge structure. Find the design
without Lean, then check it once without a proof, at the latency you mean to claim:

```bash
python3.12 score/ppa.py solution.sv --task tasks/sorter --seq --path   # area and period, about a second
python3.12 check.py tasks/sorter solution.sv --unproved --latency 16 --stage-dir stage
```

The first command weighs the design through the clocked flow (`--seq`): the sky130 area, flip-flops included,
and the register-to-register period, with the critical path (`--path`); your time is the latency times that
period. The second runs every stage that needs no proof: the clocked source rules, the check that no construct
can create an `x` (`clocked_rules`), the never-loaded register check, the score, and the clocked post-synthesis
check, which drives the scored netlist through `oracle.py`'s transactions from random power-up states and holds
every emitted list to `sorted()` and to the latency. A wrong design is named there, with the transaction,
before any proof. Rule 1 (Moore outputs) has no early check in this kind: the proof is what refuses a
combinational path from an input to an output.

**The route: a phase model, `StreamTask.satisfiedAtV2_of_phases`** ([PROVING.md, section
19](../../PROVING.md#19-a-clocked-task-one-cycle-at-a-time-then-the-phases-matmul-sorter);
`reference/sorter_ins.lean` is a complete proof, 774 code lines). The reduction in `SvGolf/SeqV2.lean` turns
the statement at one point into facts about ONE clock cycle:

1. `Interface`: the ports in order and distinct declaration names (`rfl`, and `decide` on the names);
2. `Disciplined`: `ClockedBy clk none` (no asynchronous reset), a `simp` over the processes;
3. `TerminatesPU`, by `TerminatesPU.of_invariant` from the clock step;
4. the latency facts: `1 ≤ N`, `N ≤ lat`, and that the spec keeps the length (`sortAsc` does);
5. a `StreamTask.PhaseModel`: the clock step in closed form (its `CycleModel`: a `Shape` and the one-cycle
   `Step`), the phases `Ready` (after a reset, nothing to show) and `At ys j` (`j` cycles after a start, the
   inputs `ys` so far), the output schedule `out xs j`, and the one-cycle obligations `reset`, `hold`,
   `start`, `feed` and `run`;
6. the shape at every power-up state (`powerUp_cons` once per declaration);
7. rule 1, `MooreOutDep`: for a design whose every process is an `always_ff`, `MooreOutDep.of_noComb` with
   `combDeps_of_ffOnly`;
8. rule 3, `XSafe`: a `simp` over `xsafeB` and its helpers (`xsProc`, `xsStmt`, `xsWidth`, ...).

**Lay the design out so the proof stays short**:

* register every output: with only `always_ff` processes, rule 1 is one line (`combDeps_of_ffOnly`);
* keep every process an `always_ff` whose body writes with nonblocking assignments only: the library's clock
  step in closed form (`cycleStep2_ffOnly`; the reference uses it through `cycleStep2_profile`) is for such
  designs only. A continuous `assign` or an `always_comb` block anywhere, an output driven by one included
  (`assign out_valid = tok[0]`), means proving the combinational settle yourself, as the arbiter's proof does
  ([PROVING.md, section 20](../../PROVING.md#20-a-reactive-task-the-arbiter-reacttask));
* reset every register whose value matters: the claims hold from every power-up value, the first reset edge
  included (a design whose `out_valid` timing within the latency depends on an unreset register can still be
  correct: the post-synthesis check holds each power-up's run to the claims, not to another power-up's cycles);
* nest generate loops: the loader gives each generate loop a fixed budget of `(N + W + 2)² + 64` iterations at a
  point (the sum of the parameter values plus 2, squared, plus 64), and a nested loop gets the whole budget
  again. A loop over `N`, `W`, `N·W` or `N²` iterations always fits; one flat loop over `N·N·W` lanes or `N³`
  iterations exceeds the budget at points in the range (at `(100, 8)`: 80000 lanes against 12164), and there the
  loader gives up: the design reads as an empty one, so the statement is unprovable, however correct the circuit
  is. Write one loop per index and nest them;
* for `XSafe`, operands of one width and run-time indices whose every value is in range, as in the arbiter's
  advice.

**The skeleton** (`reference/sorter_ins.lean` is it, filled in for the insertion array):

```lean
-- svgolf-latency: 16
import Submission.Design
import SvGolf.SeqV2

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W : Nat) : Nat := 2 * N   -- yours: your design's latency

-- 1. agreement: `design.sem N W = myD N W`, a hand-built Design2
-- 2. one cycle in closed form; 3. the invariant; 4. the phase model `model N W`

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W⟩ := p
  obtain ⟨hN, hW, -⟩ := hp
  exact Tasks.Sorter.task.satisfiedAtV2_of_phases (my_interface N W hN hW) (my_disciplined N W hN hW)
    (my_terminatesPU N W hN hW) hN (show N ≤ 2 * N by omega) (fun xs h => (my_len_sort xs).trans h)
    (model N W hN hW) (my_powerUp N W hN hW) (my_moore N W hN hW) (my_xsafe N W hN hW)

end Submission
```

`#print axioms solution` must show `propext`, `Classical.choice` and `Quot.sound` only.

**Library lemmas that exist today**:

* `SvGolf.SeqV2`: `StreamTask.satisfiedAtV2_of_phases` (the reduction), `MooreOutDep.of_noComb`,
  `combDeps_of_ffOnly`, `MooreOutDep.of_check` (rule 1 by evaluation, for a design with combinational logic),
  `TerminatesPU.of_invariant`, `powerUp_cons`, `powerUp_nil`;
* `SvGolf.Seq`: `StreamTask.PhaseModel` and the v1 reduction it feeds (`StreamTask.guar_of_phases`);
* `LeanModels.Sv.SeqProfile`, `LeanModels.Sv.SeqFamily`, `LeanModels.Sv.NbaCommit`: G0's clock step for a
  flip-flop-only design, the packed-family commit lemmas (`bvInsertAt_packBV`, `foldl_range_ofBitVec_packBV`,
  `LVec.foldl_range_insertAt_last`) and `nbaFold`.

## Status (2026-11-09)

```
trusted statement: final, decided 2026-11-08, amended 2026-11-09 before any record was published
  (the second clocked statement: StreamTask.StatementV2 of SvGolf/TaskSeq.lean, stated by Spec.lean)
run2 proof: complete, from every power-up state (lat = 2N)
checker: stream-family (check.py)   post-synthesis: stream-family (8 seeds at (3, 4) and at (8, 8))
reference: reference/sorter_ins.sv + sorter_ins.lean (adapted from andrewpeck/cell-sort, MIT), check.py
  ACCEPTS it (--postsynth full)
attacks: 8, each rejected at solution with the reference proof; 7 wrong at post-synthesis, and
  rst_gate refused by rule 1 (no output reads rst combinationally, decided 2026-11-09)
ranking: ranked (decided 2026-11-08); par is the reference's record
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
  is 1 or before the first reset, and the claims hold from every power-up state of the design. Claims begin
  at the first entry after `rst` falls. A reset aborts: the claims stop at the entry that asserts it. The
  snapshot just before that entry is still claimed, and since no output may read an input combinationally,
  `rst` included (rule 1; decided 2026-11-09), it is on the wire for the whole reset cycle too: a design that
  gates an output with the reset (`assign out_valid = q & ~rst`) is refused.
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
  task.StatementV2 (fun p => sem p.1 p.2) (fun p => lat p.1 p.2)
```

`sortAsc` is insertion sort, ascending, unsigned (`List.insertionSort (· ≤ ·)` written out, because the
trusted text imports no Mathlib). `StreamTask.StatementV2` is the second clocked statement. For every point in range it asks for
(`StreamTask.SatisfiedAtV2`):

- **the interface**: exactly these ports, in this order, and no two declarations of one name;
- **the clock discipline** (`ClockedBy clk none`): `clk` an input, every edge process clocked by it, no
  asynchronous reset (decided 2026-11-09; the source gate refuses one too), nothing reading `clk` as data;
- **termination from every power-up** (`TerminatesPU`): from every power-up state, under every schedule, on
  every known stimulus, every run completes;
- `lat ≥ 1`;
- **the claims from every power-up** (rule 2, `FollowsPU`): from every power-up state (every declared signal,
  2-state ones included, at some 0/1 value of its width), under every schedule, on every known stimulus, in
  every completed run, from every reset release and up to any later cycle: if the environment kept the
  handshake above, the design kept its side;
- **Moore outputs** (rule 1, `MooreOutDep` with nothing exempt): no combinational path, control dependencies
  included, from `rst`, `start`, `in_valid` or `in_data` to `out_valid` or `out_data`, so what a snapshot shows
  is on the wire for the whole next period;
- **no construct that can create an `x` from known operands** (rule 3, `XSafe`): with concrete power-up
  states and known inputs, every value a run computes is then known, and no simulator resolution of an
  unknown is ever taken.

`SvGolf/TaskSeq.lean` defines `StreamTask` and the rules; `design/sequential/CONTRACT.md` is the decision log
(C8, and interpretation points 6 and 7); `design/soundness/TXTASK-V2-REVIEW.md` is the review of v2;
`REVIEW.md` is this task's review. The first statement's text was frozen on 2026-11-03; v2 (2026-11-05)
replaced its run from ls-sv's `x` start by every power-up and added rules 1 and 3, and it is final since
2026-11-08. Its two amendments of 2026-11-09 for this kind (rule 1 with nothing exempt, no asynchronous reset;
`REVIEW.md`) were made in place before any record of the task was published. A later statement change is a version
bump that re-issues the records, never an edit.

The refusal register ([`REFUSALS.md`](../../REFUSALS.md), rendered from the register at the pinned revision) still
names the superseded `StreamTask.Statement` (the first statement) in its row for this task's guarantee and says that each
sorter attack is wrong at post-synthesis. The ranked statement is `StreamTask.StatementV2`, and `rst_gate` passes
the post-synthesis check (rule 1 refuses it); the register's newer text comes with the next pin.

## Rules for this task

* **No task-specific banned operators.** Comparisons are the task. Run-time `/ % **` are banned, as in every
  task (since 2026-11-06; the svGolf README, "Rules").
* **The latency line.** `Solution.lean` declares its latency in exactly one header line
  `-- svgolf-latency: n` (a decimal number of cycles, 1 to 999999999) and defines
  `Submission.lat : Nat → Nat → Nat`; the goal pins `Submission.lat 8 8 = n`, and the score uses `n`. `lat`
  is your function: at every other point it need only be a bound your proof establishes. At each point of the post-synthesis check the checker has the kernel evaluate `Submission.lat` there (it
  must reduce to a number, 1 to 999999999) and runs that point against it (decided 2026-11-08); without a
  proof, `check.py --unproved` takes `--latency-at POINT:n` for those points (else the scoring point's `n`).
* **One clock, synchronous reset, no asynchronous process**: one clock and one edge
  (`always_ff @(posedge clk)`); the reset synchronous, `rst` read inside the clocked body; no asynchronous
  reset, no `iff`, no `negedge`; no `initial`, no initializer on state, no `always_latch`; no delays, waits,
  forks or other event controls; no blocking assignment in an `always_ff` but the header of a procedural `for`
  loop over an iterator it declares. Each is refused at the source gate; the statement itself refuses an
  asynchronous reset too (`ClockedBy clk none`, decided 2026-11-09).
* **Moore outputs** (rule 1): register every output; no input, `rst` included, may reach an output
  combinationally (decided 2026-11-09).
* **Every power-up** (rule 2): the claims hold from every 0/1 power-up value of every register and variable,
  the first reset edge included, so a register that is never reset may only hold a value that does not matter.
  A register that is never loaded (`u <= u`), which the pinned flow removes while reads of it remain, is
  refused at the `score` stage.
* **No x-creating construct** (rule 3, `XSafe`): the `clocked_rules` stage refuses such a construct before
  the proof (`check/clocked_rules.py`); the statement's conjunct is the authority.
* **Parameter range** (C10): `N·W < 2^31`. The design's own `int` expressions are checked to agree with a
  32-bit elaboration (`PDesign.int32Agrees`) at the probe and scoring points; between them the proof is about
  ls-sv's unbounded integers, so keep the design's constant expressions within the range (the reference's
  largest is `N*W - 1`).
* **Probe points**: `(N, W)` = `(1, 1)`, `(1, 8)`, `(2, 1)`, `(2, 4)`, `(3, 1)`, `(3, 4)`, `(4, 8)` and the
  scoring point `(8, 8)`. Mind `N = 1`, where the one value comes straight back, and `W = 1`.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`allow_bv_decide: false`). No `sorry`. Proof time
  limit: 300 CPU s, the one limit of every task (the reference: 17.0 to 17.4 CPU s, three cold runs,
  2026-11-07, `score/time_limits.json`).
* **Scoring at `(8, 8)`** (C7): area is sky130 A0' µm², flops included; time is `n` × the
  register-to-register period, both on the netlist repaired by buffering only (`sky130_a0_v2`: buffer trees on
  every net over its driver's limits, nothing resized; a netlist the repair cannot make legal is rejected),
  every input driven by the default `sky130_fd_sc_hd__buf_8` (`sky130_a0_v3`). The ranked number is area ×
  time, `area × (n × period)` in µm²·ns (decided 2026-11-05), and the task is ranked by it (decided 2026-11-08);
  the Pareto frontier of (area, time), NAND2 gate equivalents and unit depth are exploration columns. One
  submission declares one latency: the same design with another `n` is a separate record. Every number can be
  reproduced bit for bit: score/PPA.md, "Reproduce a score" (`ppa.py --seq` for a clocked task). Eight
  byte-wide values: small enough that post-synthesis and ls-sv traces are cheap, large enough that an `O(N)`
  cell array, a sorting network behind serial-parallel buffers, and the latency/area trade between them all
  show.
* **Post-synthesis check** (`task.json` `postsynth`) at `(3, 4)` and `(8, 8)`, 8 seeds each (F5, decided
  2026-11-07; every random draw from `$SVGOLF_POSTSYNTH_SALT`): per seed a random power-up state, one reset
  cycle, then `oracle.py`'s 24 transactions with idleness observed. Where the netlist and ls-sv start from the
  same state (seed 0, from all zeros) the netlist must agree with ls-sv on `out_valid` everywhere and on
  `out_data` where valid; from different power-up states ls-sv's own run must meet the statement's claims (L5
  of the task's `REVIEW.md`, fixed 2026-11-08). `out_valid` must be 0 before the first start, every emitted value must come within the
  point's latency of its start, and each transaction's emitted values must be `good`.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the
  block; the record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

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
nonblocking assignments, every one reset but `out_data` (read only where `out_valid` = 1); three process shapes (cells `0 .. N-2` as a generate family, the top
cell, the output register).

**Invariant** (the header has it in full): reading the cells bottom-up, after `t` inputs of a transaction
they hold `[0]^(N-t) ++ sortAsc [x_{t-1}, .., x_0]`, and each insert is `tail ∘ insertAsc x` (ties land
where `insertAsc` puts them). After the `j`-th drain step they hold `S[j..N) ++ [0]^j` and `out_data` shows
`S[j-1]`, `S` the sorted values. After the last output the state is the reset state again, so back-to-back
starts need nothing.

**Timing**, MEASURED (2026-11-04, Icarus 12, `tests/sorter/sim.py`, all eight probe points × 3 seeds × 24
transactions, plus a transaction aborted by a mid-stream reset): `out_valid` = 1 exactly at snapshots
`s+N+1 .. s+2N`, consecutive, for every transaction, so `lat = 2N`, attained by every transaction: tight for
this design, one cycle above the task's bound `2N - 1` (the output is registered). `out_valid` is never x or z
after the release (Icarus starts every register at x) and is 0 before the first start.

**Upstream candidates** (searched 2026-11-03; the original was run unchanged through the source gate and the
extractor first): `andrewpeck/cell-sort` (MIT; chosen), `Poofjunior/fpga_fast_serial_sort` (the 2015 cell
sort with a streaming drain, but no license: not usable), `realise-lab/hwpq` `register_array`/
`systolic_array` (BSD-3, priority queues with 0 as the empty marker), `Weiyet/RTLStructLib` `List/sorter.sv`
(MIT, an FSM insertion sort over a parallel input, `O(N²)` cycles), `doelab/sort-verilog` (MIT, fixed-size
generated sorting networks). What the pipeline refused in the unchanged originals: unpacked arrays (ports,
nets, variables and element-select targets: the dominant real-world idiom, in every candidate), the
unconditional `generate begin : name … end` block wrapping a loop, module instances in genvar-dependent
generate-if branches, `for` loops in `always_ff` (the loop index was then a blocking assignment to the gate),
asynchronous resets, `priority case`, `` `resetall ``, and upstream's own defects (a corrupted first line in
`unit_cell.sv`, a net assigned in `always_ff`).

**Proof**: `reference/sorter_ins.lean` (983 lines), accepted by `check.py` (`n = 16`; `lat = 2N` at every
`N, W` in range). The loaded family is the hand-built one (`so_sem_eq`; the cell family is empty at `N = 1`);
one cycle is G0's clock step over the FF-only profile, committed register by register, the reset's write last
(`so_cycle`, `next_reset`); a load is `tail ∘ insertAsc x` on the ascending cells (`hw_ins`) and insertions
commute (`sort_snoc`), so the invariant (`at_step`) gives the cells, the token delay line and the output
`j` cycles after a start; the phase model (`model`: `Ready`, the all-zero state, and `At ys j`) holds from
every state of the register shape, every power-up state has that shape (`so_powerUp`), rule 1 is
`combDeps_of_ffOnly` (`so_moore`), rule 3 a `simp` over `xsafeB` (`so_xsafe`), and
`StreamTask.satisfiedAtV2_of_phases` (`SvGolf/SeqV2.lean`) turns them into the statement. PROVING.md section
19 walks through it.

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

An eighth design, `rst_gate` (point L1 of the readiness review of 2026-11-08, [`REVIEW.md`](REVIEW.md)), registers
the outputs and gates `out_valid` with the reset (`assign out_valid = ov_q & ~rst`). Every snapshot it shows is the
reference's, so the post-synthesis check passes it; on the wire, the snapshot before a reset entry is hidden during
the reset cycle. Since 2026-11-09 rule 1 exempts nothing, and `tests/sorter/negative/Refute.lean` refutes it for
every latency (`rst_gate_refuted`); with the reference's proof it fails first in `so_decls` (its extra registers).

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
after the per-edge loads, `tests/run.py --update-scores`; the same numbers at 2026-11-08, `tests/run.py
--only sorter`) at the scoring point `(8, 8)`: area **5512.7872 µm²** (sky130 A0′, 713 cells including 81
`dfxtp_1` flops: 64 cell bits, 8 tokens, the 9-bit output register), time **16 × 2523 ps = 40,368 ps** (`n =
16`; the register-to-register period over an 11-cell critical path, every load pin read per edge; 2510 ps
before the per-edge loads, as under `sky130_a0_v1`; under `sky130_a0_v2`, whose `buf_1` input drive made an
input path the critical one, 2621 ps). The ranked number, area × time: **222,540.19 µm²·ns** (DERIVED from the
two). Extra columns: 1288.819 GE, unit depth 15. With `score.py --seq` at `(3, 4)`: 239.3 GE, 20 flops, depth
10, `n = 6`.
