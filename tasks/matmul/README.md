# Task `matmul`: N×N signed matrix multiplication, clocked

Multiply two `N × N` matrices of signed `W`-bit entries, with every sum wrapping at `AccW` bits. This is
svGolf's TRANSACTION task, one of its three clocked tasks (with the arbiter and the sorter). The design has a
clock, a reset and a handshake: it reads `A` and `B` when `start` is pulsed, and after each start raises
`done` once `C` holds the product. The proof covers every `N, W, AccW ≥ 1` with
`N·N·W < 2^31` and `N·N·AccW < 2^31`, and it also proves the cycle count: the score is the area times that
count times the clock period. So the task is the schedule: how many multipliers, how many cycles, and how
short a cycle.

Status (2026-11-09):

```
trusted statement: final, decided 2026-11-08, amended 2026-11-09 before any record was published
  (txtask-v2: TxTask.StatementV2 of SvGolf/TaskSeq.lean, stated by Spec.lean)
run2 proof: complete, from every power-up state (lat = N)
checker: tx-family (check.py)   post-synthesis: tx-family (8 seeds at (2, 4, 8) and at (4, 8, 32))
reference: reference/matmul_g1.sv + matmul_g1.lean (own code), check.py ACCEPTS it (--postsynth full)
attacks: 7; 6 rejected at solution with the reference proof and wrong at post-synthesis, and
  async_reset refused at source (no asynchronous reset, decided 2026-11-09)
ranking: ranked (decided 2026-11-08); par is the reference's record
```

Labels: **MEASURED** = run (command or file named); **DERIVED** = a hand argument given here; **JUDGED** =
opinion.

| file | what |
|---|---|
| [`Spec.lean`](Spec.lean) | trusted text: the task (`task`, `product`, `Statement`) |
| [`../../SvGolf/TaskSeq.lean`](../../SvGolf/TaskSeq.lean) | trusted text: the kind `TxTask`, the handshake, and txtask-v2's rules 1 to 3 and `TxTask.StatementV2` (its Status lists every declaration the statement reaches, final since 2026-11-08, amended 2026-11-09) |
| [`task.json`](task.json) | `tx-family`, status `ready`, the probe points, the scoring point, the post-synthesis block |
| [`oracle.py`](oracle.py) | the post-synthesis transactions (`txns`) and the task's own evaluator (`good`) |
| [`reference/matmul_g1.sv`](reference/matmul_g1.sv) | the reference: `N²` multiply-accumulate units and one step counter (own code) |
| [`reference/matmul_g1.lean`](reference/matmul_g1.lean) | its proof, for every `(N, W, AccW)` in range (untrusted, checked like a submission) |
| [`../../SvGolf/SeqV2.lean`](../../SvGolf/SeqV2.lean), [`../../SvGolf/Seq.lean`](../../SvGolf/Seq.lean) | the svGolf proof library for transaction and stream tasks: the reduction `TxTask.satisfiedAtV2_of_phases`, the phase model `TxTask.PhaseModel`, `combDeps_of_ffOnly`, `TerminatesPU.of_invariant`, `powerUp_cons` |
| [`REVIEW.md`](REVIEW.md) | the statement's review: v2 first, the v1 history after it |
| [`../../tests/matmul/attacks/`](../../tests/matmul/attacks/) | seven attack designs |

## Start a new design

A new matrix multiplier is your own `solution.sv` (the header below; run-time `/ % **` are banned, `*` is allowed) and
a `Solution.lean` that proves it, with the latency it claims, for every `(N, W, AccW)` in range. Any schedule
is allowed: `N²` parallel multiply-accumulate units, fewer units over more cycles, a systolic array. Find the
design without Lean, then check it once without a proof, at the latency you mean to claim:

```bash
python3.12 score/ppa.py solution.sv --task tasks/matmul --seq --path   # area and period
python3.12 check.py tasks/matmul solution.sv --unproved --latency 4 --stage-dir stage
```

The first command weighs the design through the clocked flow (`--seq`): the sky130 area, flip-flops included,
and the register-to-register period, with the critical path (`--path`); your time is the latency times that
period. The second runs every stage that needs no proof: the clocked source rules, the check that no construct
can create an `x` (`clocked_rules`), the never-loaded register check, the score, and the clocked post-synthesis
check, which drives the scored netlist through `oracle.py`'s transactions from random power-up states and holds
every `C` to the oracle's product and every `done` to the latency. A wrong design is named there, with the
transaction, before any proof. Rule 1 (Moore outputs) has no early check in this kind: the proof is what
refuses a combinational path from an input to an output.

**The route: a phase model, `TxTask.satisfiedAtV2_of_phases`** ([PROVING.md, section
19](../../PROVING.md#19-a-clocked-task-one-cycle-at-a-time-then-the-phases-matmul-sorter);
`reference/matmul_g1.lean` is a complete proof). The reduction in `SvGolf/SeqV2.lean` turns the statement at
one point into facts about ONE clock cycle:

1. `Interface`: the ports in order and distinct declaration names (`rfl`, and `decide` on the names);
2. `Disciplined`: `ClockedBy clk none` (no asynchronous reset), a `simp` over the processes;
3. `TerminatesPU`, by `TerminatesPU.of_invariant` from the clock step;
4. `1 ≤ lat`;
5. a `TxTask.PhaseModel`: the clock step in closed form (its `CycleModel`: a `Shape` and the one-cycle `Step`),
   the phases `Ready` (after a reset, before the first start, `done` = 0), `Busy x m` (working on the operands `x`, `done`
   within `m + 1` more cycles) and `Fin x` (`done` = 1, `C` the product), and the one-cycle obligations
   `reset`, `start`, `busy`, `hold_ready` and `hold_fin`;
6. the shape at every power-up state (`powerUp_cons` once per declaration);
7. rule 1, `MooreOutDep`: for a design whose every process is an `always_ff`, `MooreOutDep.of_noComb` with
   `combDeps_of_ffOnly`;
8. rule 3, `XSafe`: a `simp` over `xsafeB` and its helpers (`xsProc`, `xsStmt`, `xsWidth`, ...).

**Lay the design out so the proof stays short**:

* register every output: with only `always_ff` processes, rule 1 is one line (`combDeps_of_ffOnly`);
* keep every process an `always_ff` whose body writes with nonblocking assignments only: the library's clock
  step in closed form (`cycleStep2_ffOnly`; the reference uses it through `cycleStep2_profile`) is for such
  designs only. A continuous `assign` or an `always_comb` block anywhere, an output driven by one included,
  means proving the combinational settle yourself, as the arbiter's proof does ([PROVING.md, section
  20](../../PROVING.md#20-a-reactive-task-the-arbiter-reacttask));
* reset every register whose value matters (`busy`, `done`, the step counter): the claims hold from every
  power-up value, the first reset edge included (a design whose `done` timing within the latency depends on an
  unreset register can still be correct: the post-synthesis check holds each power-up's run to the claims);
  the operand and accumulator registers may stay unreset when `start` loads them, as in the reference;
* nest generate loops: the loader gives each generate loop a fixed budget of `(N + W + AccW + 2)² + 64`
  iterations at a point (the sum of the parameter values plus 2, squared, plus 64), and a nested loop gets the
  whole budget again. A loop over `N` or `N²` iterations always fits, and so does one loop per index, nested as
  in the reference. One flat loop over the bits of a port (`N·N·W` or `N·N·AccW` lanes) or over `(i, j, k)`
  triples (`N³`) exceeds the budget at points in the range (at `(30, 10, 1)`: 9000 lanes against 1913), and
  there the loader gives up: the design reads as an empty one, so the statement is unprovable, however correct
  the circuit is;
* for `XSafe`, operands of one width (sign-extend explicitly, as the reference does) and run-time indices
  whose every value is in range; shifting the operand registers keeps every select static;
* no `$signed(...)` widened into a wider sum: ls-sv refuses its width conversion
  (`ConversionExpression:width`, at the `design` stage), although `score/ppa.py` weighs the design. Sign-extend
  a `W`-bit entry `x` by hand, as the reference does: `{{AccW{x[W-1]}}, x}`.

**The skeleton** (`reference/matmul_g1.lean` is it, filled in for the reference):

```lean
-- svgolf-latency: 4
import Submission.Design
import SvGolf.SeqV2

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N   -- yours: your design's latency

-- 1. agreement: `design.sem N W AccW = myD N W AccW`, a hand-built Design2
-- 2. one cycle in closed form; 3. the invariant; 4. the phase model `model N W AccW`

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hW, hA, hNW, -⟩ := hp
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (my_interface N W AccW hN hW hA)
    (my_disciplined N W AccW hN hW hA) (my_terminatesPU N W AccW hN hW hA) hN
    (model N W AccW hN hW hA hNW) (my_powerUp N W AccW hN hW hA) (my_moore N W AccW hN hW hA)
    (my_xsafe N W AccW hN hW hA)

end Submission
```

`#print axioms solution` must show `propext`, `Classical.choice` and `Quot.sound` only.

**Library lemmas that exist today**:

* `SvGolf.SeqV2`: `TxTask.satisfiedAtV2_of_phases` (the reduction), `MooreOutDep.of_noComb`,
  `combDeps_of_ffOnly`, `MooreOutDep.of_check` (rule 1 by evaluation, for a design with combinational logic),
  `TerminatesPU.of_invariant`, `powerUp_cons`, `powerUp_nil`;
* `SvGolf.Seq`: `TxTask.PhaseModel` and the v1 reduction it feeds (`TxTask.guar_of_phases`);
* `LeanModels.Sv.SeqProfile`, `LeanModels.Sv.SeqFamily`, `LeanModels.Sv.NbaCommit`: G0's clock step for a
  flip-flop-only design and the packed-family commit lemmas; `LeanModels.Sv.Lib.BitVecArith` and
  `LeanModels.Sv.CombViewArith` for the sign extensions and the wrapped sums.

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
every summation order is legal. Overflow wraps, as GPU accumulators do (decided 11/03). Examples:
- `[[-1, 2], [3, 4]] · [[5, 6], [7, 0]] = [[9, -6], [43, 18]]`. At `W = 4`, `AccW = 8` that is
  `A = 16'h432F`, `B = 16'h0765`, `C = 32'h122BFA09`.
- `[[-8]] · [[-8]] = 64`: `8'h40` at `AccW = 8`, and `0` at `AccW = 6` (`W = 4`).

## The handshake

The clock is `clk`, rising edge. Below, "entry `c`" is the inputs of cycle `c`, and "snapshot `c`" is the
state after cycle `c`'s edge.
- **Reset.** `rst` is synchronous and active high, held for at least one cycle. Nothing is claimed while it
  is 1 or before the first reset, and the claims hold from every power-up state of the design. Claims begin
  at the first entry after `rst` falls. A reset aborts: the claims stop at the entry that asserts it. The
  snapshot just before that entry is still claimed, and since no output may read an input combinationally,
  `rst` included (rule 1; decided 2026-11-09), it is on the wire for the whole reset cycle too.
- **Start.** `start` is a one-cycle pulse. The environment raises it only when the design is idle: no
  transaction since the release, or the last one has shown `done` = 1. The earliest legal starts are the
  first entry after the release, and the entry right after the snapshot that first shows `done`
  (back-to-back).
- **Operands.** `A` and `B` are held from the start entry through the entry whose edge first shows `done`.
  Outside that window they are free: any known values, which the claim ignores.
- **Done.** `done` is known in every snapshot after the release. `done` = 1 claims a result, and before the
  first start there is none, so between the release and the first start `done` is 0 (as the sorter's
  `out_valid`; decided 2026-11-09). After a start it first shows 1 within `lat` cycles: at
  snapshot `s + d` with `d ≤ lat`, where `s` is the snapshot right after the edge that samples `start` (so a
  `done` already visible there has `d = 0`). Before that it is 0. Early completion and data-dependent latency
  are legal.
- **Hold.** From that snapshot until the next start, `done` = 1 and `C` = `A·B` for the transaction's
  operands. `C` matters only there; elsewhere it is free. If a design keeps `done` = 1 in the snapshot of a
  back-to-back start, that counts as the new transaction finishing at once, so `C` must already be the new
  product there.

The latency function `lat N W AccW ≥ 1` is the submission's own, defined in its Lean file (so a design whose
`done` already shows at `d = 0` still declares at least 1). The number scored is `n = lat 4 8 32`.

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
  task.StatementV2 (fun p => sem p.1 p.2.1 p.2.2) (fun p => lat p.1 p.2.1 p.2.2)
```

`product` is the sum above: an `Int` dot product of the sign-extended entries (`BitVec.toInt`), then
`BitVec.ofInt AccW`, packed row-major. `TxTask.StatementV2` is txtask-v2. For every point in range it asks
for (`TxTask.SatisfiedAtV2`):

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
  included, from `rst`, `start`, `A` or `B` to `done` or `C`, so what a snapshot shows is on the wire for the
  whole next period;
- **no construct that can create an `x` from known operands** (rule 3, `XSafe`): with concrete power-up
  states and known inputs, every value a run computes is then known, and no simulator resolution of an
  unknown is ever taken.

`SvGolf/TaskSeq.lean` defines `TxTask` and the rules. `design/sequential/CONTRACT.md` is the decision log, C1
to C10, with the formal reading of each item; `design/soundness/TXTASK-V2-REVIEW.md` is the review of v2;
`REVIEW.md` is this task's review: what the statement says, why it cannot be met vacuously, and the open
points. The v1 text was frozen on 11/03 as the git tag `txtask-v1`; v2 (2026-11-05) replaced its run from
ls-sv's `x` start by every power-up and added rules 1 and 3, and it is final since 2026-11-08. Its three
amendments of 2026-11-09 (`done` = 0 before the first start, rule 1 with nothing exempt, no asynchronous reset;
`REVIEW.md`) were made in place before any record of the task was published. A later statement change is a version
bump that re-issues the records, never an edit.

The refusal register ([`REFUSALS.md`](../../REFUSALS.md), rendered from the register at the pinned revision) still
names the superseded `TxTask.Statement` (txtask-v1) in its row for this task's guarantee and says that each matmul
attack is wrong at post-synthesis. The ranked statement is `TxTask.StatementV2`, and `async_reset` is refused at
`source`; the register's newer text comes with the next pin.

## Rules for this task

* **No task-specific banned operators** (C6, decided 11/03). `*` is allowed: the score prices it. Run-time
  `/ % **` are banned, as in every task (since 2026-11-06; the svGolf README, "Rules").
* **The latency line.** `Solution.lean` declares its latency in exactly one header line
  `-- svgolf-latency: n` (a decimal number of cycles, 1 to 999999999) and defines
  `Submission.lat : Nat → Nat → Nat → Nat`; the goal pins `Submission.lat 4 8 32 = n`, and the score uses `n`.
  `lat` is your function: at every other point it need only be a bound your proof establishes. At each point of the post-synthesis check the checker has the kernel evaluate `Submission.lat` there (it
  must reduce to a number, 1 to 999999999) and runs that point against it (decided 2026-11-08); without a
  proof, `check.py --unproved` takes `--latency-at POINT:n` for those points (else the scoring point's `n`).
* **One clock, synchronous reset, no asynchronous process**: exactly one clock and one edge
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
* **Parameter range** (C10): `N·N·W < 2^31` and `N·N·AccW < 2^31`, so every width and index expression of the
  interface stays in the 32-bit `int` range. The design's own `int` expressions are checked to agree with a
  32-bit elaboration (`PDesign.int32Agrees`) at the probe and scoring points; between them the proof is about
  ls-sv's unbounded integers, so keep the design's constant expressions within the range (the reference's stay
  below `N·N·W` and `N·N·AccW`).
* **Probe points**: the extractor cross-checks the design at `(N, W, AccW)` = `(1, 1, 1)`, `(2, 3, 5)`,
  `(3, 4, 8)` and the scoring point `(4, 8, 32)`. Mind `N = 1`, and `W = 1`, where an entry is 0 or -1.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`allow_bv_decide: false`). No `native_decide`,
  no `sorry`. Proof time limit: 300 CPU s, the one limit of every task (the reference: 16.2 to 17.5 CPU s,
  three cold runs, 2026-11-07, `score/time_limits.json`).
* **Scoring at `(4, 8, 32)`** (C7, the sky130 decision of 11/03): area is sky130 A0' µm², flops (`dfxtp_1`)
  included. Time is `n` × the register-to-register period in ps from the pinned liberty, which already
  includes the flop's clock-to-Q and setup. Both are taken on the netlist REPAIRED by buffering only (a buffer
  tree on every net over its driver's limits, flop Q nets, inputs and output bits included; `sky130_a0_v2`,
  11/04), every input driven by the default `sky130_fd_sc_hd__buf_8` (`sky130_a0_v3`); a design the repair
  cannot make electrically legal is rejected at stage `ppa`. The reference: 87,173.6064 µm², period 10,696 ps,
  time 42,784 ps, every load pin read per edge (`sky130_a0_v3`; 6 buffers on 5 nets: busy's flop Q 1 x
  `buf_4`, NOR(busy, start) and NOR(rst, .) 1 x `buf_8` each, one more control net 2 x `buf_4`, the input
  `start` 1 x `buf_12`; `tests/expected.json`). Before the per-edge loads it was 10,705 ps and 42,820 ps under
  v2's `buf_1` and v3's `buf_8` alike (5 buffers, the third control net 1 x `buf_8`, the same area); the
  unrepaired v1 netlist read 48,079 ps from extrapolated tables, and duplicating one control flop was then a
  4.4× time shortcut that loses under v2: 43,560 ps). The ranked number is area × time,
  `area × (n × period)` in µm²·ns (decided 11/05), and the task is ranked by it (decided 2026-11-08); the
  Pareto frontier of (area, time) is an exploration view. On a tie in both, the earlier record stands. NAND2
  gate equivalents and unit depth are extra columns. One submission declares one latency: the same design
  with another `n` is a separate record. Every number can be reproduced bit for bit: score/PPA.md, "Reproduce
  a score" (`ppa.py --seq` for a clocked task).
* **Special cases are legal but do not pay.** A design may treat `N = 4` specially, but it must still be
  correct, and proved, for every `N`.
* **Post-synthesis check** (`task.json` `postsynth`) at `(2, 4, 8)` and `(4, 8, 32)`. For each of 8 seeds
  (3 before 2026-11-07, F5; every random draw from `$SVGOLF_POSTSYNTH_SALT`): a random power-up state, one
  reset cycle, then `oracle.py`'s 24 transactions. Where the netlist and ls-sv start from the same state
  (seed 0, from all zeros) the netlist must agree with ls-sv cycle by cycle, on `done` everywhere and on `C`
  wherever `done` = 1 after a start; from different power-up states ls-sv's own run must meet the statement's
  claims (L5 of the task's `REVIEW.md`, fixed 2026-11-08). Its `C` must also be `good` for the oracle, so a bug shared by the design and
  ls-sv is still caught. `done` must first rise within the point's latency. An x or z on `done` after the release, or on `C` while `done` = 1 after a start, rejects.
* **Input drive** (the sky130 score, `sky130_a0_v3`): every primary input is driven by `sky130_fd_sc_hd__buf_8`,
  the default (`task.json` names no `input_drive`), standing for the on-chip bus or register that feeds the
  block; the record says so in `ppa.setup.input_drive` (score/PPA.md, "The input drive").

## What counts as a solution

A file `solution.sv` with the module above, and a Lean file `Solution.lean`. The Lean file defines the
latency function `Submission.lat : Nat → Nat → Nat → Nat`, declares `n` with a header line
`-- svgolf-latency: n`, and proves `Submission.Goal`. That goal is
`SvGolf.Tasks.Matmul.Statement design.sem Submission.lat ∧ Submission.lat 4 8 32 = n`, for the design the
checker extracts from `solution.sv` (`check.py`'s kind `tx-family`):

```bash
python3.12 check.py tasks/matmul solution.sv Solution.lean
```

Without a proof, `check.py --unproved --latency n tasks/matmul solution.sv` runs every other stage, the
clocked post-synthesis check included, against the latency you mean to claim.

## The reference (`reference/matmul_g1.sv`)

`N²` multiply-accumulate units and one step counter `k`. `start` captures `A` and `B` into shift registers
and clears `C`. At step `k`, unit `(i, j)` adds `A[i][k]·B[k][j]`, both operands sign-extended to `AccW`
bits, and the register's width does the wrap. Each step shifts `A` by one entry and `B` by one row, so every
select is static. `done` rises after the `N`-th step and stays 1, with `C` held, until the next `start`.
There are only flip-flops, all written by nonblocking assignments; the reset clears `busy`, `done` and `k`,
and `start` loads the operand registers and clears `C`.

**Timing**, MEASURED (iverilog, 11/03, at the five probe and post-synthesis points, 3 seeds × 24
transactions each): `done` first shows 1 exactly `N` snapshots after the start edge (`d = N`), holds with
`C` unchanged through every gap, and `C` is `good` on all 360 transactions. So the reference meets `lat = N`
by the contract's count. `N + 1`, an earlier plan's figure, is also a valid bound, but it scores `n = 5`
instead of `4`. The proof declares `lat = N`.

**Proof**: `reference/matmul_g1.lean` (851 lines), accepted by `check.py` (`n = 4`): the loaded family is the
hand-built one at every in-range point (`mm_sem_eq`), one cycle is G0's clock step (`mm_cycle`), the invariant
on `k` gives the product after `N` busy cycles (`pe_step`, `accC_N`), the phase model (`model`) holds from
every state of the register shape, every power-up state has that shape (`mm_powerUp`), rule 1 is
`combDeps_of_ffOnly` (`mm_moore`), rule 3 a `simp` over `xsafeB` (`mm_xsafe`), and
`TxTask.satisfiedAtV2_of_phases` (`SvGolf/SeqV2.lean`) turns them into the statement.

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

## Attack designs (`tests/matmul/attacks/`, MEASURED)

Six designs, each the reference with one change, correct-looking and wrong for some `N, W, AccW`; each is
rejected at the `solution` stage with the reference's proof, and each is also rejected by the clocked
post-synthesis check alone (`check.py --unproved --latency 4`), so none is merely different
(`tests/expected.json` has the messages and the first failing transaction of each):

| attack | the change | wrong for | where the proof fails |
|---|---|---|---|
| `off_by_one_k` | the step counter starts at 1: `N - 1` busy steps, the last product never reaches `C` | every `N` | `mm_ctrl` |
| `done_early` | `done` is set one step early while the accumulation runs all `N` steps | every `N` | `mm_ctrl` |
| `no_clear_on_start` | the accumulators are cleared by the reset, not by `start`: every later transaction adds onto the previous result | every point | `pe_inst` |
| `unsigned_product` | the operands are not extended: the `W`-bit part-selects are zero-extended, an unsigned product | `AccW > W ≥ 2` | `pe_inst` |
| `missing_sign_ext` | the product is sign-extended only to `2W` bits, then zero-extended into the accumulator | `AccW > 2W` | `mm_decls`, `pe_inst` |
| `acc_2w` | the accumulator is `2W` bits, sign-extended to `AccW` by continuous assignments | `AccW > 2W` | `mm_decls`, `pe_inst` |

The last two are right where `AccW ≤ 2W`, so the check rejects them at `(4, 8, 32)` only (171 and 33 failures)
and passes them at `(2, 4, 8)`; the others fail at `(2, 4, 8)` already (69 to 153 failures).

A seventh design, `async_reset` (point L-a of the readiness review of 2026-11-08, [`REVIEW.md`](REVIEW.md)),
gives the control process an asynchronous reset (`always_ff @(posedge clk or posedge rst)`). The source gate
refuses it at `source`, and since 2026-11-09 the statement does too: `TxTask.Disciplined` is `ClockedBy clk none`,
and `tests/matmul/negative/Refute.lean` refutes it for every latency (`async_reset_refuted`).

## Scores

MEASURED by `check.py` (the clocked score, `tests/expected.json`; the same numbers at 2026-11-08, `tests/run.py
--only matmul`) at the scoring point `(4, 8, 32)`: area **87,173.6064 µm²** (sky130 A0′, 802 `dfxtp_1` flops),
time **4 × 10,696 ps = 42,784 ps** (`n = 4`; the register-to-register period over a 60-cell datapath path, on
the netlist repaired by buffering only). The ranked number, area × time: **3,729,635.58 µm²·ns** (DERIVED from
the two). Extra columns: 20,783.15 GE, unit depth 61.
