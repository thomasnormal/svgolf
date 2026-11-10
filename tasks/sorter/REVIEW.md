# `sorter` and `StreamTask`: review of the trusted statement, the oracle and the reference

Files under review, both trusted text:
- [Spec.lean](Spec.lean), the task;
- [../../SvGolf/TaskSeq.lean](../../SvGolf/TaskSeq.lean), the handshake, `StreamTask` and txtask-v2.

The task states txtask-v2, `StreamTask.StatementV2`, final since 2026-11-08 and amended on 2026-11-09, before
any record of the task was published (the first section below). The sections after it are the review of
txtask-v1 (11/03 to 11/04), kept as written then, apart from neutral
wording: v2 keeps every v1 claim word for word, so what they say about the handshake, the defences and the
oracle still holds. `lake build tasks.sorter.Spec` builds the statement. Labels: **MEASURED** = run,
**READ** = read off the source, **DERIVED** = argued, **JUDGED** = opinion.

## txtask-v2: the ranked statement (final, decided 2026-11-08)

**What the task states.** `Statement sem lat := task.StatementV2 …`, which at every point in range is
`StreamTask.SatisfiedAtV2`: v1's interface (with distinct declaration names, decided 2026-11-06), the clock
discipline with no asynchronous reset (`ClockedBy clk none`, decided 2026-11-09; the frozen tag `txtask-v1`
admitted one on `rst`), `lat ≥ 1`, and

* **rule 2, every power-up**: termination (`TerminatesPU`) and v1's claim, word for word (`FollowsPU`), of
  every run from EVERY power-up state (every declared signal, 2-state ones included, at some 0/1 value of
  its width), under every schedule, on every known stimulus. This replaces v1's run from ls-sv's `x` start
  (`initState2`), where a simulator's resolution of an unknown (`if (x)` takes the else branch) decided what
  the proof was about;
* **rule 1, Moore outputs** (`MooreOutDep d []`: nothing exempt since 2026-11-09): no combinational path,
  control dependencies included, from `rst`, `start`, `in_valid` or `in_data` to `out_valid` or `out_data`;
* **rule 3, no construct that creates an `x` from known operands** (`XSafe`).

Comments of the trusted text that predate the 2026-11-09 amendment are out of date (READ): `SvGolf/TaskSeq.lean`
says twice (l.66-67, l.666-667) that everything before its v2 section is txtask-v1, unchanged but for the
distinct-names conjunct, although `TxTask.Disciplined`, `StreamTask.Disciplined` and `TxTask.Guar` changed there,
and l.693-694 and [Spec.lean](Spec.lean) l.39 call the v2 clock discipline v1's, which it no longer is. The
definitions are what this section states; the next round that edits the trusted text corrects the comments.

READ: no run from the `x` start is reached any more; the statement's runs are `run2At` from a power-up state
(`ModelsPU`, `TerminatesPU`). The full text, the reasons (the Mealy phantom F1 and the x-optimism H1 that a
soundness probe found in v1) and the acceptance table are in
[`design/soundness/TXTASK-V2-REVIEW.md`](../../design/soundness/TXTASK-V2-REVIEW.md).

**The decisions it rests on.**
* 2026-11-05: IEEE 1800 decides defined values and ls-sv is never changed for the pinned flow; an `x` is an
  unknown 0/1 value, so a proof holds for every resolution; rules 1 to 3.
* 2026-11-06: stimuli stay known-input; rule 3 stays structural; a Python twin of rule 3 refuses before the
  proof (`clocked_rules`); never-loaded registers are refused in every clocked task; each `Interface` asks for
  distinct declaration names; the sorter states v2.
* 2026-11-07: the primitives the reactive kind shares are final; the post-synthesis check runs 8 seeds, every
  draw from a salt (F5).
* 2026-11-08: the tx/stream half of txtask-v2 is final (`SvGolf/TaskSeq.lean`'s Status lists it), and the
  sorter, then matmul, leave preview and rank. A later statement change is a version bump that re-issues the
  records.
* 2026-11-09, before the first records were published: rule 1 exempts nothing, `rst` included; no asynchronous
  reset (`Disciplined` is `ClockedBy clk none`).

**The reference proves it.** MEASURED (2026-11-08, `tests/run.py`, the references step): `sorter_ins` is
accepted (`--postsynth full`, 8 seeds at `(3, 4)` and `(8, 8)`, 1642 and 3990 cycles, 0 failures), its proof in
17.0 to 17.4 CPU s (`score/time_limits.json`). The design did not change for v2; its proof gained section 9
(every power-up state has the phase model's shape; rule 1 by `combDeps_of_ffOnly`; rule 3 by `simp`).

**The readiness review (2026-11-08).** Two independent reviews of the tx/stream statements approved them and
left these points (a label in the first column is the review's own, as the attacks' headers and
`tests/expected.json` cite it). The decisions of 2026-11-09 changed the statement for some of them (the
"how it stands" column says which).

| point | what it found | how it stands |
|---|---|---|
| the reset in rule 1 (low; L1) | rule 1 exempts `rst`, and `TxTask.SatisfiedAtV2`'s docstring argued that the wire then shows every claimed snapshot. But the claims up to a horizon `h` cover the snapshot `h - 1`, and the entry `h` may assert `rst`. MEASURED: a counter-design, the reference with registered outputs and `assign out_valid = ov_q & ~rst`, passes every check that needs no proof; a consumer at the edge of a reset sees 0 where the reference shows the last output | FIXED 2026-11-09: rule 1 exempts nothing (`MooreOutDep d []`, as `SeqTask`); the counter-design `tests/sorter/attacks/rst_gate.sv` is refuted for every latency (`tests/sorter/negative/Refute.lean`, `rst_gate_refuted`: the path from `rst` to `out_valid`) |
| `Spec.lean`'s operator sentence (low) | its docstring says run-time operators are not banned; every task bans run-time `/ % **` since 2026-11-06 (`task.json` `banlist`) | FIXED 2026-11-09: the sentence now says that run-time `/ % **` are banned, as in every task (a comment-only change) |
| 32-bit agreement (low) | `PDesign.int32Agrees` is checked at the probe and scoring points only; elsewhere in range `design.sem` is ls-sv's unbounded constant tier, so a design whose own `int` constants pass `2^31` there is proved about another circuit than a 32-bit simulator's (no scored netlist is affected) | recorded (Task v2 decision 1); the README says so |
| generate-loop fuel | the loader expands one generate loop to at most `(N + W + 2)² + 64` iterations | for the sorter every loop over `N`, `W`, `N·W` or `N²` fits; the README advises nested loops |
| an asynchronous reset (L-a of matmul's review) | `ClockedBy` pins the name of an asynchronous reset, not its level, and rule 1 does not see a path through its reset event | FIXED 2026-11-09: `StreamTask.Disciplined` is `ClockedBy clk none` (as `ReactTask.Disciplined`), so the statement itself refuses an asynchronous reset in either polarity (the source gate refuses it too) |
| undriven variables | rule 2 reads a variable no process writes as a power-up value that never changes, Yosys as undefined | a recorded dependency on `fourstate` (e) (TXTASK-V2-REVIEW.md section 10, finding B) |

**The post-synthesis check across two power-ups (L5), fixed 2026-11-08.** The check used to compare the netlist
with ls-sv bit for bit on `out_valid` at every cycle and on `out_data` where valid, also at the seeds where the
two start from DIFFERENT power-up states, so a correct design whose `out_valid` timing within the latency depends
on an unreset register could be rejected (recorded on 2026-11-06, TXTASK-V2-REVIEW.md section 12.2). Since
2026-11-08 it compares bit for bit only where the two start from the same state (seed 0, from all zeros), as the
reactive kind does, and from different power-ups it holds ls-sv's own run to the statement's claims up to its rely
horizon, beside the netlist's run against the task's evaluator. In the same round each post-synthesis point is run
against that point's latency, `Submission.lat` evaluated by the kernel (decided 2026-11-08).

**What v2 does not close.** A `unique`/`priority` case is validated by ls-sv on the snapshots, not where it
executes (an ls-sv bug; the source gate refuses the qualifiers); and ls-sv and the netlist can still differ on
defined values (a Yosys or ls-sv bug), which only the sampled post-synthesis check looks for.

## The statement in plain words (v1, kept by v2)

A submission is one module `sorter #(N, W)` with ports `clk, rst, start, in_valid, in_data[W]`
(inputs) and `out_valid, out_data[W]` (outputs), in this order, and a latency function
`lat N W ≥ 1`.

It satisfies the task at every `N, W ≥ 1` when:
- the ports, termination and the clock discipline hold, as for `matmul`;
- in every run, from every cycle after `rst` falls, up to any later cycle, the following holds,
  provided the environment followed the protocol so far:
  - **the environment:**
    - `start` is a one-cycle pulse, raised only when the design is idle (no transaction yet, or
      every earlier start's `N` outputs emitted);
    - after each `start`, `in_valid` = 1 for exactly the `N` cycles beginning the next cycle, with
      the values on `in_data`;
    - `in_valid` = 0 otherwise.
  - **the design:**
    - shows `out_valid` as a known bit at every cycle, and 0 before the first `start`;
    - from each `start` to the next, sets `out_valid` = 1 on exactly `N` cycles, all within `lat`
      cycles of the edge that samples `start`;
    - on those cycles, in order, puts on `out_data` the values sorted ascending as unsigned numbers,
      duplicates kept.

(v2 adds: in every run from every power-up state, Moore outputs, no x-creating construct.)

The sort is `sortAsc`, the insertion sort of C8, written out in `Spec.lean` (structural recursion,
which the kernel evaluates). Core Lean has no `List.insertionSort`, and the trusted text imports no
Mathlib.

## History: the txtask-v1 review (11/03 to 11/04)

The decisions were C1, C2, C3, C8 and C9 of
[../../design/sequential/CONTRACT.md](../../design/sequential/CONTRACT.md), defaults until the maintainers
ruled; interpretation points 6 and 7 there are the sorter's. The shared handshake and defences are those of
`TxTask` ([../matmul/REVIEW.md](../matmul/REVIEW.md)). The framework module was new and changed nothing in
`SvGolf/Task.lean` (placement as for `matmul`: kept separate).

### Why `StreamTask` is its own structure (C8)

`TxTask` has one result, held at `done`. A stream has `N` results, emitted one per valid cycle, with
no `done`. Overloading `TxTask` would make `done` mean "valid" and `C` a list, and so blur both
statements. The two share the handshake: reset release, `Idle`-only starts, the latency bound, flag
knownness and horizon-relative claims.

### Defences specific to the sorter

| attack | blocked by |
|---|---|
| dropping or duplicating a value | the emitted values must EQUAL the sorted list, so there are exactly `N` of them |
| emitting late, after the window | `out_valid` = 0 at every cycle after `s + lat` until the next start |
| emitting before `start`, or leftovers | `out_valid` = 0 before the first start; each transaction's segment emits exactly its own `N` values |
| x on `out_valid`, or on `out_data` when valid | known values |
| depending on `in_data` while `in_valid` = 0 | there the environment drives arbitrary known values |

### Evidence (in `Spec.lean`, proved)

- `sortAsc [3, 15, 0, 3, 8] = [0, 3, 3, 8, 15]` at `W = 4`.
- The port names are distinct.

### Open points (11/04)

As for `matmul`: the reduction theorem, flat designs only. The range includes `N·W < 2^31` (C10), so
a design that buffers the whole stream stays in the 32-bit `int` range. The reference (an insertion
array) is `reference/sorter_ins.sv`, now proved (`reference/sorter_ins.lean`, `lat = 2N` at every
`N, W ≥ 1`) and accepted by `check.py` (kind `stream-family`); see the last section.

### What the reference showed about the statement (11/04)

Read against `tasks/sorter/Spec.lean` and `StreamTask` at `txtask-v1`; no semantic defect found.
- **`start` is redundant under the rely.** `Rely` pins `in_valid` at every entry from the release:
  1 exactly when a start lies in `[c − N, c)`. So a design may ignore `start`, and the reference does
  (it inserts on `in_valid`, drains otherwise). This is a freedom, not a hole: every claim is still
  about the values on `in_valid` entries. It would change if a later version allowed input gaps.
- **No tie rule is observable.** The emitted values must equal `sortAsc xs` as a list of `W`-bit
  values, and equal values are equal there, so `<` against `≤` in a design never matters (measured:
  both tie variants of the reference pass). `sortAsc`'s own tie placement only shapes the proof's
  invariant, where the reference's strict `>` matches `insertAsc` exactly.
- **Latency floor.** No design meets `lat < 2N − 1`: the minimum depends on the value sampled at entry
  `s + N`. The reference has `2N` (registered output).
- **Stale labels.** `Spec.lean` and `SvGolf/TaskSeq.lean` (like `tasks/matmul/Spec.lean`) said
  "DRAFT of TRUSTED text, for review", although `CONTRACT.md` records the freeze as
  `txtask-v1`. Documentation only; fixing the Lean headers was left to `txtask-v2`, since the frozen
  text is not edited (`SvGolf/TaskSeq.lean`'s tx/stream half lost its banners on 2026-11-08).

### What the proof, the checker and the attacks showed (11/04)

Read against `txtask-v1` again, now with a proof through it; no defect found in the frozen text.
- **The proof goes through the statement as written.** `StreamTask.satisfiedAt_of_phases`
  (`SvGolf/Seq.lean`, untrusted; under v2 `StreamTask.satisfiedAtV2_of_phases`, `SvGolf/SeqV2.lean`) needs
  one fact about the spec beyond the phase model: `spec xs` has `count` elements (`Idle` asks for exactly
  `count` outputs). `sortAsc` keeps the length, so this is a property of THIS task's spec, not an extra
  assumption; a future stream task whose output length differs from its input count would need `Idle`
  restated (a question for that task's statement, not a sorter one).
- **The attacks** (`tests/sorter/attacks/`, seven, each the reference with one change): a token shift
  that reads its own cell, a missing `else`, the neighbour push reading the cell's own value, the token
  entering with the start, a reset that leaves the cells, a top cell the drain does not clear, signed
  order. MEASURED: every one is rejected at `solution` with the reference proof AND by the clocked
  post-synthesis check alone (`--unproved --latency 16`, 2 to 69 failures at `(3, 4)`), so each is a
  wrong design, not a different one. The designer's loop-bound mutant (`k < N-2`) is refused earlier, at
  `fourstate` (undriven bits), so it cannot serve as a proof attack and `token_self` replaces it.
- **The power-up state matters, and the checker sees it.** `reset_keeps_cells` is right whenever the
  cells happen to power up 0; the statement still refuses it (after a release the claim covers every
  initial state), the proof fails at `cell_inst`, and the post-synthesis check catches it both ways: the
  randomized netlist state gives a wrong first transaction, and ls-sv's `x` cells (v1's `x` start; under
  v2 ls-sv runs from concrete power-up states) give an unknown `out_data` where `out_valid` = 1.
- **Tie order is not an attack.** The two tie variants of `tests/sorter/sim.py` (`>=` for `>`) are
  correct designs: they emit the same list, so the statement holds for them. The reference's proof would
  fail on them (it is a proof of the reference), but that would show nothing about the statement, so
  they are kept out of the attacks on purpose.

### The oracle (`oracle.py`): what is reviewed with the spec

`good(params, txn, result)` is `result["out"] == sorted(txn["xs"])`: the values a design emitted on its
`out_valid` cycles from one start to the next, ascending, duplicates kept, exact (a value outside
`[0, 2^W)`, a missing or extra value is not good). `sort_asc` transcribes `Spec.lean`'s `sortAsc`
(`insertAsc` folded from the right, inserting before the first element it is `≤` to), and the self-test
checks `sorted == sort_asc` on every generated transaction. Out-of-range points raise.

`txns(params, seed)` is the stimulus. Its contract with the checker: `gap` counts idle entries before a
start, from the release for the first transaction, otherwise from the entry after the snapshot that
shows the previous transaction's `N`-th output (`StreamTask.Idle`), so 0 is back-to-back; `free` holds
known values for `in_data` on every entry with `in_valid` = 0, which `Rely` leaves free. The generator
never violates the rely provided the checker observes idleness (`tests/sorter/tb.sv` does). Question for
the review: a reset in the middle of a transaction (an abort) is not part of `txns`; `tests/sorter/sim.py`
adds one per seed, so a reset that leaves stale values in a half-loaded array shows in the next
transaction. The post-synthesis check could adopt it.
