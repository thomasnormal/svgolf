# `sorter` and `StreamTask`: review of the trusted statement, the oracle and the reference

Files under review, both trusted text (drafted 11/03, frozen as `txtask-v1`):
- [Spec.lean](Spec.lean), the task;
- [../../SvGolf/TaskSeq.lean](../../SvGolf/TaskSeq.lean), the handshake and `StreamTask`.

The decisions are C1, C2, C3, C8 and C9 of
[../../design/sequential/CONTRACT.md](../../design/sequential/CONTRACT.md), defaults until you rule;
interpretation points 6 and 7 there are the sorter's. The shared handshake and defences are those of
`TxTask` ([../matmul/REVIEW.md](../matmul/REVIEW.md)). `lake build tasks.sorter.Spec` builds the
statement. The framework module is new and changes nothing in `SvGolf/Task.lean` (placement as
for `matmul`: merged into it or kept separate at the `txtask-v1` freeze, your call).

## The statement in plain words

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

The sort is `sortAsc`, the insertion sort of C8, written out in `Spec.lean` (structural recursion,
which the kernel evaluates). Core Lean has no `List.insertionSort`, and the trusted text imports no
Mathlib.

## Why `StreamTask` is its own structure (C8)

`TxTask` has one result, held at `done`. A stream has `N` results, emitted one per valid cycle, with
no `done`. Overloading `TxTask` would make `done` mean "valid" and `C` a list, and so blur both
statements. The two share the handshake: reset release, `Idle`-only starts, the latency bound, flag
knownness and horizon-relative claims.

## Defences specific to the sorter

| attack | blocked by |
|---|---|
| dropping or duplicating a value | the emitted values must EQUAL the sorted list, so there are exactly `N` of them |
| emitting late, after the window | `out_valid` = 0 at every cycle after `s + lat` until the next start |
| emitting before `start`, or leftovers | `out_valid` = 0 before the first start; each transaction's segment emits exactly its own `N` values |
| x on `out_valid`, or on `out_data` when valid | known values |
| depending on `in_data` while `in_valid` = 0 | there the environment drives arbitrary known values |

## Evidence (in `Spec.lean`, proved)

- `sortAsc [3, 15, 0, 3, 8] = [0, 3, 3, 8, 15]` at `W = 4`.
- The port names are distinct.

## Open points

As for `matmul`: the reduction theorem, flat designs only. The range includes `N·W < 2^31` (C10), so
a design that buffers the whole stream stays in the 32-bit `int` range. The reference (an insertion
array) is `reference/sorter_ins.sv`, now proved (`reference/sorter_ins.lean`, `lat = 2N` at every
`N, W ≥ 1`) and accepted by `check.py` (kind `stream-family`); see the last section.

## What the reference showed about the statement (11/04)

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
- **Stale labels.** `Spec.lean` and `SvGolf/TaskSeq.lean` (like `tasks/matmul/Spec.lean`) still say
  "DRAFT of TRUSTED text, for review", although `CONTRACT.md` records the freeze as
  `txtask-v1`. Documentation only; fixing the Lean headers is a
  `txtask-v2` question, since the frozen text is not edited.

## What the proof, the checker and the attacks showed (11/04)

Read against `txtask-v1` again, now with a proof through it; no defect found in the frozen text.
- **The proof goes through the statement as written.** `StreamTask.satisfiedAt_of_phases`
  (`SvGolf/Seq.lean`, untrusted) needs one fact about the spec beyond the phase model: `spec xs` has
  `count` elements (`Idle` asks for exactly `count` outputs). `sortAsc` keeps the length, so this is a
  property of THIS task's spec, not an extra assumption; a future stream task whose output length differs
  from its input count would need `Idle` restated (a `txtask-v2` question, not a sorter one).
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
  randomized netlist state gives a wrong first transaction, and ls-sv's `x` cells give an unknown
  `out_data` where `out_valid` = 1.
- **Tie order is not an attack.** The two tie variants of `tests/sorter/sim.py` (`>=` for `>`) are
  correct designs: they emit the same list, so the statement holds for them. The reference's proof would
  fail on them (it is a proof of the reference), but that would show nothing about the statement, so
  they are kept out of the attacks on purpose.

## The oracle (`oracle.py`): what is reviewed with the spec

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
