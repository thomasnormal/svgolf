# `matmul` and `TxTask`: review of the trusted statement and of the task's oracle

Files under review:
- [Spec.lean](Spec.lean), the task, trusted;
- [../../SvGolf/TaskSeq.lean](../../SvGolf/TaskSeq.lean), the handshake and `TxTask`, trusted;
- [oracle.py](oracle.py), the task's own transaction evaluator, untrusted but binding in the
  post-synthesis check (section "The oracle" below).

The decisions they encode are the log [../../design/sequential/CONTRACT.md](../../design/sequential/CONTRACT.md).
**Frozen 11/03 as the git tag `txtask-v1`** (commit 0473d4d1): C1 to C10 stand as the lead's
defaults, delegated by the maintainers, with the arithmetic, the banlist and C7 ruled by them. A change is a
version bump (`txtask-v2`), never an edit of v1. `lake build tasks.matmul.Spec` builds the statement
and its sanity checks. The framework is a NEW module, `SvGolf/TaskSeq.lean`, that imports
`SvGolf/Task.lean` and changes nothing in it, so it rebuilds no combinational task statement and
moves no record's trusted-file hash. The sections below were written for the draft, and the text
has not changed since. Gate 3 step 1 added the package around it: `task.json` (kind `tx-family`),
`oracle.py` and `README.md`.

## The statement in plain words

A submission is one module `matmul #(N, W, AccW)` with ports `clk, rst, start, A[N·N·W], B[N·N·W]`
(inputs) and `done, C[N·N·AccW]` (outputs), in this order. Entries are flat, row-major and LSB-first:
entry `(i, k)` of `A` is `A[(i·N+k)·W +: W]`. It also declares a latency function `lat N W AccW ≥ 1`.

It satisfies the task at every `N, W, AccW ≥ 1` when:
- the ports are exactly these;
- every run terminates;
- the clock discipline holds (`ClockedBy`):
  - `clk` is an input port;
  - every flop is clocked by it;
  - nothing reads it as data;
  - an asynchronous reset could only be `rst`.
- In every run, from every cycle after `rst` falls, and up to any later cycle, the following holds,
  provided the environment followed the protocol so far:
  - **the environment:**
    - `rst` stays 0;
    - `start` is a one-cycle pulse, raised only when the design is idle (no transaction yet, or the
      last one has shown `done` = 1);
    - `A` and `B` are held from `start` until `done` rises.
  - **the design:**
    - shows `done` as a known bit at every cycle;
    - after each `start`, raises `done` within `lat` cycles of the edge that samples `start`;
    - from then until the next `start`, shows `done` = 1 and `C = A·B`, where the entries are
      signed `W`-bit and each `C[i][j] = Σ_k A[i][k]·B[k][j]` is taken mod `2^AccW`.

## What `TxTask` is

It is the transaction form of the sequential statements: held operands, one result, a declared
latency bound. It is a bounded-latency rely/guarantee contract, the D11 shape. The rely depends on
what the design shows (idleness reads `done`), so it is stated up to a horizon: a protocol violation
at a later cycle cannot void an earlier claim.

## Why it cannot be satisfied vacuously, and what each defence is

| attack | blocked by |
|---|---|
| never raising `done`, or raising it late | `Guar`: `done` = 1 at some cycle `≤ s + lat`. The first transaction after a reset is always rely-compliant (it is idle by definition), so the claim bites. `lat` is the declared, proved number |
| `done` early with a wrong or partial `C` | `Guar`: from the first `done` to the next `start`, `C` = the product at EVERY cycle |
| a result left over from the previous transaction | `done` must be known, so it is 0 until the new result is ready; a `done` = 1 in the start's own snapshot counts as the new result (CONTRACT.md, point 5) |
| x on `done` or on `C` while `done` = 1 | known values (`LVec.ofBitVec`) |
| depending on `A`/`B` after `done` | they are free there (any known values), and `C` must still hold the product |
| a clock that never ticks, or is gated, tied, read as data | `ClockedBy`, and the loader's own guard (`ClockGuard2.lean`) |
| an environment that cannot exist | the rely is about the stimulus. A single transaction held to the horizon always satisfies it; later transactions need only wait for `done` |
| state carried across a reset | claims start at EVERY release |

## Evidence (in `Spec.lean`, proved)

- A 2×2 product with a negative entry, `[[-1,2],[3,4]]·[[5,6],[7,0]] = [[9,-6],[43,18]]`, packed at
  `W = 4`, `AccW = 8`.
- Wrap at 8 and at 6 bits.
- The off-points `(1,1,1)`, `(2,3,5)`, `(3,4,8)` and the scoring point `(4,8,32)` are in range.
- The port names are distinct.

## Open points

- The `TxTask` reduction theorem is to come in `SvGolf/Seq.lean`: the statement from one-cycle lemmas
  plus a phase/latency invariant. It consumes A's closed-form cycle lemmas.
- `ClockedBy` forbids a clock copy, so flops inside child instances are not admitted (flat designs
  only, for now).
- Parameter range (C10, added 11/04): `N·N·W < 2^31 ∧ N·N·AccW < 2^31` keeps every width and index
  expression in the 32-bit `int` range, where a real elaboration and ls-sv's unbounded constant tier
  agree. Above it, a design's ports and part-select bases wrap in every simulator but not in the model.
- The latency count. By the contract's reading (CONTRACT.md, point 4), the reference
  `reference/matmul_g1.sv` shows `done` exactly `N` snapshots after the start edge (MEASURED in
  iverilog at five points, README.md "The reference"). PLAN4.md's `lat N = N + 1` is a valid bound
  but not the tight one, and the score takes the declared `n` (5 rather than 4 at the scoring
  point). The proof track decides which it proves. The text needs no change either way.
- `Spec.lean`'s header still reads "DRAFT of TRUSTED text, for review". The text is frozen,
  so the stale word stays until a version bump. It is reported here and not edited.

## The oracle (`oracle.py`): what is reviewed with the spec

Gate 2's clocked post-synthesis check has two binding comparisons: (i) the netlist against ls-sv,
and (ii) the netlist's `C` against the task's own evaluator, `oracle.py`'s `good`. Comparison (ii)
exists to catch a bug that ls-sv shares with the candidate, so `good` must be independent of the
Lean side. It uses Python integers only.

`product(N, W, AccW, a, b)` transcribes `Spec.lean`'s `product`:
- entry `idx` is bits `[idx·W, idx·W + W)`, read as two's complement (`BitVec.toInt`);
- `C[i][j]` is the exact integer `Σ_k A[i·N+k]·B[k·N+j]`, reduced by Python's `% 2^AccW`, which is
  `BitVec.ofInt`'s wrap;
- entry `(i, j)` is placed at bit `(i·N + j)·AccW`.

`good(params, txn, result)` is `result["C"] == product(…)`, exact: a result with a bit above the port
width, or without an integer `C`, is not good. Out-of-range points (`task.inRange`, C10 included)
raise rather than answer.

`txns(params, seed)` is the stimulus. Its contract with the checker:
- `gap` counts idle entries before a start: from the release for the first transaction, otherwise
  from the entry after the snapshot that first shows `done`. So gap 0 is the earliest start the rely
  allows (`TxTask.Idle`).
- The `free` operand values are driven only on those gap entries. That is outside every hold window
  (`TxTask.Rely` holds the operands up to and including the entry whose edge first shows `done`),
  so the generator never violates the rely.

Evidence, MEASURED with `python3 oracle.py` (0.16 s):
- the three `Spec.lean` examples;
- a second formulation of the product (k outermost, sign by subtraction) agreeing on all 600
  generated transactions (5 points × 5 seeds);
- determinism;
- coverage: extremes, back-to-back after a nonzero result, gaps, a hold longer than `N + 1`;
- at the post-synthesis points `(2, 4, 8)` and `(4, 8, 32)`, every seed tells apart each wrong
  arithmetic of the planned attacks, where it differs at all: an unsigned product, a missing sign
  extension, a `2W`-bit accumulator (both only when `AccW > 2W`), off-by-one `k` both ways, `B·A`,
  `Cᵀ`, and an accumulator not cleared on start.

Mutating the oracle (unsigned entries, a dropped `k`, `B·A`, no gaps, no free values, no extremes)
fails the self-test each time.

Questions for the review:
- The post-synthesis budget in `task.json` (8 seeds × 24 transactions since 2026-11-07, F5; 3 seeds
  before; one reset cycle, at
  `(2, 4, 8)` and `(4, 8, 32)`) is a proposal. ls-sv's per-cycle cost on the reference is not
  measured yet.
- The `postsynth` keys `points`, `seeds`, `reset_cycles`, `txns`, and the top-level `clock`, `reset`
  and `protocol`, are this package's proposal for the `tx-family` kind. The checker defines the
  final names.
