# `matmul` and `TxTask`: review of the trusted statement and of the task's oracle

Files under review:
- [Spec.lean](Spec.lean), the task, trusted;
- [../../SvGolf/TaskSeq.lean](../../SvGolf/TaskSeq.lean), the handshake, `TxTask` and txtask-v2, trusted;
- [oracle.py](oracle.py), the task's own transaction evaluator, untrusted but binding in the
  post-synthesis check (section "The oracle" below).

The task states txtask-v2, `TxTask.StatementV2`, final since 2026-11-08 and amended on 2026-11-09, before any
record of the task was published (the first section below). The sections after it are the review of
txtask-v1 (11/03 to 11/04), kept as written then, apart from neutral
wording: v2 keeps every v1 claim word for word, so what they say about the handshake, the defences and the
oracle still holds. The decisions they encode are the log
[../../design/sequential/CONTRACT.md](../../design/sequential/CONTRACT.md). `lake build tasks.matmul.Spec`
builds the statement and its sanity checks. Labels: **MEASURED** = run, **READ** = read off the source,
**DERIVED** = argued, **JUDGED** = opinion.

## txtask-v2: the ranked statement (final, decided 2026-11-08)

**What the task states.** `Statement sem lat := task.StatementV2 …`, which at every point in range is
`TxTask.SatisfiedAtV2`: v1's interface (with distinct declaration names, decided 2026-11-06), the clock
discipline with no asynchronous reset (`ClockedBy clk none`, decided 2026-11-09; the frozen tag `txtask-v1`
admitted one on `rst`), `lat ≥ 1`, and

* **rule 2, every power-up**: termination (`TerminatesPU`) and v1's claim, word for word (`FollowsPU`; its
  `Guar` asks `done` = 0 from the release up to the first start since 2026-11-09), of
  every run from EVERY power-up state (every declared signal, 2-state ones included, at some 0/1 value of
  its width), under every schedule, on every known stimulus. This replaces v1's run from ls-sv's `x` start
  (`initState2`), where a simulator's resolution of an unknown (`if (x)` takes the else branch) decided what
  the proof was about;
* **rule 1, Moore outputs** (`MooreOutDep d []`: nothing exempt since 2026-11-09): no combinational path,
  control dependencies included, from `rst`, `start`, `A` or `B` to `done` or `C`;
* **rule 3, no construct that creates an `x` from known operands** (`XSafe`).

Comments of the trusted text that predate the 2026-11-09 amendment are out of date (READ): `SvGolf/TaskSeq.lean`
says twice (l.66-67, l.666-667) that everything before its v2 section is txtask-v1, unchanged but for the
distinct-names conjunct, although `TxTask.Disciplined`, `StreamTask.Disciplined` and `TxTask.Guar` changed there,
and l.693-694 and [Spec.lean](Spec.lean) l.43 call the v2 clock discipline v1's, which it no longer is. The
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
  distinct declaration names; matmul states v2.
* 2026-11-07: the primitives the reactive kind shares are final; the post-synthesis check runs 8 seeds, every
  draw from a salt (F5).
* 2026-11-08: the tx/stream half of txtask-v2 is final (`SvGolf/TaskSeq.lean`'s Status lists it), and the
  sorter, then matmul, leave preview and rank. A later statement change is a version bump that re-issues the
  records.
* 2026-11-09, before the first records were published: `done` is 0 from the release up to the first start
  (`TxTask.Guar` gains `StreamTask.Guar`'s conjunct); rule 1 exempts nothing, `rst` included; no asynchronous
  reset (`Disciplined` is `ClockedBy clk none`).

**The reference proves it.** MEASURED (2026-11-08, `tests/run.py`, the references step): `matmul_g1` is
accepted (`--postsynth full`, 8 seeds at `(2, 4, 8)` and `(4, 8, 32)`, 828 and 1257 cycles, 0 failures), its
proof in 16.2 to 17.5 CPU s (`score/time_limits.json`). The design did not change for v2; its proof gained
section 8 (every power-up state has the phase model's shape; rule 1 by `combDeps_of_ffOnly`; rule 3 by
`simp`).

**The readiness review (2026-11-08).** Two independent reviews of the tx/stream statements approved them and
left these points (a label in the first column is the review's own, as the attacks' headers and
`tests/expected.json` cite it). The decisions of 2026-11-09 changed the statement for some of them (the
"how it stands" column says which).

| point | what it found | how it stands |
|---|---|---|
| `done` before the first start (medium) | between a release and the first start, `TxTask.Guar` asks only that `done` be known; `StreamTask.Guar`, by contrast, asks `out_valid` = 0 there (CONTRACT.md, point 6). MEASURED: a counter-design, the reference with `done <= 1'b1` in its reset branch and a six-line edit of the reference proof, is accepted end to end (`--postsynth full`, 0 mismatches; 87009.6992 µm² x 43088 ps), showing `done` = 1 with three different garbage `C` values from three power-ups before the first start | FIXED 2026-11-09: `done` = 1 claims a result, and before the first start there is none, so `TxTask.Guar` asks `done` = 0 from the release up to the first start (the conjunct `StreamTask.Guar` has); the counter-design is now refuted (`tests/matmul/negative/Mutants.lean`, the generated mutants that raise `done` before the first start), and the post-synthesis check holds the netlist and ls-sv's run to it |
| generate-loop fuel (medium) | the loader expands one generate loop to at most `(N + W + AccW + 2)² + 64` iterations at a point (`PDesign.surfaceFuel`, per loop). MEASURED: the reference plus one flat loop over the `N·N·W` bits of `A` instantiates at `(4, 8, 32)` and times out at `(30, 10, 1)` and `(20, 4, 1)`, both in range, where `design.sem` becomes the error design and no proof can hold | the refusal is loud, not unsound; the README and PROVING.md section 19 say it and advise one loop per index, nested as in the reference; a fuel that covers a product of the parameters is a later ls-sv change |
| an asynchronous reset (low; L-a) | `ClockedBy` pins the name of an asynchronous reset, not its level, and rule 1 does not see a path through its reset event | FIXED 2026-11-09: `TxTask.Disciplined` is `ClockedBy clk none` (as `ReactTask.Disciplined`), so the statement itself refuses an asynchronous reset in either polarity; `tests/matmul/attacks/async_reset.sv` is refuted for every latency (`async_reset_refuted`) and pinned at `source` |
| the reset in rule 1 (low; L1 of the sorter's review) | rule 1 exempts `rst`; the claims up to a horizon `h` cover the snapshot `h - 1`, and the entry `h` may assert `rst`, so an output gated by the reset may show a claimed value in that snapshot and another on the wire (measured on the sorter) | FIXED 2026-11-09: rule 1 exempts nothing (`MooreOutDep d []`, as `SeqTask`), so an output may not read `rst` combinationally either; the counter-design is refuted (`tests/sorter/negative/Refute.lean`, `rst_gate_refuted`) |
| undriven variables (low) | rule 2 reads a variable no process writes as a power-up value that never changes, Yosys as undefined | a recorded dependency on `fourstate` (e) (TXTASK-V2-REVIEW.md section 10, finding B) |
| 32-bit agreement (low) | `PDesign.int32Agrees` is checked at the probe and scoring points only; elsewhere in range `design.sem` is ls-sv's unbounded constant tier. The interface's own widths and indices stay below `2^31` at every point in range (`(i*N+k)*W + W - 1 ≤ N*N*W - 1`), and the scored and post-synthesis points are among those probed | recorded (Task v2 decision 1); the README says so |
| `lat` at other points (low) | `lat` is constrained only by the proof at points other than the scoring point, so it may be very large there | by design; the README says that `lat` elsewhere need only be a bound the proof establishes |
| `Spec.lean`'s operator sentence (low) | its docstring says run-time operators are not banned; every task bans run-time `/ % **` since 2026-11-06 (`task.json` `banlist`) | FIXED 2026-11-09: the sentence now says that run-time `/ % **` are banned, as in every task (a comment-only change) |

**The post-synthesis check across two power-ups (L5), fixed 2026-11-08.** The check used to compare the netlist
with ls-sv bit for bit on `done` at every cycle and on `C` where `done` = 1 after a start, also at the seeds where
the two start from DIFFERENT power-up states, so a correct design whose `done` timing within the latency depends
on an unreset register could be rejected (recorded on 2026-11-06, TXTASK-V2-REVIEW.md section 12.2). Since
2026-11-08 it compares bit for bit only where the two start from the same state (seed 0, from all zeros), as the
reactive kind does, and from different power-ups it holds ls-sv's own run to the statement's claims up to its rely
horizon, beside the netlist's run against the task's evaluator. In the same round each post-synthesis point is run
against that point's latency, `Submission.lat` evaluated by the kernel (decided 2026-11-08).

**What v2 does not close.** A `unique`/`priority` case is validated by ls-sv on the snapshots, not where it
executes (an ls-sv bug; the source gate refuses the qualifiers); and ls-sv and the netlist can still differ on
defined values (a Yosys or ls-sv bug), which only the sampled post-synthesis check looks for.

## History: the txtask-v1 review (11/03 to 11/04)

**Frozen 11/03 as the git tag `txtask-v1`** (commit 0473d4d1): C1 to C10 stood as defaults delegated by the
maintainers, with the arithmetic, the banlist and C7 decided by them. A change is a version bump
(`txtask-v2`), never an edit of v1. The framework is a NEW module, `SvGolf/TaskSeq.lean`, that imports
`SvGolf/Task.lean` and changes nothing in it, so it rebuilds no combinational task statement and moves no
record's trusted-file hash. The sections below were written for the draft, and the v1 text did not change
after them. The task package (`task.json`, kind `tx-family`, `oracle.py` and `README.md`) was added around it.

### The statement in plain words

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
  - no flop has an asynchronous reset (since 2026-11-09; before, one could only be on `rst`).
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

(v2 adds: in every run from every power-up state, Moore outputs, no x-creating construct.)

### What `TxTask` is

It is the transaction form of the sequential statements: held operands, one result, a declared
latency bound. It is a bounded-latency rely/guarantee contract, the D11 shape. The rely depends on
what the design shows (idleness reads `done`), so it is stated up to a horizon: a protocol violation
at a later cycle cannot void an earlier claim.

### Why it cannot be satisfied vacuously, and what each defence is

| attack | blocked by |
|---|---|
| never raising `done`, or raising it late | `Guar`: `done` = 1 at some cycle `≤ s + lat`. The first transaction after a reset is always rely-compliant (it is idle by definition), so the claim bites. `lat` is the declared, proved number |
| `done` early with a wrong or partial `C` | `Guar`: from the first `done` to the next `start`, `C` = the product at EVERY cycle |
| a result left over from the previous transaction | `done` must be known, so it is 0 until the new result is ready; a `done` = 1 in the start's own snapshot counts as the new result (CONTRACT.md, point 5) |
| `done` = 1 before there is a result | `Guar`: `done` = 0 from the release up to the first start |
| x on `done` or on `C` while `done` = 1 | known values (`LVec.ofBitVec`) |
| depending on `A`/`B` after `done` | they are free there (any known values), and `C` must still hold the product |
| a clock that never ticks, or is gated, tied, read as data | `ClockedBy`, and the loader's own guard (`ClockGuard2.lean`) |
| an environment that cannot exist | the rely is about the stimulus. A single transaction held to the horizon always satisfies it; later transactions need only wait for `done` |
| state carried across a reset | claims start at EVERY release |


### Evidence (in `Spec.lean`, proved)

- A 2×2 product with a negative entry, `[[-1,2],[3,4]]·[[5,6],[7,0]] = [[9,-6],[43,18]]`, packed at
  `W = 4`, `AccW = 8`.
- Wrap at 8 and at 6 bits.
- The off-points `(1,1,1)`, `(2,3,5)`, `(3,4,8)` and the scoring point `(4,8,32)` are in range.
- The port names are distinct.

### Open points (11/04)

- The `TxTask` reduction theorem was to come in `SvGolf/Seq.lean` (it did: `TxTask.satisfiedAt_of_phases`, and
  under v2 `TxTask.satisfiedAtV2_of_phases` in `SvGolf/SeqV2.lean`): the statement from one-cycle lemmas plus a
  phase/latency invariant. It consumes the closed-form cycle lemmas.
- `ClockedBy` forbids a clock copy, so flops inside child instances are not admitted (flat designs
  only, for now).
- Parameter range (C10, added 11/04): `N·N·W < 2^31 ∧ N·N·AccW < 2^31` keeps every width and index
  expression in the 32-bit `int` range, where a real elaboration and ls-sv's unbounded constant tier
  agree. Above it, a design's ports and part-select bases wrap in every simulator but not in the model.
- The latency count. By the contract's reading (CONTRACT.md, point 4), the reference
  `reference/matmul_g1.sv` shows `done` exactly `N` snapshots after the start edge (MEASURED in
  iverilog at five points, README.md "The reference"). An earlier plan's `lat N = N + 1` is a valid bound
  but not the tight one, and the score takes the declared `n` (5 rather than 4 at the scoring
  point). The proof declares `lat = N`. The text needs no change either way.
- `Spec.lean`'s header read "DRAFT of TRUSTED text, for review". The text was frozen, so the stale word
  stayed until a version bump (`SvGolf/TaskSeq.lean`'s tx/stream half lost its banners on 2026-11-08).

### The oracle (`oracle.py`): what is reviewed with the spec

The clocked post-synthesis check has two binding comparisons: (i) the netlist against ls-sv,
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

Questions for the review (11/04; answered since):
- The post-synthesis budget in `task.json` (8 seeds × 24 transactions since 2026-11-07, F5; 3 seeds
  before; one reset cycle, at `(2, 4, 8)` and `(4, 8, 32)`) was a proposal; the references' runs measure it
  (828 and 1257 cycles at the two points, 2026-11-08).
- The `postsynth` keys `points`, `seeds`, `reset_cycles`, `txns`, and the top-level `clock`, `reset`
  and `protocol`, were this package's proposal for the `tx-family` kind; `check/postsynth.py` reads them
  as named here.
