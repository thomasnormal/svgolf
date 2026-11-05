# The sequential contract: decision log (Gate 0 of `svgolf/PLAN4.md`)

The decisions C1 to C9 of `PLAN4.md` §5 (prep `82729dd0`), with where each one lives in the draft
trusted text and how it is formalized.
- **Status: FROZEN 11/03 as `txtask-v1`.** Asked whether to freeze the drafted defaults or review
  first, the maintainers answered: "Don't worry. You choose the order, just keep following the plan." So every
  item below stands as the lead's default, apart from the items marked "ruled". This is a delegation,
  not a review: the maintainers may still rule on any item, and a change after the freeze is a version bump
  (`txtask-v2`), never an edit of v1.
- **Freeze:** the commit tagged `txtask-v1`. From it on, the checker and the proofs may depend on the
  text.
- **[M]** marks an item the maintainers rule on (`PLAN4.md` §5); its default is in force until then.

Files:
- [`SvGolf/TaskSeq.lean`](../../SvGolf/TaskSeq.lean): `ClockedBy`, `SeqTask`, the handshake,
  `TxTask`, `StreamTask`.
- [`tasks/matmul/Spec.lean`](../../tasks/matmul/Spec.lean), C6.
- [`tasks/sorter/Spec.lean`](../../tasks/sorter/Spec.lean), C8.
- [`SvGolf/Seq.lean`](../../SvGolf/Seq.lean): the untrusted reduction lemmas.
- Executable traces for the counter fixture:
  [`design/sequential/CounterTraces.lean`](CounterTraces.lean).

Throughout:
- the stimulus entry `c` is cycle `c`'s inputs;
- the snapshot `c` is the state after cycle `c`'s clock edge and the settle that follows;
- so the design's reaction to an input sampled at the edge of cycle `c` is visible from snapshot `c`
  on.

| item | decision (default unless ruled) | formalized as |
|---|---|---|
| **C1** reset [M] | synchronous, active-high `rst`, held ≥ 1 cycle; while 1, nothing is claimed and `start` is ignored; claims begin the cycle after `rst` falls; before the first reset nothing is claimed | `Released rst stim c1 h`: the entry `c1 − 1` asserts `rst`, every entry in `[c1, h)` deasserts it; every claim is `∀ c1 h, Released … → Rely … → Guar …` |
| **C2** start and idle [M] | `Idle(trace, c)`: true from release until the next accepted start, and again from the first cycle in which `done` = 1 until the next start; `start` a one-cycle pulse raised only when `Idle`; inputs known, held from the start cycle through the cycle in which `done` first rises; a start on a cycle where `done` = 1 is accepted (back-to-back); inputs while not `Idle` are ignored by the claim | `TxTask.Idle`: every start `s < c` has a snapshot `c'` in `[s, c)` showing `done` = 1, so a start at the entry right after the snapshot that shows `done` is idle (back-to-back). `TxTask.Rely`: `start` known; `start = 1 → Idle`; the operands of a start held at every later entry before the first `done` |
| **C3** latency [M] | the player supplies `lat : P → Nat`, `lat p ≥ 1`; `done` first rises at a cycle ≤ `lat p` after the edge that samples `start`; early completion and data-dependent latency are legal; the checker pins `lat p₀ = n` and scores `n` | `1 ≤ lat` is a conjunct of `SatisfiedAt`; `Guar`: for a start `s`, some snapshot `c ∈ [s, s + lat]` shows `done` = 1 (the snapshot of the start entry is "0 cycles after the edge that samples start"); the goal is `Statement design.sem lat ∧ lat p₀ = n` |
| **C4** done and hold [M] | `done` a level; once high it stays high, with the payload known and equal, until the next accepted start or reset; known in every cycle after release | `Guar`: `done` known at every cycle in `[c1, h)`; for every cycle from the first `done` after `s` until the next start, `done` = 1 and the payload equals `result x` (a reset ends the horizon: `Released` needs `rst` = 0 up to `h`) |
| **C5** knownness [M] | payload cared about only while `done` = 1; nothing before the first reset | the payload appears only in the hold clause of `Guar` |
| **C6** matmul [M] (arithmetic ruled) | `N, W, AccW ≥ 1`; signed `W`-bit inputs, products sign-extended, accumulation mod `2^AccW` (ruled 11/03); ports `clk, rst, start, A[N·N·W], B[N·N·W], done, C[N·N·AccW]`, flat row-major, entry `(i, k)` at `(i·N + k)·W`, LSB first; no banlist (ruled 11/03); scoring point `(4, 8, 32)` | `tasks/matmul/Spec.lean`: `task : TxTask (Nat × Nat × Nat)`, `product` (an `Int` sum, then `BitVec.ofInt AccW`), the examples (a 2×2 product with a negative entry, wrap at 8 and 6 bits, the off-points `(1,1,1)`, `(2,3,5)`, `(3,4,8)`, `(4,8,32)` in range) |
| **C7** scoring (ruled 11/03) | the cycle count `n` is part of the proof; time = `n` × the shortest clock period the design allows. Since sky130 became the ranked metric (decided 11/03), area is sky130 A0′ µm² including the flops (`dfxtp_1`), and the period is the longest register-to-register path in ps from the pinned liberty, which includes the flop's own clock-to-Q and setup, so the ad hoc per-cycle overhead is gone; Pareto frontier of (area, time), ties to the earlier record; one submission, one latency | checker side (Gate 2); nothing in the trusted Lean text |
| **C8** sorter's `StreamTask` [M] | ports `clk, rst, start, in_valid, in_data[W], out_valid, out_data[W]`; after an accepted start, `in_valid` = 1 for exactly `N` consecutive cycles beginning the cycle after start, no gaps; unsigned values; exactly `N` output cycles, not necessarily consecutive, whose values in order are the insertion sort of the inputs, the last ≤ `lat` after start; no backpressure; `out_valid` known after reset, `out_data` cared about only when valid | `StreamTask` (`Rely`, `Guar`, `Idle` = every earlier start's `N` outputs emitted), `tasks/sorter/Spec.lean` (`sortAsc`) |
| **C10** parameter range [M] (added 11/04, flagged by A) | every width and index expression a natural design writes stays below `2^31`, where real 32-bit `int` elaboration and ls-sv's unbounded constant tier agree (`PDesign.int32Agrees`, checked by the loader only at the defaults and the probe points): matmul `N·N·W < 2^31 ∧ N·N·AccW < 2^31`, sorter `N·W < 2^31` (Task v2 decision 1, the `clmul` precedent) | a conjunct of each task's `inRange` |
| **C9** form [M] | v1 now, over run2; the maps to the D11 contract and to Task v2 come as untrusted theorems later | `⊨₂` over `run2`, inputs read from the stimulus, as `CombTask` |

**Already ruled:** matmul overflow wraps; no banlist for matmul; the clock is clocking, not observed
(decided 11/03).

## Interpretation points, flagged for the review

Each is a place where the formal text had to choose between readings of the item.
1. **C1: no claim in the reset cycles themselves.** The claim starts at the release `c1`. The
   snapshot of the last reset entry (`c1 − 1`) is not constrained, even though the design has just
   been reset there.
   - This is for `TxTask` and `StreamTask`.
   - The warm-up form `SeqTask` keeps the shape approved on 10/30: a claim from every reset ENTRY,
     whose snapshot shows the reset state. This is how the counter fixture is stated.
2. **C2: idleness is observed.** The rely reads the design's own `done` (a hypothesis about the
   trace). It is stated up to a horizon `h`, so a protocol violation after `h` cannot void a claim
   before it, and a design that never raises `done` still fails: its first transaction is always
   rely-compliant.
3. **C2: "inputs while not Idle are ignored".** This is read as: outside the hold interval of a
   transaction the operands are free (any known values), and the claim does not depend on them.
   `start` is never raised while not `Idle` (rely).
4. **C3: "`≤ lat` cycles after the edge".** This is read as: snapshot index `≤ s + lat`, where
   snapshot `s` is the one right after the edge that samples `start`. A design whose `done` is
   visible in snapshot `s` itself has latency 0 by this count. `lat ≥ 1` is still required (C3).
5. **C4 and back-to-back.** When a start comes right after `done`, `done` may drop at that start's
   edge. If a design keeps `done` = 1 in the start's own snapshot, that counts as the NEW
   transaction finishing at once, so the payload there must already be the new result.
6. **C8: `out_valid` = 0 before the first start.** C8 says only "known after reset". The draft
   also requires 0 before the first start, so a design cannot emit spurious outputs that are not
   part of any transaction. Between transactions, the next start's segment requires exactly `N`
   valid cycles.
7. **C8: idleness for a stream.** C2's `Idle` reads `done`, which the sorter does not have. The
   draft reads "finished" as "the `N` outputs of every earlier start have been emitted".

## The counter fixture's executable traces (Gate 0 step 3)

[`CounterTraces.lean`](CounterTraces.lean) runs `run2` on the counter (`cnt.sv`, the `SeqTask`
fixture) and checks the `SeqTask` claim on the resulting finite traces with a Boolean checker
(`#guard`):
- a LEGAL trace (reset, enable patterns, a mid-run reset, a wrap at `N = 2`) passes;
- traces of three wrong designs FAIL: enable ignored, early wrap, reset not honoured;
- a stimulus that never asserts reset makes the claim VACUOUS (nothing to check), even for a wrong
  design. This is C1's "nothing before the first reset".

The Boolean checker is an executable reading of the claim, not a proved equivalent of it (labelled
in the file). The trusted statement is the `Prop`.

The fixture's design is the loaded `cnt.sv`. `CounterInst.lean` proves that it is the hand-built
family `cntD N` at every `N ≥ 1`, so `cnt_statement` holds of the loaded family
(`cnt_statement_sem`). It does so with one side condition, `1 ≤ w` on the register width in
`cnt_static`: the `+ 1'b1` operand is widened to `w` (the one node `fitExpr2` inserts), and that
lowering is the counter's only for `w ≥ 1`. The task's range `1 ≤ N` covers it.
