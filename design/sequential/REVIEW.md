# `ClockedBy` and `SeqTask`: review of the DRAFT trusted text

The file under review is [../../SvGolf/TaskSeq.lean](../../SvGolf/TaskSeq.lean), its first two
sections, a DRAFT of trusted text. (The handshake, `TxTask` and `StreamTask` there are reviewed with
their tasks: [../../tasks/matmul/REVIEW.md](../../tasks/matmul/REVIEW.md),
[../../tasks/sorter/REVIEW.md](../../tasks/sorter/REVIEW.md).)
- **Why a separate module:** it is separate from `SvGolf/Task.lean` so that the draft changes neither
  that file nor what depends on it: every task statement, the whole `tasks` library, and every
  record's trusted-file hashes.
- **At the freeze (`txtask-v1`)** it is merged into `Task.lean` unchanged, or kept separate (your
  call; the lead approved this placement).

## `ClockedBy` (replaces `Unclocked` for a clocked design)

`ClockedBy k rst d` holds when:
- `k` is an input port of `d`;
- every edge-phase process (the processes ls-sv runs at the clock edge) is clocked by `k`;
- an edge process with an asynchronous reset uses the port `rst`;
- no process reads `k` as data.

Under it, ls-sv's reading of a stimulus entry as "one rising edge of the clock" is exact. That
excludes the undriven, tied, derived, gated and data-read clock, the silent wrongness WP-S0
measured.
- It is the statement-side twin of the loader's guard (`LeanModels/Sv/ClockGuard2.lean`, WP-Q0).
- The guard refuses the same designs earlier; the statement does not depend on it.
- The names a process reads are computed by `exprNames`/`stmtNames` in the file itself (about 60
  lines). The trusted text therefore imports nothing beyond `SvGolf.Task` and the ls-sv semantics.

**Known restriction.** `ClockedBy` forbids even the plain copy `assign t = clk`, which is what a
flattened child instance's clock connection becomes. So flops inside child instances are not
admitted; the loader's guard accepts such copies. Widening `ClockedBy` to the guard's copy-set rule
is a later change.

## `SeqTask` (the cycle-exact Moore form; you approved the shape on 10/30)

The text is that of `design/sequential/README.md` §2: a state machine, Moore outputs read after the
edge, a claim from every reset, `ClockedBy` instead of `Unclocked`.
- The study's `CombTask.toSeq` and `toSeq_satisfiedAt_iff` (in `SvGolf/Seq.lean`, proved) show that a
  combinational task is its one-point-state case.
- No public task uses `SeqTask`: being cycle-exact, it leaves no design freedom.
- It is kept for warm-up fixtures, and the counter is Gate 2's fixture. The counter's statement is
  proved for every `N` (`design/sequential/CounterCycle.lean`), and the design `cnt.sv` loads to is
  proved to be the hand-built family at every `N ≥ 1` (`CounterInst.lean`). Its claim runs on
  concrete traces in `CounterTraces.lean`.

## Decisions

- Placement: a separate module now, moved at the freeze. Our lean: yes.
- The `ClockedBy` restriction above: accept it for the first tasks. Our lean: yes.
- Everything else is as approved on 10/30 and in `CONTRACT.md` (C1: synchronous active-high reset).
