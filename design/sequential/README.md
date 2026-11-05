# Sequential and asynchronous designs in svGolf: a design study (WP-S0, 10/30)

> **Status 10/30:** S0 landed as the loader refusal `Clock:source` / `Clock:reset` / `Clock:multiple` / `Clock:data-read` (`LeanModels/Sv/ClockGuard2.lean`, a check beside `name.sem`; fixtures `Examples/system-verilog/sem2/clk_*`, differential rows pinned on Xcelium). `ClockedBy` for the `SeqTask` statement stays to be written; the loader now guarantees its premise for every design `load_design_sv2` accepts.

Direction (decided 10/30): "eventually we want to do full CPUs, so start thinking about
non-combinatorics, asynchronous stuff". This note lays the road: what ls-sv does for clocked designs
today (tried for real), the statement a sequential task should make, the proof method, the ls-sv
features in order, the cost model and the checker, the ladder to a CPU, and a seven-day spike.
Nothing in the trusted base was edited; the sketches in this directory compile and contain no `sorry`.

Files: this note; `experiments.md` (every measurement quoted below, with the messages);
`SeqTask.lean` (the statement, the degenerate-case theorem, the reduction theorem, compiled);
`CounterCycle.lean` + `cnt.sv` (the N-bit counter at symbolic `N`: closed-form one-cycle lemma and the full
statement `cntTask.Statement cntD`, PROVED for every `N >= 1`); `compile.sh` (how the sketches are
compiled, in a scratch copy).

---

## 0. The first page

### 0.1 What ls-sv does for clocked designs today (all measured, `experiments.md` E1 to E5)

* **Accepted and right**: `always_ff @(posedge clk)` with non-blocking assignments, synchronous reset
  by `if`, enable, `case` FSMs, shift registers, pipelines, unpacked-array memories, async active-low
  reset (`@(posedge clk or negedge rst_n)`, the pinned `pin3` ledger). The cycle is: apply the
  entry's inputs, settle, reset-event phase, run EVERY edge process once (σ order), commit the
  non-blocking updates, settle, snapshot. `N`-parametric designs instantiate for every `N`.
  Races between blocking assignments are visible as σ-dependence.
* **Wrong in one place, silently**: the clock's VALUE is never read. An undriven, tied-low, gated or
  internal clock still ticks every cycle in ls-sv and never in a simulator (`dead_clk`:
  `always_ff @(posedge clk) y <= a & b` with `clk` undriven gives `y = a & b` per cycle; a gated clock
  with enable 0 still counts). `Unclocked` in `CombTask` is what blocks this today; the 4-state stage
  catches the undriven wire but NOT a clock tied to a constant (Yosys drops the flip-flop, `y = 1'hx`,
  0 GE).
* **Loud (good)**: `negedge`, a clock that is not a plain identifier, `always_latch`, `always @*`,
  `initial`, delays, declaration initializers on written variables, two processes writing one bit,
  non-blocking assignment in `always_comb`.
* **Proved so far**: only the M0 tier has sequential theorems (`counter_refines`, `toggle_refines_model`,
  `swap_nba_swaps`, `race_blk` at fixed width 8, by a closed-form one-cycle lemma, an induction over the
  stimulus and list mathematics). In `Design2` (the tier with `N`-parametric designs) there is NO
  sequential proof layer: the whole settle theorem (`Comb2*`, `sv_structure`, `sv_equations`) is for designs
  without edge processes; only `Runs2.forall_of_step`, `Terminates2.of_invariant` and the cycle
  decomposition (`snapshot_step`) are generic.
* **Checker today**: a flip-flop in the netlist stops `score.py` ("cells the GE table does not price"),
  and `postsynth` has one fresh one-cycle run per vector: no clock, no reset, no trace.

### 0.2 Recommended statement shape (`SeqTask`, `SeqTask.lean`)

A Lean state machine `(State N, init, step, obs)` plus a protocol; the claim is "from every reset, for
every input trace, the output trace is the machine's":

* **Protocol.** One stimulus entry is one clock period with exactly one rising edge of the task's clock
  INPUT PORT. Inputs are stable through the period (set after the previous edge, before this one). The
  snapshot is taken after the edge and the settle that follows, with the entry's inputs still applied
  (this is what ls-sv, the M0 `⊑@clk` and the Xcelium testbench's negedge sampling all already do).
  Reset is an input of the protocol (a port and a level). The machine's `step` is only used on entries
  that do not assert reset; a reset entry restarts the machine at `init`. Nothing is claimed before the
  first reset (registers are x there: the 4-state start-up is part of the model), and the claim covers
  every later reset too.
* **Observation.** Outputs are known 4-state vectors equal to `obs state input`. A sequential task's `obs`
  must ignore the input (Moore, registered outputs: a reviewer-checked predicate `Moore`); the input
  argument exists so that the combinational task is the one-point-state case.
* **Design side** (replaces `Unclocked`): exact interface (clock, reset, data inputs, outputs, order and
  widths), `ClockedBy` (every edge process is clocked by the clock port; the clock is an input port;
  NOTHING else mentions it; an async-reset block uses the reset port), `Terminates2`, and `Follows`.
  This closes the undriven, tied, derived and gated clock for good WITHOUT changing ls-sv's
  one-edge-per-entry model: under the discipline that model IS the protocol.
* **Combinational tasks are the degenerate case**: `CombTask.toSeq`, `toSeq_satisfiedAt_iff` (proved).
* **Reduction theorem** (proved): `SeqTask.satisfiedAt_of_cycle` turns the statement into an invariant on
  snapshots, a simulation relation `R` to the spec state, and two one-cycle lemmas (reset cycle, ordinary
  cycle) about `cycleStep2`. This is the shape a `sv_seq` tactic must produce (section 3).
* Later statement classes, same skeleton: relational spec (forward simulation, for variable-latency
  units), transaction tasks `TxTask` (request/response with a latency bound, the gallery's `⊨tx`), and
  environment-closed tasks (memory, bus) as causal hypotheses on the stimulus.

### 0.3 ls-sv feature order (efforts in agent-days, one agent, shared Lean slot; section 4)

| # | feature | ids | days |
|---|---|---|---|
| S0 | clock discipline as a loader refusal (gated, derived, tied, internal, clock-as-data become loud) + `ClockedBy` | `sg-unclocked`, charter single-clock gap | 1.5 |
| S1 | register-transfer theory of `cycleStep2` for one clock: `always_ff`, NBA-only bodies, sync reset, enable; `Terminates2`; then the `sv_seq` tactic | `SEQ`, `gu-unknown-names` | 6 to 8, +6 to 8 |
| S2 | async active-low reset in the same theory (already modelled in `Sem2`) | `pr-event-list` | 3 |
| S3 | 4-state start-up and `initial`: a POLICY (no initial values on state; reset only), not a feature | `pr-init-var`, `ld-initial-syscall` | 1 |
| S4 | two-phase cycle: `negedge`, level-sensitive latches, `always_latch` | `pr-edge-other`, `pr-always-latch`, `LATCH4` | 8 to 10 |
| S5 | clock edges as events (edge detection from the clock signal): clock gating, derived clocks | `pr-clock-wide`, `le-instance-clock` | 8 to 12 |
| S6 | several clocks: tick sets and interleavings | `pr-event-list` | 6 to 8 |
| S7 | CDC: a sound sampling model (per-bit old-or-new across domains) and the Gray-code proof library | new | 18 to 20 |
| S8 | scheduler (delays, events, regions): NOT needed by any synthesizable task | `R1` | only for R1 adequacy |

### 0.4 Spike plan (7 days, section 7)

Goal: the N-bit counter with enable and synchronous reset as a real task, proved for ALL `N` and ALL
cycles, accepted by `check.py` end to end. Day 1 statement approval, slot-light work (clocked
postsynth harness in Python and C++ against Verilator; the counter reference and oracle); day 2 S0 and the
differential rows with Xcelium pins; days 3 and 4 the `Seq2` library and the hand proof; day 5 checker
(flip-flop prices, `dfflegalize`, clocked postsynth, `task.json` kind); day 6 `sv_seq` v0 on the counter if
WP-G has landed; day 7 dry run by an independent agent. Dependencies and what runs beside WP-F/P/G/B2 are in
section 7.

### 0.5 What this study already proved (so the estimates are not guesses)

Both files compile (`compile.sh`, 10/30, Lean slot, no `sorry`, no `native_decide`):

* `SeqTask.lean`: the degenerate-case theorems (`toSeq_follows_iff`, `toSeq_satisfiedAt_iff`: `CombTask` is the
  one-point-state `SeqTask`) and the reduction theorem `SeqTask.satisfiedAt_of_cycle`, about 70 lines of
  proof over `Runs2.snapshot_step`/`forall_of_step`.
* `CounterCycle.lean`: for the hand-built instantiation `cntD N` of `cnt.sv` (its agreement with
  `load_sv`'s real `cnt.sem N` is checked by `#guard` at `N = 1, 2, 3, 4, 8, 16, 32`),
  **`cnt_statement : cntTask.Statement cntD`, i.e. for EVERY `N >= 1`, every schedule, every stimulus and every
  cycle, from every reset `q` is the spec counter** (`#print axioms`: `propext, Classical.choice,
  Quot.sound`). The engine is ONE closed-form lemma, `cnt_cycle`, for `cycleStep2 (cntD N)` on the 4-signal
  state at symbolic `N` (about 25 lines: unfold, `simp` over `edgePass2`/`execStmt2`/`evalExpr2`, three
  branches), cross-fuel determinism to drop the fuel, and the register algebra (reset forgets an x register,
  enable increments a known one) on the `LVec.ofBitVec` calculus of `Known2` (`add_ofBitVec`,
  `resizeU_ofBitVec`, `condTrue_ofBitVec`). Whole file: 293 lines, one compile; the proof work was an
  afternoon, most of it waiting for the Lean slot. What is NOT proved: `cntD N = cnt.sem N` for symbolic `N`
  (the `#guard`s are concrete), which is the instantiation gap `Gen2`-style lemmas or the `sv_seq` front end
  must close, exactly as WP-G needs for `always_comb`.

### 0.6 Decisions the maintainers must take (details in section 8)

1. Approve the `SeqTask` shape (Moore after the edge, reset-first claim, `ClockedBy` instead of
   edge-detected semantics in v1).
2. Initial values policy: none on state; reset only (and `dfflegalize ... x` as the mechanical backstop).
3. Flip-flop prices in `ge.json` and the pinned `dfflegalize` line; the metric for multi-cycle tasks
   (area-delay product or a three-axis Pareto).
4. When to build edge-detected semantics (S5) and the CDC sampling model (S7); recommended: not before a
   RISC core runs on one clock.
5. First CPU ISA: purpose-made 16-bit first, then RV32I through `LeanModels.Rv`.
6. Which sequential task is the first public one (the counter is the spike, not necessarily the showcase).

---

## 1. What exists

### 1.1 The semantics (`LeanModels/Sv/Sem2.lean`)

`cycleStep2 d σ fuel inputs st k` is, in order: `applyInputs2` (declared inputs only; an unbound input
holds); `combSettle2` (σ-ordered passes to a fixpoint); the **reset-event phase** (`alwaysFFR`
processes whose reset made a negedge between the previous snapshot and the settled inputs run their
WHOLE body, commit, settle); the **edge phase** (`edgeIndices`: every `alwaysFF`/`alwaysPlain`/`alwaysFFR`
process, filtered by process KIND only, run once in σ order; blocking writes hit the state, non-blocking
writes queue); `commitNba2` in issue order; `combSettle2`. The snapshot is the final state. `run2` starts
from `initState2` (declaration initializers, else all x). The clock name in `alwaysFF clock body` is
never read at run time. `Process2.isCombPhase` sends `unsupported` processes to the comb phase so that
they are loud.

`Spec2.lean` gives `Runs2` (some fuel completes), `⊨₂` (all schedules, all stimuli, all completed
runs), `Terminates2`, and the generic cycle tools: `Runs2.snapshot_step` (snapshot `c` is an `.ok`
`cycleStep2` from the previous snapshot or `initState2`, at stimulus entry `c`), `Runs2.forall_of_step`
(a step-preserved invariant holds on every snapshot), `Terminates2.of_invariant`. `Mono2.lean`: fuel
monotonicity, `cycleStep2_det`, `Runs2.functional`, `Deterministic2` and the refutation of `raceD`
(blocking `x = 0; x = 1` in two `always_ff`: σ_src leaves 1, σ_rev leaves 0). `Hier2.lean`:
`clockGuardProc`, the instance-level clock-source rule (a flattened child flop must be clocked, through
bare connections, by an input port of the top) and the recorded "single-clock gap" for the top level.

### 1.2 Tried for real (`experiments.md`, E1 and E2)

A counter with enable and synchronous reset, a shift register and a two-stage pipeline: accepted by the
extractor and by `load_design_sv2`, `run2` correct under both schedules. Table of everything else
(refusals with their messages, the clock-value gap, async reset, latches, races): `experiments.md`
E2. Two facts that shape the statement:

* The post-edge snapshot of a combinational output that reads an input sees the NEW register and the
  HELD input: for `r <= x; assign y = r + x`, `y_c = r_{c+1} + x_c`. A Mealy output as a simulator's
  consumer would see it (before the next edge, with the next inputs) is not in any snapshot.
* Before the first reset the registers are x and stay x under arithmetic (`x + 1 = x`); `if (rst)` with
  `rst = x` takes the else branch.

### 1.3 What the examples prove, and by what means

M0 tier (`Design`, fixed width 8; `Examples/system-verilog/{counter,toggle,swap_nba,race_blk}`):
`counter_refines : counterDesign ⊑@clk[from rst] counterModel` (from any snapshot that sampled `rst`,
whatever abstract state is posited before, the `count` column follows `if rst then 0 else s + 1`),
`toggle_refines_model` (a two-input model), `swap_nba_swaps`, `race_blk_not_deterministic`. Means:
a closed-form one-cycle lemma for the exact state shape (`counter_cycleStep`, threshold form), an induction
over the stimulus (`counter_runFrom`), cross-fuel determinism to pin any hypothesis trace to the canonical
one, then pure list mathematics. `⊑@clk[from rst]` is the ancestor of `Follows` below (same "from every
reset, whatever came before" shape). The R1 timed tier (`SvWorld`, `slotStep`, `runSlots`, `wakeEdges`;
Examples `clocked`, `negedge`, `delay`, `always`) is a resumable-process scheduler with Active/Inactive/NBA;
the adequacy lemma `cycleOf (runSlots ..) = run ..` is not proved, so it is a reference for later, not a
proof surface. In `Design2` there is no sequential `Examples` theorem; `alu_div` (the CV32E40P serial
divider, async reset + FSM) is ingested only. The differential corpus has 12 `cases2.json` rows with
`always_ff` (plus the pinned `pin3` in `Sem2`) and 6 M0 rows.

### 1.4 The undriven-clock exploit and why `Unclocked` blocks it

`logic clk; always_ff @(posedge clk) y <= a & b;` with `clk` undriven satisfies the combinational
statement (right `y` in every ls-sv snapshot) and scores 0 GE or fails in Yosys, because ls-sv runs the
edge phase whatever `clk` holds. `CombTask.SatisfiedAt` requires `Unclocked d` (no process with
`isEdgePhase`), so no design with any edge process is provable for a combinational task. Defence in depth
today: `fourstate` (undriven wire), `score` (unpriced flip-flop), `postsynth` (unknown constant). With
sequential tasks `Unclocked` must go, and `ClockedBy` (section 2.3) is what takes its place.

---

## 2. The statement

### 2.1 The sketch (`SeqTask.lean`, abridged)

```lean
structure SeqTask where
  inRange : Nat → Prop
  clk : Option String                     -- none: combinational task
  rst : Option (String × Bool)            -- (port, asserted level)
  inputs outputs : Nat → List Sig         -- data ports, in order
  State : Nat → Type
  init : (N : Nat) → State N
  step : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → State N
  obs  : (N : Nat) → State N → Vals ((inputs N).map Prod.snd) → Vals ((outputs N).map Prod.snd)

def SeqTask.Follows (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ c0 ps, t.StartOK N ps →                         -- first entry of ps asserts reset
      (∀ j p, ps[j]? = some p → ∃ e, stim[c0 + j]? = some e ∧ t.Drives N e p) →
      ∀ j a, (t.scan N (t.init N) ps)[j]? = some a → ∃ st, tr[c0 + j]? = some st ∧ t.ObsOK N st a

def SeqTask.SatisfiedAt N d := t.Interface N d ∧ (t.Disciplined d ∧ Terminates2 d) ∧ t.Follows N d
def SeqTask.Statement sem   := ∀ N, t.inRange N → t.SatisfiedAt N (sem N)
```

`Drives e (r, v)`: the reset port of `e` carries the level for `r` and every data input holds the known
value in `v` at its declared width (the `HoldAll` of the combinational statement); `scan` runs the machine
(a reset entry gives `init`, any other `step`); `ObsOK st (s, v)` is `HoldAll st outputs (obs s v)`, i.e.
the output ports hold exactly the known values. The hypothesis is about the STIMULUS, as in `CombTask`
(a snapshot-form hypothesis could be kept false by a design that drives its own inputs); `ps` is a
universally quantified list, so for every list of good inputs there is a stimulus (non-vacuity) and a
completed run (by `Terminates2`).

### 2.2 The design choices and the alternatives rejected

* **Moore, observed after the edge.** The snapshot is after the edge with the cycle's inputs still
  applied. A combinational output reading an input would be `g(regs_{c+1}, in_c)`, which is not what a
  synchronous consumer sees (it sees `g(regs_c, in_c)` before the edge). Rather than export the pre-edge
  state (a trace-type change, which the R1 `cycleOf` work is meant to make cheap later), v1 requires
  registered outputs (`Moore`). Every rung of the ladder up to the first core can be written with
  registered outputs and synchronous memories. The degenerate comb case needs `obs` to see the input,
  which is why the argument exists.
* **Outputs known, not merely equal.** `HoldAll` demands `LVec.ofBitVec` values, so an output that
  depends on an unreset register is x and fails: this is the "never-reset register" defence, and it
  allows data registers that are written before they are observed (masked by a known condition).
* **Reset in the protocol, claim from every reset.** The spec is silent before the first reset. `Follows`
  quantifies over every reset entry `c0`, so a mid-run reset must also restart the machine, and a design
  cannot "remember" anything across a reset that the spec forgets. Synchronous and asynchronous reset
  are the same at this granularity (inputs change between edges; the async design resets in the pre-edge
  reset phase and holds through the edge), so the STATEMENT does not pin the style; the cost does.
* **Deterministic machine now, relation later.** A function `step` over-constrains latency (a divider
  must take exactly `N + 2` cycles). The generalization is a spec relation `Step : State → Input → State → Prop`
  with a forward simulation (the design's snapshot sequence is a path of the relation), then `TxTask`:
  `request`/`response`/`latency`/`holdUntil` as in the CV32E40P gallery's `⊨tx`, proved by a simulation to
  the transaction automaton plus a ranking function for the latency bound. Both reuse `Follows`' skeleton.
* **Why not pin the clock waveform in the statement** (alternating 0,1 entries, edge detected from the
  clock signal): that is the right model for several clocks, negedge and gating (S5/S6), and it doubles the
  trace and changes the snapshot meaning. For one clock the discipline is equivalent and costs nothing.

### 2.3 Defence against the exploits (what blocks what)

| exploit | blocked by |
|---|---|
| undriven / internal clock | `ClockedBy`: the clock must be an input port (`Interface` fixes it); also `fourstate` |
| tied clock (0 or 1; Yosys drops the flip-flop) | `ClockedBy` (a tied clock is not an input port) and the post-synthesis netlist check |
| gated or derived clock | `ClockedBy` (every edge process is on the clock port; no process may mention it as data) |
| clock used as data (`assign y = clk ^ a`) | `ClockedBy`: `mentionsData clk = false` for every process |
| async reset driven by internal logic | `ClockedBy`: an `alwaysFFR` must name the task's reset port |
| never-reset register feeding an output | known outputs after reset (x fails `HoldAll`); postsynth randomizes initial register contents (section 5) |
| outputs depending on simulation order | `⊨₂` quantifies every schedule, so a racy design must equal the spec under all of them; NBA-only bodies are order-independent |
| blocking/non-blocking race | same; plus the one-driver rule (`driversOk`) refuses two processes writing one bit |
| initial values (a free reset) | ls-sv refuses the initialized variable and `initial`; the pinned `dfflegalize ... x` makes an initialized flip-flop a scoring ERROR (measured: "initialized D flip-flops are not supported"); as pinned today the init value silently vanishes from the netlist |
| latch as hidden state | `always_latch`/`@*` are loud; an incomplete `always_comb` is accepted by ls-sv but refused by Yosys `proc` (`fourstate` rule (e)) |
| x-pessimism differences (`if (x)`) | stimulus hypothesis is known values; the design-side x cases are decided by ls-sv's pinned rules |

### 2.4 `CombTask` as the degenerate case (proved in `SeqTask.lean`)

`CombTask.toSeq c` has `clk = rst = none`, `State = Unit`, `obs N () v = c.fn N v`. Then
`toSeq_interface` (the ports are the task's), `toSeq_follows_iff` (`Follows` is exactly `Computes`: take `ps`
of length one for the forward direction, read the snapshot of each driven entry for the other) and
`toSeq_satisfiedAt_iff` (the whole statement, `Disciplined` for a clock-less task being `Unclocked`). So
the new class does not move the trusted statement of `add`, `mul` or the (former) 16-bit divider; whether `CombTask` stays as
a separate structure or is defined by `toSeq` is a cosmetic choice for the maintainers.

---

## 3. The proof method

### 3.1 The theorem shape the player proves

Refinement by an invariant, the standard simulation proof. For a design family and its `SeqTask`:

1. an invariant `Inv` on snapshots (shape: names and widths; for the tactics also "the combinational
   equations hold");
2. a relation `R : snapshot → State N → Prop` (for the counter, `q = ofBitVec s`);
3. the reset lemma: any successful cycle whose entry asserts reset gives `R st init` and the right
   observation, from ANY invariant state (this is "reset forgets history, x included");
4. the step lemma: `Inv prev`, `R prev s`, a successful cycle with a non-reset entry `v` give
   `R st (step s v)` and the observation.

`SeqTask.satisfiedAt_of_cycle` (proved from `Runs2.snapshot_step` and `Runs2.forall_of_step`, about 70 lines
of induction on the input list) turns 1 to 4 plus `Interface`, `Disciplined`, `Terminates2` into
`SatisfiedAt`. Fuel, schedules, the trace and the stimulus list never appear in the player's lemmas. For
a parametric design the lemmas quantify over `N` and the induction over cycles is the library's; the
player's only induction is over `N` inside the arithmetic (the carry chain), exactly as for `add`.

### 3.2 What the tactics generate: the register-transfer view (`sv_seq`)

The combinational tactics read the design as sites (target access, read accesses, affine data), a
generate tree, ranks that make the read-to-write relation acyclic, and pointwise Boolean equations with
knownness (`CombView`, `CombEq`, `CombKnown`: `PDesign.summary` is sound against `instantiate2`). The
sequential generalization keeps all of it and cuts at the registers:

* **Registers are cut points.** A window written by an edge process is a SOURCE for the combinational
  rank (the comb part, with the edge processes deleted, is an ordinary `CombDesign` whose undriven nets
  include the registers; `Runs2.comb_held` already says undriven nets hold), and a SINK of one
  next-state site. The rank obligation is unchanged and only about comb sites. The only new structural
  obligations: edge bodies are NBA-only (no blocking writes, so the σ order of edge processes is
  irrelevant and the NBA queue is just parallel assignments) and register windows are disjoint (the
  one-driver rule, already enforced by `driversOk`).
* **Next-state equations.** A symbolic executor `Stmt2.nbaExec`, the twin of `Stmt2.symExec` (which
  refuses `nbaAssign` today), turns `if (rst) q <= 0; else if (en) q <= q + 1;` into one equation per
  register window, `q' = if rst then 0 else if en then q + 1 else q`, with reads always of the PRE-edge
  frame (NBA semantics; no substitution of earlier writes). This is the same `if`/`case` equation shape as
  WP-G's `always_comb` equations, so the two should be designed once, with a mode flag (blocking-comb
  versus NBA-register).
* **Frames.** A cycle relates two settled frames: `pre` solves the comb equations for (registers of the
  previous snapshot, this cycle's inputs); the registers of the new snapshot are the next-state equations
  evaluated on `pre`; `post` solves the same comb equations for (new registers, same inputs). `sv_seq`
  emits `hpre`, `hnext`, `hpost` (and knownness for both frames: known registers and known inputs give
  known everything; with reset asserted the next-state tree selects the reset constant whatever the old
  registers were, so the reset lemma's "forgets x" is a `simp` on the guard) as the plain Lean equations
  the player consumes with `omega` or the arithmetic library. The generic theorems behind it:
  `Runs2.seq_snapshot` (the analog of `Runs2.comb_snapshot`: every snapshot has such a `pre`) and
  `Terminates2.of_acyclic_seq`. Written once, about 1500 to 2500 lines, reusing the comb settle theorem.
* **Parametric designs.** Registers inside `generate` (`q[i] <= q[i-1]`), arrays of registers and
  parametric depth are sites in the generate tree like any other; invariants are over `N`. A pipeline of
  depth `D` has the last `D` inputs as spec state, and the relation is a statement per stage.
* **Pipelines and CPUs.** The relation becomes a simulation relation per stage, with an abstraction
  function from the registers to the architectural state defined at instruction boundaries; the statement
  is a retirement-stream refinement (section 6). Nothing in the cycle theory changes.

What the counter spike shows about scale: a per-design closed-form cycle lemma (unfold `cycleStep2`, `simp`
through the edge phase, split on the guards) is a 25-line job for one register and a two-level `if`, and it
needs the exact state shape; it does not scale to a comb part, `generate` loops or twenty registers, which is
why the cycle theory must be a library (`Seq2`) that the tactics instantiate rather than code written per
design.

The 7-day spike builds `Seq2` and the hand proof; `sv_seq` follows WP-G (the equation shape) and WP-P (the
proof API: shared summary, `sv_interface`, named obligations), and WP-B2 (word-level `+`, `==`, `<`) is on
the critical path of every natural counter-like design (the spike uses a gate-level incrementer, the
existing `ripple_row` lemma, so it does not wait).

---

## 4. What ls-sv must add, in order

Units: agent-days, one agent, shared Lean slot (the unit of WP-E: the Wallace tape was about one day).
Estimates carry about 50% uncertainty. "Pins" are differential rows in `harness/sv/cases2.json` with the
Xcelium trace pinned in `xcelium_golden.json` (`xcelium_batch.py`, one run at a time).

### S0. Clock discipline as a refusal (1.5 days; first, because it removes the only silent wrongness)

* Decision: a top-level edge process is admitted only if its clock is an input port and nothing else
  mentions that port; otherwise a loud process (`Clock:discipline`), as `Hier2.clockGuardProc` already does
  for instances. A refusal-only change in the sense of round 6.
* Tests: negative designs (tied, gated, derived, internal, clock as data) loud; the positive examples
  unchanged (diff run). Pins: the gated-clock row with Xcelium (measured: counter `0 0 1 2 3 4`).
* Exploit if done wrong: a design accepted here and run once per cycle by ls-sv while hardware never
  ticks (the undriven-clock exploit, gated clock).

### S1. Register-transfer theory, one clock, `always_ff`, NBA, synchronous reset, enable (6 to 8 days, then `sv_seq` 6 to 8)

* Decision: the profile (edge bodies NBA-only; `if`/`case` guards; no blocking writes to state; no
  temporaries), registers as cut points, the two-frame cycle lemma, and `Deterministic2` for NBA-only
  designs (all schedules agree). Parametrize the theory by a predicate `fires : Process2 → Bool` (which
  edge processes tick in this step) from the start: `fires = all` now, an edge-detected set under S5/S6,
  so nothing is rebuilt.
* Tests: the E1 designs plus FSM, shift register, swap (`a <= b; b <= a`), memory with a dynamic write
  index, reset mid-run, reset x, enable x, simultaneous reset and enable; Xcelium pins for each. The
  M0 `counter/toggle/swap_nba/race_blk` theorems re-derived on the new layer.
* Exploit if done wrong: NBA committed early (or blocking semantics) lets a design compute what no
  simulator computes (swap, pipelines); an edge process reading the pre-edge frame wrongly would hide a
  one-cycle error in every pipeline.

### S2. Asynchronous active-low reset in the theory (3 days; semantics exist)

* `Sem2` already models `alwaysFFR` (the pre-edge reset-event phase runs the WHOLE body, pinned: pin3, 8
  cycles, Xcelium and Icarus). Work: the two-frame lemma with the reset-event phase in front; restrict the
  reset signal to the task's reset port (`ClockedBy`); add rows for reset asserted from the first entry,
  held, glitching (`1 -> x`), and released with data changing.
* Exploit if done wrong: a reset derived from internal logic (no event in a cycle model, a real reset in
  hardware); running only the reset branch at the event instead of the body (pinned against).

### S3. 4-state start-up and `initial` (1 day, a policy)

* Decision: registers start x (as now); no declaration initializers or `initial` on state; reset is the only
  initialization; the claim starts at a reset. `initial` for ROM contents is not needed (a `case` table or a
  constant array assigned by generate is synthesizable and already in the tier).
* Backstop: `dfflegalize -cell $_DFF_P_ x ...` makes an initialized flip-flop a scoring error (measured).
* Exploit if open: reset by initial value (ls-sv sees 0 at time zero, the written netlist drops the init).

### S4. Two-phase cycle: `negedge`, latches, `always_latch` (8 to 10 days)

* Decision: a cycle has a posedge phase and a negedge phase; negedge processes see the registers the
  posedge phase committed (half-cycle path); a level-sensitive latch is transparent during a named phase
  and holds otherwise (a register updated in the settle of that phase). `always_latch` and an incomplete
  `always_comb` are the same construct; LATCH4 gives it a 4-state rule (the latch is x until first
  transparent) BEFORE the model admits it. This changes `cycleStep2` and everything proved on it
  (Mono2, Comb2's cycle lemma): do S1 first, with `fires` abstract.
* Pins: negedge register capturing a posedge register (half-cycle path), latch open/closed sequences,
  latch fed by a late input, enable glitch, x enable. Price: `$_DLATCH_P_` in `ge.json`.
* Exploit if done wrong: a latch modelled as a wire (transparent always) hides state; negedge modelled as
  posedge removes half-cycle paths.

### S5. Clock edges as events: gating, derived clocks (8 to 12 days)

* Decision: edge detection from the clock SIGNAL between snapshots (`isNegedge`/`isPosedge` on `bit0`, as
  `resetIndices` already does for resets): `fires` becomes `edgeIndices d prev cur`. The stimulus then has
  two entries per period (clock low, clock high). A clock produced in the Active region (continuous
  assign) ticks in the same step with OLD data (pinned: `clk_a`), a clock produced by NBA logic ticks a
  delta cycle later with NEW data (pinned: `clk_n` captures the new value every time) and needs the R1
  slot loop, so it stays refused. Integrated clock gate = latch (S4) + AND.
* Exploit if done wrong: treating an NBA-derived clock like an assign-derived one gives wrong captures
  (measured above); gating glitches.

### S6. Several clocks (6 to 8 days on top of S5; the model, not the proofs, is the point)

* Decision: every clock is an input port; a step is a SET of clocks that rise together (empty allowed); the
  stimulus quantifies all interleavings; coincident edges sample OLD values (pinned: `clk2`). Fairness is
  not assumed for safety; liveness claims carry an explicit bound ("the other clock ticks within `r`
  steps").
* Exploit if done wrong: a model that lets one domain see another's NBA result in the same step.

### S7. Clock-domain crossing: a sound sampling model (18 to 20 days with the proof library; do last)

* Decision (needs the maintainers): with ideal sampling, a binary-pointer FIFO verifies, because an interleaving
  model captures either the old or the new multi-bit value atomically. Metastability proper is out of
  scope, but the minimal sound extra is: a flop that samples a signal driven by another domain captures,
  BIT BY BIT, the old or the new value whenever the source changed since this domain's last tick (an oracle
  choice, quantified like σ). Then binary pointers fail (a mixed value is garbage) and Gray pointers pass (one bit
  changes). A CDC proof obligation: the sampled bus changes in at most one bit per source tick (Gray code
  lemma), the two-flop synchronizer output is a register like any other, and the FIFO invariant holds for
  every interleaving and every old/new choice.
* There is nothing to pin on Xcelium (physical metastability is not simulated); the model is validated by
  proving the Gray FIFO and refuting the binary one, and by a random-skew gate-level simulation if wanted.
* Exploit if done wrong: any ideal-sampling CDC model accepts broken crossings and rejects nothing.

### S8. The scheduler (delays, `initial`, events, regions): only for R1 adequacy

No synthesizable task needs it. The only reasons to build it are the derived-clock delta cycles (kept
refused) and the formal bridge between the cycle model and the scheduler (`cycleOf (runSlots ..) = run ..`),
which is the R1 lane's work and not on this road.

---

## 5. Cost model and checker

### 5.1 Area with flip-flops

* **Flow.** Add to the pinned `svgolf.ys`, after `synth -flatten`, one line:
  `dfflegalize -cell $_DFF_P_ x -cell $_DFF_PN0_ x -cell $_DFF_PN1_ x`. Effects measured on `cnt` at `N = 16`:
  synchronous reset and enable stop being absorbed into the flip-flop cell (`$_SDFFE_PP0P_`) and become
  gates that ABC sees and pays for; ABC's output depends strongly on the flip-flop cell set (the
  async-reset counter went from 15 to 9 levels), which is why the line is part of the pinned script; and `x`
  (no init) turns an initialized flip-flop into a Yosys error. Keep `abc` WITHOUT `-dff` (retiming would
  change register structure under a proof about registers).
* **Prices.** Add `DFF_P`, `DFF_PN0`, `DFF_PN1` (and `DLATCH_P` with S4) to `ge.json` as a pinned
  convention. The existing weights (NOT 0.667, NAND 1, AND 1.333, XOR 2, MUX 2.333) are a fixed table, not
  a library; for flip-flops a defensible convention is the ratio of a public library's cell areas to its
  `nand2` (from memory, sky130_fd_sc_hd: `dfxtp_1` about 5.3, `dfrtp_1` about 6.7: verify against the
  library file before pinning), or round numbers 5 and 6.5. Price the set that `dfflegalize` leaves; reject
  everything else (`score.py` already refuses unpriced cells, which is the right default).
* **Depth.** `ltp -noff` prints the longest path from a flip-flop output or a port to a flip-flop input or a
  port (measured): the register-to-register path, i.e. the clock-period proxy, with no change to the script.
* **Latency.** A multi-cycle task adds cycles to the cost. Record the cycle count the statement allows or the
  task's reference run measures. Metric options: area-delay product `area_ge * depth * cycles`, or a
  three-axis Pareto (area, period, latency) as the leaderboard already keeps two axes.
* Score stability: Yosys optimizes across registers (constant bits are removed, equal registers merge), so
  scores are not a sum of per-register costs; that is fine, the proof is about the source and the score about
  the netlist, as for combinational tasks.

### 5.2 The post-synthesis check for a clocked design

Today: one fresh one-cycle run per vector. New mode (`postsynth.py --clocked`, `svgolf-eval --trace`):

1. **Traces, not vectors.** `T` seeded random traces of `L` cycles over the task's protocol: reset asserted
   first for 1 to 3 cycles and again at random points, data inputs random with corner bursts (all 0, all 1,
   walking, held values), enables toggling; the task contributes protocol constraints (`corners`) as now.
2. **Three simulators, one sample point.** ls-sv (`run2` on the whole trace, both schedules), the SCORED
   netlist (Verilator on the written netlist plus `simcells.v`, which has the `$_DFF_*` models) and the RTL
   (bug-report only), each driven with the protocol: set inputs, rising edge, evaluate, sample the outputs
   after the edge settles. This is the sample point of ls-sv's snapshot and of the Xcelium testbench
   (`gen_tb2.py` samples at the following negedge), so they are comparable cycle by cycle.
3. **Initial state.** Run the netlist (and the RTL) with randomized initial register contents
   (`--x-initial unique`, `+verilator+rand+reset+2`, several seeds) and require identical outputs after the
   first reset: a design that works only because registers start at 0 differs from itself. Outputs before
   the first reset are not compared (the statement is silent there).
4. **Fail closed** as now: x/z in ls-sv outputs after the first reset, σ_src ≠ σ_rev, run not completing,
   port differences, netlist not re-reading as the scored one, an unknown constant. Budget: ls-sv costs
   about 0.3 ms per combinational vector; a registered design costs about that per cycle, so 200 traces of
   64 cycles is about 4 seconds for a counter-size design and minutes for a core (to be measured in the
   spike).
5. For CPU tasks the traces are PROGRAMS: random instruction sequences generated against the ISA step
   function, memory images included, compared on the retirement stream as well as the pins.

### 5.3 Source gate, banlist, fourstate, leaderboard

* **Source gate**: unchanged (directives, attributes, pragmas, `unique`/`priority`); add refusals that ls-sv
  already makes loud so the gate says it earlier: `initial`, declaration initializers on registers,
  `always_latch`, delays, `negedge` (until S4).
* **Banlist**: per task as now (the serial multiplier bans `*`, the counter may ban `+` if the task wants a
  hand-built incrementer); the Yosys backstop is unchanged.
* **fourstate**: keep rules (a) to (e); rule (e) already refuses an undriven clock and an inferred latch. Add a
  rule that the clock and reset ports are not tied (they are inputs, so only a connection to a constant in an
  instance can tie them) and the LATCH4 rule before S4.
* **Checker stages**: `Unclocked` stops being a statement conjunct for tasks with a clock; stage `design`
  compiles `SeqTask.Statement`; `tasks/<name>/task.json` gains `kind: "seq-family"`, `clock`, `reset`
  (port, level), `protocol` (corners, trace lengths) and `metric`.
* **Leaderboard record**: add `ffs` (flip-flop count), `area_comb_ge`, `area_ff_ge`, `period` (= `depth`, named
  as such for clocked tasks), `cycles` (latency or throughput as the task defines), `metric` and its value,
  `clock_discipline` (the `ClockedBy` check passed), and the hash of the `dfflegalize` line (already inside
  `script_sha256`).

---

## 6. The ladder to a CPU

Statement shapes: **S** = `SeqTask` as above, **R** = relational spec / forward simulation, **T** =
`TxTask` (request/response with latency bound), **E** = environment-closed (the stimulus is a causal
function of past outputs, expressed as a hypothesis on `(stim, tr)`, with an existence lemma), **X** =
needs S7. Weeks are calendar weeks of the lane (lead plus agents, one Lean slot), assuming WP-F/P/G/B2
are done; each is the whole rung including task files, oracle, reference proof, baselines, dry run.

| rung | statement and new feature | weeks |
|---|---|---|
| 1. Counter, enable, sync reset | S; the whole foundation: S0, S1, checker clocked mode | 2 |
| 2. LFSR (`N` bits, fixed polynomial) | S; feedback XOR over slices; the proof is `BitVec` algebra per bit | 0.5 to 1 |
| 3. Shift register, serial-in parallel-out, load | S; registers inside `generate`, per-bit equations | 1 |
| 4. Serial multiplier (shift and add, `N` cycles) | T or R: start/done, latency bound `N + c`; invariant `acc + mcand * mplier = a * b` mod `2^N` | 2 to 3 |
| 5. Iterative divider (restoring) | T; invariant of the restoring recurrence (the `fdiv` certificate work is reusable) | 2 to 3 |
| 6. Synchronous FIFO (depth `2^k`) | R: spec is a queue with `push/pop/full/empty`; array-valued state, pointers mod `2D` | 2 to 3 |
| 7. UART transmitter, then receiver | R/T: serializer, baud divider, FSM; the receiver samples an asynchronous input through a 2-flop synchronizer (ideal sampling is fine for one clock domain and an input) | 2 (+2) |
| 8. Handshake: skid buffer, round-robin arbiter | R + E: valid/ready, data integrity, one-hot grant, bounded wait under fairness of requests | 2 to 3 |
| 9. Asynchronous FIFO, Gray pointers, two clocks | X: S5, S6, S7; invariant over both domains and the synchronizer contents; interleavings quantified | 8 to 10 |
| 10. Accumulator machine (8-bit accumulator, 16 instructions, external ROM) | S + E: retire stream equals the program's interpreter trace; instruction memory is an input with one-cycle latency (`imem_data_{c+1} = ROM[imem_addr_c]`) | 3 to 4 |
| 11. Small RISC core against an ISA step function | R + E (below); multi-cycle first, pipelined second | 4 (multi-cycle), +8 (pipelined) |
| 12. Memory interfaces and caches as environment assumptions | E: a bounded-latency memory environment with a store-to-load consistency model; a cache is a refinement between two designs | 4 to 8 |

About 17 weeks to rung 8, 27 to rung 9, a multi-cycle core after about 33, a pipelined one after about 41,
before caches: roughly ten months of lane time, perhaps six with several agents in parallel on
independent rungs. The error bars are large; the dominant terms are proof engineering per rung and
ls-sv gaps found by each (rung 7's receiver, rung 9's model).

**The ISA.** Recommended in two steps. (a) A purpose-made 16-bit, 8-register load/store ISA
("GolfRISC-16": `add sub and or xor slt shl shr addi lw sw beq bne jal`, fixed 16-bit encoding, about
40 lines of Lean for `step : ArchState → Instr → ArchState` with a decode function) for the first
multi-cycle core. Reasons: a 16-bit datapath keeps the netlist (a few thousand GE), the ls-sv simulation
speed (postsynth runs programs) and the proof arithmetic small, and the spec is short enough to be
reviewed as part of the trusted base. (b) Then RV32I (no CSR, no FENCE/ECALL, aligned word accesses
first), with `LeanModels.Rv.execInstr`/`isaStep` as the spec: the repository already has a 2000-line
RV32IMC + M-mode model in plain Lean over `BitVec 32`, validated against the sail-riscv emulator on 257
cases (`docs/rv-model.md`), and the CV32E40P spec-surface gallery (`docs/cv32e40p-spec-surface.md`) already
fixes the design laws this note follows (specs mention ports only; ISA facts are definitions; every safety
spec has a realizability twin). A purpose-made ISA is not validated against anything; RV32I is. The core
task is therefore best started on (a) and certified on (b).

**The refinement for a core.** Statement R + E: the core's outputs include a retirement port
(`retire_valid, retire_pc, retire_rd, retire_data, store_addr, store_data`); the claim is that the
subsequence of valid retirement events equals a prefix of the ISA execution of the memory image the
environment provides (stuttering refinement: filter the cycles where `retire_valid` is low), plus a
realizability twin (under an environment that answers within `L` cycles, a valid event occurs within `K`
cycles of the previous one). Multi-cycle proof: an abstraction function `abs : Regs → ArchState` that is
the identity on the architectural registers when the FSM is in FETCH, a relation `R(regs, s)` = (FETCH and
`abs regs = s`) or (mid-instruction with partial results consistent with `execInstr`), and one lemma per FSM
state. Pipelined: `R` per stage plus forwarding and flush invariants; the architectural state is the
committed state, in-flight instructions are an extra ghost list; the proof is large but its SHAPE is the
multi-cycle one.

**Environment assumptions** (rungs 10 to 12). An environment is a Lean function from the past outputs to
the next inputs; the statement quantifies over environments that satisfy a `WellBehaved` predicate
(bounded latency, memory contents consistent with its own writes). In `Runs2` terms the hypothesis is
`∀ c, stim[c].rdata = env (tr.take c)`, which is a relation between stimulus and trace; non-vacuity is
the construction of the stimulus by recursion on `c` (each entry depends on earlier snapshots only).

---

## 7. Spike plan (next seven days)

### 7.1 The vertical slice

N-bit counter with enable and synchronous reset (`en`, `rst`, `q`), parametric `N ≥ 1`, proved for all `N`
and all cycles, accepted by `check.py` as the first `seq-family` task.

* **Statement draft**: `SeqTask` with `clk = some "clk"`, `rst = some ("rst", true)`, `inputs _ = [("en", 1)]`,
  `outputs N = [("q", N)]`, `State N = BitVec N`, `init = 0`, `step N s (en, ()) = if en = 1 then s + 1 else s`,
  `obs N s _ = (s, ())`. (`CounterCycle.lean`.)
* **ls-sv gaps it hits**: (1) the clock discipline (S0): `cnt` is accepted today but the task needs the
  refusal of the dead-clock variants; (2) the register-transfer cycle theory (S1): none exists for
  `Design2` at symbolic `N`; (3) the instantiation of an `always_ff` body at symbolic `N` has no
  `Gen2`-style theorem (the `always_comb` precedent, `asDesign N`, is a hand-built design family plus
  `#guard` agreement at concrete widths; WP-G has the same need); (4) word-level `+` (WP-B2) for the
  natural source; the spike's reference uses a generated half-adder chain with the existing ripple lemmas.
* **Hand proof for all `N` and all cycles with the current library**: possible, by the M0 recipe on
  `Design2`: a closed-form one-cycle lemma for the exact state shape, `Runs2.forall_of_step` and
  `SeqTask.satisfiedAt_of_cycle`. **Done in this study** (section 0.5): the statement, the reduction theorem
  and the whole counter proof for the hand-built family `cntD N`, kernel-checked with the standard axioms.
  So the spike's day 3 to 5 proof work shrinks to: the instantiation agreement for symbolic `N`
  (`cntD N = cnt.sem N`), the registered-`+` version of the arithmetic (WP-B2, or the generated incrementer),
  the ports/interface and `Terminates2` glue for the player's file, and making the lemmas a library
  (`Seq2`) instead of per-design code.
* **Checker changes**: flip-flop prices and `dfflegalize` in `score/`; `task.json` `seq-family`; `Disciplined`
  in place of `Unclocked`; `postsynth.py --clocked` with the trace harness (works against the RTL and the
  netlist before ls-sv is involved, so it is slot-free work); leaderboard fields.

### 7.2 Work packages and days

| WP | content | days | needs | can run with |
|---|---|---|---|---|
| Q1 | The maintainers approve statement, policies, prices (section 8) | day 1 | this note | everything |
| Q2 | clocked postsynth harness (Python, C++/Verilator, trace generator, randomized initial state) against RTL and netlist; counter reference SV, oracle | days 1 to 3 | none (slot-free) | WP-F/P/G |
| Q3 | S0 clock discipline in ls-sv (loader refusal, `ClockedBy` decidable check), rows, Xcelium pins | days 2 to 3 | Q1 | small Lean; before or after WP-P |
| Q4 | `Seq2`: NBA symbolic execution + two-frame cycle lemma, `Terminates2`, `Deterministic2` for NBA-only designs; counter one-cycle lemma at symbolic `N` (instantiation agreement); hand proof of the statement | days 3 to 5 | Q1, `SeqTask.lean` | after WP-P gate 1; Lean-heavy, serialize with WP-G |
| Q5 | checker: `ge.json`/`svgolf.ys` flip-flop lines, `score.py`, `task.json` kind, `check.py` stages, leaderboard fields, tests/expected | days 4 to 6 | Q1, Q2 | after WP-C2 (light postsynth) lands, not during a regression |
| Q6 | counter task end to end: `Spec.lean`, `reference/`, baselines (hand-built incrementer, `+` version), expected scores | days 5 to 6 | Q3, Q4, Q5 | |
| Q7 | `sv_seq` v0 (front end for one `always_ff` with NBA and `if`/`else`; emits the RT equations; counter in two lines) | days 6 to 7, stretch | WP-G, WP-P, Q4 | |
| Q8 | dry run by an independent agent from public material only; friction log; decisions list | day 7 | Q6 | |

Dependencies on the combinational work: **WP-F** (done or integrating) needs nothing; **WP-P** (proof API
and speed) should land its shared summary and `sv_interface` before Q7 and ideally before Q4 touches
`CombView*`; **WP-G** (`always_comb` bodies, `~`, `?:`) defines the `if`/`else` equation shape that Q7 must
reuse, so its design note (day 3 of PLAN2) should be reviewed with NBA bodies in view; **WP-B2** (word-level
operators) is needed for the natural counter source and for rungs 4 to 6, not for the spike. Parallel with
them: Q2 and the statement/policy work (no slot), Q3 and Q4 (small Lean jobs; Q4 is Lean-heavy and should
queue after WP-G rather than overlap it, since both change the instantiation/summary front end). The one
real conflict is the front end files `CombView*`/`CombEq*`: Q7 must wait for WP-G and WP-P to finish editing
them.

### 7.3 What the week should NOT do

S4 to S7, the TxTask class, CDC, any CPU work beyond this note, and any change to `CombTask` (the
degenerate-case theorem makes that a later cosmetic decision).

---

## 8. Decisions for the maintainers

1. **Statement shape.** Approve `SeqTask` as in 0.2: Moore observation after the edge; claim from every
   reset; `ClockedBy` instead of edge-detected semantics for v1; the spec a deterministic machine in v1
   (relational / `TxTask` when rung 4 needs it). Alternatives: pre-edge Mealy sampling (needs the pre-edge
   state in the trace; affects the R1 `cycleOf` abstraction) or edge-detected semantics now (S5 first; two
   entries per period).
2. **Initial values.** No declaration initializers or `initial` on state, reset is the only initialization;
   confirm the pinned `dfflegalize ... x` backstop (it turns today's silent drop of the init value into an
   error).
3. **Prices and metric.** The flip-flop weights (convention to pin) and whether multi-cycle tasks are
   scored by area-delay product or a three-axis Pareto; whether the clock period proxy is plain `ltp -noff`.
4. **Sequencing of the hard semantics.** Build S4 to S7 only after a one-clock RISC core runs; or earlier if an
   async FIFO is wanted as a showcase task. If CDC is built, take the per-bit old-or-new sampling model
   (otherwise a binary-pointer FIFO verifies).
5. **ISA.** Purpose-made 16-bit first, RV32I through `LeanModels.Rv` next, or RV32I directly.
6. **First public sequential task.** The counter is the spike; a golfable first task (serial multiplier,
   LFSR, or UART transmitter) may be a better showcase, and decides whether `TxTask` comes before or
   after the first release.
7. **`CombTask` and `SeqTask`.** Keep both structures (the theorem links them), or define `CombTask` through
   `toSeq` once the new statement is trusted.

---

## 9. Reproducing

`compile.sh` lists the commands (from the repository's root, through the Lean slot wrapper):
`lake env lean design/sequential/SeqTask.lean`, then `CounterCycle.lean` (which imports `SeqTask` as a
sibling module and builds a scratch `.olean` outside the repository). The experiments (`experiments.md`)
need `check/envelope.py` with `--cache-dir` in a scratch directory, `check.py --unproved` (its stages run
under the checker's integrity tripwire; no checker file was edited), Yosys 0.53 with the pinned scripts, and
a licensed Xcelium host for the Xcelium rows.
