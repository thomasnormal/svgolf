# Modelling LRM-legal nondeterminism in the symbolic tier

Design note, 2026-10-31, revised the same day after an adversarial review. It answers the ruling on the register's
`never` rows: "it should be possible to model the nondeterminism in Lean. If a golfer uses these constructs, they just have to
prove they can handle the nondeterminism. The final output of the circuit should always be deterministic, unless the task
doesn't require it." Nothing here is built. The evidence about the tools is `docs/sv-tools-split-audit.md` (measured on
2026-10-31, probes reproducible from `harness/sv/tools_split_audit/`); the code references are to `svgolf-prep` 05e59add.

**What the review changed.** The first version of this note (a) called self-reading `always_comb` LRM nondeterminism, (b) said
the existing `Computes` and `Terminates2` conjuncts already reject bad combinational loops, (c) argued soundness for acyclic
netlists only, (d) priced the wake-up semantics as a row deliverable and the full interleaving semantics as an R1 rung, and
(e) filed two writers of one bit as plainly illegal. All five were wrong or incomplete and are corrected below; the
effort numbers of the first version are withdrawn.

## 0. Summary

* **What is quantified today.** `Models2` ranges over every `ScheduleOracle` (a permutation of the ready processes at each
  pass) and every stimulus: races between whole processes (`race_blk`: `always @(posedge clk) a = b;` and `... b = a;`).
  It does NOT range over which processes wake up (every comb process is re-run every pass until nothing changes), when a
  continuous assignment's update lands relative to a running process, or the interleaving inside a process (IEEE 4.7).
* **Three different things have been called "the tools split", and the ruling covers only the first.**
  (1) *LRM-legal nondeterminism*: the LRM leaves the order open (4.7, 4.8). Examples: two plain `always @*` blocks writing one
  variable (four tools, four traces), the lost wake-up of an `always_comb` that reads a continuous copy of what it writes
  (alias-read; arguably legal, 4.7). (2) *Simulator versus synthesizer*: the LRM's answer is deterministic and the
  synthesizers compute another one. Example: self-reading `always_comb` (`y = t; t = a;`): 9.2.2.2.1(b) keeps `t` out of the
  sensitivity list, so the block does not re-run on its own write and `y` stays one change behind `a`; Icarus and Xcelium do
  that, Verilator and the Yosys netlist give `y = a`. (3) *Tool bugs*: Yosys evaluates a port actual self-determined, reads
  `"\x41"` as text. These are `P-SAME-PROGRAM` refusals, not a schedule.
* **A run set cannot lift (2).** `CombTask.Computes` quantifies over every run; the stale run gives `y_k = a_(k-1)` where the
  task demands `fn(a_k)`, so a genuine self-read is unprovable whatever run set the model uses. What a lift admits is the
  guard's recorded over-refusal residue (dead reads, infeasible paths), which a sharper guard admits for far less. The question
  that decides the row is the maintainers': which reading does the proof follow (section 10, question 1).
* **The golfer's obligation needs no new clause.** `Computes` plus `Terminates2` already say "in every completed run, under
  every schedule and stimulus, the outputs are `fn` of the inputs, and every run completes". Admitting a nondeterministic
  construct changes what "every run" ranges over (`Runs2`), not the statement.
* **Soundness needs more than the first version said** (section 4): the netlist can leave the model's run set by six
  mechanisms, each with its own gate; for combinational loops there is no argument yet, and section 7 shows a loop the model
  calls constant 0 whose scored netlist holds state.
* **Loops: do not relax.** The first version claimed `Terminates2` and `Computes` reject the bad loops. They do not
  (section 7, measured). `fourstate`'s loop refusal stays until a new obligation exists.
* **Effort: unsized.** The wake-up semantics (O1) belongs inside R1 inch 4b, not beside it; the full interleaving semantics
  (O3) is beyond R1. Neither has a standalone golf payoff identified (section 6).

## 1. What the model quantifies today

The definitions (`LeanModels/Sv/Sem2.lean`, `Spec2.lean`, `Mono2.lean`):

| item | definition | what it quantifies |
|---|---|---|
| `ScheduleOracle` | `choose : Nat → List Nat → List Nat` with `choose_perm`: a permutation of the ready list at invocation `k` | the ORDER in which ready processes run in a pass; never which processes are ready |
| `combSettle2` | pass: run EVERY comb process (`assign`, `always_comb`) whole, in `σ.choose k combIndices` order; repeat until the state is unchanged; fuel exhausted is `.timeout` | a fixpoint iteration; the schedule changes the path to the fixpoint, not the set of processes run |
| `cycleStep2` | apply inputs; settle; reset-event phase; edge phase in `σ` order with an NBA queue; commit; settle | one snapshot per stimulus entry |
| `Runs2 d σ stim tr` | `∃ fuel, run2 d σ fuel stim = .ok tr` | a COMPLETED run; one trace per `(σ, stim)` (`Runs2.functional`, `run2_det`) |
| `Models2 d P` | `∀ σ stim tr, Runs2 d σ stim tr → P d stim tr` | every schedule, stimulus and completed run |
| `Terminates2 d` | `∀ σ stim, ∃ tr, Runs2 d σ stim tr` | the non-vacuity half: every run completes |
| `Deterministic2 d` | any two completed runs of one stimulus give equal WHOLE traces | internal signals included (stronger than the golfer needs) |

So nondeterminism enters through one door, the order of whole-process executions inside a pass. It is real and used: two
processes that each write the variable the other reads give two traces (`race_blk`, whose processes are `a = b` and `b = a`;
`Mono2` ends with the same pair). Three things event-driven simulators do are NOT choices in the model:

1. **Wake-up.** An `always_comb` runs at time zero and then when something in its implicit sensitivity list changes; the list
   excludes "any expression that is also written within the block" (IEEE 9.2.2.2.1(b)). `combSettle2` re-runs the block on its
   own writes, so `y = t; t = a;` has exactly one run in the model, `y = a`. Icarus 12 and Xcelium 24.03 give the LRM's answer
   (`y` one change behind; Xcelium reads `xx` at cycle 0), Verilator and the Yosys netlist give `y = a`. This is shape (2) of the
   summary, deterministic in the LRM.
2. **When a continuous assignment's update lands.** IEEE 4.7/4.8: update events may be intermingled with a running process. In
   `assign w = t; always_comb begin y = w; t = a; end`, Icarus applies the update inside the run and loses the wake-up (stale
   `y`); Xcelium, Verilator and the netlist defer it (`y = a`). That Icarus's order is legal is an inference from 4.7 ("the
   simulator may suspend execution ... the order of interleaved execution is nondeterministic"), not a quoted sentence.
3. **Interleaving within a process.** Same clause: statements need not execute as one event.

What bounds the gap today is the pair of guards. `CombGuard2` refuses a body that reads a bit before writing it and writes it
later; `CombGuard2Sound` proves that an admitted body is idempotent, so the one run an event-driven simulator makes per wake-up
reaches the fixpoint the settle computes. `CombAlias2`/`CombAlias2Sound` do the same for reads through continuous assigns (their
header says simulator equivalence is NOT proved; the argument is the measured mechanism). The guards ARE the boundary of the
fragment on which the model equals the event-driven simulators.

## 2. What the shapes need

| shape | LRM answer | what the tools do | kind | in the model today | needed |
|---|---|---|---|---|---|
| self-read, `y = t; t = a;` | deterministic: stale | stale: Icarus, Xcelium. settled: Verilator, Yosys | (2) simulator vs synthesizer | settled only | a decision (question 1), not a run set |
| alias-read, `assign w = t; ... y = w; t = a;` | arguably either (4.7) | stale: Icarus only. settled: Xcelium, Verilator, Yosys | (1), Icarus-only | settled only | declare Icarus (route A) or a lost-wake-up run (route B) |
| two PLAIN `always @*` writers of one bit | open (a race) | four tools, four traces; Yosys: "multiple conflicting drivers" | (1) | extractor refuses `always @*` | plain-`always @*` support first; then `σ` already covers the order |
| two writers, one of them `always_comb`/`always_ff` (or `initial` + `always_comb`) | illegal (9.2.2.2, 9.2.2.4) | slang error; Xcelium rejects | illegal | Lean guard `driversOk`; `initial` + `always_comb` is refused only because the loader has no `Initial` process kind yet | nothing: no run set contains it |
| settling loop `y = s ? d : y` | one stable value per input | identical in all five tools | loop | accepted by `run2` | a termination AND a state-freedom argument (section 7) |
| state-holding loop (`loop_lat_if`) | the 4-state run is constant | RTL simulators: constant 0. netlist: two stable states | loop | accepted by `run2`, answers constant 0 | nothing safe: refuse |
| oscillating loop | no value | Icarus hangs, Verilator aborts, Xcelium stops at an arbitrary value | loop | `.timeout`: no run | nothing: a design with no completed run never satisfies `Terminates2` |
| Yosys reading `p + q` self-determined | not a choice: Yosys is non-conformant | slang, Verilator, Xcelium agree | (3) tool bug | refused | not nondeterminism (section 4, mechanism 5) |

## 3. The golfer's obligation, as stated in the task

`SvGolf/Task.lean` already has the shape. `CombTask.Computes N d` is `d ⊨₂ spec2 (fun stim tr => ∀ c inputs st, stim[c]? =
some inputs → tr[c]? = some st → ∀ v, HoldAll inputs (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v))`, and
`SatisfiedAt` pairs it with `Unclocked d ∧ Terminates2 d`. Read with a larger `Runs2`:

* "the final output of the circuit is deterministic" is `Computes`: `fn` is a function, so every completed run, whatever
  schedule or hold-previous choice produced it, must end the cycle in the same output ports;
* "every legal behaviour completes" is `Terminates2`: an oscillating run has no completed trace and falsifies it, and
  `Terminates2` quantifies over every oracle, so the oscillation cannot be hidden;
* only the OUTPUT ports at the end-of-cycle snapshot are observed. Internal nondeterminism that never reaches an output is
  allowed (the obligation is `Computes`, not `Deterministic2`). Glitches inside a cycle are unobservable at that granularity,
  which is also what the netlist check sees.

"Unless the task does not require it": a task whose answer is a relation (any valid output) needs a relational variant
(`Computes` as `R inputs outputs` instead of `outputs = fn inputs`). `CombTask` is functional by construction; a `RelTask` is a
small addition to the trusted file, not part of this note.

The work is in the TRUSTED semantics, not in the task statement. That is the right place (the statement stays short), and it is
where the risk sits: a run missing from the model silently shrinks every golfer's obligation. The converse also holds and
matters for shape (2): a run added that no pipeline tool needs makes a correct design unprovable.

## 4. Why a proof over a superset is sound for the scored circuit

Let `B(d)` be the set of behaviours of the circuit Yosys synthesizes from `d` and `R(d)` the model's set of runs. The model is
ADEQUATE for `d` (A1) when every behaviour in `B(d)` is the final snapshot of some run in `R(d)`. If A1 holds and the golfer
proves "every run in `R(d)` ends with `outputs = fn(inputs)`", the netlist computes `fn`. A1 is not provable in Lean (Yosys is not
in the kernel); it is established per class and tested by sampling (`sg-ps-differ`). The first version stated A1 for a
combinational netlist only. The netlist can leave `R(d)` by these mechanisms, and each has a gate that excludes it:

| # | mechanism | example | gate that excludes it |
|---|---|---|---|
| 1 | the netlist realises a run no LRM schedule produces | self-read: settled `y = a` against the LRM's stale run | not a gate: `R` must contain the synthesis run explicitly, in addition to the LRM runs. Today the guard refuses the shape |
| 2 | x/z resolved freely by the synthesizer | an undriven read, `if (x)`, an `'x` literal | `srcgate` (x/z literals), `fourstate` (every x source) |
| 3 | several drivers | two plain `always @*` writers: the netlist keeps one writer's value (`two_plain`); `00` for always_comb blocks writing `11` and `10` (`drv_pw_lit`) | slang error if one writer is `always_comb`/`always_ff`; for two plain writers the extractor (`always @*` is loud) and `fourstate` (Yosys `check`: multiple conflicting drivers) |
| 4 | combinational loops | `y = y & a`: two stable states | `fourstate` (Yosys `check`: found logic loop). NO argument that A1 holds for a cyclic netlist exists (section 7) |
| 5 | the frontends read the text differently | port-actual context width, parameter-override width, `"\x41"` (`\a \v \f` were here until 2026-11-01: Xcelium alone dissents, so they are admitted) | `P-SAME-PROGRAM` refusals in the extractor and the Lean guards; not a schedule, no run set helps |
| 6 | the check is sampled | a difference confined to a region no vector reaches | `postsynth` samples (fixed corners, harvested constants, random); it cannot see mechanism 4 where the circuit's initial state is fixed at 0 (Verilator gets `--x-initial 0` and `randReset(0)`) |

A1 per class of design: for an acyclic, x-free netlist the output is a function of the inputs and A1 says that function is one of
the model's final snapshots (the settled run suffices, "L1"). For a cyclic netlist the output is not a function in general, so
A1 would need both uniqueness of the stable state for every initial state and the model reaching it; neither exists. For an
x-sourced design A1 is false by design (Yosys picks a value) and mechanism 2's gate is what keeps it out.

Three remarks.

1. **Monotone in `R`, with a cost at both ends.** Adding runs makes A1 easier and the proof harder. For shape (2) the model needs
   two non-equivalent additions: the synthesizers' run (settled; NOT an LRM run) for soundness of the score, and the LRM's run
   (stale) if the proof is to hold in the simulators too. Their union makes a genuine self-read unprovable (section 0).
2. **A1 is not weakened by a larger `R`, and a larger `R` needs its own differential evidence.** The acceptance test is "the
   pinned trace of every pipeline tool is a trace of the model" on the nine `rbw_*` and seven `acg_alias_*` rows. The Xcelium
   golden file (`harness/sv/xcelium_golden.json`) holds 2 of the 7 alias rows (`acg_alias_assign`, `acg_alias_port`) and none of
   the `rbw_*` rows or the `fold_uwovr` / `fold_sho_*` rows; the others are measured in the audit but unpinned. Pinning 5 alias
   rows, 9 `rbw_*` rows and 4 override rows is part of the price of every route below, and cannot be done first:
   `xcelium_batch.py` pins only SIMULATED rows (a row with a `refusal` is skipped), so the pins arrive with the lift.
3. **Tool bugs are a different axis** (mechanism 5). One could quantify over "elaboration profiles" (LRM reading, Yosys reading)
   and let the golfer prove both give equal outputs, but that needs a second elaborator in Lean and admits only designs where the
   readings agree, which `PExpr.portSafe` already admits syntactically. Not proposed.

## 5. Cost to the `sv_comb` tactics

The tactic stack (`Comb2*`, `CombEq*`, `CombKnown*`, `CombLib`, `CombProc*`, `CombView*`) is 22 748 lines, example files included.
Its bridge is `combSettle2_eqs` / `cycleStep2_eqs` (`Comb2Sound.lean`), `Models2.of_comb` and `Terminates2.of_acyclic`
(`Comb2.lean`): per-settle equations of the settled run, lifted to every snapshot. Under a larger run set they remain true only
for designs on which the new runs add nothing. The four guard files, `CombGuard2` (474), `CombGuard2Sound` (1 415), `CombAlias2`
(457) and `CombAlias2Sound` (758), 3 104 lines, are what a wake-up semantics reworks most directly; they are not in the 22 748.

* **Plan.** Keep the old judgment as the fast path and prove adequacy A2: for a design in the guard-admitted fragment
  (`CombDesign`, `Acyclic`, plus `combGuardProc`/`aliasGuardProc` admission) the new run set has the same final snapshots as the old
  one. `Acyclic` is part of the statement: with a non-monotone 4-state `if`, cyclic designs can differ by wake-up order, so the
  confluence claim does not hold without it. Mathematically this is what `CombGuard2Sound` (idempotence) and `CombAlias2Sound`
  already say about one run; A2 states it for the whole set and closes the bridge once. `CombAlias2Sound`'s own header says the
  missing bridge "would need a new interpreter and a second copy of the self-read guard's simulation proof", and R1 §5.3 calls the
  analogous adequacy lemma "a genuine theorem" and "the honest price of the rung". The claim that the 22 748 lines need no edit if
  `Models2.of_comb` is re-proved from A2 is plausible and UNVERIFIED (no consumer count was made).
* **Outside the fragment** (a self-reading body, a loop) the tactics do not apply: by-hand proofs first. The by-hand route exists
  (`Comb2ProcExample`, `Spec2` invariants) but is expensive, and the realistic population is small (nobody writes `y = t; t = a;`
  on purpose).
* **API churn.** `Spec2.lean` (498 lines) and `Mono2.lean` (811) restate for the new oracle; the additive pattern of `Regions.lean`
  (`RegionOracle` with an embedding `toRegion`, so no existing `∀ σ` theorem breaks) is the model: introduce the new oracle as a
  new type with a conservativity embedding (`ScheduleOracle.toEvt` is a proposed name, not an existing one), then move the judgment.

## 6. Design options and their relation to R1

Sizes are given by analogy in lines of Lean, not in time: the first version's "engineer-weeks, mine" are withdrawn.

| option | what it adds | size by analogy | relation to R1 |
|---|---|---|---|
| **O0 declare** | Icarus-only splits (alias-read; untyped override width) become declared departures; the guard stops refusing them | the round-6 declarations it re-adds were rows plus a guard flag; dominated by the Xcelium pins (section 4, remark 2) | none |
| **O1 wake-up** | per-process implicit sensitivity set (reuse the bit-window machinery of `CombGuard2`: `Expr2.rdW`, `Stmt2.mayW`); a process runs at time zero and when a bit of its set changes, never on its own writes; `σ` chooses among the woken processes; adequacy A2 | A2 is the class of `CombGuard2Sound` (1 415 lines) for the whole run set, plus restating `Spec2`/`Mono2` (1 309 lines) and the `Models2.of_comb` bridge; unsized | **the same machinery as R1 inch 4b.** R1's illustrative `Trigger` (`atEdge`, `atTime`, `atEvent`, `waitFor`) has no change-triggered implicit sensitivity, and `Slot.lean` implements Active/Inactive/NBA for the timed tier only. O1 is the implicit-sensitivity trigger R1 needs for `always_comb` and `always @*`; built beside R1 it would be built twice, with the adequacy proved twice |
| **O2 lost wake-up** | one oracle bit per continuous-assign update: apply it inside the running process and drop the wake-up (Icarus) or defer it (Xcelium) | on top of O1; tool-shaped, not LRM-shaped | none |
| **O3 full interleaving** | statement-granular small-step semantics with pending update events: IEEE 4.7 faithfully | **unpriced, and beyond R1.** R1 §2.3 states that the oracle "never chooses ... the statement order inside a process", and §9.8 builds on suspension points being SYNTACTIC ("a language that could suspend at an arbitrary point would need a real continuation"). O3 is that language | none |

Recommendation: O0 for the two Icarus-only rows (after the pins and the maintainers' questions 1 and 2), O1 only as part of R1 inch 4b
and the sequential layer (`always_latch`, `always @*` and clock gating all need wake-up semantics), O2 and O3 only if the maintainers
wants L2 portability across simulators. No standalone golf payoff for O1 has been identified: the only construct it was
proposed for, self-read, gains the residue only (section 0).

## 7. Combinational loops

**Proof side: the first version's claim is retracted.** It said a latch fails `Computes` and an oscillator fails `Terminates2`,
so "no static rule is needed at all: the two existing conjuncts already reject the bad loops", and proposed a `fourstate`
exemption conditioned on a `Terminates2` proof. That holds only for ternary-monotone shapes such as `y = s ? d : y` (`y` stays
`x` while `s = 0`). It fails for a loop whose start value is resolved by a procedural `if`, because `execStmt2` evaluates
`if c` with an `x` condition by taking the else branch, so the model's run settles to a KNOWN value while the netlist still has
two stable states. The counterexample, measured (probe `loop_lat_if`):

```systemverilog
module loop_lat_if(input logic a, output logic y);
  logic t;
  always_comb begin if (y) t = a; else t = 1'b0; end
  always_comb y = t;
endmodule
```

* Icarus, Verilator and Xcelium simulate the RTL as `y = 0` for every stimulus; `run2` through the Lean slot gives the same
  (stimuli `1,1,0,1,1,0` and `0,1,1,0,1`: see the audit appendix). By hand: from the `x` start `if (y)` takes the else branch,
  `t = 0`, `y = 0`, and `y` never leaves `{x, 0}`. So `Computes` holds with `fn = const 0` and `Terminates2` holds.
* The pinned scorer prices it at one gate, `$_AND_(.A(a), .B(y), .Y(y))`, 1.333 GE, depth 1: the netlist is `y = y & a`.
* Yosys `sat` on that netlist: for `a = 1` both `y = 1` and `y = 0` are satisfiable (two stable states); for `a = 0` only `y = 0`.
  The circuit remembers its history.
* `fourstate` rejects it today only through Yosys `check` ("found logic loop"); the extractor emits no `Unsupported` for it.
  `postsynth` has no way to see it (read from `check/postsynth.py`, not run): it simulates with `--x-initial 0` and `randReset(0)`,
  so every vector starts from `y = 0` and agrees with the model.

So the relaxation of the first version would admit a design the proof calls constant while the scored circuit has memory. The
criterion that makes a loop a function is "functional for ALL initial boolean values of the loop signals" (the setting of Riedel
and Bruck's cyclic combinational circuits), a quantifier the model does not have. Two ways to get it, either of which must be
designed BEFORE any relaxation: (i) restrict loops to a ternary-monotone fragment (no procedural `if`/`case`/`&&`/`===` reading a
loop-reachable signal), where the 4-state fixpoint from all-`x` being fully known implies the same for every boolean start (the
classical ternary-simulation argument); this is the loop-restricted form of the existing `XTAINT` plan item; or (ii) a new
obligation `LoopFunctional` quantifying over every boolean start of the loop signals.

**Score side, measured** (`score.py --no-gate`, the pinned `canon.ys` + `svgolf.ys`):

| design | scored netlist | area / depth |
|---|---|---|
| `y = s ? d : y` (mux feedback) | one `$_MUX_` whose `Y` drives its own `A` | 2.333 GE / depth 1 |
| `a = s ? d : b; b = s ? a : d` (settling structural loop) | loop optimized away: `b = MUX(d, d, s)`, `a = d` | 2.333 GE / 1 |
| cross-coupled NOR latch | `NOT`, `ANDNOT`, `OR` with the loop retained | 3.333 GE / 2 |
| `assign a = ~a` | no gate (the loop is removed) | 0 GE |
| `a = en ? ~a : 1'b0` (a true oscillator once `en = 1`) | `AND(en, _1_)` and `NAND(en, _1_)` with the loop retained: a ring oscillator, priced like any gate | 2.333 GE / depth 2 |
| `loop_lat_if` (state-holding, above) | `$_AND_(a, y) -> y` | 1.333 GE / 1 |

The flow accepts and prices loops: `abc -g ...`, `opt_clean`, `stat -json` and `ltp -noff` all complete. The checker does not
get that far: `fourstate` refuses every logic loop by design, because a retained loop is a latch to the proof, and the table
shows that this refusal is load-bearing, not conservative. `postsynth` would refuse a netlist with a loop a second time: it lints
with `-Wall` and every warning fatal except two (`NETLIST_WNO`), and `UNOPTFLAT` is not one of them. Relaxing it would need
`postsynth` to simulate a retained loop AND to see state (a random initial state per vector, not 0). That is a checker change
as large as the proof-side obligation.

**Why it might matter.** Cyclic combinational circuits can be smaller than acyclic ones for the same function (Riedel and Bruck,
DAC 2003), so loops are a golf dimension that the current rule closes. That is also the risk: it is the corner on which tool
behaviour is least tested, and the register keeps the oscillating half (`gu-comb-loop`) as `never` because there is nothing to
lift there.

## 8. The rows, in order

| order | row | kind | what is needed | size |
|---|---|---|---|---|
| 1 | `hi-override-untyped-width` | Icarus-only | lift the extractor refusal, then pin the four `fold_uwovr` / `fold_sho_*` Xcelium traces (the batch tool pins simulated rows only); one declared row | small; dominated by the pins |
| 2 | `gu-alias-read` | Icarus-only; Icarus's order arguably legal | The maintainers' question 2 (route A declare / route B run set); the five unpinned Xcelium traces (pinned once the rows are simulated, i.e. with the lift); then O0 | small for route A; O1+O2 for route B |
| 3 | loops, only if the maintainers want them (question 3) | loop | design `LoopFunctional` or the ternary-monotone fragment FIRST (section 7), then a `fourstate` exemption and `postsynth` that sees state. Independent of O1 | not sized |
| 4 | plain `always @*` writer pairs | (1) | plain `always @*` support in the extractor, then `σ` already covers the order; `fourstate` still rejects the netlist (conflicting drivers), so no golf value | not sized |
| not by a run set | `gu-self-read` | (2) simulator vs synthesizer | The maintainers' question 1; at most a sharper guard (the residue). O1 is justified by the sequential layer, not by this row | |
| never | `le-driver-procs` (always_comb/always_ff pairs), `le-driver-mixed`, `le-driver-input`, `pr-always-nocontrol`, section A | ILLEGAL (slang) | none | no run set contains them |
| not this route | `le-portconn-context-width`, `hi-override-context`, `lit-string-hex` | Yosys is non-conformant | none | section 4, mechanism 5 |

## 9. Risks

1. **A missing run shrinks every obligation.** The run set is trusted. Mitigation: the acceptance test of section 4, remark 2,
   repeated whenever a tool version changes.
2. **Time zero.** Xcelium reads `xx` at cycle 0 on stale designs because the block's time-zero run precedes the testbench's first
   assignment. The task statement constrains every cycle including the first and applies inputs before the settle; the run set
   must say whether the time-zero run happens before or after the first stimulus, or include both.
3. **Superset blow-up.** Every added knob multiplies the `Terminates2` obligation: a design must complete under every combination.
   O2's dropped-wake-up bit can produce non-terminating runs for designs that are fine under every real tool. Keep the knobs to
   what a measured tool does.
4. **A1 stays empirical.** A bigger `R` does not prove the netlist is inside it; `postsynth` samples. The nondeterminism model
   does not close that gap and should not be described as closing it.
5. **Vacuity at the other end.** A model that adds runs a real tool never produces can make a correct design unprovable. That is
   acceptable (the golfer rewrites it), but each added knob should name the tool and the row that motivates it. For shape (2) this
   is not a risk but the whole effect.
6. **Gates that carry A1 today are not in the proof.** `fourstate`'s x-source refusal, Yosys `check` and the Lean guards carry
   mechanisms 2 to 4 of section 4. Any relaxation that removes one of them (the first version's loop exemption, O1's time-zero
   `x`) removes an assumption of A1 and needs A1 re-argued for that class.
7. **Effort accounting.** There are no time estimates in this note. The line-count analogues are lower bounds.

## 10. Open questions for the maintainers

1. **Self-read: which reading does the proof follow?** For `y = t; t = a;` the LRM's simulation answer is deterministic and stale
   (Icarus, Xcelium); the synthesizers (Yosys, Verilator) compute the settled value. (i) Follow the LRM: a genuine self-read is
   unprovable and the lift is only a sharper guard for the residue. (ii) Follow the synthesizers, a declared departure from
   explicit LRM text for Icarus AND Xcelium: the guard can go, but that contradicts the 2026-10-29 policy "where the model would
   follow one oracle against explicit LRM text, refuse" unless you amend it. (iii) Both, which is (i) in effect. The row stays
   `never` until you answer.
2. **Alias-read: declare or model?** It is Icarus-only, so your ruling already admits it by declaration (route A). Route B models
   the lost-wake-up order as a run. A: small, but Icarus's order, which is arguably LRM-legal, is then not a run that binds the
   golfer. B: needs O1 and O2.
3. **Do loops matter?** If cyclic combinational circuits are a golf dimension you want, the obligation (ternary-monotone fragment
   or `LoopFunctional`) must be designed first, then two checker changes (`fourstate` and `postsynth`). If not, they stay refused.
4. **Relational tasks.** Do you want a `RelTask` (output in a set, not equal to a function) now? "Unless the task does not require
   it" suggests yes eventually; none of the current ladder needs it.
5. **Xcelium-only dissents.** `pr-init-var` (Xcelium rejects `logic q = 0; always_ff ...`; Verilator also warns on the
   whole-variable form; slang, Yosys and Icarus accept) and `lit-string` (Xcelium reads `\a \v \f` as letters) are not Icarus
   splits and not decided by your rulings. Does an Xcelium-only dissent block a construct that slang, Yosys and Verilator read
   alike?
   **ANSWERED 2026-11-01: no.** "This could be an Xcelium bug. You should check the spec. If the sv spec agrees with
   verilator, slang and yosys, we'll accept it." `\a \v \f` are admitted (IEEE 1800-2023 Table 5-1; rows `lit_str_ctl`,
   `lit_str_ctl_ok`, Xcelium a declared departure); `pr-init-var` stays refused until the sequential tier (the LRM does not
   say whether an initializer is another process: Verilator warns citing 9.2.2, Xcelium rejects).
6. **`\xHH`, closed as a proposal.** Yosys and Xcelium read `"\x41"` as text; the extractor now refuses a hex escape
   (`StringLiteral:hex-escape`, row `lit-string-hex`). Confirm.
   **ANSWERED 2026-11-01: "You decide"**; it stays refused (Yosys, which produces the scored netlist, is the dissenter
   against slang and the LRM: a proof/score split, not an oracle dissent).
7. **Frontend readings as nondeterminism?** Should the golfer be allowed to use a construct on which Yosys is non-conformant if
   they prove both readings give equal outputs, or does `P-SAME-PROGRAM` stay absolute there?
8. **Plain `always @*` pairs.** Legal races that the existing `σ` order models, but they need plain `always @*` support and
   `fourstate` rejects the netlist. Worth admitting as an exercise of the ruling, or not at all?
9. **Staffing.** O1 touches the trusted semantics and overlaps R1; it should be reviewed by someone who has not written the model
   it generalises.
