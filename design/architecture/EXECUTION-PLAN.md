# Execution plan: the two tracks, weeks of 2026-11-03 and 2026-11-09

> **Superseded (11/03) by [svgolf/PLAN4.md](../../PLAN4.md), the one active plan** ("plan 3" in PLAN4's history). Every
> work stream finished its scheduled items early, and the Day-9 integration (`integ1103`) is closing. This file stays as
> the record of the architecture programme: the gates passed, the work items with their commits and rulings, and the
> stop-rule record. Its open items (the G-W1/G-W2 reviews, which became the decisions owed in PLAN4 §4–5, and the week-2
> candidates in the WS*-DAY9 write-ups) are carried into PLAN4. Status marks here are no longer updated.

**Status.** Plan, written 2026-11-02 by the lead after the maintainers approved the architecture (`ARCH-NOTE.md`): both tracks, and decisions 1–10
as leaned (process-atomic profile ruling; no fuel in any definition; observation interface now; event-level environment with a clocking
discipline; v1 svGolf statements kept with a registered debt; an `Admissible` conjunct; one AST with `Stmt2` frozen; 4-state authority with a
2-state view; elaboration in Lean with slang as a multi-point witness; liveness, CDC and SVA deferred with fixed signatures). All sizes are
JUDGED. Days are working days; agents keep running over the weekend, but no gate falls on one. **Amended the same day after an outside review
of this plan (§7 lists what changed).**

**Scope of E in these two weeks** (also stated in `docs/sv-kernel.md`). E is the authoritative semantics of the *declared SystemVerilog
profile*, not of the unrestricted LRM: the profile includes process-atomic execution between suspension points, recorded as a
language-profile restriction (§4.7) with the panel evidence (Xcelium re-runs the block). It grows in named steps, and nothing outside the
current step is expected of it:
- **E-core-0**: continuous assignments, blocking `always_comb`, 4-state values, single-driver signals, acyclic dependencies; no timing, no
  NBA, no hierarchy, no dynamic `while`; canonical loops only when WS3 needs them.
- **E-core-1**: `always_ff`, NBA, async reset, the clocking discipline.
- **E-core-2**: hierarchy, instances, module contracts.

## 1 Workstreams

| id | name | owner | branch / worktree | Lean use | first deliverable |
|---|---|---|---|---|---|
| **WS0** | Integration and hygiene | lead | `integ1102` → `svgolf-prep` → master (via `lssv-main-final`) | builds and suites | `integ1102` landed and pushed |
| **WS1** | Authority track: E-core and the keystone refinements | agent A | `arch-x1` (own worktree) | heavy | X1: R-COMB-0, kernel-checked |
| **WS2** | Product track: observations, cycle machine, contracts | agent P | `arch-obs` | medium | X5: `ObservationModel`, `Obs_run2`, `Computes ↔ Computes_obs` |
| **WS3** | Product track: loops | agent L | `arch-loop` | heavy | G1: nested `clmul` for every N, tactic-free |
| **WS4** | Measurements | agent M | `arch-measure` | light (one `#eval` batch at a time) | X3, X8, X6, X9, X10 reports |
| **WS5** | Governance and documents | lead | `svgolf-prep` | none | `docs/sv-kernel.md`, debt rows, departure row, Stmt2 freeze guard |
| — | Extractor retain-mode twins, Xcelium rows for loop semantics | codex ls-sv agent (proposed; the maintainers relay) | master | — | `--retain-loops` default plan; 200-trip Xcelium row |

**Rules every workstream follows.**
- **One Lean slot, FIFO** (a slot wrapper), acquisitions of at most about 15 minutes, `LEAN_NUM_THREADS=2`, no root `lake build`,
  no nested `SVGOLF_LEAN_WRAP`. Priority when several wait:
  - before G-A: A > L > P > M > lead dev builds;
  - after G-A passes: A and L alternate heavy acquisitions, P takes the next one, M runs only short batches;
  - if G-A fails: no new E work; L and P take the slot for the provisional product work.
- **The full suite runs only on gate nights** (Day 0, Day 5, Day 9). It took 39,428 s on 11-02 and holds the slot for most of a day under
  load. Other nights run a scoped suite (`tests/run.py --only` the touched tasks, plus `tools/check_sv_chain.sh`). Each gate names its
  baseline commit and its scoped prerequisite suite; the full suite is required before a merge, not before an agent starts its next scoped
  proof. A failure is re-run alone before it is believed, and a failure caused by unrelated master movement is recorded and does not block a
  gate.
- **Expectation changes are recorded, never just re-pinned.** When a test's expected verdict changes (for example a stale attack row), the
  change records the old verdict, the new one, why the change in the extractor or semantics makes the new one correct, and which check
  confirms it.
- **Every deliverable carries its status label**: *provisional over `run2`*, *derived from E*, *transport theorem*, or *trusted statement*.
  A product-track proof over `Obs_run2` is never reported as a proof about SystemVerilog until R-DESIGN2 transports it.
- **`Admissible` is policy, not semantics.** E gives a source its meaning; `Admissible` decides whether svGolf accepts it for scoring. Its
  clauses come from X10, never from ad hoc loader refusals.
- **Agents never push, never merge into `svgolf-prep`, never touch the shared tree.** The lead merges. Commits use explicit paths and the
  repo's trailer. No `sorry`, no `native_decide`; `#print axioms` pinned on every new theorem.
- **Every agent reports daily**: done, measured (heartbeats, lines, seconds), blocked, next. A stop rule that fires is reported the same day,
  never worked around.
- **Re-scoping rule**: automate only tedium; the agent writing the proof does the thinking. **Structure rule**: no lowering, no
  unrolling in meaning. **Authority rule**: every view a tactic relies on carries a refinement theorem.

## 2 Gates

| gate | day | condition | if it fails |
|---|---|---|---|
| **G-A** | Day 3 | X1's assign-only half, on E-core-0: (1) a legal-schedule predicate exists, permutation-based as `choose_perm` today, with a proved lemma that no ready process is skipped and none runs after it is done; (2) every legal process-atomic schedule closes the slot, by an explicit rank measure; (3) the closed store satisfies `CombEqs`, and its solution is unique under the rank; (4) a negative cyclic case fails the rank hypothesis; (5) `#print axioms` clean; (6) heartbeats, kernel time, term size and `.olean` size recorded | **stop growing E**; freeze it to what closed; re-plan with the maintainers (ARCH-NOTE §7 stop rule) |
| **G-L0** | Day 2 | the loop domain: the nested `clmul` loops' `TripSchema` (indexed, the inner one depending on the outer index) agrees with the source headers; endpoint cases (0 and 1 trips, N = 126, 127, 200, `<=`, descending, `+= c`, negative start, nested dependent bound, iterator shadowing) | a representation problem, not a library-size problem: fix the schema before L1 |
| **G-L1** | Day 3 | rows: row 0 is the state after initialization, row k+1 one body execution, the final state row N | stop rule S3 (about 400 lines across L1 to L3) |
| **G-L2** | Day 4 | the body is admitted by the comb guard and total on shaped states | as G-L1 |
| **G-L3** | Day 6 | the arithmetic exit: the final row satisfies the `clmul` spec, giving `Statement` for every N | as G-L1 |
| **G-B** | Day 6 | X1 complete, as a chain and not a fixture equality: E-core-0 → R-BODY → R-COMB-0 → `CombEqs` → `combSettle2`, for assigns plus one `always_comb`; a negative self-reading or cyclic design that fails the hypotheses | no general E core (M3) is started; the authority track re-plans |
| **G-W1** | Day 5 | week-1 review with the maintainers | — |
| **G-W2** | Day 10 | week-2 review; plan week 3 (sv-0.3 envelope, R-CYCLE, R-DESIGN2 slice) | — |

**Gate status** (`[x]` passed and checked by the lead, `[~]` in progress, `[ ]` open; commits are on the workstream branches until they are
merged):

- `[x]` G-A, 11-02, ahead of Day 3, on `arch-x1`: E-core-0 for assigns `0e4aa7a0` and R-COMB-0 `1d28a0ee`; the X1-NOTE result is `7f54bed7`.
- `[x]` G-L0, G-L1, G-L2 and G-L3, 11-02, ahead of Days 2 to 6, on `arch-loop`.
  - G-L0: trip schemas `a6672a4e`.
  - G-L1: rows `fb98950c`.
  - G-L2: the guard `0baa6bab`.
  - G-L3: the nested `clmul` `Statement` for every N `2cbcbb95`, provisional over `run2`.
  - Ahead of the Day 7–8 rows: automation items B, A, C and E, which brought the proof from 394 to 96 design-specific lines
    (`4c86bff6`).
- `[x]` G-B, 11-02, ahead of Day 6, on `arch-x1`: the chain with `always_comb` is `dcc95d55`; the X1-NOTE result is `49553261`.
  - Ahead of week 2: the R-DESIGN2 comb slice `d00b2919`, a transport theorem.
- `[ ]` G-W1 (Day 5) and G-W2 (Day 10): reviews with the maintainers.

**Work items done ahead of their day** (11-02):
- `[x]` WS0 Day 0: the integration suite's failures triaged (7 stale attack rows re-triaged `8e72c072`; 2 environmental; 3 under
  load, passing when re-run alone); master merged into `integ1102`, built; `svgolf-prep` fast-forwarded to it (0 behind master).
- `[x]` WS0 Day 1: `integ1102` landed on `svgolf-prep`, and the ls-sv parts were pushed to master as one verified commit (`7be3eb99`, merged as `76b96afd`, fast-forward). That push carried WP-LIN, gates 4b and 4c, the `CombProc` arm fix, the register fixes, the kernel page and the freeze guard. Master was merged back into prep (`79c30bb8`; prep = master + `svgolf/`). The `ci-sv-deps` tooling (an Sv landing builds the comb chain above it) was tested and pushed separately (`c0a5df20`). The scoped suite on the synced tree PASSED (11-03 00:58), run one task per slot acquisition: layout, build, unit, modes, canon, references, validate and attacks, every row; 0 failed. Master's next ls-sv batch (8202bf7f: qualified-case violations loud, Initial retained loud, fixed-dimension queries, two-state declarations) is merged into prep, and the design attacks are being re-run on it.
- `[x]` WS5 Day 1, on `svgolf-prep`:
  - `docs/sv-kernel.md`, with the debt rows (`122e24d0`);
  - the `Stmt2` freeze guard `Examples/system-verilog/stmt2_frozen/guard.lean` (`122e24d0`);
  - the §4.7 departure as register row `sv-div-4` with paired guards (`d17b712d`).
- `[x]` WS1:
  - R-COMB-1, the window-granular rank, derived from E (`arch-x1` `439574fd`);
  - D-X1f's fuel half: `always_comb` statement fuel counted in `combFuel`, with sufficiency in `Comb2Fuel`, and all 93
    `Comb2Base` dependents green (`b47a2cab`). The termination half (D-X1f2, window-acyclic designs) is still owed.
  - D-X1h, the first R-CYCLE slice: `CounterE`'s `cnt_rise_step` derives the counter task's step and init from `rEdge` at a
    symbolic N (`728b6ee2`). The `Obs`-level inclusion is not done.
  - The three E-core-0 fidelity findings from X2 (`33dc39c8` and the commit after it). Every Kernel module, `ObsCombE` and
    `CounterE` rebuild green with no `sorryAx`.
    - `acg_xproc_bits` is fixed. An `always_comb` now senses the unwritten bits of a partly written read
      (`Stmt2.partialSens`, LRM 9.2.2.2.1), and `Core0Smoke.xprocBits` pins Xcelium's 01/10/1x.
    - dyn32 is not a defect. E reads out-of-range bits as x per LRM 11.5.1, as `run2` does, and Xcelium's all-x is the
      declared `xcelium-runtime-partial-part-select-all-x` (`dyn32_part`). The row `dyn32` itself is still an undeclared
      XREF-DIFF in the ls-sv audit (docs/sv-xcelium-audit.md 6.1 item 5), and that is the lane's item.
    - A violated `unique`/`unique0`/`priority` claim refuses loudly with `CaseCheck:<qualifier>`, under `run2`'s exact
      conditions. A claim that holds runs the first matching arm (`Core0Smoke.uniqueDup`).
  - D-X1h, the `Obs`-level counter inclusion (`e4d1f7bb`). `cnt_included N` holds at every N: with `clk` hidden, every
    E-core-1 behaviour of the counter is a `run2` behaviour.
    - New: the E-core-1 backend `Obs_E1` (`Kernel/Core1Obs.lean`, 103 lines), and `IncludedOnPorts` with its transport
      `Safe.of_includedOnPorts`.
    - Size: about 270 lines against a ~150 stop; the overrun was reported after the fact.
    - `cnt_follows_E1` (`92bd7481`, 50 lines): over `Obs_E1`, at every N, the counter has `Progress` and
      `cntTask.Follows_obs`, by P's `cnt_satisfiedAt_obs` moved along the inclusion. It is the first sequential task statement
      over E, but it is a *transport theorem*, not derived from E: its safety conjunct is P's `run2` proof carried along
      `cnt_included`. This was mislabelled "derived from E" until the integ1103 review. The interface, admission and
      receptiveness conjuncts are not yet over `Obs_E1`.
  - D-X1f2, termination for window-acyclic designs (`ca33c55a`, 312 lines against ~350). `combSettle2_terminates_win`:
    given the window rank, `combSettle2` returns from every shaped state under every schedule. The fixture is the ibex
    block, whose process-level lowering is cyclic. It covers concrete lowerings only, since `lowerWin` goes through
    `symExec`.
  - D-X1g (`bebc7f65`, 238 lines, all restatement). `WSettleAgree` restates `SettleAgree` over the window rank.
    `included_E0_run2_win` shows every E behaviour is a `run2` behaviour, including for designs whose process lowering is
    cyclic. `Core0Smoke.ibex_included` holds where the process-rank route has no instance (`ibex_no_settles`).
    - Not restated: the typed converse (`run2` → E) and progress over the window rank.
    - Week-2 candidate, a symbolic-N lowering (JUDGED): 400–700 lines for a general lowering built without `symExec`, or
      100–150 per family by L's `SingleE` route.
  - The WS1 Day-9 write-up `WS1-DAY9.md` (`59d8d223`): 12 proved items, the stop-rule record, and 12 open debts.
  - WS1 is through its schedule and waits for the week-2 choices.
  - X4, ahead of Days 7–8: R-EDGE for NBA-only edge processes with async reset, derived from E (`e39d0871`). The discipline
    predicate takes the active edge as a parameter (D-X1k), with `clockExpand_disciplined`; the audit found 0 undisciplined
    testbenches (`7315a647`, `edce9ef8`).
- `[x]` WS2:
  - `IncludedOn` in `Observe.lean` (`arch-obs` `506330b3`);
  - the records' direction over `run2` (`d141c956`).
  - `statement_obs_of_comb` instantiated on all 4 records, 7 code lines each (the E0 instances take 39–60), against the
    check.py-staged solutions (`82cbe8ca`). `CombDesign.writesInput_eq_false` discharges `Receptive` from `CombDesign`
    alone. `svgolf/design/architecture/TASKV2-REVIEW.md` (87 lines) is ready for the Day-5 review.
  - The Day-5/6 counter cycle machine over `run2` (`CounterMachine.lean`) is superseded: WS1 derived the counter's cycle step
    from E (below).
  - Days 7–8, already on the branch: the contract shape D11 (`Contract.lean`, `e4c9aaf5`), with `safety_sound` and its
    inclusion variants, and the composition rule (`compose_holds`/`compose_safe`). The `full_adder` contract is proved
    (`ContractFA.lean`, `fa_sat`, provisional over `run2`).
  - `ContractTask.lean` (`c0e041d6`), the bridge from `Contract.Sat` to Task v2. It has a design-free `Contract.Refines`,
    `satAt_of_sat` generic over the backend, and the canonical contract of any `CombTask`, refining its spec once for all tasks
    (104 generic lines). The full adder is carried through it to `Statement_obs`, provisional over `run2` (52 lines).
  - The Day-8 `ripple_fa` attempt stopped at a finding (READ). `compose_safe`'s `hrely`/`hpar` quantify over every probe list,
    not only runs, so a design with glue processes (port connections, `c[0] = cin`) cannot instantiate it. Decision:
    - add `compose_safe_inv`, the run-restricted invariant form (~15 lines), with `compose_safe` as its `True` instance;
    - `ripple_fa` stays closed until R-HIER on E-core-2. Reusing the child's proof needs the hierarchy map, and a `run2`
      version (250–400 lines, JUDGED) would be a provisional duplicate.
  - Landed:
    - `compose_safe_inv`, with `compose_safe` derived from it (`8cfa9656`);
    - the `ripple_fa` requirements note: about 250–300 lines beyond R-HIER and R-COMB-0, JUDGED (`d2fbab08`);
    - the Day-9 write-up `WS2-DAY9.md` (`c0450148`);
    - TASKV2-REVIEW decision 8, the clock port is clocking and not observed (`1048d0ac`).
  - WS2 is through its schedule and waits on the Day-5 review and the Day-9 merge.
- `[x]` WS3, on `arch-loop`:
  - the recursive loop recognizer, with the priority encoder and popcount proved for every N (`e748d043`);
  - nesting through it, the generic code down 270 lines (`a03c6bb5`).
  - the loop seam over E-core-0, with the body meaning transported (`562a89db`);
  - the three loop designs' task statements over `Obs_E0`, derived from E with no `run2` in the chain, checked at build time
    (`c7b56d30`). This is beyond the plan: week 3's R-DESIGN2 slice for single-process `always_comb` loops.
  - ordinary `always_comb` style over E: `CombFragE`, plus two real `ibex_alu` blocks proved derived from E (`d7af3dac`).
  - whole-slot statements over E for ordinary `always_comb` (`5e2e16e9`, partial):
    - done: the written-before-read check `combWbr`, the locality lemma `Stmt2.sem_rel` with `sem_inv`, and idem/quiet with
      `singleE_comb`;
    - `adder_flags_slot` is derived from E; the latch fixture is in the fragment and refused by the check (`latch_refused`);
    - open: the bwlogic whole slot, which needs the claim-at-opening slot lemma (approved, cap 40 lines);
    - 386 generic lines against the ~250 stop line; compression is a later pass.
- `[x]` WS4, on `arch-measure`:
  - X9 (`a2d85ae0`), X10 (`5aeef789`) and the Day-6 censuses (`d4f1d493`);
  - general-width monotonicity, 90 theorems (`49155b44`).
  - X7 preparation, the baseline cost per template site on today's route (`e7c1fa44`, `d3f2d5b9`):
    - 20.7k–46.8k kHB for the parametric references and 5.4k for the two flat 111–113-site designs;
    - 14.2k and 19.5k kHB for the sliced `ibex_alu` and `ibex_cs_registers`;
    - plus the slicer's census of what the package tier must cover.
  - X2, ahead of Day 7 (`d9a1cf0e`): preemption is invisible without a fed `always_comb` (450 of 460 rows invariant) and changes
    most fed ones (10 of 11 decided); `sv-div-4` widened, and two E-core-0 fidelity findings went to WS1.
  - Next: X12 (`Std.Do` on `execBody`).

## 3 Day by day

### Day 0 — Mon 11-02 (evening)

- **WS0**:
  - When the `integ1102` suite exits, re-run any failure alone before believing it.
  - Triage the 9 failures of nightly `20261102T0500`. One (`fdiv16_draft` coverage) is already fixed on `integ1102`. Seven are attack rows
    whose expected stage went stale because master's extractor now loads those designs (`func_call`, `assign_func`, `gen_always_step`,
    `inst_karatsuba_rec`, `verilog2001_wire`): confirm each new verdict is genuine (the design is correct or refused for a real reason), then
    update `tests/expected.json` row by row, each change recording old verdict, new verdict, why, and the confirming check (§1).
    `fdiv16/rnz_dropped` timed out at 151 s under load: re-run it alone.
  - Merge master's newest commits into `integ1102` (including `c64ebdac`, the loop fuel change), rebuild, scoped suite.
- **WS5**: record the decisions as decided in `ARCH-NOTE.md`; write the agent briefs (from this plan).
- **The maintainers**: relay the three codex messages (§5).

### Day 1 — Tue 11-03

- **WS0**: land `integ1102` into `svgolf-prep`; push the ls-sv parts to master through `lssv-main-final` (WP-LIN, gates 4b and 4c, the
  `CombProc` arm fix, register fixes, the `ci-sv-deps` tooling); merge master back; full suite tonight is NOT run (scoped only).
- **WS5**: `docs/sv-kernel.md` (the declared profile v0, the layers, the rule "new constructs land in E first", `Stmt2` frozen); debt rows in
  the register: svGolf statements over `run2` (family §3.4(b)), Design2 adequacy, statement-level fuel, `Sv.Res`; the §4.7 process-atomic
  departure in `docs/sv-declared-divergences.json`; a guard that fails if `Stmt2` gains a constructor.
- **WS1 (A)**: one-page X1 design on E-core-0: types (`VarId`, typed `Val`, `Config`, `ProcState`); the **legal-schedule predicate**, permutation
  based as `choose_perm`, and the statement of the no-skip lemma; `step` (total, structural), `Steps`, `SlotCloses`; the statements of R-COMB-0,
  of the agreement with `combSettle2`, and of the negative cyclic case. Lead reviews the same day.
- **WS2 (P)**: `ObservationModel` (backend as a parameter; trusted versus proof observations as two types); `Obs_run2` with pre = `cycleStep2`'s
  `st2` (the state the edge pass starts from, `Sem2.lean:695-708`) and post = the snapshot, plus a theorem saying what `st2` is: the state
  after the inputs are applied, the comb logic settles, and any async-reset event has run with its NBA committed and comb settled again, before
  the edge processes run; `st2 = st1` when no reset event fires (ruled 2026-11-02 on agent P's finding).
- **WS3 (L)**: `TripSchema` as an indexed domain (`count`, `value : Fin count → Int` read in 32-bit, its agreement with the header), the inner
  schema of a nested loop depending on the outer index; `toList` and the bridge to `intRange` (`Param.lean:2586`) as derived views. Master's
  `forFuel2` is a legacy reference only; the new loop meaning must not depend on it. Build the nested `clmul` design from
  `tests/clmul/attacks/proc_nested_for.sv` with retained loops.
- **WS4 (M)**: X3 record-transfer audit (no Lean): for the 7 svGolf records, does the proof expose `Acyclic`, and does it make a procedural
  decision on x? X8 arc-granularity census (pyslang only, on the fetched ibex and cv32e40p sources).

### Day 2 — Wed 11-04

- **WS1**: E-core-0 for continuous assigns: `step`, the executor and `exec_sound`; a `#guard` on a three-assign chain.
- **WS2**: prove `Computes ↔ Computes_obs` for `CombTask`; state `Obs_E` as a signature only.
- **WS3**: **gate G-L0**: the `TripSchema` agreement for the nested `clmul` headers at a symbolic N and on the endpoint cases; then start the
  rows library (`Realizes`, `block_run_iff`, frame), as small as G1 needs.
- **WS4**: X3 report; start X6 (pyslang at several parameter points per census block, against Lean's widths, signs and enum values; one
  batched `#eval` file).
- **WS0**: integration, scoped suite.

### Day 3 — Thu 11-05 — gate G-A

- **WS1**: R-COMB-0, assign-only: legal process-atomic schedules close the slot (rank measure); the closed store solves `CombEqs` and is
  unique. **Gate G-A.**
- **WS2**: the counter `SeqTask` restated over `Obs_run2` (provisional, using `satisfiedAt_of_cycle`, `SeqTask.lean`); a `#guard` showing a
  register-file read-during-write is now statable through the pre sample.
- **WS3**: **gate G-L1**: rows for nested `clmul` (row 0, row k+1, final = row N), by hand; stop rule S3 counts L1 to L3 together.
- **WS4**: X6 report; X9 (operator-table monotonicity by kernel `decide`; list the non-monotone operators).
- **Lead → the maintainers**: short gate note.

### Day 4 — Fri 11-06 — gate G-L2

- **WS1**: add one `always_comb`: a fuel-free, structural body execution (`execBody`, from `evalPure2` and the `symExec` pattern); the
  process-atomic activation.
- **WS2**: draft of Task v2's skeleton `Sat` over an `ObservationModel`, with `CombTask` and `SeqTask` as instances. **Draft only**: it is
  trusted text and needs the maintainers' review before anything uses it.
- **WS3**: **gate G-L2**: the guard lemma over a trip family (`combGuardProc` admits the loop) and totality on shaped states.
- **WS4**: X10 synthesis agreement, first cut: Yosys against the pinned Xcelium traces and today's model, on `unique`/`priority`, self-read
  `always_comb` and attributes.

### Day 5 — Mon 11-09 — week-1 review (G-W1)

- **WS1**: R-COMB-0 with one `always_comb`, single driver, acyclic.
- **WS2**: the counter over observations lands; start the cycle machine D6 over `run2` (`out`, `next`, `init`) for the counter.
- **WS3**: Bridge S for nested `clmul`: the settled snapshot equals `rows N`.
- **WS4**: X10 and X8 reports.
- **Lead**: week-1 report to the maintainers (gates, measurements, adjustments). **Full suite tonight.**
- **The maintainers**: review the Task v2 skeleton draft and the `fdivp` trusted spec.

### Day 6 — Tue 11-10 — gate G-B

- **WS1**: the agreement theorem with `combSettle2` on the E-core-0 fragment; axioms pinned; lines and heartbeats recorded. **Gate G-B.**
- **WS3**: **gate G-L3**: nested `clmul` `Statement` for every N, tactic-free, through Bridge S (label: *provisional over `run2`* until
  R-DESIGN2). Report separately: rows-library lines, guard and totality lines, arithmetic lines, total, heartbeats, `.olean` size, against
  the generate reference (206 lines). That split shows whether the loop route removes plumbing or only moves it.
- **WS2**: cycle machine for the counter; the provisional R-CYCLE over `run2`.
- **WS4**: the two measurements ARCH-NOTE §7 owes before any tier is priced: a census of the symbolic proof path over sv-tests, and an RB82
  re-run after WP-PROC.

### Day 7 — Wed 11-11

- **WS1**: X4, the R-EDGE spike: NBA-only edge processes with async active-low reset; the `Disciplined` predicate; audit `clockExpand` and
  the Xcelium testbenches against it.
- **WS3**: from G1, the list of steps that were tedium; size the loop tactic from that list; automate the first item (the generic-trip step
  equation).
- **WS2**: the contract shape D11 (rely, guarantee, ghost state, arcs, realizability) and `Contract.safety_sound` stated; a `full_adder`
  contract as the first target.
- **WS4**: X2 on the E-core-0 rows (a preemptive choice policy in A's executor; count observations that change).

### Day 8 — Thu 11-12

- **WS1**: R-EDGE spike proof; discipline audit report.
- **WS3**: automation item 1 on nested `clmul`; the proof gets shorter or the item is dropped.
- **WS2**: the composition rule (R-CONTRACT, safety only) for combinational children; `ripple_fa` through the `full_adder` contract, attempted.
- **WS4**: X7 preparation (lens cost per site), or X12 (Std.Do on `execBody`) if A's `execBody` exists.

### Day 9 — Fri 11-13

- **All**: write-ups; the lead merges every branch into a fresh integration branch. **Full suite tonight.**
  - Known merge edits. `arch-loop` × `arch-x1`: `Loop2Slot.sens_of_read` becomes
    `exact Elab.mem_sens_of_raw hp hr (fun W hW => …)`, because `Elab.sens`'s comb arm gained `++ partialSens` in `33dc39c8`.
    The qualifier hypotheses (`qualFree`, `chk = .none`, `hqf`) touch no call site in `c7b56d30`; recheck them at merge.
- **Lead**: week-2 report and the week-3 proposal (sv-0.3 envelope start, R-CYCLE, an R-DESIGN2 slice, the loop tactic sized by G1).

### Day 10 — Mon 11-16 — week-2 review (G-W2)

- **The maintainers**: review; decide week 3.
- **WS0**: land week 2 into `svgolf-prep` and master.

## 4 What the maintainers do, and when

| day | item |
|---|---|
| 0 | relay the codex messages (§5) |
| 3 | read the G-A gate note (go or re-plan) |
| 5 | week-1 review; review the Task v2 skeleton draft; review the `fdivp` trusted spec |
| 6 | G-B result (whether the general E core starts in week 3) |
| 10 | week-2 review; week-3 scope |
| any | approve family-doc proposals (ARCH-NOTE §10.2) if the other lanes agree |

## 5 Messages for the codex agents (the maintainers relay)

**ls-sv.** (1) the maintainers ruled the architecture: `svgolf/design/architecture/ARCH-NOTE.md` on `svgolf-prep` (exact profile semantics E is the
authority; cycle views and contracts are derived, each with a refinement theorem; no fuel in definitions; one AST; `Stmt2` frozen, no new
constructors). (2) Until `Sv.Ast` exists, new constructs stay retained in `PStmt`/envelope form; please add no new lowering and no new fuel
cap. `c64ebdac` is the right direction; the target is the trip list from the header (a `TripSchema`), with no fuel. (3) Proposed split: you
own the extractor's retain-mode twins of today's proof-path rewrites (USERFN inlining, local hoisting, `@*`, net→variable, unrolling) behind
flags, defaults unchanged, plus Xcelium rows for the loop semantics (N = 0, 1, 126, 127, 200, `<=`, descending, `+= c`, nested, shadowing);
our side owns the Lean semantics and refinement theorems. (4) Your recent extractor progress made seven svGolf attack expectations stale; we
are updating them, nothing to do. Before pushing a change to a core Sv file, please run `tools/check_sv_chain.sh` (and `tools/triad.sh`'s new
`--dependents` once it lands). (5) Two tests that looked like yours failed on master on 11-01: `test_let_expressions::test_subroutine_in_expansion_is_not_guessed`
and 13 cases of `test_oracle_disagreements.py` ("25 != 23"). Please re-check them on current head.

**ls-python.** (1) Hosted CI on master has had no green run since 10-22 (the last 40 master runs: 25 failed, 15 in progress). One log
(run 41421627995) shows Lean errors in `LeanModels/Python/PayloadBlind.lean` and a Python step with `failures=13`; the doc says
`PayloadBlind` moved to the sunfish repository. Please check whether that is yours. (2) `docs/family-architecture.md` says Python's
definition is the monadic interpreter, while `docs/python-architecture.md` says every theorem is stated over `Semantics.lean`; could you
reconcile them, and publish one line "theorems are stated over X; the adequacy edge to the definition is Y"? (3) The SV architecture study
proposes three family-level refinements (ARCH-NOTE §10.2): a three-way fuel-placement rule (structural-in-disguise: no fuel; defunctionalized
concurrency or suspension: total step plus closure; direct recursion: the §3.4 index, which Python keeps), trusted statements over an
observation interface, and direction-labelled views (Exact, OverApprox, UnderApprox) in Core. Nothing changes for Python; your objections
are wanted before anything goes into the family doc.

**ls-cpp.** FYI, and objections welcome before anything goes into the family doc: the SV study (`svgolf/design/architecture/ARCH-NOTE.md`
§10.2) proposes that parameters are a ∀-dimension of a definition with no cap or default point leaking into meaning (templates are the C++
case), loops with canonical headers read as folds over a decision list (Std's `Spec.forIn_list`), names as structured data never concatenated
strings, trusted statements over an observation interface, and one shared contract shape (rely, guarantee, ghost state, arcs, realizability).

## 6 Risks to this plan

- **The Lean slot** is the throughput limit. Three Lean-heavy streams plus integration share it. If waits exceed about an hour, the lead
  pauses WS4's Lean items first, then WS2.
- **G-A failing** stops the authority track early by design; the product track continues on `Obs_run2`.
- **Master moves fast.** Merge master into the integration branch daily; never let a workstream branch drift more than two days.
- **Hosted CI is red** and not ours to fix; local checks (`check_sv_chain.sh`, scoped suites) carry the load until it is green.

## 7 Changes after the outside review of this plan (2026-11-02)

Adopted: a formal legal-schedule predicate with a no-skip lemma inside G-A; G-A's acceptance list, including a negative cyclic case and
cost measurements; `TripSchema` as an indexed domain with dependent inner schemas and lists as derived views; G-L split into L0 (loop
domain) to L3 (arithmetic); G-B as the full chain with a negative case; X5's theorem on what the pre sample means; status labels on every
deliverable; E-core-0/1/2 scopes; `Admissible` as policy; the slot policy after and on failure of G-A; per-gate baselines and the
record-keeping rule for changed expectations; the G-L3 cost breakdown.

Held, with the reason: fairness as a separate hypothesis. Legality is permutation-based, as `ScheduleOracle.choose_perm` is today, so no
ready process can be skipped within a region pass; for the acyclic fragment the rank measure then bounds the activations under every legal
schedule (JUDGED). G-A states the no-skip lemma explicitly, and if X1 shows a starvation case under that legality, a fairness hypothesis is
added then.
