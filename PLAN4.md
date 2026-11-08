# svGolf: plan 4, the first sequential milestone and the machinery under it (from Wed 11/04)

History:
- `PLAN.md` was week 1: the framework.
- `PLAN2.md` was week 2: tactics, coverage, tasks, the parametric divider.
- The architecture programme `design/architecture/EXECUTION-PLAN.md` was "plan 3": the exact semantics E, the observation
  interface, loops and measurements. Its Day-9 integration (`integ1103`) is closing now.

**This is the one active plan.** `PLAN.md`, `PLAN2.md` and `EXECUTION-PLAN.md` are history: each has a "superseded"
banner, and their open items are carried into §4.

Revision 2 (11/03 evening) folds in an external review (gpt-6-pro) of revision 1. The changes:
- the plan is phase-gated, and the first acceptance target is ONE vertical slice;
- the transaction contract is frozen before any checker code;
- the clock-step theorem is stated over an explicit schedule class, with negative fixtures;
- the observation transport is stated against a named relation and a declared profile;
- the sorter gets its own stream contract;
- the post-synthesis check is tied to the task specification;
- every gate carries measured artifacts and a fallback.

Conventions:
- Status marks: `[x]` done and verified, `[~]` in progress, `[ ]` open.
- Owners: **A**, **P**, **L** (the architecture agents), the **ls-sv** codex lane, the **lead**.
- Status labels on every task, theorem, checker result and record: *provisional over run2*, *transport theorem*,
  *derived from E*, *trusted statement* (`docs/sv-kernel.md`).
- Estimates are JUDGED; gate reports are MEASURED.
- **Real-world designs first** (decided 11/03): "It's always a good idea to find real world designs (and possibly adapt
  them) rather than building everything from scratch. That's to ensure we can actually support and prove things about
  circuits as people make them today."
  - Every new reference or example starts with a search: GitHub, OpenCores, vendor and university examples.
  - The UNMODIFIED original goes through the source gate, the extractor and the loader. What they refuse is a
    finding for the ls-sv lane.
  - Then it is adapted minimally, with a provenance header: URL, commit, license, kept copyright, and every change
    with its reason.
  - Licenses must be permissive, because svGolf goes public. GPL is flagged.
  - A from-scratch design needs a stated reason.
  - Applied first to the sorter (11/03). Matmul G2 (the systolic array, Gate 5) starts from a real systolic array.
    G1's from-scratch reference stays, because its proof is under way.
- Stop lines are hard: the agent stops AT the line and reports. A missed stop line triggers the gate's declared
  fallback, never an open-ended "in progress".

## 0. Where we start (11/03 evening)

- **Seven combinational tasks are ready**, proved for every parameter against svGolf's v1 statement (*provisional over
  run2*): `_example`, `add`, `mul`, `clmul`, `aes_sbox`, the former 16-bit divider (binary16; `fdivp` at `(5, 11)` since 11/03), `fdivp`.
  - Three of the four accepted records are carried to E (*transport theorems*).
  - Spec reviews owed: `clmul`, `aes_sbox`, `fdivp`.
- **E covers:**
  - E-core-0: assigns and `always_comb`;
  - E-core-1: `always_ff` with NBA;
  - the window-rank R-DESIGN2, which covers the real ibex block.
- **E's exactness is declared for a profile, not claimed for the whole LRM** (`docs/sv-kernel.md`): process-atomic
  execution (`sv-div-4`), and qualified-case reports not deferred (LRM 12.4.2.1; X1-NOTE §13, register row `sv-div-5`
  to land with E's first master slice).
- **Integration:** `integ1103` builds green (all Sv modules, the SV chain, svGolf, every design compile script; MEASURED
  11/03). The per-task suite is partly run.
- **Regression found by the suite:** three references (`add_proc`, `add_proc_m`, `sbox_table`) broke when master
  2218821b added a qualified-case premise to `Terminates2.of_lowerComb_acyclic`. FIXED (`fix-hnq-refs`, merged into
  prep as d0bf45a2). MEASURED 11/03 21:05 by check8 on prep 4caa0d32: the design attacks and the references of all
  seven tasks pass.
- **In flight:**
  - the removal of the former 16-bit task and library restructure (branch `svgolf-fdivp-fold`);
  - `sv_exhaustive` (L, `sv-exhaustive`);
  - the SeqTask/ClockedBy drafts and the always_ff symbolic-N spike (P, `svgolf-seq-counter`);
  - G0 scaffolding (A, same branch);
  - a long-term formal-tools exploration (report only).

## 1. The first milestone (the only blocking target of this plan)

```
Gate 0  reviewed transaction contract (TxTask, SeqTask, ClockedBy) + decision log + fresh-checkout build
Gate 1  G0: the exact pre/post clock-step theorem, over a named schedule class, on a tiny fixture, with negative fixtures
Gate 2  the minimal clocked checker, end to end on the counter fixture (positive and negative submissions)
Gate 3  matmul G1, end to end: spec, reference, proof for all parameters, checker, post-synthesis, off-point checks
```

The status at Gate 3 is recorded on the task as:

```
trusted statement: complete    run2 proof: complete    checker: complete
post-synthesis: complete       E transport: pending (Gate 4)
```

Gates 4 and 5 (§3) follow. Everything in §4 is explicitly non-blocking for the milestone.

**Fallback rule.** If G0's symbolic-N agreement (2c) or the generic transport misses its stop line, G1 ships as a
*provisional over run2* task and E transport moves to Gate 4. The first public sequential task must not wait on the
hardest semantic theorem.

## 2. The gates, with implementation steps

### Gate 0: contract freeze (P drafts, the maintainers review; lead: integration)

**Status 11/04:** `[x]` DONE: the contract is frozen, Day 9 is closed and merged, the arch branches are retired, and the
fresh-checkout build is green (the liberty follow-up is in §3c).

**Earlier status (11/03 late):**
- The drafts are committed (`svgolf-seq-counter` 3cb098c1): `SvGolf/TaskSeq.lean` (a new module, so `Task.lean` and the
  record hashes are untouched until the freeze), `SvGolf/Seq.lean`, the matmul and sorter Specs, `CONTRACT.md` with 7
  flagged interpretation points, and 3 `REVIEW.md` files.
- `CounterTraces.lean`: the contract executable over run2.
- **The plan's top risk is retired for the counter:** `cnt_sem_eq : cntSv.sem N = cntD N` holds for every N ≥ 1
  (877f3b21, 49 code lines, MEASURED).
- **The contract is FROZEN as `txtask-v1`** (11/03, `svgolf-seq-counter` 0473d4d1, after prep was merged in as d6939d88).
  Asked whether to freeze the defaults or review first, the maintainers said: "Don't worry. You choose the order, just keep
  following the plan." So the defaults of §5 stand, as a delegation, not a review: a later ruling is a `txtask-v2` bump.
  The per-cycle overhead is settled by the sky130 ruling (C7).
- Gates 2 and 3 resumed in workflow `seq-milestone-g2g3`: the checker (P1, then P2), the matmul G1 proof (A) and the
  matmul task package run in parallel, then the end-to-end run and a review.
- What is left of Gate 0: close Day 9, and the fresh-checkout build.

**Steps:**
1. **Lead.** Close Day 9:
   - `[x]` finish the per-task suite on `integ1103` in short segments: 73 steps, all green (11/04 00:58, tip 7709398d);
   - `[x]` merge `fix-hnq-refs` (d0bf45a2);
   - `[x]` merge the current prep into `integ1103`, rebuild, and bring it into svgolf-prep: prep 3448322a merged (before
     master c0516458's `Param.lean` regression, since fixed upstream by 92de26d0). `check10` was green on 11/04 02:22:
     build, then every task's design attacks and references. `integ1103` is merged into prep as 097c0431.
   - `[x]` retire the arch branches: the worktrees and branches arch-loop/measure/obs/x1, integ1102m and wprb0 are
     removed, all merged (11/04).
   - `[x]` run a fresh-checkout build (`git clone` + `lake build` + `svgolf/lake build`) and record the result.
     - `check11` (prep 097c0431) found three gaps that built worktrees had hidden, all fixed in `prep-fresh-fixes` and
       merged as e953816c:
       - the sequential modules were built by no standard target: SvGolf.lean now imports every `LeanModels.Sv`
         module a reference imports;
       - a null `goal_arg` broke byte-identical combinational results;
       - matmul's simp set missed master's new concatenation workers (the master change was correct).
     - `check12` (the fixes, a fresh clone) has 50 of 51 steps green:
       - 34 root batches, the SV chain (54 modules, 57 examples), svgolf (122 jobs);
       - every task's design attacks;
       - every task's references.
       The exception is matmul's references row in a clone without the pinned sky130 liberty: a clocked score needs
       it. It passes with the liberty.
     - Also found: master's Python lane does not build from a fresh clone (`PayloadBlind.lean`, `VCTests.lean`). That
       is not ours and was reported to that lane.
     - **Follow-up:** fetch the pinned liberty (sha256-checked) when it is absent. Once the repair step makes sky130
       the ranked score for every task, every task needs it (§3c).
2. **P.** Commit the drafts as text for review, with nothing importing them yet:
   - `SvGolf/Task.lean`: `SeqTask`, `ClockedBy`, `TxTask`;
   - `SvGolf/Seq.lean`: the untrusted reduction lemmas;
   - one `REVIEW.md` per new trusted structure.
3. **P.** Write the contract decisions (§5 C1–C9) into the drafts and into a decision log
   `svgolf/design/sequential/CONTRACT.md`. Include concrete legal and illegal traces for the counter fixture as
   `#guard`s over run2, so the contract is executable before any checker exists.
4. `[x]` **The maintainers** rule on the decisions marked [M] in §5. Delegated 11/03; the defaults stand.
5. `[x]` Freeze the text: the commit tagged `txtask-v1` (0473d4d1). From it on, the checker and the proofs may depend on it.

**Acceptance:**
- the reviewed drafts committed;
- `CONTRACT.md` with every C-item decided;
- the counter traces pass as `#guard`s;
- the fresh-checkout build is green;
- no new `sorry`, `axiom` or `unsafe`, and the axioms baseline is recorded.

### Gate 1: G0, the clock-step theorem (A)

**Status 11/03 late:** `[~]`. Green at `svgolf-seq-counter` 7c5a536a, with 2c on the declared fallback (a per-design
recipe).

| item | what was proved | file and lines (MEASURED) |
|---|---|---|
| clock-step theorem | `cycleStep2_ffOnly` / `cycleStep2_profile` | `Seq2Cycle` 256 |
| schedule class | `WellFormedClockStep`; run2's σ are exactly this class (`wellFormed_choose`); `omitted_process` | `SeqProfile` 334 |
| profile | the decidable `ffOnlyProfileB` with its soundness (`upd_covered`, `ffUpd_disj`) | `SeqProfile` |
| counter fixture | `cnt_sem_clockStep`, `cnt_sem_cycle` for every N ≥ 1 | `CounterG0` 96 |
| negatives | five, pinned | `seq_neg/check.lean` 66 |
| commit lemmas | moved from `Core1Edge` | `NbaCommit` 138 |
| family pieces | `driversOk_of_ff`, `packBV` | `SeqFamily` 108 |

- **Size:** 698 new library lines against the 600 stop, an overrun reported after the fact.
- **Cost:** wall times 6–33 s per file; at most 142k heartbeats per theorem; axioms clean.
- **Source fidelity:** probe points at N ∈ {1, 2, 3, 8} with 0 errors; the counter's pinned Xcelium rows.
- **Open:** `cycleObs2_ffOnly` waits for `integ1103` on prep.

The schedule class is named, not "every schedule". In run2, `cycleStep2` runs every edge process once in an order σ (a
permutation; `choose_perm`), then commits NBAs once. In E-core-1 the legal schedules are the oracle's permutations.

- `WellFormedClockStep σ` is that class: each edge process runs exactly once per active edge, all NBA right-hand sides
  read the same pre-state, and there is one commit point.

**The profile `FFOnlyProfile d`** is decidable:
- every process is `always_ff` on the one declared edge;
- bodies use NBA only (no blocking writes to state);
- targets are static windows;
- distinct processes write pairwise-disjoint windows;
- no process writes an input;
- reset branches are ordinary NBA writes guarded by the reset input (synchronous reset, §5 C1).

**Steps:**
1. `LeanModels/Sv/NbaCommit.lean` [~]: commit order-independence for disjoint windows. It is moved from `Core1Edge`;
   `Core1Edge` must import it when the branches meet.
2. `LeanModels/Sv/Seq2Cycle.lean` [~]: `cycleStep2_ffOnly`. Under `FFOnlyProfile d` and every σ (run2's schedules),
   post = `updateDisjoint pre (fun w => rhs w pre)`, where every right-hand side is evaluated on the SAME pre-state.
   Add `cycleObs2_ffOnly`: the observation interface's pre and post samples are exactly that pre and that post (the
   samples, not merely a normal form).
3. `LeanModels/Sv/SeqFamily.lean` [~]:
   - `driversOk_of_ff`, the one-driver rule for an always_ff generate family;
   - the agreement `design.sem N = ffD N` at symbolic N for always_ff generate families (2c; P's `CounterInst` spike
     feeds it);
   - `packBV` and its read-back lemmas.
4. **Negative fixtures** (`Examples/system-verilog/seq_neg/*`), each refused or failing for its stated reason:
   - a process reading a window it writes with a blocking assignment;
   - two processes with overlapping windows;
   - a blocking assignment in an `always_ff` body;
   - a reset branch outside the profile (asynchronous);
   - a two-process dependency cycle through blocking temporaries;
   - a schedule that omits a process. This last one is a theorem: `¬ WellFormedClockStep σ` gives no conclusion; it is
     not an SV fixture.
5. **Tiny fixture:** the counter instantiated through steps 2–3, at symbolic N, replacing its hand-built `cntD`
   agreement (today `#guard`s at 7 points).
6. **Source-fidelity evidence** for the fixture: the extractor's multi-point probes (`--probe-points`) at N ∈ {1, 2, 3, 8},
   and the counter's differential rows in `harness/sv` (Icarus, plus Xcelium where pinned).

**Acceptance:**
- steps 1–5 build;
- the negative fixtures behave as stated;
- MEASURED lines (split: commit lemmas / cycle theorem / family agreement / fixture), heartbeats per theorem, `.olean`
  sizes and `#print axioms`.

**Stop line:** 600 lines of library code; 2c alone stops at 250 and reports. **Fallback:** if 2c misses, Gates 2–3
use per-design agreement proofs (the counter's existing route) and 2c moves to Gate 4.

### Gate 2: the minimal clocked checker, on the counter fixture (P)

**Status 11/04:** `[x]` DONE (`svgolf-seq-counter` ec32654b, ef1e4078, 239e294b, 16dc08c0; 899 of 1,200 lines).
- check.py's kinds `seq-family`/`tx-family`: the latency header, the generated goal `Statement design.sem lat ∧ lat p₀ = n`
  (Comparator `--goal-arg`).
- The clocked source-gate rules, with 12 refusal fixtures. The loop-index rule is being narrowed (workflow
  `clocked-gate-loop-index`).
- Scoring per C7: sky130 µm² and time = cycles × the register-to-register period; two clean exports are byte-identical.
- The clocked post-synthesis check with binding checks (i) and (ii).
- MEASURED: the proved counter is accepted through every stage. The 9 negatives fail at their expected stages.
- Matmul G1 scores 87,101 µm², 48,079 ps at (4,8,32). That is ~790 ps per level, which looks suspicious; it is being
  investigated in Gate 3.
- The sorter's `stream-family` kind: landed 11/04 (9584c55f); the sorter is end to end (Gate 5).

**Steps:**
1. `check.py`:
   - kind `tx-family` (and `seq-family` for SeqTask fixtures);
   - parse `-- svgolf-latency:` and the latency definition the proof file exports;
   - generate the goal `Statement design.sem lat ∧ lat p₀ = n`;
   - record `latency`.
2. **Source gate rules for clocked kinds:**
   - exactly one clock;
   - one edge;
   - synchronous reset only;
   - no `initial`, no declaration initializers on state, no `always_latch`, no `negedge`, no delays, waits, forks or
     extra event controls;
   - no blocking assignment in `always_ff`.

   Combinational feedback stays with the existing loader checks. Each rule gets a refusal fixture.
3. **Scoring:**
   - `score/svgolf_seq.ys` = the comb flow + `dfflegalize -cell $_DFF_P_ x -cell $_SDFF_PP0_ x …` (the exact cell set
     follows C1);
   - `score/ge_seq.json` with sky130-ratio flop prices;
   - depth = Yosys `ltp -noff` over the synthesized netlist: the longest combinational path between any two of {input
     port, flop Q, flop D, output port}, in gates;
   - time = n × depth;
   - pinned Yosys/ABC versions, and the hashes of both files in every record. Same inputs → same score (checked by
     running twice from clean checkouts).
4. **Clocked post-synthesis check** (`score/postsynth.py --tx`, `svgolf-eval --trace`):
   - Verilator netlist with randomized initial state (several seeds);
   - the exact sequence: random state → reset asserted for R cycles (C1) → reset released → idle cycles →
     transactions from the task's generator (`oracle.py`: `txns(params, seed)`) with back-to-back and gap cases.
   - **Binding checks:**
     - (i) the netlist vs ls-sv cycle by cycle, on `done` every cycle and the payload in cared positions;
     - (ii) the netlist's cared outputs vs the task's own transaction evaluator (`oracle.py`'s `good`, reviewed with
       the spec).

     Either failing rejects; (ii) catches a bug shared by the candidate and ls-sv.
   - Latency: the first done at or before n (C3); x/z in a cared position or in `done` after reset → reject.
   - The record logs, per transaction: reset cycles, the start cycle, the first done cycle, the sample cycles, the
     hold interval.
5. **Tests:**
   - positive: the counter fixture through every stage;
   - negatives, each at its expected stage: wrong latency, late done, wrong payload, x in a cared position, start
     ignored, `initial` block, async reset, two clocks, initializer;
   - plus `tests/run.py` support for the kind.

**Acceptance:**
- the counter fixture passes every stage;
- every negative fails at its expected stage;
- two clean runs give byte-identical scores;
- MEASURED stage times.

**Stop line:** 1,200 lines of Python and tests before the counter passes end to end; then report.

### Gate 3: matmul G1, end to end (P spec and checker; A reference and proof)

**The architecture is chosen now:** N² parallel MACs and one k counter.
- Each accumulator `acc[i][j]` adds `A[i][k]·B[k][j]` at cycle k, reading the held A and B by dynamic part-select.
- C is the accumulator array itself, with no dynamic writes.
- Latency is N: `done` first shows in the snapshot N cycles after the edge that samples `start`. That is MEASURED and
  proved; the plan's first figure, N + 1, was a valid but looser bound.

This architecture exercises generated array families, so G0's 2c is tested, and its invariant is short:
`acc[i][j] = Σ_{k' < k} A[i][k']·B[k'][j] mod 2^AccW`.

**Steps:**
1. **P:** `tasks/matmul/Spec.lean` per §5 C6, `task.json`, `oracle.py` (transaction generator plus `good`),
   `README.md`, `REVIEW.md`. The maintainers review the spec.
2. **A:** `tasks/matmul/reference/matmul_g1.sv` (one module; generate over (i, j); FF-only; synchronous reset).
3. **A:** `tasks/matmul/reference/matmul_g1.lean`:
   - G0's agreement and cycle theorem;
   - the invariant by induction on k;
   - the latency function `lat N = N` (it was `N + 1` in the first draft);
   - `Statement`.

   The spec side uses core Nat/Int sums (no Mathlib in the task cone).
4. **A and P, attack designs** (`tests/matmul/attacks/`), each correct-looking, wrong for some N/W/AccW, and each must
   fail the reference proof: off-by-one k, unsigned instead of signed product, missing sign extension, done one cycle
   early, accumulator not cleared on start, AccW truncated to 2W.
5. **Off-point checks:**
   - the extractor's probe points at (N, W, AccW) ∈ {(1,1,1), (2,3,5), (3,4,8), (4,8,32)};
   - post-synthesis also at (2, 4, 8) beside the scoring point (4, 8, 32);
   - the universal theorem makes point-specialization unprofitable but legal (a design may special-case N = 4 if it is
     still correct for all N).
6. **Measured report:**
   - lines, split into the plumbing reused from G0 / the invariant / the Nat arithmetic / the statement glue;
   - elaboration time and heartbeats per theorem;
   - `.olean` size;
   - the generated equation count;
   - the synthesized trace length;
   - axioms;
   - the score at the scoring point.

**Acceptance:** `check.py` accepts the reference; every attack fails at `solution`; the task is `ready` with the
status block of §1.

**Stop line:** 600 lines for the G1 proof on top of G0. **Fallback:** the per-design agreement (Gate 1 fallback).

**Status 11/04:** `[x]` DONE. On svgolf-prep since 13e5c1f8 (the merge of `svgolf-seq-counter` at ecf65c13).
- `check.py` accepts `tasks/matmul/reference/matmul_g1.lean` (1c17536f): `lat = N`, header 4, the generated goal
  `Statement design.sem lat ∧ lat 4 8 32 = 4`. Solution stage 8.6–9.6 s cold, 176.6k heartbeats for the whole
  file (none above the default limit), clean axioms. The generic TxTask reduction
  `SvGolf.TxTask.satisfiedAt_of_phases` is in `SvGolf/Seq.lean` (7eb67caf, +248 lines). The review proved it is not
  vacuous: no PhaseModel exists for a toy that raises done early.
- Attacks (ecf65c13): the six of step 4 are all rejected at solution, and each is also wrong at post-synthesis.
  Off-points: extractor clean at the four probe points; post-synthesis 0 failures at (2,4,8) and (4,8,32).
- Score at (4,8,32): 87,101 µm², time 4 × 48,079 ps, 802 flops (GE 20,783, depth 61). Under `sky130_a0_v2` (11/04, the
  netlist repaired by buffering only: 5 buffers on 5 nets): 87,173.6064 µm², time 4 × 10,705 = 42,820 ps.
- **Accepted overrun:** 964 lines (766 of code) against the 900 stop line. 192 of them are design-independent lemmas
  (`win_*`, `overlaps_comm`, `ffDisjB_of_pairwise`, `flatMap_ffUpd`, `insertAt_full`, `shr_ofBitVec`, …). They
  move to `LeanModels/Sv` (SeqFamily) or `SvGolf/Seq.lean` before the sorter proof, which needs the same ones.
  Without them the matmul part is 772 lines.
- **Scoring finding (MEASURED):** the 48,079 ps period is NOT the datapath. It is three cells: the busy flop (fanout
  198), then NOR(busy, start) driving 360 pins, then NOR(rst, ·) driving 257. All are unbuffered `_1` cells at up to
  9.7× max_capacitance, so the NLDM tables are extrapolated far out of range. With loads capped at the table's edge,
  a what-if puts the period at 10,648 ps over a 60-cell path. A0′ does no buffering or sizing, so its delay ranks
  control-net fanout. This bears on the ranked metric for every task [M]; see §3c.
  **Resolved 11/04 ("Please add the repair step everywhere (buffering). Also feel free to outright reject designs
  from golfers that produce illegal netlists"):** `sky130_a0_v2` weighs every task's A0′ netlist after a repair by
  buffering only (balanced buffer trees on every net over its driver's limits, inputs, flop Q nets and output bits
  included; replicated tie cells; nothing resized) and rejects a netlist the repair cannot make legal; matmul's period is
  10,705 ps and the 4.4× flop-duplication shortcut now loses (43,560 against 42,820 ps; score/PPA.md, "The repair and the
  legality check").

**Earlier status (11/03 late):**
- **The task package is done** (a3ab2487): task.json (`tx-family`), oracle.py (`txns`, `good`; self-test, 7 oracle
  mutations caught, byte-identical across CPython 3.9/3.12/3.15), README and REVIEW.
- **The proof stopped at the 600-line line** (d7c654ea, `matmul_g1.partial.lean`, 564 lines; MEASURED 8.3 s wall,
  default heartbeats, clean axioms). Proved at every N, W, AccW ≥ 1:
  - `mm_sem_eq`: the loaded family is the hand-built design (2c worked; no fallback);
  - `mm_profile`: FF-only at symbolic N;
  - `mm_cycle`: one cycle is G0's clock step;
  - `pe_step`: the invariant step on k;
  - `product_eq` / `accC_N`: the spec's product.
  JUDGED: about 200 lines remain (the start/hold/reset steps, the trace invariant and `Guar`, Interface and ClockedBy,
  the assembly).
- 11/04: the finish runs in workflow `seq-gate3-finish`: the library lemma, then the proof at `lat = N` with a matmul
  stop line of 900 (the 2c agreement alone took 267 lines), then end to end, then a review.
- **Decision on the stop line (lead):** the remainder is transaction-protocol plumbing that every `TxTask` reference
  repeats. It goes into the untrusted svGolf library `SvGolf/Seq.lean` as ONE generic lemma, stop line 300: from a
  per-cycle step, a busy invariant, the done/hold conditions and the reset step to `Statement`. The sorter's
  `StreamTask` gets the analogue later. The matmul file's own lines keep the 600 line. This follows the maintainers'
  rule: a general library, never a per-task one.
- **Latency finding** (task-package agent, MEASURED in simulation): the reference raises `done` exactly N cycles
  after the start edge, so `lat = N` would hold and score 4 instead of 5 at (4, 8, 32). The proof states
  `lat = N + 1`. Tightening it is a follow-up for the proof, if cheap.


## 3. After the milestone

### Gate 4: observation and transport (A)

**Steps:**
1. **The observation relation**, stated once for the flop-only profile: traces of input valuations per cycle; samples
   pre = after inputs and settle before the edge, post = after the NBA commit; clock hidden (decided 11/03); reset cycles
   included as ordinary inputs; knownness projected.
2. **G3:** `FFOnlyProfile d → Behaviours(Obs_E1, d) ⊆ Behaviours(Obs_run2, d)` off the clock. It is NAMED a soundness
   inclusion: it transports safety statements and is not an equivalence.
   - The converse direction (run2 → E on typed stimuli) is stated as a separate open item.
   - For the comb profile the equivalence `computes_iff_computes_obs` already exists.
3. Instances: the counter and matmul G1, so both are carried to E as *transport theorems*.
4. Source/load/design regression: G0's mutation fixtures re-run against E.

**Stop line:** 400 for the generic theorem; about 100 per instance.

### Gate 5: breadth

- **G2, the systolic matmul (A):** an output-stationary N×N array, FF-only, skew inside the always_ff bodies.
  - The invariant with explicit bounds, writing m(t,i,j) = t − i − j:
    - PE(i,j) holds 0 for t ≤ i + j;
    - Σ_{k < m} A[i][k]·B[k][j] for i + j < t ≤ i + j + N;
    - the full sum for t > i + j + N;
    - the pipeline registers hold A[i][t−i−j] when 0 ≤ t−i−j < N, else 0.
  - Done at t = 3N − 2, or per the reference's skew, with a lemma stating the exact sampling cycle.
  - Stop at 900. Same attack and measurement requirements as G1.
- **G1 revision: size the step counter** (raised by the maintainers' look at the 2×2 schematic, 11/04).
  - G1 declares `logic [31:0] k` whatever N is. Sizing it as `[$clog2(N+1)-1:0]` (it counts to N) is a better design.
  - MEASURED at 2×2, W = 2, AccW = 4: 473 → 251 cells, 66 → 36 flops, 3,782 → 2,043 µm². At W = 1, AccW = 2: 289 → 86
    cells.
  - It keeps G1's structure: N×N MACs fed by two shift registers, not a systolic array. That is G2 above, which is what
    "looks like an array" in the strict sense.
  - Proof: the invariant on `k` and the `c32_nat`-style width facts change from 32 bits to the parametric width. The
    statement does not change.
  - Do it after the library quality pass lands, since that pass is renaming those very lemmas.
  - Display: the detail page draws matmul at (N, W, AccW) = (2, 1, 2) or (2, 2, 4) as a BLOCK VIEW, an N×N grid of MAC
    blocks with the two shift registers and control, and each block expands to its gates. A flat layered gate drawing
    loses the array.
- **The sorter (L, after `sv_exhaustive`):** under its own `StreamTask` (§5 C8), with an insertion-array reference
  that reuses G0.
  - `[x]` 11/03, **reference design and task package** (`svgolf-seq-counter` 35c9b3a7, no Lean).
    - Adapted from the real-world `andrewpeck/cell-sort` (MIT, cfc46709), an insertion cell array. The header keeps
      its provenance and lists every change: C8 ports, cells inlined into one flat generate family, FF-only, a
      streaming drain, a valid-token delay line.
    - lat = 2N, attained in every transaction.
    - MEASURED: Icarus at 8 points from (1,1) to (8,8), with resets mid-stream. The source gate (with the clocked
      rules), the banlist and the extractor all pass, the extractor with 0 Unsupported. ls-sv loads it in the
      FF-only profile at 9 points.
    - Score with the sequential flow at (8,8): 1288.8 GE, 81 flops, depth 15.
    - 8 mutants fail. The tie-order mutants are invisible, because equal values are interchangeable; keep them out of
      the attacks.
    - The proof needs, from G0:
      - three process shapes;
      - a family loop that runs zero times at N = 1;
      - last-write-wins for the reset;
      - the invariant stepped by `tail ∘ insertAsc`;
      - `sortAsc (reverse xs) = sortAsc xs`.
    - (Was open: check.py's kind `stream-family` and run.py's layout step; both landed 11/04, below.)
  - `[x]` 11/04, **end to end, as Gate 3 did for matmul** (branch `svgolf-sorter`). Status on the task:
    `trusted statement: complete · run2 proof: complete · checker: complete · post-synthesis: complete ·
    E transport: pending (Gate 4)`.
    - The library first: matmul_g1's design-independent lemmas moved to `LeanModels/Sv` (10b06ded; matmul_g1
      966 → 746 lines), and the stream reduction `StreamTask.satisfiedAt_of_phases` (C8) in `SvGolf/Seq.lean`
      (ab9151c1, +300 lines, the stop line; not vacuous: a toy that emits one value early has no phase model).
    - `check.py` kind `stream-family` (9584c55f): latency header, goal `Statement design.sem lat ∧ lat 8 8 = n`,
      the clocked stream check in post-synthesis.
    - The proof `reference/sorter_ins.lean` (039c2162, 899 lines against the 900 stop line; SeqFamily +103
      generic lines): every N, W ≥ 1 at `lat = 2N`. MEASURED: `check.py` accepts it with the clocked score,
      solution stage 7.2–7.6 s in three cold runs (`score/time_limits.json`), 123.3k heartbeats for the whole
      file (21.1k the largest declaration), `.olean` 12.9 MB, 739 generated equation lemmas, clean axioms.
      Lines: agreement 214, one cycle 333, the sort 107, the invariant 56, phases and statement 189.
    - Off-points: the extractor at the eight probe points (1,1) … (8,8), 0 frontend errors (at N = 1 the
      zero-instance loop body is kept as source, `GenerateFor:no-template`; the proof covers N = 1);
      post-synthesis full at (3,4) and (8,8), 0 failures over 3 seeds × 24 transactions (195–224 and
      448–479 cycles), every transaction at its latency (6, 16).
    - Score at (8,8): 5512.79 µm², 16 × 2510 ps = 40,160 ps, 81 flops, 713 cells (GE 1288.8, depth 15).
    - Attacks (`tests/sorter/attacks/`, 7): each rejected at solution and each wrong at post-synthesis
      (`--unproved --latency 16`). Two of the designer's seven wrong mutants could not serve: the loop bound
      `k < N-2` is refused at `fourstate` (undriven bits) before any proof, and the early-`out_valid` index
      gives a `1'hx` netlist constant; `token_self` and `early_valid` replace them. The two tie variants
      are correct designs and stay out. Refusal register: `sg-stream-guar`.
    - `tests/run.py --only sorter`: layout 25/25, references 5/5 (accepted, full post-synthesis 612 and 1405
      cycles, 0 failures, the score pinned in `tests/expected.json`), attacks 7/7; `gen_sv_refusals.py --check`
      ok; `time_limits.py --check` ok.
  - **Real-world refusals, MEASURED on five open-source sorters** (finding for the ls-sv lane):
    - **unpacked arrays**: ports, nets, variables and assignment targets. Every candidate hits this; it is the top
      refusal.
    - a `for` loop inside `always_ff`: the source gate reads its index as a blocking assignment;
    - asynchronous reset;
    - module instances inside loop-dependent generate-if;
    - unsized `'b0` port connections;
    - named generate blocks around loops;
    - `initial` blocks, and `priority case`.
  - The frozen `Spec.lean`/`TaskSeq.lean` still carry "DRAFT … for review" headers. That is cosmetic, and
    removing them waits for `txtask-v2`.
- `sv_seq_equations`, from G0's template once two designs have used it.
- **`sv_exhaustive` acceptance:**
  - the evaluator's soundness against the actual generated design;
  - its x/knownness policy;
  - first-counterexample reporting;
  - heartbeat limits;
  - mutation tests that reject a wrong S-box.

## 3b. The website (parallel track, 11/03: "make sure to build the website itself")

svGolf has the data a site needs: task manifests, trusted specs, references and baselines, the leaderboard's records
and Pareto frontiers, the proving guide. It had no site.

- `[x]` **W1, the generator** (branch `svgolf-site`).
  - 22d01898: the generator. 140 files, 32 pages, about 0.9 s; byte-identical rebuilds; 33 tests; 12 independent checks
    pass.
  - f0f9f52d: the newcomer fixes, 50 tests:
    - the local-only submission path until a repository exists;
    - honest post-synthesis wording (sampling, not proof);
    - references shown as par, not ranked;
    - curated public text instead of internal notes, with a denylist that fails the build on leaks;
    - short task titles.
  - Residue before going public: PROVING.md's work-package codes (`proving.html` is an allowed exception) and comments
    in byte-identical reference downloads. Clean those at W3.

  The original W1 scope: `svgolf/site/build.py`, standard-library Python like
  `leaderboard.py`, writes a deterministic static site to `svgolf/site/_out/` (git-ignored). It has:
  - a home page;
  - one page per task: plain-language statement, ports, parameters, the trusted Lean statement verbatim and
    highlighted, the reference and baselines, the Pareto frontier as inline SVG, the records with provenance and
    assisted-by, the attacks the checker rejects, how to submit;
  - rules and scoring, the proving guide, a roadmap.

  No external scripts. Tests in `svgolf/tests/site/`.
- `[ ]` **W2, a private preview** for the maintainers, as a Claude artifact.
- `[x]` **W3, hosting and going public. PUBLISHED 11/05 09:17 CET** (decided 11/05: "Please make it public as soon as
  you can"): https://github.com/thomasnormal/svgolf, main = export v4 (7ec90a09, pin c1c06b1e, round 4's review
  clean), Pages from GitHub Actions at https://thomasnormal.github.io/svgolf/; the pages and unit workflows passed on
  the first push. Later rounds ship as ordinary commits on top (round 5: the detail pages, the re-seeded records).
  The maintainers chose: a public repo `thomasnormal/svgolf` with GitHub Pages, "site
  + scrubbed source now". 11/04: the prerequisites are in place: every `LeanModels/Sv` module svGolf needs is on
  lean-surfaces master (the seven slices), and energy and the repair are merged. Workflow `svgolf-publish-prep` (branch
  `svgolf-publish`):
  - the site merged;
  - layout-independent paths;
  - `tools/export_public.py`, an export of svgolf-prep with fresh history (svgolf/ as the root, the neutral-attribution
    rules, a generated standalone lakefile pinned to a lean-surfaces master rev, LICENSE/NOTICE, the Pages workflow).
    The export and its scanner are development-only tooling and are not in the public tree;
  - a name-free scanner;
  - a dry-run export built from a fresh clone and scanned, then an independent review.
  Round 2 (11/04): a source scrub (`svgolf-scrub`: neutral attributions, no local paths), and the export INCLUDES the planning
  docs, design notes, review notes and studies (decided 11/04: "it might actually be fine to keep planning docs, as
  long as they don't have sensitive information. It'll help others contribute."); it drops only development-only
  tooling. Then: the export is re-run on a pin whose refusal register carries the scrub, the repo is created, main is
  pushed, and Pages is enabled.
- `[ ]` **W4, the sequential tasks' pages** (matmul, sorter: latency, time = cycles × period, protocol diagrams) when
  Gate 3 lands.
- **THE FOCUS NOW (decided 11/04): "Let's focus on getting the site working well on a few high quality tasks first."**
  The order, each step checked in a browser at desktop and phone width:
  1. `[x]` **The redesign** (`site-redesign`, branch `svgolf-site-charts`), merged into prep as 861c5670 (11/04):
     - the zk.golf-like design system;
     - the area × time score (`leaderboard/combined.py`) with its chart and the x-y explorer;
     - the trusted statement as property cards, each task's `Properties.lean` proving `statement_iff_properties`;
     - light-theme contrast to WCAG AA (the lead's fix after the review);
     - 70 site tests, byte-identical builds.
     Open: clmul, `_example` and four references have no sky130 measurement (add them to `score/tests/ppa/designs.json`);
     reference dates come from git history, which the public export's fresh history loses (store a date per
     reference); matmul and the sorter stay hidden until the scrub lands.
  2. `[x]` **One scoring story everywhere:** the ranked-board switch to A0′ (leaderboard.py, README, site) after ppa v3,
     plus the "Reproduce a score" page. Landed with ppa v3 (prep 8be44458, 11/04).
  2b. `[x]` **Measured at several points** (workflow `site-multipoint`, branch `svgolf-points`; on prep 11/05,
     c94d604e). The points live in one untrusted config file, not in task.json (a trusted file), and the scored
     point's numbers must equal the goldens bit for bit, by test. (decided 11/04: "Maybe it would be interesting to score tasks at multiple points
     (not just N=16) and make the alternative parameters available in the 'Compare the designs' plot").
     - Every proof already holds for every N, so this is measurement only.
     - Each task's points (in `score/points.json`; the scored one is task.json's): add 8/16/32/64; mul and clmul
       4/8/16/32; matmul (2,8,32)/(4,8,32); the sorter's N values; fdivp binary16 and binary32 if the Newton reference fits the
       time budget; aes_sbox is fixed.
     - The flow is the same pinned flow at each point.
     - Data: references and baselines are measured at every point into a points file the site reads. A golfer's record
       gets its extra points from the site build or a nightly, not the checker (cost ×k), and they are always shown
       as measured, not ranked.
     - Explorer: a point selector (N = 8, 16, 32, …) and a scaling view (any metric against N, one line per design),
       which shows where an adder's architecture starts to pay off.
     - The ranked board stays at the scored point. Ranking at several points (the ISPD-style rule in §3e) is a
       separate call for the maintainers.
     - Order: after ppa v3 lands, since its input drive changes every number.
     - `[x]` Built 11/05 (branch `svgolf-points`; score/PPA.md, "Measured at several points"). The points live in the
       untrusted `score/points.json` (task.json untouched); `score/points.py measure` writes `score/measured/<task>.json`,
       equal to the goldens bit for bit at the scored point (`score/test_points.py`); the explorer's point selector and
       scaling view (score over par's at each point by default). Dropped: `fdivp_newton` at binary32 and `dadda_ks_32`
       (over the 120 s limit). OPEN: the four references and clmul's baselines without a golden still show no sky130
       number at the scored point (their measured numbers are in the data).
     - fdivp_srt measured after it landed (11/05): bfloat16, binary16 (equal to its golden) and binary32. Its binary32
       run took 104 s against the 120 s limit, so a re-measure under load can drop it; pin it in points.json if that
       happens.
  3. `[x]` version 1, on prep 11/05 (workflow `site-detail-pages`, branch `svgolf-detail`): 18 pages, every record and
     every reference without one (`tasks/<t>/reference/<stem>.html`): the three cards, the area-time plot, the
     schematic of a labelled display instance (`site/gen_schematics.py`, netlistsvg 1.0.2 pinned, committed SVGs,
     740 kB), the critical path node by node (`ppa.py --path` gained arrival and transition; no scored number moved),
     cells, sources and proof, reproduce; fdivp's and aes_sbox's reference records seeded. `[ ]` OPEN: layouts
     (place-and-route on a Linux host, a cache outside the tree). The five older records were re-seeded after
     `ppa.py --path` changed the checker's fingerprint (f9ece217: same scores and files).
     **Detail pages for every record:** the schematic at a small display instance (the block view for arrays), the
     layout, the critical path, the source, the proof stats. Matmul gets the sized-counter revision.
     - Decided 11/04, of Logicode's result view: "This little dashboard with Area, Performance, and PA-plot is quite
       nice."
     - So the top of every detail page (and the local checker's result view) gets the same three panels:
       - an Area card (sky130 area, cells, flops; GE as an extra);
       - a Performance card (delay, or cycles × period);
       - each card with "beats X% / matches Y%" over the task's ranked records;
       - an area-vs-time plot with this record highlighted among the records, references and Pareto front, zoomed to
         the cluster, with counters for points beyond the view.
     - Spec and prototype: workflow `logicode-scoring`.
     - Version 1 built 11/05 (branch `svgolf-detail`): a page per record (`tasks/<t>/records/<hash>.html`) and per
       proved reference without one (`tasks/<t>/reference/<stem>.html`), 18 pages: the three cards
       (site/standing.py: the field is the other players' ranked records, empty today, so every page reads
       "Beats – · matches –"), the area-time plot (fitted to the cluster, counters beyond the view, par's score curve),
       the schematic at the display instance, the critical path with per-node arrival and transition (`ppa.py
       --path`'s new `critical_path_timing`; no scored number changed, test_ppa.py unchanged), the cells, sources,
       proof, reproduce. The schematics are generated once and committed (site/gen_schematics.py, netlistsvg 1.0.2
       pinned with a lockfile, site/schematics/display.json: add/mul/clmul/_example at N = 4, fdivp at W = 3, P = 3,
       aes_sbox its critical path; 0.74 MB of SVG for 16 designs, byte-identical reruns by test); the site build
       only reads them. A reference without a golden now takes its measured numbers at the scored point
       (score/measured), which closes 2b's OPEN item for the references (add_proc, add_proc_m and add_mux; clmul's
       baselines still show none).
     - The layout (PAGE_DESIGN section 5) is deferred: it needs place-and-route on a Linux host and a cache
       outside the tree.
     - Checked in a browser (11/05: add, mul, fdivp_srt, fdivp_newton and aes_sbox at 1280 and 390 px, light and
       dark, script on and off; numbers checked against the records and the goldens; task pages unchanged but for
       the documented additions). Fixed: the critical path now links into the drawing (the display instance's path
       listed under the table, or the table's own instances where the drawing is the scored netlist); the zoom
       keeps the view's centre and has 1:1; a cell finder; the critical path stays visible when the drawing is
       shrunk; without the script a drawing is shrunk to its box instead of showing a blank corner; each drawing is
       offered as a file of its own; aes_sbox's path drawings mark the path's own nets; "1 buffers".
  4. `[~]` (11/05: fdivp has three proved references and aes_sbox two, with records seeded; add's five references are
     one ripple architecture, so a proved Sklansky parallel-prefix adder is in progress, branch `svgolf-sklansky`.
     The natural source hits two comb-tactic walls (a conditional generate inside a loop; the partner index
     `((i >> l) << l) - 1`). Decided 11/05: make the tactics more robust, never rewrite a design around them; asked of
     ls-sv (guarded generate families; nonlinear genvar indices as named obligations). Meanwhile workflow
     `sklansky-math` proves the general prefix-scan lemma (Lib) and the Sklansky recurrence core; the glue follows.)
     **Featured tasks made excellent:** add, mul, aes_sbox, fdivp, matmul and the sorter. Each needs:
     - a curated plain-language page;
     - at least two references;
     - its attacks explained;
     - its records seeded under the current `ppa_version`. `[x]` for fdivp (fdivp, fdivp_srt, fdivp_newton) and
       aes_sbox (sbox_bp, sbox_table), 11/05, `sky130_a0_v3`, full post-synthesis check; `leaderboard.py verify`:
       10 records, 0 failed, 0 stale.
     clmul and `_example` stay, but are not featured.
  4c. `[x]` (on prep 11/05, all 52 pages, light and dark, 1280/768/390 px, 202 colour pairs AA, 140 site and
     points tests) **The pixel theme** (decided 11/05, from a sheet of six playful concepts: "Let's go with 8772. It's
     most distinctive", concept #1 'Pixel Golf Course'): a pixel-art golf world with a retro game feel across every
     page, light and dark, phone width, AA contrast (workflow `site-pixel-theme`, branch `svgolf-theme-pixel`).
  4b. **PUBLICATION BLOCKER: the clocked statements do not yet cover the outputs on the wire and unknown values at
     reset (11/04, MEASURED by a soundness probe).** The fix is a revision of the trusted text (`txtask-v2`), which
     the maintainers rule on. Until then matmul and the sorter are listed as previews, not ranked: no par, no record
     tiles, no ranked board.
  5. `[x]` **Publish (W3)** (11/05), then iterate on what visitors hit.

## 3c. PPA: power (parallel track; requested 11/03: power and other standard metrics)

- `[x]` **Energy columns**, landed 11/03 on `svgolf-energy` at 8238fea0: `score/energy.py`, 398 lines with tests;
  byte-identical across runs; 0.5–4 s per design.
  - **add:** both energies rank like area.
  - **mul:** activity energy is an area proxy, but glitch-aware energy is not (τ = −0.24 against area). The array
    multiplier is 2nd in area and last in glitch energy (glitch factor 4.66, against 1.7–1.9 for the trees); `dadda_rc`
    is best on both.
  - **The counter:** the clock dominates (N = 16: 927 fJ per cycle, 637 of it the flop clock pins).
  - Next for P: sequential sky130 timing in `ppa.py`.

  The original scope:
  - `energy_activity_sky130_v1`, `energy_glitch_sky130_v1` and `leakage_sky130_v1`, plus per-transaction energy with
    the clock pins for clocked flows;
  - all EXTRA and unranked, from the sky130 liberty;
  - stimulus: a public seed plus salted official seeds;
  - the design is `design/ppa/metrics.md` §2, and the 10/30 spike measured glitch factors of 4.5 (array multiplier)
    against 1.7–1.8 (trees);
  - stop at 400 lines.
- `[ ]` FPGA columns (LUT, FF, DSP, BRAM, fmax; Yosys-only).
- `[ ]` Combined normalised presets (area × delay, energy × delay).
- `[ ]` Physical-design columns (OpenROAD, Linux, a nightly on a Linux host).
- `[~]` Per-solution detail pages (decided 11/04): clicking a solution, reference or golfer's, opens a page with its
  schematic, its placed and routed layout, and the rest (source, proof stats, energy). The study is
  `physical-track-study`.
  - **RULED 11/04: draw a SMALL instance, not the scored one.** "For multiplication, maybe do N=2 or N=4. So
    not the same version as we use to score. That just makes it easier to see what's going on."
  - So each task names a display instance (multiplier N = 2 or 4, adder N = 4, matmul N = 2), and the page renders the
    same design at those parameters (Yosys `chparam`) through the same flow as scoring.
  - The page labels it ("drawn at N = 4; scored at N = 16"). The numbers on the page stay the scored ones.
  - A design that does not elaborate at the display instance gets the next size that does, or no picture; it is never
    refused for that.
  - **Study done 11/04** (`physical-track-study`; notes and the prototype in the session scratchpad `phys/`, to be
    committed under `design/physical/` with the build):
    - The schematic is netlistsvg with an svGolf sky130 skin (netlistsvg's own skin draws `nor2b`/`nand2b` wrongly),
      0.7–2.3 s.
    - The layout is OpenROAD-flow-scripts in its public Docker image, pinned by digest, placing and routing the display
      instance's repaired netlist. It takes 23–38 s per small instance and is deterministic (byte-identical DEF on
      repeat and across thread counts).
    - The add at N = 8 reads well in full.
    - The matmul at 2×2 is still a 473-cell tangle: its 32-bit step counter dominates. So pages also draw the critical
      path with its neighbouring nets (15 cells), and the drawn critical path can differ from the scored one.
  - **Decided (lead, 11/04):**
    - R2: pages are information only; no layout number ranks.
    - R1: a Linux container image, published by digest, becomes the scorer of record, gated by G1. G1 requires
      identical banner-free hashes and `ppa` blocks for the 19-design battery on two x86 machine types and under Mac
      emulation.
    - Why R1: a native Linux build of the same Yosys commit moves fdivp and matmul by under 1%, and `brew` now installs
      Yosys 0.70, not the pinned 0.53. Without the image, "reproduce a score" cannot be promised.
  - **Order:**
    1. `ppa-v3` (input drive).
    2. The ranked-board switch to A0′ (item below), together with the "Reproduce a score" docs (README, PPA.md and a
       site page), which the study drafted. Today README, the site and `leaderboard.py` still rank by GE and depth.
    3. The scorer image and G1. Also re-time every task's proof time limit (`score/time_limits.json`) on the
       scorer's machine class. Under host load (load average 9–12, the Lean slot contended) fdivp measured 73–120 s
       against its 120 s limit and timed out once; fdivp_newton measured 58–192 s. A time limit that host load can
       break would refuse correct submissions. Measure it on a quiet reference machine with a stated margin, or
       count kernel time rather than wall time.
    4. Detail pages, after the site redesign lands.
    5. Formal equivalence (Yosys miter, ABC `&cec`) in the checker. It takes 0.03–0.4 s on every design measured except
       fdivp_newton (undecided after 25 min against the RTL; 205 s against the pinned netlist).
  - **Decided 11/04, on R4:** "Actually that's an interesting idea. That would allow golfers to use their own routing
    tools offline … it wouldn't work for parametric sized circuits? Maybe it just has to be a different tier of tasks,
    like the aes box, of fixed sized tasks, where we don't need/use lean to prove them correct, but just lec."
    Proposed in reply (not yet approved to build):
    - **Proof tier** (today's): parametric, Lean-proved RTL, ranked at logic level (A0′). Later, hand-instantiated sky130
      cells INSIDE the proved RTL (R3 option a): ls-sv models each cell from a table generated from the liberty's
      `function` strings, so the proof is about the scored cells, and parametric designs keep working.
    - **Fixed-size layout tier:** one instance per task. The golfer submits a gate netlist plus a routed DEF/GDS from
      any tools, offline.
      - Checks: LVS (Netgen/Magic: layout ↔ netlist); equivalence against the task's reference at that instance; DRC
        (sky130 decks); then extraction and sign-off STA with slew and cap limits, which gives the score.
      - The equivalence check is exhaustive simulation up to about 32 inputs (complete, no solver trust: sbox 8, an
        8-bit adder 17, an 8×8 multiplier 16), else SAT LEC. Clocked tasks are unrolled over the fixed-latency
        transaction.
      - A proved reference keeps the chain ending in a theorem. No Lean is asked of the golfer.
      - **Certificates** (decided 11/04: "can we also have the golfer submit a certificate proof of correctness?"):
        yes; the solver is untrusted and the checker is small and verified.
        - The checker builds the miter CNF ITSELF from the two netlists (Tseitin, cell functions from the generated
          table) and never trusts a golfer's encoding.
        - Accepted proofs:
          - an LRAT proof from any solver (CaDiCaL, Kissat), checked by `cake_lpr` (verified in CakeML down to
            machine code) or by Lean's LRAT checker;
          - a PAC proof (AMulet; the checker Pastèque, verified in Isabelle) for multiplier tasks, where SAT proofs blow
            up beyond about 16 bits;
          - a Lean proof of netlist = reference at the instance. `bv_decide` trusts `ofReduceBool`, so it needs the house
            justification.
        - Without a certificate: exhaustive simulation up to about 32 inputs (complete), else our own solver under a
          time limit.
        - LVS and DRC need none; the checker reruns them, since they are deterministic and cheap.
        - Sequential designs with unbounded behaviour would use inductive-invariant certificates (Certifaiger, HWMCC).
          Fixed-latency transactions are unrolled into a combinational miter instead.
      - Tasks are chosen where the check is robust; SAT LEC is weak on structurally different multipliers.
      - Size: L.
  - **For the maintainers (R3, R4), on how golfers influence the layout** (superseded by the two tiers just above):
    - R3: should hand-instantiated sky130 cells rank at logic level for any netlist that passes the equivalence check,
      or only for cells written in the proved RTL? Measured gain: median −7.3% area.
    - R4: is the end state the golfer submitting the netlist and routed DEF with the checker only verifying (C2), rather
      than svGolf's own place-and-route ranking the tool's run (C1)? The measurements favour C2: with timing repair
      on, ORFS's random seed moved results more than any hint (area −8.8% to +14.8%), and with it off, hints moved
      delay by under 4%.
- Which metrics are RANKED stays the maintainers' decision once the columns are stable.
- **RULED 11/03: sky130 is the default.** The ranked board becomes sky130 A0′ (area µm², NLDM delay ps), with
  `area_ge_v1`/`depth_v1` kept as columns. Work item, queued after the fold of the former 16-bit task into `fdivp` lands (both touch
  `tests/expected.json` and the task READMEs):
  1. `leaderboard.py`'s default axes become (A0′ area, A0′ delay). Records without sky130 columns are unranked until
     backfilled; the 4 existing reference records have none, so `seed-references` is re-run with `--ppa require`.
  2. Update the goldens (`tests/expected.json` and the sky130 expectations) and the tests.
  3. Docs: README "Scoring"/"Leaderboard", the leaderboard README, the score lines in task READMEs.
  4. The site: par tiles, plots and tables in µm²/ps, with GE as a column.
  5. **Clocked flows:** `ppa.py` must time sequential netlists (register to register, from the liberty's clock-to-Q and
     setup). Time = cycles × the sky130 period in ps. This settles the per-cycle overhead question (C7): the library's
     own flop timing replaces any ad hoc overhead.
  - `[x]` Steps 1 to 4 (11/04, branch `svgolf-ppa-v3`, on `sky130_a0_v3`): `leaderboard.py` ranks `RANKED_AXES`
    (`area_um2_sky130`, `time_ps`: the delay, or a clocked record's `score.time_ps` = cycles × period, held to its `ppa`
    block); a record without columns, of another PPA identity or under another input drive is "not ranked" with the
    reason. The four reference records of 10-29 re-seeded with the same files under `--ppa require` (and `clmul_n`),
    `verify` 5/5 reproduced; `tests/expected.json` needed no change (no field depends on the ranking); the board golden
    re-recorded. Docs and the site switched; `reproduce.html` renders PPA.md's "Reproduce a score". Step 5 was in place
    (`check.py` `score_clocked`). OPEN: `leaderboard.py add` still refuses a clocked check result (its acceptance reads
    the combinational `postsynth` record), so no clocked record exists yet; clmul's baselines, fdivp's D1/D2 and the
    `add_proc`/`add_proc_m`/`add_mux` and `sbox_table` references have no sky130 golden by file (their site cells show "–").
  - `[x]` The STA study's D1 joined `sky130_a0_v3` before its release (11/04, branch `svgolf-ppa-v3`): a load pin's
    `rise_capacitance` times a rising edge and its `fall_capacitance` a falling one, as OpenSTA reads them
    (`score/test_ppa_opensta.py`: OpenSTA's numbers, equal to 1 fs per arc). Areas unchanged, delays -0.30% to +1.32%, no
    order or frontier changes; matmul 10,696 ps (6 buffers), the sorter 2,523 ps. Every golden re-recorded by its tool, the
    five reference records re-seeded (`verify` 5/5 reproduced). D2 stays a documented choice: the input drive is a real
    cell per input, not `set_driving_cell` (score/PPA.md, "The input drive"). OPEN: `matmul_g1` is rejected at the
    solution stage by `tests/run.py --only matmul` on this branch (a Lean compile error, not the STA); its expected.json
    numbers come from `check.py --unproved --latency 4`.
- (superseded) **[M] Switch the ranked board to sky130 A0′** (area µm², NLDM delay ps), keeping `area_ge_v1`/`depth_v1` as columns.
  - Lead's lean: yes, before going public.
  - Why: A0′ is as deterministic as GE (bit-identical, MEASURED); it keeps every ranking of the legacy score on today's
    tasks (MEASURED, WP-X1); it uses real units; and it removes the GE/sky130 mix in the sequential flop pricing.
  - A1′ (full re-mapping) stays an unranked research column: mapper choice moves it about 12% in area and 49% in delay.

**Repair step everywhere (decided 11/04):** "Please add the repair step everywhere (buffering). Also feel free to
outright reject designs from golfers that produce illegal netlists. They can fix things themselves too."
- Why (MEASURED, workflow `a0-fanout-measure`, re-checked independently):
  - the 33 combinational netlists are electrically legal (worst load 0.57× max_capacitance);
  - matmul's is not: 4 cells over max_capacitance, 361 over max_transition, and 1,616 table reads extrapolated beyond
    the characterized range, non-monotone and possibly negative. Its period read 48,079 ps against ~10,200 ps after
    repair, and duplicating a flop was a 4.4× ranked-time shortcut.
- `[x]` Workflow `ppa-repair` (branch `svgolf-ppa-repair`; merging it into prep is the lead's):
  - the ranked area AND delay come from the REPAIRED netlist, for every task, and the repair is BUFFERING ONLY
    (`ppa.Repair`, `buffer_trees_v1`, Python in `ppa.py`): every net over its driver's `max_capacitance`,
    `max_transition` or table grid gets a balanced tree of `buf_1`..`buf_16` within liberty-derived budgets (inputs
    driven by `buf_1`, flop Q nets, nets driving output bits at 10 fF per bit, all included), the tie cell is replicated
    and audited, nothing is resized, repeated to a fixpoint; the STA drives inputs with `buf_1`;
  - a netlist the repair cannot make legal is REJECTED with the net named (none known on sky130);
  - GE and unit depth are unchanged, flow A1′ is unchanged;
  - DROPPED: the first `sky130_a0_v2` (ABC `topo; buffer -p; upsize; dnsize`), after the review MEASURED a hole (the tie
    cell never load-checked), rejections a golfer cannot fix (ABC never sees input-to-output and flop-to-output loads)
    and area noise (`upsize` without a delay target: +2.4% to +40%);
  - every golden re-seeded by its tool (`ppa_validate.py table`, the energy goldens, the matmul record,
    `tests/fdivp/results/check_reference_ppa.json`); rankings before and after in score/PPA.md, "Rankings under
    `sky130_a0_v2`": v1's orders and Pareto frontiers on every task, except matmul, where the duplication probe drops
    out. Still to do: the site (§3b; the pages that call the sky130 columns unranked).

## 3d. A second `fdivp` reference: Newton–Raphson (decided 11/03: "it would be nice to have more than one reference")

`fdivp` has one proved reference (D3, restoring division: small, deep).

**Newton–Raphson:**
1. a constant-coefficient initial reciprocal;
2. K(P) Newton steps as a generate loop;
3. q = a·r;
4. an exact remainder fix-up.

It is large but shallow, so it sits at a different Pareto point.

**Proof:** a Newton error bound for every P (new mathematics) plus the existing rounding certificate (`certF_bridge`) for
the fix-up.

**Gates:**
- `[x]` **N0** (11/03, workflow, worktree `lean-surfaces-newton`, `fdivp_newton.sv` 169 lines, untracked, no Lean).
  - **Correct everywhere measured, with no fixes.** Checked RTL on every pair for all 66 formats with W+P ≤ 14,
    on all 2^32 pairs at (5,11), (8,8) and (2,14), on corner vectors at 14 formats up to 64 bits, and on gate netlists at
    (2,2) and (8,8). All 7 deliberate mutants were caught.
  - **Dominated, not a new Pareto point** (pinned flow, sky130 A0′ µm² / ps; D3 in brackets):

    | format | Newton | D3 |
    |---|---|---|
    | (2,2) | 435 / 2601 | (457 / 2892) |
    | (8,8) | 17684 / 30699 | (6077 / 23618) |

    At (2,2) it beats D3, but D2 dominates it. At (8,8) it is about 3× D3's area and slower. The "large but shallow"
    premise fails at these widths, because the Newton multipliers are as deep as the restoring chain they replace.
  - **The pinned flow cannot score it at (5,11) or (8,24).** `&fraig -x` in the `abc -g` script ran for more than 2 h
    (about 1,300 candidate constants, each a multiplier SAT problem). With fraig removed, the estimate at (5,11) is
    9005 GE / depth 284, against D3's 2166 / 289: about 4× the area at the same depth.
  - **Outside the tactic fragment:** run-time `*`, and the `$clog2` localparam (fixable as `(P + 2) / 8 + 1`).
- `[x]` **N1, the proof: PROVED and registered (11/04, branch `svgolf-fdivp-newton-proof`).** Decided 11/03:
  "it doesn't have to be competitive to be a good and interesting reference".
  - The design is `tasks/fdivp/reference/fdivp_newton.sv`: D3's output stage, a logarithmic step count
    `NI = $clog2((P + 9) / 8) + 1`, and the estimate perturbed when an exponent field is all ones (`qe`), so the pinned
    flow finishes at (5,11) in 66 s: 7892 GE, depth 252 (D3: 2166, 289).
  - The fragment reads `*` and `$clog2` localparams (`sv-comb-mul`); `Lib/Newton.lean` proves the core for every P.
  - `reference/fdivp_newton.lean` (5,300 lines): D3's sections `IEEE754Proofs` .. `DpG4` copied verbatim
    (`tests/fdivp/shared_sections.py` pins them), plus the core glue, the chain and the solution (about 640 lines).
    `check.py` accepts it. Heartbeats: structure 315 thousand, solution 536 thousand. Cold solution stage: 44.6, 45.8,
    45.3 s.
  - Registered (G6): the second entry of `task.json` `references`; `tests/expected.json` with the scores at (5,11), (8,8)
    and (2,2) (not (8,24): the pinned flow takes more than 30 min there); the cold runs in `score/time_limits.json`; the
    sky130 goldens in `score/tests/ppa/` (A0′ 33821 µm², 39679 ps at (5,11); D3 9676, 37768); the 7 mutants as
    `tests/fdivp/attacks/newton_*.sv`, each rejected at `solution` with the Newton proof (an attack may now name the
    reference proof it is submitted with, `lean: "reference/<stem>.lean"`); validation rows in `tests/run.py`; the
    READMEs and `PROVING.md`.
- `[x]` **A third reference: radix-4 SRT** (decided 11/04: "Good idea"). Landed on prep 11/05 (6bf04eca) after the
  review's licence fixes (the attacks point at the reference's LICENSES/; the provenance names Wally's `mux.sv`; the
  site shows a licensed rejected design with its notices) and a green `run.py --only fdivp` on the merged tree (layout
  25, negatives 5, references 26, validate 39, attacks 25; no failure). For master: `Lib/XFVal.lean`'s `val_csa` and
  `val_xor_top` (the SRT model itself stays in the reference).
  - S0 DONE (`svgolf-fdivp-srt` ed147f1a; `tests/fdivp/results/srt_S0.md`). Adapted from CORE-V Wally's fdivsqrt
    (Apache-2.0 WITH SHL-2.1; provenance header with 10 changes), with D3's output stage verbatim. MEASURED: 0
    mismatches (all W+P ≤ 14, all 2^32 at (5,11), (8,8) and (2,14), 14 large formats); all 10 mutants caught; the
    selection table checked exactly over 547 cells.
  - Score at (5,11): 2778 GE, depth 192, 12,311 µm², 28,694 ps (D3: 2166, 289, 9,676, 37,768). That is the lowest depth
    and delay of any fdivp design: a new Pareto point that dominates Newton. `&fraig -x` takes 2.8 s.
  - Unmodified originals: findings for ls-sv (struct parameters and members, casts, iterators declared outside the
    header, an `x` default).
  - `[x]` S1–S6 (workflow `srt-proof`). Two design edits (the lead's decisions): the parameter shift becomes a
    part-select; the four `case` tables become `?:` trees, keeping the D3/Newton proof route. The SHL-2.1 text ships
    in LICENSES/. Then the fragment check, `Lib/Srt.lean`, the proof and registration. JUDGED: about 1,600 new lines,
    a cold run of 55–75 s.
    `[x]` **DONE 11/05** (`svgolf-fdivp-srt`, `tests/fdivp/results/srt_S0.md` sections 7 to 13). MEASURED: proved for
    every W, P >= 2 (`reference/fdivp_srt.lean`, 6,090 lines, D3's 16 sections verbatim, the core in section `SrCore`,
    the selection table by one kernel `decide`); `sv_structure` 672 thousand heartbeats, `solution` 700 thousand after the
    merge onto the shared obligations; three cold `solution` stages 78.6, 73.2, 69.9 s at load below 8 (T = 78.6, the
    slowest fdivp reference; 92 to 121 s at load 10 to 17 before the merge). Registered third in `task.json` with its
    scores (2787.652 GE, depth 189; 12356.85 um^2, 27592 ps at (5, 11)) and its ten attacks, each rejected at `solution`.
- **Review (11/04), MEASURED:**
  - a cold check.py run with scoring is ACCEPTED (solution 46.3 s); three mutants are rejected;
  - the `*` width rule agrees with E and iverilog on 69,632 vectors (a wrong rule would show 1,152 disagreements);
  - `$clog2` agrees with the elaborator at 40 values.
  Fixed: `shared_sections.py` compared after newline translation, so a `\r` passed. It now compares byte for byte
  (eed8099f). The lead approved the four data files under `score/` (the cold runs, the sky130 goldens): data, not flow
  files, and none of the 12 files check.py fingerprints changed. Open, small:
  - `newton_ni_minus1` is rejected by the heartbeat limit, not by a clear mismatch;
  - the refusal message for `$signed(a)*$signed(b)` names a misleading reason.
- **G0 SOLVED 11/03 (MEASURED).** `&fraig -x` took 1258 of 1260 s of ABC time. The hard candidates sit in the
  CORRECTION stage, not in the Newton chain; the chain's cone alone proves everything in 73 s. At P = 11 the third
  candidate is dead logic: ge2 = "b is zero", rm's top bit is 0, and rm ≠ 2·mb. Each of these facts is provable only
  from the full error bound. Two fixes were found:
  - **optX** (workflow design track): perturb the estimate on inf/NaN operands only (`qe = qf − a[0] − b[0]` when an
    exponent is all ones). Those values are never read, and the perturbation makes the dead facts false, so fraig
    refutes them by counterexample. The pinned flow finishes at (5,11) in **66 s**: 7892 GE, depth 252. Validation:
    all W+P ≤ 14, all 2^32 pairs at (5,11), (8,8) and (2,14), and the corner vectors, with 0 mismatches. It keeps the
    proved recurrence (`Lib/Newton.lean`, d397f120, 488 lines, G3 met) for every finite operand.
  - **c1b** (side agent): a two-candidate correction (qq = qf + [rm ≥ mb], F = P + 5), so it needs a strict-error
    variant of the math. It finishes in 1172–1388 s against the 1800 s cap: 8125 GE, depth 254. Kept as an option.
  - **Hints do not help** (gate bypassed for measurement only):
    - `unique`/`priority` qualifiers and `'x` don't-cares did not make v0 finish;
    - `(* keep *)` is not a cut point in ABC;
    - `(* keep_hierarchy *)` IS a cut point, and a SCORING LOOPHOLE if attributes are ever admitted: on the top module
      alone, depth reads 189 against 270 and area 1681 against 9468 GE. The gate rejects every attribute today, and
      that rule must stay for this one.
  - **Decision:** take optX, because the math is already done and the margin is 27×. It is APPLIED as 8a175927 on
    `svgolf-fdivp-newton-proof`, before the proof rounds start. The glue needs one extra lemma: qe = qf when no exponent
    field is all ones. c1b's two-candidate correction is the better circuit idea, recorded for a later revision.
- **RULED 11/04 by the maintainers (reversing the lead's call): move `Lib/Newton.lean` into the fdivp_newton reference.**
  "Might still want to move it to the reference, since it's kinda cheating otherwise. Golfers won't be able to just put
  things in the standard library for free."
  - The rule: the shared library holds only GENERAL results that any golfer of that class of design would use.
    Anything that models one reference lives in that reference and counts against its time limit.
  - Audit `Lib/Restoring.lean` and `Lib/RowMajor.lean` by the same rule.
  - The move happens after `sv-lib-quality` lands, since that branch is editing those files. Its time cost is
    measured, and the proof speedup work (`sv-proof-perf`) is what pays for it.
  - `[x]` **DONE 11/04-05** (`sv-lib-split`, merged 588541f9). All 21 declarations moved unchanged into section
    `NwCore` of `fdivp_newton.lean`, with `correct_quot_of_rem_lt_three_mul` (the core's correction stage) from
    NatArith; `Lib/Newton.lean` is deleted. MEASURED: about +1 s on a 58 s solution stage at load 8-12 (+3.1%
    heartbeats); the 120 s limit holds with about 2x margin. The audit moved nothing else: Restoring, RowMajor, XFVal,
    NatArith and BitVecArith hold general facts (two plain Nat lemmas now used only by NwCore stay as textbook facts).
    `[x]` Same rule: `Lib/Srt.lean` on the SRT branch moved into `fdivp_srt.lean` as section `SrCore` (DONE 11/05, in the
    merge of svgolf-prep 06f2a700 into `svgolf-fdivp-srt`; `val_csa`, `val_xor_top` stay in `Lib/XFVal.lean`).
    The export must pin a master WITHOUT `Lib/Newton.lean` once it carries `NwCore` (same names, ambiguous otherwise).
- **Open [M]:** where spec facts shared by two references of one task live: duplicated in each reference, or one
  untrusted `tasks/fdivp/SpecFacts.lean` beside the spec. The lead's lean is the latter.

## 3e. Ideas from prior art (asked 11/04: "Do any of these have good ideas tasks or rules?")

From the sweeps `prior-art-svgolf` and `prior-art-ideas`, 11/04. Every record bar was read from its source; full
results are in the session's task outputs. Nothing found combines kernel-checked statements valid for every width with
a real-PDK PPA board. The closest are Logicode (sky130 area/fmax board, testbench only), IWLS 2026 (AIG area/delay
Pareto sets against a merged "virtual best" frontier, checked by `cec`), EPFL's best-results table (LUT-6, CEC), and
CktLean (a Lean HDL with a sky130 flow, no board).

**RULED 11/04: "Don't spend too much energy on new tasks that are in the same category as the existing
ones. Let's focus on getting the site working well on a few high quality tasks first."**
- So the tasks below are PARKED.
- The new categories (reactive controllers, the fixed-size layout tier) stay at design studies until the site is in
  shape.
- The focus is §3b: the site, the detail pages and the scoring docs, on the existing tasks.

**Tasks, ranked** (proof tier unless noted; status: parked proposals):
1. `aes_mixcol`, fixed 32→32: AES MixColumns. Its XOR count is an active record race: 94 → 92 → 91 → 89 → 88
   (eprint 2026/1481). The proof is linearity plus 32 basis vectors by `decide`. It is also the layout-tier pilot.
2. `symcount`: popcount and majority/threshold for every n (n = 2^K − 1), with `+ - *` banned. The full-adder tree
   is NOT optimal at any n (Cirbo AAAI-25: SUM_15 at 51 XAIG gates, MAJ_15 at 48), and its carry-save lemma also serves
   `mul`.
3. `sortnet`, N = 16 with W parametric: the open size record is 60 comparators at depth 10 against a lower bound of 57.
   It needs a 0-1-principle library.
4. `gfmul8`: GF(2^8) multiplication (Boyar-Peralta CMT records: 117 gates at depth 6). The proof is symbolic, from
   clmul's.
5. `aes_inv_sbox`: one line of `sv_exhaustive`; the cheapest to add (records: 121 gates at depth 21, 127 at depth 16).
6. `isqrt`, a relational statement `r² ≤ a < (r+1)²`, reusing fdivp's restoring recurrences.
7. `lzc`: fdivp's normalizer.
- Deferred: int2float (EPFL's netlist is not IEEE), SECDED, arbiters (a new task kind: see the reactive study),
  IWLS truth tables (licences unchecked).

**ReactTask is in (decided 11/05: "That's great. Please add it. I love new task types.")**: the reactive kind and its
first task, the fair N-client arbiter, from branch `svgolf-reactive` (design/reactive/README.md), with the draft's
defaults for its open choices (Moore observation, safety + bounded response with K = N - 1, no environment
assumptions, scored at N = 8). Workflow `react-arbiter`, branch `svgolf-react`: integrate, wire through the pipeline,
prove a reference for every N, review. Unranked preview until its reference is proved and the maintainers say so.

**Asynchronous FIFO (decided 11/05: "please start a workstream on making the async fifo task")**: the first
two-clock task, where timing nondeterminism matters: every interleaving of two unrelated clocks and every metastable
resolution must be covered by the proof (the maintainers' rule: proofs hold for every order and every resolution).
Round 1, workflow `async-fifo-study`, branch `svgolf-async-fifo`: a draft statement and kind, a two-clock bench with
metastability injection and attacks, real-world RTL through today's pipeline, a scoring proposal, and the ask for
ls-sv (two-clock semantics over every edge interleaving, the sampling rule, memories).
- **Round 1 result (11/05), branch `svgolf-async-fifo`, design note `design/async_fifo/README.md`, not merged:**
  - Statement revision 2 (`tasks/async_fifo/`, DRAFT, not wired into `tasks.lean` or `check.py`): a flop captures z
    wherever its input changes or may glitch in the instant (a ternary hazard view); only a same-domain flop reading
    through wires resolves z (per bit, every resolution); every decision bit must be known (txtask-v2's list). No
    synchronizer-shape rule remains in trusted text.
  - Nine kernel-checked refutations at depth 2, axioms [propext, Quot.sound]: six fail a safety clause for every
    declared bound (binLazy, fullLate, oneFlop, oneFlopCase, lateWrite, crossRst), three fail liveness for bounds up
    to 16 (bin2, combGray, stuck). Four correct designs pass every refuting run. No design is proved against the whole
    statement yet.
  - MEASURED: binary pointers with two-flop synchronizers are safe (17.3M bench instants, exhaustive search) and fail
    only liveness and flag stability, so Gray coding buys stability, not safety. `ppa.py --seq` silently merges the two
    clocks; `rtl-probe/scripts/domain_sta.py` gives per-domain periods.
  - Real-world RTL: OpenTitan, ZipCPU, pulp and verilog-axis, pinned and adapted by counted changes, refuse only at
    `Clock:multiple`. The ls-sv ask (`design/async_fifo/LSSV_ASK.txt`) is in its inbox (11/05).
  - Open for the maintainers: the metastability rule, a mux between synchronizer stages, the score (proposed
    area × (latR + latW) × period), the depth range, ports, reset, whether a liveness-only refutation of binary
    pointers is intended, and a one-clock FIFO as the proof stepping stone.

**Rules, for the maintainers** (ranking is their decision):
1. **Rank at several points** (add at 16/32/64, mul at 8/16/32), dropping each golfer's worst rank (the ISPD 2018
   metric). Proofs already cover every N. It ends the single-point lottery: commuting operands alone moves A0′ area by
   up to 11%.
2. **A committed hidden point per season:** sha256(seed) is published at the opening and revealed at the close. For
   clocked tasks the checker must evaluate `lat` at the revealed point (C3).
3. **A 1% margin to CREDIT a record** (the Pareto board itself stays exact), as in the Hutter prize and Ladder.
4. **A 30-day provisional window** for a record, during which anyone may challenge it or run `verify --full` with a
   fresh salt. Outcomes are separate append-only entries.
5. **Named per-axis record holders** (min area, min time, min area×time), with a required `method` field, as EPFL
   does. This is a schema bump.
6. **A cross-task score against a frozen par:** Σ max(0, 2 − log10(AT/AT_par)), from SYNTCOMP 2017. It is
   scale-free; par is frozen per `ppa_version`.
7. **Flags, not bans:** a `flags` field (cells, a1, …). The default board shows unflagged records; an exploit's
   records move under a flag, as in Opus Magnum.
8. **Layout tier:**
   - separate "checked" and "certified" tables, each with the certificate check's time and memory;
   - a certificate that times out is not a record;
   - the die is Tiny Tapeout's 1×1 tile (about 160×100 µm), which every reference except matmul fits.

## 4. Parallel work, classified (non-blocking for the milestone)

| item | owner | class |
|---|---|---|
| `fix-hnq-refs` (three broken references) — **DONE**: merged (d0bf45a2); check8 on prep passes every task's references | fix agent | **required for Gate 0** |
| Day-9 suite and integration | lead | **required for Gate 0** |
| Removal of the former 16-bit task plus restructure (spec into `tasks/fdivp`, no per-task libraries) — **DONE, merged into prep 11/04 (fdf46427)**.<br>• fdivp's reference is one self-contained file over `LeanModels.Sv.Lib`, measured cold at 64–72 s.<br>• The former 16-bit task's attacks, negatives and refutations are ported to (5, 11). The refutations now rest on interpreter `#guard`s
rather than the kernel, because generate expansion does not reduce there.<br>• The trusted `Spec.lean` change is mechanical: the import path, the docstring path, and the removed cross-link theorem
to the deleted task. The `Statement` itself is unchanged. The `rfl` guard which says (5, 11) IS
binary16 stays (`fdivBits_binary16` since 11/04) [M].<br>• Open, small: the canon step lost its divider row (no divider keeps its score under reordering); a few stale doc
pointers. | workflow (done) | hygiene |
| `fdivp`'s proof time: **target ≤ 90 s cold (the stop line), hard limit 120 s** | workflow | hygiene |
| `sv_exhaustive` **G-E1 and G-E2 DONE; merged into prep 11/03 (494dceac)**.<br>• `sbox_table` is now one line, `by sv_exhaustive`: cold solution stage 26.1 / 25.0 / 24.7 s at load 7–11, against 31.6 s for the generated proof. `gen_table_proof.py` and its template are retired. `run.py --only aes_sbox` layout and references: PASS, 35 checks.<br>• `sbox_bp` keeps its generated reference. The one-line proof ran 58–69 s cold at load ~5 and 83–91 s at load ~10, against the old 51–54 s. Splitting it into auxiliary theorems made it slower (93–98 s): inside one declaration they are not checked in parallel, and each starts a fresh kernel context (MEASURED). Two routes are open, neither scheduled: cut the 19.7 s exhaustive decision (the old `bp_correct` took 10.5 s), or a reference with two top-level theorems, a structure theorem plus `sv_exhaustive`.<br>• Each output is decided as a bit-vector equation (5a9c0f9c: sbox_bp 614M → 551M heartbeats). 523 tactic lines.<br>• **To master** (before svgolf is published, since the public svgolf will require lean-surfaces): `LeanModels/Sv/CombExhaustive*.lean` are the only `LeanModels/Sv` files prep has over master, but no master target builds them, because their only consumer is svGolf's `CombTask`. They land on master together with a build anchor: an `Examples/system-verilog` example proved by `sv_exhaustive`. | L (done) | later families |
| E to master in slices, `sv-div-5` row — **DONE 11/04**. Seven fast-forward slices, 2468764f → 201f28f6: Lib, the clock
step + seq_neg, the loop core + Comb2Base fuel, the kernel E with observation/contracts (22 modules, 922 theorems,
clean axioms), the E-route loop/comb, sv_exhaustive, Lib/Newton. Each slice was byte-identical to prep, built through
the slot, anchored in master's targets, and passed the rfl probe. `sv-div-5` is in the divergence register, guarded by
`harness/sv_divergence_probe.py`. svgolf-prep now carries no SV content master lacks. | lead | done |
| deferred qualified-case reports (LRM 12.4.2.1) | A, L | backlog (retires `sv-div-5`) |
| multi-process slot theorem over E | A | later families (WS4's week-2 priority) |
| typed converse, progress under the window rank | A | before Gate 4 claims equivalence |
| symbolic-N lowering without symExec | A/L | backlog |
| word-level `*` in the sv_comb fragment (value lemma: XF value of a product = product mod 2^w), plus `$clog2` localparams. Today `*` is outside v1, which blocks multiplier blocks and any `*`-using golf entry for `fdivp`/`mul`-like tasks. **In progress 11/03** on `sv-comb-mul`, as part of §3d N1. | workflow (§3d) | needed by §3d N1 |
| **Principle for E-core-2 (decided 11/03): E's meaning is defined on the STRUCTURED AST, and elaboration is optional.**<br>• Parameters stay parameters, generate families are indexed families, and an instance is a composition.<br>• The elaboration steps become optional, proved-equivalent transformations in the library: `expandGenerate`, `flatten`, `substParams`, each with `sem (T d) = sem d` and each structurally recursive, so kernel-reducible.<br>• Generate-`if`, parameter-dependent widths and name resolution become a decidable well-formedness predicate plus a meaning that is a function of parameter values. The loader's slang-differential and `int32Agrees` gates stay.<br>• R-HIER becomes "an instance means a composition"; `flatten_sound` is a theorem, not the definition.<br>Supersedes the narrower item below. A writes it into the E-core-2 design note.<br>• **Where loops stand today** (checked 11/03, after the maintainers asked "I thought we had stopped unrolling all the loops"):
  what PROVERS see is structured. The extractor keeps parameter-bound loops as `For` nodes, the PDesign keeps
  `PStmt.forLoop`, and the sv_comb tactics treat generate loops as families at symbolic N. But E's DEFINITION still
  expands them. `Stmt2` has no loop constructor, and `Param2.instStmt2` turns a procedural `for` into a `.block` of body
  copies, one per iteration value, at the concrete parameters (fuel-bounded `forValues2`); generate loops are expanded
  in `Hier2`. Separately, the extractor still unrolls LITERAL-count loops by default (`--retain-loops` keeps them).<br>• **First slice of E-core-2, when it is scheduled:** a `for` statement in E with its own structural rule (the body
  iterated, the index a process-local), with the expansion proved equal to it, so today's tools keep working through
  that theorem; then `--retain-loops` as the extractor default. | A | design note, non-blocking |
| (superseded by the row above) E's elaborator, the planned single AST: kernel-reducible by construction, with structural recursion only and no well-founded recursion or fuel. Today `instantiateGD2`'s generate and hierarchy expansion (`Hier2.lean`: `expandListH`, `expandItersH`) uses well-founded recursion, so `design.sem` does not reduce in the kernel. That is why every SV tool goes through `Summary.sound`. It aligns ls-sv with the family's kernel-reducibility rule and retires the generate-fuel debt. The summary bridge stays for speed: generic kernel interpreters are measured too slow (`sv_exhaustive` G-E0). | A | design rule for E-core-2's elaborator; a note in `docs/sv-kernel.md` at the next master push |
| **sv_comb fragment growth from real-world constructs** (11/04). Constructs real designs use that the fragment still
refuses, each with the refusing tool and its exact message.<br>• Already covered: `*` (on `sv-comb-mul`) and constant concatenation (master c0516458).<br>• Open: `<<` in a localparam (CE); a shift whose operand is an expression; signed declarations in the comb view; a
procedural `for` in `always_comb` (a leading-zero loop, iterator `integer i` at module scope); unpacked arrays and
wires assigned in a generate loop ("out-of-tier module members"); a clocked pipeline (the sequential route,
not sv_comb).<br>• Each becomes a fixture plus the fragment rule, in the structure-preserving style. | workflow, when the Lean slot frees | later families; real-world driven |
| **Procedural `for`-loop mis-models in the extractor/E** (MEASURED 11/04 by an adversarial run of 77 probes against
iverilog, Verilator and Yosys 0.53; they affect `always_comb` and `always_ff`):<br>(1) the condition is compared signed where SV compares unsigned (`i < 2'd2`); E and Yosys disagree;<br>(2) the iterator is bound by name, so it captures a same-named localparam inside an inlined function; E and Yosys
disagree;<br>(3) the iterator's declared type is ignored (`bit [2:0]` wraps); E and Yosys agree, but both differ from the LRM.<br>Reported to the ls-sv lane with generic probe files. The svGolf source gate refuses these shapes as a STOPGAP
(`svgolf-seq-counter` 68983775, item 7, which covers every procedural `for`).
MEASURED: none of the 51 references and baselines changed verdict. All 13 defect probes and the over-admission
probes are refused. An independent re-run of 76 probes plus 21 new ones found no passing probe on which E differs
from the tools. ACCEPTED: one conservative over-refusal (an iterator named like a module variable, `s1`, which is
sound). Fixed in passing: the clocked rule missed `++c`/`--c` (slang's kind is `UnaryPreincrementExpression`). Latent:
a static block-local NBA target in a loop (`t4`) makes Yosys differ from SV, so the gate must refuse it once ls-sv
admits block-local declarations (told). The clmul attack `func_oldstyle_xor` now stops at `source` (c5a54726). Separately, `score/fourstate.py` refuses a run-time index `q[i]` inside a
procedural loop ("does not know loop bounds yet"), so real-world loop designs stop there today. | ls-sv lane (E/extractor); lead (gate stopgap); fourstate open | soundness: before admitting loops anywhere new |
| **Real-world SV support, the Wally list** (decided 11/04: "We should support all of those. Make sure they are in the plan.").
Measured on CORE-V Wally's fdivsqrt, unmodified; tracking target: Wally's divider with near-zero changes. Each item
lands with a fixture, the refusal it removes, and a re-measure of the Wally count:<br>• **casts** (width, signed, type): loader (ls-sv; signed INT localparam width conversions landed in fac56e33), then the
sv_comb fragment (ours);<br>• **module instances**: the proof route through hierarchy (R-HIER, `flatten` as a proved transformation, E-core-2);
the loader already expands instances;<br>• **`` `ifndef `` and other preprocessor guards**: preprocess ONCE with a pinned macro set, and hand the same text to
Yosys and the extractor, so the source gate's one-program guarantee holds (today every directive except timescale and
default_nettype is refused);<br>• **`'x` defaults** (don't-care assignments): admit them SOUNDLY. Yosys may pick any value, so the proof must show the
outputs are known and correct with X there; by X-monotonicity (`LeanModels/Sv/XMono.lean`) any concrete choice then gives
the same outputs. Gate rule plus a lemma;<br>• **loop variables declared outside the loop** (a module-level `integer i`): the extractor and E admit them; the source
gate refuses them. Admit them when the variable is private to one process (no other reader), and in E with E-core-2's
structural `for`;<br>• **structs**: packed struct parameters, member accesses, assignment patterns: loader (ls-sv), then the fragment;<br>• the tactic gaps SRT hit: shifts by a parameter, `case` tables in `always_comb` on the D3/Newton route, expression
operands of `*`, signed arithmetic. | ls-sv (loader), lead and agents (gate, fragment, E) | high: real-world driven |
| **Hand-instantiated library cells** (decided 11/04: "Yes, I think this should be allowed. But we don't want to add a lot of lean code for every single cell in sky130, and every other library. For the purpose of the lean proof, can we just convert each cell into logically equivalent SV?").<br>• **The cell library is generated SV, with no Lean per cell.** A generator reads the pinned liberty and writes one plain module per cell: `assign` from each output pin's `function` string (`!`, `&`, `|`, `^` and juxtaposition), and `always_ff` from the `ff` group for `dfxtp`. ls-sv already gives those meaning. Any other liberty (gf180, sg13g2, …) is a rerun.<br>• **Proof vs score.** For the proof, the checker prepends the generated file, so an instance is an ordinary module instance. For the score, Yosys reads the liberty as cells (`read_liberty -lib`), so instances stay exactly as written, while ABC maps only the rest.<br>• **The trusted piece** is the generated file. It is checked per cell, exhaustively (cells have ≤ 6 inputs), against two independent readings: Yosys's own import of the liberty functions, and the PDK's functional Verilog models simulated. It lives in the task layer, like the Spec.<br>• **Admitted:** cells with a `function` (every drive strength; the liberty's own area and NLDM timing price it), `conb` ties, and `dfxtp` flops in the FF-only profile. **Out:** tristate (`ebufn`/`einv`), latches, clock gates, async-reset and scan flops (until their tiers), and physical-only cells (tap/decap/fill/diode).<br>• **Gate:** an instance is admitted only of a generated cell module, with named port connections and no parameter overrides; the golfer's own submodules wait for module instances in general (the Wally row).<br>• **Depends on** the module-instance proof route (R-HIER, `flatten` proved in E-core-2), which needs one generic inlining lemma, not one per cell. Parametric designs keep working: cells can sit inside generate loops.<br>• **Measured gain (influence study):** a full-library mapping gives a median 7.3% less area across 17 designs.<br>• **Timing prerequisites** (`sta-gap-a1`, 11/04, MEASURED against OpenSTA on all 330 cells with a function):<br>&nbsp;&nbsp;– D1: ppa.py loads nets with each pin's `capacitance`, but the liberty prices a rising edge with `rise_capacitance` and a falling one with `fall_capacitance`. The worst single-arc error was 5.6%. With per-edge capacitances it matches OpenSTA to 1 fs on every arc. The patch goes into v3 before v3 merges; ranked delays move −0.3% to +1.4%, no order changes.<br>&nbsp;&nbsp;– D2 is a documented choice: our input driver is a whole `buf_1`, which OpenSTA's `set_driving_cell` is not; fix the docs that call it that.<br>&nbsp;&nbsp;– Still to do before cells rank: `cell_class` must admit multi-output, clock and delay cells; an unused fa/ha output (0 fF, below the table grid) must not reject the netlist; a rule for transitions below the 10 ps table floor. | lead (generator, gate, flow); ls-sv (instances) | after module instances |
| **An iterative divider task** (decided 11/04): "maybe we should make a divider task that allows iterative/sequential
designs, and golfers can decide whether to use many short cycles or a few long". A `TxTask` over fdivp's IEEE spec,
scored by area and time = cycles × period. References: an iterative radix-4 SRT (one or two stages per cycle, from
the SRT reference) first; Wally's iterative fdivsqrt with minimal changes once the Wally list lands. | lead | Gate 5 breadth |
| `casez`/`casex` into E (needs Xcelium pins) | A | backlog |
| R-HIER / E-core-2 design note (from PLAN2: WP-I beyond I0) | A | later families |
| SSA reads and `case` arms for real `always_comb` (from PLAN2: S1b): on the E route, `CombFragE` admits them and 2 of 6 ibex blocks are proved; the other 4 ibex block specs | L | later families |
| week-2 candidates from the WS1/WS2/WS3 Day-9 write-ups not listed above (`design/architecture/WS*-DAY9.md`) | The maintainers pick | backlog |
| loader coverage (`cv-width`, `inside` ranges, package-localparam enum widths, **unpacked arrays: the top refusal on every real-world sorter, MEASURED 11/03**, then `for` inside `always_ff` and async reset) | ls-sv lane | later families; unpacked arrays raised |
| formal tools (kernel-checked LRAT) | explorer | report only |
| RISC-V (`alu_div`, then `mult`) | none yet | backlog |
| spec reviews `clmul`, `aes_sbox`, `fdivp`; Task v2 packet; `Admissible` A1–A6; X-robustness route | The maintainers | independent |
| **Reactive controller tasks (decided 11/04)**: "sound interesting, since they are a category of tasks we don't have yet" (SYNTCOMP's controller specs). Note: [`design/reactive/README.md`](design/reactive/README.md).<br>• **11/05: ADDED (decided 11/05: "Please add it. I love new task types.")**, branch `svgolf-react`: `SvGolf/TaskReact.lean` (the kind, two named slots for the shared clocked conjuncts), `tasks/arbiter` a statement draft (goalpost `reference/rr_mask.sv`, 769.488 µm² × 2826 ps), `check.py` kind `react-family` (clocked rules, goal `Statement design.sem`, cycles = 1), the reactive post-synthesis check (segments, a 70000-entry reset-free run, salted, G0-G4 on the netlist, a Moore sample), the 17 attacks rejected (16 postsynth, 1 source), run.py steps; site hidden here. Walls: OpenTitan tree's generate-local declarations (ls-sv), a netlist-lint false rejection of a correct rotating arbiter (task README F5, F6).<br>• **11/05: the reference is PROVED, the task is `ready`, unranked** (branch `svgolf-react`): `reference/rr_mask.lean` for every `N ≥ 1` through the new `ReactTask.satisfiedAt_of_rank` (`SvGolf/React.lean`, the rank reduction; `SvGolf/RoundRobin.lean`, lowest set bit, thermometer, mask round-robin step); `check.py --postsynth full` ACCEPTS it (solution 8.25 s cold, 51.4 M heartbeats). Not seeded: the leaderboard has no clocked record format (task README F9). Tool gaps found by the proof: no closed clock step for designs with comb logic (F10), `sv2_inst_simp` stuck at `x != '0` (F11). Next reference: the OpenTitan tree, once ls-sv instantiates generate-local declarations.<br>• **11/06: txtask-v2's rules ported** (branch `svgolf-react`, task README §7): `ReactTask`'s claims hold from every power-up state (`ModelsPU`, `TerminatesPU`), rule 3 `XSafe` is a conjunct, the known-state clause KS is gone (implied: `ReactTask.snapshots_known`), `Interface` asks distinct declaration names (else `KnownEntry` leaves a port without a known entry), rule 1 not added (`MooreOut` already forbids comb input-to-output paths); the reference re-proved (+41/-11 lines, 53.3 M heartbeats, check.py ACCEPTS it); the audit's `bit_ring.sv` and `reset_edge.sv` refuted in the kernel; A16 refused at `score` as a never-loaded register; the reactive post-synthesis check from power-up states.<br>• **Was: DRAFT, on branch `svgolf-reactive`, not wired** into `tasks.lean`/`check.py`. A new kind `ReactTask` (safety monitor + bounded response, no environment assumption) and the first task `arbiter` (N clients, `K = N - 1`, scored at `N = 8`): `tasks/arbiter/Spec.lean` + `Refute.lean` (kernel-checked refutations, `bound_tight`), 17 attacks, `tests/arbiter/sim.py`. Reference: OpenTitan `prim_arbiter_tree` behind an output register, 668 µm² / 1454 ps at `N = 8`.<br>• **Review (11/04) found two holes.** H1, x-optimism on a never-reset register: a fixed-priority netlist at 280 µm² with a valid snapshot proof (MEASURED); fixed by a known-state clause KS. It also reaches `TxTask`/`StreamTask`, where only the post-synthesis check stands in its way. H2, the loader drops `areset`/`negedge`/`iff`, so `react-family` must be a clocked kind for the source gate.<br>• **Open:** the maintainers' rulings (note §9); ~~the reduction theorem and a proved reference~~ (done 11/05); ~~the `react-family` checker kind with a reactive post-synthesis check~~ (done 11/05); next tasks HSBUF (GenBuf), the AMBA AHB arbiter, the prioritized arbiter. Build plan: note §10. | reactive track | new category; awaiting review |

**Earlier architecture gates, carried forward explicitly:**
- **Passed** (EXECUTION-PLAN): G-A, G-L0..L3, G-B, R-COMB-1, R-DESIGN2 (comb and window-rank slices), the indexed
  `TripSchema` with lists as derived views, `computes_iff_computes_obs` for the comb profile, the abstract observation
  backend, and the negative cyclic case for R-COMB.
- **Carried into this plan:** fairness of schedules for edge processes (Gate 1's schedule class); the pre/post sample
  theorem for the flop-only profile (Gate 1 step 2, Gate 4); split proof measurements (every gate).
- **Deliberately kept:** E-core-0 small. New constructs enter E only with pinned rows.

## 5. The contract decisions (Gate 0; [M] = the maintainers rule, the default is in force until then)

**C1, reset [M].**
- A synchronous, active-high input `rst`, held at least 1 cycle.
- While `rst` = 1, `start` is ignored and nothing is claimed.
- Claims begin in the cycle after `rst` falls.
- Before the first reset, nothing is claimed, and the checker randomizes state there.

**C2, start and idle [M].** A formal predicate `Idle(trace, c)`:
- true from the first cycle after reset release until the next accepted start;
- true again from the first cycle in which `done` = 1, until the next accepted start.

The environment rely:
- `start` is a one-cycle pulse, raised only when `Idle`;
- inputs are known and held stable from the start cycle through the cycle in which `done` first rises;
- `start` on a cycle where `done` = 1 is accepted and begins a new transaction (back-to-back);
- inputs presented while not `Idle` are unconstrained and ignored by the claim.

**C3, latency [M].**
- The player supplies `lat : P → Nat` in Lean, with `lat p ≥ 1`.
- Latency is counted from the clock edge that samples `start`: `done` must first rise at some cycle ≤ `lat p` after that
  edge.
- Early completion is legal.
- Data-dependent latency is allowed, bounded by `lat`.
- The checker pins `lat p₀ = n` (the header), and the score uses n.

**C4, done and hold [M].**
- `done` is a level.
- Once high, it stays high, and the payload stays known and equal, until the next accepted start or reset.
- It is cared about and known in every cycle after reset release; x/z in `done` is a failure.

**C5, knownness [M].**
- The payload is cared about only while `done` = 1; elsewhere it is free.
- Before the first reset, nothing is cared about.

**C6, matmul [M].**
- Parameters: N ≥ 1, W ≥ 1, AccW ≥ 1. The accumulator width is renamed **AccW**, so `A` names only the input matrix.
- Inputs: two's-complement W-bit; products sign-extended; accumulation mod 2^AccW (ruled: overflow wraps).
- Output: C entries AccW bits each, two's complement.
- Ports: `clk, rst, start, A[N·N·W], B[N·N·W], done, C[N·N·AccW]`, flat row-major, with entry (i, k) at bit offset
  (i·N + k)·W, LSB first.
- No operator banlist.
- The scoring point is (N, W, AccW) = (4, 8, 32).

**C7, scoring.**
- **Ruled 11/03:** the cycle count is part of the proof (like proving an algorithm's step count). The score
  is that count times the shortest clock period the design allows, as measured by Yosys. A design cannot win by
  putting the whole circuit into one long cycle.
- Area includes flops at the sky130-ratio prices (separate flow; combinational records unchanged).
- Period = the critical-path depth (Gate 2 step 3) + a fixed per-cycle register overhead: sky130 `dfxtp_1` clock-to-Q
  plus setup, in NAND2-delay units from the pinned liberty (WP-X1).
  - Without the overhead, slicing work into one-gate cycles would be free in time.
  - SETTLED by the sky130 ruling (11/03): the period is the register-to-register path in ps from the pinned liberty, with the flop's own clock-to-Q and setup, so there is no ad hoc overhead. Unit depth stays as an extra column.
- Time = n × period.
- **Superseded (decided 11/05):** the ONE ranked number is area × time (par, record, under par, the leaderboard's
  order); the Pareto frontier of (area, time) is an exploration view. (Was: the leaderboard is the Pareto frontier of
  (area, time).) On a tie in both, the earlier record stands.
- One submission declares one latency; resubmitting with another n is a separate record.

**C8, the sorter's `StreamTask` [M].** A separate contract on the same rely/guarantee base (not an overloaded TxTask).
- Ports: `clk, rst, start, in_valid, in_data[W], out_valid, out_data[W]`.
- **Input side:**
  - after an accepted `start` (C2), `in_valid` = 1 for exactly N consecutive cycles beginning the cycle after start,
    each carrying one value; no gaps in v1;
  - N ≥ 1 and W ≥ 1, values unsigned.
- **Output side:**
  - exactly N cycles with `out_valid` = 1, not necessarily consecutive;
  - their values in order = `List.insertionSort (· ≤ ·)` of the inputs, so duplicates are preserved;
  - the last of them ≤ `lat p` cycles after start;
  - no backpressure in v1;
  - `out_valid` is known in every cycle after reset; `out_data` is cared about only when `out_valid` = 1.

**C9, form [M].** v1 form now, over run2. The maps to the D11 contract and to Task v2 come as untrusted theorems later.

**Ruled 11/05.**
- **What ranks:** "keep it simple for the site's headline, and then give more tools for exploration under the
  individual tasks": the ONE ranked number is area × time (the headline, par, record, the leaderboard's order); the
  Pareto front, the x-y explorer and the scaling view are exploration. C7's "the leaderboard is the Pareto frontier"
  becomes exploration; leaderboard.py and the README follow.
- **Re-seeding:** the record fingerprint stays strict (a score is tied to an exact scorer); after a checker-file change
  the reference records are re-seeded as a routine step.
- **Layouts:** place-and-route for the detail pages runs nightly in the public repo's GitHub Actions; a run that
  times out is noted on the page, and we decide then what to do instead.

**Already ruled.** Matmul overflow wraps (decided 11/03); a clamp task may come later. No banlist for matmul (decided
11/03). The clock is clocking, not observed (decided 11/03).

## 6. Measured artifacts required at every gate

- **Lines, split** into library plumbing / invariant / arithmetic / statement glue.
- **Cost:** elaboration time and heartbeats per theorem, `.olean` sizes, generated equation counts.
- **Axioms:** `#print axioms` for every headline theorem, compared to the recorded baseline.
- **Checker:** stage times, trace lengths, scores (twice from clean checkouts), and the pinned tool versions (Yosys,
  ABC, Verilator, Lean).
- **Build:** a fresh-checkout build at each gate.

## 7. Risks

- **The symbolic-N always_ff agreement (2c).** It is new. The fallback is declared (Gate 1).
- **Contract churn after code.** Gate 0 freezes first; changes after `txtask-v1` need the maintainers and a version bump.
- **Proof time limits** (G2, `fdivp` after inlining). Measure at each gate; the answer is a cheaper proof, never a
  per-task library.
- **Post-synthesis trace length** for wide matmul ports. Use modest transaction counts in light mode and corner sets in
  full mode.
- **Drift:** master's ls-sv lane changes core files daily. Every branch merges prep daily. After each sync: the
  dependents build, every task's REFERENCES (not just the design attacks), and the design attacks.
- **Slot contention:** short acquisitions, suites in segments.
