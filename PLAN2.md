# svGolf: plan for the next seven days (week 2, Fri 10/30 to Thu 11/5)

> **Superseded (11/03) by [PLAN4.md](PLAN4.md), the one active plan.** This file is the record of week 2: its decisions,
> measurements and landed work. Its two open items are carried into PLAN4 §4: WP-I beyond I0 (now R-HIER) and the S1b
> "SSA reads / case arms" item (now on the E route via `CombFragE`). Status marks here are no longer updated.

Written 10/30 after the first plan (`PLAN.md`, Days 1 to 7) was built and verified. That plan gave
the framework: the trusted statements, the checker, the scoring flow, the leaderboard, the `sv_comb`
tactics, four tasks and their references (`add` ×2, `mul` ×5, `_example`), the dry run. This one is
about what the dry run, the profile of the proofs and the maintainers' requests showed to be next: **better
tactics, a faster and cleaner proof API, wider SystemVerilog coverage in ls-sv, better tasks and reference
proofs, a parametric floating-point divider**, and the checker and process work around them.

Conventions are those of `PLAN.md`: `[x]` done and verified, `[~]` in progress or partial, `[ ]` open;
"WP-x" is a work package (a brief in the lead's scratchpad, one agent, an independent re-run by the lead
before anything is committed); ls-sv changes (`LeanModels/Sv`, `extractors/sv`, `harness/sv`, `docs/sv-*`)
go to `github/master` small and often (fast-forward, never force), `svgolf/` stays on `svgolf-prep`.

## 0. Where we start (10/30, morning)

| | state |
|---|---|
| tasks | `_example`, `add`, `mul` ready with proved references; `fdiv16` ready (WP-H2: the flat reference is proved, `tasks/fdiv16/reference/fdiv16.lean`) |
| `mul` references | array (tactics and by hand), heap tree of 4:2 compressors, Wallace tape, `localparam` heap tree (WP-F, accepted, in regression) |
| tactics | `sv_structure`, `sv_equations`, `sv_cover`, `CombLib`; fragment: flat top, `& \| ^`, generate loops (2 deep), 1-D/2-D arrays, concatenation, part-selects; `localparam` atoms from WP-F |
| speed (measured) | tactic proofs 30 to 90 s to elaborate, by hand 3 to 8 s; `sv_structure` and the ports recipe re-derive the same summary; `simp` is the largest bucket |
| running now | WP-F (`localparam`, finishing its regression), WP-H1 (parametric fdiv: task statement, certificate for every format, recurrence arithmetic, design draft) |
| queued, briefs written | WP-P (proof API and speed), WP-G (`always_comb` bodies, `~`, `?:`) |
| red, not ours | six `Examples.python.*` modules in the repo-root `lake build` (the Python lane's own agent) |

**The binding constraint is the single Lean slot** (16 GB machine, one Lean job at a time). Plain-Lean
and Python/SV-simulation work runs beside it, but every tactic, library or reference change queues for
the slot. The schedule below serializes the Lean-heavy packages and fills the gaps with slot-light work.
A rough capacity: one Lean-heavy package per half day to one day.

**Slot rule (from the 10/30 plan review).** At most one process may invoke Lean or `lake` at a time (the
Lean-slot wrapper queues them); this includes plain-Lean work such as the fdiv certificate. Work is
classed as *slot-light* (Python, Yosys/Verilator, Xcelium differential cases, oracles, docs; may run beside
Lean), *plain Lean* (consumes the slot) or *`LeanModels.Sv` builds* (consumes the slot and rebuilds
dependents). The two-hourly integration is a source-control cadence, not a build cadence: a package may
prepare a commit at any time, but its independent verification waits for the slot.

## 1. Goals of the week (acceptance, measurable)

Each goal is split into a **hard gate** (the week succeeds if these hold) and **stretch** (reported, never promised).
Under the single Lean slot the hard gates are all the schedule can honestly carry; slippage drops work from the
bottom of the list in section 3.

0. **Correctness first (hard, before more SystemVerilog is declared supported).**
   - **WP-E1** (DONE, on main `fcb74cdc`; Xcelium-pinned rows, 2167 extractor tests, a general select-window consistency guard): constant element/range selects through multi-dimensional packed struct/union members were
     lowered in bit units, a silent wrong value with `hasUnsupported` false. Acceptance: every constant select has a
     checked source width, any mismatch becomes a loud refusal, the discovered cases are regression tests with
     Xcelium-backed differential rows. It is a dependency of any task whose source uses packed selections.
   - **WP-C3** (folded into WP-C2): the `design` stage rejects an envelope that contains an `Unsupported` process
     (`Design2.hasUnsupported`) with a clear message, before any proof, scoring or leaderboard verification. Today
     nothing in `check.py` tests it explicitly: the case is only caught indirectly (the proof of `Terminates2`
     cannot exist; the post-synthesis check reports that ls-sv does not support the design).
1. **Faster proofs.** WP-P gate 1 (DONE, measured; `svgolf/PROVING.md`-style table in its report) CORRECTED the lead's first
   profile: the "ports step 29 s" was an ARTIFACT of asynchronous elaboration (the aux-lemma `decide +kernel` waits on other
   threads); alone it costs 2.3 s CPU (wallace), 1.0 s (add_n), 4.5 s (tree). That target is withdrawn. The real hotspot is the
   simp normalization of the tactics' obligations (`sv_norm_core`): wallace 35 of 53 s CPU, tree_h 96 of 112; the rank obligation alone
   12.75 s (wallace), 14.3 (mul_n), 42.8 (tree), 33.2 (tree_h); cover obligation 6.4 s (wallace), 22.5 (tree_h); the auto + in-range
   obligations are recomputed four times (comb, acyclic, interface, equations); the summary derivation itself is only 0.3 to 1 s, so
   a cached summary alone buys little, SHARING THE OBLIGATION WORK is what pays (about 9 of 53 s on wallace). Refuted: leanchecker
   does not replay the library (it replays the named modules; library import costs 1.3 to 1.6 s CPU). New thresholds, user CPU
   seconds on the reference machine, hypotheses until P1/P2 are measured: `mul_wallace` baseline 49 s CPU (wall 51 under load),
   first acceptable <= 35 s, stretch <= 25 s; `mul_tree` baseline 98 s, first acceptable <= 70 s. Hard:
   the profile table and the first acceptable improvement; every measurement records commit, clean/warm build,
   wall and kernel time, `maxHeartbeats`, `.olean` size, axioms and whether the full reference suite ran.
2. **A clean proof API.** Hard: P1 (shared summary, `sv_interface`, `add_n` migrated, no `Summary`/`sigma_L`/
   `Summary.sound` recipe in it) and P2 (stable equation names/bundles, the named knownness theorem, `add_n` on
   the new API). Stretch: P3 (canonical Nat-indexed row-major view; `mul_final` without casts), then P4 (2-D
   coverage rules, rank diagnostics). P4 is not started on top of an unstable P3.
3. **`always_comb` (WP-G).** Hard: the four-state contract note, the minimal fragment (`always_comb`, blocking
   assignments, `if/else` on known conditions, no latch, no self-read), and an `add` reference whose carry is an
   `always_comb` body, proved for all N. Stretch: `~`, `!`, `?:` with their four-state truth tables pinned by
   differential cases. Later (only if a chosen task needs them): block-local temporaries beyond the minimum,
   procedural loops.
4. **Parametric fdiv, part one.** Done and verified: the rounding certificate for EVERY format `(w, p)`
   (symbolic) and the task-statement design (Option C, no trusted change). Hard for the rest of the week: the
   format well-formedness predicate written down. Stretch: the digit-recurrence lemmas in plain Lean (they consume
   the slot) and the parametric design draft validated exhaustively on small legal formats and by sampling on
   binary16/32. H2 (the design-level proof) starts only if WP-G and the gate-level fallback are green.
5. **Wider SystemVerilog in ls-sv: four features.** Hard: genvar step `i = i + 1`, `~^`, block-local temporaries
   with the minimal `always_comb` fragment, plus exactly ONE task-driven item chosen by the first accepted task's
   actual source (not by the generic register ranking): `st-for` if popcount is next, `ex-user-call` if the fdiv
   draft or a realistic corpus is blocked by helper functions, `casez` only if leading-zero count is definitely
   next; `aes_sbox` itself needs none of them. A feature counts as supported only after parser, symbolic
   semantics, extractor lowering, differential cases, an Examples proof and the register update. Everything else
   in the T2 table is backlog.
6. **One new task: `aes_sbox`.** Hard: reviewed trusted `Spec.lean`, oracle, baselines, tests (a task without a
   proved reference is `status: draft`, like `fdiv16`). Target: the Boyar-Peralta reference proof (113 sites; also
   a tactic-scalability measurement). Further specifications may be drafted but are not gated.
7. **Checker and process.** Hard: WP-C2 (light post-synthesis by default for LOCAL checks; `leaderboard add`,
   `verify` and all official artifacts always full; light records explicitly marked and never official), the exact
   time-limit rule (section 4 of T4), WP-C3. Stretch: nightly regression script, contributor guide.
8. **Sequential boundary.** This week's sequential acceptance is the design note (done), the S0 clock-discipline
   refusal (WP-Q0, a named serialized package after P2) and the existing counter sketch as evidence. No public
   sequential task, no `SeqTask` checker integration and no clocked PPA score are required this week.
9. **PPA boundary.** Hard: WP-X1's report (sky130 facts, A0'/A1' measurements, migration plan). Stretch: the first
   `score/ppa.py` columns. No default-board change.

### Status of the hard gates (updated 10/30 evening)

| goal | hard gate | state |
|---|---|---|
| 0 | WP-E1 select-width fix; WP-C3 unsupported-envelope rejection | DONE (`fcb74cdc`; `827da333`) |
| 1 | profile table; first acceptable speedup | profile DONE (corrected two artifacts); speedup partly: heartbeats -15..-25% on all five references (`mul_wallace` 775 -> 655 M, CPU about 36 s on a loaded machine, near the 35 s first-acceptable line); the rank-obligation normalization (12.8 s of `mul_wallace`, 43 s of `mul_tree`) is untouched and the two trees' critical path did not shrink |
| 2 | P1 shared obligations + `sv_interface`; P2 stable names + knownness theorem | DONE (`90772f97`; five references 23 code lines shorter; stretch P3/P4 not started); P3b DONE (10/31; ls-sv master 103ff293, svgolf-prep b36f1d37 + 5e965ef9): `sv_structure` and `sv_equations` DECIDE the obligations of a flat netlist (no loop, no parameter) instead of normalizing them (113 gates: structure from a failure after 4 minutes to 12 s / 122 M heartbeats at the default 200000; `sv_equations` 58.6 to 11.3 s; no `cover_k`/`width` goals for such designs), alias naming by `n <=` spine length, `withDeepRec` (no `maxRecDepth` in the player's file), `sv_cover` site witnesses for the designs the fast path does not take; 24 goal dumps byte-identical; full suite on the merged tree 386 checks, 0 failed (3154 s); the `aes_sbox` reference 654 -> 295 lines (202 code lines), `solution` 51 to 54 s cold, limit 385 -> 215 s; PROVING section 12 carries the before/after tables; NOT done: `always_comb` (lowered) path fast path. Original request text: in `runSvStructure`, when no site has a loop (`hdrs = []`) close `hdisj` and `hrank` with `closeByDecide` instead of `sv_norm` (the proof's `disjObl_plain`/`rankObl_plain`, 4 lines each, move into `CombViewThm.lean` verbatim); count sites structurally in the alias naming of `sv_equations` (it gives up when the last assign drives a bit of a vector output); let `sv_cover` pick a site witness by the writer's name; default `maxRecDepth` for the tactics. Lands after WP-G's Gate 3, because both edit the tactic front end |
| 3 | WP-G contract note, minimal `always_comb`, all-N `add` reference | DONE 10/31, hard gate met: contract note (`svgolf/design/always-comb/README.md`: four-state truth cases reproduced on Xcelium, fragment S1, equation shape, alias ordinal rule), G2.0 spike GO (629 lines, 7 s), G2.1 (`CombProcStmt`/`CombProc`, on master 65a04b14) and G2.2 (`CombProcSummary`/`Lower`/`Eq`/`Tactic`, on master 497aa2df, all additive: a second elaborator on `sv_structure`/`sv_interface`/`sv_equations`, falls through on every existing goal shape; goal dumps of the five references byte-identical with and without it). `tasks/add/reference/add_proc.{sv,lean}` (carry cell as an `always_comb` `if`/`else`) is PROVED for every N and accepted by `check.py --postsynth full`, scoring exactly as `add_n` (56/112/224 GE at N = 8/16/32). A refused body logs the planned tactic message and admits the goal, so it cannot build (`tests/add/negative/add_proc_case`, `comb_errors` pins `sorryAx`). Effort: about 1.5 slot-days against the re-estimate of 4 to 5. Not done (stretch): S1b multi-window, S2 `~ ! ?:`, S3 `case`/temporaries, consolidating the copied soundness chain (`G22-NOTE.md` lists the copies), `check.py --tactics` probing the lowered shape |
| 4 | fdiv format well-formedness predicate | DONE (`b98b1702`: `FORMAT.md` + `FormatFacts.lean`; certificate and statement design DONE earlier) |
| 5 | genvar step, `~^`, local temporaries + minimal `always_comb`, one task-driven item | L1 genvar step DONE and on master (5a4c4cc5, extractor-only lowering of the five +/-1 spellings to the `++`/`--` node; strides and parameter amounts stay loud; `i = i + 1` adder proved for all N by the unchanged tactics); L2 `~^` DONE and on master (d9eba5b2; extractor-only lowering of binary `~^`/`^~` to `~(a ^ b)` in signal expressions, 13 differential rows with Xcelium pins, Table 11-14 proved for every width; constant positions and a signed pair into a wider target stay loud; the sv_comb recognizer still rejects unary `~`, so tactic-route netlists write XNOR as `x ^ y ^ 1'b1` until WP-G adds `~`); the minimal `always_comb` DONE with WP-G (row 3); the task-driven item is `aes_sbox` (row 6); local temporaries (a `LocalDecl` is refused by the loader today) are NOT done (S3, stretch) |
| 6 | `aes_sbox` reviewed Spec, oracle, baselines, tests (draft) | DONE, and the reference PROOF landed: task `ready` (gate 1 18cc2acf; gate 2 acb6d8b7; full suite 378 checks, 0 failed; post-merge with always_comb 382 checks, 0 failed after the runner builds the ls-sv modules proofs import): fixed 8-bit, no banlist, Spec + oracle (= FIPS 197 Table 4 on all 256) + REVIEW.md; the 113-gate Boyar-Peralta reference is PROVED (654 lines, about 100 of mathematics, standard axioms, 99 s CPU, `solution` stage about 95 s cold, limit 385 s), 200.986 GE / depth 21; case table 786.894 GE / depth 11; depth-16 circuit 216.322 GE / depth 18; 7 negatives, 4 attacks, 4 functional advisories, exhaustive post-synthesis. MEASURED TACTIC LIMIT (the reason the task exists): `sv_structure` is about n^1.9 in the number of sites and fails at 113 plain sites (6,328 pairwise-disjointness goals and the rank obligation simp'd one by one; 4 m 23 s then recursion depth); the proof applies `comb_acyclic_view` by hand and has the kernel decide the two closed obligations (19 s). `sv_equations` works (35 s) with `maxRecDepth`. FINDING for the maintainers: statement order moves a flat netlist's score (198.986 to 209.321 GE across orders of one circuit), so `sbox_bp.sv` is not in `canonical_layout` |
| 7 | WP-C2/C3, time-limit rule | DONE (`827da333`); limits unchanged after WP-P's cold runs (`mul` 400 s: `mul_tree` 97 s cold vs 100 s) |
| 8 | S0 clock-discipline refusal | DONE (`c3119f74` on main: `Clock:source/reset/multiple/data-read`, 17 fixtures, 18 differential rows, Xcelium-pinned; found by the lead afterwards: the two svGolf dead-clock Lean refutations had to be retired because the loader now refuses those designs first) |
| 9 | WP-X1 report | DONE (`3cb773dc`) |

Stretch items finished 10/31 evening (svgolf-prep): `nightly.py` (suite + register/docs/time-limit checks, report, diff against
the last run; README "Tests"); `check.py --tactics` reads the `always_comb` LOWERED goal when the plain probe is refused
(`22845385`: `add_proc` in_fragment true + `lowered`, `add_proc_case` the `case` refusal; two advisory attacks); PPA stage 1
(WP-X2, branch merged): `score/ppa.py` + `ppa_pins.json` + `PPA.md` + `test_ppa.py` (30 tests, in the unit step), columns
`area_um2_sky130` / `delay_ps_sky130` / unit depth beside the unchanged default board, WIRED INTO `check.py` by WP-X3 (merged 10/31 after the maintainers said to wire it: `--ppa {auto,off,require}`, the result key `ppa`, the
tripwire list, `leaderboard.py` records and `pareto --axes`, a `ppa` step in `tests/run.py`; the liberty is fetched by pinned hash,
not vendored; A0' is the pinned flow; A1', tie bands and the hidden-seed holder remain the maintainers');
measured on 16 designs: GE vs um^2 tau 1.00 / 0.90 / 1.00 (add / mul / aes_sbox), unit depth vs delay tau 0.95 / 0.59 / 1.00;
the study's "1.3% vs ABC stime" is a Nangate45 figure, on sky130 the port gives mean 1.96%, max 6.7% (do not quote 1.3%).

Stretch items finished 11/01 (all on github/master through changelog 0.1.364, `7f7c5722`; svgolf-prep merged it as `d9558d82`):
the `always_comb` fragment now covers `~ ! ?:` and the reductions (S2), a `case` with constant items (S3a, `aes_sbox` `sbox_table`
proved, 786.894 GE), default-then-override (S3b) and bodies that write SEVERAL windows (S1b gates a to c4: `CombProcBody`,
`TSite.more`, window lists through the realization chain, `sv_structure` accepts the body, `cell_lowers_site` lowers the
carry/sum cell of `add_proc` at every N and bit; `sv_equations` refuses such a body with the reason, the equations are gate d);
consolidation Tier A and B (the soundness halves share their cores, 89 lines fewer, every old name kept); gate M (the tactics do
not depend on Mathlib's simp set); B2 word-level gates 0 to 2b (unsigned `+ -` with the Resize markers, the six comparisons,
truncation markers over operations, unsized constants, each row Xcelium-pinned; concatenation as an operand and run-time shifts
are gate 3). Cost of all that to a golfer's proof: heavy references move by at most +0.3% in heartbeats against the state before
S1b (`sbox_bp`, `mul_*`, `sbox_table`); `lp_correct` without its own `set_option` needs 199.4k of 200k, `add_mux_correct` (an
Example proof, now three declarations) 188k. Process lessons recorded: a proc-tactic simp list must not gain new names (+1 to
+4.6% on every proc-tactic theorem), and a batch under the Lean-slot wrapper must not export `SVGOLF_LEAN_WRAP` (self-deadlock). The first
full suite on the merged tree (`nightly.py`, `nightly/20261101T1000`) was started after the last push. Open follow-ups, in the
order I would take them: S1b gate d (equations of a multi-window body), S1b SSA reads (a read of an earlier window of the same
body), B2 gate 3 (run-time shifts) and concatenation operands, `case` tree arms, WP-I I0 (a truthful message at the three
`findGD2` copies), fdiv16 H2.

Later on 11/01 (merged into svgolf-prep): the full suite on the merged tree PASSED (486 checks, 0 failed, 5333 s); the maintainers answered the
status report (rulings in the register policies: loops stay refused, L1 settled run, an Xcelium-only dissent is not a split, host access
beyond files disallowed, slang analysis errors count as illegal, Mathlib wide roots kept, sandbox policy signed off, public board by pull
request with CI re-verification; `\xHH` stays refused and `native_decide`/`extern`/`implemented_by` stay refused as the lead's decisions);
WP-I step I0 is on master (0.1.367: the tactics say "this design instantiates modules"); `lake build Batteries` makes a whole-library
`import Mathlib` load (110 s cold, 3.8 GB); WP-X4 landed the A1' flow (`ppa.mapped`, a real `abc -liberty` mapping, pinned script and
builds, goldens for 24 designs, deterministic across seeds/TMPDIRs/parallelism) beside A0', neither official ("I don't really care
what's official for now; but why not A1? It's like not using -O3"). Measured A1'/A0' on 16 designs: area median 0.93 (0.68 to 1.23), delay
median 1.14; the proved array multiplier goes from first to last in area among the four proved multipliers, the `sbox_table` design drops
32% in area while the Boyar-Peralta circuit rises 23%. In flight: S1b gate d (equations of multi-window bodies, design accepted),
B2 gate 3 (3a run-time shifts merged, 3b nested concatenation running), WP-R-D DONE (`\a \v \f` admitted, slang analysis errors refused, on master),
WP-BV DONE AND REVERSED (the comparator re-verification of `bv_decide` axioms was built, then it was ruled 2026-11-01 "let's not support external
solvers for now" because the solver needs fork, exec of `cadical` and a writable TMPDIR in the sandbox: `BV_DECIDE_SUPPORTED = False` in check.py, the
groundwork stays dormant and tested), WP-T-CLMUL (new task, running), WP-H2 (fdiv16 proof, feasibility spike running), WP-RB0 (census of real RISC CPU
blocks against ls-sv, running) and a real-world SystemVerilog survey workflow (8 families, running).

Status 11/02 (the lead; PLAN2 is DONE as far as its hard gates go, and the rest has moved on). Hard gates 0 to 9 (table above):
all done. The 11/01 in-flight list, closed since:
- S1b gate d. Equations of an `always_comb` body that writes several windows, with the `add_proc_m` reference proved by the
  same proof.
- B2 gate 3 (run-time shifts, concatenation as an operand) and gates 4a to 4c: loop-indexed rows, a genvar shift amount,
  replication `{N{x}}`.
- WP-H2. `fdiv16` is `ready`: the flat 111-site reference is proved, and a second generate-for reference is proved with the
  `fdivp` glue.
- WP-H3. The parametric divider `fdivp` is proved for every format, and the task is packaged.
- WP-T-CLMUL. The `clmul` reference is proved for every N, with an exhaustive rank classification and a coverage theorem.
- WP-LIN. The quadratic obligations are grouped by signal.
- Also done: WP-PROC G1 and its three follow-ups, WP-COV, the WP-RB0 census of 85 real CPU blocks, and the register-rulings
  packages (the source gate refuses host access; Mathlib in submissions measured; tools-split audit; nondeterminism note).
- Decided 11/02: one proof time limit of 120 s for every task, and the scorer kills a timed-out tool's whole process group.
- Decided 11/02: two architecture rulings. SystemVerilog's exact semantics is the authority, and cycle views and contracts are
  derived, each with a refinement theorem. Loops are never lowered. The architecture is decided
  (`design/architecture/ARCH-NOTE.md`), and its execution plan (`design/architecture/EXECUTION-PLAN.md`, weeks of 11-03 and
  11-09) carries the remaining work.
- Decided 11/03: `fdiv16` is folded into `fdivp` (binary16 is its instance `(5, 11)`, the scoring point) and no task ships a
  proof library: the reusable lemmas are `LeanModels.Sv.Lib` (ls-sv), the rest is one self-contained
  `tasks/fdivp/reference/fdivp.lean` (cold solution stage 64 to 72 s, over the 60 s target, under the 120 s limit); the
  trusted IEEE 754 spec is `tasks/fdivp/IEEE754.lean` (moved unchanged, with `spec_validate/`); `svgolf/spec/` and
  `tasks/fdiv16/` are gone.
Not done from this plan:
- WP-I beyond I0. This is now R-HIER, in E-core-2 of the execution plan.
- Reads of an earlier window of the same body (S1b "SSA reads") and `case` tree arms. No commit yet. WS4's X7 slicer (11/02,
  `arch-measure` `e7c1fa44`) found these are what keeps real ibex blocks off the route: 6 `always_comb` blocks of `ibex_alu`
  in the ordinary style (a default then a `case`, an `if/else` after the first statement, `unique case (1'b1)`). The same
  measurement found that package enum constants need width-exact typed localparams in the recognizer (`lpTypeOk` admits
  int/integer only). `[~]` 11/03: on the E route rather than the `run2` tactic route, WS3's `CombFragE` (`arch-loop` `d7af3dac`) admits `case` of
  every kind, `if/else` anywhere and bodies writing several signals. Two of the six ibex blocks are proved against the exact
  semantics, and all six are in its fragment.
- P3/P4 of WP-P.
- Signed word-level operators.
- `integ1102` is now landed: built with current master, `svgolf-prep` fast-forwarded to it, and the ls-sv parts pushed to master
  (`76b96afd`, 11/02 21:40). The scoped suite on the synced tree then passed with 0 failures (11/03 00:58).

Decisions of 2026-10-31 (answers to the status report): (1) statement order moving a flat netlist's score is ACCEPTED
(golfers run ABC or the pinned flow themselves and submit the best order; no canon change); (2) the four `aes_sbox`
`REVIEW.md` questions are all accepted as written (ports `x`/`y`/`aes_sbox`, `ginv` as `a^254`, fixed 8-bit, Boyar-Peralta
as cited baselines); (3) the sky130 columns are to be WIRED IN as extra columns (default board unchanged), WP-X3; (4)
`~ ! ?:` first, then B2, as one family; word-level operators should generally be available to every task EXCEPT the
tasks that are about implementing the arithmetic itself (`add` and `mul` keep their `+ - *` banlists; `fdiv` bans only
`/ %`), and the B2 note's detail questions take the lead's recommendations (faithful nested form, variable shifts in and
`*` out, signed deferred); (5) keep going on stretch work as long as there is work. Older open items (98.7% wording, `never`
section, `sv-div-1`, `dyn32`, record hand-off) wait for the maintainers to pick which to discuss.

Further rulings of 2026-10-31 (on the register's `never` rows): classes are ignored for now (the scored frontend is Yosys
`read_verilog -sv`; a future synthesis frontend may change that); a slang-illegal program is rejected; tools-split refusals follow
"Verilator, Yosys and Xcelium (and slang) agree is enough" (Icarus-only splits are declared departures); LRM-legal
NONDETERMINISM is to be modelled in Lean and the golfer proves the final output deterministic unless the task does not require
it; host access (file reading and the like) is disallowed; Mathlib is ALLOWED in submissions. Work packages launched
(workflow `register-rulings`): A source-gate host-access hardening (finding: `$readmemh`, `$fopen`, `$system`, DPI,
`$value$plusargs` pass the gate today, only `` `include `` is refused), B Mathlib in submissions (spike first), C tools-split
audit + register edits + nondeterminism design note.

## 2. Tracks and work packages

### T1. Tactics (`LeanModels/Sv/CombView*`, `CombKnown*`, `CombEq*`, `CombLib`)

Order matters: the packages edit the same front-end files, so they run one after the other.

- **WP-F** `[x]` DONE and on main (`042ab83f`; regression 293/293 on the svgolf side, library chain and Examples rebuilt on the current master). `localparam` atoms. Typed `int`/`integer` localparams enter the summary as integer atoms with
  their defining equation; `/` and `%` by literals stay linear for `omega`; output for existing designs
  byte-identical (checked on `add_n`, `mul_tree`, `mul_wallace`). Accepted payoff: `mul_tree_h`
  (heap tree with `H = (N+1)/2` leaves) 2025.905 GE / depth 62. Left: regression, integration to main.
- **WP-P** `[x]` (gates 1, 2 and P3b done, status table row 1-2; P3/P4 not started, superseded by WP-LIN) proof API and speed, in four gates with stable stopping points (starts when WP-F is integrated):
  **P1** one cached summary shared by `CombDesign`/`Acyclic`/interface, `sv_interface`, `add_n` migrated,
  baseline timings and `.olean` sizes; **P2** stable equation contracts (aliases by target signal and role,
  optional record bundles, old names kept), the generic knownness theorem named and cited by `sv_equations`
  ("settled state + known inputs + rank => every supported read is known"), `add_n` migrated; **P3** a
  canonical Nat-indexed row-major view with raw-to-canonical bridges (`mul_final` loses its casts); **P4**
  2-D coverage rules and dedupe, rank diagnostics printing the failing edge, the multiplier references
  migrated, final timings. The speed targets are hypotheses until the first profile: `mul_wallace` 37 s
  baseline, <= 25 s first acceptable, <= 20 s stretch; ports step 29 s, <= 10 s, <= 3 s. Every measurement
  records commit, clean/warm build, wall time, kernel time, `maxHeartbeats`, `.olean` size, axioms and whether
  the full reference suite ran.
- **WP-G** `[x]` (gate 3 and S1a-S3b, S1b gates a to d done; see the status entries) `always_comb` bodies (brief written and amended). A four-state CONTRACT note comes first: a
  procedural `if` with an x/z condition takes the else branch, a conditional expression `c ? a : b` with c = x
  merges bitwise, `!` is not `~`; these are different rules and each is pinned by differential cases. First
  fragment: `always_comb`, blocking assignments, `if/else` on known conditions, no latch, no self-read; each
  written bit gets one equation `x = if c then e1 else e2`. Then `~ ! ?:` once their truth tables are pinned;
  block-local temporaries next; procedural `for` loops with accumulators are a separate, later gate.
  Acceptance: an `add` reference whose carry is an `always_comb` body, proved for all N.
- **WP-B2** `[x]` (gates 0 to 4c done; signed still deferred) word-level operators (`sv_bitvec`): `+ - == < <= >> <<` by literal, word concatenation
  and reduction, as equations over `BitVec` with the width rules of ls-sv, so a design that writes `a + b`
  or `x < y` (allowed in `fdiv`, which bans only `/ %`) can be proved without a gate-level rewrite.
  Needs the shape of WP-G's equations. Design note first, then ONE operator end to end (unsigned `+`), then `==`, unsigned `<`, literal shifts; signed later. Each operator has width, signedness and four-state rules to pin. Highest
  risk of the tactic items; if it does not land the fdiv design is written at gate level.
- **WP-I** `[~]` (I0 done; the rest is R-HIER in E-core-2 of `design/architecture/EXECUTION-PLAN.md`) (later, design only this week): module instances in `sv_structure`/`sv_equations`
  (`Hier2`), then recursion (F3b); the sequential layer stays deferred (combinational first).

### T2. SystemVerilog coverage in ls-sv (`LeanModels/Sv`, `extractors/sv`, `harness/sv`)

Method for every item (the "feature PR" a contestant would send, which the maintainers approve): semantics in the
symbolic tier, extractor lowering, **differential cases** in `harness/sv/cases2.json` with `measured`
fields and the Xcelium pin refreshed on a licensed Xcelium host (the golden file is data), a
small `Examples/system-verilog/` proof, the register row moved from `later` to supported
(`tools/gen_sv_refusals.py --write`, `--check` green), then push to main. **Commitment for the week (from the plan review): three items** (genvar step, `~^`, block-local temporaries with
the minimal `always_comb` fragment), **plus exactly one task-driven item**, chosen by the first accepted task's actual source (goal 5: `st-for` for popcount,
`ex-user-call` for helper-function-blocked designs, `casez` only for leading-zero count; `aes_sbox` needs none). Everything else below is backlog. A feature counts as
*supported* only when it has passed all of: parser, symbolic semantics, extractor lowering, differential
cases against the pinned simulator, an Examples proof, the register updated; the register notes the stage each
feature has reached. Candidates, in value order from the register and with what each unlocks:

| item (register id) | unlocks | day |
|---|---|---|
| genvar step `i = i + 1` (`le-generate-genvar-step`) | removes the README contradiction found by the dry run; cheap | 2 |
| `~^` xnor (`ex-xnor`) | native gate for golfers | 2 |
| block-local temporaries in `always_comb` (`ld-localdecl`) | idiomatic bodies; needed by WP-G designs | 3 |
| procedural `for` loops with accumulators (`st-for`, rank 1) | popcount, parity, carry loops | 3 to 4 |
| constant functions / helper functions (`ex-user-call`, rank 2) | `$clog2`-style helpers, Dadda schedules, bit tricks | 4 |
| `$countones` and friends (`ex-builtins`) | popcount task variants | 4 |
| `casez` wildcards (`st-casez`) | leading-zero count, priority encoders | 5 |
| `unique`/`priority` with proof obligations (`st-cond-qual`) | The maintainers want the obligation encoding; after `casez` | 6 |
| size casts `N'(x)` (`cv-explicit`), 2-state `int`/`bit` (`dc-2state`), signed (`dc-signed`) | typical golf code, comparator task | 6 to 7 |
| assignment patterns `'{...}` (`ex-assign-pattern`), `inside` (`ex-inside`), compound `+=` (`st-compound`) | lookup tables, decoders | as time allows |

**Audit of the "98.7%" claim (10/30, workflow of seven agents; answers the maintainers' question).** The README figure is
472/478 self-check rows (now 505/517 = 97.7% on master): tiny hand-written `initial`-only programs (median 17
lines, one operator or builtin per file) of the M0 self-check tier, whose oracle is the test's own declared PASS
line; it measures a regression suite, not the language, and it is not the symbolic tier svGolf proves in. The
same page: 120/235 syntax kinds MATCH, 5,901/22,071 sv-tests files extract cleanly (26.7%). The symbolic tier
has its own differential (684 rows, 426 simulated, 258 loud refusals, pinned against Xcelium). Probing that tier
with 100+ realistic designs: of eight RTL staples 4 are fully usable (enum FSM, counter, LFSR, unique/priority),
3 load but carry unsupported processes, 1 is refused; of five advanced designs (accumulator CPU, UART, sync FIFO,
AES round, SHA-256 round) **0 of 5 are usable as written**, all 5 work after rewrites (CPU and UART in 1 to 10
lines of edit; FIFO loses its unpacked memory; SHA loses its helper functions; AES becomes a flat vector with
generate loops). Blockers by frequency: user functions, run-time-indexed unpacked arrays (memories), procedural
`for` loops, explicit casts and typedef'd packed widths, scalar `wire` declarations, signed/2-state, `inside`,
enum methods, interfaces/modports, case-generate; classes, SVA, coverage, DPI, the scheduler are outside. Findings
to act on: (1) **a silent wrong value** in the extractor (constant element/range selects through multi-dimensional
packed struct/union members lowered in bit units, `hasUnsupported` false): fix package WP-E1 is running, with
a general select-width consistency check that turns any mismatch into a loud refusal; (2) the extractor exits 0
and `load_design_sv2` accepts envelopes that contain loud `Unsupported` processes, so "loads" is not
"usable": svGolf's `design` stage must be checked to reject `hasUnsupported` (verify; add if missing); (3) the
README bar should say what it measures (proposed wording in the audit report; the lead drafts it, the maintainers
approves); (4) the evidence suggests that, after the three committed items, functions and run-time-indexed
unpacked arrays outrank `casez` for realistic designs; the maintainers decide the order.

This track is staffed by agents that work in `lean-surfaces-main` style isolated worktrees (as in the
10/29 integrations), because they change the semantics layer; each pushes after its own verification.

### T3. Tasks, references, proofs (`svgolf/tasks`, `svgolf/tests`)

- **fdiv, parametric (WP-H1, running; WP-H2 next).** H1: parametric task statement (a proposed, unapplied
  diff to the trusted `SvGolf/Task.lean` for the maintainers to approve: `CombTask` has one parameter today),
  `certF_bridge` for every format, the restoring-division recurrence for every step count, a parametric
  design draft with exhaustive small-format simulation. H2 (days 5 to 7, needs WP-G and probably WP-B2):
  the design-layer proof; the first milestone is the special-case table and the normalizer, then the
  digit loop (induction over stages), then rounding and packing. A full proof inside the week is NOT
  promised; the week's promise is parts 1 to 3 of goal 4 and the plan with measured gaps for the rest.
- **New tasks: ambitious, zk.golf-inspired** (decided 10/30). WP-T0 is DONE (`svgolf/design/tasks-week2/`: a ranked
  catalogue of 27 candidates, the zk.golf summary, three drafted and typechecked trusted specs, measured
  headroom). Recommended picks: combinational **`aes_sbox`** (fixed 8 bit; a `case` table scores 786.9 GE against
  201.0 GE for the Boyar-Peralta circuit, 3.9x; all 256 entries checked against FIPS 197 Table 4), **`clmul`**
  (carry-less multiplier for every N; Karatsuba saves 34% at N = 32) and **`chacha_qr`** (fixed 32-bit
  add-rotate-xor; RFC 8439 vectors); sequential **`pipe_mul`** (a combinational task with delay D >= 1) and
  **`crc32_step`**, after WP-S0's counter spike. Finding: the Keccak seed has no golf headroom here (ABC
  normalizes polarity: 2965.2 GE at W = 16 under every rewrite), so `keccak_round` is a proof showcase, ranked
  fourth. Decisions for the maintainers listed in the study's README (the picks; a tiny trusted `SvGolf/Bits.lean`; the
  Boyar-Peralta netlist in the repo as the `aes_sbox` baseline, cited; provenance for comparison points as in
  zk.golf; whether a localparam `c % W` extension, WP-F2, is worth it for `keccak_round`). Each task follows the
  **Decided (10/30): `aes_sbox` first, as a fixed 8-bit task, with NO banlist** (no operator is banned; contestants
  may write `+ - *` and tables if they like, the defaults apply, the `$macc/$mul/$alu` backstop is off for this task) (the S-box is inherently 8-bit; a
  fixed-size statement proved over the 256 inputs; also a scalability test for the tactics, 113 sites). The
  PARAMETRIC (N-bit) line follows: `clmul` for every N, then `gfmul` (multiply modulo ANY polynomial POLY, every N
  and POLY; the AES field multiply is N = 8, POLY = 0x11B; no field theory needed), then `gfinv` (the inverse in
  GF(2^N) for every N and every irreducible POLY, statement `x * y = 1` for `x != 0`, `0 -> 0`: the parametric
  S-box core) once a small GF(2^N) field library exists (irreducible modulus gives a field; Fermat for the
  exponentiation-chain and Itoh-Tsujii style inverters), estimated 1 to 2 weeks of library work first.
  usual path (Spec.lean reviewed by the maintainers, `oracle.py`, `task.json`, reference and proof, baselines, expected
  scores, dry-run style check) and the plan-review rule: one at a time, `aes_sbox` first. Building blocks from the
  old ladder (popcount, leading-zero count, comparator, prefix adder) are built when an ambitious task needs them.
- **Better references for existing tasks:** the `add` prefix-adder reference (depth 28 or 24 against 33,
  today only simulation baselines), a column-wise Dadda `mul` once functions and conditional generate exist
  (measured value: about 3 to 8% area, not a depth class), `add` and `mul` references migrated to the new API.
- **Scoring tracks:** see T4 (WP-X, the PPA family). The AND-count / multiplicative-complexity track is DROPPED
  (decided 10/30: not a cost that matters).

### T4. Checker, scoring, leaderboard, policy (`svgolf/check*`, `score/`, `leaderboard/`)

- **Time limits (decided: per task, fast; the plan review advised keeping the old rule until WP-P's numbers exist, so the first numbers are set conservatively and re-set after WP-P; no external submission exists yet, so no fairness issue).** **Rule:** `time_limit_s = max(120, ceil(4 x T))`, where
  `T` is the MAXIMUM of three controlled cold runs of the slowest honest reference of that task on the reference
  machine (not one noisy run). Every measurement records the machine class, cold or warm build, Lean cache state,
  post-synthesis mode and the reference commit. Document the rule in the README and re-set after WP-P. Nothing is
  lowered below what a reference needs on a loaded machine. Local checker default is light; `leaderboard add` and
  `verify` and every official artifact are always full; a light record is marked and never official.
- **WP-C2 `[x]` DONE 10/30 (`827da333`; WP-C3 included; full regression 332/332): light post-synthesis by default (decided).** First measure where the 45 to 180 s of a `mul`
  check go (Verilator builds of the netlist and the RTL, ls-sv per vector, synthesis); then make the default
  run light (target at most 20 s for `mul`: the scoring-point netlist against ls-sv on the corner vectors and a
  few hundred random ones, the heavy third-party RTL build only when asked), with a full mode
  (`--postsynth full` / `SVGOLF_POSTSYNTH=full`, which competition and verification runs set) that is the
  present behavior, same salt handling, same records. Official artifacts are never light: `leaderboard.py add`/`verify`
  default to full; a light record needs an explicit flag and is marked. The tests that pin the post-synthesis verdicts (the
  attacks that only the full check catches) run in full mode. Checker files change: not while a regression runs. **WP-C3 rides in the same package** (one checker-file edit, one
  tripwire window): the `design` stage rejects `hasUnsupported` envelopes with a clear message.
- **More scores: the PPA family (WP-X, 10/30).** Wanted: real delay and fmax, power and energy,
  area, and the combined figures people quote (area x delay, energy x delay, performance per watt); for FPGAs
  LUT, flip-flop, BRAM counts and fmax; for physical design wirelength, congestion and parasitic-aware
  timing. Not wanted: AND-count / multiplicative complexity; no depth budget, no caps. The board stays
  multi-objective (Pareto in all recorded scores, 2-D projections, presets such as "smallest under delay X"
  and "best EDP"). **WP-X0 is DONE** (`svgolf/design/ppa/`; its library recommendation, Nangate45, is SUPERSEDED by the maintainers'
  choice of sky130_fd_sc_hd, see "Synthesis library" in section 5; its tools, metric definitions, STA/energy engine and
  findings stand, and WP-X1 re-runs the numbers on sky130): only Yosys/ABC/Verilator/Icarus are installed; OpenSTA
  and OpenROAD have no macOS binaries (OpenSTA builds from source; OpenROAD via amd64 Docker or Linux). The
  study used Nangate45 (FreePDK45) typical as its comparison backend because it was the available reference: 8 of 11
  entries of `score/ge.json` are exactly its X1 area ratios (ANDNOT/ORNOT, with no single cell, and BUF differ). It is
  NOT the official recommendation: its licence (research and education, a restriction on benchmarking the library) does
  not fit a public benchmark, and fetching a file at a pinned checksum is a reproducibility measure, not a licence
  clearance. The only official backend decision is sky130_fd_sc_hd; Nangate45 stays a legacy compatibility backend,
  subject to its exact terms. Flow A0 (the weighted abstract netlist): keep the pinned
  `abc -g` flow and weight its scored netlist with the liberty (delay by an NLDM STA, energy by pinned
  stimulus, area in um^2); no new tool, no invalidated record; the STA agrees with ABC's `stime` to 1.3% mean and
  is bit-identical across runs. Measured: weighted delay mostly confirms unit depth (Kendall tau +0.5 to +1.0),
  but delay per level is not constant (20.5 ps ripple adder, about 26 trees, 33.9 array multiplier), so the
  combined figures bury the array multiplier (4.7x the EDP of the heap tree) and the adder AT leader flips;
  glitch-aware energy is a different quantity from area; mapper choice moves results as much as the metric
  (treat under 10% as noise); FPGA LUT counts rank multipliers differently from GE. Staged plan: (1) port the spike
  to `score/ppa.py`, delay and um^2 columns (2 days); (2) energy, AT/EDP views, `scoring.ppa`, salted stimulus,
  record schema /2, n-D Pareto and presets (2 to 3 days); (3) Yosys-only FPGA columns (1 to 2 days); (4) Linux
  CI with OpenSTA and nextpnr cross-checks (about a week); (5) A1 mapper flow, clocked metrics (with T6), ORFS
  nightly (2 to 4 weeks). Defaults in force (restated for sky130 and the governance rules of section 5): FPGA and physical as extra
  columns; ANDNOT/ORNOT stay at 1.333 GE in the legacy score; both energies recorded, glitch-aware owns the energy
  view only; (area_ge_v1, depth_v1) stays the default board, extra axes opt-in per task; no container required of
  contestants; unit depth stays beside the weighted delay. The sequential flip-flop prices come from the sky130
  library file.
- **Checker pre-checks** (WP-C landed the oracle and `--tactics`): next is a cheap early out-of-range
  check for small N (the dry run's stride-3 adder reached the proof stage only to fail), better messages
  for design-stage refusals (temp paths wrap the useful phrase), and `--tactics` explaining WHY (the
  instance message).
- **Leaderboard hand-off and re-issue.** Decide the public route (records in a pull request?), re-issue the
  four reference records against the final checker files, add the new references; depth budget stays
  none unless the maintainers set one.
- **svGolf as its own repository.** The maintainers allowed it; this week write down the extraction plan
  (what `svgolf/` requires from lean-surfaces: `LeanModels.Sv.*`, the extractor, `tools/gen_sv_refusals.py`)
  and a CI script, but do not move it yet.

### T5. Quality and process

- **Nightly full regression** (`tests/run.py`, now 45 to 55 minutes) as a script with a log summary, plus
  the cheap steps (layout, unit, leaderboard, register) on every integration.
- **Integration cadence with main** stays small and often: the 2-hourly check; every ls-sv package pushes
  its own commit(s) after a build of the touched modules and the dependent Examples.
- **Contributor guide for feature PRs** (`CONTRIBUTING-sv.md` or a README section): the checklist above
  (semantics, extractor, differential cases, Xcelium pin, Examples, register, push), because contestants
  may add features by PR and the maintainers approve them.
- **Docs refresh:** `docs/sv-comb-design.md` and `docs/sv-comb-census.md` still cite the old by-hand line
  counts; `PROVING.md` is regenerated from the new API; `REFUSALS.md` follows the register.
- **Review practice:** every package ends with an independent re-run by the lead of the checker on its
  references and the relevant `tests/run.py` steps (done for WP-B to WP-F), and a second-model static
  review (gpt-6-pro) of new references and proofs when the maintainers want it.

### T6. Sequential, asynchronous, CPUs (the direction, 10/30)

Today every task is combinational and `CombTask` demands `Unclocked` (an undriven clock was an exploit).
The destination is full CPUs, so the road is: sequential tasks with a state-machine statement (for every
input trace the output trace equals the spec machine's, proved by an invariant over cycles and, for
parametric designs, over N), then asynchronous behavior (reset styles, latches, several clocks, clock-domain
crossing), then a pipelined core against an ISA step function in Lean. **WP-S0** (DONE 10/30; note, two Lean sketches that compile with the standard axioms, and measurements in
`svgolf/design/sequential/`; the counter is already proved for every N and every cycle on the hand-built
instantiation) wrote the design note: what ls-sv does today for clocked designs (tried for real), the trusted
statement and clock/reset protocol, the proof method and a `sv_seq` register-transfer stage, the ordered
ls-sv features (`always_ff` and non-blocking assignment, synchronous then asynchronous reset, latches,
`negedge`, several clocks), the cost model with flip-flops and clock period, the post-synthesis check for clocked
designs, the ladder to a CPU, and a seven-day spike plan. Its decisions for the maintainers: approve the `SeqTask` shape (Moore after the edge, reset-first claim, `ClockedBy`
replacing `Unclocked`); the initial-values policy (none on state, reset only, `dfflegalize` backstop); flip-flop
prices and the multi-cycle metric; the ISA (a small 16-bit first, then RV32I against `LeanModels.Rv`); the first
public sequential task; whether `CombTask` and `SeqTask` stay two structures. Its first ls-sv item, **S0 clock
discipline as a loader refusal** (1.5 days), also closes today's one silent wrongness of clocked designs (the
model never reads the clock value, so an undriven or gated clock still captures; `Unclocked` blocks it for
svGolf only). Honest calendar: about 17 weeks to a UART-level ladder, 33 to a multi-cycle core, 41 to a pipelined
one (roughly six months with parallel agents). This week's sequential acceptance is the note plus the S0 clock-discipline refusal (WP-Q0, serialized after P2) with the
counter sketch as evidence; no public sequential task, no `SeqTask` checker integration and no clocked PPA score. The
note and the sketch exist so that the next weeks' tactic and ls-sv choices (WP-P, WP-G, T2) are made
with sequential logic in view (for example: keep the equation views register-aware, prefer `always_ff`
support early in T2).

## 3. Day by day

**Order of the Lean-slot work (binding; slippage drops from the bottom):**
WP-F integration -> P1 -> P2 -> Q0 (clock discipline) -> WP-G minimal fragment -> `aes_sbox` task -> [stretch:
P3 -> P4 -> WP-G step 2 (`~ ! ?:`) -> `aes_sbox` reference proof if not already done -> WP-B2 design note -> fdiv H2].
Slot-light work (Python, Yosys/Verilator, differential cases in isolated worktrees, oracles, docs) fills the gaps
and never invokes Lean. Hard demand of the order above: about nine agent-days against seven calendar days, so the
hard gates are the promise and everything marked stretch is reported as such.

| day | Lean slot (one process at a time) | slot-light | hard gate | stretch |
|---|---|---|---|---|
| **Fri 10/30** | WP-F verified and pushed to main (this includes its library change); WP-P gate 1 (measure) | WP-E1 integrated (extractor fix, Python); WP-C2 + C3 (checker; once no regression is running); WP-X1 report; T0/S0/X0 studies filed | WP-F and WP-E1 on main; WP-C2/C3 in; hotspot table | per-task time limits re-set after the first profile |
| **Sat 10/31** | P1: shared summary, `sv_interface`; `add_n` migrated | `~^` and genvar-step differential cases (isolated worktree); WP-G four-state contract note | `add` has no `Summary`/`sigma_L` recipe; baseline timings and `.olean` sizes | the first acceptable speed threshold |
| **Sun 11/1** | P2: stable equation names/bundles, the named knownness theorem; `add_n` on the new API | register status column; `aes_sbox` task files (README, `task.json`, oracle, baselines: no Lean) | P2 + `add_n` migrated, or revert | start P3 (only if P2 is stable) |
| **Mon 11/2** | Q0: clock-discipline refusal (about 1.5 days, to Tue midday) | differential rows for the clocked fixtures; popcount/leading-zero oracles only if chosen | Q0 fixtures and messages pinned | P3 (canonical row-major view) if Q0 is waiting on Xcelium |
| **Tue 11/3** | WP-G minimal fragment; `add` with an `always_comb` carry proved for all N | block-local temporaries design; `aes_sbox` `Spec.lean` review by the maintainers | procedural add proof works for all N | `~ ! ?:` truth tables and differential cases |
| **Wed 11/4** | `aes_sbox` task: registration in tests, tactic scalability measurement on the 113-site reference | choose the fourth T2 item by the rule of goal 5; PPA stage 1 columns design | `aes_sbox` task in the tests as draft or with its reference | the reference proof, WP-G step 2, the WP-B2 design note |
| **Thu 11/5** | independent rerun of everything; nightly regression green | week report; docs refresh; timing table | week report against these gates; fdiv H2 starts only if its dependencies are green | nightly script, contributor guide |

The last day is a clean independent rerun, not another implementation day.

The days are targets: the order is binding (WP-F → WP-P → WP-G → WP-B2 → WP-H2), the dates are not.

## 4. Risks

- **The Lean slot** is the bottleneck; two packages that both rebuild `LeanModels.Sv` cannot overlap. Mitigation:
  strict order above; slot-light work (Python, Yosys/Verilator, simulation, differential testing, docs) runs in
  parallel; plain Lean and `LeanModels.Sv` builds are serialized through the Lean-slot wrapper; targeted builds only.
  The Lean-slot demand of the hard gates (about nine agent-days) already fills the week: slippage drops work from
  the bottom of the order in section 3.
- **Agent reports are model output.** Every package is re-verified by re-running the checker and the
  regression; a green report is not a green tree.
- **Moving main.** The Python lane is still red upstream and master gains commits every few minutes;
  merges are scripted and the SV tier is rebuilt only when `LeanModels/Sv` or the extractor core changed.
- **Trusted-statement changes** (multi-parameter `CombTask`, each new task's `Spec.lean`) need the maintainers;
  they are prepared as unapplied diffs and drafts, never edited in place.
- **WP-B2 (word-level operators) may not land in a week.** Fallback: write the fdiv design at gate level
  (ripple adders and comparators from `CombLib`) so it needs only WP-G.
- **Proof speed work may change output** that references and `PROVING.md` quote; each WP-P change is
  gated on byte-identical goal dumps unless the change is the point.

## 5. Decisions

**Taken (10/30):**
1. Time limits: set per task as the lead prefers, and keep them fast. Applied after WP-F's regression
   (a limit is about 3 to 4 times the slowest honest reference compile of that task, floor 120 s; the rule
   goes into the README; `task.json` numbers follow the measured times, re-set after WP-P).
2. Post-synthesis check: **light by default** (work package WP-C2, below). The full check stays available
   for competition runs and verification.
3. Multi-parameter statement: **approved** (the `CombTask` generalization delivered by WP-H1 as a diff;
   the lead reviews it before it touches the trusted `SvGolf/Task.lean`; the approval is recorded in the file).
4. New tasks: **more ambitious, inspired by zk.golf** (WP-T0 study, ranked proposals and a drafted top
   candidate, replaces the default popcount, leading-zero count, comparator list; those stay as
   building blocks where the ambitious tasks need them).
5. Direction: **sequential, asynchronous, and finally full CPUs.** Not all of it this week; the week starts
   the road (WP-S0 design study, then a spike). See track T6.
6. The register's `never` section: the maintainers will come back to it.
7. Depth budget: **none**, no cap on anything; different designs land at different places on the Pareto frontier (decided 10/30).

**Synthesis library, decided (10/30): `sky130_fd_sc_hd`** (SkyWater, Apache-2.0, corner `tt_025C_1v80`, NLDM),
pinned by commit and sha256, fetched not vendored. Reason (an independent review, which the maintainers endorsed): the
Nangate45 library licence is for research and education and restricts benchmarking the library, a poor fit for a
public benchmark; sky130 is open, foundry-associated, mature in the open flows. Nangate45 remains a legacy
compatibility backend only; ASAP7 and GF180MCU are separate exploratory reports; NO combined board across libraries.
Cell policy to pin: all ordinary combinational cells including buffers and inverters and all drive strengths; no
sequential cells for combinational tasks, no scan/clock cells, no physical-only filler/decap/tap, no level
shifters, isolation or macros; fixed handling of constants and tie cells; report total cell area, cell count,
histogram, buffer/inverter count, unmapped count; timing from a fixed setup (input transition, output load,
arrival/required times, stated wire model), full place-and-route a secondary score. Consequences, studied by
**WP-X1** (running): the flip-flop prices are the sky130 `dfxtp_1`/`dfrtp_1` areas (WP-S0's recalled 5.3 and
6.7 GE match those cell areas; to be verified against the file) and the post-synthesis check must simulate sky130
cells. **Metric governance (second independent review, adopted):** the legacy structural score is kept as it is
(`area_ge_v1` with today's table, ANDNOT/ORNOT at 1.333, and `depth_v1`; no record or golden score changes); the
sky130 flow ADDS separately named, versioned fields, never called GE: `area_um2_sky130_v1`, cell count and
histogram, `liberty_weighted_delay_ps_sky130_v1` (named so unless it is a full STA), `energy_activity_sky130_v1` and
`energy_glitch_sky130_v1`; a calibrated `area_ge_sky130_v2` is an optional later metric. The default board stays
`(area_ge_v1, depth_v1)`; switching the default to sky130 area and delay is a later decision for the maintainers, after
the columns exist and are stable. Combined views are NORMALIZED named presets (area/ref x delay/ref, energy
x delay), never an unexplained global product; glitch-aware energy defines the energy view and the energy x
delay preset only; stimulus is a public development seed plus hidden official seeds published after a record is
frozen, aggregated over several fixed seeds; boards carry a noise policy (tie band / rank intervals / 'within
flow noise') whose width is a MEASURED parameter of a mapper and cold-run sensitivity study (WP-X0 observed about
10%; until the study exists the board shows the observed variation and hard-codes no band). OpenSTA/OpenROAD are
validation and nightly tracks only. **Two flows, two sets of field names, never swapped silently:** A0' (the
existing pinned abstract netlist weighted with the sky130 liberty) fills `area_um2_sky130_v1` and
`liberty_weighted_delay_ps_sky130_v1`; A1' (a real `abc -liberty` mapping with compound cells and drive strengths)
would fill separate fields (`area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`). WP-X1's measurements decide
whether A0' suffices for the first official PPA columns or A1' is stable enough to become the physical score; A1'
never replaces A0' under the same name.

**WP-X1 result (DONE 10/30, `svgolf/design/ppa/sky130.md`).** Pinned: the ORFS copy of the tt_025C_1v80 liberty (commit
6c6fc7e2, sha256 ef34f999...), cell models at ac7fb61f; units ns/pF/V/nW. Sky130 prices (nand2_1 = 3.7536 um^2 = 1 GE): NOT 1.0,
AND/OR 1.667, ANDNOT/ORNOT 1.667 (single cells), XOR/XNOR 2.333, MUX 3.0, a21oi/o21ai 1.333, fa_1 5.333; flip-flops dfxtp_1
5.333, dfrtp_1 6.667, dfstp_1 7.0, dfbbp_1 8.667, dlxtp_1 4.0 (the sequential study's recalled 5.3/6.7 are CONFIRMED); dfxtp_1
clk-to-q 349 ps, setup 112 ps. **A0'** (the pinned netlist with sky130 cells + NLDM STA) keeps every ranking of the legacy
score; **A1'** (`abc -liberty`) reorders the proved multipliers (the array goes from 2nd to last in area) and shifts the add delay
order. Compound cells give a median -4.5% area (range -21% to +33%); sizing +4.8% area, -8.8% delay. Bit-exact on 84/84 netlists
across hash seeds, parallelism, temp dirs; STA vs ABC stime 1.96% mean / 6.7% max. Noise: commuting operands moves area up to
11-15%, mapper choice a median 12% in area and 49% in delay; proposed tie bands 10% area / 20% delay / 3% energy. Energy: glitch-
aware CV over five seeds 0.9-1.5% on the multipliers; the array's glitch factor is 4.5 against 1.7-1.8 for the trees. Post-
synthesis can simulate sky130 cells in Verilator (121-336 lines of generated models, 3-6 s build); tie cells need a rule (constants
stay literals, one conb_1 priced per module). **Recommendation (adopted as the working plan): additive.** A0' fields first
(`area_um2_sky130_v1`, cell count/histogram, `liberty_weighted_delay_ps_sky130_v1`, then the two energy fields) in annex files
outside the record hash and in `tests/expected_sky130.json`; A1' published as an unranked research column; legacy score and the 45
golden scores untouched; OpenSTA/OpenROAD CI-side only. Open for the maintainers (ten in sky130.md section 12): A0' vs A1' as the official
sky130 flow (recommended A0' first), the tie bands, the tie/constant policy, the timing setup (input slew 50 ps, output load
10 fF, no wires), who holds the hidden-seed secret, whether to compute `area_ge_sky130_v2`, the allowed flop set.

**WP-C2/C3 result (DONE, verified by the lead).** `check.py --postsynth light|full` (also `SVGOLF_POSTSYNTH`; the flag wins, default
light, a typo is an error). The post-synthesis stage is dominated by ls-sv's `run2` per vector (96 to 99% on `mul`), not by builds;
light is a deterministic subset of the full vector set with the same seed (all-0/all-1, walking, task corners, harvested constants,
random head; `postsynth.light_vectors`, default 256, `mul` 40), so a light rejection is always a full rejection. Measured stage times,
full -> light: mul_tree 166.7 s -> 21.2 s, mul_wallace 119.1 -> 15.2, mul_n 43.6 -> 6.1, mul_tree_h 40.6 -> 5.6, fdiv16 19.9 -> 2.3,
add_n 2.1 -> 2.0 (floor: the netlist's Verilator build). Official artifacts are always full (`leaderboard add`/`verify`/`seed-references`
pass full; `add` refuses a light result unless asked; light records are marked and shown as light). The only attack that separates the
modes is the new `rare_mid` (a 2^-9 out-of-range read: full rejects it with 7 of 4130 vectors, light passes). WP-C3: the `design` stage
rejects an envelope with a `Design2.hasUnsupported` process (`func_call`, `assign_func`; `fn_uninit`, `latch_never`, `latch_star` now stop
at `design` instead of `postsynth`, the post-synthesis check alone still rejects them), fail-closed. Time limits by the exact rule
(`score/time_limits.py`, numbers and environment in `score/time_limits.json`): add 120 s (floor), mul 400 s (slowest reference `mul_tree`,
T = 100 s), _example 120 s (floor), fdiv16 3600 s (draft, kept); re-measure after WP-P. Not done (offered): parallel ls-sv chunks for the
light/full stage (`svgolf-eval` starts in 0.23 s). Register: `sg-design-unsupported` added, `sg-ps-latent` updated, `rare_mid` under the
fourstate index entry.

**Sequential direction, decided (10/30, on the WP-S0 note):**
1. `SeqTask` shape approved (Moore after the edge, reset-first claim, `ClockedBy` instead of `Unclocked`).
2. Initial values: none on state, reset only, `dfflegalize` backstop. Agreed.
3. Flip-flop prices and the synthesis cell library: a STANDARD OPEN library, derive the GE table, flip-flop prices and delay
   model from its liberty file instead of conventions from memory. Library: `sky130_fd_sc_hd` (see above); the flow choice
   comes with WP-X1.
4. ISA for the CPU ladder: a small purpose-made 16-bit ISA first, then RV32I against `LeanModels.Rv`.
5. First public sequential task: something simple (the counter with enable and synchronous reset).
6. `CombTask` and `SeqTask` stay two separate structures (`CombTask.toSeq` is a proved bridge).
7. Edge-detected clocks (gating, derived clocks, several clocks) and clock-domain crossing: not before a
   one-clock core runs.
Next sequential steps: S0 clock discipline as a loader refusal (1.5 days, no dependency, first in the ls-sv
queue after WP-F), the clocked post-synthesis harness (slot-free), then `Seq2` and the checker changes once
the cell library is chosen.

**Still defaults ("I don't know what you mean"; explained in plain words):**
- *Record hand-off.* After a contestant has an accepted submission, `leaderboard.py add` writes a
  record file on the contestant's own machine. Nothing sends it anywhere: there is no shared board
  yet. The question is how a record would get onto a public board. The simplest route is a pull request
  to the svGolf repository that adds the record; the checker is deterministic and re-runs in about a
  minute, so CI can re-verify every record before it is merged. Default until decided: local records only.
- Whether `svgolf/` moves to its own repository this week (default: no).
- The register's `sv-div-1` row (the maintainers decide).
