# ARCH-NOTE: one exact semantics for SystemVerilog, derived cycle and contract views, and the proofs agents write against them

> **Status.** Design note, 2026-11-02, written by a read-only workflow. Nothing was built or run except `grep`, `sed`, `git log` and line counts. Base: worktree `integ1102` at 078216ff. Repo paths below are relative to that worktree.
>
> **Labels.**
> - **MEASURED**: a number in a committed file, or a count that I or a named researcher took over committed files.
> - **READ**: source, as file:line or §.
> - **CITED**: a paper or URL. "via digest" means the citation comes from a researcher's digest and I did not re-fetch it.
> - **JUDGED**: my estimate. Every design choice in this note is JUDGED unless it cites a ruling. All sizes are relative and JUDGED; none is a schedule.
>
> **Governing ruling** (decided 2026-11-02, binding): SystemVerilog's exact operational and elaboration semantics are the semantic authority. Cycle semantics and module contracts are first-class derived abstractions for the synthesizable hardware fragment. Every cycle model or contract used by automation carries a refinement theorem back to the exact semantics.
>
> **Standing rulings 1–7** bind everything below:
> 1. Preserve the structure of loops, generate blocks and parameters.
> 2. No lowering of loops.
> 3. Make proofs easy in Lean; this is not a normalization-to-SAT pipeline.
> 4. Fuel is doubted.
> 5. No external solvers; only the three standard axioms; no `sorry` or `native_decide` in svGolf.
> 6. Xcelium is the reference, with declared departures.
> 7. Refusals are loud.

### Which documents this note rests on, including the family's general architecture

The maintainers asked whether the general architecture documents were checked, since some of these questions matter for other languages. They were. These are the family documents I read for this note, and what each contributes:

- **`docs/family-architecture.md`**
  - §0.1: I, the definition is never weakened for provability. II, the definition is trusted and kept minimal, while the library is never trusted. II(a), the preference ladder for decision procedures.
  - §3.4: one monad. Fuel is "an index on the step function", never a monad layer. "A performance number measured on a twin is a claim about the twin."
  - §3.4(b) and §8.5: "Any route that introduces a second semantics owes an adequacy theorem, and the differential corpus does not discharge it."
  - §3.6(1a): `SemM` cannot suspend, so the continuation must be defunctionalized. "Data may carry the DECISION; it may not carry the SCRUTINEE." Also the laziness law.
  - §5.0a: the declared-divergence register.
  - §6: determinism is observation-indexed. "The SV tier's five `_det` theorems must be re-proved through `cycleOf`."
  - §8, step 7: decide fuel's fate before writing the interpreter. Step 9: separate the spec half from the interpreter half; 65% of 949 theorems recompile unchanged under a definition swap. Step 10: take the parts, never rebuild the node.
- **`docs/proof-framework-research.md`**
  - §4.1: the Leroy–Grall threshold collapse.
  - §6.5: CakeML's functional big-step semantics, in which the clocked interpreter is the official semantics.
  - §7.4: Lipton movers; "∀ schedules give the same outcome" is a theorem about race-free designs.
- **`docs/c-tier-architecture.md` §3.2**: canonical order plus a commutativity census. "A normalizing rewrite would … quietly move the claim."
- **`docs/circuit-assurance-architecture.md`**:
  - a relational semantic root;
  - `SafeUnder`, `RealizableUnder`, `ReceptiveUnder` and `DeterminateUnder`;
  - `ExactView`, `OverApproxView` and `UnderApproxView`;
  - the equation-provenance guard.
- **`docs/python-architecture.md`**: two interpreters share their pure workers, and the proof interpreter is the narrower one. Its `--proof-interpreter` run found 25 wrong answers.
- **`docs/generator-tier-architecture.md`**: a suspended machine over the shipped AST, treated as a verified object.
- **`LeanModels/Core/Outcome.lean:180-233`**: `Loud = timeout | unsupported`, `SemMWith`.

§10 says where this design conforms to family law, where it departs and why, and what should go back to the other lanes.

> **Lead's review (2026-11-02).** Written by a read-only workflow: seven researchers (properties, proof strategies, constructs, prior art, a scaling audit of this repo, and the family's general architecture), two opposed architects, one critic, one synthesizer. The ruling arrived after the architects wrote; the critic and the synthesizer worked under it, so F and P appear as the two layers of one design.
>
> *Checked against the source by the lead:* the §4.7 quotation and the panel behaviour (`docs/sv-oracle-disagreements.md`: Xcelium defers the update and re-runs the block, i.e. it behaves process-atomically, while Icarus can stay stale), so the process-atomic narrowing of D1 agrees with the reference simulator; `CycleAdequacy` stated and unproved, M0-only (`Adequacy.lean:53,102`); the Mealy gap (`design/sequential/README.md:164-169`); `CombTask.Statement` over `Runs2` (`Task.lean:183-205`); `run2` already runs each process atomically (`runCombProcess2`); `SvM := SemMWith SvWorld Finish SvClause Unit` (`World.lean:257`); `runProcResidual` is a `partial def` (`Slot.lean:314`); no svGolf document cites the family architecture.
>
> *Not checked:* the other READ and CITED items, and every "via digest" citation. No Lean was run; every size is JUDGED.
>
> *Since the note was written:* master `c64ebdac` replaced the loop fuel 128 with exact fuel derived from the header (`<`, `<=`, `>`, `>=`, constant step), so the 126-trip cap of §5.2 and §5.4 is gone on master. It still uses fuel, only computed so that it never runs out; the note's G0 ("trip list from the header, no fuel") remains the target.

> **DECIDED (decided 2026-11-02).** Both tracks approved, and decisions 1–10 as the lead leaned: (1) process-atomic execution as a declared profile ruling on LRM §4.7; (2) no fuel in any definition; (3) trusted statements over the observation interface, starting now; (4) an event-level environment with the clocking discipline as a rely; (5) svGolf v1 statements kept in force as cycle-model statements, the debt registered, records transferred by theorem later; (6) an `Admissible` conjunct, its clauses fixed by measurement; (7) one AST, `Stmt2` frozen; (8) 4-state authority with a 2-state view and the default start policy; (9) elaboration in Lean, slang a multi-point witness; (10) liveness, CDC and SVA deferred with their signatures fixed now. Execution: `EXECUTION-PLAN.md` beside this note.
>
> **MEASURED BY X6 (agent M, 2026-11-02; `measure/X6.md` on `arch-measure`), which amends §3.2 and the §9 elaboration row.** Lean's elaboration against slang's at several parameter points per design (115 designs, 876 points: v/2, v+1, 2v, 1, bit flips, a joint doubling, the tasks' probe points):
> - **Correctness holds where both run.** svGolf references 113 of 113 points agree. Over the RB0 census, wherever both elaborate, parameter values, localparams, declared widths and generate counts never differ (0 metadata differences). The 6 divergences are all at degenerate points: serv at `W=2, B=0` (the default-point context-width fold, §3.2's caveat, measured) and hazard3 at `W_REQ=1` (`$clog2(1) = 0`, a zero-width declaration slang rejects too). The 17 designs Lean loads at their default have 0 divergences at their 81 other points.
> - **The risk is coverage.** Lean refuses 42% of the census points, and 85% of those refusals come from three causes: replication or concatenation in parameter defaults (192), enum-typed or untyped parameters (103), package-scoped parameters (26). These are the first R-ELAB items. The §9 row "elaboration in the trusted definition is too big" becomes a coverage risk, and multi-point probes (Probe2) stay mandatory for svGolf tasks.
>
> **MEASURED BY X8 (agent M, 2026-11-02; `svgolf/design/architecture/measure/X8.md` on `arch-measure`), which amends §4.2, §4.3, §5.5 and §9.** On ibex_core, cv32e40p_core and the whole cva6 core (five parameter points, sources at RB0's pinned commits, never in the repo):
> 1. **At a parameter point, per-port arcs suffice.** All 18 module-level cycles that an arc-less summary invents vanish at port granularity (ibex_ex_block's shared adder among them); bit granularity was never needed.
> 2. **For every parameter value, ports are not enough.** cva6's two struct handshakes need field granularity, and cv32e40p's FIFO (`empty_o <- push_i`) is acyclic only when `FALL_THROUGH = 0`. So D6/D9 arcs are **field-refined port arcs with parameter conditions**, bits optional.
> 3. **A rank on PROCESSES does not exist for 18 of 198 real `always_comb` bodies** (ibex_controller and ibex_multdiv_fast; three cv32e40p bodies; eight in cva6), while a rank on signals exists for all but one and a rank on fields for all. Example (READ, ibex_controller.sv l.542, l.628, l.1023): the FSM `always_comb` writes `halt_if` and reads `id_in_ready_o`, and `assign id_in_ready_o = ~stall & ~halt_if & ~retain_id`. So R-COMB's hypothesis is acyclicity at **signal or field** granularity, as §4.3 says, but its termination argument must be stated over written windows, not processes: a process may be re-triggered by a higher-rank window and re-run, writing unchanged values. G-A and G-B (process rank, today's `Acyclic` and `lowerComb` certificate) are a correct first slice; they cover every svGolf record (X3), but not these blocks. **R-COMB-1 (window-granular rank) is scheduled in WS1** after the comb slice of R-DESIGN2.
> 4. **15 holds that exist only in 4-state**: default-less `case` statements whose items cover every 2-state value (cv32e40p `unique case (imm_a_mux_sel)`); an x selector matches nothing and the variable holds. Input to X9 and X10.
>
> **MEASURED AND PROVED, 2026-11-02 evening (agents M, A, P, L; reports in `measure/` on `arch-measure`, X1-NOTE §9 on `arch-x1`, LOOP-NOTE §9.5 on `arch-loop`).**
>
> 1. **X9 amends §4.3 (R-X) and the §9 2-state/4-state row.**
>    - 66 kernel `decide` facts at widths 1–2 (unary up to 3).
>    - **The order puts x below z (x ⊑ z).** With z incomparable, `?:` and the shifts fail spuriously.
>    - **Monotone:** every arithmetic, logical, shift, comparison (`==`/`!=`, relational, signed and unsigned), reduction, `?:`, concat and resize table.
>    - **Not monotone,** each with a kernel counterexample: `===`/`!==`; `==?`/`!=?` in the right operand; `case`/`casez`/`casex` matching; the `if` decision; the knownness tests; the 2-state boundary.
>    - That fixes R-X's exclusion list. The width-parametric versions are done: `XMono.lean`, 90 theorems at every width (`49155b44`).
>    - **x-reachable decisions** (an upper bound):
>      - ibex 17/319 sites, all unreset registers;
>      - cv32e40p 1/370;
>      - cva6 125/794, mostly out-of-range dynamic selects;
>      - the generated vexriscv and picorv32 cores 89–92%, because they use `'x` as a don't-care.
>    - So in handwritten RTL an x-decision is rare and is a named temporal obligation (write-before-read, index range). Designs that use `'x` as a don't-care need concretization, and an `Admissible` clause can detect them.
> 2. **X10 amends the `Admissible` decision (6) and §4.7.**
>    - 20 fixtures were run through slang, Icarus, Verilator, the pinned Yosys flow and `run2`.
>    - **Where each construct's claim holds, nothing splits.** On violating cycles, all 7 qualified-case fixtures split, and so do `full_case` and `parallel_case`:
>      - the netlist resolves the don't-care its own way;
>      - Icarus warns and continues;
>      - Verilator aborts;
>      - `run2` silently follows Icarus.
>    - So a proof over `run2` can establish a value the scored netlist does not compute. Yosys 0.53 cannot read `unique`/`priority if`.
>    - Proposed `Admissible` clauses A1–A6 are drafts of trusted text for the maintainers' Day 5 review:
>      - A1: a qualified case is admissible only with a proof that its claim holds on every reachable settled state;
>      - A2: no qualified `if`;
>      - A3: no attributes;
>      - A4: no self-reading `always_comb`;
>      - A5: no x/z digits outside case-item patterns;
>      - A6: a default-less fully covering case is admissible, with its x-hold outside the known-input rely.
>    - Sent to the ls-sv library's maintainers on 2026-11-02. It was adding symbolic qualified cases that day, and was asked to make a violation loud or an explicit obligation, never a silent fall-through.
> 3. **The Day-6 census amends §3.2 and the tier pricing.**
>    - Over 831 public sv-tests files, 28 (3.4%) reach a design the `sv_comb` tactics read. The distance is testbench constructs.
>    - 126 clean envelopes (and 18 RB0 ones) fail because the extractor emits an `Initial` process kind that the Lean envelope parser rejects. That is a loud refusal at the wrong layer; it was relayed to ls-sv.
>    - RB82 before → after WP-PROC, as written:
>      - no Unsupported 22 → 43;
>      - loader accepts 12 → 37;
>      - clean lowered design 6 → 20;
>      - `sv_structure?` 3 → 8;
>      - `sv_equations?` 0 → 6.
>    - Packages now lead the blockers, which matches X6.
> 4. **The R-DESIGN2 comb slice amends §4.3 (R-DESIGN2) and §5.1.** This is a transport theorem, by agent A.
>    - E-core-0 is an observation backend (`Obs_E0`). Both inclusions hold for assigns and `always_comb`.
>    - **`run2` → E holds only for typed stimuli.** `not_included_run2_E0` proves the unrestricted converse false for every assign-only design with an input: `run2` stores a stimulus as given, E converts it to the port width.
>    - So R-DESIGN2 is stated on typed environments (`IncludedOn`, now the general form in `Observe.lean`, P `506330b3`).
>    - The three accepted records it was instantiated on are transported to E-core-0 by `statement_E0`. The v1 statement exposes none of the four fragment hypotheses it needs (CombDesign, Acyclic, all declarations 4-state, typed initializers); the records prove them as named lemmas.
> 5. **The records' direction amends §5.1's debt row.** This is provisional over `run2`, by agent P, 111 lines.
>    - For a comb-profile design, the stimulus that re-drives every entry to its pre-sample inputs gives the identical `run2` run.
>    - So v1 implies the trusted pre-sample convention (`computes_iff_computes_obs`). A comb-profile record moves to `Statement_obs` with no re-proof (`statement_obs_of_statement`).
>    - The debt row is discharged over `run2` for comb-profile records. The move to E still needs R-DESIGN2, and `always_comb`/procedural records still wait.
> 6. **The loop route amends §5.4.** This is provisional over `run2`, by agent L.
>    - The nested `clmul` `Statement` for every N went from 394 design-specific lines (the hand proof) to 96, with `sv_loop_rows`, `sv_loop_sem`, the task lemma `satisfiedAt_of_loop` and the XOR-sum library.
>    - No fuel, block plumbing or settle theory is left in the proof.
>    - The tactics cover one loop shape. The next shapes are sized on two new designs before choosing between per-shape lemmas and a recursive recognizer.
>    - *Later the same day:*
>      - A recursive recognizer (`Stmt2.fragOk`/`step`/`frag_rec`) was chosen over per-shape lemmas. It proves a priority encoder (77 lines) and a popcount (49) for every N, and takes nesting for +13 lines, with generic code 1575 → 1305.
>      - The loop seam is five primitives, one `Stmt2` construct each. They are proved over E-core-0 (`DenotesE`, `Denotes.toE`), so each design's body meaning is a *transport theorem* to E (`body_E`, `arch-loop` `562a89db`, 200 generic lines).
>    - **Finding: the settle step cannot follow yet.** E-core-0's slot-level theorems (`activate_comb`, `Settles.ofLower`, `rcomb1`) need a lowering and per-design certificates (`completeB`, `rankedB`, `boundB`) computed on a concrete design, which do not exist at a symbolic loop bound. So R-DESIGN2 needs its own argument at symbolic N. For a single `always_comb` process with no self-read, that argument should be structural (one activation closes the slot); it is WS3's next item.
>    - **Done 11-03 (`arch-loop` `c7b56d30`): the first svGolf-shaped statements proved against the authority.**
>      - `SingleE.slot` (`Loop2Slot.lean`, structural hypotheses only, no concrete certificates): every legal schedule closes the slot at F of its opening view. Its own write may wake the process once more, and that run is a no-op.
>      - With it, nested `clmul`, the priority encoder and popcount each prove `t.Statement_obs ty Obs_E0 …` at every N, *derived from E*. Every hypothesis closes at symbolic N.
>      - `NoRun2.lean` checks at build time that the roughly 7,250 constants of those proofs include none of `run2`'s 13 execution and observation constants. Its control, the `run2` statement for `clmul`, contains 12 of them.
>      - The front end (instantiation `sem N`, the self-read guard, the one-driver rule) is still in the chain.
>      - `WSettles` at symbolic N is blocked by the lowering (`symExec` over a symbolic trip list), not by its termination argument.
> 7. **X2 amends D1 (§4.1) and register row `sv-div-4`** (agent M, 11-03, `arch-measure` `d9a1cf0e`).
>    - Instrument: a preemptive copy of E-core-0's executor, explored exhaustively per slot over the 460 Xcelium-golden comb rows that run.
>    - Every row without a FED `always_comb` (a variable another process writes in the same slot) is invariant: 450 of 460.
>    - Of the fed rows, statement-granular preemption changes 5 of 8 decided, and LRM §4.7's "at any time while evaluating" changes 10 of 11.
>    - svGolf's `add_proc` and `add_proc_m` (fed carry cells) change at N=2. The four records are assign-only and invariant.
>    - So the JUDGED prediction holds where it applies. A "no fed `always_comb`" census is a sound per-design retirement where it passes, but real RTL rarely passes it (the sliced `ibex_alu` has 8 of 11 blocks fed), so it does not replace the narrowing.
>    - `sv-div-4`'s gated text was widened to the measured condition (`eef478f2`).
>    - Two E-core-0 fidelity findings went to WS1 as a fix item:
>      - `acg_xproc_bits`: sensitivity to a partially overlapped read is Icarus-like, not Xcelium-like;
>      - `dyn32`: an overhanging indexed part-select gives in-range bits where Xcelium gives all-x.
> 8. **Ordinary `always_comb` style over E** (agent L, 11-03, `arch-loop` `d7af3dac`; amends §3.1 and the proc tier).
>    - `CombFragE.lean` (245 generic lines): one generic proof, `Stmt2.sem_run`, gives the meaning of a single activation over E for every body in the fragment, as a view function. The fragment is blocking writes to any set of static windows, `if/else` anywhere, blocks, and every `case` kind.
>    - Two real sliced `ibex_alu` blocks are proved against plain local specs, *derived from E*: `bwlogic`, a `unique case (1'b1)`, and the adder flags, four defaults then a `case`. The E part costs about 1 M heartbeats per block; the rest is backend-free spec work.
>    - All six X7 blocks are in the fragment, and four await their specs.
>    - Finding: E-core-0 ignores the case qualifier and runs the first match, while `run2` has been loud on a violation since master `2218821b`. It went to WS1 as a third fidelity item; meanwhile the claim is an explicit hypothesis.
>    - Next: the written-before-read check that makes the slot theorem derivable for these bodies.
> 9. **X7 answered: the E route is cheaper than today's route** (agent M, 11-03, `arch-measure` `03c322e9`, section E).
>    - The `clmul` task's Statement for every N costs 12.9 M heartbeats over E on the nested-loop design, against 184.7 M on today's route on `clmul_n` (structure 80.0, `sv_equations` 95.5). That is about 14 times less, on different designs of the same task: a procedural nested loop against generate-for.
>    - The priority encoder costs 9.8 M and popcount 6.7 M.
>    - Per template site the E route is within 2×: 12.9k against 36.9k kHB, or 36.7k counting `load_sv`'s elaboration.
>    - The E-specific overhead over L's own `run2` statement on the same designs is 0.6–1.0 M per design.
>    - This is evidence for the structure-preserving ruling: a loop proved as a recurrence is cheaper than its generate-unrolled sites proved one template at a time.
> 10. **CFRAG: on real RTL, loading binds, not the E fragment** (agent M, 11-03, `arch-measure` `4758901f`; amends §3.2 and the tier pricing).
>    - 195 of 209 loaded `always_comb` processes (93%) pass `CombFragE`'s `combOk`. For bodies written as `always_comb`, as opposed to lowered `always @*`, it is 21 of 30 (70%).
>    - But 290 of 499 processes sit in modules that do not load:
>      - package-scoped parameters 98;
>      - `initial` 68;
>      - package enums in parameter defaults 55;
>      - `LocalDecl` 45.
>      92% of the X8 cores' `always_comb` text is in modules that do not load.
>    - The fragment's own next construct is a dynamic element select as a target. Package parameters are the biggest lever on both sides (98 hidden, plus 7 of the 14 fragment failures), and they are loader and envelope work: the ranking went to the ls-sv library's maintainers on 2026-11-03.
>    - The extractor crashes on cva6 (Python's 4300-digit int-to-string limit).
>    - Design-level reach today is 4 single-process designs. Another 9 clean designs need a multi-process composition over E.
>
> **OUTSIDE REVIEW (2026-11-02) and the maintainers' verdicts.** The review approves the layering (E authority, D views, L library, S statements, X executor) and asks for changes before the note is settled. Each point was checked; these verdicts amend the note below.
>
> 1. **E is "exact" but narrowed: accepted as a naming fix.** E is *the authoritative semantics of the declared SystemVerilog profile*. The profile is recorded: process atomicity (§4.7) as a declared departure in the §5.0a register, canonical headers, and the list of constructs in each E milestone. Constructs outside the profile are elaboration refusals; reachable `unsupported` nodes stay a dynamic refusal; a failed view hypothesis is a view refusal. The three-refusal split of §4.1 stays.
> 2. **Fairness: accepted as "legal schedules", not as a new fairness hypothesis.** Today's oracle already has `choose_perm`: every invocation returns a *permutation of the whole ready list* (`docs/sv-r1-scheduler.md` §2.3, `Semantics.lean:155`), so no ready process can be skipped. E's `Choice` keeps that type, and R-COMB/R-DESIGN2 quantify over legal choices. For the acyclic fragment R-COMB needs no separate fairness assumption, because a rank measure bounds the activations under every legal choice (JUDGED; X1 confirms or refutes it).
> 3. **Trip lists: accepted as a standard form, though the term-size claim is mostly answered already.** `intRange i0 n` (`Param.lean:2586`) is already compact: at a symbolic `n` it is never materialized, and at a concrete `n` the list is built only by execution. Still, every family (procedural loop, generate loop, instance array) gets one `TripSchema` (start, step, count, read in 32-bit `int`), with `toList` a derived view proved equal. A fixed-size design goes through the generic lemma with the count abstracted.
> 4. **Testbench semantics: accepted.** The first E milestones are design-only. Stimulus, clocks and resets come from an event-level environment; testbench SystemVerilog (delays, `initial` stimulus, `$display`) is not interpreted to define design meaning. Timing constructs join E later as their own milestone.
> 5. **D1 before X2: kept, as a profile ruling.** The reference simulator already behaves process-atomically (Xcelium re-runs the block, `docs/sv-oracle-disagreements.md`), so D1 follows ruling 6. X2 then informs the departure's retirement condition, not the decision itself.
> 6. **Backend-independent observations: accepted.** Statements take an observation model as a parameter. `Obs_run2` and `Obs_E` are two instances, and R-DESIGN2 is stated as their agreement, so swapping the backend is a theorem rather than a change of definition underneath the statements.
> 7. **Trusted versus proof observations: accepted as two types.** Ports only in trusted statements; internal signals only in the proof-observation type used for cut points.
> 8. **Contract direction in the API: accepted.** Separate soundness theorems for safety, relations and equivalence. An over-approximating contract has no lemma that transfers a two-run property.
> 9. **`Sv.Ast` not monolithic: accepted.** One syntax package with phase-separated types (raw, elaborated, statement, expression, module, generate item) and decidable fragment predicates. `Sv.Ast` holds syntax and elaboration structure only; cycle semantics and summaries stay in D.
> 10. **Typed values in the uniform store: accepted.** `Val` keeps width, signedness, 2-state or 4-state, and aggregate shape.
> 11. **Two tracks as the delivery plan, not a fallback: accepted.** *Authority track*: X1 (tiny R-COMB slice), then minimal E for edge/NBA/reset with R-EDGE and R-CYCLE, then hierarchy and elaboration. *Product track, in parallel*: `obs` over `run2`, the loop recurrence and the nested-clmul proof, the cycle machine over today's implementation, contracts, and the counter. R-DESIGN2 joins the tracks.
> 12. **Stricter X1 gate: accepted.** X1 is a few assigns plus one `always_comb`, no hierarchy, arrays or loops, 4-state, one slot, one driver per signal, a given rank. **No general E core is built until X1 has a kernel-checked theorem connecting E, CombEqs and `combSettle2`.** M3 therefore follows X1 rather than preceding it.
> 13. **Unchanged:** the authority/derived split, no fuel in definitions, the observation interface, refinement once per fragment, direction labels, one AST, freezing Stmt2, the run2 debt row.

---

## 0 Summary in plain language

**What we build: three layers and a statement surface.**

1. **The authority (E): what a SystemVerilog design means.**
   - It follows the LRM closely. Elaboration covers parameters, generate, instances and types. Simulation covers processes, regions, nets with drivers and nonblocking updates.
   - E is written once, in Lean, as a total one-step function plus "keep stepping". No definition anywhere contains fuel.
   - Every SystemVerilog statement is a node of one source-shaped AST. Nothing is unrolled, flattened, inlined or lowered in the definition of what a design means.
   - Parameters are bound in an environment, never substituted. A generate loop is a family indexed by its trip list. An instance is a reference to a module, not a copy.
2. **The derived layer (D): the views proofs actually use.**
   - The per-module cycle machine: outputs as a function of state and inputs, and one next-state equation per register.
   - Combinational equations, loop recurrences, arrays as functions, function specifications and module contracts.
   - Each view carries a refinement theorem back to E. That theorem is proved **once, for a whole fragment**, never per design. Each one also states its direction: exact, over-approximation or under-approximation.
3. **The library (L): tactics that do the tedium.**
   - They check, by reflective `decide`, that a module is in a view's fragment.
   - They apply the refinement theorem and print equations in source names.
   - The agent does the thinking: invariants, simulation relations, contracts, cut points and the spec collapse.
4. **Trusted statements.**
   - They are written against an **observation interface** of E: the values of ports sampled at the start and at the end of each time slot (the LRM's Preponed and Postponed regions), with environment assumptions as relies. A clocking discipline is one of those relies.
   - They never mention `run2`, fuel, schedules or string names.
   - CombTask and SeqTask stay separate structures, as ruled on 10/30. Both are proved special cases of one skeleton.
   - svGolf adds an admissibility conjunct: the proof and Yosys must read the same program.

**Answers to the three questions** (detail in §1–§3).

- **Q1. Strategies.** Agents will prove by:
  - induction over a source index (genvar, trip or bit) using the source's own recurrence;
  - refinement to a Lean reference model by an inductive invariant;
  - module contracts with child blocks treated as black boxes;
  - cut points at named internal signals;
  - array abstraction;
  - Burch–Dill flushing for pipelines;
  - relational (two-run) invariants for equivalence and constant time.

  None of these needs a SAT solver. All of them need loops, generate families, instances and registers to stay addressable in what proofs read.
- **Q2. Properties.**
  - Exact and relational combinational functions.
  - Sequential refinement from reset.
  - Fixed and bounded latency.
  - Memories and FIFOs.
  - Protocol invariants under environment relies.
  - Hierarchical contracts.
  - ISA conformance of cores.
  - Two-run hyperproperties: equivalence, constant time, X-robustness.
  - Later: liveness under fairness, and clock-domain crossing.

  One skeleton (rely ⇒ guarantee over observations, with ghost state) covers most of these. A relational judgment and a stream judgment sit beside it.
- **Q3. Constructs.**
  - About 50 T1 constructs make up ordinary synthesizable RTL (JUDGED). Among them: all procedural statements with static bounds; loops with headers; `break`/`continue`/`return`; scoped locals; functions and tasks; `casez`/`casex`; `unique`/`priority`; packages; enums; structs; parameter-sized unpacked arrays and memories; casts; `inside`; streaming; instances; generate-if and generate-case; `always_ff` with async reset.
  - T2 (whole designs) adds latches, negedge, several or gated clocks, multiple drivers, tri-state, interfaces and recursion.
  - T3 is verification: assertions and SVA.
  - T4 is simulation-only material.

**The uncomfortable facts.**
- Today's svGolf statements rest on `run2` (Design2's cycle model), and no refinement theorem connects `run2` to any exact semantics.
- The only adequacy statement in the tree, `CycleAdequacy`, is a `def … : Prop`. It is stated, not proved, and it is over the M0 `Design` (READ `LeanModels/Sv/Adequacy.lean:53,102`). Its elaborator also refuses `always_comb` and `assign` (READ, same docstring). So even proved, it would cover no svGolf task.
- The region scheduler, the nearest thing to an exact semantics, cannot be reasoned about as it stands: `runProcResidual` is a `partial def` (READ `LeanModels/Sv/Slot.lean:314`).

**The first job** is the keystone refinement for combinational settle, **R-COMB**: every process-atomic event schedule of an acyclic, single-driver, sensitivity-complete design closes the time slot at the unique fixpoint of the per-process equations. It prices the whole programme. With R-DESIGN2, it also lets today's comb records transfer.

**Decisions needed from the maintainers.**
- Process-atomic execution, recorded as a declared narrowing of LRM §4.7.
- No fuel in any definition.
- An observation interface for trusted statements, introduced now.
- An event-level environment with a clocking discipline.
- What to say and do about the run2-based records.
- An admissibility conjunct in svGolf statements.
- One AST, with Stmt2 frozen.
- The 4-state authority with a 2-state view, and the default start policy.
- Elaboration in Lean, with slang as a multi-point witness.

**Generalizes to other lanes** (§10):
- authority plus direction-labelled derived views;
- a refinement of the fuel-placement law for defunctionalized languages;
- a three-way procedure for narrowing a language's latitude;
- parameters treated as a ∀-dimension;
- observation-indexed trusted statements;
- environment disciplines;
- one shared contract shape;
- structured names.

---

## 1 What strategies a proof assistant will want

**Evidence: what today's proofs consist of.**
- **The split between thinking and plumbing** (MEASURED, strategies digest, which counts non-blank, non-comment lines per declaration).
  - Hand proofs without tactics are about 91% plumbing: add_n_byhand has 47 thinking lines out of 509, and mul_n_byhand about 119 out of 1385.
  - With today's tactics, thinking rises to 54–62%: clmul_n 111 of 206, mul_wallace 164 of 264, fdivp about 1790 of 2978.
  - The remaining plumbing is *bridging*: Int↔Nat casts, `rmN`, knownness, context widths. fdivp's design-to-model glue is 1153 lines, and DpG0 alone is 110 hand-written word-value lemmas.
- **The thinking is always the same four acts:**
  - a depth rank (1–14 lines);
  - an invariant proved by induction on a *source index* (bit, row, adder, stage), never on fuel;
  - a view structure that restates the netlist over Nat;
  - a spec collapse.
- **No proof in the repo unrolls a loop** (READ, all seven ∀N references).
- **Elaboration time goes to plumbing.**
  - The rank obligation is 26–40% of a file's time, and coverage 14–16% (MEASURED, PROVING.md §9, §11).
  - Before WP-P, mul_wallace spent 35 of its 53 s normalizing obligations and 1.5 s on arithmetic (MEASURED, PROVING.md §11).

**The strategies, and what each needs from the design.** Solver-dependent techniques are out under ruling 5, but each has a Lean analogue that stays possible.

| # | Strategy | Wins on | The semantics and tactics must offer | Agent thinks / automation does | Solver status |
|---|---|---|---|---|---|
| 1 | Induction over a source index (genvar, trip, bit, row) | every parametric datapath | Families and loops stay quantified, with the index free. Recurrences are printed in the source index. A Nat-indexed cell view is derived by theorem | Thinks: the invariant. Automated: equation derivation, casts | none |
| 2 | A procedural `for` read as a fold or recurrence over its trip list | clmul, CRC, shift-xor, restoring division | The loop is a node. Its meaning is a fold over the trip list taken from the header. A generic-trip step equation, frame lemmas, totality. No fuel | Thinks: `induction k`. Automated: the generic-trip step, frames | none |
| 3 | Rank or topological certificate | every combinational design | Site identities; a checker that names the offending edge; cheap reflective checking | Thinks: a 1–14 line key. Automated: the check | none |
| 4 | Data abstraction, bits to numbers | wherever the spec is arithmetic | A word-level value view, with one value lemma per operator, context width included | Thinks: which number and which modulus. Automated: value lemmas, knownness | none |
| 5 | Refinement to a Lean reference model (RTL ⊑ model ⊨ spec) | FP, crypto, ISA units | The model as target; a "net = model term" lemma form; a kernel-reducible model | Thinks: the model and its proof. Automated: the RTL↔model glue | none |
| 6 | Cut points and stage decomposition (SVTV style) | deep datapaths, pipelines | Every net and register nameable at a cycle; composition of stage lemmas | Thinks: where to cut. Automated: symbolic evaluation per stage | GL/FGL out; `simp` in |
| 7 | Inductive invariant plus simulation relation on state | every clocked design | One next-state equation per register; pre- and post-edge frames; a stable state projection; a library cycle induction; reset forgets x | Thinks: R and Inv. Automated: cycle unfold, NBA, settle | none |
| 8 | Module contracts, assume–guarantee, uninterpreted children (∀ f) | hierarchy, reuse, recursive designs | Instances stay boundaries in proofs; a child is proved once; one composition theorem; circularity broken by rank or by time | Thinks: the contract. Automated: connections, knownness transfer | UF checkers out; ∀ f in |
| 9 | Memory and array abstraction | register files, RAMs, caches | Arrays are array-valued state of symbolic depth, with read-over-write lemmas | Thinks: the memory invariant. Automated: read/write lemmas | none |
| 10 | Burch–Dill flushing and completion functions | pipelines against an ISA | The step can run from any state; stuttering in statements | Thinks: the abstraction function. Automated: the symbolic flush | original UF checker out; `simp` flush in |
| 11 | k-induction as induction over k-cycle blocks | safety properties that need history | A composed k-step equation from a free state | Thinks: k and the strengthening. Automated: the unroll | SAT form and IC3/PDR out |
| 12 | Relational invariants over a product (self-composition) | equivalence, constant time, non-interference, X-robustness | Two runs in one semantics; product machines over *exact* views | Thinks: the relational invariant | none |
| 13 | Symbolic simulation and exhaustive kernel `decide` | short fixed-size pieces; domains of at most about 2^8 | Fuel-free, structural, kernel-reducible views | Automated | kernel `decide` only (aes_sbox: 256 inputs, READ `sbox_bp.lean:200`) |
| 14 | Stuttering and measure-based latency refinement | variable-latency units, handshakes | Transaction or stutter statements; well-founded measures | Thinks: the measure | none |

**What the design must never preclude** (JUDGED from the table and from rulings 1–3):
- Source structure must stay addressable: loops, generate families with a free genvar, instances as boundaries, registers and nets by source name.
- The step must be runnable from any configuration; flush and X-robust proofs need this.
- Two runs, or two designs, must live in one semantics.
- Proof-facing views must be kernel-reducible and free of fuel.
- Every view must be derived by theorem and never become the definition.

**What follows for automation** (ruling 3):
- Automate the derivation of equations and recurrences, next-state equations, frames, settle uniqueness, casts and context widths, knownness, coverage and rank checking, connection renaming, and symbolic k-step unrolling.
- Do not automate invariants, relations, contracts, cut points or the spec collapse. The agent has the smarts.

---

## 2 What kinds of properties we will want to prove

Each class below is tied to the judgment that states it. The ranking is JUDGED from the repo's demand and from public practice.

**Demand.**
- **Real CPU blocks** (MEASURED, RB82 census, `rb0/census.json`):
  - 82 blocks: 43 combinational, 36 sequential, 3 hierarchical.
  - Comb: decoders 14, ALUs 6, ff1 6.
  - Seq: mult-div 12, regfiles 7, CSRs 6.
- **Instances**: 141 of 331 survey entries instantiate modules (READ `real-world-sv/SURVEY.md`).
- **Concurrent assertions**:
  - 1,358 of 22,043 sv-tests paths (READ `docs/sv-concurrent-assertions.md`);
  - lowRISC `ASSERT_*` processes in 13 RB82 blocks (MEASURED, census).
- **Public practice** (CITED via digest):
  - AMD K7 FP (Russinoff);
  - Intel's i7 execution cluster (CAV 2009);
  - Centaur;
  - riscv-formal (RVFI);
  - Arm ISA-Formal;
  - Kami's multicore;
  - Burch–Dill and Sawada–Hunt;
  - Iodine and UPEC.

| Rank | Property class | Example | Statement shape | Judgment |
|---|---|---|---|---|
| 1 | Exact combinational function | add, mul, clmul, aes_sbox, fdivp | function | Sat, with no state (CombTask) |
| 2 | Relational combinational spec: input relies and output don't-cares | decoders, ff_one when x = 0, alu_div `DivPre` | relation under a rely | Sat; CombTask cannot state it today (READ `Task.lean:167-198`) |
| 3 | Sequential refinement from reset | counter, CRC step, LFSR, CSR file | Moore or Mealy simulation relation + invariant | Sat (SeqTask) |
| 4 | Fixed-latency pipeline | pipe_mul | y_c = f(x_{c−D}) | Sat (PipeTask) |
| 5 | Memories, FIFOs, register files | 7 regfile blocks; cv32e40p FIFO | simulation with a Mealy read relation | Sat over pre-edge samples |
| 6 | Bounded-latency transaction | serial mul/div (12 RB82 blocks) | request ⇒ response within L, held | Sat with a ghost counter (safety form) |
| 7 | Protocol invariants and stream conservation | valid/ready held, skid buffer, AXI-lite | invariant + beat-prefix relation | Sat with a causal closed-loop rely |
| 8 | Hierarchical contracts and composition | ripple_fa, ibex_ex_block | per-module rely ⇒ guarantee + one composition rule | Sat per module + the composition theorem |
| 9 | ISA conformance and µarch refinement of a core | RVFI-style, Burch–Dill; `LeanModels.Rv` | stuttering simulation, ghost in-flight list | Sat (closed-loop memory environment) |
| 10 | Equivalence of two designs (golfed against reference, retiming) | svGolf variants | two runs, same stimulus, observation map | ⊨² over exact views |
| 11 | Non-interference and constant time | ibex multdiv `data_ind_timing_i` | 2-safety | ⊨² |
| 12 | X-robustness and initialization | unreset registers under `if (x)` | the same answer under every 2-state concretization | ⊨², or a start policy plus an x-decision census |
| 13 | Race-freedom and determinism | swap_nba, race_blk; `Deterministic2` (READ `Mono2.lean:706`) | equality over schedules | ⊨² over schedules (a per-design theorem, family §6) |
| 14 | In-source SVA | ibex/OpenTitan `ASSERT_*` | properties sampled at Preponed, with `disable iff` | Sat after compilation (assume → rely, assert → guarantee, cover → realizability witness) |
| 15 | SoC integration: connectivity, address maps, CSR maps | CsrBehavior tables | function or invariant across the hierarchy | Sat with hierarchical observables |
| 16 | Unbounded liveness, starvation, deadlock | arbiter, "no wedge" | ∀n ∃m ≥ n under fairness | ⊨ω (stream), last |
| 17 | Clock-domain crossing | async FIFO with Gray pointers | invariant over every interleaving and every sampling choice | Sat over an over-approximating per-bit old-or-new oracle; later |
| 18 | Cache coherence and memory consistency | Kami; SC over arbitrary hierarchies | refinement to SC + SWMR, ∀ agents | Sat, contracts, families; last |

**What the statement layer must expose** (JUDGED, each tied to a row above):
- **Input relies and relational guarantees** (rows 2, 6, 7). Don't-cares are also an area lever in svGolf.
- **Two samples per slot.** The pre-edge sample is where Mealy outputs, register-file read-during-write and SVA sampling live (rows 5, 7, 14). Today's post-edge snapshots cannot see it (READ `svgolf/design/sequential/README.md:164-169`).
- **Causal environments** that answer as a function of past outputs (rows 7, 9).
- **Ghost state** (rows 6, 9).
- **Realizability twins** for every safety statement, because a safety statement over an empty behaviour set proves nothing (circuit lane, READ `circuit-assurance-architecture.md:16-31`).
- **A relational judgment** over two runs (rows 10–13).
- **A stream judgment** (row 16), later.
- **Start policies**: the LRM's x start, or every refinement of it (row 12). Today `if (x)` takes the else branch (READ `design/sequential/experiments.md:37`), so an unreset register can look known in simulation while silicon is arbitrary.

---

## 3 What SystemVerilog constructs and statements we must support

The tables are by phase and tier. Frequencies are MEASURED, each in its named population:
- S331: survey entries;
- F216: a statement census of self-contained survey files;
- RB82: real CPU blocks, where only blockers are counted;
- SVT: sv-tests through the self-check path.

Status is READ. Tiers are JUDGED:
- T1: an ordinary synthesizable block;
- T2: whole designs;
- T3: verification;
- T4: not now.

The LRM charter (`docs/sv-charter.md` §6) puts the whole language in eventual scope, so T4 means "not in the proof-facing language now", not "never".

### 3.1 Statements (the procedural language)

**Native today in Stmt2** (READ `LeanModels/Sv/Sem2.lean:198-205`): blocking assignment, nonblocking assignment, `if`, block, `case` / `case inside` (with its qualifier carried as data), and `unsupported`.

T1, which must be nodes:

| construct | frequency | status today |
|---|---|---|
| `for` with its header as written | S331 112 (34%); F216: 238 loops in procedural blocks, 189 of them parameter-bound, plus 58 in subroutines | literal bounds: unrolled by the extractor. Parameter bounds: `PStmt.forLoop`, unrolled by `Param2.instStmt2` with fuel 128, so at most 126 trips (READ `Param2.lean:1289-1295`) |
| `repeat`, `while` and `do-while` with a static bound; `foreach` over a static array | S331 2; F216 1 + 1 | refused on the proof path; the self-check path (`SStmt`) has them |
| `break`, `continue`, `return` | F216: `break` in 4 files; 22 `return`s in functions | `SStmt` only |
| block-local declarations, static and automatic | S331 66; F216 43 files; RB82 `ld-localdecl` 7 | static locals are hoisted by the extractor; the rest are refused |
| function and task calls (with formals, locals, `return`, out/inout) | S331 96; F216: 157 functions and 10 tasks, 28 functions containing a loop, 12 with out/inout | only pure single-return shapes are inlined by the extractor |
| `casez`, `casex` | S331 13 / 2; RB82 2 | refused (`st-casez`) |
| `unique`, `unique0`, `priority` on `if` and `case` | S331 39 + 2 | refused, or carried as data |
| `op=`, `++`, `--` as statements | F216 2 files; RB82 2 | rewritten only for pure targets. A node is needed, because LRM 11.4.1 evaluates the target once |

T2: named blocks and `disable`; assignments inside expressions.
T3: immediate `assert` (RB82 6); `$display` and `$error`.
T4: delays, `wait`, events, `fork`. These are already in `SStmt` and the R1 scheduler.

**Answer to the maintainers' question 4 (§5.3 has the reasoning):**
- Yes, every SystemVerilog statement should be a node, but of the one parametric AST that the authority reads, not of Stmt2 grown in place.
- `SStmt` already has most of these as structural constructors (READ `SelfCheck.lean:284-357`).
- About ten of SStmt's 34 constructors are continuation states of a stepper (`forAfterInit`, `repeatBody`, …). They move into the stepper's frames and leave the AST.

### 3.2 The other phases

| phase | T1 (must have) | T2 / later | evidence |
|---|---|---|---|
| **Elaboration** | parameters and localparams (typed, several of them); packages (`pkg::X`, import, package enums, typedefs, functions); enums; packed typedefs; generate-for, generate-if and generate-case; block-local and generate-local declarations; `$clog2`, `$bits`, `$size`; instances with overrides and named, `.*` or ordered ports; 32-bit `int` genvar arithmetic | type and struct-valued parameters; instance arrays; recursive instantiation; interfaces and modports; `defparam`, `config`, `bind` | packages gate 16 RB82 blocks and are the sole blocker for 6; 26 of 82 import one (MEASURED). Generate-if: S331 77. Instances: S331 141 |
| **Expressions** | the full operator set (already in Expr2, READ `Sem2.lean:147-175`); declared `signed`, `$signed`, `>>>`; context width and sign computed per point (LRM 11.6–11.8); explicit casts; `inside`; streaming; `$countones`, `$onehot`; x/z literals; `===`; `==?` | `let`; real, string | casts: S331 49, RB82 9. Context width is today taken from slang's default point (READ, construct digest) |
| **Lvalues and aggregates** | bit and part selects; `+:`/`-:` with a run-time base; multi-dimensional packed paths; concatenation lvalues; packed structs and unions; struct member select; **unpacked arrays of parameter size**, including ports; assignment patterns; 2-state declarations | unpacked structs; tagged unions; dynamic arrays (T3) | unpacked arrays: S331 102. All 7 RB82 regfile blocks fail as written (MEASURED) |
| **Processes** | `always_comb`; `always @*` and `@(a or b)` as their own process kind; `always_ff` and plain edge `always` with async reset of either polarity; continuous `assign` | `always_latch`; negedge, several, gated or derived clocks; `initial` on state; `final` | `always @*`: S331 57, RB82 17. ibex and cv32e40p tops gate the core clock (CITED, critic: `prim_clock_gating`, `cv32e40p_clock_gate`) |
| **Drivers and nets** | `wire` with single-driver resolution; implicit nets; `wire x = e` | several drivers; z; tri-state; `inout`; wand/wor; strengths; primitives and UDPs | F216: 132 of 216 files declare a net |
| **Memories** | register files with a run-time indexed read and write; ROMs as case tables | `$readmemh` (never in svGolf) | — |
| **Verification** (T3) | keep assertions in the AST as *observation* nodes (never processes) so that a block is no longer loud because of them | concurrent `assert`/`assume`/`cover`, sequences, checkers | RB82: 13 blocks have `ASSERT_*` processes, 8 have `initial` assert guards (MEASURED) |

**Caveats.**
- S331 and F216 are algorithm kernels. RB82 sees only blockers, and its base predates WP-PROC G1.
- No census of the symbolic proof path over sv-tests exists. One is needed before any new tier is priced (§7).

---

## 4 The target architecture under the ruling

### 4.0 The shape in one picture

```
 source.sv ──slang (parse, lexical names; types as ANNOTATIONS)──▶ envelope sv-0.3 (Sv.Ast, nothing lowered)
                                                                        │
                       ┌────────────────────────────────────────────────┘
                       ▼
   E  (AUTHORITY, trusted, minimal)   elab : Lib → Mod → Params → Except ElabRefusal Elab
                                      step : Elab → Choice → Config → StepResult     -- total, structural
                                      Steps / Behaves  (inductive closure; no fuel)
                                      obs  : Config → Sample  (Preponed, Postponed of declared observables)
                       ▲  refinement theorems, proved ONCE per fragment, each direction-labelled
   D  (DERIVED, untrusted, proved)    expression/word view · body view (structural, SemM) · loop recurrence
                                      settle view (CombEqs) · register-transfer view · cycle machine (Mealy)
                                      array view · function view · module composition · 2-state ∀ω view · contracts
                       ▲  reflective fragment checkers + application of the theorems
   L  (LIBRARY, never trusted)        sv_open / sv_cycle / sv_equations … print source-named equations
   S  (STATEMENTS, trusted)           Sat (Contract over obs + env relies) · ⊨² · later ⊨ω
                                      CombTask, SeqTask (separate structures, proved instances) · svGolf Admissible
   X  (EXECUTOR, harness)             exec budget policy = iterate step ; the ONLY fuel ; exec_sound
```

### 4.1 E: the exact semantics (the authority)

**Domain.**
- E covers everything the LRM defines for the T1 and T2 synthesizable language.
- It also covers the timing and simulation constructs testbenches need (delays, events, `wait`, `$display`), because the Xcelium pins are testbench-driven and SVA sampling is defined in region terms.
- Constructs outside this domain are refused in one of two places: at elaboration, where the design has no meaning, or as a dynamic `unsupported` node reached at run time. Both are loud.

**Form: a total small-step function and its closure.** The form is executable, and it uses no fuel.

```
Elab      := scope tree; per scope: env (parameter/genvar values as 32-bit or declared type),
             types computed in Lean, generate families (trip list from the header + one body scope),
             instance REFERENCES (module, computed parameter values, connections), processes,
             declarations, driver slots keyed by LONGEST STATIC PREFIX
VarId     := ⟨path : List Seg, decl : Nat⟩ ;  Seg := inst k | gen k i | blk k
Config    := { time, store : VarId → Val, drivers : DrvId → Val, procs : ProcId → ProcState,
               queues : RegionQueues, nba : List Update, future : TimeQueue, envState }
ProcState := { frames : List Frame, status : running | ready | waiting Trigger | done }
step      : Elab → Choice → Config → StepResult     -- one micro-step
StepResult:= next Config | slotClosed Config | refused Refusal
```

**What a micro-step is.** One micro-step is one of:
- one assignment or condition test;
- one frame push or pop (entering a loop trip, a call, a block);
- one region transition;
- one NBA commit;
- one driver resolution.

**How `step` is built.**
- `step` is defined by structural recursion on the top frame. There is no `partial` and no well-founded recursion, so the mergeSort trap is avoided.
- Loops are frames that hold their *trip list* as data. The body stays a syntactic subterm. This is family §3.6(1a): data carries the decision, never the scrutinee.

**Where nondeterminism lives: only in `Choice`.**
- `Choice` picks which ready process runs next in the current region.
- This generalizes `ScheduleOracle`, whose `choose_perm` already carries the legality proof (READ `docs/sv-r1-scheduler.md:165-180`).
- Choices are consulted only when the running process suspends or finishes. **E is process-atomic between suspension points.** This is a declared narrowing of LRM §4.7 (decision D1 in §6). The repo's own quotation of §4.7 says a simulator "may suspend execution" at any time while evaluating a procedural statement (READ `docs/sv-oracle-disagreements.md:1264-1268`).
- Under that literal reading, even a one-statement `always_comb c = b & d;` can read `b`, be preempted, miss the wake-up from another process's write of `b`, and end the slot stale (JUDGED construction).
- If preemption were admitted, no combinational or cycle view could hold for ordinary RTL.
- Xcelium re-runs the block, Verilator models no event order, and Yosys computes the settled value (READ, same file). Every tool on the panel therefore behaves atomically, apart from Icarus's synchronous BUFZ case, which is already refused as `AlwaysComb:alias-read`.
- For edge processes that communicate only by NBA, preemption is unobservable by a mover argument: their reads are of values nobody changes in Active, and their writes are deferred (Lipton, READ `proof-framework-research.md` §7.4; JUDGED application). So the narrowing bites only on comb-style processes.

**Behaviours, and where nontermination lives.**

```
Steps e ch : Config → Config → Prop                -- inductive reflexive-transitive closure
SlotCloses e ch c c'  := Steps e ch c c' ∧ step… c' = slotClosed _
Behaves e env ch (b : Nat → Config) : Prop          -- slot k closes at b k; inputs from env
Progress e env := ∀ ch k, slot k closes             -- a PROPERTY, discharged by lens theorems
NeverRefused e env := no reachable `refused`
```

Nontermination comes in three kinds, and none of them needs fuel:
1. A process activation that never suspends: a zero-delay `while`, `forever` without timing, or recursion. This is an infinite micro-step path inside one slot.
2. A zero-delay oscillation between processes. This is also an infinite path inside a slot.
3. Unbounded simulation time. This is productive behaviour, and its trace is indexed by slot number.

Kinds 1 and 2 are the *absence* of a `SlotCloses` derivation. `Progress` is a proved property: R-COMB and R-EDGE discharge it with their measures. Kind 3 is the index of the stream `b`. Statements quantify over every prefix, which is family §6's observation-indexed reading.

**The executor, and the one place fuel survives.**
- The executor is `exec budget policy c = iterate (step · policy) budget c`, and it is the only fuel in ls-sv.
- `exec_sound` (`exec n pol c = closed c' → Steps c c'`) is the single fuel lemma. It is proved by induction on `n`.
- The executor serves the harness, the Xcelium pins, `#guard`s and kernel `decide` on tiny fixtures. It is not a second semantics: it *is* `step`, iterated under one particular choice function.

**The monad.**
- A micro-step of one process lives in Core's `SemMWith`. `SvM := SemMWith SvWorld Finish SvClause Unit` already exists (READ `LeanModels/Sv/World.lean:257`).
- The process table and the queues live in the world, per family §3.6(1a).
- `x` is a value and never ρ. ρ is `Finish`.
- Refusals are `Loud.unsupported` with an `SvClause` payload (READ `Core/Outcome.lean:180-188`).

**Values.**
- Packed 4-state `LVec` from Basic.lean, with its pinned operator tables.
- Unpacked arrays as functions from index to value. The executor uses persistent arrays underneath.
- Structs and unions.
- An x or out-of-range index reads as the LRM and the Xcelium pins say, and a write there changes nothing.

**Drivers and nets.**
- Every continuous assignment, net port connection and primitive output owns a driver slot keyed by its longest static prefix, so `rf_reg[i]` per genvar is legal (ibex, READ via critic).
- A net's value is its nettype's resolution over its slots.
- A variable may have one continuous writer per element.
- "A single-driver net behaves as a variable" is a theorem, not an extractor rewrite.

**The environment.**
- It is part of the configuration: a causal function from the observed history to the next batch of input events (a time delta and port changes). Closed-loop memories and buses can therefore be expressed, and causality holds by construction.
- Clocks are ports that the environment drives. There is no implicit clock. An edge is a value change classified by the LRM's 9.4.2 table.

**Observation.**
- `obs` returns two samples per slot of a *declared observable set*: the Preponed sample (before anything in the slot runs) and the Postponed sample (after the slot closes).
- The set is ports by default. Hierarchical internal signals are added only for cut-point lemmas, never in trusted statements.
- The cycle notions are derived from these. For a clock edge in slot t, pre = Preponed(t), which is what flops and SVA sample and where Mealy outputs show. Post = Postponed(t).

**Elaboration semantics, which is part of the authority by the ruling.**
- Parameters are bound in scope environments, never substituted.
- A generate-for is a family: the trip list computed from its header in the LRM's 32-bit `int` arithmetic, plus one body scope read under `env.bind g v`. It is never expanded in a term. Today's `GenItem.genFor` already has this structure (READ `Param.lean:516`).
- An instance is a reference.
- Types, widths, signedness, enum values and label offsets are computed in Lean at each point (LRM 11.6–11.8).
- slang's results arrive only as annotations. They are checked against Lean's at **several** parameter points, using the Probe2 pattern; the default point alone hides divergence at other N (critic).
- Hier2's port, driver and clock rules, which are pinned against simulators, become elaboration rules.

**The extractor contract.** The extractor may emit only what is:
- (a) a function of the source text and lexical scope, with no parameter value consulted;
- (b) structure-preserving, one node of the same kind per construct;
- (c) semantics-free, deciding no LRM rule.

Everything else moves into Lean, and each item becomes either a theorem or a refusal: loop unrolling, function inlining, local hoisting, `@*`→`always_comb`, net→variable, array flattening, `$countones` trees, and default-point widths. One-to-one spellings may stay, for example `~^` and genvar step forms. This is C's no-transformation law (READ `c-tier-architecture.md:421-426`) and the no-lowering ruling, stated once.

**Loudness has three distinct shapes.** Today they are conflated.
1. **Elaboration refusal**: the design has no meaning.
2. **Dynamic refusal**: a reachable `unsupported` node. Every statement requires `NeverRefused`.
3. **View refusal**: the design has a meaning, but a view's hypothesis fails. The tactic names the hypothesis.

### 4.2 D: the derived layer (cycle semantics and module contracts)

The views are listed in the order proofs consume them. Each is a Lean definition plus a refinement theorem (§4.3).

| view | what an agent sees | from |
|---|---|---|
| **D1 expression and word view** | a total, structural `evalE env st e`, and `XF.val` word values with a value lemma per operator, context width included | `evalPure2` promoted to be E's own expression evaluator (READ `Pure2.lean`, fuel-free, adequate in both directions) |
| **D2 body view** | `execBody : Stmt → SemM … Flow` (Flow = next \| brk \| cont \| ret v), structural and fuel-free. Defined on the *static* fragment: loops over header trip lists, acyclic calls, no timing, no data-dependent `while` | `Stmt2.symExec` and `stepSStmts_done_agrees` generalized (READ `Comb2Proc.lean:484,1835,1997`; `Step.lean:365,506`) |
| **D3 loop recurrence** | `rows 0 = pre`, `rows (k+1) = body (trip k) (rows k)`, frame and totality lemmas; Std's `Spec.forIn_list`/`Spec.foldlM_list` as the loop rule (READ toolchain `Std/Do/Triple/SpecLemmas.lean:802,829`) | LOOP-NOTE G1's rule library, reread as lemmas about D2 |
| **D4 settle view** | one equation per comb node (`eq_<sig>_<site>`); the settled frame is the *unique* solution (`settle_spec`); evaluation in Kahn order, structural on the node count, with "no order exists" being exactly a cycle | `CombEqs` (READ `Comb2Base.lean:854`), `Terminates2.of_acyclic`, Lutsig 2.0's rule (CITED via digest, thesis §5.8.2) |
| **D5 register-transfer view** | one next-state equation per register *slice*, read from the pre sample: `step_parallel` | new; the sequential analogue of CombEqs |
| **D6 cycle machine** | per module at a parameter point: `out : Store → In → Out` (Mealy, settled), `next : Store → In → Tick → Store`, `init` (start policy), `arcs` (combinational dependencies at bit or field granularity) | P's `Machine`, with a **uniform** `Store := VarId → Val` instead of a dependent `St`. Typed records are presentation, not semantics (JUDGED: avoids kernel and `decide` problems with computed types) |
| **D7 array view** | `Fin D → BitVec W` (or `LVec W`), read-over-write | new |
| **D8 function view** | `fn.spec` per definition; a call equals the body in a fresh frame | new |
| **D9 hierarchical composition** | `compose parent (fun k => childMachine k)` with child slots and declared arcs; replication over instance families | P's open semantics; Kami's Thm 5.4 shape (CITED via digest); WP-I route C as its combinational special case |
| **D10 2-state ∀ω view** | values as `BitVec`, every x-source drawing from an oracle ω, with an x-source census | P's two-valued domain, **demoted to a view** anchored by `fourState_abstracts` |
| **D11 contracts** | `m ⊨ C`: ghost state, causal rely over shared history, relational guarantee, declared arcs, realizability twin, receptiveness | P's `Contract` plus the circuit lane's `RealizableUnder`/`ReceptiveUnder` |
| **D12 legacy Design2** | `run2`, `⊨₂`, `Computes` | kept only as a view behind R-DESIGN2 until its estate is transported |

**Hypotheses as checkers.**
- The cycle and settle views carry P's discipline S1–S7 as *hypotheses*, not as admission into meaning. Each is a `Bool` checker with a soundness theorem, decided on the *template*.
- At a symbolic N, the rank and the window-disjointness hypotheses become named obligations.
- Added to S1–S7: the clocking discipline (§4.3, R-CYCLE) and the x-decision census (R-X).

### 4.3 Every refinement theorem between the layers

**Common rules for all of them.**
- Each is proved **once**, generically, for its fragment, by the lane. None is a per-design translation validation through E. The critic's point stands: reducing an event kernel on an ibex-sized block will not finish (JUDGED). The family measured the same effect: the faithful Python interpreter does not close at 8M heartbeats where its twin closes in 568 ms (READ `family-architecture.md` §3.4, the asterisk paragraph).
- Each carries a **direction** label, following the circuit lane: Exact, OverApprox or UnderApprox.
- Automation consumes each one the same way. A tactic decides the hypotheses by reflection at a concrete point, or emits them as named goals at a symbolic N, then rewrites with the conclusion.

| id | statement shape (JUDGED sketch) | hypotheses | direction | consumed by |
|---|---|---|---|---|
| **R-ELAB** | `elab lib m p = .ok e → e.family g = ⟨tripList hdr (env p), body⟩ ∧ widthOf e x = W p …` (instantiation lemmas at a symbolic p) | header in canonical form (`++`, `--`, `+= c`, `-= c`); 32-bit agreement (`int32Agrees`) | Exact | every tactic that reads a family with a free index; reuses Gen2's 195 lemmas (MEASURED, audit) |
| **R-BODY** | activation of process π from frame f, run by micro-steps until it suspends or finishes, = `execBody env (body π) f` | body in the static fragment; acyclic calls | Exact | D3, D4, D5; `mvcgen` on `execBody` |
| **R-LOOP** | `execBody (for hdr body) = foldl (fun st v => execBody body (st.bind i v)) st (tripList hdr)`, plus `rows` lemmas | iterator not written in the body; header canonical | Exact | LOOP-NOTE G1, Bridge S |
| **R-FUN** | `execBody (call f args) = execBody f.body (frame args)`; then `fn.spec` | call graph acyclic | Exact | decoders, RVC expanders |
| **R-COMB** (keystone) | from any configuration satisfying the settle invariant, every process-atomic schedule closes the slot, and the closed store, restricted to comb-written elements, is the unique solution of the node equations | single driver per longest-static-prefix element; acyclic at bit or field granularity (a rank); sensitivity-complete (`always_comb` by definition, `@*` by R1–R6); no alias-read (READ `CombAlias2.lean`); latch-free | Exact on every signal | D4, and the `Progress` conjunct of statements |
| **R-EDGE** | in a slot where only `clk↑` (and/or a reset edge) occurs, the closed store = `settle(commit(⋃π nextπ(pre)))`, independent of the schedule | canonical event controls; edge processes communicate by NBA only (blocking writes to locals, written before read); one edge writer per slice; clock not read as data; no data or reset change in that slot | Exact | D5 |
| **R-CYCLE** | `∀ ch, Behaves e env ch b → (obs b at the edges of clk) = CycleMachine.run m (cycleInputs env) s0` (pre = `m.out s i`, post = `m.out (m.next s i) i`) | the R-COMB and R-EDGE hypotheses; `Disciplined clk rst env`; `s0` in the start policy | Exact on observations | SeqTask, PipeTask, TxTask, contracts |
| **R-RESET** | from any start in the policy, after reset is asserted across an edge (or asynchronously), the state equals the reset values | reset branch writes every register | Exact | X-robustness by start policy |
| **R-HIER** | the behaviour of `e` with instances as references = `compose` of the parent's own machine with its child machines; `flatten_sound` relates it to Hier2 | each child satisfies R-CYCLE; the parent's graph composed with the children's arcs is acyclic; port connection admitted by Hier2's pinned rules | Exact | D9; every hierarchical proof |
| **R-CONTRACT** | `machine m ⊨ C` together with R-CYCLE gives `E ⊨ C↑`, where C↑ lifts the cycle rely to an event-level rely (the discipline plus the rely on sampled inputs). Composition: if each child satisfies `C_k` and the abstract parent satisfies `C`, the parent satisfies `C` | receptiveness of each `C_k`; acyclic declared arcs; rely discharge by wiring, by a sibling's guarantee in the same cycle along an acyclic arc, by the past, or by the parent's own rely | **OverApprox** (safety only) | every contract proof; never transfers a hyperproperty |
| **R-X** (`fourState_abstracts`) | if the 4-state run makes no procedural decision on x, its known observed bits equal the 2-state bits under every ω | the x-decision census (the non-monotone `===`, case match and `$isunknown` are flagged); every operator table monotone in the information order | Exact on known bits; ∀ω OverApprox of silicon power-up | D10, X-robust statements |
| **R-PRODUCT** | `(m ×ₘ m') ⊨ C₂` → `E ⊨² C₂` | exact views only, or a child machine shared by both copies (the refinement paradox, CITED via critic: Clarkson–Schneider) | Exact | equivalence, constant time |
| **R-DESIGN2** (legacy transport) | for an admitted `pd`: `run2 (instantiateGD2 pd p) σ fuel stim = .ok tr → tr = post-samples of E under clockExpand stim`, and E has `Progress` | the `pd` is in the R-CYCLE fragment **and has an acyclicity certificate**, because v1's `Terminates2` is about σ-ordered whole passes, not about every event schedule (critic) | Exact on observations | transfer of every Design2 theorem and svGolf record |
| **R-GATE** (later) | a latch-based clock gate with an enable latched while clk is high gives a derived clock under which all flops sample old values | the ICG pattern | Exact | ibex_top and cv32e40p tops |
| **R-CDC** (later) | E ⊆ the per-bit old-or-new oracle | — | OverApprox. The step "oracle ⊇ silicon" is extra-semantic and must be stated as an assumption | multi-clock statements |

**The clocking discipline**, the hypothesis that makes R-EDGE and R-CYCLE true. `Disciplined clk rst env` is a predicate in E's own vocabulary. It requires:
- data inputs and reset change only in slots with no `clk` posedge;
- reset is held across an edge when synchronous reset is meant;
- there is no time-zero race with `initial` code.

Today the discipline is hidden in two places:
- the harness's `clockExpand`, which uses two slots per cycle with inputs held on both (READ `Adequacy.lean`);
- `cycleStep2`'s order: apply inputs, settle, reset, edge, NBA, settle (READ `Sem2.lean:695-708`).

A lemma `clockExpand_disciplined` should make that hidden assumption a theorem. Cycle-level statements carry the discipline as a rely; event-level statements need not.

**Proof sketch for R-COMB, so it can be priced** (JUDGED):
- **Termination**: a lexicographic multiset measure over ranks. Running a node can only trigger nodes of higher rank.
- **Fixpoint**: by sensitivity. A node whose inputs changed after its last run is ready again, so a closed slot leaves every node consistent with its equation.
- **Uniqueness**: by acyclicity. This is CombEqs, which already holds.
- **What is new**: the event-level invariant, "every node that violates its equation is ready, or is triggered by a pending update". No mechanized precedent is known to me for proving a cycle model against an event-driven HDL semantics. Lööw/Lutsig, Kami and Koika define a cycle semantics directly (CITED via digest). Only an attempt can price it, which is why it comes first (§7).

### 4.4 The library and the proof interface

**What `sv_open M at p` prints.** Every item below is a theorem about E obtained through the refinement theorems, never a definition the agent must trust:
- `hgen`: generate conditions resolved;
- one equation per comb node, with loops kept as `rows` recurrences;
- one next-state equation per register slice;
- one Mealy output equation per output;
- each child slot as an atom, usable only through its contract;
- the x-source census.

**What a goal never shows**: a store lookup, fuel, a schedule or a string name. Values default to the 4-state `LVec` with knownness discharged by the library; the 2-state `BitVec` presentation is available through R-X. Which presentation agents handle better is an open experiment (§7, X11).

**What the agent supplies**: invariants, relations, ghost state, contracts and their arcs, cut points, ranks, and the spec collapse. These were 54–62% of today's tactic-route proofs (MEASURED, strategies digest).

**The cost model.**
- Lenses are instantiated per **module definition and template site**. They never see flat sites, N or the instance count.
- The acceptance metric is heartbeats, kernel time and `.olean` size per template site and per module, recorded against N. It must stay flat in N and in the number of instances.
- Today's baseline is about 15.7k thousand-heartbeats per flat site after WP-LIN, from a 90-site design (MEASURED, scaling audit). That is roughly 100 sites inside the 120 s svGolf limit (JUDGED).

### 4.5 The statement surface

**One trusted skeleton**, stated over E's elaboration and observation interface only:

```
structure Contract (P : Type) where
  inRange : P → Prop
  iface   : P → Iface                       -- typed ports, parametric widths
  rely    : (p : P) → Env p → Prop          -- event-level, causal; cycle tasks include Disciplined
  guar    : (p : P) → ObsPrefix p → Prop    -- safety, on every finite prefix of obs samples
  start   : (p : P) → StartPolicy           -- LRM x start, or every 2-state refinement of it
def Sat (lib) (top) (C : Contract P) : Prop :=
  ∀ p, C.inRange p → ∃ e, elab lib top p = .ok e ∧ ifaceOf e = C.iface p ∧
    ∀ env ch, C.rely p env → NeverRefused e env ∧ Progress e env ∧
      ∀ b, Behaves e env ch b → ∀ n, C.guar p (obsPrefix b n)
```

**What the skeleton means.**
- `∀ ch` ranges over process-atomic schedules. Determinism is a per-design theorem, never a tier-wide conclusion (family §6 and the anti-tautology rule).
- **CombTask and SeqTask stay separate trusted structures** (decided 10/30, READ `PLAN2.md:529`). Each is compiled into a `Contract` and proved equivalent to it, following `toSeq_satisfiedAt_iff`.
- Several parameters are `P := Nat × Nat`, replacing families of fixed tasks.

**Beside the skeleton:**
- `⊨²`: two behaviours of one design or of two, under related environments, stated over exact views;
- `⊨ω`: streams with a fairness rely, to come last.

**svGolf: `Statement := Admissible src ∧ Sat …`.**
- `Admissible` is a decidable synthesis-fragment predicate. It makes the existing `P-SAME-PROGRAM`, `P-NO-TOOL-DIRECTIVES` and `P-NO-SILENT-PICK` policies (READ `docs/sv-refusals.md:45-51`) part of the trusted statement instead of loader behaviour.
- It is needed because, once E gives meaning to every design, constructs where the LRM and Yosys disagree would otherwise have a provable meaning and a different scored netlist. Three measured cases:
  - a self-reading `always_comb`: Xcelium gives `xx,00,01,10` and Yosys `00,01,10,11` (READ `docs/sv-tools-split-audit.md:122-124`);
  - Yosys reads `unique` as full_case plus parallel_case (READ `svgolf/REFUSALS.md:87`);
  - `(* no_rw_check *)`.

**SVA** is a property frontend. `assume` compiles to the rely, `assert` to the guarantee, and `cover` to the realizability twin. SVA never executes as design processes.

### 4.6 What each layer takes from architectures F and P, and what it rejects

**Taken from F, for E:**
- one LRM-shaped AST in which every statement is a node;
- a total structural `step` with defunctionalized frames (Step.lean's stepper made total);
- no fuel in any definition;
- `Choice` as an explicit quantified parameter;
- execution from any configuration;
- structured `VarId`s;
- array-valued state;
- the three shapes of loudness;
- the extractor contract, with slang facts as annotations;
- two samples per edge;
- the rule that a new construct lands in the authority first;
- Design2 adequacy as the transport keystone (R-DESIGN2);
- its regfile and `exu` worked examples as acceptance targets.

**Rejected or amended from F:**

| F proposed | Instead |
|---|---|
| assignment-granularity preemption in `Choice` | process-atomic, as a declared narrowing |
| a per-variable single-writer rule | longest-static-prefix driver slots |
| lens refusal alone for svGolf | the `Admissible` conjunct |
| membership testing as the main fidelity check | deterministic replay wherever determinism is proved or censused, plus several choice policies |
| a slang cross-check at the default point only | multi-point probes |
| a cycle-sampled `PortHist` rely | an event-level environment with a discipline predicate |
| "one theorem re-certifies every record" | transfer per record, conditional on an acyclicity certificate |

**Taken from P, for D:**
- the compositional Mealy machine with child slots and arcs;
- Kahn-ordered settle, read through `settle_spec`;
- `step_parallel`;
- S1–S7 as view hypotheses;
- the `Tick` alphabet, fixed now: a set of simultaneous clock events, with async reset as an event;
- contracts with ghost state, relational guarantees, causal relies and realizability twins;
- the four rely-discharge modes;
- product machines;
- CombTask and SeqTask kept separate;
- the extractor print-back miter, as a checker only;
- a function store with O(1) update lemmas.

**Rejected or amended from P:**

| P proposed | Instead |
|---|---|
| `Sv.Sync` normative by declaration | refined to E by theorem |
| the event model as an untrusted oracle | E is the authority |
| adequacy as "a research goal that gates nothing" | the ruling makes it a gate |
| 2-state as the definition | 2-state as a derived view; ASSERT_KNOWN-style x-hygiene stays statable in 4-state |
| per-port arcs | arcs per bit or field. ibex_ex_block's shared adder already needs port-level arcs, and struct-bundled handshakes would need field-level ones (JUDGED) |
| a dependent `St`, and two evaluators with `exec_eq_sem` | a uniform store; the executor is `step` iterated |
| "outside S1–S7 the design has no meaning" | E gives it a meaning; only the view refuses |

### 4.7 Fidelity stays checkable

1. **One definition, one pin set.** The 590 Xcelium golden rows (MEASURED, a grep count of `harness/sv/xcelium_golden.json` in integ1102; LOOP-NOTE counted 579 on an earlier base) are re-pointed at the executor.
   - Where a design is proved or censused deterministic, the check is equality.
   - Elsewhere it is membership, checked under several choice policies.
   - A trace that Xcelium produces and E cannot is an E bug.
2. **Run every derived view on the same rows now**, long before its theorem exists. This is the Python lane's `--proof-interpreter` practice, whose first run found 25 wrong answers (READ `docs/python-architecture.md`).
3. **Cover every clause on the proof path.** Every `step` arm cites its `SvClause`. The clause census is re-run on E and weighted by RTL populations.
4. **Use slang as a witness for elaboration at several points.** Use Verilator with random initialization as a witness for the 2-state view.
5. **Keep the ledgers.** `docs/sv-refusals.json` (277 rows, per the brief) and `docs/sv-declared-divergences.json` are kept, and the §4.7 narrowing gets its own row.

### 4.8 A large block, walked through

The fuller walk is in the critic's ibex subsystem test.

1. **regfile, for every AW and DW.**
   - The memory is one array-valued variable. The reset loop is a `for` node whose trip list is `[0, 2^AW)`.
   - R-CYCLE yields `next_mem` (a point write under `we && waddr ≠ 0`), the Mealy read `out_rda = mem.read ra` in the pre sample, and a `rows` recurrence for reset.
   - The agent proves the reset invariant by `induction k`, then a simulation relation to `m : Fin (2^AW) → BitVec DW`. `2^AW` is never expanded.
   - Today this design fails four times: parameter-sized arrays are refused, the 126-trip cap applies, Mealy reads are invisible, and instances are refused.
2. **ibex_ex_block.**
   - The ALU and multdiv are proved once each against their contracts. The ALU contract alone is JUDGED at 300–600 lines.
   - The shared-adder cycle between them is acyclic port by port (the adder arc).
   - The rely on `imd_val` state held in the ID stage is a causal rely that holds "while busy".
   - `ex_ct`, the constant-time property, is a product-machine contract over exact views.
3. **Cost.** One lens per distinct module, plus one composition per hierarchy level.
4. **Prerequisites** (all T1): packages, enum parameters, unpacked-array ports, casts, `unique case` with a WP5-style "a violated qualifier is a run-time error" obligation (READ `svgolf/REFUSALS.md:87`), `$signed`, `>>>`, async reset, arcs, contracts and the composition theorem.

---

## 5 What this implies for today's open questions

### 5.1 The svGolf statements that rest on run2

**The facts** (READ):
- `CombTask.Statement` is `Interface ∧ (Unclocked ∧ Terminates2) ∧ Computes`, where `Computes` is `d ⊨₂ …` over `Runs2 d σ stim tr := ∃ fuel, run2 d σ fuel stim = .ok tr` (`svgolf/SvGolf/Task.lean:183-205`; `LeanModels/Sv/Spec2.lean:122-145`).
- No theorem connects `run2` to any other semantics. `CycleAdequacy` is about M0 and is unproved.
- The family's §3.4(b) debt for this is not registered, and svgolf/ cites family-architecture zero times (MEASURED, family digest).

**What to do** (JUDGED):
1. **Now, and in words.** Register a §3.4(b)/§5.0a debt row along these lines: "svGolf Statement v1 is stated over the Design2 cycle model (`run2`); it is pinned against Xcelium by testing, not refined to the authority by theorem. Retirement: R-COMB + R-EDGE + R-DESIGN2 proved, and Task v2 records re-certified." Say this plainly on the svGolf rules page. Correct every place that treats `CycleAdequacy` as the bridge, because it cannot be one.
2. **Now, in Lean, with no regret.** Define the observation interface (`obs`, Preponed and Postponed samples) with a run2-backed implementation. Post is `run2`'s snapshot; pre is `cycleStep2`'s `st2` (after the async-reset phase; `st1` only when no reset event fires, corrected 2026-11-02), which `run2` computes and discards. Prove `Computes ↔ Computes_obs` as a lemma, so records do not move. New statements, SeqTask included, are written against `obs`. When E lands, the implementation of `obs` changes underneath and R-DESIGN2 is exactly the theorem that the two implementations agree. This is family §8 step 9 applied to trusted statements.
3. **Keep v1 in force; do not freeze it as "proved against SystemVerilog".** Transfer records by theorem only once R-COMB and R-DESIGN2 hold, and only for records that expose an acyclicity certificate. Tactic-route proofs establish `Acyclic`. Whether every record does was experiment X3. They all do: 4 of 4 records and 18 of 18 references expose a named `Acyclic` (`599142bf`).
4. **New task classes** (SeqTask's counter, ruled the first public sequential task on 10/30) may launch on the run2-backed `obs` as *provisional*, explicitly re-certified later. Pipelines, transactions and contracts should wait for R-CYCLE.

### 5.2 Fuel

**Answer to the maintainers' doubt: agreed for definitions.**

| part | what happens to fuel |
|---|---|
| E | no fuel. Behaviours are an inductive closure; `Progress` is a proved property |
| D views | fuel-free and structural: `execBody`, Kahn settle, the cycle machine |
| executor | the only fuel, as a harness budget, with one soundness lemma |
| Stmt2 / Sem2 | statement-level fuel sits on finite trees in six of seven `.timeout` sites; only `combSettle2` (READ `Sem2.lean:603-610`) can really diverge (MEASURED, lead and audit). It retires with Design2, and its fuel-free twins (`evalPure2`, `symExec_sound/total`) become D1 and D2 |
| loops | LOOP-NOTE's G0 should be "trip list from the header, no fuel", not `loopFuel` |

Fuel is pervasive today: 1,346–1,412 lines of `LeanModels/Sv` mention it, depending on the regex (MEASURED, audit and lead).

Fuel also leaks into meaning today: the 126-trip loop cap and the generate `surfaceFuel = (Σ|args|+2)²+64` (READ `Param.lean:2262`). By reading, not by a run, the latter makes a parameterless design with a generate loop of 68 or more trips, or a `2**AW` loop at AW ≥ 8, an error design (audit). Both caps leave the meaning.

**Why this is not a family violation (§10.1):**
- Family §3.4 says fuel is an index and never a monad layer, and `proof-framework-research.md` §6.5 cites CakeML's clocked interpreter as a published design.
- SystemVerilog must defunctionalize its continuations anyway (§3.6(1a)). Once continuations are data, the recursion is the scheduler loop, and a closure relation expresses that loop with no index.
- Direct-style lanes such as Python keep the index. The lane's §8-step-7 decision should be recorded as exactly that.

### 5.3 Should every SV statement be a Stmt2 node? How the statement language evolves

**Yes in substance, no in letter** (JUDGED):
- Every statement becomes a node of **one** source-shaped, parametric AST, `Sv.Ast`, which succeeds PStmt and SStmt.
  - It is a superset of `PDesign`/`PStmt`/`GenItem`/`PInst`, so `ofPDesign` is an injection and every committed envelope converts.
  - It takes SStmt's structural constructors.
  - It leaves SStmt's continuation states to the stepper's frames.
- Stmt2 itself is the *instantiated*, flat, fuel-indexed cycle-model language: parameters are substituted and loops unrolled before it exists (READ `Param2.lean:1289-1295`). Growing it in place would keep unrolling at instantiation, which contradicts ruling 1. It would also touch the 21 files of `LeanModels/Sv` that mention `Stmt2` (MEASURED by `grep -rl`; the brief's 29 may use a wider pattern).
- So **freeze Stmt2** (no new constructors). It survives as the legacy view behind R-DESIGN2 until its estate is transported.
- This follows the family law "one AST per tier, with fragment predicates" (Python's `heapFree`/`moduleGenFree`, READ AGENTS.md). Each view's fragment is a decidable predicate over `Sv.Ast`, not a second language.

### 5.4 Procedural loops (`svgolf/design/loop/LOOP-NOTE.md`)

- **G0** becomes "loop meaning = a fold over a trip list computed from the header, no fuel, in 32-bit `int` arithmetic". That is the E meaning, so it carries no regret. Today's `forEach vs f` with `vs = intRange i0 n` already has this shape.
- **G1**, the hand proof of nested clmul for every N, should proceed now. Its thinking transfers unchanged, and its rule library becomes D3.
- **Bridge S** is R-BODY/R-LOOP restricted to one process. **Bridge L** stays dropped.
- **Mixed designs** (a loop plus an `assign`), which LOOP-NOTE left without a cheap route, get one through R-COMB: per-process equations with the loop's recurrence inside its node.

### 5.5 Hierarchy and module summaries

- **Today.** The loader flattens instances under hoisted string names, the tactics refuse instances, and ripple_fa spends 477 lines (297 code lines) deriving the flattened process list by hand (MEASURED, WP-I-NOTE).
- **Under this design.** An instance is a reference in E, and composition is D9 with R-HIER. Hier2 becomes the far side of `flatten_sound` and the source of the pinned elaboration rules.
- **WP-I route C** is the combinational special case. Build it in R-HIER's shape:
  - child summaries carry arcs at bit or field granularity;
  - names are structured `Seg` paths, so the K2 obligation that `toString` be injective on `Int` (READ `WP-I-NOTE.md:106`) disappears by constructor injectivity;
  - certificates are modular, with ranks composed lexicographically per level.
- **Instance arrays and recursive designs** follow by induction over families, using the Kami replication shape (CITED via digest).

### 5.6 Sequential logic

**Missing today:**
- `cycleStep2` never reads the clock (READ `Sem2.lean:695-708`);
- `Process2` has no negedge flop, latch or active-high async reset (READ `:222-229`);
- `SeqTask` is an untrusted sketch, and its `CounterCycle` is about 89% plumbing (MEASURED, strategies digest).

**Order of work:**
1. R-EDGE (`step_parallel`);
2. R-CYCLE with the discipline;
3. `satisfiedAt_of_cycle` (READ `SeqTask.lean:315`) restated over D6, losing σ and fuel;
4. the counter as the first public task (decided 10/30), over `obs` with pre and post samples;
5. then regfile, pipeline and transaction tasks.

Clocks become semantic objects in E now. Negedge, several clocks, gating and latches extend the `Tick` alphabet later, without changing its signature.

### 5.7 The four statement languages and the region tier

| today | where it goes |
|---|---|
| `Stmt` (M0, 5 constructors) | retire after the four M0 example theorems (counter, toggle, swap_nba, race_blk) are restated through R-CYCLE and ⊨². The five `_det` theorems must be re-proved over the new observable in any case (family §6) |
| `SStmt` (34) | structural constructors go to `Sv.Ast`; continuation states go to frames |
| `PStmt` (9) | subsumed by `Sv.Ast` |
| `Stmt2` (6) | frozen; legacy view behind R-DESIGN2 |
| region tier (Step, Slot, World, Regions, Drive, …) | **becomes E's core**. Make `runProcResidual` total (its recursion is already on fuel, READ `Slot.lean:314`), then remove the fuel entirely in favour of `step`. Retarget it from SelfCheck's sv-0.1 envelope to `Sv.Ast`. Keep its 15-region `Region` type and its driver resolution |
| `Sv.Res` | retires with Design2 and M0; E uses Core's `SemMWith`. That is the family's by-touch convergence |

Since 10-01, 74 commits touched Slot, SelfCheck or Step, against 59 that touched `Comb*` (MEASURED, audit). From the day this note is adopted, a construct lands in `Sv.Ast` and E first, never only in the timed tier or only in Design2.

---

## 6 Decide now (expensive later) versus can safely wait

| decide NOW | why it is expensive to change later |
|---|---|
| **D1. Process-atomic E, as a declared narrowing of §4.7** | It determines whether *any* comb or cycle view can be true. Every refinement theorem depends on it |
| **D2. No fuel in any definition; E is a total `step` plus a closure** | It fixes the interpreter's *type*. Family §8 step 7: "the two routes differ in the interpreter's TYPE" |
| **D3. The observation interface (Preponed and Postponed samples of declared observables) as the only thing trusted statements see** | Once leaderboard records depend on `run2` snapshots, changing the trace type re-opens every one of them (family §6) |
| **D4. An event-level causal environment, with the clocking discipline as a rely** | It is the hypothesis of R-CYCLE. Without it the cycle model does not refine E, and statements cannot express their own assumptions |
| **D5. State and names: structured `VarId` paths, array-valued state, longest-static-prefix driver slots** | 380 + 723 lines use `SvState.lookup` over string keys today (MEASURED, audit). Every lemma depends on the store type |
| **D6. Parameters bound, never substituted; families never expanded in meaning** | Ruling 1. Anything that substitutes now becomes a cap later |
| **D7. 4-state authority, 2-state view; default start policy** | Statement meaning: x-hygiene properties and X-robustness both depend on it |
| **D8. The trusted skeleton `Sat`/`Contract`, with CombTask and SeqTask as proved instances, plus the svGolf `Admissible` conjunct** | It is the trusted base; changing it invalidates records |
| **D9. One AST (`Sv.Ast`); Stmt2 frozen; the "new constructs land in E first" rule** | Every construct added to two tiers raises the reconciliation price |
| **D10. Every view carries a direction label; every view is a theorem** | Using a view in the wrong direction is silent unsoundness |
| **D11. Elaboration in Lean, with slang as a multi-point witness** | It is the largest new trusted body. Deciding late means re-validating widths across the whole estate |

| can safely WAIT | why waiting is safe |
|---|---|
| ⊨ω and liveness | the stream index already exists in `Behaves`; Kami also left liveness for later (CITED via digest) |
| multi-clock and CDC oracle details; the gated-clock lens R-GATE | the `Tick` alphabet signature is fixed now; the lenses add views, not semantics |
| the SVA frontend | assertions are kept as observation nodes now, so blocks stop being loud |
| classes, randomization, dynamic data (T3/T4) | outside the proof-facing language |
| tri-state, `inout`, strengths | driver slots and resolution exist in E's shape from the start |
| typed-record presentation of states | presentation only |
| Std.Do `mvcgen` against a bespoke SV vcgen | decided by X12 (`5d531646`): `mvcgen` works on `execBody` with no adapter, but costs 6–17× more than the `DenotesE` view-function route, so it is a niche fallback, not the library (JUDGED) |
| a fast compiled executor | if ever needed, it is a test instrument registered as a §3.4(b) debt, and no proof rides on it |
| promoting the shared contract shape into Core | wait for SV to be the second consumer (family rule) |

---

## 7 First experiments

Each experiment says what it settles and when to stop. Order: X1 first; X2–X5 in parallel with X1, since they need no new E code beyond X1's core.

| id | experiment | settles | stop rule |
|---|---|---|---|
| **X1** (do first) | **R-COMB spike** on a minimal process-atomic E-core: flat; continuous assigns plus `always_comb`; one time slot; 4-state; no fuel. Prove (a) `SlotCloses` under every schedule, and (b) the closed store is the unique CombEqs solution. Then prove it equals `combSettle2`'s result on Design2 | whether the keystone refinement is provable and at what price; the shape of `step` and `Steps`; whether comb records can be transferred | if the assign-only half does not close in its first slice, stop growing E. Freeze it to that fragment and re-plan with the maintainers. Do not let a fifth semantics stand unbridged |
| **X2** | **§4.7 granularity measurement**: add a preemptive choice policy to X1's executor. Run the comb rows of the 590 Xcelium goldens and the svGolf records; count observations that are invariant under each policy | confirms or refutes the claim that preemption breaks nearly every `always_comb` fed by another process (JUDGED prediction: it does) | if more than a small fraction of rows are preemption-invariant, reconsider a C-style census (exact where it passes) instead of a narrowing |
| **X3** | **Record transfer audit**: for the 4 accepted svGolf records (7 is the number of tasks), check that each proof exposes an `Acyclic` certificate and makes no procedural decision on x | whether v1→v2 is one theorem or a per-record re-certification | any record without a certificate is re-proved, and the failure is recorded |
| **X4** | **R-EDGE spike plus a discipline audit**: prove NBA-only edge commutation with async active-low reset. Check that every committed harness stimulus (`clockExpand`, Xcelium testbenches) satisfies `Disciplined` | whether the clocking discipline is the right rely | a row that violates it is either a race to document, or a sign the rule must change |
| **X5** | **The observation interface over run2**: implement `obs` (pre = `cycleStep2`'s `st2` (after the async-reset phase; `st1` only when no reset event fires, corrected 2026-11-02)). Prove `Computes ↔ Computes_obs`. Restate the counter SeqTask through it | that trusted statements can switch to `obs` now with zero record churn | if the pre sample cannot be exposed without changing `run2`, expose it as a new definition proved equal on outputs |
| **X6** | **Multi-point elaboration divergence**: run pyslang at several parameter points per census block against Lean's width, sign and enum computation (Probe2 pattern) | the size of the trusted elaborator's risk | if divergences are frequent, enumerate them and keep the affected facts as declared annotations until resolved |
| **X7** | **Lens cost on E-derived equations**: heartbeats per template site for ibex_alu (884 lines) and a slice of ibex_cs_registers, against today's `symExec` route | whether E-shaped proofs stay at or below about 15.7k thousand-heartbeats per site (MEASURED baseline) | if they are more than 2× worse, keep proofs on D views only and investigate before adding constructs |
| **X8** | **Arc granularity census**: on ibex_core and cv32e40p_core, count module-level combinational cycles that disappear when arcs are per bit or field instead of per port | the arc representation | if port-level arcs suffice everywhere measured, keep bit/field as an option rather than the default |
| **X9** | **`fourState_abstracts` feasibility**: check monotonicity of every pinned `LVec` operator table by kernel `decide`; list the non-monotone ones; measure how often census blocks decide on a value that could be x | whether R-X is cheap | if non-monotone decisions are common in real blocks, make ⊨² concretization the X-robustness route instead |
| **X10** | **Synthesis agreement**: Yosys netlists against E for `unique`/`priority`, self-read `always_comb` and attributes, on inputs that violate and inputs that do not | the content of `Admissible` | every split found becomes an `Admissible` clause, never a silent pick |
| **X11** | **Cold-agent usability**: an agent proves the regfile contract through (a) 4-state goals with knownness and (b) 2-state `BitVec` goals | the default presentation | the measure is lines, time and failure modes; no argument decides this |
| **X12** | **Std.Do spike**: a WP instance for `execBody`; count VCs and time on one real `always_comb` with a loop | whether loops get the shared vcgen (family §3.4) or a bespoke one | if `mvcgen` stalls, use LOOP-NOTE's rule library by hand, as ruled |

Two more measurements are needed before any new tier is priced: a census of the symbolic proof path over sv-tests, and an RB82 re-run after WP-PROC.

---

## 8 Migration from the current tree

The order is chosen so that **no proved theorem is ever at risk**. Today's tactic route keeps working, untouched, until E can carry its results. This is family §9.2 (consolidation by touch). The one exception is the keystone, which is a theorem rather than a rewrite.

- **M0. Name it (days).**
  - Write `docs/sv-kernel.md`, declaring E the authority under the 2026-11-02 ruling.
  - Register the debt rows: svGolf on run2; Design2 adequacy; statement-level fuel; `Sv.Res`; the §4.7 narrowing.
  - Adopt the rule "new constructs land in `Sv.Ast`/E first".
  - Freeze Stmt2.
- **M1. The observation interface and the X5 restatement.** Trusted statements move to `obs` with no record churn.
- **M2. `Sv.Ast` and the sv-0.3 envelope.**
  - A superset of `PDesign`, with `ofPDesign` an injection, and loops retained by default. `--retain-loops` already exists (READ, charter entry 2026-11-02).
  - The extractor's proof-path rewrites gain retain-mode twins one by one.
  - Add structured `VarId`s, array values and longest-static-prefix driver slots.
- **M3. The E core.**
  - Port Step.lean's frames and Slot.lean's region loop and driver resolution into the total `step`, process-atomic, on `SvM`.
  - Add the executor and `exec_sound`.
  - Point the Xcelium pins at E.
  - Run D views and E side by side on every row.
  - Retire `SelfCheck.exec*` only when E's per-chapter clean share meets the self-check path's (READ `docs/sv-construct-census.json`).
- **M4. The keystones, in order:**
  1. R-BODY;
  2. R-COMB (X1 grown);
  3. R-EDGE;
  4. R-CYCLE;
  5. R-DESIGN2, which transports every Design2 theorem: 241 in the Design2 tier and 1,391 in `Comb*` (MEASURED, audit), conditional on acyclicity where `Progress` is needed;
  6. R-ELAB for Lean-side elaboration.
- **M5. Views and tactics, one acceptance proof each.** Each is accepted only when a cold agent finishes a real proof through it without seeing fuel, schedules or string names. The order:
  1. loop (G1's nested clmul);
  2. cycle (the counter);
  3. array (regfile);
  4. composition (ripple_fa via a full_adder contract, then `exu`);
  5. function;
  6. 2-state.

  Throughout, `sv_structure`/`sv_equations` keep running. They read the uninstantiated `PDesign` (READ LOOP-NOTE verdict 1), which embeds into `Sv.Ast` unchanged.
- **M6. Task v2.**
  - `Sat`/`Contract` plus `Admissible`.
  - CombTask and SeqTask are proved instances.
  - Records are re-certified by theorem (per X3), never re-proved by hand.
  - Leaderboards announce one version switch.
- **M7. Retire** M0 `Stmt`, SStmt, PStmt (now subsumed) and finally Stmt2, once no record, example or harness row depends on them.

**Kept from today, never thrown away:**
- `Logic`/`LVec` and Basic.lean's pinned operator tables;
- `evalPure2`;
- CombEqs, `Acyclic`, `Terminates2.of_acyclic` and the knownness calculus;
- the Summary pattern;
- Gen2's symbolic-N lemmas;
- WP-LIN grouping;
- the guards (ClockGuard2, RangeGuard2, CombGuard2, CombAlias2) as view-hypothesis checkers;
- Hier2's pinned rules;
- the Xcelium goldens and both ledgers;
- `LeanModels.Rv` as the shared ISA spec;
- every svGolf record, through R-DESIGN2.

---

## 9 Risks, and what would change our mind

| risk | evidence and reasoning | what would change our mind |
|---|---|---|
| **The keystone stalls** (R-COMB/R-DESIGN2) and E becomes a fifth unbridged semantics | `CycleAdequacy` was stated and then parked (READ Adequacy.lean; backlog: pieces 3–4 "NOT started"). Vericert reports that refinement proofs get tedious exactly where state representations differ (CITED via digest, OOPSLA'21 §4.7). I know of no mechanized event-to-cycle precedent (JUDGED) | If X1 does not close the assign-only fragment in its first slice, ask the maintainers to revisit how the ruling is implemented: svGolf might rest on the cycle model as a *declared* authority for the synthesizable fragment, with E as a checked oracle (P's stance), recorded as a family §5.0a narrowing |
| **The maintainers decline the §4.7 narrowing** | Under literal preemption no comb view holds for an `always_comb` fed by another process (JUDGED construction) | E keeps preemption. Views then apply only to designs that pass a C-style mover census, so most RTL would get no proof route (JUDGED). X2 measures how much |
| **Elaboration in the trusted definition is too big** | LRM 11.6–11.8 was "an obstacle" for Lööw (CITED via digest). The default-point cross-check hides divergence at other N | If X6 shows frequent divergence, keep slang's results as declared, annotated trust for those facts until Lean agrees |
| **Kernel cost of E-shaped terms** | the family's twin-versus-faithful gap (READ §3.4 asterisk) | Proofs never reduce E, only D views. If X7 shows views derived from E are much heavier than `symExec`, generate equations by proof-producing symbolic execution (Silver-style, CITED via digest) |
| **Compositionality fails on real hierarchies**: combinational paths through several children; valid/ready loops; port collapsing | ibex_ex_block's shared adder; struct-bundled handshakes (JUDGED) | If X8 finds spurious cycles even at bit granularity, add per-path arcs, or flatten that level by theorem (`flatten_sound`) |
| **2-state and 4-state mismatch with silicon** | mid-run x from divide-by-zero or out-of-range reads; `if (x)` takes else | If X9 finds frequent x-decisions, state X-robustness as ⊨² concretization rather than through start policies |
| **The LRM is imprecise**: port collapsing, time-zero order, x-propagation of particular operators | each forces a declared departure | Keep declared departures registered and aged, with retirement conditions (§5.0a). Do not let "fidelity first" become an open-ended conformance programme: E covers T1+T2, and the rest refuses |
| **Agents face raw E** when a view does not apply | F's own risk | View-refusal messages name the failing hypothesis, and an agent can always restate the property more weakly. If cold agents (X11) stall on raw goals, invest in more views, not in E |
| **Time to value** | months of M2–M4 work before new svGolf tasks benefit (JUDGED) | Run X5, G1 and the SeqTask counter on the run2-backed `obs` meanwhile, as provisional; they transfer |
| **Membership testing is weak** | a permissive E could accept a wrong trace | Use equality where determinism is proved or censused; cross-check several choice policies |
| **The synthesis gap** | the score is a Yosys netlist while proofs are about the LRM | `Admissible` is trusted. If X10 finds splits a predicate cannot capture, refuse those constructs in svGolf |
| **Hyperproperties under over-approximating views** | refinement paradox | R-PRODUCT is restricted to exact views or shared children. If a needed hyperproperty requires a relational child contract, state it at E level |

---

## 10 What generalizes to the other language lanes

### 10.1 Conformance with family law: where this design conforms and where it departs

| family law | this design | verdict |
|---|---|---|
| §0.1 I: the definition is never weakened, ∀ every nondeterminism | `∀ ch` over process-atomic schedules; §4.7 mid-process preemption is narrowed | **Departs; needs a ruling** (D1) and a §5.0a row. Justification: a definition under which no ordinary RTL can be correct measures nothing, and every tool on the panel is atomic. Retirement condition: a preemptive policy in E plus a census that makes the narrowing exact per design, C-style |
| §0.1 II: definition minimal, library untrusted | E includes elaboration (by the ruling); views and tactics are untrusted, with only their theorems believed | Conforms; the size of the elaborator is a stated risk |
| §3.4: one monad; fuel is an index, never a monad layer; §8 step 7: decide fuel before the interpreter | E's micro-step runs in Core `SemMWith` (`SvM`); **no fuel index at all**; fuel only in the executor | **Conforms in spirit, departs in letter.** Justified by §3.6(1a): once continuations are data, a total step plus a closure needs no index. Direct-style lanes keep the index (CakeML FBS) |
| §3.4(b) and §8.5: a second semantics owes adequacy | every derived view carries a refinement theorem; R-DESIGN2 is owed for the legacy `run2` | Conforms. The debt for `run2` is registered now |
| §3.4: "a performance number measured on a twin is a claim about the twin" | X7 measures cost on E-derived views, not on `symExec` | Conforms |
| §3.6(1a): defunctionalize; decision, not scrutinee; the laziness law | frames as data; trip lists as data; the body as a syntactic subterm. The executor must build continuation levels lazily | Conforms |
| §6: determinism is observation-indexed; never a tier-wide conclusion | statements over `obs`; determinism a per-design theorem; the five `_det` theorems re-proved over `obs` | Conforms |
| §8 step 9: separate the spec half | trusted statements mention only `obs`, `elab` and relies | Conforms |
| §8 step 10: take the parts, never rebuild the node | `step` is structural on the top frame | Conforms |
| §9.2: consolidation by touch | M0–M7, except the keystone theorems | Conforms |
| Circuit lane: view directions; realizability; receptiveness; equation-provenance guard | every view labelled; realizability twin mandatory; receptiveness required for relational contracts; a `#equation_guard`-style check that a contract does not import the spec it proves | Adopted |
| C §3.2: no normalizing rewrite between model and oracle | the extractor contract (§4.1) | Conforms |

### 10.2 Lessons that should go back to every lane (JUDGED; each is grounded above)

1. **The authority plus direction-labelled derived views pattern.** Each view is proved once per fragment and never per program. The circuit lane already has it; SV would be the second instance. Python's monadic runner and C's canonical order are the same shape, and each should publish its edge to its authority. Proposal: move the `Exact`/`OverApprox`/`UnderApprox` vocabulary into Core.
2. **A refinement of the fuel-placement law.** Classify every non-structural recursion site into one of three kinds:
   - structural in disguise (finite trees, trip lists): remove the fuel;
   - defunctionalized concurrency or suspension (SV processes, Go goroutines, Python generators and async): a total step plus a closure, with fuel only in the executor;
   - direct-style general recursion (calls, data-dependent `while`): the §3.4 index, as CakeML does.

   SV's 126-trip cap is the measured cost of putting fuel in the wrong place.
3. **A three-way procedure for narrowing a language's latitude.** Choose one per construct and register it:
   - a census that makes a canonical choice *exact*, as C does with unspecified evaluation order;
   - the standard's own fence, as Go does with DRF-SC;
   - a declared narrowing with panel evidence, as SV does with §4.7.

   Add the third kind to §5.0a explicitly. Today the register records divergences from the oracle, not narrowings of the spec.
4. **Parameters are a ∀-dimension of the definition, like the schedule.** No cap or default point may leak into meaning. This applies to C++ templates, Ada generics, Rust const generics and Wasm memory limits.
5. **Trusted statements sit on an observation interface, not on the interpreter.** Swapping the definition then moves no statement. Python's `CallsTo` through `callFunction`'s boundary is the same idea; SV makes it explicit with sample points.
6. **An environment is a causal parameter plus a discipline predicate stated in the authority's vocabulary, and that predicate is the hypothesis of the refinement.** Python's clock trace, stdin and argv, C's I/O and Go's external channels have this shape. The discipline must sit in the statement, not hidden in the harness.
7. **One contract shape**: rely, guarantee, ghost state, dependency arcs, realizability, receptiveness, direction. The circuit lane's `compose_contracts`, SV's K-layer and Python's `@[py_spec]` call rule are three instances. Promote it to Core when SV is the second consumer.
8. **Names are structured data, never concatenated strings.** Python's `"Class.method"` and `<genexpr@n>` are strings too (READ AGENTS.md). Kami's inlining got stuck on symbolic string names (CITED via digest), and SV's WP-I hit the same `toString` injectivity obligation.
9. **Loops are folds over a decision list.** Std's `Spec.forIn_list` is the shared rule (READ toolchain `SpecLemmas.lean:802`). This applies to Python's `for` over lists and to C `for` loops with canonical headers.
10. **When the deployed or scored artifact comes from a different frontend than the proof** (Yosys netlist against slang; a C compiler's codegen against the envelope), the trusted statement needs a same-program admissibility predicate, not only loader refusals.
11. **Every tier should publish "theorems are stated over X; the adequacy edge to the definition is Y".** Python carries the same gap as SV: its theorems are over `Semantics.lean` while the runner is the monadic rebuild, and `twinAgrees` is a contingency (READ family §8.5). SV's svGolf statements over `run2` are the same kind of debt.
