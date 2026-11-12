# WP-LOOP: a fold / invariant reading for the procedural `for`

> **Status.** Design note from a read-only gate. Date 2026-11-02. Base `svgolf-prep` 8aace5f9. The newer extractor and `Param2.lean` were read from `github/master`.
> **Nothing was run**: no Lean, no `lake`, no extractor, no pyslang.
>
> Every claim is labelled:
> - **READ**: read off the source, with `file:line` (branch `svgolf-prep` unless it says `master`).
> - **MEASURED**: a number in a committed data file or in git history.
> - **JUDGED**: my estimate. All sizes, weeks and heartbeat targets are JUDGED. None is a measurement.
>
> "(digest)" marks a fact taken from a reader's summary of a file I did not re-open. Every goal state below is a hand-written mock-up in the existing `sv_equations?` conventions, not tool output.
>
> Governing ruling: PROC-NOTE.md:3-11 (decided 2026-11-02). Preserve the structure of loops. X3 (comb-SSA flattening) is withdrawn. X4 (lift to a generate family with a row array) survives only as a structure-preserving rewrite proved by induction. The direction for G2 is "tactic support for the loop itself (a fold or loop-invariant reading, the analogue of `py_vcgen`'s `inv`/`dec`), not a flatter lowering".

> **Lead's review (2026-11-02).** The note was written by a read-only workflow: four readers, three competing designs, one adversarial judge, one synthesizer. The lead read all of it.
>
> *Checked against the source by the lead:* the 126-trip cap (`forValues2`: the outer match spends one unit of the 128, `go` spends one per trip and one on the exit test), the `.unsupported` arm of `instStmt2`, `Expr2.joinIte`, and the Xcelium gap (`harness/sv/xcelium_golden.json` has 579 rows and none named `symbolic_`, on prep and on master; `cases2.json` has 16 `symbolic_` rows, among them `symbolic_parameter_for`).
>
> *Not checked:* every other READ and "(digest)" citation. No Lean was run. That a correct design's `Statement` is false at N >= 127 is derived by reading, not by a run; it is a loud under-approximation, not an unsoundness.
>
> *Corrections since the note was written:*
> 1. **Gate 4c finished while this was drafted** (`wpb2g4c`, `f8c0d1ea`, not merged). `{ {K{1'b0}}, x }` is now read in the `assign` chain, so after the merge the `assign aw` of `proc_shift_xor.sv` is no longer refused for replication. Section 2.4's sentence on `aw` and D4(ii) are therefore out of date, and the two-process objection is **stronger** than D4 says: the shift-xor spelling people actually write becomes a live mixed design. The exemplar order (nested first) stands; the fallback decision in section 4.3 weighs more.
> 2. **The Xcelium rows have an owner.** The note leaves this open. The lead can run them through the same route gate 4c used, so stop rule S1 waits on nobody else.
> 3. **Read "weeks" as relative sizes.** PROC-NOTE priced WP-PROC G1 at about 4.5 working days and it landed the same day. The estimates in this note are JUDGED in the same way.
> 4. **The Yosys miter is not needed for this route.** Bridge L is a Lean theorem, and no lowering sits outside Lean. The miter remains only for an extractor rewrite that is kept and is not proved.

> **RE-SCOPING (decided 2026-11-02), which overrides the rest of this note where they differ.** "We are trying to make it easy to prove things about programs in Lean, not build a classical normalization-to-SAT pipeline. Some things might be easy for an agent to do on its own in Lean, so we don't need scaffold for that, but other things are tedious, and we can automate them. We don't need anything super smart, since the agent doing the Lean proof has the smarts."
>
> *Keep, because it is tedious, mechanical, or impossible to do from a proof file:* G0 (a loop needs a meaning for every N); the rule library of G1 (`rows`, `block_run_iff`, frame, totality, the guard over a trip family); the bridge to `Statement` (G2); one generic-trip symbolic step that yields a plain equation; automatic discharge of frame, knownness and range goals where `omega` or `simp` closes them, with the rest left as ordinary goals.
>
> *Drop for now, because the agent can do it:* the default fold invariant and the derived fold; the `sv_loop (inv := …)` clause, its tags and its `dec`-free syntax (the agent writes `induction k`); bit-separability detection and the "masked form" printer; closed forms and named shapes of any kind, including printer-side ones (D5 is narrowed to: no shape work at all; the `clmul` `bx` lemmas stay in the proof unless proofs keep repeating them).
>
> *G3 is no longer a fixed 1500-line gate.* The hand proof of G1 is now the driver of the plan: record where it was tedious, automate only that, and size G3 from that list. Stop rule S3 stands. The acceptance measure changes from "lines remaining" to "a cold agent finishes the proof without touching fuel, block plumbing or settle theory". Sections 4.2, 4.4 and 5 describe more than is now planned; they are kept as the record of the options.

> **OUTSIDE REVIEW AND FIRST MEASUREMENTS (2026-11-02), which also override the rest of this note.** An outside review raised four blockers and several smaller points. Each was checked against the source, and the one that could be run was run: `spike0/` holds three parameter-bound loops, `Probe.lean` and its log (`lake env lean`, interpreter, at concrete N).
>
> | loop | `lowerComb` | cost of `lowerComb` |
> |---|---|---|
> | `p = 0; for i: p = p ^ a[i]` | **some**, N = 1 to 126 | about 1 ms; at N = 127 and 200 the design is `.unsupported` (the cap of section 1, now observed) |
> | `p = '0; for i: if (b[i]) p = p ^ a` | **some**, N = 1 to 14 | 1, 3, 10, 37 ms at N = 8, 10, 12, 14: about x1.9 per extra trip |
> | `p = '0; for i, j: p[i+j] = p[i+j] ^ (a[i] & b[j])` | **some**, N = 1 to 4 | 34 ms at N = 3, **88,111 ms at N = 4**; N = 5 did not finish in the time left |
>
> Verdicts:
> 1. *"A transparent `forEach` erases loop identity": no.* The recognizers read the uninstantiated `PStmt` (`treeStmt?`, `siteOfP?`, `PDesign.summaryP`), and `X.sem N` unfolds to `PDesign.instantiateGD2 X.pdesign [N]`, so the tactic has `pd`, where `.forLoop` is a constructor. No `LoopForest` or `Proc2Inst` is needed. D7 was badly worded and is fixed below.
> 2. *"Bridge L cannot work because `lowerComb` rejects the self-read": refuted by the table.* `symExec` substitutes reads of written windows, so an initialized accumulator passes `selfReadFree`. The review's conclusion stands for another reason: the term is exponential at a concrete point, so nothing may ever evaluate `lowerComb` on a loop, including at a fixed literal bound. **Bridge S is now tried first** for one `always_comb` process, since it never builds that term. Bridge L stays the candidate for mixed designs and may only be used by induction at a symbolic trip count.
> 3. *"Unbounded `Int` against SV `int`": real, not loop-specific, not a blocker.* It is the recorded restriction of genvars (`PDesign.int32Agrees`' docstring) and applies to every for-every-N statement. Changing it would change trusted statements. It stays recorded, and G0 confirms that `int32Agrees` sees a loop header.
> 4. *"`.block (map)` still unrolls": accepted as a qualification.* A proof with a free N never expands the list; execution at a concrete point runs trip by trip. A fixed-size design must also go through the generic lemma with the trip count abstracted. "Never unrolled" below means proofs, not simulation.
> 5. *Fuel: rejected.* A per-trip threshold composes over a finite list by `fuelMono2`, and `Stmt2.fuelB` is already a static bound. A certified `loopFuel?` adds nothing: a bad estimate is already a loud `.timeout`, and the definition sits in the trusted cone, so it stays simple.
> 6. *Family guard: partly accepted.* It is a lemma about the existing `combGuardProc`, not a new admission path. The negative cases (future read, read before init) join G1's acceptance.
> 7. *Scope, corpus, measurements: accepted.* v1 is blocking `always_comb` only. Retained-versus-unrolled stays a permanent regression (`proc_loop_forms_retained` is on master). Record heartbeats, kernel time and `.olean` size against N.
> 8. *Gate order: accepted, in the re-scoped form.* The first deliverable is one compiled, tactic-free vertical slice: nested `clmul`, one process, for every N, through Bridge S. It comes before any library is sized.
> 9. *Not adopted, under the re-scoping rule until a hand proof shows the need:* a `view` projection layer, a canonical Nat/Int index context, per-write footprint summaries. Knownness goals stay visible as ordinary goals, as the review asks.

> **DIRECTION (decided 2026-11-02), the latest word and overriding everything below: no lowering for loops.** After the table above: "that's another reason we don't want to lower this stuff. The design goal should be to keep things as close to the original SV as possible, but define the semantics so they are easy to work with in Lean."
>
> So **Bridge L is dropped**, not deferred: no route goes through `lowerComb` on a loop. A loop proof reaches `Statement` by a theorem about the process as written (Bridge S), and `PStmt.forLoop` stays what proofs and tactics read. Open consequences, for the maintainers: (1) mixed designs (a loop plus an `assign`, such as the textbook shift-xor `clmul`) lose their cheap route, so they need a process-level theory or wait; (2) with "easy to work with in Lean" as the criterion, the proposal is that the loop's meaning be a fold over a trip list computed from the header, with no fuel at all, in place of the `loopFuel` of D1.

> **G1 RESULT (WS3, agent L, 2026-11-02), which updates the plan below; details and the sized plan in §9.**
> The nested procedural `clmul` (`tests/clmul/attacks/proc_nested_for.sv`, loaded with `load_sv`) satisfies
> `SvGolf.Tasks.Clmul.Statement` for every `N`, tactic-free, through Bridge S, with no lowering and nothing unrolled
> (`svgolf/design/loop/g1/ClmulNested.lean`, `statement`; label *provisional over `run2`*). MEASURED: 394 design-specific
> code lines against the 206 of the generate reference; 38 to 55 of them are loop thinking, about 300 are plumbing a
> tactic or a library lemma can produce. G0 changed shape: the loop's meaning is a `TripSchema` agreeing with the header in 32-bit `int`
> arithmetic, computed with no fuel (`headerSchema`); the `loopFuel` of D1 was not built (master's `c64ebdac` already
> derives the legacy fuel from the header). Bridge L stays dropped; Bridge S was built generically (`SingleComb`).

---

## 0. Recommendation on one page

**The answer.** Keep the loop a loop in Lean. At a parameter point it is `Stmt2.forEach vs f`: one trip list `vs` and one body function `f : Int → Stmt2`. For a symbolic `N` the list is `intRange i0 n` and `vs.map f` is never expanded. The proof only ever opens `f v` for a generic `v`.

Prove once what a run of a `forEach` is. It is a family of states `rows k`, the state before trip `k`, with `rows (k+1)` obtained from `rows k` by the body at trip `k`. The golfer sees this as **a recurrence over the trip index**, printed in the existing `eq_<sig>_<site>` style. A derived fold is available whenever the step is a function of `(k, carried window)` only.

The golfer proves an invariant by induction on `k`, with no unrolling. For a Spec-shaped loop the default invariant is the fold itself, so no clause is needed. A clause `sv_loop (inv := fun k P => …)` refines it. That is `py_vcgen`'s `inv` without `dec`, because the trip list is finite.

The bridge from the loop process to the trusted `Statement` is the one thing nobody has priced. Two candidates exist. A 3–5 day spike decides between them (§4.3).

**Build, in this order.**

| gate | what | JUDGED |
|---|---|---|
| G0 | The loop means something **for every N**: a header-derived fuel replaces the hard-wired 128 at `Param2.lean:1264`, plus fuel monotonicity, symbolic trip lemmas (twins of `Gen2.lean:377/406`), the `Stmt2.forEach` def, and 12 Xcelium rows. This is a semantics change and must be recorded. | 4–5 days |
| G1 | `LeanModels/Sv/Loop2.lean` (a new module that nothing imports): `Realizes`, `block_run_iff`, `execForEach_of_invariant`, a guard lemma for a trip family, and a totality lemma. Acceptance is a **hand-proved ∀N theorem for the nested clmul loop** (`tests/clmul/attacks/proc_nested_for.sv`). This is the experiment that prices the golfer's proof. | 1.5–2 weeks |
| G2 | The bridge to `Statement`, decided by a pre-registered spike run in parallel with G1: symbolic-N `lowerComb`, else a single-process snapshot theory, else the heavy `FunProc` generalisation. | spike 3–5 days, then 1–3 weeks |
| G3 | The tactic. A sibling "loop route" inside `sv_structure`/`sv_equations`/`sv_cover` prints the recurrence from one `Stmt2.symExec` of a generic trip. `sv_loop (inv := …)` is sugar over it. | ~3 weeks |

Then: G4 (descending, `<=`, `+= c`, several carried signals, temporaries), G5 (extractor, fourstate and shift vocabulary, owned elsewhere and parallel), and G6 (window-writing loops: ripple add, restoring division).

**Price.** 6–9 weeks to the first end-to-end loop task, which is the nested clmul (JUDGED, wide error bars). The first 2–2.5 weeks (G0, G1) are an experiment with stop rules, not a commitment (§5).

Without G5 no loop design is *scoreable*, however good the Lean side is. The fourstate stage refuses procedural loop counters today (§1, §6).

**Do not build.**
1. A `Stmt2.forLoop` constructor or a run-time counter slot (the `SelfCheck.execForLoop` route). It touches every walker over `Stmt2` and over-refuses the self-read guard (§3).
2. Any flattening of a loop (X3), and the extractor-side ghost-row lift (X4). Rows-as-states needs neither.
3. A shape-recognizer gate as the *only* mechanism (design C). A body one operator from a shape would get a refusal. Closed forms may exist only as printer-side lemmas.
4. `FunProc` / `AcyclicF` (design B's L2) before the spike has failed.
5. Evaluation of `lowerComb` on a concrete loop design at large N. Its right-hand side is a DAG whose tree size doubles per conditional trip (JUDGED, from `Expr2.joinIte`, `Comb2Proc.lean:357`).

**How it honours the ruling.**
- The loop is never unrolled for a proof with a free N (execution at a concrete point does run trip by trip). Opening `f v` at a generic `v` is the only thing a proof does.
- Literal and parameter bounds go through one path.
- The printed object is the recurrence or fold over the loop's own quantifier, which is the `inv` reading the ruling asks for.
- No lowering is added, so there is nothing for a Yosys miter to guard.
- The unrolled `run2` meaning is kept as a theorem (`block_run_iff`), not as a second semantics.

---

## 1. What exists today (READ unless marked)

**The loop node and where it dies.**
- `PStmt.forLoop (iterator) (init condition step : PExpr) (body)`: `Param.lean:446`. The M0 path refuses it at `Param.lean:1683`.
- `Ingest2.lean:379` parses envelope kind `"For"` into it.
- `instStmt2`'s arm is `Param2.lean:1263-1268` (master `:1289`). It calls `forValues2 … 128` and builds `.block (values.map fun i => instStmt2 (env.bindVal iterator i) elems body).toArray`.
- `forValues2` is `Param2.lean:1221` (master `:1247`). Master adds `procStepDelta2` (`:1223`: `i++`, `i--`, `i += c`, `i -= c`, positive amounts only). The branch differs from master in `LeanModels/Sv` only by `Param2.lean` (MEASURED: `git diff --stat`, no other `LeanModels/Sv` file listed). Merge master's `Param2.lean` first, so the arm is edited once.
- **The cap.**
  - Fuel 128 is spent once by the `fuel+1` match and once per trip. The exit test needs one more unit.
  - So a loop is decided only for ≤126 trips. At ≥127 trips `go` hits fuel 0, returns `.timeout`, and the arm answers `.unsupported "ForLoopStatement"`.
  - The process is loud, `Terminates2` fails, and a correct design has a **false** `Statement` at that N.
- The iterator is never an `SvState` slot. `env.bindVal` makes it a constant, so every `b[i]` in the body is a constant slice after instantiation.

**`Stmt2` has no loop.**
- `inductive Stmt2` is at `Sem2.lean:198`, with six constructors.
- `execStmts2` (`Sem2.lean:524-532`) hands the decremented fuel to the cell and to the tail: one fuel unit per cell, so fuel is linear in the trip count.
- `Runs2` is ∃-fuel (`Spec2.lean:124`), so linear fuel is harmless.

**The self-read guard is part of `name.sem N`.**
- `instProcess2` wraps an `always_comb` body: `combGuardProc (fun n => env.widths.lookup n) (instStmt2 …)` (`Param2.lean:1311`, master `:1337`).
- Its design premise is "Because the body has no loops, every path through a point is a prefix reaching the point followed by a suffix leaving it" (`CombGuard2.lean`, docstring).
- Definitions: `combViol` `:331`, `listCombViol` `:353`, `readsViol` `:153`, `combGuardProc` `:396`.
- `A` for a statement is the may-write set of the whole tail.
- The docstring says that at a symbolic width the walk simplifies when reads and may-writes are on different signals, and that "a read of a signal that is also written later needs the bit arithmetic of `BWin.subAll`". For the accumulator the read of `p` lies inside `M` after `p = '0`, so it passes.
- The soundness theorems `execStmt2_idem_of_admits` (`CombGuard2Sound.lean:1355`) and `runCombProcess2_alwaysComb_idem_of_admits` (`:1385`) are generic in the body.

**The sv_comb chain** (`Comb*.lean`).
- Its `always_comb` route is `Stmt2.symExec` (`Comb2Proc.lean:484`), `Design2.lowerComb` (`:634`), `Runs2.lowerComb_iff` (`:2679`), `ProcFixpoint` (`:2737`), `procFixpoint_iff_combEqs` (`:2745`) and `Terminates2.of_lowerComb_single` (`:2980`).
- `SymState := List (Win × Expr2)` (`:267`).
- `joinIte G A B = if A.same B then A else .ternary G A B` (`:357`). `Expr2.splice` (`:315`) copies `E0` twice. Both copy the previous accumulator expression into two places, so a conditional read-modify-write doubles the tree per trip (JUDGED from the definitions; not measured).
- `selfReadFree` (`:611`) is required only by `lowerComb`.
- `symExec_sound` (`:1835`) has hypotheses `symExec = some S'`, `SymOk`, `SymRel` and the run. It does **not** mention `selfReadFree`.
- `symExec_total` (`:1997`) needs `symExec = some S'`: existence of the symbolic state is a hypothesis.
- The recognizers refuse the loop: `CombProc.lean:1182` ("a parameter-dependent loop: outside the supported fragment").
- A shift amount must be a signal access or a constant (`CombView.lean:752`, `shOpdRd?`). A genvar as shift amount is gate 4b, not merged (`fdiv-param/H3-NOTE.md` p04).
- `PStmt.forLoop` arms already exist in `RangeGuard2.lean:144/295` (digest).

**Symbolic-N precedent for generate loops.**
- `genvarSeq_ascending_of` is `Gen2.lean:377`. `GenItem.expand2_genFor_ascending(_of)` is `:406`. Both are in the style "bound characterised by `c = 0 ↔ N ≤ i`, fuel exceeds the trip count, result is `intRange i0 (N - i0).toNat`".
- `PDesign.surfaceFuel` is `Param.lean:2262`.
- No procedural twin exists. Only `Param2.lean` mentions `forValues2` (grep).

**Extractor** (master `extractors/sv/extract.py`).
- `_sym_for_values` `:21392` unrolls literal-bound loops into a nested `Block` tagged `symbolic_for_unrolled`, with a cap `len(values) >= 128` at `:21435` and 32-bit value checks.
- `_sym_for_parameter_shape` `:21528` retains a `For` for parameter-constant bounds (`symbolic_for_parameter`, `:21590`). The dispatch is at `:21630-21678`.
- So Lean sees only parameter-bound loops, and no literal-bound loop.

**Checker.**
- `svgolf/score/fourstate.py` rule (d) treats a procedural loop counter as a run-time index judged by **type** range. Its text says "ls-sv does not load procedural loops today, and a PR that admits them should teach this rule loop bounds".
- The clmul README states that none of the nine loop-based multiplier cores gets past `fourstate`.
- Pinned Yosys 0.53 cannot read `return`/`break`/`while`/`foreach` in `always_comb`, so such designs cannot be scored (SURVEY.md:27, digest).

**Evidence gap (MEASURED).**
- `harness/sv/xcelium_golden.json` has 579 rows.
- 0 rows have a name containing `"symbolic_`.
- Literal-loop rows (`proc_loop_forms`, `proc_loop_forms2`, `proc_loop_forms_local`, `wl_rowloop_n1…n8`) are present.
- The charters of the retained-loop commits (b755094e, 31955b43) cite Icarus at N=3 only (digest).
- So the semantics of retained loops is **not yet Xcelium-pinned**.

**The clmul reference** (`svgolf/tasks/clmul/reference/clmul_n.lean`, 284 lines).
- It proves the generate-for AND/XOR array for every N. A row invariant by induction (`view_row` `:153`) and a collapse of the Spec's double sum (`bx_pair` `:88`, `coeff_eq` `:81`) account for its arithmetic (lines 46–209).
- The Spec is a nested `foldl` over `List.range N` (`tasks/clmul/Spec.lean:48`, `coeff`).
- `inRange N := 1 ≤ N` (`Spec.lean:54`).

**Task zoo.** `add`, `aes_sbox`, `clmul`, `fdiv16`, `fdivp`, `mul` (`ls svgolf/tasks`). `mul` bans run-time `+ - * / % **`, so its loops would be bitwise (`Spec.lean` header). No popcount task exists.

**Python lane.** `py_vcgen`'s rules (`VC2.lean`: `execWhile_of_invariant` 124-207, `execFor_of_invariant` 301-379) and clause discipline (`VCTactic.lean:36-55`) are the template. The whole proof layer carries a "LEGACY … deleted when re-founded" header since dc132410 (digest). Take the rule shape, not the code. The 3261-line walker does not port.

---

## 2. Requirements

**2.1 The ruling.** See the banner. In practice:
- (R1) A proof about a loop must be able to use a bound that is a parameter. Unrolling is impossible for a claim that holds for every N.
- (R2) A loop of size 100 must not be a 100-fold mess for the prover or for `sv_equations`.
- (R3) Keep things as high level as possible and preserve as much structure as possible.

**2.2 What a loop proof must be able to say**, for every `N ≥ 1`:
1. The process terminates and its settled snapshot satisfies the trusted function (`CombTask.Statement`, `svgolf/SvGolf/Comb.lean:113`).
2. The self-read guard admits the body (it is inside `name.sem N`).
3. Every window read or written in any trip is in range. An out-of-range read is x and an out-of-range write is dropped (`Sem2.lean:90-98`, digest), so an unproved window is an x-laundering channel.
4. Knownness: an x condition takes the else branch (`condTrue`, `Basic.lean:533`, digest), and arithmetic is all-or-nothing under x. Every invariant must carry knownness.

**2.3 Census** (MEASURED by the census reader from `proc/scan_survey.json`; I did not re-run it).
- 215 files were scanned; 63 entries contain a procedural `for`; 296 loops, 286 of them counted (PROC-NOTE.md "Loop census", which I read).
- 184 of the 296 loop nodes are two LFSR/CRC elaboration-time generators. **Rank by entries, not nodes.**
- 36 entries are comb-style, break/return/while-free and counted (57% of 63). Of those 36: 15 write indexed windows without `if`, 10 write them under `if`, and 11 write only whole variables (6 folds, 5 find-first).
- 8 of the 36 keep their loops only inside functions. 15 of the 63 carry a `break`/`return`/`while` somewhere.
- Bounds, ascending by one: 269 of 296 loops, in 56 entries. 21 are downto.
- The iterator is declared outside the header (`integer i;`) in 57 of 112 non-LFSR loops.
- Per-shape counts are PROXIES (statement-kind counts MEASURED, shape reading JUDGED). The scan cannot separate nested from sequential loops.

**2.4 Exemplars the design must handle.**
- clmul, three spellings.
  - Shift-xor: `p = '0; for i if (b[i]) p = p ^ (aw << i)` (`tests/clmul/attacks/proc_shift_xor.sv`). It is a **two-process** design: `assign aw = {{(N-1){1'b0}}, a}` plus the loop. The `aw` assign is read since gate 4c. What remains is the shift-by-trip vocabulary and the two-process bridge.
  - Nested scatter: `p[i+j] = p[i+j] ^ (a[i] & b[j])` (`proc_nested_for.sv`). It is single-process, affine only, and has the Spec's own nested-fold shape.
  - The generate form already proved.
- Arithmetic accumulator, popcount `c = c + a[i]`. It is a shape exemplar; no popcount task exists.
- Ripple adder as a procedural carry chain with a window (`add_proc_m.sv` is the generate form, proved).
- Restoring division, 13 steps downto (`fdiv-param/h2/s1_for_always.sv`).
- Find-first by override.

**2.5 Constraints.**
- `fourstate` rule (d) must learn loop bounds (§6).
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.
- The trusted statement files (`svgolf/tasks/*/Spec.lean`, `svgolf/SvGolf/Task.lean`) must not need to change.
- The proc-chain simp lists are tight on heartbeats. `lp_correct` is at 199,433k of 200,000k and `add_mux_correct` at 186,550k (MEASURED, G25-NOTE, digest). Never add names to them without measuring.

---

## 3. The competing designs, the judge's scores, and my decisions

**Three designs were drafted.**
- **A (WP-LOOP)**: the loop is an executed node `Stmt2.forEach vs f`. An invariant rule `execForEach_of_invariant` backs a tactic `sv_loop (inv := …)`. The default invariant is the fold.
- **B (rows)**: the loop is a recurrence `rows (k+1) = step_k (rows k)`, proved once by `block_run_iff`. The tool prints init/step/frame/exit/known and the golfer does the induction. It needs a settle-theory generalisation, `FunProc`.
- **C (shapes)**: a closed library of six proved loop shapes. A recognized loop is lowered to one assign and enters the existing chain as a site.

| design | soundness | structure kept | coverage | deliverability | golfer / agent experience | JUDGED cost |
|---|---|---|---|---|---|---|
| A | 4 | 4.5 | 3.5 | 3 | 4 | 8–9 weeks |
| B | 4.5 | 4 | 4 | 2 | 3.5 | ~8 weeks |
| C | 4 | 3 | 2.5 | 2.5 | 3 | 10–14 weeks |
| hybrid (judge) | | | | | | 6–8 weeks |

**Flaws the judge found.** I checked each against the source.
- **A.**
  - The Statement bridge is a one-process theory, and A's own clmul example silently rewrites the source to avoid `assign aw`.
  - The "non-affine iterator uses are fine" claim holds at the `Stmt2` level only. The *printed* equation needs a shift-by-trip vocabulary (`CombView.lean:752`).
  - Totality of the loop block on every shaped state was not priced.
- **B.**
  - The critical path is `FunProc`/`AcyclicF`, whose key congruence lemma is *not* what `execStmt2_idem_of_admits` proves. It is a new theorem in the style of `CombGuard2Sound.sim`, JUDGED at 400–600 lines and unverified.
  - It rejects `lowerComb` because the term is exponential. That matters only if something traverses the term, and a proof by induction does not.
  - The golfer's payoff is plumbing removal (View, five `sv_bridge` fields, boundary splits), not the spec collapse.
- **C.**
  - Closed world, with a variant matrix per shape. Reach is unmeasured, since the census keeps only statement-kind counts.
  - The `lowers` field demands a syntactic `Expr2` equality. READ: `Expr2.same` matches on the *second* argument's constructor, so it is stuck when the previous accumulator is opaque. `Expr2.splice` (`:315`) copies `E0` twice, so the scatter term is tree-exponential.
  - It edits the shared `siteOfP?`/`siteOfP?_cases` while `lp_correct` sits at the heartbeat limit.

**Where I decide differently from a design, or from the judge, and why.**

| # | decision | why |
|---|---|---|
| D1 | **Fuel** comes from a header-derived trip estimate with fallback 128: `loopFuel env it init cond step = 128 + est`. The header decode takes `it < e`, `<=`, `>`, `>=`; `est = |evalInt e − i0| / |δ| + 2`. It is **not** the quadratic `surfaceFuel`-style bound that B and C use. | A quadratic in `Σ|vals|` fails for a small N with a large *literal* offset (`for (i = -1000; …)`), where the design would turn loud and a ∀N claim would be false. The estimate is exact for canonical headers, and a wrong estimate is only ever a loud `.timeout`, never a wrong value. If the decode lemma proves painful, the quadratic form is the fallback. Either way `forValues2_fuel_mono` makes decided loops keep their meaning, and `int32Agrees` (`Param2.lean:1441`) stays true. |
| D2 | **Primary printed object is the step recurrence** (B). The **fold** (A's default invariant) is a library corollary, and a per-bit fold is printed only when the step is bit-separable. | A's "detect bit-separability" is an optimisation, not a foundation. Word-level steps (popcount, mul) are not separable, and the recurrence covers them. |
| D3 | **Rows are `SvState`s**: the concrete states of the block run from the settled snapshot (B). Not ghost row signals (X4), not shapes. | Every existing lemma about `st` (`boolAt`, `KnownBit`, shape) applies unchanged. No projection theorem is needed, and nesting is `rows_L2 k l`, not a 3-D packed array. |
| D4 | **The bridge is decided by a spike**, not assumed (the judge's hybrid). I add two facts. (i) The first exemplar, nested clmul, is single-process, so the single-process fallback suffices for it and the spike is not on the critical path for v1 if it fails. (ii) The shift-xor attack file also needs `replication`, which the chain refuses anyway, so "mixed design" is a weaker objection to A than the judge states. It is still real for any two-process design. | Pricing before building. |
| D5 | **No recognizer gate** (C) as the only mechanism. Shapes survive only as printer-side lemmas, starting with the fold calculus (`bx`, `bx_succ`, `bx_pair`, about 40 lines in `clmul_n.lean:46-133`) moved to CombLib. | The ruling asks for a reading of loops in general. Moving the fold calculus out of every clmul solution is a certain win, independent of loops. |
| D6 | `Stmt2.forEach` is a **plain def over `.block`**, not a constructor (A and the judge agree). | A constructor touches Sem2, CombGuard2, ClockGuard2, CombAlias2/Sound, Hier2, Probe2, Comb2Proc, `fuelMono2`, `symExec_sound/total`, CombGuard2Sound and breaks the guard's "no loops" premise (digest). The def gives printers and simp lemmas a head symbol. |
| D7 | **Tactic names**: the loop route is a sibling inside the existing `sv_structure`/`sv_equations`/`sv_cover`, selected on the uninstantiated `PStmt` (the body contains `.forLoop`). `sv_loop` is sugar. No new `sv_loop_task`. | The golfer learns one flow. Loop-free designs must stay byte-identical (the 24 dumps, `tools/check_sv_chain.sh --list`, G25-NOTE, digest). |
| D8 | **Xcelium rows before the N ≥ 127 widening is merged** (judge). | A divergence could force a change in a trusted definition. |
| D9 | **Literal-bound loops are retained too** (all designs want it), but behind an extractor flag until the loop route lands. | Retention could regress designs whose unrolled multi-window bodies the chain accepts today (JUDGED; unverified). |
| D10 | `FunProc` is demoted to a fallback. | See B's flaw. |

---

## 4. The recommended design

### 4.1 Semantics: literal and parameter bounds, one path

**The edit** (one arm, `Param2.lean:1263-1268` after merging master's `procStepDelta2`):

```lean
-- proposed; none of these names exist in the tree
def Stmt2.forEach (vs : List Int) (f : Int → Stmt2) : Stmt2 := .block (vs.map f).toArray
def loopFuel (env : IEnv) (it : String) (init cond step : PExpr) : Nat := …   -- 128 + header estimate, UNTRUSTED over-estimate
-- instStmt2:  | .forLoop it init cond step body =>
--   match forValues2 env it init cond step (loopFuel env it init cond step) with
--   | .ok vs   => Stmt2.forEach vs (fun v => instStmt2 (env.bindVal it v) elems body)
--   | … unsupported / timeout arms unchanged
```

`forValues2` itself, the trusted definition, is unchanged. Its pinned refusals stay loud: non-progress headers (`!=`, wrong direction, a step that is not positive, via `procStepDelta2`).

**Lemmas** (new module; nothing existing imports it):
- `forValues2_fuel_mono`: if `forValues2 … F = .ok vs` then it is `.ok vs` at every `F' ≥ F`. Every loop the tree decides today keeps exactly its meaning. Only the ≥127-trip region changes, from loud to decided.
- `forValues2_asc` (and the `<=`, descending, `+= c` twins): for a header whose bound is characterised as in `genvarSeq_ascending_of` (`Gen2.lean:377`) and with `loopFuel ≥ n + 2`, the result is `.ok (intRange i0 (N - i0).toNat)` at a *free* `N`. Their hypotheses are discharged by `simp` exactly as for generates. `forValues2.go` is its own function, so the 15-line induction is re-proved, not reused.
- `instStmt2_forLoop_trip`: at free `N` the instantiated statement is `Stmt2.forEach (intRange i0 n) f`. This is the handle the proof layer needs.

**Soundness bridge to the unrolled `run2`: by definition, not by a second semantics.** `Stmt2.forEach vs f` *is* the block `execStmts2` already folds, one fuel unit per cell. The bridge theorem holds for every trip list, hence for a literal point, a parameter point and a symbolic N:

```lean
-- proposed
structure Realizes (f : Int → Stmt2) (trip : Nat → Int) (n : Nat) (s0 : SvState) (rows : Nat → SvState) : Prop where
  zero : rows 0 = s0
  step : ∀ k, k < n → ∃ F, ∀ g, F ≤ g → execStmt2 g (rows k) [] (f (trip k)) = .ok (rows (k+1), [])

theorem block_run_iff (vs : List Int) :
  (∃ F, ∀ g, F ≤ g → execStmt2 g s0 [] (.block (vs.map f).toArray) = .ok (s', [])) ↔
  ∃ rows, Realizes f (fun k => vs.getD k 0) vs.length s0 rows ∧ rows vs.length = s'
```

The proof is list induction with threshold fuel splicing by `fuelMono2` (`Mono2.lean:138`, digest). Acceptance includes a kernel `#guard` on the literal loops of `proc_loop_forms*`, comparing `run2` with the fold of the step. The NBA queue is `[]` in an `always_comb` body (`symExec` returns `none` on `nbaAssign`). v1 covers blocking assignments in `always_comb` only; `always_ff` and nonblocking assignments are a later extension with their own theorem and rows.

**Extractor retention.** For `block_run_iff` to matter for literal loops, the extractor must stop unrolling them (§6). Lean then gives a retained literal loop the same meaning as the unrolled block (`block_run_iff` at a concrete list). The retained-versus-unrolled equality is also a *differential* obligation, because the extractor is Python.

**4-state.**
- The iterator is a constant in the model, never x/z, and has no slot.
- Body `if`s follow `condTrue`, so the invariant carries knownness (tactic-owned, below).
- `inRange` becomes a `∀k<n` obligation closed by `omega`, as the existing generate obligations are.

**Recorded restriction (not fixed).** The model's iterator is an unbounded `Int`, while the hardware's is a signed 32-bit `int`. A header `i <= N` at `N = 2^31-1` never terminates in a simulator but terminates in the model. This is the same gap as generate genvars, and the statement quantifies over `N ≥ 1` with no upper bound (`Spec.lean:54`). Bounding it inside `forValues2` would make `sem N` loud for `N ≥ 2^31` and falsify the unbounded `inRange`. Leave it. The extractor already enforces 32-bit on literal values (`extract.py:21435`), and the checker can bound `N` at the scoring point.

### 4.2 The loop rule and its mapping to `py_vcgen`

New module `LeanModels/Sv/Loop2.lean`. It imports Gen2; nothing imports it.

- `Rows.induct : P 0 → (∀ k, k < n → P k → P (k+1)) → P n` (core lacks `Nat.le_induction`).
- `execForEach_of_invariant`: the `execWhile_total_of_invariant` twin (`Surface.lean:334`, digest), threshold form, **no `dec`** because the trip list is finite and termination is structural. The Python `for` rule `execFor_of_invariant` (`VC2.lean:301`) also has no measure and relies on the iterable being captured once. That is exactly what `forValues2` does.
- `Rows.frame`, `Rows.shaped` (shape and width preserved), `Rows.foldl` (fold corollary), `Rows.collapse` (independent iterations collapse to a pointwise equation, the generate-family shape).
- **A totality lemma**: each trip body is total on shaped states when its static windows are in range. The judge noted that A's price omitted this, because `Terminates2` needs the run to succeed on every shaped state.
- **A guard lemma over a trip family**: if every read of trip `k` lies in `M0 ∪ ⋃_{j<k} mustW(f j)` or misses `⋃_{j≥k} mayW(f j) ∪ A0`, then `combViol` of the forEach block is `none`. The windows are affine in `j`, so this is Presburger and `omega` closes it. It is required of *every* design, because `combGuardProc` runs inside `name.sem N` and no existing tactic decides it at a symbolic length.
  - The accumulator passes because `p = '0` puts all of `p` into `M0`.
  - A ripple chain passes because trip `k-1` must-wrote `c[k]`.
  - A body-level run-time index stays refused (`Lhs2.mayW .index` is the whole signal and `mustW` is empty, `CombGuard2.lean:220,237`, digest). The iterator itself is a constant slice after `bindVal`, so `b[i]` passes. This is why the loop is deliberately *not* given a hidden counter slot.

**Mapping to `py_vcgen`.**

| `py_vcgen` | WP-LOOP |
|---|---|
| `(inv := fun (total i : Int) => …)`, binders are the loop-carried Python names | `(inv := fun (k : Nat) (P : Nat → Bool) => …)`: `k` = completed trips, then each carried signal (assigned in the loop, defined before it) as a bit function, or as a `Nat` for an arithmetic step |
| `(dec := …)` | none |
| i-th clause pair ↔ i-th `while` in source order | i-th clause ↔ i-th loop, outermost first |
| unassigned variables stay pinned (frame is free) | uncarried signals: **the frame is tactic-owned** |
| `Inv` over states the interpreter really visits | `Inv k (rows k)` over the concrete states of the block run |
| residual tags `init` `preserve` `dec` `exit` `ret` `err` `side` | `init` `preserve` `exit`, plus side tags `inRange_Lk` `known_Lk` `guard_Lk` `trip_Lk`. Duplicates are numbered; unclosed goals are appended, never dropped |
| `hcont`, `hif` | `hguard : st.boolAt "b" k = true`, `hk : k < N` |
| a `break` needs an `exit` clause | none: no `break` (Yosys 0.53 cannot read it) |
| carried variables must exist at entry | the same: SV definite assignment, which the self-read guard already enforces |
| (nothing) | **knownness** is tactic-owned. The tactic lifts `inv` to `Inv k st := frame ∧ KnownCarried st ∧ ∃ P, view st = P ∧ inv k P`, and discharges `known_Lk` from `inputsKnown`, as `sv_equations` does for assigns |
| (nothing) | wrap-around: an arithmetic accumulator needs a width side condition such as `N < 2^W`, which comes from the parameterisation |

The leverage is lower than in Python (JUDGED). The `py_vcgen` clause hides fuel, environment shape and interpreter symbolic execution. A plain-Lean recurrence has none of these, so the induction scaffold is about 6 lines (clmul `view_row`). What the tactic buys is the bookkeeping: knownness, ranges, frame, branch facts, nesting and several carried signals.

### 4.3 The bridge to `Statement`

The rows object needs `rows N = st` for the settled snapshot `st`. The reduction `CombTask.satisfiedAt_of_comb` (`svgolf/SvGolf/Comb.lean:113`) needs `CombDesign d'` and `Acyclic d'`, which are assign-only today. There are three candidate bridges.

| bridge | idea | covers | JUDGED cost | risk |
|---|---|---|---|---|
| **L** | Prove at symbolic N that `d.lowerComb = some d'` with `CombDesign d'` and `Acyclic d'` (or the single-process shortcut `Terminates2.of_lowerComb_single`, `Comb2Proc.lean:2980`). Then `Runs2.lowerComb_iff`, `procFixpoint_iff_combEqs`, `CombEqs.symWindow` and `Terminates2.of_lowerComb_acyclic` apply unchanged. | Multi-process designs and reuse of the whole rank chain for free. | spike 3–5 days; accumulator +1–2 weeks; nested scatter +1 | `SymState` grows by one window per trip for window-writing loops, with `Win.allDisjoint` at every join. The accumulator is the easy case. |
| **S** | A single-process snapshot theory: the settled `st` satisfies `ProcFixpoint`, so `st` equals the run from `st`, i.e. `rows N`. Idempotence comes from `runCombProcess2_alwaysComb_idem_of_admits`, the fixpoint exit from `combSettle2`'s `st' == st` test (`Sem2.lean:603-610`, digest), termination from `Terminates2.of_invariant` (`Spec2.lean:343`) plus the totality lemma. | One `always_comb` process, no other process. | ~2 weeks, ~1000 lines | A second settle theory beside `CombDesign`. Every later chain improvement skips it. |
| **FunProc** | B's L2: a functional-process interface and `AcyclicF` over (read, write) summaries. | General. | 2–3 weeks, ~1500 lines | The congruence lemma is new, unverified and 400–600 lines (JUDGED). It rewrites assign-specific rank proofs. |

**The spike (pre-registered).** Target: the accumulator design (nested clmul first, shift-xor with the window-fill spelling second).

Pass means a theorem of this shape, by induction over the trip list, with `#print axioms` clean:

```lean
-- proposed
theorem acc_lowers (N : Nat) (hN : 1 ≤ N) :
  ∃ d', (acc.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'
```

Together with the semantic evaluation lemma "`CombEqs d' st` gives bit `m` of the carried window `= (rows N).boolAt p m`".

Mechanism, JUDGED:
- `symExecList` over `(intRange i0 n).map f` is a `foldlM`.
- The invariant on the `SymState` is semantic, not syntactic: the state is one whole-window entry `(Wp, E_k)`, `E_k` evaluates to the row-`k` window, and `reads E_k` lies in a fixed set.
- For `joinIte` use the case split `joinIte G A B = A ∨ = .ternary G A B`. In the first case `A.same B = true` means `A = B`, so the semantic property holds trivially. The case where `Expr2.same` is stuck on an opaque accumulator therefore never matters.
- The existential `∃ d'` means the exponential tree never needs evaluating.

Decision tree, with a budget of **5 working days** for the spike:
- Pass: bridge L. Drop `FunProc` and A's G3.
- Fail on window-writing loops only: ship L for accumulators and S for the rest.
- Fail outright: ship S for the single-process nested clmul. Mixed designs wait. If the maintainers want mixed designs, `FunProc` is the escalation, and that is a decision, not an assumption.

### 4.4 Tactic surface

**Flow.** Same names as today. A computable predicate "the body contains a forEach" selects the loop route, a sibling of the existing route (the EqsM/S1b precedent). Loop-free designs take the old path byte for byte.

```lean
theorem solution : Statement Submission.design.sem := by
  sv_interface                 -- unchanged
  sv_structure                 -- loop route prints "loop L1: i = 0, +1, N trips, carried p[0,2N-1)"
  sv_equations?                -- prints the rows vocabulary below
  …                            -- golfer: sv_loop (inv := …), or just the exit goal
```

**How the step is computed.**
- The tactic runs `Stmt2.symExec` **once**, on one generic trip `f v` with `v` free and `0 ≤ v < N` in scope, from the empty `SymState`.
- `symExec_sound` yields `SymRel st₀ S_trip (rows (k+1))`, an entry field plus a frame field (digest). `selfReadFree` is not needed.
- Because the step is derived from one trip, the expression has constant size in `N`, and iteration-local temporaries are substituted away inside that one trip.
- Reads of carried windows print over `rows k`; reads of uncarried signals print over `st`.
- The `symWin` in-range conditions that stay stuck at a symbolic `v` become the `inRange_Lk` obligations.
- The existing printer machinery is reused by treating the trip as a template site with a "carried read redirect" (JUDGED; unverified).

**Mock-up 1: nested clmul** (`proc_nested_for.sv`). Two loops, so two row families.

```
sv_equations?   -- loop route (hand-written mock-up, not tool output)
  loop L1: i = 0, +1, N trips            carried: p [0, 2*N-1)
  loop L2: j = 0, +1, N trips (inside L1)
  rows_L1 : Nat → SvState           -- state before outer trip k
  rows_L2 : Nat → Nat → SvState     -- state before inner trip l of outer trip k
  eq_p_init    : ∀ m, m < 2*N-1 → (rows_L1 0).boolAt "p" m = false
  link_L2_in   : ∀ k, k < N → rows_L2 k 0 = rows_L1 k
  link_L2_out  : ∀ k, k < N → rows_L1 (k+1) = rows_L2 k N
  eq_p_L2_step : ∀ k l, k < N → l < N → ∀ m, m < 2*N-1 →
      (rows_L2 k (l+1)).boolAt "p" m =
        ((rows_L2 k l).boolAt "p" m ^^ (decide (m = k + l) && st.boolAt "a" k && st.boolAt "b" l))
  eq_p_exit    : ∀ m, m < 2*N-1 → st.boolAt "p" m = (rows_L1 N).boolAt "p" m
  known_p_L2   : ∀ k l, k < N → l ≤ N → ∀ m, m < 2*N-1 → KnownBit (rows_L2 k l) "p" m
  [inRange_L2] ⊢ ∀ k l : Int, 0 ≤ k → k < ↑N → 0 ≤ l → l < ↑N → k + l < 2*↑N - 1   -- intros; omega
  [guard_L1]   ⊢ …                                                                   -- affine, omega
  [cover_1] [inputsKnown_1] [inputsKnown_2]
```

A single bit at an affine offset is printed in "masked" form, which merges step and frame into one equation. For a window of several bits the printer emits separate `step_*` and `frame_*` lines. This is a printer decision (JUDGED).

The window `p[k+l]` is not injective in `(k,l)`. The entry/frame pair represents it as is, so no disjointness across trips is ever asked of the golfer.

With the default invariant, the one remaining goal is `exit`:

```
exit ⊢ ∀ m, m < 2*N-1,
  (List.range N).foldl (fun acc i => (List.range N).foldl
      (fun acc j => acc ^^ (decide (m = i + j) && A i && B j)) acc) false = coeff N a b m
```

(`A i = a.getLsbD i`, `B = b.getLsbD`.) This differs from `Spec.lean:48` only by `decide (m = i+j)` versus `decide (i+j = k)` and the `ofBits`/`getLsbD_ofBits` bridge the reference already has (`clmul_n.lean:98`). JUDGED: the golfer's whole proof is 15–40 lines against 206. This is the nested form's advantage, and the reason it is the first exemplar.

**Mock-up 2: shift-xor accumulator** (`p = '0; for i if (b[i]) p = p ^ (aw << i)`). The step has the same form:

```
  eq_p_L1_step : ∀ k, k < N → ∀ m, m < 2*N-1 → (rows_L1 (k+1)).boolAt "p" m =
      if st.boolAt "b" k = true
      then ((rows_L1 k).boolAt "p" m ^^ (decide (k ≤ m) && st.boolAt "aw" (m - k)))
      else (rows_L1 k).boolAt "p" m
```

Two preconditions, neither of which the Lean semantics gives for free:
- **A shift-by-trip vocabulary** (`XF.shlBits` with an affine amount) is required, because `shOpdRd?` (`CombView.lean:752`) refuses an iterator as the amount. Gate 4b is not merged.
- The collapse to the Spec is a reindexing of the double sum (`bx_pair`), so the default invariant does not finish it. JUDGED 60–110 lines.

**Mock-up 3: popcount** (`c = '0; for i c = c + a[i]`, `c : W` bits, fixed `W`; `$clog2` is outside the fragment). The step is not bit-separable, so the carried state is a word.

```
  eq_c_L1_step : ∀ k, k < N → (rows_L1 (k+1)).val "c" =
      ((rows_L1 k).val "c" + (if st.boolAt "a" k = true then 1 else 0)) % 2^W     -- `val`: vocabulary TBD
```

A clause `(inv := fun k (c : Nat) => c = cnt A k ∧ c ≤ k)` makes `preserve` need `(c+1) < 2^W`, from `hW : N < 2^W`. This is the SV twin of `tri`'s range conjunct. Whether the arithmetic step converts to a `Nat` mod expression through the existing `XF.addBits`/`XF.bv` machinery (PROVING §17) is unverified. **Popcount is the riskiest printing and the least important exemplar** (no popcount task exists), so it follows the nested form.

**Window-writing loops** (ripple add; G6). Same vocabulary: `eq_c_L1_step` for `c[k+1]`, `eq_s_L1_step` for `s[k]`, frame lines for the rest. The natural clause is a prefix invariant `∀ j ≤ k, (rows k).c j = carry j`. The guard lemma needs "reads of `c[k]` lie in must-writes of earlier trips". This is where bridge L is weakest (§4.3).

### 4.5 Loud refusals

Each refusal names the construct. Nothing is guessed.
- `break`, `continue`, `return`, `while`, `foreach`, `do`: `PStmt` has no node, and Yosys 0.53 cannot read them.
- A body that writes its own iterator (`tests/_example/attacks/for_counter_write.sv`).
- An iterator read after the loop.
- A bound that reads a non-parameter signal.
- A `!=` header, a wrong-direction header, a step ≤ 0 (`procStepDelta2`'s refusals reproduced exactly by the trip estimate).
- A run-time index write in the body (the guard over-refuses it).
- A loop inside a function body, until the inliner keeps the loop shape (PROC-NOTE X2).
- A clocked loop: tactic only. The semantic rule is shared.
- A non-affine index or shift in the **printer** (`W*k+i`, `1<<i`, `% 5`). The rule itself is index-agnostic; the message names the expression.

### 4.6 Trust base

- **Statement files unchanged**: `svgolf/tasks/*/Spec.lean`, `svgolf/SvGolf/Task.lean`. The statement quantifies over `design.sem`.
- **The one trusted definition that moves** is the fuel argument of the `forLoop` arm of `instStmt2`. It changes what `design.sem N` denotes for loops of ≥127 trips, from `.unsupported` to the real design. It must be recorded in `docs/sv-changelog.md`.
- `forValues2` (the iterate-until-false definition) is unchanged. `loopFuel` is an untrusted over-estimate. `Stmt2.forEach` is a transparent def.
- New Lean (`Loop2.lean`, recognizer, printer, tactics) is untrusted and kernel-checked. Every new lemma carries `#pin_axioms` (`PinAxioms.lean` exists).
- Extractor: literal-bound loops are retained as `For` (§6). A retained literal `For` is the same node kind parameter loops already use.
- Recorded restrictions: the unbounded `Int` iterator (§4.1); the retained-loop semantics has no Xcelium pin until G0 adds one.

### 4.7 Interaction with the existing chain, WP-LIN and heartbeats

- **Recognizers** (`CombProc.lean:981, 1086, 1182, 1321`): keep refusing `forLoop` on the old route. The loop route is selected before them.
- **Simp lists**: the six hand-copied literal lists (`CombProcTactic.lean:70-76`) get no new names. The loop route has its own sibling normalizer, as `svL_eq_norm_multi` did. All new lemmas live in new modules.
- **Heartbeats**: one loop is one site, so cost does not scale with the trip count. JUDGED target: a nested-clmul `solution` under 100,000k heartbeats. Unmeasured.
- **WP-LIN** (`wplin`, not in svgolf-prep): the loop route adds nothing to `rdWritersM`. Under bridge L an accumulator loop is lowered to one assign whose write set is the carried windows, so the existing writer groups suffice. A window-*family* loop would need a third group, and merge order then matters (JUDGED).
- **Mixed designs** (a loop process feeding or fed by generate families or assigns) are free under bridge L, and out of scope under bridge S.
- **The self-read guard** is unchanged. Only the trip-family lemma is added.
- **Generate loops** are unchanged. The loop route reuses the same planner lemmas.

---

## 5. Gate plan

All sizes JUDGED. Each gate lists its deliverable, an acceptance example, and what could fail.

**G0: semantics for every N.** 4–5 days, about 200 Lean lines.
- *Deliverable*: merge master's `Param2.lean`; `loopFuel`; the arm edit; `Stmt2.forEach`; `forValues2_fuel_mono`; `forValues2_asc/desc/le/+=c`; `instStmt2_forLoop_trip`. Audit the `RangeGuard2.lean:144/295` loop arms (read by the readers, not by me). Changelog entry.
- *Xcelium rows (Xcelium gate owner, not this note)*: N = 0, 1, 126, 127, 200, a zero-trip loop (bound `N-1` at `N=1`), `<=`, a descending header, `i += c`, nested, triangular (`j <= k`), and an iterator shadowing a parameter.
- *Acceptance*:
  - A `#guard` that a hand-built parameter-loop `PDesign` at N = 200 is not `.unsupported`.
  - `forValues2_asc` ∀N.
  - `harness/sv/diff_test2.py` green at N = 127 and 200.
  - `PDesign.int32Agrees` true at 200.
- *Could fail*: Xcelium disagrees with the model (an iterator-width or `i-1`-at-`i=0` effect). That forces a change in a trusted definition. **Stop rule S1: no merge before the rows agree.**

**G1: rule library and the pricing experiment.** 1.5–2 weeks, about 900 lines, parallel with the G2 spike.
- *Deliverable*: `Loop2.lean` as in §4.2, and a hand-built `PDesign` for the nested clmul (the envelope of `proc_nested_for.sv` should extract on master with retained `For`s; to be confirmed by running the extractor, which I did not).
- *Acceptance*: a **tactic-free ∀N theorem** that every settled state with known inputs has `p = coeff`, and `combAdmits` of the symbolic block ∀N, with `#print axioms` clean. Report: lines, heartbeats, number of new library lemmas, compared with the 206-line generate reference.
- *Could fail*: the guard lemma at symbolic length (the reader estimate is a roughly cubic walk at a concrete N, and non-injective windows overlap the may-write sets); `instStmt2 (env.bindVal it v)` at a free `v` not simplifying cleanly under `0 ≤ v < N`.
- **Stop rule S3: if the hand proof of the init/step/exit equations alone exceeds ~400 lines, stop and reconsider.** The rule library is not paying for itself and the tactic cannot rescue it.

**G2: the bridge.** Spike 3–5 days (parallel with G1), then:
- bridge L: +1–2 weeks for accumulators, +1 for scatter
- bridge S: 2 weeks
- *Deliverable*: whichever of §4.3 passes, with a theorem `CombTask.satisfiedAt_of_loop…` giving `SatisfiedAt` from the rows equations.
- *Acceptance*: `Statement` for the hand-built nested clmul, for every N, tactic-free.
- *Could fail*: see the decision tree. **Stop rule S2: no escalation to `FunProc` without a decision from the maintainers.**

**G3: the tactic.** About 3 weeks, about 1500 lines.
- *Deliverable*: the loop summary (a computable `loopSummaryP` with a soundness theorem, like `treeStmt?`/`treeStmt?_spec`, `CombProc.lean:1160/1258`), the loop route in `sv_structure`/`sv_equations`/`sv_cover`, knownness recurrence, tags, and `sv_loop`.
- *Acceptance*:
  - `Examples/system-verilog/loop_nested_clmul/` with `sv_equations?` output pinned verbatim in the `comb_hint.lean` style.
  - A solution of at most ~40 lines.
  - The 24 old dumps byte-identical; `tools/check_sv_chain.sh --list` green.
  - Heartbeats under the §4.7 target.
- *Could fail*: the step does not reduce to a clean pointwise equation after the in-range hypotheses; the printer's carried-read redirect does not fit the `Sk` grammar (O6 of design C). **Stop rule S4: if the printed step is not readable, print through the Summary route and re-price.**
- *Spike (day one)*: does the one-trip `symExec` give a constant-size step independent of `v`?

**G4: shapes of header and body.** About 1 week, about 600 lines.
- Descending headers, `<=`, `+= c`, several carried signals, iteration-local temporaries, and the second exemplar (shift-xor with the window-fill `aw`, needing the shift vocabulary from G5).

**G5: external, in parallel** (owners in §6). The fourstate interval rule; extractor retention; shift-by-trip vocabulary (gate 4b plus loop); Xcelium rows.

**G6: window-writing loops.** 2–3 weeks, about 1500 lines. Ripple add, map collapse, restoring division. Highest risk for bridge L, and the place where design C's `SiteInst` family-window extension would be needed (JUDGED).

**Later, unpriced.** A tactic for clocked loops; loops in function bodies; a process-level rank for mixed designs under bridge S.

**Total to the first end-to-end loop task** (nested clmul; G0+G1+G2+G3): about 6–9 weeks, JUDGED, with error bars of roughly ±50%. This is lower than A's 8–9 and B's ~8 because bridge L may remove `FunProc` and bridge S's second theory. It is higher than the judge's 6–8 because I priced the totality lemma and the guard lemma explicitly.

---

## 6. What the other owners must change

**Extractor (the other ls-sv agent; owner of the literal-loop unroll).** Requests:
1. Retain `For` for literal canonical headers instead of `symbolic_for_unrolled`. Use the node kind parameter loops already use (`_sym_for_parameter_shape`, `extract.py:21528`). **Drop the 128 cap there** (`:21435`). Tag it, e.g. `symbolic_for_retained`.
2. Keep unrolling headers outside the decoder tier, and make them identifiable. The meaning is still correct; only the structure is lost.
3. Put retention behind a flag (`--retain-loops`) until G3 lands. Retention could regress designs whose unrolled multi-window bodies the chain accepts today (JUDGED; unverified). Switch the default after `tools/check_sv_chain.sh --list` is green.
4. Keep the existing rows (`sem2/for_unroll`, `proc_loop_forms*`). Add differential rows for retained-versus-unrolled at N ∈ {0, 1, 2, 3, 16, 126, 127, 200}, a compound step, a negative step, nested, and an iterator shadowing a parameter.
5. Verilog-2001 iterators declared outside the header (57 of 112 non-LFSR loops, MEASURED) and compound assignments are WP-PROC items (X1, C1) that interact. Coordinate, don't duplicate.

**Loader / ingestion.** `Ingest2.lean:379` already parses `For`. The M0 path (`Param.lean:1683`) stays a refusal.

**Fourstate stage / checker.**
- **No loop design is scoreable before rule (d) learns loop bounds.** The rule text says so.
- Spec (PROC-NOTE.md:372): iterator interval from the header at the scoring point (literal or parameter start, constant bound, step ±1 or ±c, counter not assigned in the body); interval arithmetic for affine indices (`i`, `i+j`, `N-1-i`); the selected vector's range must contain the interval; refuse a body that writes its counter. The checker's rule is a check at one N. Lean's `inRange_Lk` is its for-every-N counterpart.
- A "bound < 2^31 minus margin" check at the scoring point covers the unbounded-`Int` restriction.
- Refusal messages must name the construct. The current message does not tell a contestant that the loop is the problem (clmul README).

**Shift vocabulary.** Gate 4b (`wpb2g4b`, not merged) plus a loop version, `XF.shlBits` with an affine amount and `XF.bv_shl`. Needed only for the shift-xor exemplar, not for the nested form.

**Xcelium rows.** From the Xcelium gate: the list in G0.

**Docs.** `docs/sv-changelog.md` (semantics change); `svgolf/tasks/add/README.md` (says loops are refused); the clmul README "How people write clmul"; `svgolf/PROVING.md` (a new loop section); `svgolf/REFUSALS.md`. `Comb2Proc.lean`'s "There are no loops in `Stmt2`" is accurate but stale against the extractor, which now retains parameter loops.

---

## 7. Risks and open questions

**Risks.**
1. **The golfer's leverage may be small** (JUDGED). The induction scaffold is ~6 lines. The design removes plumbing and bookkeeping, not the spec collapse. Only a nest that mirrors the Spec's fold gets a large saving, and a golfer picks the loop form that minimises area, not proof effort. The shift-xor spelling needs a reindexing collapse regardless. Stop rule S3 tests this early.
2. **The spike may fail** on `Expr2.splice` (symbolic Nat arithmetic inside slice offsets) or on `SymState` growth. Then bridge S ships for one process and mixed designs wait.
3. **The preserve goal may carry `if`s on `i`** (`instExpr2`/`fitExpr2` in-range checks) until `0 ≤ i < N` is applied. The generate path already does this with `Ctx.bindVal` (digest), so it has precedent, but the procedural path has not been tried.
4. **Knownness with arithmetic** (all-or-nothing under x). The invariant must carry it; the tactic discharges it from `inputsKnown`.
5. **Heartbeats**: the new route is unmeasured. Mitigation: sibling normalizer, new modules only.
6. **Xcelium disagreement** at N ≥ 127 or at an edge such as `i-1` at `i = 0`.
7. **The checker gate**: until the fourstate rule lands, Lean work can finish and still reach no leaderboard.
8. **Literal retention regressions** (§6, item 3).
9. **Stale measurements**: PROC-NOTE §6.1/§7.3.2 ("`sv_equations` refuses row families of a 2-D packed array") predate gate 4a (whole-row reads, merged via 4d846cff). Re-measure before pricing any design that emits row chains.
10. **Python lane is LEGACY** (digest). Only the rule shape and the clause discipline transfer, and the `for` rule has the least in-tree evidence (no in-tree `py_vcgen` `for` proof).
11. **Census reach is unmeasured** for per-shape bodies. The scan keeps statement-kind counts only.

**Open questions** (each answered by a gate, not by argument).
- Q1: Does `instStmt2 (env.bindVal it v)` at a free `v` simplify cleanly? (G1.)
- Q2: Rows as full states, or as carried-window value functions? Full states are preferred (frame for free); bridge L's `SymRel` already relates a symbolic state to a concrete one. (G1/G2.)
- Q3: What is the word-level step vocabulary for arithmetic carried state? (G3, after the nested form.)
- Q4: Retain all literal loops, or only above a trip-count threshold? (G5.)
- Q5: Does the default invariant "the fold" close `init`/`preserve` for the window-writing shapes? (G6.)

---

## 8. What this does NOT change

- `svgolf/tasks/*/Spec.lean`, `svgolf/SvGolf/Task.lean`, and the statement of every task.
- `Stmt2` (no constructor), `Expr2`, the interpreter `execStmt2`, `fuelMono2`, `symExec_sound/total`, `CombGuard2` and its soundness theorems.
- The six hand-copied simp lists, `CombProc` recognizers, and the sv_comb chain for loop-free designs (byte-identical dumps).
- The generate pipeline (`Gen2`).
- The M0 path (`Param.lean:1683`) and the self-check tier's run-time counter loops (`SelfCheck.execForLoop`, `Step.stepForLoop`).
- The banlist, Yosys scoring, and `break`/`continue`/`return`/`while`/`foreach` (still loud).
- The Python lane. This note only reads it.
- The axioms allowed in proofs: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, no `native_decide` is needed for any step above.
- The one semantic change is the fuel at `Param2.lean:1264`: loops of ≥127 trips go from loud to decided, with Xcelium rows first.


---

## 9. G1 result and the sized plan for the loop route (WS3, agent L, 2026-11-02)

Labels as in the header: MEASURED (built, counted or `#count_heartbeats`), READ (`file:line`), JUDGED. Branch
`arch-loop`; commits `a6672a4e` (G-L0), `fb98950c` (G-L1), `0baa6bab` (G-L2), `f9c39f07` and `2cbcbb95` (G-L3, after
the merge of `integ1102m` with master's `c64ebdac`).

### 9.1 What was built

| layer | where | what | code lines |
|---|---|---|---|
| loop domain (G-L0) | `LeanModels/Sv/Loop2.lean` | `TripSchema` (count, `Fin count → Int`), `TripSchema2` (inner schema per outer trip), agreement with a header in 32-bit `int` (`iter32`), uniqueness, the fuel-free decoder `headerSchema` with `headerSchema_agrees`, `toList`/`intRange` views, the bridges to the legacy `forValuesFuel2`/`forValues2` | generic |
| rows (G-L1) | `Loop2.lean` | `Denotes I s g` (uniform fuel inside an existential), `DenotesL.cons`, `Denotes.block`, `rows`, the loop rule `Denotes.loop` (induction on the trip count), `assignSlice`/`assignLit` | 81, generic |
| guard (G-L2) | `Loop2.lean` | `GuardIn`, `readsViol_covered`, `GuardIn.assign/list/block/admits`: the self-read guard over a trip family, no walk at a symbolic length | 90, generic |
| Bridge S (G-L3) | `Loop2.lean` | `rows_set` (one-signal frame: state rows are value rows), `SingleComb` (one idempotent `always_comb`: settle in two passes, `terminates`, `runs`), `driversOk_single`, `forValues2_upto`/`forFuel2_upto` | 180, generic |
| clmul, design-specific | `LeanModels/Sv/Loop2Clmul.lean` (importable by svGolf) | instantiation, rows, guard instance, value rows, idempotence, `clmul_single`, the known-input arithmetic, `clmul_correct` | 300 |
| clmul statement | `svgolf/design/loop/g1/ClmulNested.lean` (`compile-loop.sh`) | `load_sv`, `sem N` at symbolic `N`, the `coeff` collapse, `statement : Statement clmulNested.sem` | 94 |
| endpoints (G-L0) | `Examples/system-verilog/loop_edges/`, `…/loop_nested_clmul/schema.lean` | the schemas of `<`, `<=`, descending, `+= C`, negative start, shadowing, 0/1/126/127/200 trips, read off extracted envelopes; differential guards against the legacy unrolling | — |

MEASURED costs: the design-specific theorems use at most 85k heartbeats each (`clmul_correct`), 756k summed over the 32
of `Loop2Clmul` and 366k over the 11 of `ClmulNested` (`sem_eq` 80k); `.olean` sizes `Loop2` 3.19 MB (generic, G-L0
included), `Loop2Clmul` 1.23 MB, `ClmulNested` 0.66 MB. Axioms: `propext`, `Classical.choice`, `Quot.sound` on every
theorem (`#pin_axioms`).

Findings that change the plan:
- **The loop's meaning has no fuel.** `TripSchema.HeaderAgrees` + uniqueness make "the trips of a header" well
  defined; `headerSchema` computes them in closed form for canonical headers and refuses a header whose 32-bit
  iterator would wrap (`i <= 2147483647`), which the legacy unbounded reading unrolls. D1's `loopFuel` is obsolete.
- **Idempotence does not come from the guard's soundness theorem.** `runCombProcess2_alwaysComb_idem_of_admits` needs
  `Shaped`, which `applyInputs2` breaks on a stimulus of the wrong width, and `Terminates2` quantifies over every
  stimulus. It comes from the frame instead: the body sets `p` from `a`, `b` and `p`'s width only.
- **Extractor gap** (handed to the ls-sv library): an inner `for (int j = 0; j < i; j++)` is not retained; the
  envelope then carries a `LocalDecl` that `load_design_sv2` rejects.

### 9.2 Where the 394 design-specific lines went (MEASURED counts, JUDGED attribution)

| category | lines | what | automatable by |
|---|---|---|---|
| instantiation of `sem N` | 112 | the `PStmt` pins (11), the printed `Stmt2` body (9), `inst_trip`/`inst_body` (15), `clmul_loops` (12), `clmul_writes` (21), `clmul_guardProc` (3), the `paramEnv2`/`buildDecls`/`buildElems`/`assemble2`/driver-guard staging (41) | A |
| rows, frame, guard peeling | 104 | `Bound` and its preservation (14), `trip_eval` with its fuel, `trip_denotes`, `clmul_rows` with explicit composite functions and the row equations (27), `tripS`/`initS`/`outerS` (5), the guard instance (27, the affine fact `i + j < W` included), the value-row frame `rd`…`body_idem` (31) | B |
| Bridge S packaging | 83 | `applyInputs2` over the literal declarations and the invariant `Inv` (25), `clmul_single` (23), `clmul_correct` (17), `satisfiedAt_of` (18) | C |
| the generic-trip step on known values | 14 | `trip_known`: bit `i+j` flips by `a[i] & b[j]` | B |
| arithmetic library | 21 | `bx` (3), `foldl_xor` (10), `getLsbD_ofBits` (8): the reference has the same lemmas | E |
| **loop thinking** | **38** | `cx` (2), the inner and outer row inductions `inner_known`/`outer_known` with their row invariants (26), the collapse `coeff_eq` (4), the trip's value `tripP` (3), `statement` (3) | — |
| file overhead | 22 | imports, namespaces, `load_sv`, axiom pins (two files) | — |

The reference's 206 lines lean on `sv_structure`, `sv_equations`, `sv_bridge` and `sv_cover`, which do this plumbing for
generate families. The loop route has no such tactics yet, so the hand proof carries their work: it moves the plumbing,
it does not remove it. The thinking is small (38 lines by this attribution; about 55 if the step's known-value form
`trip_known` and the guard's affine fact are counted as thinking too), which is the case for automating exactly the
rest.

### 9.3 The sized plan, ranked by design-specific lines saved

Acceptance for the whole plan: a cold agent proves the nested `clmul` without touching fuel, block plumbing or settle
theory, and the design-specific count falls to the thinking plus a small residue: **at most about 70 lines** (JUDGED
target: the 38 lines of thinking, ~15 of file overhead in one file, a handful of tactic calls, the output's per-bit
equation and the guard's affine fact). Every item below ships with a
refinement or soundness theorem (ARCH-NOTE: every view a tactic relies on carries one) and is measured on the nested
`clmul` proof before the next one starts (the plan's "the proof gets shorter or the item is dropped").

**B. The loop recurrence, printed (items 8, 10, 11, 9, 5, 7 and the generic-trip step). Saves about 120 lines.**
*A tactic over lemmas and one simp set.*
- `sv_loop_rows` reads the instantiated body (`block` of trips over `List.range`, nested), and proves and prints, for a
  loop whose trips write one signal `p` from the others: `body st = set st p (vrows h (rd st) N (init w))` with the
  trip function `h` given as a plain equation (the LOOP-NOTE §4.4 `eq_p_L2_step` shape), plus `body` idempotent and the
  invariant `Bound`/width preserved. Lemmas exist (`Denotes.loop`, `rows_set`, `width_vrows`); new: a `Denotes`
  composer that computes the composite function (no `(g := …) (h := …)`: item 5), the base lemmas through the
  fuel-free `evalPure2` (`evalExpr2_eq_evalPure2`, `Pure2.lean:345`: no fuel arithmetic, item 7), and the generic-trip
  symbolic step through `Stmt2.symExec`/`symExec_sound` (`Comb2Proc.lean:484,1835`) for an arbitrary trip body.
- A simp set `sv_loop_known` (the Known2 `ofBitVec` lemmas, `getLsbD_bvInsertAt`) turns the trip function on known
  inputs into the bit equation (`trip_known` disappears).
- The guard: `GuardIn.forEach` (a lemma: a `block` of a mapped `List.range` is guard-safe when each trip is) and a simp
  set that reduces each trip's windows to affine facts, leaving `i + j < W` to `omega`. Block peeling (item 8) is
  done once, inside the tactic, for the guard, the one-driver rule and the rows.
- JUDGED size: 300 to 400 generic lines; the riskiest piece is the generic-trip step for bodies with `if`s
  (`Expr2.joinIte` growth is per trip, so constant in `N`, but unpriced).

**A. `sem N` of a single-process loop design (item 13). Saves about 105 lines.** *A lemma, a simp set and a thin
tactic.*
- A lemma `PDesign.instantiateGD2_single`: for a flat envelope with no generates and one `always_comb`, `sem N` is
  `⟨name, decls, #[combGuardProc wd (instStmt2 envP elems body)]⟩` once the stages decide, with the driver rule
  discharged by `driversOk_single` from a `WritesOnly` fact.
- A simp set `sv_loop_inst`: `instStmt2` through canonical `forLoop` headers via `forValues2_upto` (and its `<=`,
  descending, `+= c` twins from `headerSchema_agrees`), the trip instantiation (`sv2_inst_simp`'s lemmas), and the
  declaration widths at symbolic `N`; `WritesOnly` decided by simp on the instantiated body.
- `sv_loop_inst` runs the stages and prints the instantiated body (what `clmulBody` is today, written by hand), with
  `combGuardProc` removed by B's guard lemma. JUDGED size: 150 generic lines; it reuses ripple_add's staging recipe and
  should share it with the existing `sv_structure` rather than fork it.

**C. Bridge S as a task lemma (item 12 and the packaging). Saves about 75 lines.** *Lemmas only.*
- `CombTask.satisfiedAt_of_singleComb` (untrusted, beside `SvGolf.Comb`'s `satisfiedAt_of_comb`): a design whose
  declarations are its ports, with one `always_comb` whose body denotes `set p (F (a, b))`-shaped functions,
  satisfies the task at `N` once `F` on known inputs is the task's function. The `applyInputs2`/`Inv`/`SingleComb`
  obligations are discharged generically from the declarations (inputs are set, every other declared signal keeps
  its value and width). Residue: the per-bit equation of the output (about 5 lines). JUDGED size: 100 generic lines.

**D. Composite runs and fuel arithmetic (items 5, 7) outside B.** Most of their design-specific weight is inside B
(counted there). Their generic value is for other loop shapes (sequences of loops, loops after assigns): a `Denotes`
composer tactic and the `evalPure2` base lemmas, built as part of B. Saves no further clmul lines; JUDGED 50 generic
lines.

**E. The XOR-sum calculus in a library. Saves about 21 lines.** *Lemmas.* `bx`, `bx_succ`, `foldl_xor`,
`getLsbD_ofBits`, `coeff_eq`'s collapse step, moved to an untrusted library module (LOOP-NOTE D5's CombLib idea; the
reference and this proof now repeat them).

| item | kind | design-specific lines saved | generic lines (JUDGED) | order |
|---|---|---|---|---|
| B rows, frame, guard, step | tactic + lemmas + simp sets | ~120 | 300–400 | 1 |
| A `sem N` | lemma + simp set + thin tactic | ~105 | ~150 | 2 |
| C Bridge S task lemma | lemmas | ~75 | ~100 | 3 |
| E XOR calculus | lemmas | ~21 | ~30 (moved) | 4 |
| D composer, `evalPure2` base | tactic + lemmas | (inside B) | ~50 | with B |
| **after all five** | | **394 → ~70** | ~650–750 | |

Order: B first, because it carries the loop-specific risk (the generic-trip step) and its lemmas are what A and C
state their outputs in; A second, because it is mostly reuse; C third; E whenever a third proof would repeat the
lemmas. Stop rule for the build (JUDGED): if B alone does not bring the clmul proof under about 280 design-specific
lines, stop and re-price before A.

### 9.4 What this does not change

The trusted statements, `Stmt2`, `run2`, `instStmt2`, the guard and the extractor: nothing in §9 edits them. Every
deliverable above is *provisional over `run2`* until R-DESIGN2 transports it.

### 9.5 Built: B, A, C, E (WS3, 2026-11-02), measured on the nested `clmul`

Commits `ee2d1b26` (B), `eee5dd0a` (A), `903f5ef0` (C, E). Every module builds; `#pin_axioms` clean; no existing
module edited. Code lines are non-comment non-blank (the counter that gives 206 on the generate reference).

| step | design-specific lines | generic module (lines) |
|---|---|---|
| G1 by hand | 394 | — |
| after B, `sv_loop_rows` | 245 | `LeanModels/Sv/Loop2Rows.lean` (244) |
| after A, `sv_loop_sem` | 172 | `LeanModels/Sv/Loop2Sem.lean` (104) |
| after C, `CombTask.satisfiedAt_of_loop` and E, the XOR-sum lemmas | **96** | `svgolf/design/loop/LoopTask.lean` (91), `LeanModels/Sv/XorSum.lean` (41) |

- **B** (tactic over lemmas): `sv_loop_rows (body := B) (bound := ns) [defs]` prints `row`, `row_init`, `row_step`
  (a plain equation on values), `row_next`, `row_width`, `body_run`; pinned verbatim in
  `Examples/system-verilog/loop_nested_clmul/rows_hint.lean`. The run2 seam is `Denotes` and five primitive lemmas
  (`Denotes.block`, `DenotesL.cons`, `Denotes.loop`, `Denotes.assignLit`, `Denotes.assignSliceE`); the rest
  (`valE`, rows, frame, idempotence) is pure functions on states, so retargeting to E is re-proving those five.
- **A** (lemma + thin tactic): `sem_single` reuses the comb chain's declaration stage (`CombView.declsOf?`,
  `buildDecls_summary`, `buildElems_summary`, which `sv_structure`'s `sound_prefix` composes) instead of copying
  it; `sv_loop_sem [defs]` closes `X.sem N = ⟨name, decls, #[.alwaysComb B]⟩` (parameter and declaration stages by
  `rfl`, widths by `simp`/`omega`, the loop through `forValues2_param`, guard and driver rule by the shape lemmas).
- **C** (lemma): `CombTask.satisfiedAt_of_loop` leaves only the per-state correctness `hout`.
- **E** (lemmas): `bx`, `foldl_xor`, and one known XOR-accumulate trip (`andBit_known`, `xorBit_known`).

What the 96 lines are: the thinking (the three definitions that state the body, `cx`, the trip's known-value step
statement, the inner and outer row inductions, the collapse `coeff_eq`, the final bit equality: about 55), file
overhead (about 17), the task-specific `getLsbD_ofBits` (8, a fact the task could ship), and the calls with their
side goals (about 16: `sem_eq`, `sv_loop_rows`, the `satisfiedAt_of_loop` call and the input facts). The target of
§9.3 was at most about 70; the remaining gap is overhead and task facts, not loop plumbing. MEASURED heartbeats:
`sem_eq` 76k, `statement` between 100k and 200k (`#count_heartbeats` misreports it as 3k; a 100k limit fails, the
default 200k passes); `.olean` `ClmulNested` 1.27 MB, `LoopTask` 0.17 MB.

Limits of the tactics as built (JUDGED): `initNest` is one shape (an init, a two-level nest, a single slice write
per trip, a `simpleExpr` right-hand side, unit-step headers against a parameter). Other loop shapes (one level,
`if` in the body, several written signals, `<=`/descending/`+= c` headers, a loop after other statements) need
their own shape lemmas or a recursive recognizer; the run2 seam and the frame/idempotence argument carry over.

### 9.6 Generalizing the loop shape, sized by two designs (WS3, 2026-11-02) — the stop rule fired

**Designs.** Both are local specs, with no task and no trusted file. Both are proved for every `N ≥ 1`, *provisional over run2* (`compile-loop.sh`).
- `g2/prienc.sv`: one level, an `if` in the body, the header `i <= N` from 1. Spec: `y` is the bit length of `a` (`log2 a + 1`, `0` for `a = 0`). Proof: `g2/PriEnc.lean`.
- `g2/popcnt.sv`: `cnt = cnt + a[i]` with a 32-bit `cnt`. Spec: `countP` of the set bits. Proof: `g2/PopCount.lean`.

**Today's tactics refuse both** (MEASURED):
- prienc `sv_loop_sem`:
  - The instantiation simp stops at `forValues2 … (PExpr.int 1) (PExpr.binary .sle …)`. `forValues2_param` covers only `it = 0; it < P`.
  - The trip's literal stays Param2's private `intLit2`.
  - `loop_admits` then times out at `isDefEq` (200000).
- popcnt `sv_loop_sem`:
  - The header passes.
  - The simp stops at `ctxOpWidth2`, the context width of `cnt + a[i]`.
  - `loop_admits` then times out at `whnf`.
- Both, `sv_loop_rows`: `loop_rows rfl` gives a type mismatch. `B = initNest ?…` fails, because the body is not the two-level slice nest.

**Built: a recursive recognizer**, `LeanModels/Sv/Loop2Frag.lean`, 424 code lines (MEASURED).
- **The fragment.** `Stmt2.fragOk n` accepts blocks, `if`/`else` on simple conditions, and writes of simple expressions to the whole of `n` or to a constant slice of it.
- **Its meaning.** `Stmt2.step` gives the fragment's meaning on `n`'s value, computed by structural recursion.
- **One induction** (`Stmt2.frag_rec`) proves three things: soundness (`frag_den`), the guard (`frag_guard`) and the one-driver rule (`frag_writes`).
- **The shape.** `initLoop` is `n = c; for k < N: T k`, for any fragment trip `T`.
- **Headers.** `forValues2_up` covers `it < P` and `it <= P` from any literal start.
- **Tactics.** `sv_loop1_rows` and `sv_loop1_sem`.
- **The printed recurrences are plain equations:**
  - popcnt: `row st (k+1) = (evalBinOp .add (row st k) (((sig st "a").extract k 1).resizeU 32)).resizeU (row st k).width`.
  - prienc: `row st (k+1) = if ((sig st "a").extract k 1).condTrue = true then (LVec.ofInt 32 (1 + ↑k)).resizeU (row st k).width else row st k`.
- **The seam grows by two primitives**, `Denotes.assignE` (a whole-signal write of an expression) and `Denotes.ite`. The original five are unchanged, and no Comb* module was edited.

| part of `Loop2Frag` | lines | needed by the per-shape route too? |
|---|---|---|
| seam: `assignE`, `ite`, two `congr` | 41 | yes |
| headers: `forValues2_up`/`_slt`/`_sle`, two normalizations | 52 | yes, for (a) |
| `GuardIn.ifStmt` | 25 | yes, for (a) |
| tactics | 46 | yes, about the same |
| the fragment, `step` and its width and frame lemmas | 92 | no |
| `frag_rec` | 39 | no |
| `frag_den`, `frag_guard`, `frag_writes` | 64 | no |
| one-level shape (`loop1_rows`/`_admits`/`_writes`) | 51 | no |

**The per-shape alternative.**
- For (b) it was MEASURED by a probe that is not committed (`acc_rows`/`acc_admits`/`acc_writes`): 68 lines, under maxHeartbeats 5000.
- For (a) it is JUDGED at about 75 lines.
- Per-shape total for both designs: about 300 lines, against 424 for the recognizer.
- The recognizer's extra cost is about 120 lines. They buy the whole fragment, so a third one-level single-signal design in it costs 0 generic lines; per shape it would cost about 70–80. The break-even is at the third or fourth shape.

**The stop rule.**
- Per shape: (b) alone costs about 125 per-shape (under 150). (a) costs about 185 even per-shape, and the `<=` header alone is 52.
- The recognizer as a whole is 424.

**Design-specific cost** (MEASURED):

| design | code lines | maxHeartbeats 5000 | `#hb` `sem_eq` | `#hb` `statement` |
|---|---|---|---|---|
| PopCount | 49 | every declaration passes | 3.6k | 1.6k |
| PriEnc | 77 (its log2 bridge is about 30) | every declaration passes | 4.6k | 2.2k |

- The per-design count is the same under both routes, because the printed recurrence is the same.
- `Loop2Frag`: every declaration passes at 20000. One fails at 5000.

**Choice** (JUDGED): the recognizer, pending the lead's decision.

**Lead's decision (2026-11-02).**
- The recognizer is accepted. `Stmt2.step` stays a derived view, and `frag_rec`/`frag_den` are its soundness against the seam. It is *provisional over run2* like everything else.
- The seam extension is accepted. It may grow with the statement fragment on three conditions: one `Stmt2` construct per primitive; no run2 internals in a primitive's signature; and a visible count (table below).

#### The seam: 7 when accepted, now 5 (§9.7 deleted the two dead ones)

Every primitive's signature uses only `Denotes`/`DenotesL`, `valE`, `sig`, `SvState` and `LVec` operations. Only the proofs open `execStmt2`/`evalExpr2`.

The E-core-0 facts are READ on `arch-x1` at `d00b2919`. Paths:
- `Core0` = `LeanModels/Sv/Kernel/Core0.lean`
- `Core0Proc` = `LeanModels/Sv/Kernel/Core0Proc.lean`
- `Core0Comb` = `LeanModels/Sv/Kernel/Core0Comb.lean`

| # | primitive (module) | `Stmt2` construct | matching E-core-0 fact |
|---|---|---|---|
| 1 | `Denotes.block` (`Loop2`) | `.block arr` | `execBody`'s `.block` arm, `execBodyList E arr.toList` (`Core0`, definitional). Named lemma owed. |
| 2 | `DenotesL.cons` (with `DenotesL.nil`) (`Loop2`) | a statement sequence (`execStmts2`'s cons) | `execBodyList`'s cons and nil arms (`Core0`, definitional). Named lemma owed. |
| 3 | `Denotes.assignSliceE` (with its helper `Denotes.assignSlice`) (`Loop2Rows`) | `.blockingAssign (.slice n lo w) e` | `execBody_assign_run` (`Core0Proc`) with `Elab.view_writeWin` (`Core0Comb`). E needs the window in range (`Lhs2.staticWin`), which is the `sl := lo + w ≤ W` instance of `fragOk` that `frag_guard` already takes. |
| 4 | `Denotes.assignE` (`Loop2Frag`) | `.blockingAssign (.ident n) e` | `execBody_assign_run` with `Elab.view_writeWin`. |
| 5 | `Denotes.ite` (`Loop2Frag`) | `.ifStmt c a b` | `execBody_if_run` (`Core0Proc`). |

**Deleted in §9.7, because nothing used them once the recognizer took over:**
- `Denotes.loop`, the old #3, with its `rows`/`DenotesL.loop`. A loop's instantiated block is a block: `frag_den`'s block case proves it, and `listStep_range` is its recurrence.
- `Denotes.assignLit`, the old #4. It is the `.lit` case of `Denotes.assignE`.

**Transporting the whole seam to E.** `execBody_of_execStmt2` (`Core0Proc`) maps any terminating `execStmt2` run of a `staticB` body from the view of a typed store to an `execBody` run with the same view. With it, one corollary would give the E form of every `Denotes` fact over all-four-state declarations. That corollary is owed: `Denotes` over E is not defined yet. No per-primitive E lemma is then needed, and the per-construct run lemmas above are the direct route.

### 9.7 Nesting through the recognizer (WS3, 2026-11-02): `initNest` is gone

**A trip may itself be a loop.** An instantiated `for` is a block of trips, so the fragment already contains a nest. The two additions:
- `listStep_range` reads the inner loop's step as its rows.
- `rows_nest` (8 lines) names the inner row. In the tactic, `row_in`, `row_in_init : row_in st i 0 = row st i`, `row_in_step` (the inner trip, a plain equation) and `row_next : row st (i+1) = row_in st i N` replace `row_step`.

The nested `clmul` is proved on the general route, with the `clmul` `Statement` unchanged:
- `clmulBody` is now `initLoop "p" 0 N (fun i => .block #[.block (for j: p[i+j] = …)])`.
- The proof is `sv_loop_sem` and `sv_loop_rows` (the `sv_loop1_*` names of §9.6 took the old names once the old tactics were deleted).
- The new printed recurrence is pinned in `Examples/system-verilog/loop_nested_clmul/rows_hint.lean`.

**Deleted, now dead:**
- From `Loop2Rows`: the special shape `initNest` with its rows, guard, driver and tactic.
- From `Loop2Sem`: `forValues2_param` (subsumed by `forValues2_slt`) and the old `sv_loop_sem`.
- From `Loop2`: `rows`/`rows_shift`/`rows_inv`/`DenotesL.loop`/`Denotes.loop`/`Denotes.block1`/`Denotes.assignLit`, and `rows_set`, which was already unused.

| generic module (code lines, MEASURED) | before | after |
|---|---|---|
| `Loop2` | 803 | 747 |
| `Loop2Rows` | 244 | 69 |
| `Loop2Sem` | 104 | 52 |
| `Loop2Frag` | 424 | 437 |
| total | 1575 | **1305** (−270: nesting +13, deletions −283) |

**Design-specific lines (MEASURED):**
- `clmul` stays at 96 (`ClmulNested` 81 → 80, `Loop2Clmul` 15 → 16).
- `PriEnc` 77 and `PopCount` 49, unchanged.

**`clmul` heartbeats (MEASURED by a file-wide `maxHeartbeats`):**
- Every declaration passes at 20000.
- At 5000, only `sem_eq` fails, so `statement` is under 5000.
- §9.5's old route: `statement` failed at 100k and passed at 200k, and `sem_eq` was 76k.

**Builds.** All four `compile-loop.sh` modules, the three loop examples, and every `#pin_axioms` build.

**Limit (JUDGED):** `rows_nest` names a nest whose outer trip is exactly the inner loop (with or without `begin`/`end`). A trip with statements around its inner loop still gets a correct `row_step`, with `vrows` in it, but no named inner row.

### 9.8 The seam over E-core-0 (WS3, 2026-11-02): the loop body leaves *provisional over run2*

**The merge.** `arch-x1` is merged into `arch-loop` read-only, at `d00b2919`. None of A's files is edited.

**`DenotesE`** (`LeanModels/Sv/Loop2E.lean`) is the sibling of `run2`'s `Denotes` over E-core-0's fuel-free `always_comb` execution `Kernel.execBody`. It does not replace `Denotes`. From every typed store whose view satisfies `I`, one `execBody` succeeds and ends in a typed store whose view is `g` of the view. `DenotesLE` is the same for `execBodyList`.

**The five seam primitives over E** are proved from E's arms, with no `run2` and no fuel.
- The arm lemmas the §9.6 table listed as owed are now named: `execBody_block`, `execBodyList_nil`, `execBodyList_cons` and `execBodyOpt_none`/`_some`.
- The primitives: `DenotesE.block`, `DenotesLE.nil`/`cons`, `DenotesE.assignSliceE`, `DenotesE.assignE`, `DenotesE.ite`.
- The assignments go through `execBody_assign_run` with `Elab.view_writeWin`.
- `ite` goes through `execBody_if_run`. An x condition takes the else branch in E as in `run2`, so no gap there.
- **E-side hypotheses**, each a restriction E-core-0 itself imposes:
  - `AllFour E`, E-core-0's 4-state clause.
  - The target's declared width.
  - `lo + w ≤ W` for a slice, because E's write is the static in-range window (`Lhs2.staticWin`, LRM 10.4.1).
- **Is the slice bound a gap? No, for the loop route.** `run2` truncates an out-of-range slice write where E refuses it. But the recognizer's guard (`frag_guard`) already requires `lo + w ≤ W`, so every loop body proved so far is in range.

**The recognizer over E.** `Stmt2.frag_denE` is `frag_rec`'s soundness re-stated over `DenotesE`, for the in-range instance of `fragOk`. It is proved from the five E primitives only.

**The whole-seam corollary.** `Denotes.toE` is a *transport theorem*: a `run2` `Denotes` fact of a `staticB` body holds over E. It is A's `execBody_of_execStmt2` at the `Denotes` fuel bound. `Stmt2.frag_static` shows that every in-range fragment statement is `staticB`.

**The body, per design: a *transport theorem* (body).**
- `svgolf/design/loop/LoopTaskE.lean` defines `BodyE t N d`. It says: one E-core-0 activation of `d`'s `always_comb` body, from any typed store of an all-4-state elaboration with `d`'s declarations whose inputs hold known values, ends in a store whose outputs hold `t.fn N` of them.
- `CombTask.satisfiedAt_and_E` proves it beside `t.SatisfiedAt N d`, from the same per-state arithmetic `hout`. It uses `Denotes.toE`, `frag_static`, and `loopInv_view` (a typed view meets the loop invariant).
- Each design now has `statement_and_body`, with `statement` and `body_E` as its two projections: `ClmulNested.body_E`, `PriEnc.body_E` and `PopCount.body_E`, for every `N ≥ 1`.

**The boundary.**
- **Transported:** one activation of the body (`execBody`).
- **Still over `run2`:** `t.SatisfiedAt N d`, that is, `Terminates2` and `Computes`, through Bridge S (`SingleComb.settle`/`cycle`/`runs` on `combSettle2`, `cycleStep2`, `Runs2`).
- **Why it stops there:** E-core-0's slot level for an `always_comb` (`activate_comb`, `Settles.ofLower`, `rcomb1`) takes the lowering `E.toDesign2.lowerComb = some d'` and the certificates `completeB`/`rankedB`/`boundB`, all computed on a concrete design. They do not exist at a symbolic loop bound. That is what R-DESIGN2 must cover for `always_comb` loops.

**New generic lines (MEASURED): 200**, under the 250 stop rule.

| module | lines | what |
|---|---|---|
| `Loop2E` | 153 | `DenotesE`/`DenotesLE` with `congr` (14); E's arm lemmas (12); the five primitives with the `staticWin`/view helpers (54); `frag_denE` (33); `Denotes.toE`, `frag_static`, `listStaticB_of` (25); file overhead (15) |
| `LoopTaskE` | 45 | `BodyE`, `loopInv_view`, `satisfiedAt_and_E` |
| `Loop2Frag` | +2 net | `sv_frag_ok`, one tactic for the fragment side conditions, now used by `sv_loop_rows`, `sv_loop_sem` and the designs |

**Design-specific lines (MEASURED):**
- `clmul`: 96 → 102.
- `PriEnc`: 77 → 82.
- `PopCount`: 49 → 54.
- Each design pays for the pair theorem, its two projections, and the `declWidth` and `sv_frag_ok` arguments.

### 9.9 The single-process slot over E, at a symbolic bound (WS3, 2026-11-03)

**What is proved.** Each loop design's task statement is proved over the authority's backend:
- `task.Statement_obs ty Obs_E0 (fun _ => True) (fun N => Elab.ofDesign2 (sem N))`, for every `ty`.
- `ClmulNested.statement_E0`, `PriEnc.statement_E0`, `PopCount.statement_E0`.
- It uses P's Task v2 convention (`TaskV2.lean`) and A's `Obs_E0` (`Core0Obs.lean`). It is *derived from E*.
- No per-N certificate is used. The run2 statements (`statement`) are kept beside it.

**The slot** (`LeanModels/Sv/Loop2Slot.lean`). `SingleE E body I F n` says (§9.10 widens `n` to a write set `W`):
- E's only process is `body`, which runs to `F` (`DenotesE`).
- `F` writes only `n` and is idempotent.
- `quiet`: a slot that wakes nothing finds the store settled.

From these:
- `SingleE.slot`: from a typed opening, with the process ready or the store settled, every legal schedule closes the slot at ONE configuration, with view `F` of the opening view. The process runs once. If its own write woke it, it runs a second time, and that second run is a no-op.
- `behaves`: every slot of every behaviour closes settled.
- `exists_behaves`: every choice and environment has a behaviour.
- `post_eq_pre`: the sample slot repeats the edge slot.
- `pre_view`: the edge slot's view is `F` of its opening.

`quiet` for a fragment body comes from three lemmas:
- `Stmt2.frag_local`: the meaning reads only its expressions' windows.
- `sens_of_read`: every read of another signal is in E's sensitivity, since every window the body writes is `n`'s (`Stmt2.frag_targets`).
- `settled_of_quiet`.

**The composition** (`svgolf/design/loop/LoopTaskE.lean`).
- `singleE_frag` turns structural facts into `SingleE`.
- `CombTask.satisfiedAt_obs_of_frag` proves the four conjuncts of `SatisfiedAt_obs`: interface, progress, receptiveness, and the function on every behaviour.
- Its last hypothesis is `hout`, the design's arithmetic, now one backend-free lemma `out` per design. `out` is shared by the run2 `statement` (`CombTask.satisfiedAt_of_frag`) and `statement_E0`.

**Every hypothesis of `statement_E0`.** Each is decided at symbolic `N` by `simp`, `omega` or `sv_frag_ok` after `sem_eq`:
- `t.Interface N d`.
- `d.processes = #[.alwaysComb (initLoop …)]`, which is `sem_eq`.
- Every declaration 4-state.
- Declaration names distinct.
- The written signal is declared, has a width, and is not an input.
- The body is in the fragment with every slice in range.
- The task's input names are distinct.
- `hout`.
- Not needed: `completeB`, `rankedB`, `boundB`, a lowering, or any per-N certificate.

**No `run2` in the chain (MEASURED).**
- `svgolf/design/loop/NoRun2.lean` checks this at build time. It walks the transitive closure of every constant each `statement_E0` uses, in its type and its proof: about 7,250 constants.
- The closure contains none of run2's execution and observation constants: `execStmt2`, `execStmts2`, `evalExpr2`, `runCombProcess2`, `combPass2`, `combSettle2`, `cycleStep2`, `run2`, `Runs2`, `Models2`, `Terminates2`, `Loop2.Denotes`, `Obs_run2`.
- The control, `ClmulNested.statement` over run2, contains 12 of them.
- The front end is in the chain: the instantiation `sem N` (`sem_eq`), the self-read guard and the one-driver rule. The execution semantics is not.

**Lines (MEASURED):**

| part | lines |
|---|---|
| `Loop2Slot` total | 264 |
| — locality (the `quiet` argument) | 115 |
| — slot and behaviours | 134 |
| `singleE_frag` | 19 |
| the slot argument, total | ≈ 283 |
| composition: `LoopTaskE` | 45 → 141 |
| `Loop2Frag`: `initLoop.meaning`/`row`/`idem`, `loop1_single` split out | +16 |
| `LoopTask`: `satisfiedAt_of_frag` | +12 |

- The slot argument is ABOVE the ~250 stop line, by 13%.
- Design-specific: `clmul` 102 → 112, `PriEnc` 82 → 91, `PopCount` 54 → 63. Each design pays for `out` as a lemma, the run2 `statement` and `statement_E0`.

**Why not `WSettles` (A's R-COMB-1, `Kernel/Core0Win.lean`, READ on `arch-x1` at `edce9ef8`).** Its theorems take Props, and the trivial rank fits (one equation reading only inputs). Two routes were checked; neither is cheaper:
- **`WSettles.ofLowerWin` is stuck at symbolic N.**
  - Its first hypothesis is `E.toDesign2.lowerWin = some ps`.
  - `Process2.lowerWin` runs `body.symExec d []`, whose `.block` arm is `Stmt2.symExecList` over the instantiated trip list `(List.range N).map T`. It has no normal form at symbolic `N`.
  - `completeWB E ps = true` and `CombDesign (winDesign ps)` are then about a `ps` that does not compute.
- **Building `WSettles` directly** needs an equation design whose `act` field says one activation writes exactly the equations' pre-state values.
  - For a loop that is one closed-form `Expr2` of the whole loop: an `N`-indexed fold term with `ifGuard` for the `if`s.
  - Its correctness proof is a symbolic `symExec`-of-a-loop lemma, and the arithmetic would then be about `evalPure2` of that term instead of the rows.
  - JUDGED: more than `SingleE`'s 134 lines of slot argument. The 115 locality lines would be needed anyway, for `complete` and `group`.
- **For A's D-X1f2:** the termination half (`step_decreases`, `slot_closes`) needs no symbolic form. What lacks one is the lowering, `symExec` over a symbolic trip list.

### 9.10 Ordinary `always_comb` style over E, sized on ibex_alu (WS3, 2026-11-03)

**What is proved** (derived from E):
- `LeanModels/Sv/CombFragE.lean` gives ordinary `always_comb` bodies their single-activation meaning over E-core-0.
  - `Stmt2.combOk d`, the fragment: blocking assignments to static in-range windows of well-formed expressions, `if`/`else`, blocks, and `case` (plain, `inside`, `unique`, `unique0`, `priority`). Any set of signals and windows may be written, in any order: defaults then overrides, an `if` after the first statement, several writes per branch.
  - `Stmt2.sem d`: the meaning, a function on the view (`SvState → SvState`), by structural recursion with E's own evaluator (`evalPure2`) and E's case matching (`caseHit`, first match, the default when nothing hits).
  - `Stmt2.sem_run`: on every typed store of an all-4-state elaboration, one `execBody` succeeds and ends in a typed store whose view is `sem` of the view. One generic proof, by mutual induction over the body, from A's `execBody`/`execArm`/`execArms` definitions. No `run2`, no fuel, no per-design composition of primitives.
  - `activate_single`: the same for `activate` of a design whose only process is the body.
- `svgolf/design/loop/x7/X7Blocks.lean`: two of the six ibex_alu blocks of X7 B.3, as sliced by M's slicer, each against a plain local spec:
  - `bwlogic_E` (block #9, `unique case (1'b1)` over two select signals): `bwlogic_result` is the OR result when `bwlogic_or`, else the AND result when `bwlogic_and`, else the XOR result.
  - `adder_flags_E` (block #0, four defaults then a plain `case (operator_i)`, four signals written): `adder_op_b_negate` is set exactly for the 13 operators of the arm's pattern list, and the three shift flags are 0 (their arms are `if (1'b0)`).
  - Each is stated on `activate (Elab.ofDesign2 x7….sem) 0 σ`, the instantiated design the envelope gives. `*_sem` checks that it is the body written in the file.

**Every hypothesis of the two block theorems:**
- The store is typed (`Typed σ`).
- The block's inputs are 2-state values: `lookup … = some (.ofBitVec …)`. This is the spec's choice, not the fragment's: `sem_run` holds on every 4-state store.
- `bwlogic_E` only: `hclaim : ¬ (o = true ∧ a = true)`, the `unique` claim.

**Qualified `case` (a divergence of E from run2, for A).**
- E-core-0 ignores the qualifier: `execBody`'s case arm binds it as `_` and runs first match (READ `Kernel/Core0.lean:334-338`, arch-x1 `edce9ef8`, the same text as at the merged `d00b2919`).
- Since master `2218821b`, `run2` makes a violated claim loud (`checkCaseObligation`).
- So on a violation E runs the first hitting arm silently, where run2 refuses. The fragment therefore asserts its meaning only where every claim on the executed path holds. `Stmt2.claims d st` (master's obligation: `unique`: one hit, or none and a default; `unique0`: at most one; `priority`: at least one, or a default) is an explicit hypothesis of `sem_run` and `activate_single`, never dropped. For `bwlogic` it is the plain hypothesis `hclaim`.
- This is the one place where E lacks a fact the fragment needs: the claim is a hypothesis because E has no check to derive it from.
- Case matching on x/z is not a gap. Plain `case` is `===` and `inside` is wildcard equality, in one function `caseHit` that E-core-0 and run2 share (READ `Sem2.lean:287`). `sem` uses the same function, so the meaning is exact on 4-state subjects and patterns.

**Where each of the other four blocks stops:**
- All six are in the fragment and are single-process designs (MEASURED by evaluation: the `#guard` at the end of `X7Blocks.lean`, not a proof). So `activate_single` reduces each one's activation to `body.sem`, given its `*_sem` check, `AllFour` (`decide`) and, for `unique`, the claim.
- None needs a fact E-core-0 lacks, apart from the qualified-case claim above. What each lacks is its plain spec of `body.sem`:
  - `adder_in_a` (#1): `unique case (1'b1)` over four selects plus a default, with concatenations of part-selects (`{operand_a_i[30:0],2'b01}`). Its claim is "at most one of the four selects is set". The value lemmas exist (`Known2.concat_ofBitVec`, `evalPure2_concat`/`_slice`). JUDGED the same size as `bwlogic`.
  - `adder_in_b` (#2): the same shape with three arms. JUDGED smaller than `adder_in_a`.
  - `shifter` (#7): two `if`/`else`, a 64-bit `>>` by a 5-bit amount, a 32-trip `for` writing single bits `shift_result_rev[i] = shift_result[31-i]`, then `shift_result` written a second time from a read of itself. It writes six signals and reads four of them after writing them. Its spec is a bit reversal over 32 instantiated trips, not written. It is also the block that shows what `SingleE` needs (below).
  - `result_mux` (#10): a default, then a plain `case (operator_i)` of 46 patterns in 13 arms. JUDGED the same technique as `adder_flags`. But that proof splits per pattern value: `af_mean`, 13 values, costs 9.7 M. 46 values is about 3.5× that, so a membership-based lemma ("the first arm whose list holds `x`") is the cheaper route.

**`SingleE` over a write set.**
- `SingleE E body I F W` now says that `F` writes only the signals `W` (`frame : ∀ st x, x ∉ W → lookup (F st) x = lookup st x`). It used to say `F st = set st n v` for one `n`.
- The loop route instantiates it at `W = [n]` (`singleE_frag`, `LoopTaskE.lean`, four changed lines). The slot theorems never used the one-signal form.
- `idem` and `quiet` stay fields. For a comb-fragment body they are not derived. The condition the lead named is the right one:
  - E-core-0's sensitivity of an `always_comb` is the body's reads minus those overlapping a window it writes (READ `Elab.sens`, `Kernel/Core0.lean:470-476` on integ1103, LRM 9.2.2.2.1).
  - If every read of a window in `W` comes after a write of that window on every path, then `F`'s result depends only on reads outside `W`, which `F` does not change. That gives `idem`, and it gives `quiet` from the sensitivity.
  - A body that reads a `W` window before writing it on some path (a latch, or `case` without a default writing a signal read later) breaks both. On such a body E's settling can take a second activation that changes the store.
- Deriving them needs two pieces: a locality lemma for `Stmt2.sem` (`frag_local`'s analogue, 115 lines for the loop fragment) and a definitely-written-before-read check over paths, with a soundness proof. JUDGED 150 to 250 lines. Together with `CombFragE`'s 245 that is past the ~300-line stop line, so it is not started. The whole-task statement (`statement_E0`'s analogue) for these blocks waits on it.

**Lines (MEASURED, code lines without comments; raw in brackets):**

| part | lines |
|---|---|
| `CombFragE.lean` (generic: fragment, meaning, claims, `sem_run`, `activate_single`, `caseHit_ofBitVec`) | 245 (325) |
| `Loop2Slot.lean` `SingleE` over `W` | +1 (18 changed) |
| `LoopTaskE.lean` | 0 (4 changed) |
| `X7Blocks.lean` (both blocks, with their extraction checks and the six-block `#guard`) | 158 (228) |

- The generic part is under the ~300 stop line. The two blocks cost about 60 design-specific code lines each, of which about 30 are the body and declaration literals that `*_sem` checks.

**Heartbeats (MEASURED, `IO.getNumHeartbeats` around each command with `Elab.async false`, as in X7/X12; M = 10⁶):**

| block | `*_sem` (extraction) | `combOk` | `AllFour` | claims | meaning (`*_mean`) | E theorem | total |
|---|---|---|---|---|---|---|---|
| `bwlogic` | 3.15 M | 1.25 M | 0.03 M | 1.97 M | 2.76 M | 0.99 M | 10.2 M |
| `adder_flags` | 5.46 M | 1.25 M | 0.03 M | 0.37 M | 9.71 M | 1.34 M | 18.2 M |

- The E part, `activate_single` instantiated, is about 1 M per block. The cost is the plain spec of the meaning, which is backend-free (`*_mean` is about `Stmt2.sem` on an `SvState`), and the front-end check.
- Measured pitfall: the first version proved claims and meaning by `simp_all` inside the E theorem, with the typed-store and activation hypotheses in context. `simp_all` rewrote them too, and `bwlogic_E` cost 49.5 M. Proving the spec on a plain view first and composing it took it to 0.99 M.
- For scale: X12's hand route for a two-arm `case` toy (B4) is 1.22 M. X7's template route is 14 to 20 M per site.

**Reproduce:** `svgolf/design/loop/x7/compile-x7.sh` with `X7SRC` (ibex at RB0's pin), `X7MEASURE` (the slicer, copied read-only from arch-measure) and `SCRATCH`. It runs the slicer, cuts the six blocks verbatim (`x7_blocks.py`, sha256-checked slice), extracts them and compiles `X7Blocks.lean`, all in scratch. No ibex code is in the repository.

### 9.11 Written before read: whole slots for ordinary `always_comb` (WS3, 2026-11-03)

**What is proved** (`LeanModels/Sv/CombSlotE.lean`, derived from E):
- **The check, `combWbr d W body`** (decidable, structural, `Stmt2.wbr`). It threads the set `D` of FULLY written signals, meaning a blocking assignment to the whole declared width.
  - Every read of a signal of `W` must find it in `D`.
  - An `if` keeps what both branches write. An `if` without an `else` and a `case` without a `default` keep only what the empty path writes, which is `D` unchanged.
  - At the end, every signal of `W` must be in `D`.
- **Locality, `Stmt2.sem_rel`.** Two states that agree on the body's reads outside `W`, both satisfying `CombInv` (the declared names at their declared widths), give the same value to every fully written signal.
- **The frame and the invariant.** `Stmt2.sem_inv` carries any property that every write keeps through the body. Its instances are `sem_frame` (nothing outside `W` changes) and `sem_combInv`.
- **`singleE_comb`.** A single-`always_comb` design whose body is in the fragment and passes the check is a `SingleE`. Its hypotheses: no signal of `W` is an input, the declared names are distinct, and `hcl` (every claim holds on every `CombInv` state).
  - `idem` and `quiet` both come from one extensionality step (`hext`).
  - `quiet` uses that every read outside `W` is in E's sensitivity (`sens_of_readW`). E-core-0's `always_comb` sensitivity drops only reads that overlap a window the body writes (READ `Elab.sens`, `Kernel/Core0.lean:470-476` on integ1103).
- **The latch.** Under E a latch is idempotent too, so the check refuses more than idempotence needs. The proof's extensionality step needs every signal of `W` written on every path, and that is `always_comb`'s intent (no latch).

**`svgolf/design/loop/x7/X7Blocks.lean`:**
- `af_singleE`: the sliced `adder_flags` design is a `SingleE` over its four outputs. Every structural hypothesis is decided by `decide`, and `hcl` holds because the `case` is plain.
- `adder_flags_slot`: from a typed opening, with the process ready or the store settled, every legal schedule closes the slot at ONE configuration. There `adder_op_b_negate` is set exactly for `negOps` and the shift flags are 0. *Derived from E.* Its hypotheses: the store is typed, the opening is ready or settled, and `operator_i` is a 2-state value.
- `bwlogic_slot`: the same whole-slot statement for `bwlogic`, *derived from E*. Its hypotheses: the store is typed, the opening is ready or settled, the five inputs are 2-state values, and `hclaim : ¬ (o ∧ a)`.
  - `hclaim` is `unique`'s claim on the opening's select inputs. It is explicit and asked of this slot only, never of every input.
  - The route is `slot_claimed` (below), not `SingleE`: the claim is about inputs, which a typed view need not keep.
  - The claim at `F` of the opening, which the possible second activation needs, comes from the frame: the selects are not written.
- The negative fixture `latch.sv` is own code: `if (en) q = d;`. `latch_sem` and `latch_ok` show it is in the fragment; `latch_refused` (`decide`) shows the check refuses it.
- `compile-x7.sh` runs end to end with exit 0 (MEASURED, 5e2e16e9 and 85b456f7).

**The claim-at-opening slot, `slot_claimed`** (85b456f7, under the lead's 40-line cap):
- It is `SingleE.slot` for a body with a qualified `case`. The claims are asked only of the two states the slot activates the body on: the opening view and `F` of it.
- Its other hypotheses are `singleE_comb`'s, without `hin`: a slot never applies inputs.
- It reuses `SingleE`'s schedule lemmas (`closes_nil`, `closes_next`, `triggered_self`) and `activate_single`, which carries the claims.
- Lines (MEASURED): 40 generic code lines net (386 → 426). The lemma itself is 32. The rest is net +8 from factoring `single_elab`, `combInv_view`, `Stmt2.sem_settles` and `Stmt2.sem_idem` out of `singleE_comb`, so both use them. `bwlogic_slot` is 21 design lines.

**Sensitivity fix, landed (A, `33dc39c8`: acg_xproc_bits, partial-overlap reads).** `Elab.sens` now appends the unwritten bits of a partly written read (`partialSens`). `quiet` needs only that every read of a signal outside `W` is in the sensitivity, and the fix removes none of them. MEASURED: the only change it needed was `List.mem_append_left` in `sens_of_read`/`sens_of_readW` (`98ebce7b`).

**Lines (MEASURED, code lines): 386 generic at 5e2e16e9 (raw 462), against the ~250 stop line; 426 with `slot_claimed` at 85b456f7 (raw 511). The table is the 386.**

| part | code lines |
|---|---|
| the check: `rdOk`, `Stmt2.wbr` and its four mutual twins, `combWbr`, `combWbr_spec` | 60 |
| `CombInv` and `CombInv.write` | 14 |
| `Stmt2.sem_inv` (a write-kept property through the body; five mutual members) | 66 |
| `sem_combInv`, `sem_frame` | 10 |
| `agree_of_rdOk`, `agree_congr` | 11 |
| `Stmt2.sem_rel`, locality (five mutual members) | 173 |
| `sens_of_readW`, `singleE_comb` | 44 |
| header lines (namespace, open, sections) | 8 |

- Design-specific: `adder_flags` slot 39 lines (`afW`, `af_singleE`, `adder_flags_slot`); the latch fixture 24.
- **Later pass, compression** (not done now; JUDGED savings):
  - `sem_rel`'s five members repeat six hypotheses each; bundling them as one relation saves about 30 lines.
  - `sem_inv` and `sem_rel` walk the same recursion; one walk would save about 40.
  - The arm/list split for case items saves about 15.

**Heartbeats (MEASURED, `IO.getNumHeartbeats` per command, `Elab.async false`; M = 10⁶):**
- Generic module, 9.8 M in all. The parts:
  - `Stmt2.sem_rel` 5.81 M;
  - `Stmt2.sem_inv` 1.65 M;
  - the `wbr` definitions 0.87 M;
  - `singleE_comb` 0.53 M;
  - everything else under 0.2 M each.
- `slot_claimed` 0.86 M; `singleE_comb` 0.28 M after the factoring.
- Design:
  - `bwlogic_slot` 2.11 M.
  - `af_singleE` 1.92 M: every structural fact by `decide`, including `combWbr`.
  - `adder_flags_slot` 1.37 M.
  - `latch_sem` 1.44 M, `latch_ok` 0.15 M, `latch_refused` 0.13 M.
- The whole slot of `adder_flags` costs 3.3 M on top of its activation proofs (18.2 M, §9.10).

**Open, a week-2 candidate (decided by the lead; under "multi-process slot over E"): every-behaviour statements for a body with a qualified `case`.** `slot_claimed` covers one slot; a behaviour is every slot.
- `SingleE.typedI` asks its invariant of every typed view. A `unique` claim is an assumption on the inputs, which a typed view need not keep.
- Statements over every behaviour (`behaves`, `pre_view`) for such a body need an environment assumption in `SingleE`: the claim holds at every slot opening and `F` keeps it. JUDGED about 35 lines. Not built.
