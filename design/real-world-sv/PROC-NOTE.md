# WP-PROC, gate G0: where do procedural loops, user functions, nets, local declarations and `always @*` get their meaning?

> **RULING 2026-11-02, which supersedes parts of this note: preserve structure.** The point of giving Lean semantics to SV constructs is
> that proofs can use the structure of loops, generate blocks and parameters. A loop must not be unrolled where a proof has to read it: unrolling a
> size-100 loop makes a mess for the prover or for `sv_equations`, and a loop with a PARAMETER bound cannot be unrolled at all (the claim is for every
> `N`). So of the extensions below, N1, N2, N3, E1, C1, X1, L1 (G1, landed: one-to-one rewrites) stand; X2 (function bodies) stands only if the
> body keeps its shape; **X3 (comb-SSA over a stage-U block) is withdrawn** (it flattens what the proof should read), and X4 (lift of a
> parameter-bound loop to a generate family with a row array) stands only as a structure-preserving rewrite, proved by induction as `clmul` is. The
> direction for G2 is tactic support for the loop itself (a fold or loop-invariant reading, the analogue of `py_vcgen`'s `inv`/`dec`), not a flatter
> lowering. Any rewrite that is kept gets the Yosys miter at sampled parameter points as a guard. Literal-bound unrolling (stage U in the extractor,
> `instStmt2`'s up-to-128-iteration `forValues2`) is acceptable for execution (`run2`), not as the shape the tactics read.

Date 2026-11-01. Base: `svgolf-prep` 15ce95cc (survey 6aacc87b + the WP-RB0 census merge), REBASED for all measurements on master 0ca14852 (the off-prem literal-loop and pure-function lowering, section 0). Read-only gate: nothing under `LeanModels/`, `extractors/`, `harness/`, `svgolf/check*` or `svgolf/score/` is edited by this gate (the measurements use throwaway patches of the extractor applied to scratch copies, never committed: `proc/*.patch`, section 0).
Everything marked MEASURED was run; everything marked READ was read off the sources; everything marked JUDGED is my estimate. The scripts and the measured inputs are in `proc/` next to this file (`proc/README.md`; the census driver reads the survey's scratch directory, the reach tables run from the committed data).

## 0. Recommendation in one page

*Rebased on master 0ca14852 (2026-11-01 17:50), which already contains the off-prem agent's literal-loop and pure-function lowering (7f7c1e02 `unroll literal symbolic for loops`; f6ecaf7d, a50b50bf, d3b3d1d8, 94aaec34, 1cd09e76, 9dbf8a81 pure user-function materialisation / inlining / conditional return). My first draft of this note predated them; every number below is re-measured on master, and the recommendation is reshaped as EXTENSIONS of that lowering (same extractor, same tags, same register rows, no second lowering of one construct).*

**Recommendation: extend the off-prem lowering; add one module (`extractors/sv/lower_proc.py`) and delegating hunks of a few lines; no Lean change for G1 or G2.** Architecture in two stages:

* **Stage U (exists, off-prem; I do not touch its semantics): unroll and inline to PROCEDURAL form.** A literal-bounded loop becomes a nested `Block` (`symbolic_for_unrolled`), a pure function a substituted expression (`user_function_inline`). Both stay in `Stmt2` vocabulary, so Lean's own `run2`, the self-read guard and the differential harness give them their meaning, 4-state faithful for free. This is the right answer for "where do loops get their meaning" wherever the trip count is a literal.
* **Stage S (new, mine): comb-SSA to assigns and single-window phi trees, plus the LIFT of parameter-bound loops to generate families.** Stage U's blocks are accepted by the loader but are multi-statement `always_comb` bodies with self-reads, which the tactics refuse today (S1b gate d / "SSA reads" are WP-G's roadmap); stage S turns them into the shapes the tactics read (measured, section 6.2). Stage S takes stage U's output as its INPUT and is checked against it: both envelopes come from the same source, so `run2(stage U block)` is a Lean-evaluable oracle for `run2(stage S lowering)` on random 4-state vectors, on top of the Xcelium rows the off-prem agent already pinned for stage U.

**What I would add (all extensions of existing code or register rows):**

| id | extension | where it plugs in | measured need |
|---|---|---|---|
| N1 | typeless / implicit-type dimensions (`ImplicitType` syntax) | `_dtype_sym`, one tuple | typeless ports: RB0's top loader blocker; ONE line (measured) |
| N2 | `wire` / `output wire` / implicit nets as variables, with symbolic driver-coverage; `wire x = e;` = `logic x; assign x = e;` | `convert_net_sym`, `convert_port_sym` (delegate to `lower_proc`) | 24 + 26 survey files carry `NetSymbol:net-z`/`PortSymbol:net-z` on master |
| N3 | `topModules = {T}` in the default compilation | `_sym_top_compilation`, 3 lines | RB0: 8 blocks cannot select their top |
| E1 | `always @*` / level-sensitive lists as `always_comb` under R1 to R6 | `convert_procedural_block` | 25 files `ImplicitEventControl` on master |
| C1 | compound assignment and `x++`/`x--` statements in sym mode | `_convert_compound_assignment` sym branch + `_convert_selected_leaf` (3 lines; the M0 path already has the `LValueReference` read hook) | `p ^= a << i` is `AssignmentExpression:compound` on master even inside a literal loop (m2, m11 below) |
| X1 | loop-header forms their `_sym_for_values` refuses: iterator declared OUTSIDE the header (Verilog-2001 `integer i;` + `for (i = 0; ...)`), compound step `i += c`; erase the iterator's dead declaration | `_sym_for_values`, `_sym_for_delta` (about 15 lines) | m3b; 37 of 65 open loop nodes (before the sequential ones are removed) |
| L1 | block-local declarations hoisted to module-level variables with unique names | `convert_procedural_block` | `LocalDecl` is refused by the loader (m7) |
| X2 | function BODIES (locals, several statements, loops): bind formals with their `_SymCallBinding`, convert the body as a region, hoist the temporaries; plus two shift-friendliness additions to their substitution (a compound actual is materialised as a signal, literal-only subtrees such as `32 - n` are folded) | `_sym_inline_function_call` falls through to `lower_proc.inline_body` when its single-return form does not apply | 14 of the 30 loop/function-only survey files (largest class left); chacha `rotl` is clean on master but `(d ^ ra) << 16` has an operation as a shift operand, which the tactics refuse |
| X3 | stage S: comb-SSA over a stage-U block (flat SSA netlist, single-window phi trees named `<var>__<n>`) | `convert_procedural_block`, one post-pass call | tactic readiness of every unrolled block |
| X4 | LIFT of parameter-bound loops: their binding machinery with a `GenvarRef` instead of an `Int` yields a retained `SymLoop` node, stage S emits the generate family with row arrays | `_convert_stmt` ForLoopStatement sym branch, 6 lines (the `plan is None` case) | 36 of 42 remaining open loop nodes are parameter-bound |
| F1 | svGolf: fourstate loop-interval rule, function-local uninitialised read rule, `$dlatch` assertion; the lowering-check (Yosys miter) stage | `svgolf/score`, `svgolf/check` (separate commit) | policy: "rule first" |

**What I would NOT redo:** the literal unroll (`_sym_for_values`, `_SymLoopBinding`, the `symbolic_for_unrolled` block), the pure single-return function inliner (`_sym_inline_function_call`, `_SymCallBinding`, tag `user_function_inline`, conditional return with the `Squash2` condition), their differential rows (`sem2/for_unroll`, `symbolic_*_function`), the register rows `st-for` and `ex-user-call` (I extend their `why`/`prerequisite` and `kinds`, as they did), and the stage-U output vocabulary. If WP-G's tactic-side SSA reads land first (Q3), stage S for LITERAL loops becomes unnecessary and I drop X3 for them; X4 (parameter-bound loops) is independent of that, because Lean has no loop to execute.

**Not in the off-prem commits (verified on master by micro-designs and by the survey):** wire / implicit nets, `always @*`, the typeless-port dimension recovery, `topModules`, compound assignment in sym mode, block-local hoisting, parameter-bound loops, function bodies with statements (section 0.1).

### 0.1 What master closed and what it did not (MEASURED on 0ca14852, `proc/micro/m*.sv`, extractor level)

| idiom | master | note |
|---|---|---|
| m1 literal loop, `p = p ^ (a << i)` | clean | closed by the unroll |
| m12 literal popcount loop `c = c + a[i]` | clean | closed |
| m2 literal loop with `p ^= a << i` | `AssignmentExpression:compound` | open (C1) |
| m11 `y ^= b; y += 1;` | `AssignmentExpression:compound` | open (C1) |
| m3/m3b module-level `integer i;` iterator | `VariableSymbol:signed` (+ `ImplicitEventControl` / `ForLoopStatement`) | open (X1, N-signed wall on the declaration) |
| m4 parameter-bound loop | `ForLoopStatement` + a leftover `LocalDecl` | open (X4) |
| m5 function with a local and a loop, m6 function with a local and two statements | `CallExpression`, `SubroutineSymbol:Subroutine` | open (X2) |
| m10 `rotl` as one assignment, m13 call inside an `always_comb` statement | clean | closed by the pure inliner (but the shift operand is an operation, section 6.1) |
| m7 block-local `logic t1` | clean at the extractor, `LocalDecl` for the loader | open (L1) |
| m8 `always @*`, m9 `wire [7:0] t = a ^ b` | `ImplicitEventControl`; `packed: null` | open (E1, N1/N2) |

Not in the table because they are semantic rather than extractor questions: bit-indexed writes and reads in unrolled loops (`y[i] = a[i]`, `b[i]`) are closed for `run2` (their `sem2/for_unroll` row: disjoint windows, `Int` indices); read-modify-write of a block variable and partial writes are closed for `run2` too (`Stmt2` executes them, the guard admits write-then-read) and OPEN for the tactics (S1b gate d refuses multi-window bodies, `noSelfRead` refuses the read of the written window: stage S or WP-G's SSA reads).

How much of survey gaps 1, 2 and 4 the off-prem commits closed on the 216 real files (files whose envelope still carries the kind; the extractor of the base before the rebase -> master, same files, no patches): `ForLoopStatement` 40 -> 31, `SubroutineSymbol:Subroutine` 52 -> 49, `CallExpression` 43 -> 41, files with a `LocalDecl` 33 -> 27 (the declaration sat inside a loop that is now unrolled), clean files 23 -> 25. So the off-prem lowering removed the loop refusal from about a fifth of the loop-bearing files and the function refusal from a sixteenth of the function-bearing ones, and moved two files from refused to clean: it is a correct and narrow first step, and the remaining shapes are the common ones (parameter bounds, function bodies with state).

**Measured reach on master.** "Clean" = the extractor envelope has no `Unsupported` node, no `LocalDecl` and no `packed: null` declaration. The G1 columns are MEASURED with a throwaway patch of master's extractor that implements the G1 lowerings WITHOUT their admission checks (`proc/g1_upper_bound_hack.patch`; with the cheap loop/compound extensions C1 and X1 on top: `proc/h2_loop_compound_hack.patch`), so they are upper bounds; the last column adds every file whose only remaining obstacles are loop/function kinds and which passes a statement-level census (upper bound for X2 to X4).

| population | master today | + N1, N2, N3, E1 | + C1, X1 | + L1 | + function bodies, lifted loops (<=) | what the off-prem commits gave |
|---|---|---|---|---|---|---|
| survey real files (216 self-contained) | 25 | 67 | 68 | 73 | **93** | +2 (23 -> 25) |
| RB0 CPU blocks (82 as-is rows) | 14 | 34 | 34 | 34 | **39** | 0 |
| survey probes (240 extracted) | 149 | 169 | 172 | 175 | **194** | +9 (140 -> 149) |

The off-prem lowering is real but narrow for real code: most real loops have parameter bounds (36 of the 42 loop nodes still refused on master with C1/X1 applied), and most real functions have locals or several statements (49 files still carry `Subroutine` on master). G1 is where the reach is (+42 survey files, +20 CPU blocks, +20 probes), then X2 to X4 (+20 survey files, of which 14 function-body files and 5 to 6 parameter-bound loops).

At the loader level RB0's own funnel counts 12 of 82 blocks accepted by `load_design_sv2`; the register-row model of section 2.3 gives the same +20 / +5 shape.

**One thing the lowering cannot fix, measured**: the tactic recognizer refuses a shift whose amount is a genvar (`shOpdRd?`: only a signal access, a sized literal or an unsized constant), and, on master, the pure inliner leaves a compound actual as the shift operand. The natural `if (b[i]) p ^= a << i` loads and scores but is outside the tactic fragment for a PARAMETRIC N (literal-bound loops unroll to literal amounts, which are inside). One recognizer case (REPORT, not mine), section 7.3.

**Gate plan**: G1 = {N1, N2, N3, E1, C1, X1, L1}, about 4.5 working days; G2 = {X2, X3, X4, F1 including the lowering-check}, about 10 working days (JUDGED, section 9).

## 1. What is refused today, layer by layer (MEASURED)

The same source construct dies at several independent layers; a fix has to clear all of them.

| layer | what stops it | evidence |
|---|---|---|
| source gate | directives, `unique`, attributes (not mine) | RB0: 47 of 78 real primary files fail it |
| extractor (sym mode) | on master: `ForLoopStatement` with a non-literal header (parameter bound, iterator declared outside the header, compound step, more than 128 iterations) -> `Unsupported` carrying only the TEXT of the loop (master unrolls the literal single-`int`-iterator form, 7f7c1e02); `AssignmentExpression:compound` (`_convert_compound_assignment`: `_SYM is not None` -> unsupported, even inside a literal loop); `TimedStatement:ImplicitEventControl`/`EventListControl`; every user function except the pure single-return forms master now inlines (locals, several statements, loops stay `CallExpression` + `SubroutineSymbol:Subroutine`); `NetSymbol:net-z` / `PortSymbol:net-z` (`_sym_net_z`) | `proc/micro/m*.sv` run on master (section 0.1); envelope of a parameter-bound clmul loop: `Block{LocalDecl i, Unsupported ForLoopStatement(text only)}` |
| extractor, declaration shape | typeless / implicit-type declarations (`input [N-1:0] a`, `wire [N-1:0] x`) get `packed: null` because `_dtype_sym` recovers dimensions only from `BitType`/`LogicType`/`RegType` syntax | `q__g02`, `q__v03` envelopes |
| loader | `LocalDecl` statement has no arm in `Ingest2.parsePStmt` ("unknown statement kind", whole envelope rejected); `packed: null` -> `unrecoverable packed dimensions` (RB0: 25 blocks, the same 25 as `dc-net-z`) | register `ld-localdecl`, RB0 section 5 |
| tactics | multi-window / self-reading `always_comb` bodies; shift amount = genvar; replication; literal-width part-select; 3-D packed | PROVING.md section 4, `CombView.shOpdRd?` |
| svGolf fourstate | a procedural loop counter is a run-time `int` index, so `b[i]` is refused (`sg-fs-loop-index`, rule (d): "a PR that admits loops should teach this rule loop bounds"); function-local reads before assignment are an x source with no rule yet (README Rules, `fn_uninit.sv`); `always @*` that latches is silent in Yosys `proc` | `fourstate.py` header, probes c05 to c09, x20 |
| Yosys 0.53 | `return`, `break`, `while` outside constant functions, `foreach`, automatic locals in `always_comb`, `import` cannot be read AT ALL, so such a design cannot be scored whatever ls-sv does | survey section 3 |

Consequence for scope: `return`-style functions and `break` loops are unscoreable; the lowering only needs name-assignment functions and counted `for` loops.

## 2. Reach: three populations (MEASURED)

### 2.1 Survey real files (216 self-contained of 440 extracted; the survey's own count is 213 under a slightly different filter)

Measured on master with the throwaway patches (section 0): 25 clean files today; 67 with N1/N2/N3/E1 (upper bound); 68 with C1/X1; 73 with L1; at most 93 with function bodies and lifted loops (`proc/run_hack.py`, `proc/run_hack2.py`). What is left in the 30 files whose only obstacles are loop/function kinds (master + G1 + C1/X1): 14 function-body files, 5 parameter-bound-loop files, 1 with both, and 10 that the statement census refuses (`break`, `while`, non-counted loops, NBAs). Of the 42 `for` nodes still refused 36 have parameter-dependent bounds. The tier MODEL below was computed on the extractor of the base before the rebase (23 clean files, model T4 97), reads only Unsupported KINDS, and is kept as a cross-check; the loop and function census describes the population and is unaffected by the rebase.

Tier model: a file is accepted at tier T iff every `Unsupported` kind of its envelope is covered by T, every loader-refused node (`LocalDecl`, `packed: null`) is covered, and (for the loop/function tier) a pyslang statement census of every comb-style block and function passes the admission predicate of section 4.1 (`proc/scan_proc.py`, `proc/reach.py`).

| tier | accepted | by topic |
|---|---|---|
| T0 today (no Unsupported, no LocalDecl, no `packed:null`) | 23 | arx 3, fpdiv 5, sbox 2, bitops 11, arith 1, alu 1 |
| T1 + typeless dims + `wire` | 61 | + clmul 3, arx 4, fpdiv 7, sbox 18, hashround 7, bitops 16, arith 2, alu 4 |
| T2 + `always @*` / level lists | 78 | sbox 23, arx 9, fpdiv 10 |
| T3 + local declarations | 79 | |
| T4 + loops / functions | **97** | clmul 7, arx 10, fpdiv 10, sbox 30, hashround 11, bitops 18, arith 3, alu 8 |

Caveat: these are UPPER bounds. A file whose only Unsupported kind is `ForLoopStatement` may still hide an unsupported construct inside the loop text (the envelope carries the text only). The statement census removed 12 files at T4 for `break`, `while`, non-counted loops, NBAs, concat targets; further expression-level obstacles (`$countones`, struct members, casts inside loop bodies) are only seen once the lowering runs: expect a 20 to 30 percent shortfall on the T4 step (JUDGED; the probes below are the calibration).

Loop census of the same 216 files (pyslang, default point): 63 files contain 296 `for` loops; 286 are counted loops (literal or parameter-affine start and bound, step +-1); 52 of the 63 files have only such loops and no `break`/`while`; **31 files keep their loops only in comb-style blocks** (`always_comb`, `always @*`, functions), the rest are in `always_ff`/sequential blocks (not mine). Subroutines: 167 in 50 files (157 functions, 10 tasks); 21 use `return`, 28 contain a loop, 12 have output/inout arguments, only 1 calls another user function; 110 are static, 57 automatic.

### 2.2 The 241 reduced probes

Extractor level on master, measured with the same patches: 149 clean today (140 before the off-prem commits), 169 with N1/N2/N3/E1, 172 with C1/X1, 175 with L1, at most 194 with function bodies and lifted loops (`proc/run_hack_probes.py`). The off-prem commits flipped 11 probes (`x20` the literal popcount loop; `p06`, `x03`, `f11`, `k05` pure functions; six Yosys-readability probes of the y series) and the new `SlangError` marker un-cleaned two (`p30`, `w02`: programs slang rejects). Pipeline level BEFORE the rebase (177 run through `check.py --unproved --tactics` on the earlier extractor): 101 reach the design stage accepted, 39 of them in the tactic fragment; 51 stop at `design`, 18 at `fourstate`, 5 at the source gate, 2 at `extract`. Applying the tier model to the 240 that extract gives 54 extractor-level flips; triage by reading each (the y/z series are Yosys-readability probes, `g21` is a source-gate case, `$countones` is a system call, not inlinable): **34 real design-stage flips**: 17 `wire`/typeless (`f17 g02 s01 s02 s03 v01 v02 v03 v06 v07 v08 v11 v12 v13 v14 x10 p12`), 1 non-ANSI with event list (`p23`), 1 `@*` (`f06`), 2 local declarations (`f07 p11`), 13 loops / functions (`c05 c06 c08 c09 p01 p04 p05 p06 p_for_clmul f01 x20 x03 x09`); plus 2 package-qualified function probes (`f11 k05`) that an inliner reading the callee symbol would also take.

### 2.3 RB0: 79 real CPU blocks (second population; `rb0/census.json` blockers by register row)

Measured (RB0's `census_extract.py --repo` pointed at a scratch copy of the extractor with the G1 patch): of the 82 as-is rows 14 are clean today and 34 with dims + nets + `@*` + `topModules` (all 82 extract; 8 failed to select their top before). Master's own commits move this population by 0 (14 clean before and after the rebase), and C1/X1 by 0. What is visible afterwards, per block that is still not clean: `ForLoopStatement` 21, `LocalDecl` 16, concurrent-assert `always` 13, `UninstantiatedDef` 12, `CallExpression` 11, `AssignmentExpression:target` 10, `Subroutine` 9, explicit casts 9. Loops and locals were HIDDEN behind the `@*` blocks they sit in (that is why the register-row model below gives them only +1): with loop/function kinds allowed the count is 39 (+5: `biriscv_exec`, `hazard3_onehot_priority`, `hazard3_priority_encode`, `hazard3_shift_barrel`, `ot_prim_leading_one_ppc`); the rest need packages, unpacked arrays or multi-file support. The register-row model:

A block is "freed" at tier T iff its blocker set is non-empty and a subset of the rows T lowers (`proc/reach.py`; blockers hidden behind the loader's first message are not seen).

| tier | newly freed | blocker-free in all |
|---|---|---|
| already clean | | 6 |
| T1 `ld-init-expr` + `dc-net-z` | 7 | 13 |
| + `x:top-instantiated` (`--top` of an instantiated module: slang `topModules`) | +8 | 21 |
| + `pr-implicit-event` | +6 | 27 |
| + `ld-localdecl`, `le-generate-decl` | +1 | 28 |
| + `st-for`, `st-compound`, `ex-user-call`, `dc-member-kinds` | +1 | 29 |

The remaining 50 blocks are stuck outside this WP: `le-param-package` 16, `dc-unpacked` 11, `hi-uninstantiated` 9, `st-assign-target` 9, `pr-concurrent-assert` 9, `ld-initial-syscall` 8, `cv-explicit` 8, `le-const-context` 8. CPU datapath code has few loops; RB0's own note says the same.

### 2.4 Reading the three together

* The two populations agree on the cause and differ on the weight: nets / typeless dims first, `always @*` second, loops and functions third for CPUs and first for the golf kernels (function bodies and parameter-bound loops: +20 survey files on top of master).
* G1 is therefore not "the cheap leftovers": it is where the reach is (measured on master: +48 of +68 survey files, +20 of +25 CPU blocks, +26 of +45 probes, counting N1 to L1 as G1).
* RB0's trap is confirmed and adopted: the right lowering of `wire x = e;` is `logic x; assign x = e;` (a net declaration assignment is a continuous assignment, an initializer runs once at time 0).

## 3. The options, with evidence

### 3.1 Option B: semantics in Lean (Stmt2 `for`, calls, locals + loop reasoning in the tactics)

What exists: `Stmt2` has no loop (`Sem2.lean` 198 to 209); `Comb2Proc.symExec`/`Design2.lowerComb` is a PROVED lowering of loop-free `always_comb` bodies to assigns (single window today, S1b multi-window and S3 case/override landed or in flight, "SSA reads of the written window" and "temporaries" are named follow-ups in `G25-NOTE.md`). A loop would need: a `Stmt2.forLoop` + instantiation-time unrolling in `Param2.instStmt2` (cheap, and gives `run2` and the post-synthesis check a faithful loop), but the PROOF side then needs the tactic to execute one iteration symbolically against a state parametrised by the iteration index and to emit an induction principle for the loop-carried windows. That is a new layer in `Comb2Proc` (frames, windows indexed by affine expressions of the loop variable, a loop invariant interface). Function calls need frames and a 4-state rule for unassigned locals in Lean.

Cost (JUDGED): 2 to 3 weeks for loops with a usable tactic story, 1 week for calls; every proof file that goes through `symExec` is in the blast radius; RB0's own effort guess for `st-for` and `ex-user-call` is `L` (several PRs). Faithfulness: the best (the semantic object is the loop itself; the proved `lowerComb` theorems extend). I do not recommend it as the first route; I do recommend keeping it open as the long-term replacement for the loop-free SSA half (section 10, Q3).

### 3.2 Option A: extractor lowering (precedent: genvar `i = i + 1`, binary `~^`)

The precedents are pure rewrites inside `extract.py` (`_genstep`; the `~^` desugaring, with `test_xnor_lowering.py`) and, since this afternoon, the off-prem unroll and pure-function inliner of master, which are the closest precedent and the base this note extends: they convert the loop body once per iteration with the iterator bound to an `Int` (`_SymLoopBinding`, read in `_sym_named_value`) and substitute function actuals by symbol (`_SymCallBinding`), so the output stays in `Stmt2` vocabulary and Lean's own semantics gives it meaning. What is new in this note is size and state: SSA renaming, hoisted declarations, lifting and statement-bodied inlining are not point rewrites, so the trusted code grows by roughly 1500 lines in `lower_proc.py` plus ~650 lines of svGolf checks (JUDGED) and the equivalence argument becomes a per-construct theorem-by-test (section 5). Mitigations that make it acceptable: a separate module, emission of existing vocabulary only, monotone application, 4-state-preserving phi trees, the stage-U block as a Lean-evaluable oracle, and the per-design formal miter.

Evidence that the target shapes are already inside the pipeline: the hand-written chain `r16_xor_chain_gen_acc_if` (`logic [N:0][N-1:0] acc; for (genvar i...) always_comb if (b[i]) acc[i+1] = acc[i] ^ a; else acc[i+1] = acc[i];`) is design-accepted and `in_fragment: true` in the survey run (`sv_structure` only); `add_proc` is the same cell on a bit with a full tactic proof (`PROVING.md` section 13). The extractor's M0 mode already converts `For`, compound assignment and the `Resize`d shift (`p ^= a << i` -> `p = p ^ (Resize15(a) u<< i)`), so expression conversion is reusable; only statement-level lowering is new.

Spike (reverted): adding `SyntaxKind.ImplicitType` to the tuple in `_dtype_sym` recovers the packed dimensions of typeless ports and implicit-type nets. After it, `input [N-1:0] a` loads with `packed` of one dimension, and `wire [N-1:0] x` surfaces as the extractor's own `NetSymbol:net-z` instead of the loader's `unrecoverable packed dimensions`. So the typeless half of RB0's #1 blocker is ONE LINE and the net half is the driver-coverage analysis the register already names as its prerequisite.

### 3.3 Option C: what master already is, plus the extensions I recommend

Master's unroll is Option B's cheap half realised on the extractor side: the loop's meaning is Lean's (the unrolled block is executed by `run2` with `if`-on-x and the self-read guard), and no loop reaches the tactics. The recommendation is to keep that as stage U and add stage S next to it:

* Stage U stays as is and is extended only where its admission is narrower than real code needs (C1 compound assignment, X1 header forms, X2 statement-bodied functions, L1 hoisted locals): those are extractor-side spellings the loader does not read.
* Stage S (X3, X4) turns a stage-U region into the shapes the tactics read: straight-line `Assign`s and single-window `AlwaysComb` if/case trees, generate families with row arrays for parameter-bound loops. It is optional per region and takes stage U's JSON as input, so that `run2(U) = run2(S)` is checkable in Lean on any source (section 5.3).
* The Lean side is not touched. Optional asks (REPORT only): the recognizer's genvar shift amount and its family-row accesses (7.3), a `LocalDecl` arm in `Ingest2` (would make the hoist unnecessary), the cache-key line in `check/envelope.py`.

Why not "B for the SSA half": WP-G is extending the PROVED `lowerComb` with SSA reads and temporaries (their listed next steps). When that lands, a stage-U block of a literal loop is exactly its input, and stage S for literal loops (X3) becomes redundant; I would then keep stage S only for the parameter-bound lift (X4), which has no Lean counterpart because `Stmt2` has no loop. Until then stage S is the stopgap that makes unrolled loops provable, and it is the only route for parameter-bound loops either way.

## 4. The lowering, precisely

Module: `extractors/sv/lower_proc.py` (new). Hook sites in `extract.py`, each a delegating hunk of a few lines, sym mode only, placed next to the off-prem code they extend: `_dtype_sym` (N1: one tuple), `convert_net_sym`/`convert_port_sym` (N2), `_sym_top_compilation` (N3), `convert_procedural_block` (E1 `@*`; L1 hoist; the stage-S post-pass call X3), `_convert_compound_assignment` sym branch and `_convert_selected_leaf` (C1; the leaf hook already substitutes the compound read in M0 mode and returns `None` in sym mode), `_sym_for_values` / `_sym_for_delta` (X1: initializer-form iterator, compound step), the `plan is None` branch of the ForLoopStatement case in `_convert_stmt` (X4: bind the iterator to a `GenvarRef` through `_SYM_LOOP_BINDINGS` and retain a `SymLoop` node), and `_sym_inline_function_call` (X2: fall through to `lower_proc.inline_body` when the single-return form does not apply; two additions to the substitution). The substitution of every region variable READ happens through the hook that already exists (`_sym_named_value`, by slang SYMBOL, never by name: a block-local `t` shadowing a module `t` is unambiguous). Stage S itself is a pure function from envelope JSON (a stage-U `Block`, a `SymLoop`, a function body) to envelope JSON: no pyslang, so it is unit-tested on literal dicts and its output can be rendered back to SV (6.3). All state lives in a context object saved and restored per module like `_SYM`.

### 4.1 Admission (everything else is refused with a message naming the construct; the register gets one row per refusal reason)

A *region* is an `always_comb` / admitted `always @*` body, or a function body at one call site.

* (S) statements: `begin..end`, local declaration WITHOUT initializer, blocking assignment (simple, compound `op=`, `++`/`--` as a statement), `if/else`, plain `case` (constant items; no `inside`/`unique`), counted `for`, empty. Refused: `while`/`do`/`repeat`/`forever`/`foreach`, `break`/`continue`/`return` (Yosys cannot read most), `disable`, nonblocking assignment, event/delay control, tasks, system tasks other than the pure functions the extractor already folds.
* (T) targets: whole variable; bit / part select whose indices are affine in parameters and enclosing loop variables (a run-time or non-affine index is refused: the driven window must be known); no concatenation targets, no struct members, no unpacked arrays.
* (A) definite assignment, per bit window, decided with AFFINE interval arithmetic over the parameters (never by evaluating at the default point: the default-point fold hazard of `_sym_*point_dependent`; where affine reasoning cannot decide, refuse): every module-level variable written by the region is written on every path (else it is a latch); every region-local and function local is written before it is read on every path. This is exactly the fourstate rule (e) / USERFN requirement, enforced twice (here and in `fourstate.py`).
* (G) the `CombGuard2` read-before-write rule, so that whatever the lowering admits the Lean guard would also admit on the original.
* (L) loops: `for (T i = c0; i REL bound; step)`, `REL` in `< <= != > >=`, step `i++ i-- i=i+c i=i-c i+=c i-=c` (master accepts the first four; `i+=c`/`i-=c` is X1), the iterator declared in the header or (X1) a module-level / block-level variable that is only ever an iterator (then its dead declaration is erased), not assigned in the body, not read after the loop; `c0` and `bound` affine in parameters and enclosing loop variables. Decision *unroll vs lift* is SYNTACTIC: `c0` and `bound` mention no parameter -> stage U (master's unroll, at most 128 iterations; the budget is one constant); otherwise lift (X4). A value-based decision would make the `--probe-points` cross-check differ between points, which is exactly why master's `_sym_for_values` refuses parameter bounds instead of unrolling them at the default point.
* (F) functions: `function` (not `task`), non-recursive, input arguments only, result assigned by `fname = e` (a `return` is accepted only as the last statement of the body, because it is rewritten to that, and the design is then unscoreable anyway); locals not used across calls; body admitted by (S), (T), (A), (L); static and automatic lifetimes coincide because every local is written before read. Package-qualified callees are read from the callee symbol.

Admission is monotone: a region with none of {loop, call, compound, `x++`, local decl, `@*`} is not touched, so every row admitted today keeps its envelope byte for byte (`diff_test2 --golden` on the touched rows is the acceptance check).

### 4.2 Nets, typeless declarations, `@*`, locals, compound (G1)

**N1 typeless dimensions.** `_dtype_sym` also recovers packed dimensions from `ImplicitType` syntax (ports, nets, non-ANSI body declarations, `reg [..] y;` re-declaring a port). One line plus tests (spike above).

**N2 nets.** A `wire` becomes a `Var` (an `output wire` an `out` `Port` with recovered dimensions) iff its net type is plain `wire` and *every bit has exactly one continuous driver*: a whole-net `assign`, a declaration assignment, windows of `assign`s whose union covers the declared range (affine interval union over the parameters), a generate-for of bit/part assigns covering the range, or an instance output connection; two drivers on a bit (resolution), a partially driven net, `tri*`/`wand`/`wor`/`supply*`/`trireg` stay refused with today's message. Under that condition net resolution is the identity and `z` is unreachable, so a variable with a continuous driver is the same object; this is the register's own prerequisite ("driver-coverage analysis"), implemented symbolically so that all parameter points agree. `wire [w] x = e;` -> `Var x` + module-level `Assign x = e` at the declaration's position (NOT an initializer). Implicit nets (`assign y = a;` with `y` undeclared, `default_nettype wire`) are 1-bit nets of the same kind. `input wire [..] a` needs only N1 (input net ports are already admitted: the instantiating scope drives every bit).
Fourstate: nothing new (rule (e), Yosys `check`, already refuses an undriven bit that is used).

**N3 `--top` fix** (RB0 finding 3): pass `topModules = {T}` to the slang `CompilationOptions` so a module instantiated elsewhere in the same sources can be the top (8 RB0 blocks). Three lines, its own tiny commit.

**E1 `always @*` / `always @(a or b or ..)`.** IEEE 1800 9.2.2.2.2 lists exactly three differences between `always_comb` and `always @*`: `always_comb` runs once at time zero, is sensitive to the contents of called functions, and forbids other processes to write its targets; R3, R4 and R6 below are those three, R1/R2/R5 are the shape of the block. Converted like `always_comb` iff (R1) no edge term, no `iff`, no delay/event control in the body; (R2) the sensitivity set is the read set: implicit lists by definition, explicit lists must CONTAIN the base signal of every read (a subset is refused: simulators wake on the list, Yosys synthesizes the function, a tools split), selects in the list are refused; (R3) the read set is not empty and contains no 2-state (`bit`/`int`) signal: an `@*` block does not run at time zero, so a block that reads nothing that can change would leave its outputs x in a simulator while ls-sv computes them (a 2-state input that is driven to its initial value produces no event either); (R4) a called function that reads a module signal it does not receive as an argument is refused (Verilog-2001 `@*` does not wake on those reads, `always_comb` does; again a split); (R5) full definite assignment (Yosys `proc` infers a latch SILENTLY for `@*`, where `always_comb` is an error), and the `CombGuard2` guard runs on the converted body because it becomes `Process2.alwaysComb`; (R6) no other process writes a target (slang's `MultipleAlwaysAssigns` does not fire for `@*`; the extractor's overlapping-driver check and Yosys `check` do). Register: `pr-implicit-event` prerequisite ("4-state rule for the initial x of a level-sensitive block") becomes R3, enforced in the extractor; `fourstate.py` gains a Yosys assertion that no `$dlatch`/`$adlatch` exists after `proc` (so an `@*` latch is refused at the original text as well). Open time-zero race (which tool sees a time-zero input change) is a test-bench property; the Xcelium rows apply stimulus after time zero like every row, and the row set pins one `@*` with a time-zero stimulus as a DECLARED observation, not a claim.

**L1 block-local declarations.** `begin : lbl  logic [w] t; ... end` in a region -> module-level `Var` named `<lbl>__t` (unnamed block: `blk<k>__t`, k = index of the lowered region in module order), initializer refused (a static initializer runs once; refusing is exact), declaration order preserved, uniqueness by appending `_` against all module names. Loop variables are not hoisted (consumed by the loop lowering). Generate-local declarations are an array hoist and belong to G2 (section 4.4).

**C1 compound assignment, `x++`/`x--` statements (loop-free).** `x op= e` -> `x = x op e` with the operands exactly as slang bound them (`expression.right`, whose left operand is an `LValueReference` placeholder: the converter prints the target read there), `x[idx]` targets only with a selector that is side-effect free and evaluated once (constant, genvar or loop variable, or a plain signal read; anything else refused, as M0's capture machinery is not reproduced). The loader executes the result natively (`blockingAssign y (y ^ b)` after `y = a` passes the guard).

### 4.3 Stage S: the comb-SSA core and the lift (G2: X3, X4)

Input: the envelope JSON of a region as stage U leaves it (an `AlwaysComb` whose body is a `Block` of `BlockingAssign` / `If` / `Case` / nested unrolled `Block`s over module-level names, plus `SymLoop` nodes for parameter-bound loops and `LocalDecl` nodes already renamed unique by L1); output: `Var` declarations and `Assign` / `AlwaysComb` / `GenerateFor` nodes. The pass applies only to a region that contains a stage-U marker (`symbolic_for_unrolled`, `user_function_inline` with a statement body, a hoisted local, a `SymLoop`); every other `always_comb` is left byte for byte. Reads are renamed on the JSON (`Ident`, `BitSel`, `PartSel`, `ArraySel` carry the name; a closed list of node kinds, any other kind that mentions a signal refuses the region), which is unambiguous because stage U/L1 make every name in the region unique.

Abstract state: for every variable `v` of the region, a list of *definitions* `(window, signal-or-family)`; a read of `v[w]` resolves, newest first, to the definition whose window contains `w` (a read that straddles definitions builds a concat of slices; one that reaches a never-written bit is an uninitialised read: refused by (A)). Statements:

* `v[w] = e` (straight line): new signal `v__n` (the n-th definition of `v` in execution order), `assign v__n = merge(old, w, e)`; for a whole-variable write `merge = e`; for a window write `merge = {old[hi:w.hi+1], e, old[w.lo-1:0]}` (`old` is the previous definition; constant windows after unrolling, affine slices inside lifted loops).
* `if (c) S1 else S2`: lower `S1` and `S2` against copies of the state, then for every variable `v` written in either arm one *phi*: a single-window `always_comb` tree `if (c) v__n = <v at end of S1> else v__n = <v at end of S2>`, where the leaves are SSA signals (possibly the incoming definition). `case` is the same with a `case` tree (default required: it is the latch rule). A phi is NEVER a `?:` (section 5.2).
* the last definition of a module-level variable is renamed to the variable itself (the port keeps driving the original name; `p__1 .. p__{n-1}` are the intermediates). Region-local variables keep `__n` names throughout.
* *Unrolled loops* arrive already unrolled from stage U (iterator = `Int` of 32 bits, so `i - 1` at `i = 0` is -1 and an index of -1 is the out-of-range read x, exactly as in the loop); stage S turns the straight-line block into a flat netlist (the `aes_sbox` fast path of the tactics).
* *Lift* (parameter-dependent bound): the body is executed ONCE with the loop variable bound to the genvar; each loop-carried variable `v` gets a packed row array `v__n` with `N + 1` rows (`row 0` = incoming definition, `row N` = outgoing), each iteration-local temporary a packed row array of `N` rows indexed by the genvar; the loop becomes a labelled `GenerateFor` (`<v>__lp<k>`) whose body holds the iteration's definitions as `Assign`/phi trees; after the loop the definition of `v` is `v__n[N]`. When the update of a carried VECTOR is bitwise (`& | ^ ~ ?:` over accesses of the same width, the clmul accumulate), the row is emitted as 2-D bit cells with an inner generate over the bit index, because `sv_equations` reads cells and 1-D bit chains but not family rows (measured, 6.1); an arithmetic update stays a row. Nested rectangular loops give a 3-D packed array (loader fine, tactics refuse 3-D: limitation, section 7).
* *Direct mode inside loops (v1)*: a variable whose every bit is written at most once in the loop, by windows that are injective in the loop variable, and which the loop body reads only at windows OUTSIDE the set the loop writes or at windows it has itself written earlier in the same iteration (the `for (i) y[i] = f(a[i], b[i])` idiom), needs no versions: the loop becomes `generate for (i) assign y[i] = ...` on the ORIGINAL signal. Conditional writes under a default (`y = '0; for (i) if (c(i)) y[i] = 1'b1;`) become a single-window `if` tree `if (c(i)) y[i] = 1'b1; else y[i] = y__1[i]`, with `y__1 = '0` the default's signal. The ripple idiom `c[i+1] = g(c[i])` (a read of the window the PREVIOUS iteration wrote) is in v1 handled by the versioned row mode, not direct mode (whole-row chain, correct but not the shape `add_n` has); the affine-shift direct mode that would recover `add_n`'s shape (solve `i+1 = j` for the writing iteration) is a v2 optimisation, JUDGED 1 day.

The algorithm, as the executor `exec(stmt, S)` over a state `S : Var -> [Def]` (newest first), `Def = (window, ref)`:

```
read(v, w, S)        = ref of the newest Def whose window contains w; if w straddles Defs, concat of the slices
                       (newest wins per bit); if a bit has no Def, the incoming value of v (module variables
                       the region does not define first: refused by (A) unless the region never writes that bit)
exec(v[w] = e, S)    = let n = fresh(v); emit Assign v__n = merge(read(v, whole, S), w, conv(e, S));  S[v] := (w, v__n) :: S[v]
exec(if c A else B)  = SA = exec(A, S); SB = exec(B, S);                       -- arms see copies
                       for v in written(A) u written(B):
                         let n = fresh(v); emit AlwaysComb{ if (conv(c, S)) v__n = ref(SA, v) else v__n = ref(SB, v) }
                         S[v] := (whole, v__n)
exec(case ...)       = the same with a case tree; no default arm = latch = refused by (A)
exec(Block of unrolled iterations) = exec each statement in order (stage U did the unroll)
exec(SymLoop)        = classify each written v as carried / iteration-local / direct;
                       carried: declare v__n[0..N] rows, emit Assign v__n[0] = ref(S, v); run body ONCE with i := genvar,
                       reading v through row i and writing row i+1; temporaries: row arrays [0..N-1];
                       emit GenerateFor{ genvar i, init, bound, step, label v__lp<k>, body }; S[v] := (whole, v__n[N])
exec(statement-bodied call) = stage U (X2) bound the formals and left the body as a region; its result is the Ident f__c<k>
conv(e, S)           = the JSON expression e with every Ident/BitSel/PartSel/ArraySel of a region variable replaced by
                       read(v, window, S); in a SymLoop the iterator is already a GenvarRef (put there by the conversion)
finish               = rename the last Def of every module-level variable to the variable's own name
```

Loop-carried versus iteration-local is decided by the (A) analysis restricted to the body: a variable is iteration-local iff every read in the body is dominated by a write in the same iteration and it is not read after the loop (or is region-local); everything else the loop writes is carried. A variable read after the loop whose loop writes are not carried is refused in v1.

**Naming (stable, readable, in the order the golfer wrote it).** `<var>__<n>` with n counting the definitions of `<var>` in execution order (loops count once, as one row array); the final definition of a module-level variable keeps the bare name; region-locals `<lbl|blk<k>>__<var>__<n>`; function temporaries `<fname>__c<k>__<local>__<n>`, results `<fname>__c<k>` (k = call-site index per module); loop labels `<var>__lp<k>`; clashes with any module identifier append `_` deterministically. The tactics derive equation names from signal names (`eq_<signal>_<site>`), so these names are what the golfer's proof mentions. To make them discoverable the checker prints, with `--unproved`, a NEW stage artefact `lowered.sv` (the lowered envelope rendered back to SV, section 6.3) and, in the JSON, a `lowering` list (source span -> hoisted names).

### 4.4 Functions (G2: X2)

Master inlines a function whose result is ONE return expression over its input formals, by substituting the converted actuals by symbol (`_SymCallBinding`), and a complete `if (c) return x; else return z;` with a `Squash2` condition. X2 keeps that path untouched and adds the bodies it refuses (locals, several statements, loops). A call in an expression (module `assign`, region statement, generate body) is then inlined at conversion: formals bound by name to `<fname>__c<k>__<formal>` with `assign formal = actual` (an actual that is a plain signal access or a constant is substituted instead of copied; a compound actual is copied, which also makes it a signal ACCESS, the only left operand of a shift the tactics read), the body lowered by 4.3 in its own region, literal-only subtrees folded after substitution (32-bit signed, width-exact: `32 - n` with `n := 16` becomes `16`, the only shift amount shape besides a signal the tactics read), the call node replaced by `Ident <fname>__c<k>`. Argument evaluation order and static-versus-automatic sharing are unobservable because bodies are pure and every local is written before read. Calls inside a generate body hoist their temporaries as row arrays indexed by the enclosing genvars (the same allocator as lifted-loop temporaries). Unreferenced `Subroutine` members are dropped (they are inert), referenced ones are consumed by the inliner; a function the inliner refuses leaves today's `SubroutineSymbol:Subroutine` / `CallExpression` loud node.

## 5. Why the lowered design means the same as the original

### 5.1 The theorems the tests are standing in for

Let `R` be an admitted region, `L(R)` its lowering. For every parameter point and every assignment of 4-state values to the signals R reads:

* **EQ-1 (loop-free SSA).** The value of each variable R writes at the end of one execution of R equals the value of the corresponding signal in the settled lowered design. Induction on the statement: assignment is compositional (evaluating `e` against the current values equals evaluating it against their defining signals); `if`/`case` are phi trees with the SAME condition and arms, so truthiness (any known 1 bit => true, otherwise the else branch), `case` equality and the else-on-x rule are executed by Lean's own `ifStmt`/`caseStmt`; an unselected arm's value, even if x, never reaches the result because it is not merged. (A)+(G) make the block's result independent of the previous run's values, which is the premise of the settle semantics (`CombGuard2Sound`: admitted bodies are idempotent).
* **EQ-2 (unroll).** Unrolling a counted loop with literal bounds whose body does not assign the loop variable is the definition of the loop.
* **EQ-3 (lift).** Row `k` of the carried array equals the state after `k` iterations, by induction on `k`; the body is a function of (state, loop variable) only; the genvar is the same integer as the loop variable (32-bit signed wrap cannot occur: `parameter int N` < 2^31 and the variable stops at N).
* **EQ-4 (inline).** A call is a sequential execution of the body on a fresh frame; with pure bodies and definite assignment it is the pure function the inlined signals compute.
* **EQ-5 (`@*`).** Under R1 to R6 a level-sensitive block recomputes its targets whenever a read signal changes, and the settle semantics computes the same fixpoint.
* **EQ-6 (net).** With exactly one driver on every bit the resolved value is the driver's value.

None of these is a Lean theorem in G1/G2. The standing-in evidence per design is in 5.3 and 6.3.

### 5.2 The 4-state subtleties, case by case

| subtlety | handling |
|---|---|
| `if (x)` takes else, `c ? a : b` merges | phi trees are `if`/`case` trees, so the original `if` semantics is executed by Lean; a straight-line statement becomes a continuous assign. Emitting `?:` would differ on an x condition (fine for the task statement, which quantifies over known inputs, but wrong as an ls-sv semantics and visible to the differential rows) |
| unassigned local / return value read (x in IEEE; Yosys resolves freely) | refused by (A); plus a `fourstate.py` rule BEFORE the construct is enabled (policy: "where the construct brings an x source, a rule in fourstate.py lands first") |
| latch (`if` without `else`, `case` without `default`) | refused by (A); `always @*` latches additionally caught by the Yosys `$dlatch` assertion |
| read of the target before its write (`y = t; t = a;`) | refused by (G), the Lean guard's own rule |
| last write wins (`y = a; y = b;`) | the n-th definition shadows the (n-1)-th in the state; only the last reaches the port |
| `integer`/`int` loop counter is signed 32-bit | unrolled literals and genvar uses keep the converted widths/signedness of the surrounding nodes; `b[i]` with `i` outside `b` is the same out-of-range read the loop would do; the svGolf rule (d) is taught the loop interval (section 7.1) |
| out-of-range / x index read inside an unselected arm | unselected arms are not merged (phi), so no x leaks |
| trip count not static | refused (loop shape (L)) |
| a bit written twice by different iterations (`p[k] ^= ...` over a double loop) | not injective: versioned rows, not direct mode |
| default-point fold | no analysis reads a parameter's value; unroll-vs-lift is syntactic; coverage and definite assignment are affine; `--probe-points` re-extraction must produce the same shape (a test) |

### 5.3 Differential evidence plan (per lowering)

* New rows in `harness/sv/cases2.json` per construct (about 6 to 12 each: the idiom, its 4-state edges, a parametric point set N = 1, 2, 3, 4, 8), with Xcelium pins captured on a licensed Xcelium host and merged into `xcelium_golden.json`; every row simulates the ORIGINAL text (that is what the harness does) against `run2` on the LOWERED envelope, including x/z stimulus where the construct is 4-state-faithful (the `if`-tree phi, unrolled loops) and known-only stimulus for the declared `@*` time-zero row.
* **Stage S against stage U, in Lean, no simulator needed**: for every source in the corpora a flag (`--no-ssa`) produces the stage-U envelope, the default produces stage S's; `runner2` evaluates both on a few thousand random 4-state vectors (x/z included, parameter points N = 1, 2, 3, 4, 8) and any difference of any signal at the settled state is a failure. Stage U is the semantic reference because Lean executes it natively and the off-prem agent pinned it against Icarus (`sem2/for_unroll`, `symbolic_*_function`); stage S only has to equal it. For parameter-bound loops there is no stage-U twin at the symbolic level, but at each probe point the loop IS literal: re-extracting at the point with the lift disabled gives master's unroll (literal after override) as the oracle for that point.
* Unit tests (python3.12 pytest, `extractors/sv/test_lower_proc.py`): the admission matrix (each refusal message, positive and negative), the naming rule, shape stability across `--probe-points`, the survey probes that cover each lowering, monotonicity (a corpus of today's admitted envelopes is byte-identical).
* `python3 -m pytest extractors/sv` and the harness unit tests unchanged-green; `diff_test2 --golden` on every touched row (no admitted row changes value).

## 6. The golfer's view

### 6.1 clmul written naturally

```systemverilog
module clmul_n #(parameter int N = 16) (input logic [N-1:0] a, b, output logic [2*N-1:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < N; i++)
      if (b[i]) p ^= a << i;      // context-sized: no cast needed, p is 2N wide
  end
endmodule
```

lowers (4.3, lift, parametric bound) to

```systemverilog
  logic [N:0][2*N-1:0] p__1;                 // p__1[k] = p after k iterations
  assign p__1[0] = '0;
  for (genvar i = 0; i < N; i++) begin : p__lp1
    always_comb begin
      if (b[i]) p__1[i+1] = p__1[i] ^ (a << i);
      else      p__1[i+1] = p__1[i];
    end
  end
  assign p = p__1[N];
```

the `add_proc` carry cell with a row instead of a bit. MEASURED on the shape probe `v6_chain_alwayscomb_shape` (the same family with the shift dropped and a 2N-wide operand, so that it is inside the fragment: design stage accepted, `--tactics` `in_fragment: true`), `sv_structure?` prints what the golfer has to rank (verbatim, trimmed):

```
declarations:  input a [N-1:0]  input b [N-1:0]  output p [2*N-1:0]  ae [2*N-1:0]  p__1 [N:0] [2*N-1:0]
plain sites:   plain#2 : drives p__1[0]   reads []        plain#3 : drives p   reads [p__1[N]]   (+ the two writes of ae)
family `lp_p`: for i in [0, N):
  lp_p#0[i] : drives p__1[i + 1]   reads [b[i], p__1[i], ae, p__1[i]]
rank relation:  rank(plain#2) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; plain#2 drives p__1[0]]
                rank(lp_p#0[i']) < rank(lp_p#0[i])   [lp_p#0[i] reads p__1[i]; lp_p#0[i'] drives p__1[i' + 1]]
                rank(lp_p#0[i']) < rank(plain#3)     [plain#3 reads p__1[N]; lp_p#0[i'] drives p__1[i' + 1]]   ...
```

so the rank the golfer writes is the one of the ripple adder, `(0, i + 1)` for the chain cells and a larger one for `p`, and the names in the goal are the lowered ones (`p__1`, `lp_p`). The second tactic stops, MEASURED: `sv_equations?` on the same design answers `site lp_p#0[i]: the access p__1[i + 1] does not match the declaration of p__1 (a select needs zero-based descending packed dimensions [hi:0], with the number of selects the declaration allows)`. I first suspected the always_comb form (inside an `always_comb` body the extractor emits an element select of a 2-D packed array as `BitSel(Ident p__1, i)`, a continuous assign gets `ArraySel`), and tested four more shapes in batches 4 and 5: the same row chain as a continuous `?:` assign (`s1`), with N-wide rows (`t1` assign, `t2` always_comb), and a plain `acc[i+1] = acc[i] ^ ae` without any mux (`t3`): ALL FIVE give the same message, so the cause is neither the always_comb form nor the row width: **`sv_equations` does not read a generate family that reads or writes whole ROWS of a 2-D packed array** (the plain-site row writes of `mul_n`, `s[0] = ...`, and the bit-cell families `s[i][j]` are read). By contrast a one-bit accumulator chain `par[i+1]` in a 1-D vector, written as an always_comb if/else per iteration (`s2_chain_bit_alwayscomb`), goes through completely; the tactic prints (verbatim, trimmed)

```
eq_par_plain_0  : st.boolAt "par" 0 = false
eq_par_lp_par_0 : ∀ (i : Nat), i < N →
    st.boolAt "par" (i + 1) = if st.boolAt "b" i = true then st.boolAt "par" i ^^ st.boolAt "a" i else st.boolAt "par" i
[noSelfRead] ⊢ ∀ i, 0 ≤ i → i < N → (i + 1).toNat + 1 ≤ i.toNat ∨ i.toNat + 1 ≤ (i + 1).toNat      [cover_*], [inRange_*], [inputsKnown_*] as for add_proc
```

that is the equation the golfer's induction (`par[k]` = parity of the first `k` selected bits) consumes. Consequence for the lift (X4): a loop-carried VECTOR whose update is bitwise (the clmul XOR accumulate, masks, parity vectors) is emitted as 2-D bit cells with an inner generate over the bit index (`acc[i+1][j] = b[i] ? acc[i][j] ^ ae[j] : acc[i][j]`, the `mul_n` shape the equation layer reads), and a vector whose update is arithmetic (`cnt = cnt + a[i]`) stays a row chain, which the loader accepts and `sv_structure` reads but `sv_equations` does not until the tactics read family rows (gap 7.3.2). The phi form (if-tree versus `?:`) is NOT what decides it: both give the same refusal on rows and both are read on bit cells.

A ChaCha quarter-round step written with a function (name-assignment style, because Yosys 0.53 cannot read `return`):

```systemverilog
function automatic logic [31:0] rotl(input logic [31:0] x, input int n);
  rotl = (x << n) | (x >> (32 - n));
endfunction
assign a1 = a + b;
assign d1 = rotl(d ^ a1, 16);
```

On master this extracts clean (MEASURED, `proc/micro/m10.sv`) as `rd = ((d ^ ra) << 16) | ((d ^ ra) >> (32 - 16))` with the tag `user_function_inline`: the actual is substituted, so a shift operand is an OPERATION (and the amount `32 - 16` is an unfolded expression), both outside the tactic fragment. X2's two additions turn it into the form below, which lowers to `assign rotl__c1__x = d ^ a1; assign rotl__c1 = (rotl__c1__x << 16) | (rotl__c1__x >> 16); assign d1 = rotl__c1;`: shift operands are signal accesses, amounts are literals, so the lowered netlist is inside the fragment and, being fixed size, a flat netlist the tactics decide (the `aes_sbox` fast path). The `+` is the task's business (a banlist is per task).

### 6.2 What the tactics do with the hand-lowered shapes (MEASURED, `proc/lowered/*.sv`, `check.py --unproved --tactics`)

All shapes extract with no `Unsupported` and no `LocalDecl` (MEASURED, extractor). Through `check.py --unproved --tactics` (MEASURED; design stage accepted for all; the five batches are collected by `proc/mk_results.py` into `proc/results.md`):

| design | shape | design stage | in tactic fragment |
|---|---|---|---|
| `v1_clmul_chain` | assign chain, packed `[N:0][2N-1:0]` rows, `sh[i] = a << i` (genvar amount), `acc[i+1] = b[i] ? acc[i]^sh[i] : acc[i]` | accepted | **no**: `site g_it#0: operand of a shift that is not a signal access, a sized literal or an unsized constant` |
| `v1b_clmul_chain_rowshift` | the same chain with the shift removed (`sh[i] = a`) | accepted | **yes** (`ok`) |
| `v2_bitwise_for` | the bit-parallel loop in direct mode: `generate for (i) assign p[i] = a[i] & b[i]; assign p[i+N] = a[i] ^ b[i]` | accepted | **yes** |
| `v4_if_chain_ssa` | SSA assigns, a mux step on a one-bit condition | accepted | **yes** |
| `v3_ssa_localparam_w32` | SSA assigns, `localparam` widths, rotation by concatenated part-selects of a literal-width PORT | accepted | **no**: `site plain#0: legacy part select` (the control for 7.4) |
| `v6_chain_alwayscomb_shape`, `s1_chain_assign_rows`, `t1_rows_n_assign`, `t2_rows_n_alwayscomb`, `t3_rows_2n_assign_plain` | row-valued chains (always_comb or assign, N or 2N wide) | accepted | `sv_structure` yes; `sv_equations` NO, all five (6.1) |
| `s2_chain_bit_alwayscomb` | one-bit accumulator chain, always_comb if/else per iteration | accepted | yes, structure AND equations (6.1) |
| survey probe `r16_xor_chain_gen_acc_if` | SSA chain, one `always_comb if/else` per iteration, row XOR | accepted | yes (survey run, `sv_structure` only) |
| `add_proc` (task reference) | the same cell with a bit instead of a row | accepted | proved with the tactics (`PROVING.md` section 13) |

Also measured (batch 2): `v6_chain_alwayscomb_shape` design accepted and `in_fragment: true` (the always_comb row chain, above); `v5_clmul_chain_alwayscomb` (the proposed lowering of the natural loop: `v1`'s shift inside the r16 cell) design accepted, `in_fragment: false` with `site lp_p#0: operand of a shift that is not a signal access, a sized literal or an unsized constant`; `v8_unrolled_clmul4` (the literal-bound loop unrolled to straight-line SSA with literal shifts) design accepted, `in_fragment: true`. Batch 3 (the one-line ImplicitType spike applied for the duration of the run only): `v9_typeless_ansi_inputs` (`input [N-1:0] a, b` in an ANSI header) design stage ACCEPTED, so the loader takes the typeless declarations once their dimensions are recovered (its tactics refusal is the `{a ^ b, a & b}` concatenation of operations I wrote, unrelated); `v10_typeless_nonansi` (non-ANSI header, `parameter N`, `input [N-1:0] a, b;`, `reg [..] p;`) gets past the declarations and stops exactly at `TimedStatement:EventListControl: always @(a or b)`, the E1 item.

The split the table shows: the chain, mux and bit-parallel shapes the lowering produces are the shapes the tactics already read (`v1b`, `v2`, `v4`, `r16`), and removing the one construct the natural clmul loop adds, the genvar shift amount, moves `v1` from refused to read (`v1b`). The hand-written workaround for a golfer today is exactly `v1b`'s: no shift in the loop, or a per-row signal.
### 6.3 The lowering-check stage (proposed; not in G1)

`lowered.sv` = the lowered envelope printed back as SystemVerilog (a small printer over the existing vocabulary: ~200 lines, trusted only for this check). The checker adds a stage after `fourstate`: Yosys reads the ORIGINAL canonical text and `lowered.sv`, builds `miter -equiv -flatten` over the outputs at the scoring point and every backstop point, and proves the miter output constant 0 with `sat -verify -prove trigger 0` (the designs are combinational); a counterexample is a bug report ("the lowering of your design is wrong at point P, input vector V"). It turns a lowering bug into a loud, per-design refusal instead of a proof about the wrong design, at no cost to designs without a lowered region (skipped). It does not replace the differential rows (it covers the points, not all N) but removes the main risk of Option A. Cost: 1.5 days (printer + stage + 6 negative tests that mutate the lowering).

## 7. What has to change outside `lower_proc.py`

### 7.1 svGolf (separate commit, `svgolf/score`, `svgolf/check`)

* `fourstate.py` rule (d): a counted-loop variable of the admitted shape (literal start, bound constant at the point, step +-1, not assigned in the body) ranges over its loop interval; select indices that are affine in loop variables get interval arithmetic. This replaces `sg-fs-loop-index` for admitted loops only (any other procedural counter keeps the type-range rule). About 120 lines + selftests. The parametric guarantee for all N comes from the Lean `inRange` obligations of the lowered design.
* `fourstate.py` new rule: function-local / return value read before assignment (slang AST definite-assignment walker, ~120 lines), landing BEFORE function inlining is enabled; a Yosys `select -assert-none t:$dlatch t:$adlatch` after `proc` for `@*` latches.
* `check/envelope.py`: the cache key hashes `extract.py` only (`extractor_sha256`); it must hash `lower_proc.py` too (one line), else an edit to the lowering would reuse stale envelopes.
* `check.py`: the `lowering` summary and `lowered.sv` artefact (section 4.3), the lowering-check stage (6.3).

### 7.2 ls-sv

`extractors/sv/lower_proc.py` + the hooks of section 4; `docs/sv-refusals.json` rows (section 8); `docs/sv-changelog.md` entries; `docs/sv-lowering.md` (this note's semantics, trimmed); `harness/sv/cases2.json` rows + `xcelium_golden.json` pins. `LeanModels/Sv` is NOT touched.

### 7.3 Reports for owners of other lanes (not mine to patch)

1. **Tactics (WP-B2 / WP-G owners):** `CombView.shOpdRd?` refuses a genvar shift amount. Accepting `.genvarRef` (and affine expressions of genvars and parameters) as a shift amount would bring the natural `p ^= a << i` clmul for parametric N into the fragment; the equation side needs the amount as a numeral that depends on the instance index (`XF.shl` over a `Nat` function of `i`). Estimated cost on their side: one recognizer case plus its shape lemma, 1 to 2 days (JUDGED). Without it a golfer writes the shift as a per-row signal (`sh[i] = a`, read through an amount signal) or in the bit-level form.
2. **Tactics:** `sv_equations` refuses a generate family that reads or writes whole ROWS of a 2-D packed array (`the access acc[i + 1] does not match the declaration of acc (a select needs zero-based descending packed dimensions [hi:0], with the number of selects the declaration allows)`): MEASURED on five shapes (`v6`, `s1`, `t1`, `t2`, `t3`: `assign` or `always_comb`, N- or 2N-wide rows, with or without a mux); `sv_structure` reads all of them. The plain-site row decomposition (`s[0] = ...` in `mul_n`) exists; extending it to affine row indices in families is the repair (JUDGED 1 to 2 days on their side). Every accumulator loop whose carried variable is an ARITHMETIC vector produces row cells, so this gates the tactic route of those lifted loops (bitwise vectors use bit cells, above). Also: 3-D packed arrays (nested lifted loops give them); `sv_equations` multi-window bodies (S1b gate d, in flight) matter for loop-free regions the lowering leaves procedural.
3. **Loader (optional):** a `LocalDecl` arm in `Ingest2` would let loop-free locals stay procedural (nicer equation names than the hoist); not needed.

### 7.4 The survey's cheap items 6 and 7 (replication, literal part-selects): does the same machinery help?

* **Literal-width part-select ("legacy part select").** READ from the recognizer: `CombView.leafRd?` refuses `PExpr.partSel` (the extractor's node for a constant-bound select on a base whose declared width is literal) while the same text on a parameter-width base arrives as `arrayPart` with affine bounds and is read. A constant bound is affine, so the repair is a recognizer case (`partSel n hi lo` with literal bounds -> `arrayPart` with constant affine bounds) or an extractor routing change; the lowering machinery does not help (nothing is hoisted, no state). It matters more than the loops for the ARX family (rotation by `{x[15:0], x[31:16]}` is the dominant style, 12 of 31 entries): the chacha function style of 6.1 sidesteps it through shifts by literals, the concat style needs this repair. REPORT to the tactics owners; the note's chacha example is the workaround.
* **Replication `{N{x}}`.** The loader reads it (`Expr2.repl`, count evaluated per point); `leafRd?` refuses `PExpr.repl`. The comb-SSA allocator could materialise a replicated mask as a generate-filled row (`m__k[j] = x` for `j < N`), which would bring the `a & {N{b[i]}}` partial-product idiom into the fragment, but it changes the signals the golfer's equations talk about for a construct whose natural home is one recognizer constructor with an affine count. I would not lower it; if the recognizer slips, the hoist is a 1 to 1.5 day fallback on top of G2 (JUDGED).

## 8. Effect on the refusal register

| row | today | after G1 | after G2 |
|---|---|---|---|
| `ld-init-expr` (typeless ports / dims) | later | lifted for typeless and implicit-type declarations (N1); remains for non-literal initializers | |
| `dc-net-z` | later | split: lifted for fully-driven single-driver `wire`/`output wire`/implicit nets (N2); remains `later` for undriven bits, multi-driver nets, tri/wand/wor | |
| `pr-implicit-event`, `pr-event-list` | later | lifted for level-sensitive lists under R1 to R6; `later` for edge lists (sequential layer) | |
| `ld-localdecl` | later | lifted by hoisting (L1); `le-generate-decl` for generate-local | `le-generate-decl` lifted (row arrays) |
| `st-compound` | later | lifted for identifier / affine-select targets (C1) | |
| `st-for` (off-prem 7f7c1e02 already narrowed `why`/`prerequisite` and `kinds` to `ForLoopStatement`) | later (literal single-`int` loops unrolled) | X1: header forms (outside iterator, compound step) | X4: parameter-bound counted loops lifted; refusal sub-reasons as extra `sv_kind` suffixes of the SAME tag (`ForLoopStatement:shape`, `:budget`, `:sequential`); `while`/`break`/non-counted stay `later` |
| `ex-user-call`, `dc-member-kinds` (functions) (off-prem f6ecaf7d..9dbf8a81 narrowed the row to the non-pure forms) | later (pure single-return forms inlined) | | X2: statement-bodied non-recursive input-only functions; `later` for tasks, output args, recursion, `return` in the middle |
| `x:top-instantiated` (RB0, no row) | | new row + fix (N3) | |
| svGolf `sg-fs-loop-index` | later | | lifted by the loop-interval rule for admitted loops |
| svGolf `sg-fs-latch` | later | extended to `always @*` latches (Yosys `$dlatch` after `proc`) | |
| svGolf new | | | `sg-fs-userfn-uninit`, `sg-lowering-check` |

New principle line proposed for the register: **P-LOWERING** (to confirm): an extractor lowering is admitted only with (a) a stated admission predicate whose refusals are register rows, (b) emission in existing vocabulary, (c) 4-state-preserving constructs, (d) differential rows with Xcelium pins, (e) the per-design equivalence stage once it exists.

## 9. Estimates per construct and the prototype plan

Working days of one agent, JUDGED; `x` = Xcelium pins + register + changelog included.

| item | code | tests/rows | risk | days |
|---|---|---|---|---|
| N1 typeless dims (`ImplicitType`) | 1 line + 20 | 8 unit, 3 rows | low (dimension forms: `[N-1:0]`, multi-dim, signed, `reg` redecl) | 0.3 |
| N3 `topModules` | 3 lines | 2 | low | 0.1 |
| N2 nets (coverage, decl assign, implicit nets) | ~250 | 20 unit, 8 rows | medium: affine interval union, instance-driven nets, `default_nettype` | 1.5 |
| E1 `@*`/level lists (R1 to R6) | ~100 | 12 unit, 6 rows | medium: R3/R4 corner cases; the time-zero declared row | 0.7 |
| L1 local hoist | ~60 | 6 unit, 3 rows | low | 0.4 |
| C1 compound / incdec (sym branch + leaf hook) | ~50 | 8 unit, 5 rows | low-medium (selector once) | 0.5 |
| X1 loop-header forms (outside iterator + dead-declaration erase, `+=` step) | ~40 | 6 unit, 3 rows | low (the `integer` signed wall on the declaration) | 0.4 |
| register + changelog + `x` for G1 | | | | 0.6 |
| **G1 total** | ~550 | ~60 unit, ~28 rows | | **~4.5** |
| X3 stage S core (state, merge, phi, naming, direct mode, JSON renamer) | ~450 | 25 unit, 10 rows, the U-vs-S oracle harness | medium-high | 2.5 |
| X4 lift (SymLoop, row arrays, generate emission, iteration temps) | ~250 | 15 unit, 10 rows | high: windows indexed by genvars, nested loops, probe-point shape stability | 2.5 |
| X2 function bodies (formals, region, generate-body hoist, compound-actual materialisation, literal folding) | ~150 | 12 unit, 8 rows | medium (reuses `_SymCallBinding`) | 1.2 |
| `fourstate.py` (d) loop interval + USERFN + `$dlatch` | ~300 | 20 selftests | medium | 1.5 |
| lowering-check stage (printer + miter + negatives) | ~350 | 10 | medium | 1.5 |
| register, docs, changelog, `x` | | | | 0.8 |
| **G2 total** | ~1500 | ~90 unit, ~30 rows | | **~10** |

(The unroll, 0.6 days in the first draft, is gone: it is master's.)

Option B comparison (JUDGED): loops in `Stmt2` + `instStmt2` unroll 1 day, tactic loop reasoning 10 to 15 days, calls 5 days, plus re-pinning the proof files; RB0 guesses `L` for both.

**Prototype plan.** Every commit is rebased on master first and touches `extract.py` only in the delegating hunks of section 4. G1 order (each step = tests + rows + one commit): N1 -> N3 -> N2 -> E1 -> C1 -> X1 -> L1 -> register/changelog. G2 order: stage S core on master's unrolled blocks (headline: fixed-size clmul and the chacha quarter round, which master already unrolls/inlines and the tactics cannot yet read; validates naming, the printer and the U-vs-S oracle) -> X2 function bodies -> X4 lift (headline: parametric clmul) -> fourstate rules -> lowering-check. Gate reports after G1 and after G2; a stop after the core if the formal miter finds anything unexpected.

**Risks, in the order I would watch them.** (1) A hook in `extract.py` collides with the off-prem ls-sv agent's edits of the same functions: mitigated by keeping every hook a one-liner into `lower_proc.py`, but each G1 commit should rebase on `master` first (REPORT if a hook site moved). (2) Shape instability across `--probe-points` (the cross-check would flag `XCHECK-FAIL`): every decision is syntactic, one unit test re-extracts at several points and compares shapes. (3) Names: a refactor of the naming rule changes every golfer's equation names, so the rule is pinned by a test and documented in PROVING.md at G1 (it is a user interface). (4) The tactic fragment: lowering widens what is ACCEPTED far more than what the tactics READ (the genvar shift, 3-D rows, replication, literal-width part-selects); the note says so at the point of use and the golfer falls back to the by-hand route (`add_n_byhand`). (5) Double loops that read-modify-write single bits of one carried vector (`p[i+j] ^= a[j] & b[i]`, the triangular clmul `c07`): accepted by versioned rows, correct, large, hostile to proofs; the direct per-bit chain recovering the AND/XOR array shape is a v2 optimisation, not promised. (6) Xcelium access for the pins is a dependency of every G1/G2 row.

## 10. Questions for the lead

* Q1. Is a per-design formal miter (6.3) acceptable as the equivalence story instead of a Lean theorem? (It is exact at the scoring/backstop points; for all N the argument is the induction in EQ-3 plus the differential rows.)
* Q2. `always @*` R3 refuses 2-state signals and empty read sets rather than adding an fourstate rule only; OK to keep the rule in the extractor, with the fourstate side limited to the `$dlatch` assertion?
* Q3. WP-G is extending the proved `lowerComb` with SSA reads and temporaries, and master's unroll hands it exactly the straight-line blocks it needs. Should stage S for LITERAL loops (X3) be built at all, or only X4 (the lift, which no Lean-side work can replace)? My default: build X3, behind a flag, because the clmul/chacha headline targets are unprovable without it today and WP-G has no date; drop it for literal loops when SSA reads land.
* Q4. The genvar shift amount in the recognizer (7.3.1): who owns it? Without it the natural parametric clmul is accepted and scored but not provable with the tactics.
* Q5. Generate-local declarations and function calls inside generate bodies need 3-D packed rows for nested loops (outside the tactic fragment). Defer to G3, or refuse nested-loop temporaries in G2?
* Q6. (Resolved by measurement, no decision needed.) The phi form, `always_comb if` tree versus continuous `?:`, does not decide tactic readability (rows are refused in both, bit cells are read in both), so the 4-state-faithful if-tree stays everywhere. The open item is the tactics' row-family gap of 7.3.2: do you want the lowering to emit bit cells for bitwise vector updates (my default, costs an inner generate) and rows otherwise, or rows always and wait for the tactics?
* Q7. Ownership of the hunks. The off-prem agent edits `extract.py` constantly (and master's `test_let_expressions.py::test_subroutine_in_expansion_is_not_guessed` already fails on its own change: not mine, but it shows how fast the file moves). My hunks are delegating one-liners into `lower_proc.py` placed next to its `_sym_for_values` / `_sym_inline_function_call` / `_convert_compound_assignment`; can I ask the maintainers to tell that agent to leave those call sites in place (and to add its own forms through `lower_proc` where they overlap: loop headers, function bodies), so the two efforts stay one lowering?

## 11. Files

* this note; `proc/README.md`; `proc/reach.py` (tier MODEL on the three populations, from the committed data; pre-rebase extractor, kept as a cross-check); `proc/g1_upper_bound_hack.patch` and `proc/h2_loop_compound_hack.patch` (throwaway upper-bound patches of master 0ca14852's extractor: N1/N2/N3/E1, then C1/X1) with their drivers `proc/run_hack.py` (survey files), `proc/run_hack2.py` (survey files, iterator-forms patch), `proc/run_hack_probes.py` (probes), `proc/rb0_clean.py` (RB0, after `rb0/census_extract.py --repo`); `proc/micro/m*.sv` (the thirteen micro-designs of section 0.1); `proc/scan_proc.py`, `proc/run_scan.py`, `proc/reach_probes.py`, `proc/sum_scan2.py` (pyslang statement census and its drivers); `proc/survey_files.json`, `proc/scan_survey.json`, `proc/probe_scan.json` (measured inputs of the model); `proc/lowered/*` (hand-lowered shapes and tactic probes); `proc/results.json` (headline numbers of the first draft; the master-based ones are in section 0); `proc/results.md` (what `check.py --unproved --tactics` and the tactics answered on the hand-lowered shapes, written by `proc/mk_results.py`).

## 12. G1 as built (2026-11-01, branch wpproc1, one commit per item)

Built: N1 typeless dimensions, N3 `--top` of an instantiated module, C1 compound assignment, X1 loop headers, L1 block-local
hoist, E1 `always @*` and level lists under R1 to R6, N2 nets with one continuous driver. The contract is `docs/sv-proc-lowering.md`;
the logic is `extractors/sv/lower_proc.py`; every item has unit tests (`test_lower_proc.py`, 88 tests), Xcelium-pinned rows `proc_*`
(`harness/sv/cases2.json`: 26 `proc_*` rows plus the lifted `wpg_local`, every one PASS against Icarus and XREF-MATCH against Xcelium 24.03-s004), and its register rows
updated in place. Monotone by measurement (`harness/sv/regress_envelopes.py`): no committed symbolic envelope or svGolf design that was
admitted before changed.

Differences from sections 4 and 8 (all in the refusing direction or recorded):

* **C1 stops at compound assignment.** Statement-position `x++` / `x--` were already lowered by master. The lowering reads slang's
  bound tree (the placeholder of the right-hand side takes the converted read of the target), not a rewrite of the source.
* **X1** needed one more fix than the note counted: `<=` / `>=` were missing from the operator table under slang's own names
  (`LessThanEqual`, `GreaterThanEqual`), so they were refused even in master's declared-iterator form.
* **L1** hoists only static locals of a module-level `always_comb` or E1 block; generate scopes, initializers and automatic
  variables stay loud (a recorded over-refusal).
* **E1** decides R5 on the converted JSON with BIT-WINDOW coverage (an unrolled `y[i] = ...` loop counts), whole assignment for
  parametric widths, and `case` only with a `default`; R3 is enforced in the extractor as designed; R6 uses slang's driver table
  (`AnalysisManager.getDrivers`, once per compilation, only when such a block exists). The Yosys assertion that no latch exists
  after `proc` (`select -assert-none t:$dlatch t:$adlatch t:$dlatchsr`, defense in depth for R5) is rule (e) of
  `score/fourstate.py` since follow-up 3 (below).
* **N2** accepts two point-independent shapes (one whole-net driver by source text; literal windows tiling a literal-width net) and
  refuses generate-scope drivers and windows of parametric-width nets (section 4 allowed an affine interval union over the
  parameters; the whole-driver shape covers what the surveyed code does). The strength is read from the syntax tree.
* **Finding outside the item list, closed by follow-up 1:** in symbolic mode `_continuous_assignment_has_strength` read source bytes
  that only the M0 path loads, so `assign (strong0, highz1) y = a;` on a `logic y` was extracted as a plain assignment. Measured
  later (rows `cstr_highz`, `cstr_weak`): Icarus 12 applies it (z where a = 1), Xcelium 24.03 ignores it on a variable (`*W,CAVSTR`,
  y = a: the model's reading), Yosys 0.53 cannot read it (syntax error), Verilator 5.042 stops on `highz`: no shared reading, so
  `ContinuousAssignSymbol:strength` refuses every strength-qualified `assign` (register row `st-cont-strength`). The earlier
  wording "silent wrong answer" was half the picture.
* **svGolf, closed by follow-up 2:** `extractor_sha256` (the stage record, so the leaderboard, and the envelope cache key) is the
  identity of `extract.py` AND `lower_proc.py` (`check/envelope.py` `extractor_sha256`; `extract.py` alone for a checkout from before
  `lower_proc.py`); the integrity tripwire fingerprints both files. The byte-identity goldens mask `extractor_sha256` and did not move.
* **Follow-up 3:** rule (e) of `score/fourstate.py` refuses every latch `proc` infers; `latch_never.sv` and `latch_star.sv` now stop
  at `fourstate` (they used to stop at `design`), and 148 designs of the repository (task references and test designs) keep their
  fourstate verdict.

Measured reach after G1 (extractor level: no `Unsupported`, no `LocalDecl`, no `packed: null`; the three populations of section 2):
| population | master 3473d36b | G1 (wpproc1) |
|---|---|---|
| survey: 216 self-contained real files | 29 clean (54 without an `Unsupported` node, 25 of those carry `packed: null` or `LocalDecl`, which the loader refuses) | **57 clean** |
| RB0: 82 as-is CPU blocks | 14 clean (8 do not extract: `--top` of an instantiated module) | **29 clean** (all 82 extract) |
| probes: 240 that extract | 153 clean (156 with `LocalDecl` allowed) | **179 clean** (180 with `LocalDecl` allowed; 193 if loop and function kinds are allowed, the stage-S upper bound) |

The upper bounds of the throwaway patches of section 0 (measured on master 0ca14852, without driver analysis or admission rules) were
73, 22 of 79 and 175: the survey gap (73 against 57) is the safety rules working (nets with no or several drivers, latches, lists that
miss a read) plus the shapes the first version leaves out (below). Extractor level only: the Lean loader and the tactics are not
re-measured; every construct class is exercised end to end by the 26 `proc_*` rows (loader, Icarus, Xcelium).

What is left in the survey (walls present / walls that are the file's only one): `SubroutineSymbol:Subroutine` 49 / 0,
`CallExpression` 41 / 0, `AssignmentExpression:target` 29, `NamedValueExpression:type` 29, `ElementSelect:default-point-index` 28,
`PortSymbol:net-z` 26 / 4, `NetSymbol:net-z` 21 / 5, `ForLoopStatement` 12 / 5, `SignalEventControl:None_` 7 sole,
`ConversionExpression:Explicit` 6 sole. Measured next steps inside this item list: (1) N2 residue, decided by the new decision trace
over the survey (nets): drivers inside a generate scope 49 nets in 23 files, driver windows selected by an expression 40 nets in 6
files, nets declared in a generate scope 22 nets in 7 files, undriven 30 (3 files, correctly refused); 14 files have net walls
only and 10 of them are one of the first three, so the generate-for / affine-window cover of the design note (section 4) is worth
about 10 survey files. (2) E1: 295 `@*`/list blocks lowered in 21 survey files, refused 8 by R5 (7 files; the exhaustive `case`
without `default` of hazard3's ALU is the recorded over-refusal) and 1 by R1; the 7 sole `SignalEventControl:None_` files are
generated code with PART-SELECTS in the event list (`always @(x[6:0])`): a full-width select is the signal (one file), the rest
need a bit-granular R2 (the list must cover the windows the body reads).
