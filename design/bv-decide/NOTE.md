# Allowing `bv_decide` in submissions: the comparator re-verifies the certificate (WP-BV)

> **STATUS (2026-11-01, G3): DORMANT.** The maintainers ruled, after this note's sandbox widening was explained to them (`fork`, the exec of
> `cadical`, a writable `TMPDIR`), that external solvers are not supported for now. `check.py`'s
> `BV_DECIDE_SUPPORTED` is False: `allow_bv_decide: true` is an infrastructure error, the comparator is never given `--bv-decide`
> (without it every `bv_decide` axiom is rejected with a message that names the policy), the sandbox Spec never gets the solver,
> and a refused `bv_decide` proof carries a hint. Everything below describes the work that is KEPT, dormant, so that enabling it is a
> small change (section 11). Where the text says "allowed", "accepted" or "defaults to true", read "when the constant is True".

Design note, 2026-11-01 (G0; section 10 records the as-built facts of G1 and G2). Decided 2026-11-01: the bit-blasting ban
goes, since the proof time limit bounds it anyway, and a submission may not declare new axioms.
Toolchain `leanprover/lean4:v4.33.0-rc1`; every claim about Lean below is read off its sources
(`~/.elan/toolchains/.../src/lean`) and was measured with the probes in `$SCRATCH/wpbv/probe` (the spike that
decided the design is `BvRecheck-spike.lean` next to this file).

## 0. Decision

* The comparator **re-verifies** a `bv_decide` axiom itself and accepts it exactly when `verifyBVExpr E C` evaluates to
  `true` in the comparator process. No submission code runs; the decoder is not trusted; the work is milliseconds for
  realistic proofs (a 504 MB certificate: 22 s).
* **The stop rule did not fire.** The re-check needs no submission code and trusts the LRAT checker, the bitblaster and
  the CNF conversion (`Std.Tactic.BVDecide.Reflect.verifyBVExpr`, all proved sound by `unsat_of_verifyBVExpr_eq_true`)
  as the tactic itself does, plus ONE thing the tactic does not need to trust: the toolchain's six small `ToExpr`
  instances for the reflection types (section 3). That addition is stated, not hidden.
* `native_decide`, `extern`, `implemented_by`, a user-written `axiom` and every other axiom stay refused.
* The flag: `allow_bv_decide` defaults to **true** (absent means allowed); `false` forbids. The five shipped tasks carry
  `false` today (written when the checker refused `true`); they are flipped to `true`.
* The sandbox must give the solution's compile three things it does not have (section 7).

## 1. What `bv_decide` leaves in a proof (read off the toolchain, checked by `#print axioms`)

`bv_decide` ends in `Lean.Meta.Tactic.BVDecide.LratCert.toReflectionProof` (`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean`):

1. `addAndCompile` two definitions, `<decl>._expr_def_<i>_<j> : BVLogicalExpr := toExpr r` (the reflected goal) and
   `<decl>._cert_def_<i>_<j> : String := toExpr cert` (the LRAT proof, a string literal: `Expr.lit (.strVal _)`);
2. `nativeEqTrue` (`Lean/Meta/Native.lean`): compile `verifyBVExpr E C`, run it with `evalConst` (the compiled
   checker, in the elaborator's process), and if it is `true` add

   ```
   axiom <decl>._native.bv_decide.ax_<i>_<j> : @Eq.{1} Bool (Std.Tactic.BVDecide.Reflect.verifyBVExpr E C) Bool.true
   ```
   (no level parameters, safe, `E` and `C` the two constants of step 1);
3. the proof term applies `unsat_of_verifyBVExpr_eq_true E C ax`.

`#print axioms` of a bv_decide theorem: `[propext, Classical.choice, Quot.sound, t2._native.bv_decide.ax_1_5]`. **There is no
`Lean.ofReduceBool`** in this toolchain (`nativeEqTrue` adds an axiom; nothing in `Lean`/`Std` uses `reduceBool` but its
own declaration in `Init/Core.lean`), so "`Lean.ofReduceBool` is accepted when every use is explained by verified
bv_decide axioms" is vacuous here; a hand-written use of it stays rejected (a test pins that).
`cadical` runs as a child process of `lean` (`Lean/Meta/Tactic/BVDecide/External.lean`: `cadical <cnf> <lrat>
--lrat --binary=true --quiet --shrink=0`, with a default `timeout := 10` seconds of the tactic's own config).

The shapes of `E`: the kernel value of `<decl>._expr_def_*` is `toExpr (r : BVLogicalExpr)` through the instances of
`Lean/Meta/Tactic/BVDecide/Reflect/Basic.lean` (`BVBinOp`, `BVUnOp`, `BVExpr w`, `BVBinPred`, `Gate`, `BVPred`,
`BoolExpr`): closed constructor applications, naturals as `OfNat.ofNat Nat n (instOfNatNat n)`, bit-vector
constants as `BitVec.ofNat w n`, the width equations of `append`/`replicate` as `Eq.refl Nat w`.

## 2. How the comparator walks dependencies today

`check/Comparator.lean` (`reach`) walks the solution's closure through types and values (it does not use the
`#print axioms` cache), collects every `axiomInfo`, and rejects any not in `--allow`. So today a bv_decide proof is
rejected at `comparator` ("axioms outside the allowed set") and `check.py` refuses a task that sets `allow_bv_decide`
before it starts. Name and shape cannot be trusted: a submission may write `axiom ... : verifyBVExpr E C = true` over
a false certificate, and `unsat_of_verifyBVExpr_eq_true` turns it into `False`.

## 3. The re-check

For each axiom of the closure that is not in `--allow`, when `--bv-decide` is given:

1. **Name** (policy only): the last three components are `_native`, `bv_decide`, `ax_*`. A true statement under another
   name is an ordinary axiom, rejected as before.
2. **Shape**: `axiomInfo`, safe, no level parameters, type exactly `Eq.{1} Bool (verifyBVExpr (const E) (const C)) Bool.true`.
3. **Operands**: `E` a closed definition of type `BVLogicalExpr`, `C` a closed definition of type `String` whose value is a
   string literal. Their kernel VALUES are read as `Expr` data (`env.find?`); nothing is evaluated through them.
4. **Decode** `E`'s value into a runtime `BVLogicalExpr` (a ~150-line structural reader: the six `BVExpr`
   index-dependent constructors need the width bookkeeping). It carries a node budget (default 5·10^7, against a
   shared term with exponentially many paths) and a depth limit (default 5·10^5; a 10^6-deep chain was measured to decode
   fine in the interpreted comparator).
5. **Round trip**: `toExpr decoded == value` (structural `Expr` equality). The decoder is therefore NOT trusted: whatever
   it returns is used only if the toolchain's own encoder gives back exactly the kernel term. Anything that is not
   literally `toExpr` of a value (an `id E`, a `let`, a beta-redex, `mdata`, a reference to another definition) is
   rejected; so is a bit-vector literal that is not reduced.
6. **Evaluate** `Std.Tactic.BVDecide.Reflect.verifyBVExpr decoded cert` in the comparator process, by the toolchain's
   compiled code (the `lean --run` interpreter calls the native symbol of an imported function: a 40 MB certificate
   takes 1.6 s, so it is not interpreting the checker). Accept iff `true`.

**Why accepting is sound.** An accepted axiom is the statement `verifyBVExpr ⟦E⟧ ⟦C⟧ = true` whose evaluation (by the
compiled code the tactic itself relies on) is `true`: it is a *true* proposition, so adding it as an axiom adds nothing to
the logic, whoever declared it. This is also why a hand-written axiom with the generated name and a TRUE statement is
accepted (it is a true theorem, indistinguishable from the tactic's, which is itself an `addDecl` of an axiom): the
name is a label for the policy "no axiom of your own", the evaluation is the check. A false statement (a forged
certificate) evaluates to `false` and is rejected.

**What is trusted, exactly.** (a) the compiled `verifyBVExpr` agrees with its definition on this input (the tactic's own
assumption: the compiler, `Lean.ofReduceBool`-style); (b) the toolchain's `ToExpr` instances denote the values they
encode (the tactic needs only that the *kernel* accepts `E`; this re-check also needs the converse, so it is the one
addition; the instances are 80 lines of constructor/constant pairs and the round-trip test below exercises every
constructor); (c) the kernel (unchanged). NOT trusted: CaDiCaL, the SAT answer, the decoder, the axiom's name.

**Why not the alternatives** (measured, `probe/`):

* *Kernel evaluation* (`decide +kernel` on `verifyBVExpr E C = true`): no trusted native code at all, but it did not
  finish in 240 s even for the 38 KB certificate of a 16-bit `a &&& b + a ||| b`, and certificates reach hundreds of
  MB. Not an option.
* *`evalConst` on the submission's `E`/`C`, or `nativeEqTrue` over the submission's environment*: runs compiled
  submission code (the `_expr_def` definitions are `addAndCompile`d: their IR is the submission's), which the brief and
  the threat model exclude.
* *Compile and run the inlined terms in a toolchain-only environment*: no submission code either, but it pulls in the
  compiler and its extension states for no gain over a 150-line decoder with a round trip, and its trust is the same.
* *Trust name and shape*: unsound (section 2).

## 4. The attack list (each becomes a test in `tests/checker/test_bv_decide.py`)

| attack | outcome |
|---|---|
| forged axiom over a false certificate (`verifyBVExpr (const true) "" = true`; proves `False`) | decode ok, evaluates `false`: **rejected** ("does not verify") |
| forged axiom, generated name, a TRUE statement (the real pair re-declared) | evaluates `true`: **accepted** (sound; documented) |
| true statement, another name (`myax`) | **rejected**: ordinary axiom outside the allowed set |
| generated name, other type (`= false`, `False`, a `∀`, inline operands) | **rejected**: shape |
| operands not in the exact form (`id E`, certificate `C ++ ""`, an opaque or theorem operand) | **rejected**: not a constructor term / not a string literal (true statements, refused for strictness) |
| a bv_decide axiom smuggled through a package (Mathlib module, other module) | walked like any other: re-verified wherever it lives, so a false one is rejected and a true one is harmless; the package-closure kernel replay is unchanged |
| `implemented_by`/`extern` on the checker's definitions | cannot be declared outside the defining module (parametric attributes need the declaring module); the comparator runs the TOOLCHAIN's compiled symbol, not the submission's IR or attribute data (it imports with `loadExts := false` and never `evalConst`s a submission constant); the existing `implemented_by`/`extern` scan of the submission's constants stays |
| a toolchain module shadowed by a package directory (a replaced `Reflect.olean`) | point 4 of the comparator (toolchain modules must resolve inside the installation) already covers every module the submission loads, and a bv_decide axiom needs `Std.Tactic.BVDecide` loaded |
| huge certificate / huge widths / a multiplier at width 10^5 | memory and time bounded by the supervisor's RSS and wall limits and `verify_time_limit_s` (default 900 s); a limit hit is "comparator did not report/finish": a **rejection**, fail closed. Honest cost: ~0.04 s per MB of certificate (504 MB: 22 s) |
| a DAG-shared term (2^40 paths in 40 nodes) | node budget exhausted: **rejected** |
| a term nested 10^6 deep | decoded fine (no stack overflow at 10^6); the depth limit exists for the limit above it |
| `Lean.ofReduceBool` used by hand | **rejected** (not allowed, not bv_decide-shaped) |
| `native_decide`, `decide +native` | **rejected** (`_native.native_decide.ax_*`: another name) |
| the task forbids it (`allow_bv_decide: false`) | **rejected** with a message naming the flag |

## 5. Measurements (Apple M2 Pro, loaded shared machine, `LEAN_NUM_THREADS=2`, toolchain v4.33.0-rc1)

| goal (`bv_decide`) | tactic compile | olean | certificate | decoded nodes | comparator `verifyBVExpr` |
|---|--:|--:|--:|--:|--:|
| 16-bit `(a &&& b) + (a \|\|\| b) = a + b` | 0.3 s | 69 KB | 38 KB | 16 | 1 ms |
| 24-bit ordering + 20-bit select | 0.3 s | 96 KB | 40 KB | 25 | 3 ms |
| 64-bit bit tricks (two goals) | 0.4 s | 306 KB | 105 + 141 KB | 31 + 11 | 6 + 6 ms |
| 8-bit `a * (b + 1) = a * b + a` | 0.9 s | 5.3 MB | 5.3 MB | 13 | 0.21 s |
| 10-bit, same | 5 s | 40 MB | 40 MB | 13 | 1.6 s |
| 12-bit, same | 75 s | 504 MB | 504 MB | 13 | 21.6 s (RSS 2.4 GB) |
| AND chain 300 deep | 1 s | 1.2 MB | 0.47 MB | 1201 | 16 ms |
| AND chain 2000 deep | 7 s | 22 MB | 17 MB | 8001 | 0.46 s |
| AND chain 8000 deep | 81 s | 91 MB | 72 MB | 32001 | 1.96 s |

Default `bv_decide` SAT timeout is 10 s: the 16-bit and 32-bit multiplier distributivity goals time out without
`(config := { timeout := N })`. The comparator's own start (`lean --run`, `import Lean`) is 1.2-2.1 s and 1.8-2.4 GB
RSS regardless. A hard multiplier goal is dominated by CaDiCaL at proof time; the re-check is 3 to 4 times cheaper than
the proof, so `verify_time_limit_s = 900` covers any certificate the proof limit allows.

## 6. What changes (G1)

* `check/Comparator.lean`: `--bv-decide`, `--bv-max-nodes`, `--bv-max-depth`; point 6; the report gains
  `bv_decide: {allowed, verified: [{axiom, nodes, cert_bytes, decode_ms, verify_ms, verified}]}`. Without `--bv-decide`
  a bv_decide axiom is rejected with a message naming `allow_bv_decide: false`.
* `check.py`: the refusal is gone; `allow_bv_decide` (default true, must be a boolean); `--bv-decide` is passed to the
  comparator when allowed; the solution's compile gets the sandbox additions below.
* the five `task.json`: `allow_bv_decide: true` (fdiv16's comment removed).
* tests: `tests/checker/test_bv_decide.py` (the table above, on hand-built modules), the `bv_decide_shaped` attack of
  `tests/run.py` re-pointed at a FALSE forgery over constants `E`, `C` (the old one wrote inline operands, which the shape
  check now refuses whatever they evaluate to, so it no longer exercised the evaluation), an accepted `bv_decide` row, and the
  sandbox cases of `tests/sandbox`.

## 7. The sandbox (measured)

`bv_decide` does NOT run under the checker's Lean sandbox today. The tactic writes a CNF file and an LRAT file into
the temporary directory (`IO.FS.withTempFile`), starts `cadical` as a child of `lean` and reads its proof back.
Measured with the compile spec of `Lean._run_sandboxed` (Seatbelt; `probe/sbx_probe.py`):

| spec | result |
|---|---|
| today | `operation not permitted` (no writable temporary directory) |
| + a writable `TMPDIR` | `operation not permitted` (fork denied) |
| + `TMPDIR` + fork | `could not execute external process '.../bin/cadical'` |
| + `TMPDIR` + fork + `cadical` in `exec_paths` | **works** (5.3 MB certificate: 1.0 s, as outside the sandbox; olean adopted; no temp leftovers) |

So the solution's compile (only that compile, and only for a task that allows `bv_decide`) gets: the toolchain's
`bin/cadical` as a second program in `exec_paths`, `fork`, and one fresh directory (`pol.mkdtemp`) in `write`, which
is `TMPDIR`. Capability analysis: `cadical` is the toolchain's own binary under the SAME profile (no network, no other
program, no read outside the inputs, one writable directory); a hostile file that starts it with other arguments can
read what Lean could already read and write the one temporary directory; `fork` lets Lean start only the two listed
programs (the profile's `process-exec` list is unchanged otherwise: an attempt to run `/bin/sh` or `curl` is now a child
whose exec fails, visible as an exit status and no output, not as an exception, which the `host_cadical` attack classifies);
the supervisor's RSS and wall limits are summed over the whole process group, so a runaway solver is killed with the
compile. **The one widening the sign-off should see:** with `fork` a hostile file can start further copies of `lean` (a
`lean --run` of a script it wrote into the temporary directory, which the profile lets it read) and `cadical`, all in the
compile's process group and profile; a spawning bomb is bounded by the group's summed resident memory (the polled limit,
60% of the RAM up to 12 GB, over processes of at least about 20 MB each) and the wall-clock limit, not by a process count
(macOS has no per-group process limit; `RLIMIT_NPROC` there counts the user's every process). Before this change a file could
start no process at all. On Linux the same Spec becomes
`--ro-bind-try .../cadical` and `--bind <tmp>` (the bubblewrap argv is unit-tested; no Linux host was available:
the first Linux checker must run the end-to-end row before it is trusted with this).

## 8. Flag and policy

`allow_bv_decide`: default true. A task may set `false` to forbid it (the comparator then rejects any bv_decide axiom
with a message that names the flag). Fixed-size subgoals only is a CONVENTION the proof limit enforces in practice (a
statement for all N is not bit-blastable); the checker does not try to detect it.

## 9. Residual risks

* The compiled `verifyBVExpr` is trusted as the tactic trusts it, plus the six `ToExpr` instances (section 3).
* A Lean toolchain bump may change the shapes (a new `BVExpr` constructor, another `ToExpr`): the decoder then rejects
  (fail closed) and `test_bv_decide.py` fails on the real proofs, which is the signal.
* The Linux sandbox path is unit-tested only.
* `cadical` itself is outside the model (a bug in it can only make a proof that should verify fail to produce a certificate,
  or crash the sandboxed compile; it cannot make a false certificate verify).

## 10. As built (G1, G2)

* **Files.** `check/Comparator.lean` (point 6, `BvRecheck` namespace: `decLog`/`decPred`/`decBV` decoders, `axiomOperands`,
  `defValue`, `recheck`; `--bv-decide`, `--bv-max-nodes` 5·10^7, `--bv-max-depth` 5·10^5; the report's `bv_decide` object);
  `check.py` (`allow_bv_decide` default true and boolean-checked, `Lean.compile/run(..., bv_solver=)`, `_run_sandboxed`'s extra
  Spec for the solution's compile only, `--bv-decide` for the comparator); the five `tasks/*/task.json` (`true`) and
  `design/fdiv-param/task.draft.json`; `tests/checker/test_bv_decide.py`, `tests/checker/test_import_packages.py`
  (`BvDecideFlag`), `tests/sandbox/test_sandbox.py` (the Spec of the solver compile and of every other run),
  `tests/sandbox/attacks.py` + `tests/run.py` (`bv_decide_shaped` re-pointed at a false forgery, `bv_decide_subgoal`
  accepted, `host_cadical` and `host_spawn_bomb` in the sandbox step; `--attack` now also selects sandbox attacks).
* **Decoder edge hardened after G0:** `E` and `C` must be SAFE definitions (an `unsafe` definition is not unfolded by the
  kernel's meaning).
* **Measured end to end** (macOS Seatbelt, `--sandbox require`, `tests/run.py --attack bv_decide`): `bv_decide_shaped` rejected at
  `comparator` with "the LRAT certificate Submission.forgedC does not verify: `verifyBVExpr Submission.forgedE
  Submission.forgedC` evaluates to `false`" (28 s); `bv_decide_subgoal` ACCEPTED (the `_example` reference proof plus a 16-bit
  `bv_decide` fact it uses: solution 1.14 s, comparator 11.7 s, leanchecker 11.9 s; the report lists one verified axiom).
  `leanchecker` accepts a module that declares the generated axiom (it replays axioms as declarations).
* **Sandbox attacks, measured** (`tests/run.py --attack host_cadical,host_spawn_bomb --sandbox require`): `host_cadical`: the
  legitimate `cadical` run on a CNF in the temporary directory works, and its proof written outside, a CNF read from another
  directory, `/bin/sh` and `curl` are all BLOCKED (with `fork` granted a program that may not run is a child whose exec failed:
  an exit status and no output, not an exception, which is why the attack classifies by output); a real `bv_decide` fact in the
  same file is accepted with one verified axiom; with `--sandbox off` (the control) the marker IS written. `host_spawn_bomb`
  (a file that starts copies of `lean`, each starting four more, from a script it wrote into the temporary directory): stopped by
  the supervisor's summed-RSS limit (`SVGOLF_MEMORY`, limit lowered to 1.5 GB) in 20 s, and no process of the bomb is left.
* **`tests/checker/test_bv_decide.py`** (real Lean, hand-built chain, ~80 s): 10 tests green: real proofs (1 axiom, 2 axioms, an
  axiom behind a helper) accepted; a forged-true axiom accepted; forged-false (kernel accepts `1 = 2` from it), wrong shapes
  (four), another name, `id E`, `C ++ ""`, the node budget, the depth limit, `Lean.ofReduceBool`, `native_decide` and the
  forbidden flag all rejected with the intended message.
* **A consequence for the shared tree:** the five `task.json` files are inputs of the `tests` Lake library (`taskFiles`), so the
  next `lake build` of svgolf there re-elaborates `tests` (the negative designs' refutations); nothing else changes.

## 11. The ruling and what is kept (G3, 2026-11-01)

* **Decision.** Not supported for now. The sandbox widening of section 7 is the whole objection (the comparator's re-verification
  was not): with `fork` granted, a hostile file in the compile can start further copies of `lean`, bounded by the supervisor's
  summed memory and wall limits and not by a process count; measured by `host_spawn_bomb`.
* **Behaviour now.** `BV_DECIDE_SUPPORTED = False` in `check.py` (one constant, one assignment, no reader of an environment variable,
  option or task key; an AST test pins it). `allow_bv_decide` absent or false: forbidden. `true`: infrastructure error ("the checker
  does not support external SAT solvers (decided 2026-11-01): allow_bv_decide must be false or absent"). `Lean._run_sandboxed`
  honours `bv_solver` only while the constant is True, so the Spec NEVER gets `fork`, the exec of `cadical` or the private
  `TMPDIR` (`test_sandbox.py` pins it with the solver binary present and the flag asked for). Without `--bv-decide` the comparator
  rejects a `bv_decide` axiom with "`bv_decide` is not supported: it runs an external SAT solver (cadical), which the checker does
  not support (decided 2026-11-01); prove the goal with decide +kernel, omega, simp or a symbolic argument".
* **The friendly failure.** With the sandbox on, a `bv_decide` proof fails at `solution` with `operation not permitted` at the
  `bv_decide` token and no mention of the tactic or the solver; `check.py` adds `HINT: bv_decide runs an external SAT solver
  (cadical) ...` when the file uses `bv_decide` in code (a comment does not count) and a Lean error sits on a line that mentions
  it, or a message names the solver (`bv_decide_hint`). With `--sandbox off` the proof compiles and the comparator's message above is
  the hint. A test for each path: `BvDecideFlag` (fake Lean, the hint and its no-false-positive cases) and `tests/run.py`
  `bv_decide_subgoal_sandbox` / `bv_decide_subgoal_off` (real Lean).
* **Kept, with tests** (all green): the comparator's point 6 (`test_bv_decide.py`, which passes `--bv-decide` itself); the Spec grant
  (`test_sandbox.py`, constant forced True inside the test); the end-to-end groundwork rows (`bv_decide_groundwork_accepted`,
  `bv_decide_groundwork_forged`, `host_cadical`, `host_spawn_bomb`, run through `tests/checker/check_bv_enabled.py`, a wrapper that
  sets the constant in its own process, never an environment switch). The default rows pin the shipped behaviour:
  `host_cadical (default flags)` and `host_spawn_bomb (default flags)` show that by default nothing can be started.
* **Enabling later**: README.md, "`bv_decide`", "What enabling would take" (five steps: the sign-off, the constant, the task flags and
  the two attack rows, the checklist, the docs).
* **The task files**: the five `task.json` are back to `"allow_bv_decide": false` (what they said before WP-BV; fdiv16's comment, which
  said "flip this once the comparator can", now gives the real reason).
