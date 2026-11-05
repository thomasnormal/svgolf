# svGolf

svGolf is a [zk.golf](https://zk.golf)-style competition for SystemVerilog
hardware. For each task you:

1. write a circuit in SystemVerilog;
2. prove in Lean that it meets the task's **trusted statement**, under the
   ls-sv semantics of [lean-surfaces](https://github.com/thomasnormal/lean-surfaces/tree/01945ccf28bb1f95347ebabe9704adbd32e4e045) (the sv-0.2 tier: `load_design_sv2`,
   `run2`, the `⊨₂` judgment and `Terminates2`);
3. get scored by a pinned synthesis flow, weighed on the sky130 standard
   cells (flow A0'): **area** in um^2 and **time** in ps (the critical-path
   delay; on a clocked task, cycles x the clock period). Smaller is better
   on both; the leaderboard keeps their Pareto frontier
   ([Leaderboard](#leaderboard)). Area in NAND2 gate equivalents and depth
   in gates are extra columns. Every number can be reproduced bit for bit
   ("Reproduce a score" under [Scoring](#scoring)).

A proof that a circuit is correct is worth nothing if the statement can be
met without computing anything, so the statements, the checker and the
scoring are all built to be hard to game. `SvGolf/Task.lean` explains the
statement; "Checker v0 limits" below says what is not covered yet.

Every refusal the checker makes, why, what you can write instead, which
refusals are meant to be lifted later (and what has to exist first) and
which never will be: [REFUSALS.md](REFUSALS.md) (generated from
`docs/sv-refusals.json` of lean-surfaces by `tools/gen_sv_refusals.py`).

## Quick start

```bash
# in a clone of this repository, from its root
# 1. is the design admissible, and what does it score? (15 s, no proof needed, never accepts)
python3.12 check.py tasks/add my_adder.sv --unproved
# 2. prove it: PROVING.md (the loop, the tactics, two worked references) -- then the real check (about a minute;
#    its post-synthesis stage runs LIGHT by default, a few seconds: local feedback, see "Checking")
python3.12 check.py tasks/add my_adder.sv MyAdder.lean
# 3. record it on YOUR machine (re-runs the check IN FULL MODE: the leaderboard's artifacts are never light;
#    see "Leaderboard" for what the record is, and for what it is not yet)
python3 leaderboard/leaderboard.py add --task add --player alice --sv my_adder.sv --lean MyAdder.lean \
    --data-dir ./my-records
```

Start from a task's own `tasks/<name>/README.md`: it states the task, what is banned, and links the
reference design and its proof. If your Lean wrapper is not the default (a shared machine), set
`SVGOLF_LEAN_WRAP` once; `check.py` and `leaderboard.py` both read it.

## Rules

* **Proofs are symbolic and parametric.** When a task is n-bit, the
  statement covers every `N` in the task's range, and so must the proof:
  induction on bit indices, `BitVec` algebra, the ls-sv proof layers.
  `bv_decide` is NOT supported for now: it runs an external SAT solver, which
  the checker declines to sandbox (decided 2026-11-01; "`bv_decide`" below).
  Use `decide +kernel`, `omega`, `simp` or a symbolic argument. `native_decide`
  is banned. `sorry` and `admit` never pass (the axiom check rejects `sorryAx`).
* **Axioms.** Only the task's `allowed_axioms` (normally `propext`,
  `Classical.choice`, `Quot.sound`). No new axioms, no `extern` or
  `implemented_by`: an `axiom` of your own, the axioms `native_decide` and
  `bv_decide` generate, and `Lean.ofReduceBool` are all rejected.
* **Banned operators, per task.** A task bans the run-time operator that IS
  the task, and anything Yosys turns into the same cell: the adder and
  multiplier tasks ban `+ - * / % **` (Yosys's `alumacc` merges `+` chains
  into the same `$macc` cell as `*`); the divider bans `/ %`. Constant
  arithmetic stays allowed: parameter expressions, genvar loops (the step
  may be `i++`, `i--`, `i = i + 1`, `i += 1`, `i = 1 + i`, `i = i - 1` or `i -= 1`;
  any other step such as `i += 2` or `i = i + K` is refused at the `design`
  stage), index arithmetic over parameters and genvars (`a[i+1]`),
  procedural `for` counters (`k++`), constant functions.
* **One program for both tools (the source gate).** The proof is about the
  design the extractor reads (through slang); the score is about the design
  Yosys reads. The checker makes them ONE text: it refuses preprocessor
  directives other than `` `timescale `` and `` `default_nettype none|wire ``
  (Yosys predefines `SYNTHESIS` and `YOSYS`, slang does not, so
  `` `ifdef SYNTHESIS `` would prove one circuit and score another),
  attributes `(* ... *)` (Yosys gives `full_case`, `parallel_case`, `nosync`,
  ... a synthesis meaning; slang none), comments that Yosys reads as pragmas
  (`// synopsys translate_off`, `// synopsys full_case`, ...), and the
  `unique` / `unique0` / `priority` qualifiers (Yosys reads them as
  `full_case`/`parallel_case`, a synthesis don't-care, while ls-sv runs the
  first matching arm: a `unique case` that never matches scores 0 GE). It
  then strips every comment, and the extractor, the banlist and Yosys all
  read that canonical text (`score/srcgate.py`).
* **No host access (also the source gate).** The checker runs untrusted text
  on the organizer's machine, and the tools it runs read more than the text:
  Yosys's `read_verilog` opens the file of a `$readmemh` / `$readmemb` itself
  while it reads the design (measured with the pinned Yosys 0.53: the file's
  contents become the memory's initial value, so one submitted text scores
  9.331 GE with one host file and 0 GE with another, and a file that does not
  exist is an error). A submission could pull a host file (a hidden salt, an
  oracle) into the netlist and leak bits of it through its score, and the
  proof never sees the file. The gate therefore refuses every construct that
  reaches the host: the memory-file tasks (`$readmemh`, `$readmemb`,
  `$writememh`, `$writememb`), the file I/O family (`$fopen` ... `$ferror`),
  process and environment access (`$system`, `$test$plusargs`,
  `$value$plusargs`, `$getenv`), the wave and dump writers (`$dumpfile`,
  `$dumpvars`, `$dumpports*`, the `$fsdb*` / `$shm_*` families), the
  coverage-database, SDF and Annex D file tasks (`$coverage_save`,
  `$sdf_annotate`, `$input`, `$log`, `$save`, ...), and DPI (`import
  "DPI-C"`, `export "DPI-C"`: native code). It reads slang's syntax tree, not
  the characters: a comment or a string literal that only NAMES one of them is
  fine, while a use in a function that is never called, in a generate branch
  the scoring point does not take, in a module the top does not instantiate or
  in a parameter initializer is refused all the same. An escaped identifier
  that begins with `$` is refused whatever it spells: Yosys's lexer gives
  `\$readmemh` the very name of the system task (and runs it), where slang
  reads an ordinary identifier (the same trick lets a user function `\$clog2`
  shadow the builtin for one tool and not the other). The console and
  simulation-control tasks (`$display`, `$write`, `$finish`, ...) and the pure
  system functions (`$clog2`, `$bits`, `$signed`, ...) stay. The table is
  `HOST_FAMILIES` in `score/srcgate.py`, one row per family. **This rule covers
  the SystemVerilog text.** The Lean file is not scanned for `#eval`, `IO`,
  `run_cmd`, `elab` or `initialize` (the shipped references use a local `elab`
  and macros, and Lean metaprograms reach IO under many names); it is CONTAINED
  instead: every process that runs submitted text runs in an operating-system
  sandbox (see "Sandbox" under "Checking"), and the same sandbox is the second layer under Yosys and
  Verilator for the constructs the gate would miss. Only the reading of files was ruled on (decided
  2026-10-31); the rest of the family (writes, programs, the environment, dumps, DPI) is the
  register authors' extension of that ruling, awaiting confirmation.
* **No x or z value may arise (the 4-state rules).** ls-sv, like IEEE 1800
  simulation, computes with unknown values: `if (x)` takes the else branch,
  a case item or `==` operand with a `z` bit never matches a known input.
  Yosys reads an `x`/`z` as a synthesis don't-care: it drops x/z bits from
  comparisons and resolves an unknown value however it likes. So wherever an
  `x` reaches a decision, the proved and the scored circuits can differ, and
  the player picks where (measured: the complementary items `2'b0z` and
  `2'b1z` on `{a[0], cin}` match no input in ls-sv and EVERY input in
  Yosys, so the default arm ls-sv runs is dead logic in the netlist, and the
  scored arms can differ from it on one input pair in 2^32). Every SOURCE
  of an x or z is therefore refused, exactly:
  * the source gate refuses every `x`, `z` or `?` digit in a literal
    (`1'bz`, `4'b10x0`, `'x`, `'z`), except the wildcard digits of a `casez`
    item (`z`, `?`) and of a `casex` item (`x`, `z`, `?`), where both tools
    agree they match anything. No `'x` don't-care assignments either;
  * the `fourstate` stage (`score/fourstate.py`, at the scoring point)
    refuses a parameter or constant expression with unknown bits (`1 / 0`
    is not banned as constant arithmetic, but it is x), a constant index or
    range outside the declared range, a run-time index whose type lets it
    leave the declared range (an out-of-range read is x: declare a
    power-of-two array or narrow the index), and, by Yosys's `check`, a net
    that is used but undriven, has conflicting drivers, or sits on a logic
    loop;
  * a program slang's driver rejects is rejected, analysis errors included
    (decided 2026-11-01): the `banlist` front check and the `fourstate` stage
    read the errors of slang's ANALYSIS pass, which `getAllDiagnostics()`
    omits (`score/slangdriver.py`, per parameter point): two writers of one
    variable when one is `always_comb`/`always_ff` (an `initial` block counts),
    continuous and procedural assignments to one variable, writing an input
    port, an `always` without timing control. The verdict uses the slang
    driver's own severities and cannot be downgraded by a pragma
    (`tests/add/attacks/slang_*.sv`).
  Three x sources have no rule yet because nothing can reach them today:
  run-time `/` and `%` (x on a zero divisor) are banned by every task; a
  function-local variable or return value read before it is assigned
  needs user function calls, which ls-sv does not have (such a design loads
  with an Unsupported node and is rejected at the `design` stage:
  `tests/_example/attacks/fn_uninit.sv`); and a
  latch that is never loaded (`always_latch`, or `always @*` assigning a
  variable on some paths only: x in IEEE, 0 in Yosys) is refused by rule (e)
  of `score/fourstate.py` (`proc` inferred a latch; `latch_never.sv`,
  `latch_star.sv`, rejected at the `fourstate` stage). A task that admits the first, or
  an ls-sv PR that adds a latch construct, needs its own rule first.
* **No other restrictions.** Any SystemVerilog that passes these rules and
  that ls-sv and Yosys accept is fair game. Where ls-sv and Yosys disagree on
  what the same text means, that is a bug report we want, not an exploit.
* **The post-synthesis check backs this up** (the checker's `postsynth`
  stage, `check/postsynth.py`). The proof is about ls-sv's reading of the
  design, the score about the netlist Yosys built from the same text. After
  scoring, the checker simulates both at the scoring point on a vector set
  (the task's whole budget in `full` mode, a deterministic subset of it in the
  `light` mode that is `check.py`'s default for local feedback: see "Checking",
  "Post-synthesis modes") and rejects the submission unless they agree on every
  vector:
  * ls-sv's side is `design.sem` itself, the term the proof is about, run by
    `run2` under both schedules (`check/SvEval.lean`, compiled as
    `svgolf-eval`); the netlist's side is the very gate netlist the score
    counted (re-read and re-counted to be sure), simulated by Verilator (a
    C++ model of the netlist and Yosys's gate-cell models, built once per run
    while ls-sv evaluates, all vectors through one harness run);
  * the vectors are all-0, all-1, walking ones and zeros on every input, the
    task's corner values, inputs built from every constant the design
    compares against (so a difference hidden behind `a == 16'hBEEF` is
    found), and seeded random vectors; all deterministic, the seed recorded;
  * it fails closed: an ls-sv run that does not complete, an `x` or `z` in
    ls-sv's outputs, an unknown-valued constant in the netlist, a netlist
    Verilator will not lint, build or run cleanly, a harness that prints the
    wrong number of rows, the two schedules disagreeing, or different ports
    all reject;
  * **Verilator is a 2-state simulator** (decision 10/29: svGolf simulates with
    Verilator, not Icarus), so the netlist side has no `x` or `z`, and this
    stage cannot see an unknown the netlist computes. It does not need to:
    Yosys's gate cells (`simcells.v`) are total Boolean functions, so an
    unknown can only come from an unknown-valued constant in the netlist
    (`1'hx`; scanned for, and such a netlist is rejected on every vector,
    the report showing what a 2-state model reads) or from an undriven or
    unconnected net or pin (Verilator's lint runs with `-Wall` and every
    warning fatal except `DECLFILENAME` and `UNUSEDSIGNAL`: UNDRIVEN,
    PINMISSING, PINCONNECTEMPTY, MULTIDRIVEN, UNOPTFLAT and the WIDTH family
    reject). The x/z defences stay where they are: the source gate, the
    `fourstate` stage, and ls-sv's own 4-state outputs on the other side of
    the comparison. What is lost against the 4-state Icarus run it replaced is
    only a witness for an unknown that the netlist invents from known inputs
    and driven nets, and Yosys gate cells have none to find;
  * a rejection is written as a bug report: per failing vector the inputs,
    ls-sv's outputs, the netlist's, and Verilator's reading of the source
    (also 2-state) as a third opinion, with who agrees with whom. File it:
    either ls-sv or Yosys is wrong about your design;
  * **light and full** (WP-C2). The default `light` mode is a safety net for
    local feedback: it runs a deterministic SUBSET of the full vectors (a
    light rejection is always a full rejection) in seconds instead of
    minutes. Competition and verification runs, `leaderboard.py add` /
    `verify` and `tests/run.py` use `full`, which is the whole budget
    described here. Official artifacts are never light.

  It is sampling, not proof: a difference confined to a rare input region
  that no constant comparison selects slips through (see "Checker v0
  limits"). That is why the known disagreements are refused statically, and
  exactly, before any proof is tried (the source gate's `unique`/`priority`
  and x/z-literal refusals, the 4-state rules); the post-synthesis check is
  the backstop for the ones nobody has found yet (a Yosys or ls-sv bug).
  Measured on `tests/<task>/attacks/` with the static rules bypassed
  (`postsynth_alone` in `tests/expected.json`): it rejects a `1'bz`/`1'bx`
  case item (every vector), complementary z items, x/z constants in `==`
  operands, an undriven net and an out-of-range read, whose differences
  cover most of the inputs (x/z localparams and a constant `1 / 0` it
  rejects only because ls-sv does not support them and it fails closed);
  it rejects a z item confined to 2^-28 of the inputs only
  through the harvested comparison constant (its 0/1 bits; its x/z bits
  stay free); it PASSES `add`'s `zpair_add_rare.sv` and `_example`'s
  `oob_rare.sv`, whose difference is one input pair in 2^32 selected by a
  reduction-AND rather than a comparison constant. Before the x/z-literal
  rule, the `1'bz` and `1'bx` case items passed every other stage with
  ls-sv computing the right function (only a proof, which nobody wrote,
  stood between them and a 0 GE entry). For competition runs, set a secret
  `SVGOLF_POSTSYNTH_SALT` so that a player cannot predict the random
  vectors (the seed is recorded either way, so a run stays reproducible
  afterwards).
* **Scoring** is `score/score.py` with the pinned two-stage flow
  (`score/canon.ys`, then `score/svgolf.ys` in a fresh Yosys process) and the
  pinned table `score/ge.json`, at the task's scoring point (e.g. `N = 16`).
  The score depends on the circuit's expression structure, not on its
  layout or names. Reordering module items has not moved a score in the
  adder, multiplier and divider references, but it does for a flat netlist
  of many assigns (`aes_sbox`: 198.986 to 209.321 GE across statement orders
  of one circuit; `tasks/aes_sbox/README.md`, Findings), so it is not
  guaranteed not to (the canonical RTLIL is numbered differently), and swapping the operands of a commutative operator
  does change it. This is accepted (decided 2026-10-31): the score is a function of the file as submitted, and a golfer
  searches statement orders with the pinned flow before submitting. Not every structural choice survives synthesis, though:
  ABC re-derives the logic, and some RTL carry-structure choices (a final
  adder that steps two bits at a time instead of one, in the dry run) score
  identically to the milli-GE. Score a block standalone with `score/score.py`
  before building a proof around it. See "Scoring".

## Layout

```
svgolf/
  lakefile.toml, lean-toolchain     the svGolf Lake project (requires lean-surfaces)
  SvGolf/Task.lean                  TRUSTED: the task-statement helpers (CombTask)
  SvGolf/Comb.lean                  proof helpers (untrusted, kernel-checked)
  SvGolf/LoadSv.lean                `load_sv`: load a design from its .sv (extracted at
                                    elaboration time, cached under .lake/envelopes/)
  tasks.lean                        aggregator of the `tasks` library (the Spec files, then the
                                    Properties files)
  tasks/<name>/                     one directory per task: what a player needs (below)
  tests.lean                        aggregator of the `tests` library (the Refute files)
  tests/run.py                      the regression runner: runs everything (see "Tests")
  tests/expected.json               golden expectations: every score quoted in a README,
                                    every negative's rejection stage
  tests/<name>/                     a task's tests (below)
  check.py                          the checker (v0)
  check/Comparator.lean             the checker's Lean side (statement, axioms, extern)
  check/envelope.py                 the ONE extraction path (source gate, then the pinned
                                    extractor): check.py, load_sv and the validation scripts
  check/postsynth.py                the post-synthesis check (ls-sv vs the scored netlist)
  check/SvEval.lean                 its ls-sv side, the executable `svgolf-eval`
                                    (`design.sem` under `run2` on many vectors)
  score/score.py                    scoring; score/canon.ys + score/svgolf.ys (the two
                                    stages) and score/ge.json are pinned
  score/srcgate.py                  the source gate (one program for slang and Yosys)
  score/banlist.py                  the operator banlist (pyslang + Yosys backstop)
  score/fourstate.py                the 4-state rules (no x or z value can arise)
  score/ppa.py, score/ppa_pins.json  the EXTRA sky130 columns (area um^2, delay ps) of the scored
  score/ppa_mapped.ys,              netlist (flow A0') and of its real `abc -liberty` mapping
  score/ppa_mapped_pins.json        (flow A1', the pinned Yosys script and its pins), recorded by
  score/PPA.md, score/lib/          check.py as `ppa` and `ppa.mapped`; score/PPA.md says what
                                    they are and are not; score/lib/ (git-ignored) holds the
                                    fetched liberty (`python3.12 score/ppa.py --fetch-liberty`)
  score/test_*.py, score/tests/     tests and fixtures (score/tests/gate: the gate's;
                                    score/tests/fourstate: the 4-state rules';
                                    score/tests/ppa: the PPA goldens of both flows and the netlist idioms)
  score/time_limits.py              the proof time limits from measurements: the rule
  score/time_limits.json            ("Proof effort") and the cold runs it is applied to;
                                    neither is hashed by the checker
  leaderboard/leaderboard.py        the leaderboard: records of accepted submissions, Pareto
                                    frontier, boards, verification (leaderboard/README.md)
  leaderboard/data/<task>/          one <record_hash>.json per accepted submission, with its
                                    .sv and .lean next to it
  tests/leaderboard/                its tests (synthetic check results, no Lean)
  tests/checker/test_advisories.py  the advisory outputs of check.py (functional oracles,
                                    `warnings`, `--tactics` classification, `dev_hint`), the
                                    post-synthesis mode selection and light vector set, the
                                    generated Design module: no Lean
  tests/checker/test_design_stage.py  the `design` stage rejecting an unsupported construct,
                                    with a fake Lean
  tests/checker/test_import_packages.py  imports from the Mathlib packages (the import probe,
                                    rejection vs infrastructure error, the search-path tripwire
                                    inside the real `integrity_snapshot`, the import cross-check
                                    against the comparator's report), with a fake Lean
  tests/checker/test_comparator.py  check/Comparator.lean on a hand-built module chain with
                                    REAL Lean (a planted `False`, a package axiom, a shadowed
                                    toolchain module, an `extern`): the `comparator` step
  tests/checker/test_bv_decide.py   the comparator's DORMANT re-verification of `bv_decide` axioms
                                    with REAL Lean (real proofs accepted with `--bv-decide`, forged
                                    and malformed axioms, hostile terms, `ofReduceBool`,
                                    `native_decide`; rejected by policy without the flag): the
                                    `comparator` step
  tests/checker/check_bv_enabled.py  check.py with the dormant `BV_DECIDE_SUPPORTED` forced on in its
                                    own process: the groundwork rows of `tests/run.py` only
  tests/checker/test_ppa_wiring.py  the `--ppa` modes, the absent-liberty path, the tripwire, flow
                                    A1''s `mapped` block and its failure modes, and the
                                    byte-identity of the default result against the checker
                                    from before the wiring (goldens in tests/checker/ppa_wiring/;
                                    byte_identity.py is its normalizer): fake Lean
  tests/imports/test_allowlist.py   the checker's import allowlist, against tests/expected.json
                                    ("import_allowlist"), and the import closure of Mathlib
                                    recomputed from the package sources: no Lean, a second or two
  tests/imports/mathlib_band.lean   the `_example` reference proof with Mathlib tactics in its
                                    arithmetic: the accepted fixture of the `attacks` step, and
                                    the base of its Mathlib attacks
  PROVING.md                        how to prove a task with the sv_comb tactics (a guide for
                                    contestants), with the tactic proofs of `add` and `mul`
  PLAN.md                           the lead's plan (not part of the framework)
```

Extractor output is never committed (`.gitignore`: `*.sv.json`,
`*.probes.json`): `check.py` extracts each submission into its staging
directory, and `load_sv` extracts into the cache `.lake/envelopes/` (delete it
at will; the next build re-extracts).

### A task directory

```
tasks/<name>/
  README.md        the task text: the module header to implement, the statement in
                   words, the rules (banlist, axioms, time limit, scoring point)
  task.json        machine-readable task (below)
  Spec.lean        TRUSTED statement, module `tasks.<name>.Spec`
  Properties.lean  the statement as named properties, one definition per thing a design must
                   satisfy, and `statement_iff_properties`: the statement holds exactly when every
                   property does (proved, NOT trusted; module `tasks.<name>.Properties`)
  properties.json  each property's name, Lean declaration and plain-words explanation, and the
                   definitions they use (the property cards of the task's page)
  REVIEW.md        optional: the review of the trusted statement for the project owner (hard
                   gate "reviewed trusted Spec.lean"): the statement in words, its sources, the
                   cheating surfaces and their defences (`aes_sbox` has one)
  oracle.py        optional: a Python oracle of the task's function, for the advisory
                   functional check (NOT trusted; `oracle` in the task.json table)
  reference/       PROVED sample solutions only, each a pair <stem>.sv + <stem>.lean
                   (a submission, see "Submitting"); a draft task instead holds its
                   goalpost <stem>.sv + <stem>.partial.lean (unproved, see `status`)
  IEEE754.lean     `fdivp` only: TRUSTED, the IEEE 754 division spec its statement uses
                   (module `tasks.fdivp.IEEE754`)
  spec_validate/   `fdivp` only: the spec's differential validation (untrusted tooling)
  (no proof library: a task ships no proved facts about designs; reusable proof code goes to
  lean-surfaces' `LeanModels/Sv/Lib` (`LeanModels.Sv.Lib`), the rest into the
  task's reference proof)
```

and its tests, which a player does not need:

```
tests/<name>/
  negative/        designs that must fail: *.sv, README.md, and Refute.lean (module
                   `tests.<name>.negative.Refute`, in the `tests` library:
                   kernel-checked proofs that they do NOT satisfy the statement,
                   loading each design with `load_sv`)
  baselines/       designs that are scored but never accepted: unproved,
                   simulation-only circuits and banned-operator baselines
  validate/        simulation checks (Verilator, ls-sv `run2`, the scored
                   netlists), with a README
  attacks/         designs where ls-sv and Yosys read one text differently (x/z case
                   items, an undriven net, an out-of-range read, `===` against x,
                   `unique` violations, ...): each must be rejected at the stage
                   `tests/expected.json` gives (`source`, `fourstate`, `banlist`)
  results/         measurement records the READMEs cite (check.py outputs, logs)
```

`tests/canon/variants.py` writes the layout, renaming, reordering and
commutation variants of a design that the `canon` step scores.

The expectations (each negative's rejection stage, every score quoted in a
README, gate mix included, which baselines the banlist rejects) are in
`tests/expected.json`, which `tests/run.py` checks.

`task.json` fields:

| field | meaning |
|---|---|
| `name`, `title` | the task's name (the directory name) and a one-line title |
| `status` | `ready`: at least one proved reference, `references` lists them; `draft`: no proved reference yet, `references` is `[]` and `draft_reference` names the goalpost |
| `kind` | `comb-family` (one parameter, `CombTask.Statement`; or several, as `fdivp`: the statement constant then has type `(Nat → … → Nat → Design2) → Prop`, a family of fixed-size tasks, `tasks/fdivp/Spec.lean`) or `comb-fixed` (no parameter, `CombTask.StatementFixed`; `parameters` is `[]`, the scoring point `{}`) |
| `top` | the top module name the submission must use |
| `parameters` | `[{name, range}]`: the overridable parameter(s) the top must have, by name and in order (the scoring script overrides them by name); localparams are free |
| `ports` | informative copy of the interface (`Spec.lean` is authoritative) |
| `statement` | `{module, constant}`: the Lean module and the statement constant, of type `(Nat → Design2) → Prop` |
| `banlist` | `{operators}`: banned run-time operators, from `+ - * / % **` |
| `probe_points` | parameter points for the extractor's multi-point cross-check (`--probe-points`), also used by the banlist front check; the checker always adds the scoring point and the backstop points |
| `scoring` | `{params, depth_budget}`: the scoring point, and a depth budget (`null` = none; a depth over budget rejects) |
| `leaderboard` | optional, `{depth_budget}`: a depth budget for the leaderboard only (positive integer, `null` or absent = none). The board then also ranks the best area under it and flags the entries over it; nothing is rejected (that is `scoring.depth_budget`). See "Leaderboard" |
| `backstop_points` | parameter points for the Yosys banlist backstop (default: the scoring point) |
| `allowed_axioms`, `allow_bv_decide` | the axiom policy: the axioms a proof may use, and `bv_decide`'s switch. `bv_decide` is not supported (see "`bv_decide`"): absent or `false` forbids it, `true` is an infrastructure error ("the checker does not support external SAT solvers"), and so is a non-boolean. The shipped tasks say `false` |
| `postsynth` | the post-synthesis check's budget (optional; defaults in brackets): `random` [1000] seeded random vectors, `corners` [{}] `{input: [values]}` whose cartesian product is checked (an input without values: 0 and all-1), `harvest_pairs` [2000] compatible pairs of harvested comparison constants, `light_vectors` [256] the most vectors the LIGHT mode runs (set from the reference's ls-sv cost per vector: `mul` has 40), `fuel` [100000] `run2`'s fuel per run, `time_limit_s` [900] a fail-closed cap on the ls-sv evaluation. Counts, not a time budget, decide what is checked, so a result does not depend on the machine |
| `oracle` | optional, `"oracle.py"`: a Python ORACLE of the task's function in the task directory, `def oracle(params: dict, inputs: dict) -> dict` (`params`: the point the `postsynth` stage evaluates at, e.g. `{"N": 16}`, `{}` for a fixed-size task; `inputs`: input port name to int; result: output port name to int, already masked to the output's width). With one, the `postsynth` stage also compares ls-sv's outputs on every vector it already uses with the oracle's and reports `functional` and, on a mismatch, one `warnings` line (see "Checking"); it never changes a verdict. The oracle is a contestant convenience and NOT part of the trusted statement (`Spec.lean`, `SvGolf/Task.lean` and `fdivp`'s `IEEE754.lean` are): every task has one today (`fdivp`'s is exact `Fraction` arithmetic for every format, written separately from the spec's own validation oracle `spec_validate/oracle.py`); a task without one is simply not checked |
| `time_limit_s` | wall-clock limit for compiling the proof (120 s for every task, the rule in "Proof effort"; `score/time_limits.py` checks it) |
| `verify_time_limit_s` | wall-clock limit for each of the comparator and `leanchecker` (default 900) |
| `references` | `[{sv, lean, note?}]`: the proved reference solutions, each a pair `reference/<stem>.sv` + `reference/<stem>.lean` that `check.py` accepts (`tests/run.py` checks it, and the score). Several pairs may be listed; the first is the one `tests/run.py` submits the negative designs with. `add` and `mul` list two: `<stem>` (proved with the sv_comb tactics) and `<stem>_byhand` (the same design, a byte-identical `.sv`, proved with no tactic: the measured baseline of the proof effort); `tests/expected.json` marks the second `same_design_as` the first, and `tests/run.py` checks the bytes |
| `draft_reference` | draft tasks only, `{sv, lean, note?}`: the goalpost design `reference/<stem>.sv` and its partial, unproved Lean file `reference/<stem>.partial.lean` |

Keys starting with `_` are comments. Add a task by creating `tasks/<name>/`,
its tests under `tests/<name>/` and its entry in `tests/expected.json`,
adding `import tasks.<name>.Spec` to `tasks.lean` (and
`import tests.<name>.negative.Refute` to `tests.lean`), and running
`tests/run.py`, which also checks this layout.

## The statement

`SvGolf/Task.lean` (read its docstring) defines a combinational task as an
interface (input and output ports with widths that are functions of `N`) and a
function on `BitVec`s, and the statement `CombTask.Statement t sem` as: for
every `N` in range,

1. the design's input ports and output ports are EXACTLY the task's (names,
   order and widths);
2. `Unclocked` and `Terminates2`: no process is clocked (no `always_ff`, no
   `always @(posedge …)`: ls-sv runs those once per cycle whatever their
   clock holds, so a register on a clock nothing drives would hold the right
   value in ls-sv and `x` in every simulator, and score 0 GE), and every run
   completes, under every schedule and stimulus;
3. in every completed run, every cycle whose stimulus entry drives every
   input with a known value ends with the outputs holding exactly the
   function's value.

The docstring goes through the ways a weaker statement could be met
vacuously (a design that never settles, hypotheses that never hold, stimulus
width and name conventions, extra or missing ports, `x` values, history) and
how each conjunct rules them out. Each task's `tests/<name>/negative/Refute.lean` checks a
few of them in Lean.

`SvGolf/Comb.lean` has the untrusted helpers: `CombTask.satisfiedAt_of_comb`
reduces the statement, for a design in the comb profile with an acyclicity
certificate, to ONE settled-state lemma (pure combinational reasoning, no
runs); `CombTask.SatisfiedAt.exists_run` is the non-vacuity theorem;
`CombTask.not_computes_of_counterexample` refutes by one concrete run.

## Building

```bash
lake build          # SvGolf, tasks (statements, fdivp's IEEE 754 spec), tests (refutations),
                    # and the checker's ls-sv evaluator svgolf-eval (native code)
```

`tests` needs Python: its refutations load their designs with `load_sv`,
which runs `python3.12 check/envelope.py` (pyslang and the pinned extractor)
at elaboration time and caches the envelopes under `.lake/envelopes/` (set
`SVGOLF_PYTHON` for another interpreter). The library `needs` every `.sv`
file under `tasks/` and `tests/`, every `task.json` (a design's top and probe
points come from its task), the extractor and the extraction scripts
(`lakefile.toml`), so changing a design re-elaborates the refutations, as
lean-surfaces' own `lakefile.toml` does for its envelopes. `lake build SvGolf
tasks svgolf-eval` (what the checker builds) needs no Python.

`svgolf-eval` (`check/SvEval.lean`, a `lean_exe`) is compiled to native code:
building it compiles the C of the `LeanModels.Sv` modules it imports into the
dependency's `.lake/build/ir` (`.lake/packages/lean-models/.lake/build/ir`; about 50 s the first
time, next to the oleans svGolf already builds there), and the binary is about 100 MB.

`lean-models` is a Lake dependency with its own build under `.lake/packages/lean-models`, which Lake alone
writes. (Inside lean-surfaces, where svGolf was developed, a harness of that repository could rewrite a
`LeanModels.Sv` olean outside Lake, after which the link of `svgolf-eval` failed with undefined `l_...`
symbols until the affected modules' `.trace` files were moved away and Lake rebuilt them; a separate build
does not have that hazard.)

The project requires lean-surfaces' root package `lean-models` by git, at the revision `lakefile.toml` and
`lake-manifest.json` pin, and the dependency's packages (Mathlib and friends) at the revisions its manifest
pins; Lake clones them into `.lake/packages/`. Since `LeanModels.Sv` imports no Mathlib, nothing of Mathlib
is built; `LeanModels.Sv` modules are built in the dependency's `.lake/build`. `lake-manifest.json` is
committed; resolving it from scratch (`lake update`, or a deleted manifest) runs Mathlib's post-update hook,
which fetches Mathlib's olean cache: set `MATHLIB_NO_CACHE_ON_UPDATE=1` to skip it.

## Submitting

A submission is two files: `solution.sv` and `Solution.lean`. The checker
extracts the design itself and generates the trusted module
`Submission.Design`:

```lean
import LeanModels.Sv.Ingest2
import tasks.<name>.Spec
namespace Submission
load_design_sv2 design from "<the envelope the checker extracted>"
abbrev Goal : Prop := <the task's statement constant> design.sem
end Submission
```

`Solution.lean` must `import Submission.Design` and prove

```lean
theorem Submission.solution : Submission.Goal
```

It may import `Init`, `Std`, `Lean`, `LeanModels.Sv.*`, `SvGolf.*`,
and `tasks.*`, and Mathlib with the packages it imports (`Mathlib.*`,
`Batteries.*`, `Aesop.*`, `Qq.*`, `ProofWidgets.*`, `Plausible.*`, `ImportGraph.*`,
`LeanSearchClient.*`; "Mathlib in submissions" below), nothing else (no
`Examples.*`, no `LeanModels.Python.*`, no other submission). It is one
file in v0. `tasks/_example/reference/band.lean` is a complete example: a
for-all-`N` proof that walks the design's instantiation symbolically, proves
the comb profile and acyclicity, and reduces the rest to one settled-state
lemma.

`LeanModels.Sv.*` includes lean-surfaces' `sv_comb` tactic library
(`sv_structure`, `sv_equations`, `sv_cover`, `sv_bridge` and the plain-Lean library
`LeanModels.Sv.CombLib`: `CombView`, `CombViewThm`, `CombViewSound`,
`CombViewMain`, `CombViewDiag`, `CombViewTactic`, `CombViewArith`, `CombViewPlain`,
`CombKnownBits`, `CombKnownThm`, `CombEqBase`, `CombEqShape`, `CombEqThm`, `CombEqPlain`,
`CombEqTactic`, `CombBridge`, `CombCover`, `CombLib`; their import closure is 46 modules, all in
`LeanModels.Sv` apart from `Lean`). For a design in the tactics' fragment
the proof of a task is a page, not a thousand lines:
**[PROVING.md](PROVING.md)** is the guide (the shape of a proof, a worked
example on the adder, the multiplier, what the tactics accept and refuse, when
to fall back to a by-hand proof). `tasks/add/reference/add_n.lean` and
`tasks/mul/reference/mul_n.lean` are complete tactic proofs;
`add_n_byhand.lean` and `mul_n_byhand.lean` prove the same statements with no
tactic ("Proof effort" below). The tactics' elaborators are `unsafe` Lean code
that runs while your file compiles (like any tactic); nothing in a final
theorem depends on it: the comparator walks the proof's dependencies through
the kernel and the `leanchecker` replay re-checks every declaration, and both
accept the references.

To develop a proof, run the checker once with `--keep` (or `--stage-dir
DIR`): the result's `dev_hint` is the command that recompiles your
`Solution.lean` against the staged design, and an editor can work on that
staged file. Before you have a proof, `--unproved --stage-dir DIR` stages the
design and lets you compile probe files (`sv_structure?`, `sv_equations?`)
against it with `LEAN_PATH=DIR/build lake env lean Probe.lean`
([PROVING.md](PROVING.md), section 0).

Before writing a proof, `python3.12 check.py tasks/<name> DESIGN.sv
--unproved` runs every stage that needs no proof (source, extract, banlist,
fourstate, design, score, postsynth) and stops at the pseudo-stage `unproved`, with the
score: is the design admissible, and what does it score? It never accepts.
`python3.12 check/postsynth.py --task tasks/<name> DESIGN.sv [--point N=32]
[--keep DIR]` runs the post-synthesis check alone, at any point, and keeps
the netlist, the vectors and every simulator's output.

### Mathlib in submissions

Mathlib is allowed (decided 2026-10-31: it is often critical for the arithmetic of
a circuit proof). A `Solution.lean` may import `Mathlib.*` and the packages Mathlib's
import closure reaches: `Batteries`, `Aesop`, `Qq`, `ProofWidgets`, `Plausible`,
`ImportGraph`, `LeanSearchClient` (`PACKAGE_ROOTS` in `check.py`; the lake manifest also
pins `Cli`, which only Mathlib's own executable uses, and `Lake` is a toolchain module:
neither is admitted). Lookalikes (`Mathlib2.Tactic`), `Examples.*`, `LeanModels.Python.*` and
other submissions stay refused. `tests/imports/test_allowlist.py` recomputes the import
closure of `Mathlib` from the package sources (8,643 package modules, 213 toolchain
modules) and fails if it reaches a module root that is not on the list.

**Nothing is built for it in svGolf.** Mathlib is one of svGolf's packages (`.lake/packages/mathlib`, at the
revision lean-surfaces pins; `lake exe cache get` fetches its build), so
`lake env` already puts the Mathlib build on `LEAN_PATH`; the checker builds no Mathlib and
needs the packages' `.olean` files to exist on the machine. Until 2026-11-01 this machine lacked 110
`Batteries` modules (36 `Mathlib` modules need them, the `Mathlib` umbrella among them), so a whole-library
`import Mathlib` or `import Batteries` failed to load and the checker answered with an infrastructure error
(exit 2), not a rejection: the sources are in the checkout, the verdict must not depend on which machine ran
it. `lake build Batteries` from the repository root (190 jobs) fixed that. MEASURED afterwards (2026-11-01,
`import Mathlib` plus `example : (2:ℕ) + 2 = 4 := by norm_num`, standalone `lake env lean`): exit 0, 110 s wall on
the first (cold-cache) run with 3.5 s CPU, peak resident memory 3.8 GB (the mmap of the oleans), inside the
sandbox's default limit (60% of the RAM up to 12 GB). A warm run was not timed; budget the memory when many
submissions import the whole library (decided 2026-11-01: "let's make the common libraries available").

**What it does to the trust story** (`P-TRUSTED-BASE`). Allowing Mathlib makes the `.olean`
files of eight package checkouts something the comparator and `leanchecker` LOAD and, before
this round, trusted: no stage re-checked a package's declarations, and a solution's own build
ran arbitrary code with the checker's privileges (the sandbox of WP-S, "Sandbox" below, now denies
that write; the replay below stays as the layer behind it), so it could write one. The review of WP-B found two
runs that accepted a false statement this way (a package-free solution plants
`Mathlib/Evil.olean`, a module with `theorem evil : False` added with the kernel check
switched off, so no axiom anywhere in its value; the next run imports it and "proves" the goal
for the wrong design), and a second route through `Cli`'s unbuilt build directory, which `lake
env` puts ahead of Mathlib's. The layers now are:

* **The comparator replays the closure it uses.** Every constant that the solution and the goal
  reach, through types and values, minus what the toolchain provides (`Init`, `Std`, `Lean`) and
  minus the submission's own modules (`leanchecker`'s), is sent through the kernel on a fresh
  `Init`/`Std`/`Lean` environment (`Lean.Environment.replay`). Measured: the Mathlib fixture
  (`tests/imports/mathlib_band.lean`) reaches 7,938 constants and replays 3,213 of them in
  2.6 s; the plain `_example` reference reaches 6,887 and replays 2,215 in 2.4 s. The planted
  `False` fails with the kernel's own error (`declaration type mismatch, 'Mathlib.Evil.evil'
  has type True but it is expected to have type False`), in the real flow on a copy of the
  packages and in `tests/checker/test_comparator.py` on a hand-built chain. Replaying is also what
  makes a rejected run's leftovers harmless: the tripwire below detects a write, it does not undo it.
* **The toolchain is the toolchain.** Every loaded `Init`/`Std`/`Lean`/`Lake` module must resolve
  into the installation's own `lib/lean` (Lean resolves a module root to the FIRST search-path
  entry that has a directory of that name, so a package build directory ahead of the toolchain
  could stand in for it, and the replay takes the toolchain as given).
* **The integrity tripwire watches the Lean search path for every solution**, imports or not
  (a package-free solution can plant what a later Mathlib importer loads): the `.olean`,
  `.olean.server` and `.olean.private` files of the package builds on `lake env printenv
  LEAN_PATH` (about 33,000 files, 0.3 s per snapshot (0.5 s for the whole integrity snapshot)), the top-level names of every entry (a new module
  root shadows a package) and entries that do not exist, recorded as absent (`Cli`'s build
  directory is one on this machine: creating it is a difference), and the
  `lake-manifest.json` that pins Mathlib's revision. A rejected run leaves what it wrote on
  disk, so the next snapshot starts from the planted state: that is the replay's job.
* **The header is read the way Lean reads it.** A comment is whitespace (`import A/-c-/import B` is
  two imports; the checker used to splice them into one token and never saw the second, so a
  hidden `import Mathlib.Tactic.Ring` skipped the probe and the package checks, a hidden
  `import LeanModels.Python.*` the allowlist), and after the comparator the imports Lean itself
  recorded in the compiled `Submission.Solution` are compared with the allowlist and with what
  the checker read (`import_mismatch`): a difference is rejected at `imports`.
* **The comparator's axiom walk** goes through the solution's dependency closure by kernel
  values, Mathlib's declarations included, so a `native_decide` hidden behind a lemma that
  the proof uses is rejected at `comparator` (the generated axiom `native_helper._native.native_decide.ax_1_1`
  is outside the allowed set), exactly like one in the file (`tests/run.py`: `mathlib_native_decide`,
  `mathlib_decide_native`). Mathlib's own tactics leave only the three allowed axioms (`ring`:
  `propext`; `norm_num`: `propext`; `linarith`, `positivity`, `nlinarith`, `grind`, `aesop`, `omega`,
  `fin_cases`: subsets of the three; `decide`, `decide +kernel`: none; checked with `#print axioms`
  on sixteen small theorems). A scan of the whole loadable closure of `Mathlib` (10,029 modules,
  740,344 constants, imported as the comparator imports them; 9 minutes) finds 15 axioms, all declared
  by core: the three allowed, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` and eight
  compiler-internal ones (`lcProof`, `lcAny`, `lcCast`, `lcErased`, `lcUnreachable`, `lcVoid`,
  `Quot.lcInv`, `isScalarObj`); no module of Mathlib, Batteries, Aesop, Qq, ProofWidgets, Plausible,
  ImportGraph or LeanSearchClient declares one. DIRECT users of the non-allowed ones: `Lean.trustCompiler`
  has two, core's `Lean.reduceBool` and `Lean.reduceNat`; `lcProof` has 27 (core's unsafe array
  folds, Aesop's `UnionFind.findRepUnsafe`, the auxiliary proofs of Mathlib's `Part.unwrap` and
  `FP.nextUpPos`, ...); every other one has none. TRANSITIVELY (one pass in import order, 2.4 minutes): `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, `sorryAx` and the other seven compiler axioms but `lcProof` have no dependent
  at all; `Lean.trustCompiler` has four, all in `Init`; `lcProof`, which proves any proposition, has
  217, all of them compiled or `unsafe` code and its auxiliary proofs (117 in `Lean`, 48 in `Init`, 41
  in Mathlib, among them `Repr` and `ToExpr` instances, the `FP` floating-point code and `memoFixImpl`,
  six in Aesop, three in ProofWidgets, two in Batteries). A proof that mentions one of them is rejected by
  the same axiom walk, and none of the tactics above reaches them (their `#print axioms` are listed
  above). `bv_decide`'s generated axiom (`<decl>._native.bv_decide.ax_*`) is rejected the same way, by a message that names
  the policy ("`bv_decide` is not supported", "`bv_decide`" below).
* `leanchecker` replays the NEW declarations of `Submission.Design` and `Submission.Solution`
  (unchanged); the packages' declarations are replayed by the comparator, as above.
* **The revision is recorded.** For a solution that imports a package, `stages.packages.revisions`
  has, per admitted package, the revision `lake-manifest.json` pins and the HEAD of the
  checkout; a checkout at another revision (other simp sets, other lemma names under the same Lean
  version, so the same file could be accepted on one machine and rejected on another) is an
  infrastructure error.
* Mathlib adds no host capability that `import Lean` did not already give; every one of them,
  `#eval`, `run_cmd`, `elab`, `initialize`, runs inside the sandbox ("Sandbox" below).

**What it costs.** Importing alone (a file that is only `import X`, `lean file.lean`; three
runs, the first after an idle gap), measured on the shared development machine (Apple M2 Pro,
loaded: other jobs ran throughout; `LEAN_NUM_THREADS=2`), 2026-10-31:

| import | modules | exported `.olean` MB | seconds (runs 1, 2, 3) | peak RSS |
|---|--:|--:|---|--:|
| `Init` | | | 0.33, 0.31, 0.28 | 0.4 GB |
| `Lean` (allowed already) | 2,322 | 335 | 5.4, 1.8, 1.1 | 1.3 GB |
| `Mathlib.Tactic.Ring` | 2,173 | 415 | 4.2, 1.5, 1.4 | 1.35 GB |
| `Mathlib.Tactic.Linarith` | 2,262 | 436 | 1.7, 1.4, 1.5 | 1.4 GB |
| `Mathlib.Tactic` | 4,513 | 1,023 | 11.3, 2.3, 2.2 | 2.9 GB |
| `Mathlib` (the whole library) | | | UNMEASURED: it does not load on this machine (no `Batteries` umbrella build); 4,513 modules and 2.7 GB for `Mathlib.Tactic` suggest several times that, an extrapolation, not a measurement | |

Through `check.py` itself (`--no-score --no-trusted-build`; the stage seconds of its JSON,
`stages.packages` for the probe), on the checker of this round (the replay of the used closure
in the comparator, the search-path tripwire), 2026-10-31 late afternoon on a BUSY machine (load
average 8 to 10, swap in use, so the wall clock of every row is inflated: the same `add_n` took
6.2 s in `solution` when the machine was quiet, 21.3 s here):

| design, Mathlib imports | probe | `solution` | `comparator` | `leanchecker` | replay: constants reached / replayed, seconds |
|---|--:|--:|--:|--:|--:|
| `add_n` reference, none | | 21.3 | 34.0 | 22.3 | 8,815 / 3,694, 4.8 |
| `add_n`, `Mathlib.Tactic.Ring` | 5.3 | 26.6 | 32.5 | 25.7 | 9,556 / 4,374, 5.0 |
| `add_n`, `Mathlib.Tactic` (with `sv_core_simp`, before gate M) | 57.2 | 95.2 | 65.2 | 72.0 | 9,579 / 4,404, 5.9 |
| `sbox_bp` (the slowest reference), none | | 101.6 | 33.4 | 52.2 | 8,834 / 3,736, 4.4 |
| `sbox_bp`, `Mathlib.Tactic` (with `sv_core_simp`, before gate M) | 12.0 | 60.7 | 47.2 | 66.7 | 8,875 / 3,761, 4.3 |
| `tests/imports/mathlib_band.lean`, four narrow imports (`Ring`, `Linarith`, `Positivity`, `NormNum`) | 4.3 | 2.9 | 14.9 | 18.1 | 7,938 / 3,213, 2.6 |
| the same proof, `Mathlib.Tactic` instead | 10.1 | 9.9 | 30.2 | 27.1 | 8,268 / 3,523, 2.8 |

For the shape, the previous measurement (quiet machine, the checker before this round) gave
`solution`, `comparator` and `leanchecker` of the `add_n` reference as 6.2, 9.4 and 18.2 s, with
`Mathlib.Tactic.Ring` 7.5, 14.4 and 19.3, with `Mathlib.Tactic` and the one-line fix 23.4, 61.2 and
25.6; `sbox_bp` 51.9, 18.6 and 46.8 with no import and 56.1, 54.0 and 61.6 with `Mathlib.Tactic`;
`mathlib_band` 3.3, 14.7 and 19.0 with the four narrow imports and 47.8 to 64.1 s in the comparator
with `Mathlib.Tactic`. Two things changed for the comparator. It no longer visits every imported
constant (its `extern`/`implemented_by` check reads the constants of the submission's modules only,
where it walked all 430,004 of `Mathlib.Tactic`: the `mathlib_band` comparator with `Mathlib.Tactic`
is 30 s above on a busy machine, against 48 to 64 s on a quiet one), and it replays the used
closure, which costs 2.5 to 6 s (about 3,200 to 4,400 constants; the busy machine's figure is the
larger) and holds a second, `Init`/`Std`/`Lean`-only environment in memory. `leanchecker` and
`solution` are as before. Memory was not re-measured: the busy machine swapped, which makes
resident sets read low (1.0 to 3.7 GB here against 2.0 to 4.6 GB on the quiet one); budget 3 to
5 GB for `Mathlib.Tactic` and 0.6 to 1.2 GB more than no import for a narrow one.

A narrow import is within the noise of no import in the slowest reference's `solution`,
`comparator` and `leanchecker`, and costs 3 to 5 s in the probe; `Mathlib.Tactic` costs 2 to
3 times the narrow import in the probe, in `solution` and in the comparator.

**The time limit.** `time_limit_s` bounds the compile of `Solution.lean`, and the `import`
is part of that compile: a Mathlib import comes out of the player's budget (a second or two
warm for the narrow imports, up to ten seconds for `Mathlib.Tactic` the first time the files
are read, and that cold cost comes back whenever the OS has dropped the files, for instance
on a shared host). The limit does not move for a Mathlib import, so a Mathlib submission gets no
extra margin. The limit is WALL CLOCK, which a Mathlib import makes more sensitive to the
host's load than a core-Lean file: measured by the review round, the `add_n` proof with
`Mathlib.Tactic` took 8.9 s on a quiet machine and 82 to 94 s (23.7 s of CPU) while other jobs
had the machine swapping, against 10.6 and 13.2 s for the unchanged reference at the same
time, with a 120 s limit. So: do not run Mathlib submissions concurrently with other jobs or
under memory pressure (a graded run holds the Lean slot alone), and budget the memory below.
The comparator and `leanchecker` keep their `verify_time_limit_s`.

**A module or package missing from the machine is an infrastructure error, not a rejection.**
For a solution that imports a package, the `trusted` stage ends with a probe
(`stages.packages`): the generated `Submission.ImportProbe`, the package imports and nothing
else, compiled alone, before the design and the player's file. If it fails, the failure is
the machine's, not the player's code (a player's own output could forge any message the
`solution` stage prints), unless the player named a module that no package has a SOURCE for:

| the probe | verdict |
|---|---|
| a module the player named, whose source file no package has (a stale name such as `Mathlib.Data.Nat.Defs`, which this Mathlib no longer has) | rejected at `imports`, naming it |
| a module the packages have the source of but this machine did not build (`Batteries`, the umbrella, or one of the 110 unbuilt `Batteries` modules, named directly) | infrastructure error: the verdict must not depend on the machine |
| a module only a transitive import needs (`import Mathlib` without the whole `Batteries` build), a package on no entry of the search path, `unknown module prefix` | infrastructure error |
| a checkout not at the revision `lake-manifest.json` pins | infrastructure error (before the probe) |
| any other failure, including Lean dying without output (a truncated `.olean`) | infrastructure error; the message carries the exit status or signal and the package build directories on the search path |

Infrastructure errors exit with status 2 (`stage: infrastructure`), like a missing
`LeanModels.Sv` olean.

**Mathlib's simp set and the sv_comb tactics.** The tactics normalize their obligations with `simp only [...]`
and then a `simp`; a plain `simp` sees every `@[simp]` lemma that is imported, and `import Mathlib.Tactic` adds some
37,000 of them (58,112 lemmas in the set against 20,570 without the packages). Until 2026-11-01 six of the seven
shipped references proved with the tactics did not compile once Mathlib was imported, proofs unchanged
(`sbox_bp` was the one that did): `Nat.cast_natAbs : (n.natAbs : α) = |n|` turns the declared-range obligations into
`|↑N + -1|`, which the `omega` after them cannot read; `Order.add_one_le_iff` rewrites `x + 1 ≤ y` to `x < y` (a
form `sv_rowmajor` does not expect); `sv_cover` meets `(1 + 1).toNat`; `mul_struct` runs out of heartbeats. The
tactics are now robust against it: their own `simp` calls are `sv_simp` (`LeanModels/Sv/CombCoreSimp.lean`), `simp`
with the ambient simp set minus every `@[simp]` tag that Mathlib or one of its packages added (lemmas they declare,
core lemmas they re-tag, their `@[simp]` definitions), for that one call, so the tactics see Lean core's simp set,
which they were written against, WITHOUT the player writing anything: all seven references are accepted under
`import Mathlib.Tactic` with the proof unchanged (`tests/run.py`, `attacks`: `mathlib_tactics_*`). With no package
imported `sv_simp` is `simp` (the goals the tactics print are unchanged). The player's OWN `simp` still sees
Mathlib's lemmas, as it should; `SvGolf.CoreSimp`'s `sv_core_simp` remains available to erase the package tags for the
rest of a file or section if a proof of the player's wants core's simp set for its own `simp` calls. No declaration
and no axiom is added. [PROVING.md](PROVING.md) says what to do.

## Checking

```bash
python3.12 check.py tasks/_example tasks/_example/reference/band.sv \
    tasks/_example/reference/band.lean
```

prints a JSON result: `accepted`, the failing `stage` and `errors`, per-stage
details, `score`, and (unless `--ppa off`) `ppa`, the sky130 columns of the scored
netlist, which the board ranks (see "Scoring"; `score` holds the extra GE columns). The stages, in order:

| stage | what |
|---|---|
| `imports` | the Lean file's imports are on the allowlist (`IMPORT_ALLOW` in `check.py`: `Init`, `Std`, `Lean`, `LeanModels.Sv.*`, which includes the whole sv_comb tactic library, `SvGolf.*`, `tasks.*`, `Submission.Design`, and the eight module roots of Mathlib's package closure, `PACKAGE_ROOTS`; tested by `tests/imports/test_allowlist.py`, which recomputes that closure from the package sources) and include `Submission.Design`; comments are whitespace, so a comment between two imports on one line does not hide the second. For a solution that imports one of the packages, the `trusted` stage ends with a PROBE (`stages.packages`, with the revisions of the package checkouts): the generated `Submission.ImportProbe`, the package imports and nothing else, compiled alone. A module the player named that no package has a source for (a stale name) is rejected here; a package or module missing from the machine (not built, on no search-path entry, a checkout not at the revision the manifest pins) is an infrastructure error (exit 2), never a rejection ("Mathlib in submissions"). Checked AGAIN after the comparator against the imports Lean recorded in the compiled solution: a header the checker read differently from Lean is rejected here |
| `source` | `score/srcgate.py` (see "Rules"): no directives, attributes, pragma comments, `unique`/`priority`, x/z literal digits outside a casez/casex item wildcard, or host access (`$readmemh`, `$fopen`, `$system`, `$value$plusargs`, `$dumpfile`, DPI, ...); every later stage reads the gate's comment-free canonical text, never the submitted file |
| `extract` | the pinned lean-surfaces extractor (`extractors/sv/extract.py --top <top> --probe-points ...`, run through `check/envelope.py`, the one extraction path `load_sv` uses too) writes the envelope and the multi-point cross-check sidecar; a player's `.json` is never read. The probe points always include the scoring point (an extractor without `--probe-points` is an infrastructure error, not a skipped check). The top must have exactly the task's (non-local) parameters, by name. |
| `banlist` | `score/banlist.py`: pyslang front check (which also reads the errors of slang's analysis pass, `score/slangdriver.py`) and Yosys backstop |
| `fourstate` | `score/fourstate.py` at the scoring point (see "Rules"): no parameter or constant expression with unknown bits, no constant or run-time select that can leave its declared range, no undriven or conflicting net or logic loop (Yosys `check -assert` after `proc; flatten`), and no error of slang's analysis pass (`score/slangdriver.py`). Measured (standalone, 2026-10-29): 0.03 to 0.06 s for the `_example` and `add` designs and those of the former 16-bit divider task, 0.55 s for the `mul` reference at `N = 16`, about 1 s for the 32-bit Dadda trees |
| `trusted` | `lake build SvGolf tasks svgolf-eval` (not timed) |
| `design` | compile the generated `Submission.Design`; ls-sv's loader refusals (the Lean-vs-slang cross-checks, the one-driver rule) reject here. So does a design that LOADS but that ls-sv cannot run (WP-C3): the generated module ends with an `#eval` that tests `Design2.hasUnsupported` of `design.sem` at the scoring point and at the other points of the extractor's cross-check that are not larger than it (the larger ones cost interpreter time, 25 s at `mul_tree`'s `N = 32`, and a design loud only there has no proof of its for-all-`N` statement anyway) and, on the first loud node, rejects with its kind and text and the point (`tests/_example/attacks/func_call.sv`: a correct `a & b` written through a user function; ls-sv has no function calls). No proof, score or leaderboard work happens before it; `stages.design.unsupported_free_points` counts the points checked |
| `solution` | compile `Solution.lean`, under the task's wall-clock limit |
| `integrity` | nothing outside the solution's own `.olean` changed during that build: the whole staging tree and the trusted scripts by content (the `svgolf-eval` binary, Yosys's `simcells.v`, and `score/ppa.py` with `score/ppa_pins.json`, `score/ppa_mapped.ys` and `score/ppa_mapped_pins.json` included), the svGolf and `LeanModels.Sv` builds, the Lean SEARCH PATH (`lake env printenv LEAN_PATH`) for every solution, imports or not: the `.olean*` files of the package builds on it (Mathlib and friends: about 33,000 files, 0.3 s), every entry's top-level names, and the entries that do not exist, recorded as absent (a `Mathlib/` created in `Cli`'s unbuilt build directory, which `lake env` puts ahead of Mathlib's, would shadow it), the `lake-manifest.json` that pins the packages, the Lean toolchain, Yosys, Verilator (its scripts and binaries and its whole `VERILATOR_ROOT`, the runtime every model is compiled against), the C++ compiler, `make` and elan's settings by metadata (size, mtime, ctime, inode); checked again after the postsynth stage, and `check/sandbox/**` is in the fingerprinted trusted base. A tripwire, not a sandbox: it detects after the fact; the sandbox (below) makes the writes it watches for impossible, and the tripwire stays as the layer behind it. |
| `comparator` | `check/Comparator.lean`, which imports the compiled modules WITHOUT running their initializers: the kernel (with `leanchecker`'s limits) accepts `theorem _ : Submission.Goal := Submission.solution`, and the same with the solution's own proof term; every axiom in the solution's dependency closure (walked through kernel values, not the `#print axioms` cache) is allowed; no `extern`/`implemented_by` in `Submission.*`; every `Init`/`Std`/`Lean`/`Lake` module resolves into the toolchain; and the dependency closure of the solution and the goal, minus the toolchain and `Submission.*`, is REPLAYED through the kernel (a package olean with a declaration added without kernel checking is rejected). It reports the imports Lean recorded for each module. Under `verify_time_limit_s`. |
| `leanchecker` | `leanchecker` replays the submission's modules through the kernel (catches declarations added without kernel checking). Under `verify_time_limit_s`. |
| `score` | `score/score.py` at the task's scoring point (the two-stage canonical flow), keeping the scored gate netlist; a depth over the task's budget rejects |
| `postsynth` | `check/postsynth.py` (see "Rules" and "Post-synthesis modes" below): ls-sv (`svgolf-eval`, built in the `trusted` stage) and Verilator on the scored netlist agree on every vector of the run's set (`stages.postsynth.mode`: `light`, the default, a subset; or `full`, the task's whole `postsynth` budget); fail closed; a rejection is a bug report. The netlist model is built once per run, concurrently with ls-sv's evaluation (about 1.5 to 2 s of `verilator` + `make -j 2`, whatever the netlist), and the netlist side then costs about 0.4 microseconds per vector: the stage is ls-sv-bound. Measured standalone (2026-10-29, `check/postsynth.py`, unloaded; Icarus before, Verilator after): `_example` 0.3 s, 2.5 s; `add` (4132 vectors) 1.3 s, 2.0 s; the former 16-bit divider's goalpost (4543 vectors) 26.2 s, 19.9 s; `mul` reference (330 vectors) 46.0 s, 44.0 s. A small design pays the fixed build; a big one gains what Icarus spent per vector (about 1 ms on the former 16-bit divider). The process tree peaks at about 0.5 GB while the model compiles (`SVGOLF_VERILATOR_JOBS=1`: 0.4 GB, 1.4 s slower), 0.2 GB before |
| `ppa` | `score/ppa.py` (WP-X3, see "Scoring" and `score/PPA.md`): the EXTRA sky130 columns of the very netlist the `score` stage kept and `postsynth` verified (no second synthesis): `area_um2_sky130`, `delay_ps_sky130`, `unit_depth`, the cell histogram, and the hashes of its inputs, as the result key `ppa` and the stage `stages.ppa` (`mode`, `seconds`, and `mapped_seconds`); WP-X4 adds, inside a weighed `ppa`, the sub-object `mapped` (flow A1': a real `abc -liberty` mapping of the canonical RTLIL of the same score run, `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, cells, histogram, cell levels; `{"available": false, "reason": ...}` for a design it cannot map, never a failure of the check). `--ppa auto` (the default) weighs it when the pinned liberty is present and otherwise records `ppa: {"available": false, "reason": ...}` with one line on stderr; `--ppa require` makes an absent or wrong liberty an infrastructure error (exit status 2, before any other work): competitions, `leaderboard.py add`/`verify --full` and `tests/run.py` (where the liberty exists) use it; `--ppa off` adds no key and no stage. A design the pinned flow cannot weigh (a cell outside its table, an undriven net, an x/z bit that a gate or an output reads, ...) carries its reason in `ppa` and never fails the check; the reader understands the dead public-named wires Yosys leaves of techmapped cells, so run-time bit selects, variable shifts, `case` muxes, constant tables and `/` or `%` by a variable all weigh (`score/tests/ppa/idioms.json`). Infrastructure errors (exit status 2, no verdict) are: a liberty that `require` cannot open (absent, unreadable, not the pinned file), in `require` a defect of `ppa.py`, a depth/gate-count disagreement with the `score` stage or a repaired netlist that is not the scored circuit, and, in every mode, a netlist file that is not the one `postsynth` verified (`netlist_sha256` is compared with `stages.postsynth.netlist_sha256`). Since `sky130_a0_v2` (11/04) the stage REJECTS one kind of design: one the repair (buffering only) cannot make electrically legal (`ppa: {"available": false, "illegal": true, "reason": ..., "legality": ...}`, the net named in the rejection; none is known on sky130). Nothing in `ppa` changes `accepted`, `stage` or any other field of a design whose netlist is legal (tested character for character against the checker from before the wiring, times, paths and tool identities aside: `tests/checker/test_ppa_wiring.py`). Measured (2026-10-31): 0.11 to 0.13 s under `auto` (the liberty's 12.8 MB are hashed and scanned for cells, about 0.10 s, then a few thousand gates are timed); under `--ppa require` the liberty is opened before the first stage, so `stages.ppa.seconds` is 0.00 to 0.02 s and the 0.10 s are spent up front; since `sky130_a0_v2` the repair is Python in `ppa.py`, 0.01 to 0.6 s per netlist, 1.3 s for matmul (two weighings and a read-back; 11/04) |

**Post-synthesis modes** (WP-C2, 10/30). `check.py --postsynth light|full`, or
`SVGOLF_POSTSYNTH=light|full` (the flag wins; anything else is an error, never a
silent default), selects how much of the vector budget the `postsynth` stage runs.

| | `light` (the default of `check.py`, for local feedback) | `full` |
|---|---|---|
| vectors | a deterministic SUBSET of the full set: all-0 and all-1, then at most Q = (`light_vectors` - 2) / 4 from each of four classes, `light_vectors` = 256 unless the task says otherwise: the walking ones and zeros (evenly spaced), the task corners (evenly spaced), the harvested comparison constants (the 0 and 1 fills of each constant's assignment, then of the pairs), and the random vectors (the first of the full stream, plus everything the other classes leave unused) | the task's whole budget: the fixed vectors, the corners, every harvested constant, pair and fill, `random` seeded random vectors |
| the rest | identical: the netlist read-back, the unknown-literal scan, Verilator's lint, the x/z, schedule and port checks, the bug report with the Verilator-RTL third opinion (the RTL model is built only to illustrate a rejection, in either mode) | the same |
| who runs it | you, locally (`check.py`'s default); `tests/run.py` runs only the attacks that light also rejects in light | competitions and verification runs (set `SVGOLF_POSTSYNTH=full`), `leaderboard.py add` and `verify --full` (they pass `--postsynth full` themselves), `tests/run.py` everywhere else |
| record | `stages.postsynth.mode: "light"`, `vectors` (run), `full_vectors` (what full would run), `full_counts`, `light_vectors`, and the same seed | `mode: "full"`, `vectors == full_vectors`, exactly the fields and counts of the checker before the modes existed |

The light set is a subset of the full one with the same seed (the random vectors
are a prefix of the same stream), so **a light rejection is a full rejection**; what
light can miss is a difference only the dropped vectors reach. Measured
2026-10-30 on the attacks with the static rules bypassed (`tests/expected.json`,
`postsynth_mode`): light rejects every attack the full check rejects, the 2^-28
`z_rare.sv` included (it follows the harvested constant), except the ones the entry
marks `postsynth_mode: full`. The extra line `check.py` prints on stderr says
which mode ran. A **light check is not an official check**: a record made from one is
possible only with `leaderboard.py add --postsynth light`, and is marked `light` on the
board.

Where the full check's time goes (measured 2026-10-30, standalone `check/postsynth.py`,
one core of a loaded M2 Pro, load average about 6; `stages.postsynth.seconds`; the
stages before it, `extract` and `score`, take 0.4 to 2.3 s and 0.1 to 1.4 s):

| reference | ls-sv per vector | full: vectors, stage | of which ls-sv | light: vectors, stage |
|---|--:|--:|--:|--:|
| `_example` `band` | 0.02 ms | 4130, 3.1 s | 0.1 s | 256, 2.3 s |
| `add_n` | 0.24 ms | 4132, 2.1 s | 1.0 s | 255, 2.0 s |
| binary16 divider (former 16-bit task), first circuit (baseline) | 4.3 ms | 4543, 19.9 s | 19.4 s | 236, 2.3 s |
| binary16 divider (former 16-bit task), reference (flat netlist) | 7.3 ms | 4543, 34.1 s | 33.2 s | 236, not measured |
| binary16 divider (former 16-bit task), second reference (generate-for) | 9.5 ms | 4443, 43.4 s | 42.0 s | not measured |
| `mul_n` | 130 ms | 330, 43.6 s | 42.7 s | 40, 6.1 s |
| `mul_tree_h` | 120 ms | 330, 40.6 s | 39.8 s | 40, 5.6 s |
| `mul_wallace` | 358 ms | 330, 119.1 s | 118.1 s | 40, 15.2 s |
| `mul_tree` | 501 ms | 330, 166.7 s | 165.3 s | 40, 21.2 s |

It is ls-sv's `run2` per vector (both schedules, an interpreter), not the builds, that
dominates: 96 to 99 % of every `mul` stage. The netlist's Verilator build is 1.5 to 2.2 s,
concurrent with ls-sv (free on `mul`, the whole stage for `add`); its run 0.2 to 0.5 s; the
read-back 0.04 to 0.1 s; the constant harvest 0.02 to 0.9 s; the comparison loop and the
oracle milliseconds. The RTL (third-opinion) build, 1.6 to 3.2 s, happens only after a
rejection or under `check/postsynth.py --third-all`. So the lever is the vector count, and
the floor is the netlist build: `add` cannot go under 2 s. The stage checks only the
SCORING point (`N = 16` for `mul`), in both modes; the other probe points are checked by
the `design` stage's extractor cross-check, not simulated.

**The `ppa` stage and `--ppa {auto,off,require}`** (WP-X3, 10/31). The sky130 columns were wired in as
EXTRA, beside the GE board, and no submission that was accepted was rejected for them (superseded: decided 11/03, the
board ranks them, see "Scoring"; 11/04, a design the repair, buffering only, cannot make electrically legal is rejected
at this stage), and every other field of the result is what it was (with `--ppa off` the result is the old one
key for key and value for value; against the recorded old results only times, directories, tool identities, the
envelope hash and the comparator's constants count are not compared, and between `off` and `auto` of one
checkout only times and directories are not: `tests/checker/byte_identity.py`). The liberty (12.8 MB, `sky130_fd_sc_hd__tt_025C_1v80.lib`) is not in the
repository: fetch it once with `python3.12 score/ppa.py --fetch-liberty` (into `score/lib/`, git-ignored;
size and sha256 checked before it is moved into place), or point `$SVGOLF_SKY130_LIB` at a copy (the hash is
checked on every load). Without it `--ppa auto` still checks everything else and says so
(`ppa: {"available": false, "reason": "liberty not found: ..."}`; stderr: `ppa: not computed: ...`).
WP-X4 (11/01): a weighed `ppa` block also carries `mapped`, flow **A1'** (a real `abc -liberty` mapping of the canonical RTLIL of
the same score run: one more Yosys process, 0.3 to 1.4 s on the references, checked against the scored netlist on 2048 input
vectors, then weighed by the same STA); `--ppa` semantics are unchanged (`off` maps nothing, `require` opens the liberty and the
mapped-flow pins before any work), a design the mapping cannot weigh has `mapped: {"available": false, "reason": ...}` and the check
goes on, a mapped netlist that is not the scored circuit is an infrastructure error in `require` only (`score/PPA.md`, "Wiring").

Set `SVGOLF_LEAN_WRAP` (or `--lean-wrap`) to prefix every `lake`/`lean`
call, e.g. with a slot-limiting wrapper; the time limit counts only the proof
compilation itself, not waiting for the wrapper. `python3.12` is required
(pyslang and the extractor). The `postsynth` stage and the validation
scripts also need Verilator 5 (the measurements here are 5.042, recorded in
every postsynth result as `verilator`), a C++ compiler (`$CXX`, default
`c++`) and `make`; a missing tool is an infrastructure error, not a
rejection. `SVGOLF_VERILATOR_JOBS` (default 2) sets the parallelism of the
model's C++ build.

**Advisory output.** Three things in the result are contestant conveniences; none changes
`accepted`, `stage` or the meaning of any other field.

* `dev_hint` (with `--keep` or `--stage-dir`): the command that recompiles your `Solution.lean`
  against the staged design, and, for an `--unproved` run (no `Solution.lean` yet), the command
  that compiles ANY probe file against it: `... LEAN_PATH=<stage>/build lake env lean
  <YourFile>.lean`, where the file starts with `import Submission.Design`. Both put your Lean
  wrapper (`--lean-wrap` / `SVGOLF_LEAN_WRAP`) in front of `lake`, as the checker does.
* **Functional smoke check.** If the task has an `oracle` (see the `task.json` table), the
  `postsynth` stage compares the outputs ls-sv already computed on its vectors (the light
  mode's by default, a few hundred; all of them under `--postsynth full`), at the scoring
  point, with the oracle's: no new simulator run, about 8 ms for 4500 vectors. The result is
  `stages.postsynth.functional`, `{"checked": K, "mismatches": M, "examples": [up to 3 of
  {"point", "inputs", "expected", "got"}]}` (values as hex strings; `"unchecked"` and a `"note"`
  appear when a vector could not be compared, because ls-sv gave no known value or the oracle
  failed: that is never a mismatch). If `M > 0` the result also has a top-level array `warnings`
  with ONE line, `functional: the design disagrees with the task's function on 120 of 4132
  vectors; first: a=0x1 b=0xffff cin=0x1 expected ... got ...`, which `--unproved` prints on
  stderr too. A functionally wrong design passes every stage before the proof, `--unproved`
  included, and then fails the proof with an opaque type mismatch; this finds it first. It is
  advisory: the Lean proof is the authority, the oracle is not part of the trusted statement,
  and a task without an oracle has no `functional` key. (A full run reaches the check only when
  the proof compiles, so run `--unproved` first.) `tests/add/attacks/wrong_carry.sv` is the
  test.
* **`--tactics`** (`--unproved` only; combinational tasks). After the `design` stage, ONE extra
  Lean job compiles a generated probe, `sv_structure?` on `CombDesign (design.sem N)` (the goal
  of every tactic proof, PROVING.md section 2.1), against the staged design, and the result has
  `tactics: {"in_fragment": true|false|null, "message": ...}` and one line on stderr:
  `in_fragment: true` (message `ok`) when the sv_comb tactics can read the design,
  `false` with the first line of the tactic's own refusal (for example `sv_structure: outside
  the supported fragment — localparam `L`: `$clog2` is outside the v1 fragment ...`; PROVING.md
  section 4 lists them) when they cannot, `null` when the probe itself could not run. It costs about 2 s
  (`stages.tactics.seconds`) and answers a question the checker's own stages cannot: a design
  with a `?:`, a `$clog2` localparam or an `always_comb` outside the first fragment (PROVING.md
  section 13) is admissible and scores, but has no tactic proof. When the plain probe is refused, a
  second job asks the `always_comb` elaborator on the LOWERED goal (`∃ d', (design.sem N).lowerComb
  = some d' ∧ CombDesign d' ∧ Acyclic d'`): a design it reads reports `in_fragment: true` with
  `lowered: true`, and one with an unreadable `always_comb` body reports that elaborator's refusal
  (for example ```case` arm is not a single assignment `t = v;` (the first fragment has no `begin … end`, `if` or `case` inside an arm)``) instead of the plain one.
  It does not say the proof will go through.

### Sandbox

`check.py` runs other people's text: a `Solution.lean` is compiled and ELABORATED (`#eval`, `run_cmd`, `elab`,
`initialize`, `unsafe` code and, with Mathlib, every tactic it ships) with the checker's own privileges, and Yosys,
Verilator and the compiled model read the `.sv`. Measured 2026-10-31 on the checker as it was: a reference proof plus
an `#eval` that reads `/etc/hosts` and writes a file outside the staging tree was ACCEPTED; the same file read the
competition salt `SVGOLF_POSTSYNTH_SALT` out of the checker's environment (with which a player precomputes the
post-synthesis vectors), opened a TCP connection (Lean 4.33 core has sockets: `Std.Internal.UV.TCP`, no program is
spawned), replaced the trusted `Design.olean` through a hard link, and spawned `/bin/sh`. A scan of the Lean file cannot
stop that: the shipped references use a local `elab` and macros, Lean metaprograms reach IO under many names, and
`unsafe` code makes the interpreter itself untrusted. So the processes are CONTAINED, by the operating system:

```bash
python3.12 check.py TASK SOLUTION.sv SOLUTION.lean --sandbox require    # off | auto (default) | require
```

| `--sandbox` | |
|---|---|
| `auto` (default, `$SVGOLF_SANDBOX`) | use the sandbox when the mechanism exists AND passes the self-test; say on stderr when it does not (`sandbox: NOT ACTIVE (...)`) and run without |
| `require` | an infrastructure error (exit status 2, never a verdict) when it is not there. `leaderboard.py add` and `verify --full` use it, and so does every competition run |
| `off` | no sandbox. The environment is scrubbed in every mode |

**What runs inside.** The Lean compiles (the generated `Submission.Design`, the import probe, `Solution.lean`),
the comparator and `leanchecker`, the pinned extractor, Yosys (score, banlist, fourstate, the netlist re-read, the
constant harvest), Verilator and its C++ build, the compiled model, `svgolf-eval`. Each gets a `Spec` (`check/sandbox/spec.py`)
and nothing else: **no network of any kind** (TCP, UDP, unix sockets, DNS); **reads** of its program, the toolchain, the Lean search
path and its own inputs only (no `~/.ssh`, no `/etc`, no other competitor's staging directory); **writes** of one fresh
directory outside the staging tree (the compile's `.olean`: the checker copies `Solution.olean` out, a regular file of that
exact name, and notes anything else under `stages.sandbox.stray_outputs`); **no other program** (`/bin/sh`, `curl`, `kill`) and no
signal to another process, and no `fork` at all; an **environment that is an allowlist** (`check/sandbox/envscrub.py`), so neither the salt nor a
token is in it; and the **supervisor's limits** (`check/sandbox/supervisor.py`), enforced from outside: the wall-clock
limit, resident memory summed over the process group and POLLED (macOS cannot enforce an address-space limit, and one would
break the mmap of Mathlib's oleans anyway; default 60% of the RAM up to 12 GB, `SVGOLF_SANDBOX_RSS_MB`), a cap on the output
the checker will ever buffer (16 MB of Lean, 64 MB of a tool; `capture_output` used to let a flood to `/dev/fd/1` exhaust the
CHECKER), `RLIMIT_FSIZE` (2 GB, 4 GB) and `RLIMIT_CPU`. `lake` itself is never inside (it runs `git` in every package
checkout and would clone a missing one): `lake env` is asked once, outside, and the toolchain's `lean` then runs directly,
which is also faster (no `lake` start-up, about 1 s per call). The slot wrapper (`--lean-wrap`) stays OUTERMOST:
slot, supervisor, sandbox, program (the slot's `LEAN_NUM_THREADS` is forwarded).

**Mechanisms.**

| OS | mechanism | status |
|---|---|---|
| macOS | Seatbelt, `sandbox-exec -f PROFILE` (deprecated by Apple, unchanged for a decade; Chrome, Bazel and Nix use the same kernel interface). The profile is generated from the Spec: `(deny default)`, `system.sb` for dyld, `process-exec` of the listed programs, `file-read*` and `file-write*` of the listed trees, `(deny network*)`, `(allow signal (target self))`, `(deny file-link)`, and a GLOBAL `file-read-metadata` | measured: the whole checker, the references and the attacks below |
| Linux | bubblewrap (`bwrap`): `--unshare-all --disable-userns --cap-drop ALL --clearenv`, a private `/tmp`, read-only mounts of exactly the Spec's trees (what is not mounted does not exist, and a Lean file finds no `/bin/sh`), `--bind` of the output directory | the self-test and the process-level tests (`tests/sandbox/test_sandbox.py`: tool specs, exec limits, secrets unreadable, writes confined, merged-`/usr` links) ran on Rocky Linux 9.8 with bwrap 0.6.3. **Lean was not run there**: the first Linux checker runs `tests/run.py --sandbox require` |

Needs unprivileged user namespaces on Linux (Debian `kernel.unprivileged_userns_clone=1`; Ubuntu 24.04's AppArmor restriction
needs a profile for `bwrap`). Seatbelt cannot nest (`sandbox_apply: Operation not permitted`): a checker already inside
another Seatbelt sandbox falls back (`auto`) or stops (`require`).

**The self-test.** A sandbox that is not there is worse than none, so every `auto` and `require` start (0.3 s) runs a canary
in the same machinery: a Python program that reads a file inside its Spec (must work), writes the output directory (must
work), reads a file the TEST created outside it, lists a directory outside it, writes outside it (the file must not reach the
host), connects to a loopback listener the test runs, starts `/bin/sh`, and looks for an `SVGOLF_` variable. Everything it
touches the test made itself. A mechanism that fails any of it (a nested sandbox, user namespaces off, a profile Apple changed)
is "not available".

**Cost and equivalence.** Measured 2026-10-31 on an Apple M2 Pro that other jobs were loading (single stages varied by a
factor of 2 to 6 from run to run, in both directions): `add_n`, `sbox_bp` and `mul_n` through `check.py --postsynth full` with
`--sandbox off` and `--sandbox require` give the same result character for character apart from the two sandbox keys and
one wall-clock leaf, and the stage times overlap (`solution` 30.2 s off against 5.6 s on for `add_n`, 118 s against 176 s for
`sbox_bp`, 31 s against 37 s for `mul_n`; `leanchecker` 21 s / 17 s, 184 s / 118 s, 24 s / 25 s). The mechanism itself is cheap:
12 ms per `sandbox-exec`, 0.4 s for the self-test, and a direct `lean` saves the 1.05 s that every `lake env` costs (seven of
them per check). `Design.olean` and `Solution.olean` built in the sandbox are bit-identical to the unsandboxed ones (same stage
path). Global `file-read-metadata` is deliberate: `leanchecker` stats every module of the search path (10 s of system time),
and a path-filtered rule made it 60% slower (13.7 s to 22 s); with the global rule it is within noise. All references pass
under `--sandbox require` (`tests/run.py --sandbox require`: `add`'s four, `aes_sbox`, `mul`'s five, the former 16-bit divider's draft: 73
checks), and so do the whole `attacks` step (153 checks) and `sandbox` step.

**The result.** `sandbox` (`mode`, `mechanism`, `active`, and `reason` when `auto` fell back) and `stages.sandbox` (the self-test,
the number of processes run inside per kind, each profile's digest, the largest resident set seen, what ran OUTSIDE: only
`lake build` of the trusted modules). `--sandbox off` adds neither key.

**What the sandbox does not do** (residuals, all recorded in `docs/sv-refusals.json`):

* A hostile Lean file that CATCHES its errors is accepted, neutralized: a denied call cannot be told from a permitted one, so
  `try IO.FS.readFile "/etc/hosts" catch _ => ...` compiles whatever happens. The `host_catching` attack pins that (every
  action blocked, `integrity` clean, the proof still has to be a proof).
* The submission can learn that a path EXISTS and its size and times (global `file-read-metadata`), not its content or a listing.
* A crafted `.olean` is still loaded by the comparator and `leanchecker`; they run inside the sandbox too (measured: they do not run
  the solution's `initialize`), and the kernel replay is the check.
* The parsers that run IN the checker's own process (pyslang in the source gate, the banlist and fourstate front checks) are not
  sandboxed; the sandbox covers every subprocess. Moving them into one sandboxed worker is the recorded next step.
* Whatever `system.sb` grants every Apple command-line program (a few system services, `sysctl` reads, public system files);
  kernel and Seatbelt bugs; timing side channels; CPU and memory up to the limits above.
* On Linux a Lean file can run the other binaries of the toolchain it can read (`lake`, `clang`): no `/bin/sh`, no network, no
  writable path, so nothing leaves.

**Tests.** `tests/sandbox/test_env.py` (the environment allowlist, and an AST lint: every `subprocess` call in the checker, scorer
and postsynth modules passes `env=`), `test_sandbox.py` (profile and `bwrap` argument generation including awkward paths, the
supervisor's limits, a self-test that must FAIL on a mechanism that does not sandbox, `configure`, the Lean plumbing, the real
mechanism), `test_tools.py` (Yosys `$readmemh` loads a host file into the netlist; a Verilator model runs `$system`; both
unsandboxed, both blocked sandboxed), and `tests/run.py`'s `sandbox` step: `host_naive` (the finding: ACCEPTED with `--sandbox off`
and the file exists; REJECTED at `solution` with the sandbox, "operation not permitted"), `host_catching`, `host_memory_bomb`,
`host_output_flood`, `host_cpu_bomb`, `host_cadical` and `host_spawn_bomb` (a file that runs the toolchain's `cadical` by hand, or
starts copies of `lean`: by default nothing can start, every try is blocked; the GROUNDWORK rows force the dormant `bv_decide` support
on through `tests/checker/check_bv_enabled.py` and show what the grant would be, "`bv_decide`" below), and the integrity-tripwire attacks `mathlib_plant_*` with the sandbox ON (the write is denied
before it can happen; their tripwire versions in the `attacks` step run `--sandbox off`). The `host_env_salt` attack (the
secrets are invisible) is in the `attacks` step. The step skips, with a message, on a machine without a mechanism.

### `bv_decide`

**Not supported for now.** `bv_decide` bit-blasts a goal about fixed-width `BitVec`s, asks an EXTERNAL SAT solver (the
toolchain's `cadical`) for an UNSAT proof in the LRAT format, and closes the goal from it. The checker does not support it
(decided 2026-11-01: "maybe that's a bad idea. Let's not support external solvers for now"). A task's `allow_bv_decide` is
therefore `false` or absent; `true` is an infrastructure error ("the checker does not support external SAT solvers");
`check.py` never passes `--bv-decide` to the comparator; and a submission that uses the tactic is refused:

* with the sandbox on (the default where it works) the compile fails at `solution`, because the tactic cannot start its solver
  (`operation not permitted`), and the rejection carries a hint: *bv_decide runs an external SAT solver (cadical), which the
  checker does not support; prove the goal with decide +kernel, omega, simp or a symbolic argument*;
* with `--sandbox off` the proof compiles, and the comparator rejects the axiom the tactic generated
  (`<decl>._native.bv_decide.ax_*`) at `comparator`, with the message "`bv_decide` is not supported: it runs an external SAT
  solver (cadical), which the checker does not support ...". A hand-written axiom of that name is rejected the same way, and
  so is any other axiom of your own, `native_decide`'s and `Lean.ofReduceBool`.

For a fixed-width fact use `decide +kernel` (no extra axiom, but the kernel enumerates), `omega` for linear facts, `simp`, or the
symbolic proof the rules ask for anyway (PROVING.md).

**Why.** The tactic writes a CNF and an LRAT file into the temporary directory and starts `cadical` as a child of `lean`. None of
that is possible inside the compile's sandbox Spec, and WP-BV measured the minimum that would make it work: the toolchain's
`bin/cadical` among the programs the compile may execute, `fork`, and one more fresh writable directory (`TMPDIR`). Without a
writable `TMPDIR` the tactic fails with `operation not permitted`, then without `fork` the same, then without the `cadical`
exec with "could not execute external process". The grant is a real widening: with `fork` a hostile file can also start further
copies of `lean` (the only other program it may execute) in the compile's process group, bounded by the supervisor's summed
resident-memory and wall-clock limits, not by a process count (the groundwork row `host_spawn_bomb` shows the memory limit
stopping such a bomb in 20 s). The maintainers declined it.

**What exists, dormant.** The work is kept so that enabling is a small change (design note `design/bv-decide/NOTE.md`, with the
alternatives and the measurements):

* **The comparator's re-verification** (`check/Comparator.lean`, point 6, `--bv-decide`). A `bv_decide` proof ends in an axiom
  `<decl>._native.bv_decide.ax_<i>_<j> : verifyBVExpr E C = true`, added after the tactic ran the compiled LRAT checker on `E` (the
  bit-blasted goal, a closed `BVLogicalExpr` constructor term) and `C` (the certificate, a string literal). Name and shape prove
  nothing: an axiom of exactly that shape over a false certificate proves `False`. With the flag, the comparator evaluates the
  statement itself: it requires the name `_native.bv_decide.ax_*` and the exact type with `E`, `C` safe closed definitions; decodes
  `E` from its kernel value (no submission code runs); requires the toolchain's own `toExpr` of the decoded value to equal that
  value syntactically (so the decoder is not trusted and any other shape of the same value is refused); and runs the toolchain's
  compiled `verifyBVExpr` (LRAT checker, bit-blaster, CNF conversion, proved sound against the definition by
  `unsat_of_verifyBVExpr_eq_true`) in its own process, accepting the axiom iff the result is `true`, which makes it a true theorem.
  `--bv-max-nodes` and `--bv-max-depth` bound a hostile term. Trusted: the compiled checker as the tactic itself trusts it, and
  the toolchain's `ToExpr` instances of the reflection types; not trusted: CaDiCaL, the decoder, the axiom's name. Measured: a
  38 KB certificate verifies in 1 ms, 5.3 MB in 0.21 s, 504 MB in 22 s.
* **The sandbox grant** (`Lean._run_sandboxed(bv_solver=True)`), honoured only while `BV_DECIDE_SUPPORTED` is True, with its Spec
  tests (`tests/sandbox/test_sandbox.py`, which force the constant inside the test and also pin that, while it is False, even a
  caller that asks gets no `cadical`, no `fork`, no `TMPDIR`).
* **The tests**: `tests/checker/test_bv_decide.py` (real Lean, 10 tests: the comparator with `--bv-decide` accepts real proofs and
  rejects forged and malformed axioms, hostile terms, `ofReduceBool`, `native_decide`; and without the flag rejects every
  `bv_decide` axiom, naming the policy), `BvDecideFlag` in `tests/checker/test_import_packages.py` (the constant, the task key,
  the hint), and the `bv_decide_groundwork_*`, `host_cadical` and `host_spawn_bomb` rows of `tests/run.py`, which run `check.py`
  through `tests/checker/check_bv_enabled.py`, a wrapper that sets the constant in its own process.

**What enabling would take.** (1) the maintainers accept the sandbox widening above (and, for Linux, that the bubblewrap path, unit-tested
only, is run with a real Lean). (2) Flip `BV_DECIDE_SUPPORTED` in `check.py` to `True`: absent then means allowed, `true` is
accepted, the compile gets the solver, the comparator gets `--bv-decide`, and the hint is not added. (3) Flip the `false` of the
tasks that should allow it, and move the `bv_decide_subgoal_*` attack rows back to an ACCEPTED row (the groundwork rows show their
shape). (4) Run the checklist: `test_bv_decide.py`, `test_import_packages.py`, `test_sandbox.py`, `tests/run.py --attack bv_decide`
and the `host_cadical` / `host_spawn_bomb` sandbox rows with the wrapper's constant now the shipped one, `gen_sv_refusals.py
--check`. (5) Rewrite this section, the register policy row and `sg-bv-decide`. Nothing outside `check.py` can switch it on: no
environment variable, option or task key reads the constant (a test pins that).

### Checker v0 limits

* **The sandbox needs a mechanism, and has residuals.** With `--sandbox auto` (the default) on a machine
  without one (no `sandbox-exec`, no `bwrap`, user namespaces off, or already inside another Seatbelt
  sandbox) the solution's Lean runs with the checker's privileges, and the check says so on stderr and
  in `sandbox.reason`; official runs use `--sandbox require`. Residuals, in "Sandbox" above: a hostile
  file that catches its errors is accepted but neutralized; the parsers that run in the checker's own
  process (pyslang) are not sandboxed; the existence, size and times of any path are visible;
  kernel and Seatbelt bugs. Measured before the sandbox (2026-10-31): the reference `Solution.lean` of
  `_example` with an added `#eval IO.FS.readFile "/etc/hosts"` and an `IO.FS.writeFile` was ACCEPTED,
  read the file, wrote the other one, and whatever the `#eval` printed came back in
  `stages.solution.messages`; `tests/run.py`'s `host_naive` keeps that as its control (`--sandbox off`).
* **One file, one design.** Multi-file proofs and multi-file designs are not
  supported yet. Hierarchical designs (several modules in one file) are, as
  far as ls-sv's loader is.
* **Integrity is a tripwire.** It sees changed, new and deleted files in
  the places it watches, after the solution build and again at the end, and
  the solution's process group is killed when its compile returns. A process
  that escapes the group, or tampers and restores in between, is beyond it.
  It detects, it does not undo: what a rejected solution wrote stays on disk
  (a stray `.olean` in a package's build directory, say), and the next run's
  snapshot starts from that state. For the package oleans this is why the
  comparator replays the closure it uses instead of trusting the files.
  A concurrent build of lean-surfaces' `LeanModels.Sv` oleans during a check
  trips it (the check rejects; rerun it).
* **Frontends.** ls-sv reads the design through slang (pyslang 11); Yosys
  through its own `read_verilog -sv`. The source gate makes them read the
  same text with no tool-specific annotation; a design one accepts and the
  other does not is rejected at the corresponding stage. Two tools that give
  the same text DIFFERENT meanings are refused statically where the
  difference is known and its source can be named exactly (the
  `unique`/`unique0`/`priority` qualifiers and x/z literal digits in the
  gate, every other source of an x in the `fourstate` stage), and caught by
  the `postsynth` stage where its vectors reach it otherwise (an unknown
  Yosys or ls-sv bug). "The tools split" means the PIPELINE tools (slang and
  ls-sv, Yosys, Verilator, Xcelium): a difference that only Icarus shows is a
  declared departure, and a program slang rejects is a program to reject
  (decided 2026-10-31). Nondeterminism the LRM itself leaves open is to be
  modelled, the golfer proving the output the same in every legal run; no
  construct is admitted on that ruling yet, and self-reading `always_comb` is
  not such a construct (the LRM's answer is deterministic, the synthesizers
  compute another)
  ([design/nondeterminism/NOTE.md](design/nondeterminism/NOTE.md), the audit
  `docs/sv-tools-split-audit.md`). The `unique`/`unique0`/`priority` refusal is decided
  in the gate because Yosys's reading is a documented don't-care (remove
  their entries from `SYNTH_QUALIFIERS` in `score/srcgate.py` to admit
  them). With the gate's refusal bypassed, the postsynth check alone
  rejects a `unique case` that never matches (every vector) and one whose
  items overlap (a quarter of the vectors, or, when the overlap hides behind
  constant comparisons, the harvested vectors), and passes the benign ones
  (`tests/_example/attacks/`, `postsynth_alone` in `tests/expected.json`).
* **The post-synthesis check samples, and its default mode samples less.** It
  compares ls-sv and the scored netlist on the task's vector budget (`full`
  mode) or on a deterministic subset of it (`light`, the default of
  `check.py`: local feedback; a competition, `leaderboard.py add`/`verify`
  and `tests/run.py` run `full`), not on every input. What only `full`
  catches is a difference confined to a region the dropped vectors reach:
  `tests/_example/attacks/rare_mid.sv` (the out-of-range read on 2^-9 of the
  inputs, no comparison constant) is rejected by 7 of the 4130 full vectors
  and passed by the 256 light ones, and is the one attack in the suite that
  separates the modes (every other attack the full check rejects, light
  rejects too, `z_rare.sv` and `unique_rare.sv` through their harvested
  constants). A difference
  confined to a rare region that no constant comparison of the design
  selects (a parity or hash condition, a constant Yosys folds away before
  the harvest) can pass it. The random vectors' seed hashes the canonical
  text with `$SVGOLF_POSTSYNTH_SALT` (empty by default, so anyone can
  reproduce a run; a competition sets a secret one so a player cannot steer
  the vectors). ls-sv's `run2` is the slow side (about 130 ms per vector on
  the 1026-process array multiplier at `N = 16`, 4.4 ms on the former
  16-bit divider's goalpost, 0.25 ms on the `add` ripple; 120 to 500 ms on the four `mul`
  trees, measured 2026-10-30), so big designs get small random budgets and
  the light mode a per-task `light_vectors`. The netlist side stopped being a cost when it moved from Icarus to
  Verilator (about 0.4 microseconds per vector after a fixed build of 1.5 to
  2 s, against about 1 ms per vector for Icarus on the former 16-bit divider), but the budgets
  in `task.json` were left as they were: every extra vector costs the ls-sv
  time above, and the baselines' post-synthesis checks (Kogge-Stone at 15 s,
  the 16-bit Dadda trees at 83 to 162 s) multiply with them. A future
  evaluator for `design.sem` that is faster than `run2` is what would buy
  bigger budgets. `svgolf-eval` is compiled code (no `implemented_by`,
  `extern` or `csimp` in the `LeanModels.Sv` closure it imports); its gap to
  the kernel's `design.sem` is `toExpr` faithfulness and the compiler.
* **The parameter's declared type is not pinned.** The statement covers
  `sem N` for every `N` in range, in ls-sv's unbounded constant tier; a
  parameter declared narrower than `int` (`parameter bit [3:0] N`) would make
  Yosys's value at the scoring point differ. The multi-point cross-check
  always includes the scoring point, so the scored design is one where
  ls-sv's loader and slang agree; elsewhere the statement is about ls-sv's
  reading.
* **The banlist front check is heuristic.** Constness is judged by the
  symbols an expression reads (parameters, localparams, genvars, enum
  values, loop counters by symbol identity), and a variable merely COPIED
  from a loop counter (`automatic int j = i; ... a[j+1]`) counts as run-time:
  a false rejection, never a false acceptance at the backstop points. A loop
  counter that the loop body itself writes is run-time too (Yosys ignores
  such a write and folds the loop, so only the front check sees it). The
  Yosys backstop is the ground truth for synthesized cells.

## Proof effort

Each of the `add` and `mul` tasks has two proofs of the same statement for the
same design (a byte-identical `.sv`; `mul` has a third, a fourth and a fifth reference, three different designs): the intended workflow with the `sv_comb`
tactics (`reference/<stem>.lean`, [PROVING.md](PROVING.md)) and the baseline
without them (`reference/<stem>_byhand.lean`). Both are accepted by `check.py`
with the standard three axioms; `tests/run.py` re-checks both.

| task | proof | code lines | elaboration, best of two (wall s / CPU s) | `check.py` `solution` stage (s) | closed by the player |
|---|---|---|---|---|---|
| `add` | by hand (`add_n_byhand.lean`) | 509 | 2.8 / 3.7 | 2.8 | everything |
| `add` | tactics (`add_n.lean`) | 84 | 8.9 / 8.3 | 14.2 | 7 structure goals (one `CombDesign ∧ Acyclic` theorem) and 10 `sv_equations` obligations (all one-liners), the rank, the ports (`sv_interface`, one line), the arithmetic (about 45 lines) |
| `mul` | by hand (`mul_n_byhand.lean`) | 1385 | 7.5 / 13.3 | 11.3 | everything |
| `mul` | tactics (`mul_n.lean`) | 70 | 30.0 / 31.0 | 30.2 | 51 structure goals (24 of them are `CombDesign`'s) and 22 `sv_equations` obligations (all `intros; omega`, `sv_cover` (the six 2-D coverage goals included) or `inputsKnown`), the lexicographic key (12 lines), the ports (`sv_interface`, one line), the bridge and arithmetic (`sv_bridge`, one line per field of `MulNetlistView`, about 30 lines with the port prelude) |
| `mul` | tactics, tree design (`mul_tree.lean`, a second design: PROVING.md, section 8) | 322 | 79.3 / 80.9 | 74.4 | 69 structure goals and 38 `sv_equations` obligations (all `intros; omega`, `sv_cover` (the seven 2-D / selector coverage goals included) or `inputsKnown`), the lexicographic key (13 lines), the ports (`sv_interface`, one line), the bridge (`sv_bridge`, 18 lines, about 30 with the port prelude), the arithmetic (250 lines) |
| `mul` | tactics, Wallace tape design (`mul_wallace.lean`, a third design: PROVING.md, section 9) | 264 | 36.9 / 41.1 | 40.9 | 61 structure goals and 25 `sv_equations` obligations (all `intros; omega`, `sv_cover` (the five coverage goals included) or `inputsKnown`), the lexicographic key (9 lines), the ports (`sv_interface`, one line), the bridge (`sv_bridge`, 11 lines, about 20 with the port prelude), the arithmetic (about 200 lines) |
| `mul` | tactics, two-row-leaf tree design with a localparam (`mul_tree_h.lean`, a fourth design: PROVING.md, section 10) | 307 | 86.5 / 79.9 | 83.6 | 65 structure goals and 36 `sv_equations` obligations (all `intros; omega`, `sv_cover` (the six coverage goals included) or `inputsKnown`), the lexicographic key (11 lines), the ports (`sv_interface`, one line), the bridge (`sv_bridge`, 16 lines), the arithmetic (237 lines) |

* **Code lines** are the lines left after removing comments (line, block and
  doc) and blank lines; `import` and `namespace` lines count. It is the count
  of `leaderboard/leaderboard.py` (`lean_code_lines`), so a leaderboard record
  of the same file says the same number.
* **Elaboration** is one `lake env lean -o` of the file against the staged
  `Submission.Design` (`check.py --keep`'s `dev_hint`), under
  `LEAN_NUM_THREADS=2` and `nice` (the slot wrapper of the development machine,
  a 16 GB laptop): the best of two single runs, wall seconds and CPU seconds
  (`lean` uses two threads, so the wall clock can be below the CPU time). The
  table is the quiet machine; the same runs while other jobs were running took
  5.5 / 4.7 (`add` by hand), 15.0 / 11.4 (`add` tactics), 15.8 / 17.0 (`mul` by
  hand) and 47.5 / 40.9 (`mul` tactics). The tactic proofs take about 2.3 times
  the CPU time of the by-hand ones, because the tactics normalize large goals
  with `simp`, and are four to six times shorter. The `check.py` column is its
  own timer (`solution` stage, one run, the proof compilation only).
* **What is left to the player** is what `sv_structure?` and
  `sv_equations?` print as goals: the per-task READMEs list them tag by tag
  (`tasks/add/README.md`, `tasks/mul/README.md`), [PROVING.md](PROVING.md) shows how each
  was closed. The ports (names, order, widths, which the task statement pins) are one line,
  `sv_interface`, since WP-P; before it each tactic proof applied the soundness theorem
  `CombView.Summary.sound` by hand (23 lines). The elaboration and `check.py` columns above are the
  measurements before WP-P (the WP-P measurements are in PROVING.md, "Proof effort"); the code-line
  column is the current file (before WP-P: 107, 235, 594, 446 and 546 lines for the five tactic references;
  before WP-P3/P4, which replaced the multiplier references' glue theorem and coverage macros by `sv_bridge`
  and the 2-D rule of `sv_cover`: 84, 213, 571, 423 and 522; the WP-P3/P4 measurements are in PROVING.md,
  section 11).
* **The imports** of the tactic proofs are on the checker's allowlist
  already (`LeanModels.Sv.*`); `tests/imports/test_allowlist.py` pins that, and
  that the tactic library's own imports stay on it.
  The unsafe tactic elaborators run at elaboration only: the staged build, the
  comparator (kernel acceptance, axioms walked through the kernel values, no
  `extern`/`implemented_by` in `Submission.*`) and the `leanchecker` replay
  accept both tactic proofs.

**The proof time limit** (`time_limit_s` of `task.json`) is **120 s, the same for every task**
(decided 2026-11-02; it replaces the 10/30 rule `max(120, ceil(4 x T))`). All proofs should be
checkable quickly, so the limit is a ceiling and does not follow how slow a reference happens to
be. If an honest proof needs longer, either that proof or our scaffolding is bad, and that is
what gets fixed.

T is the LARGEST of the controlled COLD runs of the slowest reference of a task: `check.py`'s
`stages.solution.seconds`, the compile of that reference's `Solution.lean` and nothing else (not
the stages around it, not waiting for the slot wrapper). The target is T at most 60 s, a 2x margin
for a slower or busier machine. The recorded runs and what was controlled are in
`score/time_limits.json`; `python3 score/time_limits.py` prints the table, and `tests/run.py`
(step `layout`) fails when a `time_limit_s` is not 120 or a T is over it.

| task | slowest reference (cold runs, s) | T | `time_limit_s` | was |
|---|---|--:|--:|--:|
| `_example` | `band_lp.lean` (2.13, 2.08, 2.11) | 2.1 | **120** | 120 |
| `clmul` | `clmul_n.lean` (7.42, 7.66, 7.66) | 7.7 | **120** | 120 |
| `add` | `add_n.lean`, tactics (12.11, 9.57, 9.49) | 12.1 | **120** | 120 |
| `fdivp` | `fdivp_srt.lean`, its SRT core in the reference (78.58, 73.19, 69.92); `fdivp.lean`, self-contained (70.26, 64.48, 71.58; 31.0, 26.0, 24.8 with the proof library prebuilt, before 2026-11-03); `fdivp_newton.lean`, its Newton core in the reference since 2026-11-04 (49.92, 48.6, 52.67) | 78.6 | **120** | new |
| `aes_sbox` | `sbox_bp.lean` (53.73, 51.04, 50.91) | 53.7 | **120** | 215 |
| `mul` | `mul_tree.lean` (87.09, 86.76, 99.98); `mul_tree_h.lean` (71.31, 69.21, 71.31) | 100.0 | **120** | 400 |

`mul_tree`, `mul_tree_h` and `fdivp` are over the 60 s target: those are the proofs to improve, or to drop
as references (`fdivp`'s proof compiles its whole library in the solution stage since 2026-11-03: no task
ships a prebuilt proof library). Loaded-machine runs can exceed these numbers (the flat binary16 reference of the
former 16-bit task took 150 s once under load, against its 130 s limit then), so a timeout on a busy machine is re-run alone before it
counts. These runs predate WP-LIN for `add`, `mul` and `aes_sbox`.

What was controlled for the 10/30 runs: an Apple M2 Pro, 12 cores, 16 GB, macOS 27.2, a shared
development machine on which other users' jobs ran throughout (load average 5.0 to 8.8 when each
run started); COLD per run means a new process and a fresh staging directory for every run, one
run at a time through the Lean slot wrapper (`LEAN_NUM_THREADS=2`, `nice 19`), with the project
build (`lake build SvGolf tasks svgolf-eval`) warm and current and the OS file cache not purged;
Lean `v4.33.0-rc1`; `check.py`'s default light post-synthesis mode (it does not enter the proof
time). Later entries state their own conditions in `score/time_limits.json`.

## Scoring

**The ranked score is sky130 A0'** (decided 11/03): the scored netlist of the pinned flow below, each gate one sky130
cell, repaired by buffering only and weighed with the pinned `sky130_fd_sc_hd` liberty (`score/ppa.py`). Its two
numbers are the cell area in um^2 (`area_um2_sky130`, exact as `area_e4um2_sky130` in 1e-4 um^2) and the time in ps:
the critical-path delay (`delay_ps_sky130`) of a combinational design, `cycles` x the register-to-register period of a
clocked one (`check.py`'s clocked `time_ps`). Lower is better on both, and the leaderboard ranks their Pareto frontier
("Leaderboard"). Area in NAND2 gate equivalents (`area_mge`) and depth (`ltp -noff`) are EXTRA columns of the same
run: shown beside the score, ranked by nothing. "Reproduce a score" (the end of this section, and
[score/PPA.md](score/PPA.md)'s section of that name) gives every ranked number again, bit for bit.

```bash
python3.12 score/ppa.py SOLUTION.sv --task tasks/<name>        # the ranked score (sky130 um^2, ps) and the GE columns
python3.12 score/score.py SOLUTION.sv --task tasks/<name>      # the GE columns alone, at the task's scoring point
python3.12 score/score.py SOLUTION.sv --top T --param N=16     # anywhere
python3.12 score/score.py --pareto results/*.json              # the (GE area, depth) frontier: an extra view
```

The sources go through the source gate first and Yosys reads the canonical
text (`--no-gate` skips this for experiments; the result then says
`"gated": false`, and it is not an svGolf score). The pinned flow runs in TWO
Yosys processes. Stage 1, `score/canon.ys`, canonicalizes:

```
read_verilog -sv <sources>
hierarchy -check -top <top> -chparam N <n>
proc
flatten -noscopeinfo
hierarchy -top <top>
setattr -unset src; setattr -mod -unset src            # source locations
setattr -unset hdlname; setattr -mod -unset hdlname    # original hierarchical names
rename -hide                                           # every non-port name private,
rename -enumerate                                      # then numbered
write_rtlil canon.il
```

and stage 2, `score/svgolf.ys`, in a FRESH process, synthesizes and measures:

```
read_rtlil canon.il
synth -flatten -top <top>
abc -g AND,NAND,OR,NOR,XOR,XNOR,ANDNOT,ORNOT,MUX
opt_clean
stat -json                      # gate counts by type
ltp -noff                       # longest topological path
write_verilog -noattr -noexpr   # the scored netlist, for the postsynth stage
```

The extra GE columns: area is the gate count weighted by `score/ge.json` (NAND2 gate equivalents:
NOT 0.667, NAND/NOR 1, AND/OR/ANDNOT/ORNOT 1.333, XOR/XNOR 2, MUX 2.333),
kept exactly as integer milli-GE (`area_mge`). Depth is the `ltp -noff`
length, the number of gates on the longest path. Any other cell type (a
latch, a flip-flop) makes the score fail. Every result records the Yosys
version and the sha256 of both scripts (`canon_script_sha256`,
`script_sha256`), of the GE table, of the sources and of the canonical RTLIL
(`rtlil_sha256`), so two scores are comparable exactly when the flow's
hashes agree. Scoring is deterministic: `--repeat 2` synthesizes twice and
fails unless the results are identical. `--netlist OUT` and `--rtlil OUT`
keep the scored netlist and the canonical RTLIL.

**Canonical layout: the score is a function of the circuit, not of the
text.** With one Yosys process, the same circuit scored differently under a
different layout: the former 16-bit divider's goalpost gave 2079.747 GE / depth 297 as
committed and 2095.076 / 295 with its comments deleted (Yosys's results
depend on process-global state, its table of interned names, which the
frontend fills with names like `$and$design.sv:42$17`; stripping the names in
the same process does not help, re-reading the design in a fresh one does).
Under the two-stage flow, measured over 8 designs (the four tasks'
references, the Sklansky, Kogge-Stone and comparison-carry adders), the
`canon` step of `tests/run.py` checks:

* LAYOUT (leading blank lines, every line joined into one, one token per
  line, indentation removed, doubled or tabs, a line break after every
  comma) and RENAMING (every internal signal renamed four ways, generate
  labels and genvars renamed) leave the canonical RTLIL byte-identical, so
  the score cannot change. So does renaming a submodule (flattening in
  stage 1 removes module names);
* ORDER (declarations hoisted, the other module items reversed or shuffled)
  changes the numbering inside the canonical RTLIL but, measured, not the
  score (not guaranteed by construction: the regression battery watches it);
* COMMUTATION is scored: swapping the operands of every `& | ^ ^~ == != &&
  ||` is the same function but a different expression tree, and ABC starts
  from the tree it is given (`mul_n` 1962.576 → 2087.118 GE, the former
  16-bit divider's goalpost 2089.081 / 298 → 2046.093 / 300, Sklansky 127.658 / 28 → 124.992
  / 30). The score is a function of the design's expression structure: how
  you write `a & b` versus `b & a` is yours to golf. Decision
  (10/29): accepted as golfable, not normalized. Measured on `mul_n` at
  `N = 16`: one swapped operand moves the score by at most 0.03%; swapping
  every commutative operand adds 6.3% area at the same depth. Yosys hands
  ABC the same network in both cases (identical cell-type counts before
  ABC); ABC's mapping then picks different gate polarities (672 NAND / 269
  AND / 0 ORNOT against 298 / 449 / 181), because its tie-breaking follows
  the order in which it receives the nodes. It is a property of heuristic
  logic synthesis, not of the pinned flow.

**sky130 area and delay, two flows (A0' ranked since 11/03, repaired since 11/04: below).** Beside the extra GE
columns `(area_ge_v1, depth_v1)`, every check (unless `--ppa off`) records `ppa`, the scored netlist weighed with the real
`sky130_fd_sc_hd` liberty (`score/ppa.py`, [score/PPA.md](score/PPA.md)): `area_um2_sky130` (um^2, exact:
`area_e4um2_sky130` is the integer in 1e-4 um^2; the sum of the cell areas of the repaired netlist),
`delay_ps_sky130` (integer ps: the latest primary-output arrival of a graph-based NLDM static timing
analysis, every input driven by the task's input drive (default `sky130_fd_sc_hd__buf_8`) fed by a 50 ps ramp, every
output bit 10 fF, no wires), `unit_depth` (the GE
columns' depth), `cells_sky130` and `cell_hist_sky130`, with the hashes of the liberty, `ppa_pins.json`, `ppa.py` and the
weighed netlist, `setup` (the timing setup, its `input_drive` included), and `ppa_version` (`sky130_a0_v3` since 11/04,
below). This is flow **A0'**: the pinned `abc -g`
netlist re-expressed gate for gate as sky130 cells, then repaired by buffering only (no cell resized); no new synthesis and no mapping,
so it is a function of the scored netlist (the one the GE columns count) and exact run to run. Beside it, as the sub-object `ppa.mapped`, flow **A1'**:
the canonical RTLIL of the same run mapped by a real `abc -liberty` run (the pinned Yosys script `score/ppa_mapped.ys`: Yosys
0.53's default ABC script, every ordinary sky130 cell and drive strength allowed, compound cells, no sizing pass), checked against the
scored netlist on a sample of input vectors and weighed by the very same STA: `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`
(integer ps), `mapped_cells_sky130_v1`, `mapped_cell_hist_sky130_v1`, `mapped_levels_sky130_v1`, with its own version
(`ppa_mapped_version` `sky130_a1_v1`) and hashes. A1' is closer to a fabricated chip and more sensitive to the mapper than A0': over the
18 reference and baseline designs of `score/tests/ppa/designs.json` it is a median 0.93x the repaired A0' in area and 1.04x in delay,
and on the four proved multipliers it puts the array multiplier last in area where GE and A0' put it first. A0' is the ranked score
(decided 11/03); A1' is an unranked research column; their fields are never swapped silently; the measured tables are in
[score/PPA.md](score/PPA.md). The liberty is fetched, not vendored: `python3.12 score/ppa.py --fetch-liberty`. What they do
NOT claim: a fabricated chip's picoseconds (one library, one corner, no wires, a repair rather than timing closure, a 130 nm
process; the board ranks the exact integers of this model), or a difference smaller than the noise: between similar designs about **10% in area and 20% in delay** is mapper and
rewrite noise (commuting operands alone moves A0' area up to 11% and delay up to 32%, A1' area up to 15.5% and delay up to 20%;
between ABC scripts the same design's area moves a median 12% and delay 49%; both flows are bit-exact run to run, across hash
seeds, parallelism and temp directories, and A1' is ONE ABC script, so "mapped" is not "the" mapped result), and a golfer who wants a good PPA row runs ABC and the flow
themselves and submits the best one. A clocked task's design is weighed through the clocked flow (`--seq`: its
register-to-register period); every combinational idiom tried weighs once it reaches the stage, including run-time selects and shifts, `case` muxes and constant
tables, dividers (`score/tests/ppa/idioms.json`). Some designs do not reach it: the `postsynth` stage refuses a netlist whose dead
public-named wires are partly undriven or carry an x literal (a known gap of that stage, not of the columns: `score/PPA.md`, "Known gap").
`leaderboard.py pareto` ranks the A0' area and time; `pareto --axes area_mge,depth` (or `area_um2_sky130_mapped_v1,mapped_delay_sky130_v1`)
prints the Pareto frontier over other columns (opt-in; see "Leaderboard").

**sky130 A0' is repaired, and an illegal netlist is rejected (`sky130_a0_v2`; decided 11/03: sky130 A0' is the ranked
score; 11/04: the repair step everywhere, buffering only, and designs that produce illegal netlists rejected).** Before it is weighed, the A0' netlist is REPAIRED
BY BUFFERING ONLY (`ppa.py`'s own repair, `buffer_trees_v1`, the pins file's `repair` and `constants` sections): every
input is driven by the task's input drive (inputs are not free; `buf_1` in v2, below for v3), every output BIT is a 10
fF load, and every net over its driver's limits (a load over `max_capacitance` or past the timing tables, a transition
over `max_transition`), inputs, flop Q nets and nets driving output bits included, gets a balanced tree of
`buf_1`..`buf_16` cells sized from the liberty so that it is legal by construction, repeated until nothing is over; the
constant tie cell is replicated within its limit; no cell is resized. `area_um2_sky130`, `delay_ps_sky130` (for a
clocked task the register-to-register period) and the histogram are those of the REPAIRED netlist; `unit_depth` and the
GE columns are unchanged. A netlist the repair cannot make legal is REJECTED at stage `ppa` with the net named in the
design's words (an input by its port bit, what it drives as output bits); nothing is extrapolated, and no such netlist
is known on sky130. The trees are built to the limits, not for speed: a heavy net is slow, and a golfer who wants it
faster restructures it. A first version that let ABC buffer and size the netlist (`upsize; dnsize`) was dropped before
it shipped: it never load-checked the tie cell, it rejected loads ABC cannot see (an input or a flop Q wired to many
output bits) that a golfer could not fix, and its sizing moved areas +2.4% to +40% unevenly. Details:
[score/PPA.md](score/PPA.md), "The repair and the legality check". Measured on every reference and baseline at its
scoring point (11/04): all legal, none rejected; three netlists need buffers (`fdivp_newton` 1, matmul G1 5, the matmul
duplication probe 2), so every other area is v1's to the 1e-4 um^2; combinational delays +0.0% to +60.7% (median +5.3%,
the driven inputs; `sbox_table`, whose inputs are heavily loaded, most); matmul's period 48,079 to 10,705 ps (its v1
tables were extrapolated). Every task keeps v1's area and delay orders and Pareto frontiers, except matmul, where the
flop-duplication probe (4.4x faster than the reference in v1) is now slower and leaves the frontier; score/PPA.md,
"Rankings under `sky130_a0_v2`".

**The input drive is the task's (`sky130_a0_v3`; decided 11/04: each task chooses the drive that is more realistic or
interesting for it).** A task's `task.json` may name `input_drive`, the cell in front of every primary input: one of the
liberty's buffers `sky130_fd_sc_hd__buf_1` .. `buf_16`, its inverters `inv_1` .. `inv_16`, or `sky130_fd_sc_hd__dfxtp_1`
(a register's Q), the allowlist of `score/ppa_pins.json` `timing.input_drive`; absent, the default
**`sky130_fd_sc_hd__buf_8`**, which every task uses today (their inputs stand for an on-chip bus or a register). Any
other name is a task-configuration error (`tests/run.py`'s layout step, an infrastructure error in `check.py` before any
stage runs), never a number. The drive is audited like any driver, and its budget (`buf_8` 973 fF, `buf_1` 130 fF) is
the load the repair holds an input net to; the record's `ppa.setup.input_drive` names it, so it is in the record hash,
and each task's README states it; a record weighed under another drive than its task's now is not comparable:
`leaderboard.py verify` marks it stale and `pareto --axes` does not rank it (never a failure). Why `buf_8` (MEASURED
over the 36 ranked rows under five drives): no drive changes any task's orders or Pareto frontier, and `buf_8` adds a
small, nearly uniform 73 to 192 ps over an ideal input where `buf_1` added 70 to 1,276 ps (`sbox_table` +61% for one
legal 115 fF input load, which the golfer could not buffer away). Measured against v2: every area unchanged,
combinational delays -1,084 ps (`sbox_table`) to +25 ps (median -66), matmul's period 10,705 ps unchanged, and 0 flipped
pairs and 0 frontier changes on every task: no ranking moves. score/PPA.md, "The input drive" and "Rankings under
`sky130_a0_v3`".

**Loads per edge (`sky130_a0_v3`, before its release, 11/04).** A load pin presents its `rise_capacitance` to a rising
edge and its `fall_capacitance` to a falling one, as OpenSTA reads them; the STA had loaded every net with the pins'
`capacitance` and was 0.5% to 2.8% off OpenSTA on the references. With the change it equals OpenSTA to 1 fs per arc
(`score/test_ppa_opensta.py` records OpenSTA's numbers). MEASURED on every reference and baseline at its scoring point:
every area unchanged, delays -0.30% to +1.32%, no delay order, area x time order or Pareto frontier changes; matmul's
period 10,705 to 10,696 ps (one of its five trees is now 2 x `buf_4`, 6 buffers, the same area), the sorter's 2,510 to
2,523. score/PPA.md, "The per-edge loads".

**Reproduce a score.** The ranked numbers (A0' area and time) are a pure function of the design text, the pinned flow, the
pins and the task's scoring point and input drive, and each is reproduced bit for bit by one command from the repository's root (Python 3.12 with `pyslang`, `Yosys 0.53 (git sha1
53c22ab7c0ce…)` and the `yosys-abc` beside it on `PATH`):

```
python3.12 score/ppa.py --fetch-liberty                     # once: the pinned liberty (sha256 ef34f999…5d23d5) into score/lib/
python3.12 score/ppa.py SOLUTION.sv --task tasks/<name> --no-mapped --json out.json --netlist scored.v --repaired-netlist repaired.v
python3.12 score/ppa.py SOLUTION.sv --task tasks/matmul --seq   # a clocked task
```

That is the source gate (`score/srcgate.py`: the canonical text), Yosys process 1 (`score/canon.ys`: read, `hierarchy
-chparam` at the task's scoring point, `proc`, `flatten`, names and `src` attributes stripped, `write_rtlil`), Yosys
process 2 (`score/svgolf.ys`: `synth -flatten`, `abc -g AND,NAND,OR,NOR,XOR,XNOR,ANDNOT,ORNOT,MUX` with Yosys 0.53's
default ABC script, `write_verilog`; clocked: `score/svgolf_seq.ys`), then `ppa.py` in Python alone: one `_1` cell per
gate, the buffering repair, the STA with the task's input drive behind a 50 ps ramp and 10 fF per output bit, the
legality audit. `out.json` carries every input's hash (Yosys version, scripts, canonical RTLIL, liberty, pins, `ppa.py`,
the scored and the repaired netlist) and `setup`. [score/PPA.md](score/PPA.md), "Reproduce a score", lists the tool
versions and file hashes, prints both Yosys scripts as filled in for the `add` reference, shows the ABC scripts, and
runs the same steps by hand (`srcgate.py`, two `yosys -s` runs, `ppa.py --netlist-in`); it was tested by following it
literally in a scratch copy on the `add` and `aes_sbox` references, bit for bit equal to the goldens.

## The banlist

`score/banlist.py` runs two independent checks, both driven by the task's
`banlist.operators`, on the source gate's canonical text:

* the **front check** (pyslang) elaborates the design at the defaults and at
  the task's probe and backstop points, walks every run-time root
  (continuous assigns, procedural blocks, net and variable initializers, port
  connections, and the bodies of functions called with run-time arguments
  or whose body reads a signal declared outside the function, including
  generate branches the scoring point does not take), and flags each banned
  operator, unary minus, `++`/`--` and compound assignment whose operands
  read a run-time value. Parameters, localparams, genvars, enum values and
  procedural loop counters are constant; a loop counter is recognised by
  symbol identity (a module signal that shares its name is still run-time),
  a pre-declared counter (`for (k = 0; ...)`) only inside its loop, and a
  counter the loop body writes never. A call is constant only when its
  arguments are AND its body reads nothing but its own arguments, locals and
  return variable: `function automatic logic [15:0] g(input int k); g = a /
  16; endfunction assign q = g(0);` divides `a` at run time (and the backstop
  cannot see it: Yosys turns `/ 16` into a shift). The system functions Yosys
  builds from `$add` chains (`$countones`, `$countbits`, `$onehot`,
  `$onehot0`, `$isunknown`) are banned with `+` on a run-time argument, and
  the array reduction methods `.sum()` and `.product()` with `+` and `*`
  (`.and()`, `.or()`, `.xor()` are bitwise and allowed). It reports
  `file:line:col`.
* the **backstop** (Yosys) runs `proc; opt` at the backstop points, BEFORE
  `alumacc` (so comparison cells stay allowed), and rejects every cell of the
  banned operators' types (`$add $sub $neg $mul $div $divfloor $mod $modfloor
  $pow`, plus `$alu $macc $macc_v2 $lcu $fa` when any of `+ - *` is banned).
  It reports the cell's source location.

Note that run-time index arithmetic is arithmetic: `a[j + 1]` with a signal
`j`, `v[sel -: 4]` and `x[sel*W +: W]` build `$add`/`$sub`/`$mul` cells and
are rejected under an arithmetic banlist.

## Leaderboard

`leaderboard/leaderboard.py` (documented in full in
[leaderboard/README.md](leaderboard/README.md); Python 3, standard library
only) turns an accepted submission into a **record** and ranks the records
on the sky130 A0' score: the area in um^2 and the time in ps (decided 11/03;
"Scoring"). Area in GE and depth are extra columns.

```bash
# record locally: runs check.py on the pair and writes the record only if it is ACCEPTED.
# --data-dir keeps YOUR records out of the repository's own (leaderboard/data holds the
# reference records and, today, is the only board there is)
python3 leaderboard/leaderboard.py add --task add --player alice \
    --assisted-by "Claude (Anthropic)" --sv my_adder.sv --lean MyAdder.lean --data-dir ./my-records
python3 leaderboard/leaderboard.py pareto --task add --data-dir ./my-records  # the (sky130 area, time) frontier
python3 leaderboard/leaderboard.py pareto --task add --axes area_mge,depth      # opt-in: the frontier over other columns (here GE)
python3 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1   # ... over flow A1''s columns
python3 leaderboard/leaderboard.py board  --task add       # ranked table (--format json too)
python3 leaderboard/leaderboard.py verify                  # re-verify every stored record
python3 leaderboard/leaderboard.py export --out LEADERBOARD.md   # all tasks, Markdown
```

* **There is no submission server yet.** `add` writes a record on your machine and nothing is
  sent anywhere. A record is self-verifying (`verify --full` re-runs the whole check), so a
  pull request carrying the record directory is a possible hand-off, but how records reach a public
  board is an open decision (PLAN.md, "Open questions for the maintainers"); until it is taken, the board
  is the maintainers' `leaderboard/data`, and running `add` without `--data-dir` writes into it.
* **A record** is one JSON file per accepted submission,
  `leaderboard/data/<task>/<record_hash>.json`, with the submitted `.sv` and
  `.lean` copied next to it. It holds the player handle, `assisted_by`, the
  sha256 of both files and of the source gate's canonical text, the GE
  columns (`score`: `area_mge` in integer milli-GE, depth, gate counts, scoring point), the
  checker's identity (svgolf and lean-surfaces revisions, Lean toolchain, Yosys
  and Verilator versions, the sha256 of the two scripts, the GE table and the
  checker's files), the proof's facts (axioms, build seconds, code lines,
  imports, tactics), the optional `ppa` object (check.py's sky130 columns, flow A0', THE RANKED SCORE, and inside it the
  optional sub-object `mapped`, flow A1', see "Scoring"; a record made before them has no such key and stays valid but is
  not ranked until it is backfilled, and a
  `leaderboard.py` from before the `ppa` key treats a record that has one as corrupt: update every reader first; one
  from before `mapped` accepts it) and `record_hash`, the sha256 of the record's canonical
  JSON. `add` refuses anything `check.py` does not accept at every stage.
* **How a record is verified.** `verify --offline` re-hashes the record and
  the stored files and rechecks the area arithmetic (milliseconds); plain
  `verify` also rescores the stored design with `score.py` (the source gate
  and the pinned Yosys flow: seconds, no Lean); `verify --full` runs
  `check.py` again on every stored pair (the cost of the original checks).
  Records are tamper-evident, not tamper-proof; see leaderboard/README.md for
  what each level catches.
* **Official artifacts are full, and carry the PPA columns.** `add` runs `check.py --ppa require --postsynth full` (the whole
  post-synthesis vector budget, and the sky130 columns: an absent pinned liberty is an infrastructure
  error and a live `add` writes nothing; `add --from-check RESULT.json` records a stored result as it is, so a
  result made by `--ppa auto` that found no liberty is refused and a result with no `ppa` key (`--ppa off`, an
  older checker) gives a record without the columns, which `add` says in a NOTE), `verify --full` rechecks the same way (a record made before the columns:
  with `--ppa off`, it needs no liberty; under another Yosys flow the record is stale and the columns are not compared)
  and compares the columns exactly
  (`verify` without `--full` re-weighs through `score/ppa.py` when the liberty is there and says so when it is
  not; `--offline` checks the columns against the record's own score), and
  `seed-references` records in full mode: `check.py`'s own default, `light`, is for
  local feedback. A result whose post-synthesis check ran light is REFUSED by
  `add` unless `add --postsynth light` asks for a light record, which the record
  marks (`postsynth.mode: "light"`, with `vectors` and `full_vectors`), `add` says in
  its output, and the boards show (`light` after the record hash, and a footnote). A
  record without `postsynth.mode` was made before the modes existed and reads as
  full. Whether a public board accepts light records is the hand-off policy
  (undecided; the default is that it takes full records only); a light record is a
  legitimate local one.
* **`assisted_by`** is the list of tools and AI systems that helped write the
  design or the proof, as free text (`["Claude (Anthropic)", "a proof assistant"]`);
  empty means unassisted. It is the submitter's word, shown next to every
  entry, and `--unassisted` ranks only the entries with an empty list. It does
  not change the ranking otherwise.
* **The boards rank the sky130 score** (decided 11/03). `pareto`, `board` and `export` rank the A0' area
  (`ppa.area_e4um2_sky130`, exact in 1e-4 um^2) and time (`ppa.delay_ps_sky130`; a clocked record's `score.time_ps`,
  cycles x period) and show the GE area and depth as extra columns. A record is ranked only if it carries the columns and
  they are comparable: weighed under the current `ppa_version`, liberty and pins file, and under the task's input drive
  now. The others are listed as "Not ranked" with the reason; a record without sky130 columns (made before them, or with
  `--ppa off`) is not ranked until it is backfilled (checked again under `--ppa require`). `pareto --axes` (any of
  `area_mge`, `depth`, `area_um2_sky130`, `time_ps`, `delay_ps_sky130`, `unit_depth`, `cells_sky130`, and flow A1''s
  `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1`, `mapped_levels_sky130_v1`) is the
  opt-in n-dimensional frontier over other columns (`--axes area_um2_sky130,time_ps` is the board's; ties kept, areas
  compared as exact integers); records without them, or computed under another `ppa_version`/liberty/pins (or, for the
  mapped axes, another `ppa_mapped_version`/script/pins), are listed as "not shown" with the reason. The boards print no
  confidence band: that 10% / 20% noise is a ranking decision, not a column.
* **Policy: the Pareto frontier, no budget by default.** A record is on the
  frontier iff no other record is at least as good on both sky130 area and
  time and strictly better on one; ties are kept; listings are in one
  deterministic order (area, time, earlier date, player, hash: on a tie in
  both, the earlier record stands). The board lists the frontier first, then
  the dominated records by layer. A task author may add a depth budget
  (`leaderboard.depth_budget` in `task.json`, ranking only; or the checker's
  own `scoring.depth_budget`, which rejects; on the unit depth): the board
  then also ranks the best sky130 area under it and flags the entries over
  it. No task has one today. Scores are comparable exactly when the pinned
  flow, the scoring point, the sky130 pins and the task's input drive agree,
  so the board ranks only records checked under the current ones and lists
  the rest as "Not ranked" until they are submitted again.

Reference points that are **not** records, because `check.py` accepts nothing
unproved or with a banned operator (at `N = 16`: the ranked sky130 A0' area and
time from `score/tests/ppa/expected_ppa.json`, the extra GE area and depth from
`tests/expected.json`):

| task | design | sky130 um^2, ps | GE, depth |
|---|---|---|---|
| `add` | Sklansky prefix adder (simulation only) | 541.7696, 2451 | 127.658, 28 |
| `add` | Kogge-Stone prefix adder (simulation only) | 641.8656, 2064 | 149.652, 24 |
| `add` | comparison-carry adder (policy probe, simulation only) | 857.072, 1965 | 195.975, 17 |
| `add` | Yosys's own `{cout, s} = a + b + cin` (banned `+`, banlist lifted) | 497.9776, 3143 | 117.994, 33 |
| `mul` | Dadda tree + ripple final adder (simulation only) | 8230.3936, 5461 | 1953.585, 61 |
| `mul` | Dadda tree + Kogge-Stone final adder (simulation only) | 8937.3216, 5148 | 2076.51, 48 |
| `mul` | Yosys's own `p = a * b` (banned `*`, banlist lifted) | 8825.9648, 6261 | 2081.227, 59 |
| `fdivp` | the flat binary16 divider (the reference of the former 16-bit task, removed 2026-11-03) under the parametric header, right at `(5, 11)` only (simulation only; at `(5, 11)`) | 8734.6272, 35735 | 1944.775, 303 |

The proved references are the first records (`svgolf-reference`,
`assisted_by` `["Claude (Anthropic)"]`, notes `reference solution`;
`leaderboard.py seed-references` records them again; the records of
`leaderboard/data` were re-seeded under `sky130_a0_v3` on 11/04, with the
same design and proof files, so they carry the ranked columns).

## Tests

```bash
SVGOLF_LEAN_WRAP=<slot wrapper, optional> python3.12 tests/run.py   # everything; exit 0 iff all pass
python3.12 tests/run.py --only add --skip attacks                   # one task, a step skipped
python3.12 tests/run.py --full                                      # with the heavy simulation plans
```

`tests/run.py` is the one entry point. It runs, in order, and prints a
summary table (step, checks, failures, time):

* `layout`: every `task.json` against the schema above, every reference a
  proved `<stem>.sv` + `<stem>.lean` pair (a draft: `<stem>.partial.lean`),
  nothing a player does not need under `tasks/`, no extractor output outside
  `.lake/`, `tests/expected.json` listing exactly the designs on disk (its
  `flow` the pinned flow: Yosys version, the sha256 of both scripts and the
  GE table; a reference marked `same_design_as` byte-identical to its twin),
  and the Dadda baselines reproducible from `gen_dadda.py`;
* `build`: `lake build` (SvGolf, tasks, tests), so every refutation of a
  negative design is re-checked by the kernel, its design re-extracted by
  `load_sv` when anything it depends on changed;
* `unit`: `score/test_score.py`, `score/test_srcgate.py`,
  `score/banlist.py --selftest`, `score/fourstate.py --selftest`, and
  `tests/checker/test_advisories.py` (the oracles against independent arithmetic, the
  functional comparison and its warning, the `--tactics` classification, `dev_hint`,
  the stripped `SVGOLF_ELAPSED` line, the post-synthesis mode selection and light
  vector set, the generated `Submission.Design` text: no Lean, 46 tests),
  `tests/checker/test_design_stage.py` (the `design` stage rejecting an Unsupported
  construct, on check.py's real early stages with a fake Lean: 5 tests), `score/test_ppa.py`
  (the sky130 columns, stage 1: the netlist reader on escaped identifiers and dead wires, the eight idiom
  designs of `score/tests/ppa/idioms.json` with goldens; flow A1' (WP-X4): the mapped netlist weighed by the same STA, the equivalence
  sample, the pins, the loud reasons, the goldens of `expected_ppa_mapped.json`, bit-exactness across hash seeds and temp
  directories; its real-liberty tests are skipped where the pinned liberty is absent),
  `tests/checker/test_ppa_wiring.py` (the `--ppa` modes, the absent and the unreadable liberty, a netlist
  swapped after the postsynth stage, `aes_sbox` designs with dead wires in their netlists through check.py's stages, the
  integrity tripwire over `score/ppa.py`, `score/ppa_pins.json`, `score/ppa_mapped.ys` and `score/ppa_mapped_pins.json`, flow A1''s
  `mapped` block through check.py's stages and its failure modes, and the byte-identity of the default
  result against the checker from before the wiring on the `add` and `aes_sbox` references: `--ppa off` is
  the old result character for character, `auto` is that plus exactly the key `ppa` and the stage
  `stages.ppa`; no Lean, a fake Lean for the `design` stage), `score/time_limits.py
  --selftest`,
  `tests/checker/test_import_packages.py` (imports from the Mathlib packages, on
  check.py's real early stages with a fake Lean: the generated import probe, a
  module no package has a source for rejected at `imports`, a package or module
  missing from the machine, a checkout at another revision or a probe that dies
  silently an infrastructure error, a comment between two imports, the REAL
  `integrity_snapshot` inside `check` with a solution whose build changes, adds or
  deletes a package olean, creates a search-path entry that did not exist or a module
  root, or edits the manifest, and the comparator's import report checked against the
  header: 27 tests, mutation-checked), and
  `tests/imports/test_allowlist.py` (the checker's import allowlist against
  `tests/expected.json`'s `import_allowlist`: the 14 sv_comb tactic modules,
  the framework modules and Mathlib with its packages admitted; `Examples.*`,
  `LeanModels.Python.*`, `LeanModels.Core.*`, another submission, `Lake`, `Cli`
  and lookalikes (`Mathlib2`) refused; header parsing; the import closure of the
  tactic library, 44 modules, inside the list, so a later change of
  lean-surfaces that made a tactic module import something off the list fails
  here, not in every reference proof; and the import closure of `Mathlib`,
  8,643 package modules in eight roots, recomputed from the package sources, so a
  Mathlib bump that reaches a package the checker does not admit fails here; the
  glued-import headers; `SvGolf/CoreSimp.lean` lists exactly the checker's package roots), and the
  sandbox's own tests (WP-S, "Sandbox" under "Checking"): `tests/sandbox/test_env.py` (the environment
  allowlist; an AST lint that every `subprocess` call of the checker passes `env=`),
  `tests/sandbox/test_sandbox.py` (profile and `bwrap` argument generation, the supervisor's limits, a
  self-test that must fail on a mechanism that does not sandbox, `configure`, the Lean plumbing with a stubbed
  supervisor, the real mechanism on small commands; skipped where there is none) and
  `tests/sandbox/test_tools.py` (Yosys `$readmemh` and a Verilator model's `$system`, unsandboxed and
  sandboxed; needs Yosys, Verilator, `make` and a C++ compiler);
* `comparator`: `tests/checker/test_comparator.py`, `check/Comparator.lean` on a
  hand-built module chain with real Lean and nothing from Mathlib (about a minute): the
  honest chain accepted with its report (imports, toolchain modules, replay), a "package"
  whose `theorem evil : False` was added with the kernel check off (it passes the
  comparator's kernel check and axiom walk and is rejected by the replay of the
  dependency closure, with the kernel's error), a package axiom, a copy of a toolchain
  module (`Lake.Util.Casing`) resolved from a directory ahead of the toolchain's, and an
  `extern` under the submission prefix; and `tests/checker/test_bv_decide.py` (about two minutes,
  real Lean; the dormant re-verification of `bv_decide` axioms, "`bv_decide`" above): with `--bv-decide`
  real proofs accepted with their axioms listed under `bv_decide.verified` (one axiom, two, one behind a
  helper lemma) and a hand-written axiom with the generated name and a TRUE statement accepted;
  rejected: a forged axiom over a false certificate (which proves `False`, and passes the comparator's
  kernel check), the generated name over the wrong type, a true statement under another name, a true
  statement whose formula is `id E` or whose certificate is not a literal, a shared term over the
  decoding budget and a term over the depth limit, `Lean.ofReduceBool`, `native_decide`; and without the
  flag, which is all `check.py` passes, every `bv_decide` proof, naming the policy;
* `leaderboard`: `tests/leaderboard/test_leaderboard.py` (record round trip
  and tamper detection, refusal of rejected submissions, the Pareto frontier,
  the depth budget, the Markdown golden file, `add` against a fake
  `check.py`: synthetic check results, the post-synthesis mode in records,
  `add` and the boards, no Lean, no Yosys, about 2 s) and
  `leaderboard/leaderboard.py verify --offline` on the committed records
  (hashes, stored files, score arithmetic);
* `modes`: the post-synthesis modes through `check/postsynth.py`, no Lean
  (`_example` and `add` in both modes, `mul_n` in light: the record says which
  ran, the full record is the whole set, the light one stays within the task's
  `light_vectors` and under the full set, both share the seed and the full
  set's size; the command line and `$SVGOLF_POSTSYNTH` select the mode, the
  flag wins, a typo is an error);
* `canon`: the canonical layout (see "Scoring"): each design of
  `tests/expected.json`'s `canonical_layout` re-laid-out and renamed has a
  byte-identical canonical RTLIL and its score, reordered its score, and with
  its commutative operands swapped the recorded score;
* `references`: every proved reference (both pairs of `add` and `mul`: the
  tactic proof and the by-hand baseline) through `check.py --postsynth full`:
  accepted (the `postsynth` stage included, in FULL mode: the whole vector
  budget, `vectors == full_vectors`, and the `design` stage's unsupported-
  construct check ran at every point it should), and the score equal to `tests/expected.json`
  (area in milli-GE, depth, gate mix) at the scoring point and at every
  other point a README quotes (a `same_design_as` twin only at the scoring
  point: same bytes, same score);
* `drafts`: a draft task's goalpost through `check.py` with its partial Lean
  file, rejected exactly at the expected stage (`comparator`: no
  `Submission.solution`, every earlier stage passes), and its score;
* `negatives`: every negative design through `check.py` with the task's
  reference proof, rejected at its expected stage (`banlist` for the banned
  operators, `fourstate` for the two that read an undriven net, `solution`
  for the rest; every refutation is in the `tests` library), and its quoted
  scores;
* `baselines`: every baseline scored (`score.py` applies no banlist, so a
  banned-operator baseline is scored "with the banlist lifted"), the
  banlist's verdict as expected, token identity where claimed, the 4-state
  rules passing at every scored point, and the post-synthesis check passing (`check/postsynth.py`, at the scoring point;
  `--full`: at every scored point), so no legitimate design is falsely
  rejected;
* `ppa`: the sky130 columns of every design of `score/tests/ppa/designs.json` that the `references` step
  did not already see in a real `check.py` result (the baselines, the banned-operator probes, the draft
  goalpost), weighed by check.py's own `ppa_block` and equal to `score/tests/ppa/expected_ppa.json`, and of
  the eight netlist idioms of `score/tests/ppa/idioms.json` (equal to `expected_idioms.json`, whatever
  `--only` says). The goldens pin (GE, depth, gates) and (um^2, ps, levels, cells, netlist hash); every
  weighed block is also checked by derivation for what they do not pin (area against the cell histogram
  priced in the live liberty, the setup and liberty file against the pins, the shape of `critical`). The
  `references` step checks the same on the `ppa` block of each reference's real result (run
  with `--ppa require`), and that the `add` and `aes_sbox` results are, key for key, the checker's from
  before the wiring plus the new key and stage. **Without the pinned liberty** (not in the repository:
  `python3.12 score/ppa.py --fetch-liberty`) these checks are SKIPPED with a message (recorded as ok, saying
  SKIPPED), the references run `--ppa auto`, and `score/test_ppa.py`'s real-library tests skip as before;
  nothing unrelated fails. Where the file exists the suite sets `SVGOLF_PPA_REQUIRE_LIB=1` (a real-library
  test cannot skip silently); a file that is not the pinned liberty is one failure;
* `validate`: simulation, quick plans by default (Verilator and ls-sv `run2`
  on the `add` designs, the scored `add` netlists in Verilator, Verilator on
  every `mul` design, Verilator on the `fdivp` designs at many formats, `aes_sbox`'s cross-checks against FIPS 197
  and the authors' netlists and Verilator on all 256 inputs of every design), the documented
  full plans with `--full` (hours: exhaustive and bulk runs);
* `attacks`: the checker attacked with submissions written to a temporary
  directory: a proof of the wrong statement, an extra axiom, a hand-declared
  axiom shaped like `bv_decide`'s (`bv_decide_shaped`: rejected at the comparator by policy,
  "`bv_decide` is not supported"), the reference proof plus a fixed-size fact closed by a real
  `bv_decide` (`bv_decide_subgoal_sandbox`: rejected at `solution` with the hint, because the sandbox
  does not let the tactic start its solver; `bv_decide_subgoal_off`: with `--sandbox off` it compiles and
  is rejected at `comparator`, naming the policy), the DORMANT groundwork rows through
  `tests/checker/check_bv_enabled.py` (`bv_decide_groundwork_accepted`: the same proof ACCEPTED, its axiom
  re-verified; `bv_decide_groundwork_forged`: a forged axiom rejected by evaluation, "does not
  verify"), an `implemented_by`, a `solution` and a
  lemma added with the kernel check off (the comparator catches the first,
  only `leanchecker` the second), a forbidden import (`Examples.*`, and, next
  to the allowed sv_comb library, a lookalike `Mathlib2.Tactic` and
  `LeanModels.Python.*`), the Mathlib attacks (`mathlib_native_decide`,
  `mathlib_decide_native`: the `_example` proof with Mathlib tactics and a lemma closed
  by native evaluation that the proof uses, rejected at the comparator naming
  the generated axiom `native_helper._native.*`; `mathlib_lookalike`; `mathlib_glued_lookalike`: the
  lookalike hidden behind a comment on the previous import's line; `mathlib_plant_free` and
  `mathlib_plant_importing`: a solution whose build creates a file in Mathlib's build directory,
  rejected at `integrity`, the runner removing the file afterwards) next to the runs that must be
  ACCEPTED (`mathlib_band`, and `mathlib_tactics_*`: the tactic-proved references (`TACTIC_REFERENCES` of `tests/run.py`) with
  `import Mathlib.Tactic`, no `sv_core_simp` needed), a missing design import, a design whose parameter has the wrong name, one whose parameter is
  4 bits wide (Yosys would score `N = 16` as `N = 0`), and the source-gate
  fixtures (`score/tests/gate`: `` `ifdef SYNTHESIS ``, `` `ifdef YOSYS ``,
  `translate_off`, `(* full_case *)`, `unique case`, `priority case`, x/z
  literal digits in case items, `==` operands and localparams, an `x` digit
  in a casez item, and the host-access families: `$readmemh` / `$readmemb` /
  `$writemem*`, `$fopen` and the file I/O family, `$system`, `$test$plusargs` /
  `$value$plusargs`, `$dumpfile` / `$dumpvars` / `$dumpports` (in an `initial`
  block and, the one form that reached the proof stage before the gate, in an
  `always_comb`), DPI imports and exports, `$sdf_annotate` / `$coverage_save` /
  `$input` / `$log` / `$save`, an escaped `\$`-name, and the same calls in dead
  code or behind a macro), each with the reference proof. Each must be rejected
  at its stage. The positive twins (`ok_host_comments.sv`, `ok_host_words.sv`:
  the refused names only in comments, string literals and an identifier that
  contains a `$`) go through `check.py --unproved` and must pass every check
  that needs no proof; `ok_host_console.sv` (`$display` and `$write` in an
  `initial` block) is gate-only, because ls-sv refuses `initial`. All three
  must also be text Yosys reads (`score/test_srcgate.py`). Then the
  designs of `tests/<task>/attacks/`, where ls-sv and Yosys read one text
  differently, through `check.py --unproved` (none has a proof): each
  rejected at its stage, `source` for the x/z literals and
  `unique`/`priority`, `fourstate` for x without a literal (a constant
  `1 / 0`, an undriven net, an out-of-range read), `banlist` for the
  loop-counter writes and `.sum()`, `design` for a design that loads with an
  Unsupported node (WP-C3: the latent function-local x, the two latches, and
  `func_call.sv` / `assign_func.sv`, a correct `a & b` through a user function;
  the message must name the construct); and, where `tests/expected.json` says
  `postsynth_alone`, the postsynth check with the source gate and the
  fourstate stage bypassed, which must reject, or pass where the expectation
  says so: the two benign `unique` designs, and the two one-input-pair
  differences (`add`'s `zpair_add_rare.sv`, `_example`'s `oob_rare.sv`)
  that sampling cannot be expected to find, which is what the static
  refusals are for. That run, and the `check.py` run, are in the LIGHT mode
  unless the entry says `postsynth_mode: full` (`rare_mid.sv`, the one attack
  only the full check rejects; its `postsynth_light: passes` pins the light
  mode's verdict). The `attacks` that exercise the integrity tripwire (`mathlib_plant_*`) run with
  `--sandbox off`, because with the sandbox the write they attempt is denied before the tripwire has
  anything to see; `host_env_salt` is ACCEPTED only when the checker's secrets (the competition salt,
  tokens) are invisible to the Lean file.
* `sandbox` (WP-S): the sandbox against real attacks, each through `check.py --sandbox require` on `_example`
  (skipped, with a message, where the machine has no mechanism): `host_naive` (the 2026-10-31 finding: with
  `--sandbox off` ACCEPTED and the file outside the stage exists, the control that shows the attack is real;
  with the sandbox REJECTED at `solution`, "operation not permitted", no file), `host_catching` (every
  action tried and every failure caught, so the file compiles either way: with `--sandbox off` the marker is
  written, a loopback listener hears a connection and the tripwire rejects the overwritten `Design.olean`; with
  the sandbox ACCEPTED, every action but the harmless listing of the scrubbed environment BLOCKED, no marker, no connection),
  `host_memory_bomb`, `host_output_flood` (a flood to `/dev/fd/1`, past `#eval`'s capture) and `host_cpu_bomb`
  (stopped by the supervisor's memory limit, output cap and the task's wall clock), and the two tripwire attacks with
  the sandbox ON. `tests/run.py --sandbox require` runs EVERY step's `check.py` calls with it.

Runtime (measured 2026-10-29 with Verilator as the simulator, 226 checks
without `validate`, 0 failed): 20 minutes of work when the Lean slot is free
(build 30 s, canon 68 s, references 207 s, drafts 53 s, negatives 245 s,
baselines 372 s, attacks 233 s) and 4 minutes for the quick `validate` plans
(14 checks; `add`'s `validate.py` is 3 minutes, 90 s of them the C++ builds of
45 designs-and-widths at about 2 s each; the former 16-bit divider's `sample` step was 3 s where
the Icarus step was about 90 s). The ~60 `check.py` runs take 10 to 60 s each,
the `mul` reference about 90 s with its postsynth stage; the 16-bit Dadda
trees' postsynth checks are the long ones (83 and 162 s); the build is
45 s to 90 s when the refutations re-elaborate (a changed design, task,
extractor, or a comment in a `.sv`). On a machine whose one
Lean slot another job holds, waiting comes on top: the runs of 2026-10-28
took hours of wall clock for that reason. `--full` adds hours (`fdivp`'s
exhaustive steps, the `mul` reference's full plan, `add`'s full
`validate.py` and `verilator.py`, and the postsynth checks of every baseline
at every scored point).

The sky130 columns (WP-X3) add about 60 s to that (measured 2026-10-31, again after the review fixes): the `ppa` step
17 s run alone (the sixteen designs of `designs.json`, 12 s, and the eight netlist idioms, 5 s; in the full suite the
`references` step has already weighed some of them), `tests/checker/test_ppa_wiring.py` 41 s in the `unit` step (28
tests), `score/test_ppa.py` +7 s (34 tests, 17 to 23 s depending on load), `leaderboard` +1 s, and in each reference run the
`ppa` stage itself: 0.11 to 0.13 s under `--ppa auto`, 0.00 to 0.02 s under `--ppa require` (what the suite uses: the liberty
is opened before the first stage). Where the pinned liberty is absent the `ppa` step and the per-reference checks are skipped
(a message each) and only the wiring tests' absent-liberty cases run.

`python3.12 tests/run.py --update-scores` rewrites the scores in
`tests/expected.json` with the measured ones, after a deliberate change of the
pinned flow (review the diff: every README quoting a changed score must change
too).

**Nightly.** `python3.12 nightly.py` (from the repository's root; `--only`, `--skip`, `--full` pass through to
`tests/run.py`) runs the whole suite plus the checks that keep the register and the docs honest
(`REFUSALS.md` against what the pinned register renders, `score/time_limits.py --check`), writes
`nightly/<stamp>/{run.log,checks.json,report.md}` (not committed) and compares the checks with the newest earlier
run: `REGRESSION` (was ok, now fails or vanished), `FIXED`, `NEW`, `SLOWER` (more than 1.5 x and 30 s). Exit 0 iff
nothing failed and nothing regressed. Scheduling it (cron, launchd) is the operator's business; it edits nothing
outside `nightly/`.

## Tasks

| task | statement | reference | score at N = 16: sky130 A0' um^2, ps (ranked); GE, depth (extra) |
|---|---|---|---|
| `_example` | N-bit bitwise AND (toy) | `assign y = a & b;`, for-all-`N` proof | 100.096 um^2, 280 ps; 21.328 GE, depth 1 |
| `add` | N-bit adder with carry, `{cout, s} = a + b + cin`; bans `+ - * / % **` | ripple carry from gates, for-all-`N` proof (with the sv_comb tactics, and by hand as `add_n_byhand`); Sklansky and Kogge-Stone prefix adders by simulation (`tests/add/baselines`) | ripple 460.4416 um^2, 2611 ps; 112.0 GE, depth 33. Sklansky 541.7696, 2451; 127.658, 28. Kogge-Stone 641.8656, 2064; 149.652, 24 (Yosys's own `+`: 497.9776, 3143; 117.994, 33) |
| `mul` | N-bit unsigned multiplier, `p = a * b` on `2N` bits; bans `+ - * / % **` | array multiplier (AND partial products, ripple-carry rows of full adders), for-all-`N` proof (with the sv_comb tactics, and by hand as `mul_n_byhand`); Dadda trees by simulation (`tests/mul/baselines`) | array 8290.4512 um^2, 10907 ps; 1962.576 GE, depth 88. Dadda + ripple 8230.3936, 5461; 1953.585, 61. Dadda + Kogge-Stone 8937.3216, 5148; 2076.51, 48 (Yosys's own `*`: 8825.9648, 6261; 2081.227, 59) |
| `fdivp` | IEEE 754 division PARAMETRIC in the format, `fdiv #(W, P)` on `W + P` bits for every `W >= 2`, `P >= 2`, round to nearest even, canonical NaN, subnormals (`SvGolf.IEEE754.divide`); bans `/ % **` | a word-level netlist of 34 sites (linear normalizer and `P + 2` restoring steps as generate families), Verilator-validated on all 66 formats with `W + P <= 14` and both 2^32-pair formats and **proved for every format** (`tasks/fdivp/README.md`; one self-contained proof over `LeanModels.Sv.Lib`: the spec's facts, the certificate, the math layer, the glue `Glue.chain`, `OutN_fdivBits`); binary16 is the instance `(5, 11)` (the former 16-bit task, removed 2026-11-03, is folded in); the natural form D1 and the fragment-friendly D2 are baselines (`tests/fdivp/baselines`); a second proved reference, a Newton-Raphson divider (a logarithmic number of Newton steps over the run-time `*`), is not competitive; a third, a radix-4 SRT divider adapted from CORE-V Wally (carry-save remainder, digit selection by table constants, on-the-fly conversion), is the fastest | 9675.5296 um^2, 37984 ps; 2166.076 GE, depth 289 at `(5, 11)` (Newton 33824.9408, 40031; 7892.452, 252; SRT 12356.8512, 27592; 2787.652, 189; D1 1911.446 GE, 300, not weighed) |
| `aes_sbox` | the AES S-box (FIPS 197 Section 5.1.1), `y = S(x)` on 8 bits, defined algebraically (inverse in GF(2^8), then the affine map), fixed size; NO operator banned; the post-synthesis check is exhaustive (all 256 inputs) | Boyar-Peralta 113-gate circuit, validated (Verilator, all 256 inputs; gate for gate against the authors' netlist file), scored and **proved** (113 plain sites: `sv_structure` and `sv_equations` decide the obligations of a flat netlist instead of normalising them, `PROVING.md` section 12); a 256-entry `case` table and the depth-16 Boyar-Peralta circuit by simulation (`tests/aes_sbox/baselines`) | 892.1056 um^2, 4297 ps; 200.986 GE, depth 21 (fixed size). `case` table 3445.8048, 2288; 786.894, 11. Depth-16 circuit 952.1632, 3670; 216.322, 18 |
| `clmul` | N-bit carry-less multiplier (product of polynomials over GF(2)), `p = a (x) b` on `2N-1` bits; bans run-time `+ - *` | the N x N AND/XOR array (`mul_n`'s shape without carries), validated (Verilator, exhaustive to `N = 8`; the Lean spec equals the oracle on every pair to `N = 7`), scored and **proved** for every `N` (`sv_structure`/`sv_equations`/`sv_cover`/`sv_bridge`, 206 code lines, `solution` stage 7.7 s); schoolbook and Karatsuba baselines by simulation (`tests/clmul/baselines`); 18 real-world styles under `tests/clmul/attacks` (`tasks/clmul/README.md`, "How people write clmul") | 3429.5392 um^2, 1114 ps; 772.267 GE, depth 6 at `N = 16`; Karatsuba (4-bit base, generated) 2756.4, 1807; 621.959, 8 |
| `matmul` | **Preview, not ranked yet: the statement is being revised to cover the outputs on the wire and unknown values at reset; submissions are not ranked until then.** N x N signed matrix multiplication, clocked, `C = A * B` wrapping at `AccW` bits behind a start/done handshake (`tasks/matmul/README.md`) | N x N parallel multiply-accumulate units and a step counter, latency N, proved for every `N, W, AccW` | not ranked (a preview) |
| `sorter` | **Preview, not ranked yet: the statement is being revised to cover the outputs on the wire and unknown values at reset; submissions are not ranked until then.** A streaming sorter of N unsigned W-bit values, clocked, one value per cycle in and out (`tasks/sorter/README.md`) | an insertion-cell array adapted from andrewpeck/cell-sort (MIT), latency 2N, proved for every `N, W` | not ranked (a preview) |
