# svGolf

**Hardware golf, with proofs.** Write a circuit in SystemVerilog, prove it in
Lean with [Proglib](https://github.com/thomasnormal/proglib) for every size the
task allows, and compete on area × time.

svGolf is a [zk.golf](https://zk.golf)-style competition for SystemVerilog
hardware. For each task you:

1. write a circuit in SystemVerilog;
2. prove in Lean that it meets the task's **trusted statement**, under the
   ls-sv semantics of [Proglib](https://github.com/thomasnormal/proglib/tree/178529f15e736ea2aff7188cf9051ed6810dec9d)
   (formerly lean-surfaces; [The statement](#the-statement) says which part of it);
3. get scored by a pinned synthesis flow, weighed on the sky130 standard
   cells (flow A0'). The one ranked number is **area x time**: the cell area
   in um^2 times the critical-path delay (on a clocked task, cycles x the
   clock period), in um2*ns, lower is better (decided 2026-11-05; [Scoring](#scoring)).
   Par, the record and "under par" use it; to beat par is to be accepted
   with a smaller area x time than the task's par design: one design per
   task, the simplest algorithm, proved by the maintainers (`leaderboard/par.json`;
   every other design is an entry, the maintainers' own too). The
   Pareto frontier of area and time, area in NAND2 gate equivalents, depth
   in gates and the other flows are exploration columns. Every number can
   be reproduced bit for bit ("Reproduce a score" under [Scoring](#scoring)).

The site, <https://thomasnormal.github.io/svgolf/>, shows the tasks, the board and every record with its
proof. To play, clone the repository:

```bash
git clone https://github.com/thomasnormal/svgolf
```

**Platforms.** macOS and Linux; Windows is not supported. The ranked numbers are rated on one build, the
Homebrew Yosys 0.53 for macOS arm64 ("The build ratings use", under [Scoring](#scoring)). On Linux the sandbox
is not yet checked end to end ([Sandbox](#sandbox)). **Tools:** elan (it installs Lean), Yosys 0.53 with
`yosys-abc`, Verilator 5, a C++ compiler, `make` and Python 3.12: Step 0 of the [Quick start](#quick-start).

| where | what |
|---|---|
| [the site](https://thomasnormal.github.io/svgolf/) | the tasks, the board, the rules, every record and its proof |
| `tasks/<name>/README.md` | one task: its statement in words, what is banned, par (`_example` is the tutorial, `add` the first real task) |
| [PROVING.md](PROVING.md) | how to write the proof: the loop, the tactics, worked references |
| [CONTRIBUTING.md](CONTRIBUTING.md) | the route through the rules, adding a construct to ls-sv, the regression |
| [REFUSALS.md](REFUSALS.md) | every refusal the checker makes, why, what to write instead, and which are meant to be lifted later (generated from Proglib's refusal register `docs/sv-refusals.json` by its `tools/gen_sv_refusals.py`) |

**Read these, in this order:** a task's `tasks/<name>/README.md` (`tasks/_example/` is the tutorial,
`tasks/add/` the first real task: the statement, what is banned, par); [Quick start](#quick-start)
(Step 0, the inner loop, the three commands); [Submitting](#submitting) (the two files and the Lean
contract); [PROVING.md](PROVING.md) sections 0 to 2 (the loop, the shape of a proof, the adder; for a
clocked task, `matmul`, `sorter` or `arbiter`: section 0, then section 19, or 20 for the arbiter); then
the rest of this file as you need it.

A proof that a circuit is correct is worth nothing if the statement can be
met without computing anything, so the statements, the checker and the
scoring are all built to be hard to game. `SvGolf/Task.lean` explains the
statement; "Checker v0 limits" below says what is not covered yet.

## Quick start

**Step 0, once per machine.** Install [elan](https://github.com/leanprover/elan) (it installs the Lean
toolchain that `lean-toolchain` pins, `leanprover/lean4:v4.33.0-rc1`, on first use), Yosys 0.53 with its
`yosys-abc` (the pinned flow; the ranked numbers are made with one build of it, "The build ratings use"),
Verilator 5, a C++ compiler and `make` (the post-synthesis stage compiles
Verilator's model of the netlist, and without them `check.py` stops with the infrastructure error
"postsynth: `c++` is not on PATH ...", or names the compiler `$CXX` sets; "Checking" says which compiler) and
Python 3.12. Then:

```bash
python3.12 -m pip install -r requirements.txt   # pyslang 11.0.0, the extractor's SystemVerilog frontend
lake build                                      # the trusted Lean and the checker's evaluator ("Building")
python3.12 score/ppa.py --fetch-liberty         # the pinned sky130 liberty (12.8 MB, checked by its hash)
```

Where the system marks its Python externally managed (`pip` refuses to install), make a virtual environment
first and run every command inside it: `python3.12 -m venv .venv && . .venv/bin/activate` (`.venv/` is
git-ignored).

In the first `lake build` of a clone of the public repository, Lake clones Proglib and its packages from
github.com (it needs network access there) and builds the `LeanModels.Sv` modules svGolf uses; Mathlib is
cloned, never built. Measured from a fresh clone: about 6 minutes, and about 1 GB of clones on disk, on an
Apple M2 Pro laptop with 16 GB and the toolchain already installed (2026-11-05); on a slower Linux machine
with Lean on 2 threads (2026-11-10), 484 s for elan's first toolchain download, then 1215 s for `lake build`
(about 8 minutes of it cloning) at a peak resident memory of 3.75 GB. Before it, `check.py` stops with an
infrastructure error that names the missing extractor.

A proof that imports Mathlib needs Mathlib's build, which `lake build` does not make (svGolf and the
references import no Mathlib): in a clone of the public repository, `lake exe cache get` fetches it (109 s
on that machine; where the open-file limit is 1024, raise it first: `ulimit -n 65536`; at 1024 it failed
with "No file descriptors available (os error 24)"). Without it, `check.py` stops such a proof with an
infrastructure error: "the package(s) ['Mathlib'] are on no entry of the Lean search path" ("Mathlib in
submissions").

**The three commands.** A submission is `solution.sv` and `Solution.lean` (any names and paths;
"Submitting" says what the Lean file must contain):

```bash
# in a clone of this repository, from its root
# 1. is the design admissible, and is it right on the task's oracle? (15 s, no proof needed, never accepts;
#    exits 0 when every stage passed, and its last line on stderr is the ranked area x time with par)
python3.12 check.py tasks/add solution.sv --unproved
# 2. prove it: PROVING.md (the loop, the tactics, two worked references) -- then the real check (about a minute;
#    its post-synthesis stage runs LIGHT by default, a few seconds: local feedback, see "Checking")
python3.12 check.py tasks/add solution.sv Solution.lean
# 3. record it (re-runs the check IN FULL MODE, in the OS sandbox: the leaderboard's artifacts are never light).
#    It writes leaderboard/data/add/, the directory a pull request adds; add --data-dir DIR for a private trial
python3.12 leaderboard/leaderboard.py add --task add --player YOUR_HANDLE --assisted-by "TOOL OR MODEL" \
    --sv solution.sv --lean Solution.lean
```

**After step 3.** To hand in a record, `leaderboard.py submit` opens a pull request that adds its three
files; a check on the pull request verifies every record and runs the full check on the added ones, and a
maintainer re-makes the ranked number on the rating build when the pull request is merged. For the adder:
`python3.12 leaderboard/leaderboard.py submit --task add --record HASH`, HASH as step 3 prints it; `--dry-run`
prints the steps first. It uses your git and the GitHub command-line tool `gh` (without `gh` it prints the
steps for doing by hand).

**The golfing inner loop** needs no Lean and takes about 2 seconds:

```bash
python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped          # the ranked area and delay
python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped --path   # ... and the critical path, net by net
```

It runs the source gate and the pinned flow and prints `ppa.area_um2_sky130` and `ppa.delay_ps_sky130`, whose
product is the ranked number (`--no-mapped` leaves out the extra flow A1'); its last line on stderr says them in one
line, `ppa (sky130 A0'): area 460.4416 um^2, delay 2611 ps; area x delay = 1202.21 um2*ns` for the adder's par. A
clocked task's run (`--seq`) gives the period instead, and with `--latency n` the ranked score, area x n cycles x
period. It does not check the banlist,
the 4-state rules, whether ls-sv can read the design, the post-synthesis simulation or the task's function,
and it needs no proof: run `--unproved` before you prove.

Start from a task's own `tasks/<name>/README.md`: it states the task, what is banned, and links the
reference design and its proof. If your Lean wrapper is not the default (a shared machine), set
`SVGOLF_LEAN_WRAP` once; `check.py` and `leaderboard.py` both read it, and `SVGOLF_LEAN_WRAP_ONCE=1`
makes `check.py` take the wrapper once for the whole run instead of once per `lake`/`lean` call.

## Rules

**Universal task correctness** (decided 2026-11-05). A candidate implementation is
valid if, for every admissible initial state, external input sequence, and
nondeterministic choice permitted by its execution semantics, the resulting
observable behaviour satisfies the task specification.

* The specification may permit several outputs or execution traces, including
  approximate results.
* Nondeterministic choices need not produce identical outcomes; each must only
  produce a permitted one.
* The proof must account for every admissible choice (an unknown value's 0/1
  resolution, the order of simultaneous events, how independent clocks
  interleave, how a synchronizer's metastable bit resolves) and preserve the
  correlations and timing constraints the semantics fixes (one power-up value
  per register, inputs stable around their own clock edge).
* A failed or incomplete proof does not establish validity: a timeout, a
  refusal or an unsupported construct is a rejection, never a pass.

So whatever value or order the synthesizer, the silicon or the environment
picks is one of the cases already proved, and the real behaviour refines the
proof.

* **Proofs are symbolic and parametric.** When a task is n-bit, the
  statement covers every `N` in the task's range, and so must the proof:
  induction on bit indices, `BitVec` algebra, the ls-sv proof layers.
  `bv_decide` is NOT supported for now: it runs an external SAT solver, which
  the checker declines to sandbox (decided 2026-11-01; "`bv_decide`" below).
  Use `decide +kernel`, `omega`, `simp` or a symbolic argument. `native_decide`
  is banned. `sorry` and `admit` never pass (the axiom check rejects `sorryAx`).
* **Proof time limit.** 300 s of CPU time of the Lean process for every task
  (decided 2026-11-06), with a wall-clock backstop of 5 times it, 1500 s. It is
  300 because CPU seconds count every elaboration thread: the limit was 120
  wall-clock seconds, and an honest proof uses about 2.3 CPU seconds per
  wall-clock second ("Proof effort").
* **Axioms.** Only the task's `allowed_axioms` (normally `propext`,
  `Classical.choice`, `Quot.sound`). No new axioms, no `extern` or
  `implemented_by`: an `axiom` of your own, the axioms `native_decide` and
  `bv_decide` generate, and `Lean.ofReduceBool` are all rejected.
* **Banned operators, per task.** A task bans the run-time operator that IS
  the task, and anything Yosys turns into the same cell: the adder and
  multiplier tasks ban `+ - * / % **` (Yosys's `alumacc` merges `+` chains
  into the same `$macc` cell as `*`); the divider bans `/ %`. **Every task
  bans run-time `/ % **`** (since 2026-11-06, under the 2026-11-05 ruling
  below that svGolf disallows a construct where Yosys departs from the
  standard): a zero divisor, or `0 ** -1`, makes an x from KNOWN operands,
  which ls-sv carries into a decision (the else branch of `if (x)`) while
  Yosys builds a defined value there, and with a 2-state destination IEEE
  itself defines the value (0) and Yosys builds another
  (`tests/clmul/attacks/div_zero_x.sv`: the right product everywhere in
  ls-sv, p[0] flipped in the netlist on one input pair in 2^32, which the
  post-synthesis vectors miss); `score/banlist.py` adds them to every task's
  list (`ALWAYS_BANNED`) and says why in its message. A task that
  bans `+` or `-` also bans run-time ordering comparisons `< <= > >=`
  (decided 2026-11-05): Yosys builds each as its own adder, an `$alu`, so
  the banlist rejects every `$alu` that `alumacc` builds; equality and
  comparisons over parameters stay allowed. Constant
  arithmetic stays allowed: parameter expressions, genvar loops (the step
  may be `i++`, `i--`, `i = i + 1`, `i += 1`, `i = 1 + i`, `i = i - 1` or `i -= 1`;
  any other step such as `i += 2` or `i = i + K` is refused at the `design`
  stage; `i = i + 1` reaches the `sv_comb` tactics as `i++`, measured:
  PROVING.md, section 4), index arithmetic over parameters and genvars (`a[i+1]`),
  procedural `for` counters (`k++`), constant functions, and the size queries
  `$bits(q)` and `$size(q)` of a signal, which do not read it (since 2026-11-07:
  `$bits(q) / $bits(q)` is constant).
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
  on the maintainers' machines, and the tools it runs read more than the text:
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
  2026-10-31); the rest of the family (writes, programs, the environment, dumps, DPI) is refused by the
  refusal register's rows, which extend that ruling.
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
  of an x or z the checker knows is therefore refused statically, at the
  parameter points it probes (the scoring point and the task's probe and
  backstop points; what that leaves open is in "Checker v0 limits", "The x
  rules are decided at the probed points"):
  * the source gate refuses every `x`, `z` or `?` digit in a literal
    (`1'bz`, `4'b10x0`, `'x`, `'z`), except the wildcard digits of a `casez`
    item (`z`, `?`) and of a `casex` item (`x`, `z`, `?`), where both tools
    agree they match anything. No `'x` don't-care assignments either;
  * the `fourstate` stage (`score/fourstate.py`, at every point the checker
    probes: the scoring point, then the task's probe and backstop points,
    since 2026-11-06; before, at the scoring point only, while the statement
    covers every `N` in range: the audit's `tests/_example/attacks/
    undriven_offpoint.sv` is undriven only away from `N = 16`)
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
  Three x sources have no rule here because nothing can reach them today:
  run-time `/`, `%` and `**` (x on a zero divisor or a negative exponent) are
  banned by every task, through the banlist, since 2026-11-06 (before, `clmul`,
  `aes_sbox`, `matmul` and `sorter` admitted them, and no rule refused the x a
  zero divisor makes: the universal-correctness audit); a
  function-local variable or return value read before it is assigned
  needs user function calls, which ls-sv does not have (such a design loads
  with an Unsupported node and is rejected at the `design` stage:
  `tests/_example/attacks/fn_uninit.sv`); and a
  latch that is never loaded (`always_latch`, or `always @*` assigning a
  variable on some paths only: x in IEEE, 0 in Yosys) is refused by rule (e)
  of `score/fourstate.py` (`proc` inferred a latch; `latch_never.sv`,
  `latch_star.sv`, rejected at the `fourstate` stage). A task that admits the first, or
  an ls-sv PR that adds a latch construct, needs its own rule first.
* **A reactive task (`kind` `react-family`: the `arbiter`) is clocked**, and these
  rules come with it (the statement `ReactTask`, `SvGolf/TaskReact.lean`; the
  task's README gives the reasons):
  * one clock, the task's `clock`, on its rising edge, and a synchronous reset,
    the task's `reset` port. The source gate refuses an asynchronous reset, a
    `negedge` clock and an `iff` guard; past it, the pinned loader refuses the
    last two itself and keeps an asynchronous reset (as `alwaysFFR`), which the
    statement's clock discipline (`ClockedBy clk none`) refuses (a comment in
    `SvGolf/TaskReact.lean` still says the loader drops the three; it is out of
    date: a comment, not part of the statement);
  * Moore outputs (`MooreOut`): no combinational path from an input port, the
    reset included, to an output port, so register every output. What a
    snapshot shows is on the wire for the whole next clock period;
  * every power-up state: the claims hold from every 0/1 power-up value of every
    register and variable, 2-state ones included, the first reset edge
    included, so a register that is never reset may only hold a value that does
    not matter. A register that is never loaded (`u <= u`), which the pinned
    flow removes while reads of it remain, is refused at the `score` stage;
  * no construct that can create an `x` from known operands (`XSafe`): the
    `clocked_rules` stage checks it before the proof (`check/clocked_rules.py`);
  * no latency: one decision per cycle, and a `-- svgolf-latency:` line is
    refused. The time is the register-to-register period of the clocked flow
    (`score/svgolf_seq.ys`, `score/ppa.py --seq`), the area includes the
    flip-flops ("Scoring");
  * the post-synthesis check is reactive: at each of the task's post-synthesis
    points the scored netlist runs from power-up states through the task
    oracle's segments, each a reset entry and then entries with `rst` = 0, the
    last one 70000 entries long without a reset. It rejects unless the netlist
    equals ls-sv from the all-zeros start, every grant meets the guarantee on
    the netlist at every seed, and the outputs sampled before each rising edge
    equal the previous snapshot (the Moore sample).
* **A clocked task with a latency (`kind` `tx-family`: `matmul`; `stream-family`:
  the `sorter`)** has the reactive task's clock rules and these (the statements
  `TxTask.StatementV2` and `StreamTask.StatementV2`, the second clocked statement, in
  `SvGolf/TaskSeq.lean`, final since 2026-11-08 and amended 2026-11-09 before
  any record of these tasks was published; the tasks' READMEs give the
  handshakes; some comments of the trusted text predate the amendment and are
  out of date: `SvGolf/TaskSeq.lean` twice calls the earlier statement by its old name
  (txtask-v1), unchanged but for the distinct names, and it and both
  tasks' `Spec.lean` call the v2 clock discipline v1's, which is now `ClockedBy
  clk none`; comments, not part of the statement):
  * the latency line: `Solution.lean` declares its latency in exactly one header
    line `-- svgolf-latency: n` (a decimal number of cycles, 1 to 999999999) and
    defines `Submission.lat`, one `Nat` per parameter; the goal is the task's
    `Statement design.sem lat ∧ lat p0 = n` at the scoring point `p0`. At other
    points `lat` need only be a bound the proof establishes, but at each point
    of the post-synthesis check the kernel must reduce it to a number (1 to
    999999999), which the check uses there (decided 2026-11-08; `check.py` and
    the tests call this rule F8; without a proof,
    `check.py --unproved --latency n --latency-at POINT:m`);
  * the time is `n` x the register-to-register period of the clocked flow
    (`score/svgolf_seq.ys`, `score/ppa.py --seq`), the area includes the
    flip-flops, and the ranked number is area x (cycles x period) ("Scoring");
    one submission declares one latency;
  * one clock on its rising edge and a synchronous reset `rst`; no asynchronous
    process (the source gate refuses an asynchronous reset, a `negedge` clock,
    an `iff` guard, `initial`, initializers on state and `always_latch`; the
    statement itself refuses an asynchronous reset, `ClockedBy clk none`, as
    for the reactive kind, decided 2026-11-09);
  * Moore outputs (rule 1, `MooreOutDep`): no combinational path from an input
    port, `rst` included, to an output port, so register every output (decided
    2026-11-09: no input is exempt). This kind has no early Moore check; the
    proof refuses a Mealy output;
  * every power-up state (rule 2) and no x-creating construct (rule 3, `XSafe`,
    checked before the proof by the `clocked_rules` stage), as for the reactive
    kind; a never-loaded register is refused at the `score` stage;
  * the post-synthesis check runs transactions: at each of the task's
    post-synthesis points, per seed, the scored netlist starts from a random
    power-up state, takes one reset cycle and then the task oracle's
    transactions, and it rejects unless every transaction finishes within that
    point's latency, the task's oracle (`good`) accepts every payload, and,
    where the netlist and ls-sv start from the same state (seed 0, all zeros),
    the netlist equals ls-sv on the flag (`done`, `out_valid`) at every cycle and
    on the payload where it is claimed; from different power-up states ls-sv's
    own run must meet the statement's claims (the tasks' reviews,
    fixed 2026-11-08), so a correct
    design whose flag timing within the latency depends on an unreset register
    is not refused;
  * the loader expands one generate loop to at most `(s + 2)² + 64` iterations
    at a point, `s` the sum of the parameter values (`PDesign.surfaceFuel`):
    nest one loop per index rather than one flat loop over a product of the
    parameters, or `design.sem` is the error design at the points beyond it.
* **No other restrictions.** Any SystemVerilog that passes these rules and
  that ls-sv and Yosys accept is fair game. Where ls-sv and Yosys disagree on
  what the same text means, that is a bug report we want, not an exploit.
* **IEEE 1800 is the final arbiter for defined values** (decided 2026-11-05).
  ls-sv follows the standard, never a tool. Where the pinned flow (Yosys and
  ABC) reads a construct differently from the standard, ls-sv does not change:
  svGolf disallows that construct in submissions instead (the source gate, the
  banlist or the `fourstate` rules, as with the latch and x/z cases above).
  An unknown is not a third value: an x stands for a bit whose 0/1 value is
  not known (IEEE 1800 §6.3.1), so a proof must hold for every resolution of
  it, as formal tools treat x; a simulator's resolution (the else branch of
  `if (x)`) is not the semantics. That is the rule; the trusted statement
  does not state it yet. It is stated over ls-sv's `run2`, which resolves an
  x the way a simulator does (`if (x)` takes the else branch, an x `case`
  subject matches nothing), so a design in which an x reaches a decision can
  satisfy the statement (`tests/_example/attacks/undriven_mux.sv` and
  `oob_rare.sv` do). Until ls-sv's every-resolution semantics lands (planned,
  not built), validity therefore rests also on the Python x-source rules (the
  source gate, the banlist and the `fourstate` stage), which are part of the
  trusted base, not only defence in depth.
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
    ls-sv's outputs, an unknown-valued constant that a gate, a flip-flop or
    an output reads (Yosys's own reading of the netlist decides; a constant
    nothing reads, which Yosys leaves for example where it removed an unused
    register bit, is accepted and listed in the check's result), a net bit
    with more than one driver of which one is an unknown-valued constant,
    read or not, and a netlist that defines a box module (`(* blackbox *)`,
    `whitebox`) or has a cell that is neither a gate of Yosys's cell
    library nor a module the netlist defines (decided 2026-11-12: where
    Yosys's view of the netlist could hide an unknown, the rule fails safe;
    its scope is the netlist's unknown constants, so two known drivers of
    one bit are left to Verilator's lint and to the comparison itself), a
    netlist Verilator will not lint, build or run cleanly, a harness that prints the
    wrong number of rows, the two schedules disagreeing, or different ports
    all reject;
  * **Verilator is a 2-state simulator** (decided 2026-10-29: svGolf simulates with
    Verilator, not Icarus), so the netlist side has no `x` or `z`, and this
    stage cannot see an unknown the netlist computes. It does not need to:
    Yosys's gate cells (`simcells.v`) are total Boolean functions, so an
    unknown can only come from an unknown-valued constant in the netlist
    (`1'hx`; where a gate pin, a flip-flop or an output reads one, the
    netlist is rejected, on every vector of a combinational task, the report
    showing what a 2-state model reads, and the message naming the wires
    that hold it and their readers, and, from a second Yosys run made only
    then that keeps the design's names, the bits in your own words; one nothing reads is in the fan-in of no
    observed output, so every value it could take gives the same rows) or from an undriven or
    unconnected net or pin (Verilator's lint runs with `-Wall` and every
    warning fatal except `DECLFILENAME`, `UNUSEDSIGNAL` and `UNOPTFLAT`:
    UNDRIVEN, PINMISSING, PINCONNECTEMPTY, MULTIDRIVEN and the WIDTH family
    reject). A combinational loop in the netlist is refused bit by bit before
    Verilator runs (2026-11-13): Verilator's own UNOPTFLAT looks at whole
    vectors, so it also called circular the assigns by which Yosys writes
    flip-flops it merged, one bit of a vector from another
    (`assign { q[2], q[0] } = { q[3], q[1] };`), and refused correct designs
    (two equal registers, a narrow result sign-extended into a wider
    register); with every real loop refused first, that false loop is
    simulated, which Verilator does correctly. The x/z defences stay where they are: the source gate, the
    `fourstate` stage, and ls-sv's own 4-state outputs on the other side of
    the comparison. What is lost against the 4-state Icarus run it replaced is
    only a witness for an unknown that the netlist invents from known inputs
    and driven nets, and Yosys gate cells have none to find;
  * a rejection is written as a bug report: per failing vector the inputs,
    ls-sv's outputs, the netlist's, and Verilator's reading of the source
    (also 2-state) as a third opinion, with who agrees with whom. File it:
    either ls-sv or Yosys is wrong about your design;
  * **light and full**. The default `light` mode is a safety net for
    local feedback: it runs a deterministic SUBSET of the full vectors (a
    light rejection is always a full rejection) in seconds instead of
    minutes. Competition and verification runs, `leaderboard.py add` /
    `verify` and `tests/run.py` use `full`, which is the whole budget
    described here. Official artifacts are never light.

  It is sampling, not proof: a difference confined to a rare input region
  that no constant comparison selects slips through (see "Checker v0
  limits"). That is why the known disagreements are refused statically
  before any proof is tried (the source gate's `unique`/`priority` and
  x/z-literal refusals, which are lexical and hold at every `N`; the banlist's
  run-time `/ % **`; the 4-state rules, at the points the checker probes);
  the post-synthesis check is
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
  afterwards). A clocked task's check (F5, decided 2026-11-07) runs 8 seeds
  per point and derives EVERYTHING random in a seed's run from the salt and
  records it: the stimulus or transaction source, Verilator's `randSeed` (the
  netlist's random power-up) and ls-sv's power-up `seed:<k>`.
* **Scoring** is `score/score.py` with the pinned two-stage flow
  (`score/canon.ys`, then `score/svgolf.ys` in a fresh Yosys process) and the
  pinned table `score/ge.json`, at the task's scoring point (e.g. `N = 16`),
  and `score/ppa.py` weighs that netlist for the ranked numbers ("Scoring").
  The score is a deterministic function of the file as submitted: names,
  comments, blank lines, whitespace and the file name never change it (stage
  1 erases them), while the order of an operator's operands, how a chain of
  gates is grouped, gate forms and the order of independent statements do,
  always the same way (measured 2026-11-05: reordering the 113 assigns of
  `aes_sbox`'s reference moved its delay by up to 17.7%, and moving one
  generate block of a proved multiplier ahead of another moved its area 12.6%
  and its delay 41%), because ABC's choices follow the order of the gates it
  reads. None of these changes what the circuit computes, which IEEE 1800
  decides (above); they change only the netlist the pinned flow builds.
  Trying them is golf (decided 2026-10-31 and 2026-11-05): a golfer searches
  gate forms and statement orders with the pinned flow before submitting. Not every structural choice survives synthesis, though:
  ABC re-derives the logic, and some RTL carry-structure choices (a final
  adder that steps two bits at a time instead of one, in an early trial) score
  identically to the milli-GE. Score a block standalone with `score/score.py`
  before building a proof around it. See "Scoring".

## Layout

```
svgolf/
  lakefile.toml, lean-toolchain     the svGolf Lake project (requires Proglib)
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
  score/fourstate.py                the 4-state rules (no x or z value can arise at the probed points)
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
                                    frontier, boards, verification, `submit` (leaderboard/README.md)
  leaderboard/pr_check.py           the check of a pull request that adds records (the `records`
                                    workflow runs it); .github/pull_request_template.md its form
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
  PLAN.md, PLAN2.md, PLAN4.md       the maintainers' working plans (history, not the rules)
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
  REVIEW.md        optional: the maintainers' review of the trusted statement (before a task is
                   listed): the statement in words, its sources, the
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
  Proglib's `LeanModels/Sv/Lib` (`LeanModels.Sv.Lib`), the rest into the
  task's reference proof)
```

and its tests, which a player does not need:

```
tests/<name>/
  negative/        designs that must fail: *.sv, README.md, and Refute.lean (module
                   `tests.<name>.negative.Refute`, in the `tests` library:
                   kernel-checked proofs that they do NOT satisfy the statement,
                   loading each design with `load_sv`)
  baselines/       proved designs, each <stem>.sv with its proof <stem>.lean:
                   one with a banned operator (checked with check.py
                   --lift-banlist) is a comparison line on the site, never an
                   entry; one without is an entry, shown once it is recorded
                   under a player's handle
  unproved/        test material without a proof (one-width generated
                   netlists, a design ls-sv does not run yet): simulated by
                   tests/run.py, shown nowhere on the site
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
README, gate mix included, which baselines the banlist rejects, and each
baseline's proof file) are in `tests/expected.json`, which `tests/run.py`
checks.

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
| `leaderboard` | optional, `{depth_budget}`: a depth budget for the leaderboard only (positive integer, `null` or absent = none). The board then also ranks the best area x time under it and flags the entries over it; nothing is rejected (that is `scoring.depth_budget`). See "Leaderboard" |
| `backstop_points` | parameter points for the Yosys banlist backstop (default: the scoring point) |
| `allowed_axioms`, `allow_bv_decide` | the axiom policy: the axioms a proof may use, and `bv_decide`'s switch. `bv_decide` is not supported (see "`bv_decide`"): absent or `false` forbids it, `true` is an infrastructure error ("the checker does not support external SAT solvers"), and so is a non-boolean. The shipped tasks say `false` |
| `postsynth` | the post-synthesis check's budget (optional; defaults in brackets): `random` [1000] seeded random vectors, `corners` [{}] `{input: [values]}` whose cartesian product is checked (an input without values: 0 and all-1), `harvest_pairs` [2000] compatible pairs of harvested comparison constants, `light_vectors` [256] the most vectors the LIGHT mode runs (set from the reference's ls-sv cost per vector: `mul` has 40), `fuel` [100000] `run2`'s fuel per run, `time_limit_s` [900] a fail-closed cap on the ls-sv evaluation. Counts, not a time budget, decide what is checked, so a result does not depend on the machine |
| `oracle` | optional, `"oracle.py"`: a Python ORACLE of the task's function in the task directory, `def oracle(params: dict, inputs: dict) -> dict` (`params`: the point the `postsynth` stage evaluates at, e.g. `{"N": 16}`, `{}` for a fixed-size task; `inputs`: input port name to int; result: output port name to int, already masked to the output's width). With one, the `postsynth` stage also compares ls-sv's outputs on every vector it already uses with the oracle's and reports `functional` and, on a mismatch, one `warnings` line (see "Checking"); it never changes a verdict. The oracle is a contestant convenience and NOT part of the trusted statement (`Spec.lean`, `SvGolf/Task.lean` and `fdivp`'s `IEEE754.lean` are): every task has one today (`fdivp`'s is exact `Fraction` arithmetic for every format, written separately from the spec's own validation oracle `spec_validate/oracle.py`); a task without one is simply not checked |
| `time_limit_s` | the limit for compiling the proof, in CPU seconds of the Lean process (300 s for every task, the rule in "Proof effort"; `score/time_limits.py` checks it); the compile also has a wall-clock backstop of 5 times it |
| `verify_time_limit_s` | the limit for each of the comparator and `leanchecker`, in CPU seconds of the Lean process (default 900; since 2026-11-06, before then wall-clock seconds), with a wall-clock backstop of 5 times it, as for `time_limit_s` |
| `references` | `[{sv, lean, note?}]`: the proved reference solutions, each a pair `reference/<stem>.sv` + `reference/<stem>.lean` that `check.py` accepts (`tests/run.py` checks it, and the score). One of them is par's design (`leaderboard/par.json`, decided 2026-11-12: one design per task); the others are entries, shown once they are recorded under a player's handle. Several pairs may be listed; the first is the one `tests/run.py` submits the negative designs with. `add` and `mul` list two: `<stem>` (proved with the sv_comb tactics) and `<stem>_byhand` (the same design, a byte-identical `.sv`, proved with no tactic: the measured baseline of the proof effort); `tests/expected.json` marks the second `same_design_as` the first, and `tests/run.py` checks the bytes |
| `draft_reference` | draft tasks only, `{sv, lean, note?}`: the goalpost design `reference/<stem>.sv` and its partial, unproved Lean file `reference/<stem>.partial.lean` |

Keys starting with `_` are comments. Add a task by creating `tasks/<name>/`,
its tests under `tests/<name>/` and its entry in `tests/expected.json`,
adding `import tasks.<name>.Spec` to `tasks.lean` (and
`import tests.<name>.negative.Refute` to `tests.lean`), and running
`tests/run.py`, which also checks this layout.

## The statement

The statements are written over the sv-0.2 tier of Proglib's ls-sv semantics: `load_design_sv2`,
`run2`, the `⊨₂` judgment and `Terminates2`.

`SvGolf/Task.lean` (read its docstring) defines a combinational task as an
interface (input and output ports with widths that are functions of `N`) and a
function on `BitVec`s, and the statement `CombTask.Statement t sem` as: for
every `N` in range (every family task bounds it so that every width and `int`
localparam it implies stays below `2^31`, the values an `int` holds: `N < 2^31`
in `_example` and `add`, `N < 2^30` in `mul` and `clmul`, whose output is `2N`
bits wide, `W + P + 1 < 2^31` in `fdivp`; decided 2026-11-06),

1. the design's input ports and output ports are EXACTLY the task's (names,
   order and widths);
2. `Unclocked`, `LoopFree` and `Terminates2`: no process is clocked (no
   `always_ff`, no `always @(posedge …)`: ls-sv runs those once per cycle
   whatever their clock holds, so a register on a clock nothing drives would
   hold the right value in ls-sv and `x` in every simulator, and score 0 GE);
   there is no combinational loop and no latch (the design lowers to
   continuous assigns that can be ranked, each reading only what lower-ranked
   ones write: ls-sv starts every signal at `x` and settles, so it would read
   a loop at one state, while a circuit powers up in any state the loop can
   hold); and every run completes, under every schedule and stimulus;
3. in every completed run, every cycle whose stimulus entry drives every
   input with a known value ends with the outputs holding exactly the
   function's value.

The docstring goes through the ways a weaker statement could be met
vacuously (a design that never settles, hypotheses that never hold, stimulus
width and name conventions, extra or missing ports, `x` values, combinational
loops, history) and
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
Proglib's own `lakefile.toml` does for its envelopes. `lake build SvGolf
tasks svgolf-eval` (what the checker builds) needs no Python.

**Three refutations do not build at the pinned library yet.** `tests/add`, `tests/mul` and
`tests/clmul` each have a `negative/Refute.lean` that loads an `only_n16.sv`, and
the pinned ls-sv's loader refuses that design (`PDesign.int32Agrees`: at the
defaults an INT-class constant expression leaves the 32-bit range), so the three
modules do not build at the pin. `tests.lean` does not import them, so the default
`lake build` stays green. They are unchanged: `tests/run.py`'s `negatives` step
builds each one alone (`lake build tests.add.negative.Refute`) and checks that it
fails with that refusal (`PENDING_REFUTES`); one that builds fails the step until
it is imported again. Once the pinned library's loader takes their `only_n16.sv`, they go back into `tests.lean`.
The same refusal stops `check.py` on the three `only_n16.sv` at the `design`
stage, before the proof whose failure `tests/expected.json` records for them
(`solution`), so the `negatives` step pins the design-stage refusal for those
three rows until that round (`PENDING_STAGES`), and checks their scores as
before; a row rejected at its `tests/expected.json` stage fails the step until
its entry is dropped.

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

Written inside `namespace Submission`, as every reference does, that is `theorem solution : Goal`.
`Goal` unfolds to the task's statement of your design: `SvGolf.Tasks.Add.Statement Submission.design.sem`
for `add` (`task.json`'s `statement.constant`). The file names and paths are free (`solution.sv` and
`Solution.lean` throughout these docs); the module name `Submission`, the `import Submission.Design`
header and the theorem are fixed. A skeleton for a combinational task:

```lean
import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombEqTactic   -- sv_structure, sv_equations, sv_cover, sv_bridge
import LeanModels.Sv.CombLib        -- the plain-Lean library: ripple rows, AddView, ...

namespace Submission
open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

theorem solution : Goal := by
  -- your proof: tasks/add/reference/add_n.lean is a complete one

end Submission
```

The clocked tasks have their own skeletons, in their `tasks/<name>/README.md`, "Proving a new design" (the
task page shows the same text). `matmul` and `sorter` declare a latency in one line of its own in
`Solution.lean`, `-- svgolf-latency: n` (not in the `.sv`; the references put it first), define `lat`, one
`Nat` per parameter, and prove `theorem solution : Goal lat`: their generated `Goal` takes the latency,
and `Goal lat` is the task's `Statement design.sem lat ∧ lat p0 = n` at the scoring point `p0` ("Rules").
The `arbiter` has no latency line and proves `theorem solution : Goal`. None of the three uses the `sv_comb` tactics:
[PROVING.md](PROVING.md) section 19 is the route for `matmul` and `sorter`, section 20 for the `arbiter`.

It may import `Init`, `Std`, `Lean`, `LeanModels.Sv.*`, `SvGolf.*`,
and `tasks.*`, and Mathlib with the packages it imports (`Mathlib.*`,
`Batteries.*`, `Aesop.*`, `Qq.*`, `ProofWidgets.*`, `Plausible.*`, `ImportGraph.*`,
`LeanSearchClient.*`; "Mathlib in submissions" below), nothing else (no
`Examples.*`, no `LeanModels.Python.*`, no other submission). It is one
file in v0. `tasks/_example/reference/band_tactics.lean` is a complete example
in 38 code lines: a for-all-`N` proof through `sv_structure`, `sv_interface` and
`sv_equations`, the route of every tactic proof. `tasks/_example/reference/band.lean`
proves the same without tactics: it walks the design's instantiation
symbolically, proves the comb profile and acyclicity, and reduces the rest to
one settled-state lemma.

`LeanModels.Sv.*` includes Proglib's `sv_comb` tactic library
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
DIR`; a later run replaces DIR only when it is empty or `check.py` made it, and refuses any
other directory): the result's `dev_hint` is the command that recompiles your
`Solution.lean` against the staged design, and an editor can work on that
staged file. Before you have a proof, `--unproved --stage-dir DIR` stages the
design and lets you compile probe files (`sv_structure?`, `sv_equations?`)
against it with `LEAN_PATH=DIR/build lake env lean Probe.lean`
([PROVING.md](PROVING.md), section 0).

Before writing a proof, `python3.12 check.py tasks/<name> DESIGN.sv
--unproved` runs every stage that needs no proof (source, extract, banlist,
fourstate, design, score, postsynth) and stops at the pseudo-stage `unproved`, with the
score: is the design admissible, and what does it score? It never accepts (`"accepted": false`); when
every stage passed it exits 0 with `"unproved_ok": true` and its success sentence under `notes`, and a
failed stage exits 1 as in a full check. It also compares the design's outputs on the post-synthesis
vectors with the task's function (`task.json` `oracle`; every task has one) and prints a `functional:`
warning naming the first failing input: advisory, but a wrong design has no proof (PROVING.md, section 0).
`python3.12 check/postsynth.py --task tasks/<name> DESIGN.sv [--point N=32]
[--keep DIR]` runs the post-synthesis check alone, at any point, and keeps
the netlist, the vectors and every simulator's output.

`--lift-banlist` checks a design that uses an operator the task bans (decided 2026-11-12: every design the site
draws is proved, the baselines with a banned operator included). It runs every stage, the proof's included, with the
task's own operator banlist lifted: the banlist stage checks only the run-time `/ % **` every task bans, and
everything else (the statement, the ranges, the axioms, the limits) is the task's. Such a result is never
accepted: a run where every stage passed stops at the pseudo-stage `lifted` with `"lifted_ok": true`, exits 0,
and says "banned operator: proved, not an entry"; it carries `banlist_lifted` (what was lifted and the task
banlist's own verdict), and `leaderboard.py add` refuses it. With `--unproved` it stages the design for the same
fast loop as above.

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
ran arbitrary code with the checker's privileges (the sandbox, "Sandbox" below, now denies
that write; the replay below stays as the layer behind it), so it could write one. The review of the Mathlib support found two
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
extra margin. The limit counts CPU seconds (decided 2026-11-05; "Proof effort"), so the host's
load does not push a proof over it, but the wall-clock BACKSTOP (5 times the limit, 1500 s) does
see it, and a Mathlib import makes the wall clock more sensitive to the load than a core-Lean
file: measured by the review round, the `add_n` proof with `Mathlib.Tactic` took 8.9 s on a quiet
machine and 82 to 94 s of wall clock (23.7 s of CPU) while other jobs had the machine swapping,
against 10.6 and 13.2 s for the unchanged reference at the same time. That worst ratio of wall
clock to CPU time, about 4, is why the backstop is 5 times the limit. So: do not run Mathlib
submissions concurrently with other jobs or under memory pressure (a graded run holds the Lean
slot alone), and budget the memory below.
The comparator and `leanchecker` keep their own limit, `verify_time_limit_s` (900 s each), which counts CPU seconds
too since 2026-11-06, with the same wall-clock backstop of 5 times it (4500 s): as a wall-clock limit it let a
loaded machine reject an honest submission. Their records carry `cpu_seconds`,
`time_limit_counts: "cpu"`, `wall_limit_s` and, when one stopped them, `stopped_by`.

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
netlist, which the board ranks (see "Scoring"; `score` holds the extra GE columns). An accepted result also
says whether the check was COMPLETE (`complete`, and `incomplete` with the reasons when it was not): a run
with `--no-score`, a light post-synthesis check, `--no-trusted-build` or a `--time-limit` other than the
task's left part of the check out, so it establishes nothing a board may rank, and `leaderboard.py add`
refuses it (decided 2026-11-06; "Leaderboard"). The stages, in order:

| stage | what |
|---|---|
| `imports` | the Lean file's imports are on the allowlist (`IMPORT_ALLOW` in `check.py`: `Init`, `Std`, `Lean`, `LeanModels.Sv.*`, which includes the whole sv_comb tactic library, `SvGolf.*`, `tasks.*`, `Submission.Design`, and the eight module roots of Mathlib's package closure, `PACKAGE_ROOTS`; tested by `tests/imports/test_allowlist.py`, which recomputes that closure from the package sources) and include `Submission.Design`; comments are whitespace, so a comment between two imports on one line does not hide the second. For a solution that imports one of the packages, the `trusted` stage ends with a PROBE (`stages.packages`, with the revisions of the package checkouts): the generated `Submission.ImportProbe`, the package imports and nothing else, compiled alone. A module the player named that no package has a source for (a stale name) is rejected here; a package or module missing from the machine (not built, on no search-path entry, a checkout not at the revision the manifest pins) is an infrastructure error (exit 2), never a rejection ("Mathlib in submissions"). Checked AGAIN after the comparator against the imports Lean recorded in the compiled solution: a header the checker read differently from Lean is rejected here |
| `source` | `score/srcgate.py` (see "Rules"): no directives, attributes, pragma comments, `unique`/`priority`, x/z literal digits outside a casez/casex item wildcard, or host access (`$readmemh`, `$fopen`, `$system`, `$value$plusargs`, `$dumpfile`, DPI, ...); every later stage reads the gate's comment-free canonical text, never the submitted file |
| `extract` | the pinned Proglib extractor (`extractors/sv/extract.py --top <top> --probe-points ...`, run through `check/envelope.py`, the one extraction path `load_sv` uses too) writes the envelope and the multi-point cross-check sidecar; a player's `.json` is never read. The probe points always include the scoring point (an extractor without `--probe-points` is an infrastructure error, not a skipped check). The top must have exactly the task's (non-local) parameters, by name, and (since 2026-11-07, every kind) exactly the task's ports at every probe point (at the defaults when the task has none): the input ports in declaration order with their widths are task.json's `ports.inputs`, the output ports its `ports.outputs`, and no port has another direction (`port_problems`: the statement's `Interface` at those points, before any proof; a port the extractor cannot read is left to `design`). |
| `banlist` | `score/banlist.py`: pyslang front check (which also reads the errors of slang's analysis pass, `score/slangdriver.py`) and Yosys backstop |
| `fourstate` | `score/fourstate.py` at every point the checker probes, the scoring point first, then the task's probe and backstop points (see "Rules"; at the scoring point only before 2026-11-06), stopping at the first point that fails: no parameter or constant expression with unknown bits, no constant or run-time select that can leave its declared range, no undriven or conflicting net or logic loop (Yosys `check -assert` after `proc; flatten`), and no error of slang's analysis pass (`score/slangdriver.py`). `stages.fourstate.points` has each point's verdict and time, `failed_point` the one that failed. A point nobody probes is not checked: this narrows, and does not close, the gap to a statement over every `N` ("Checker v0 limits"). Measured (standalone, all points, 2026-11-06, the proved references): `_example` 0.08 s (4 points), `add` 0.22 s (6), `clmul` 1.2 s (8), `fdivp` 0.5 to 1.0 s (8), `aes_sbox` 0.04 s (1), `mul` 3.3 to 15.0 s (7; `mul_tree` the most, 2.6 s of it at the scoring point), `matmul` 0.18 s (4), `sorter` 0.23 s (8); at the scoring point alone they were 0.02 to 2.6 s |
| `trusted` | `lake build SvGolf tasks svgolf-eval` (not timed) |
| `design` | compile the generated `Submission.Design`; ls-sv's loader refusals (the Lean-vs-slang cross-checks, the one-driver rule) reject here. So does a design that LOADS but that ls-sv cannot run: the generated module ends with an `#eval` that tests `Design2.hasUnsupported` of `design.sem` at the scoring point and at the other points of the extractor's cross-check that are not larger than it (the larger ones cost interpreter time, 25 s at `mul_tree`'s `N = 32`, and a design loud only there has no proof of its for-all-`N` statement anyway) and, on the first loud node, rejects with its kind and text and the point (`tests/_example/attacks/func_call.sv`: a correct `a & b` written through a user function; ls-sv has no function calls). No proof, score or leaderboard work happens before it; `stages.design.unsupported_free_points` counts the points checked |
| `solution` | compile `Solution.lean` under the task's time limit, which counts the CPU seconds of the Lean process (user + system, every thread), with a wall-clock backstop of 5 times it for a proof that waits; `stages.solution` has `cpu_seconds` and the wall clock's `seconds` apart, and on a timeout `stopped_by` (`cpu` or `wall`); the rejection names the limit, both readings, and the last declaration the kernel finished and when ("When a proof hits the limit", under "Proof effort") |
| `integrity` | nothing outside the solution's own `.olean` changed during that build: the whole staging tree and the trusted scripts by content (the `svgolf-eval` binary, Yosys's `simcells.v`, `score/ppa.py` with `score/ppa_pins.json`, `score/ppa_mapped.ys` and `score/ppa_mapped_pins.json`, and, since 2026-11-07, the clocked kinds' `score/svgolf_seq.ys`, `score/ge_seq.json` and `check/clocked_rules.py` included), the svGolf and `LeanModels.Sv` builds, the Lean SEARCH PATH (`lake env printenv LEAN_PATH`) for every solution, imports or not: the `.olean*` files of the package builds on it (Mathlib and friends: about 33,000 files, 0.3 s), every entry's top-level names, and the entries that do not exist, recorded as absent (a `Mathlib/` created in `Cli`'s unbuilt build directory, which `lake env` puts ahead of Mathlib's, would shadow it), the `lake-manifest.json` that pins the packages, the Lean toolchain, Yosys, Verilator (its scripts and binaries and its whole `VERILATOR_ROOT`, the runtime every model is compiled against), the C++ compiler, `make` and elan's settings by metadata (size, mtime, ctime, inode); checked again after the postsynth stage, and `check/sandbox/**` is in the fingerprinted trusted base. A tripwire, not a sandbox: it detects after the fact; the sandbox (below) makes the writes it watches for impossible, and the tripwire stays as the layer behind it. |
| `comparator` | `check/Comparator.lean`, which imports the compiled modules WITHOUT running their initializers: the kernel (with `leanchecker`'s limits) accepts `theorem _ : Submission.Goal := Submission.solution`, and the same with the solution's own proof term; every axiom in the solution's dependency closure (walked through kernel values, not the `#print axioms` cache) is allowed; no `extern`/`implemented_by` in `Submission.*`; every `Init`/`Std`/`Lean`/`Lake` module resolves into the toolchain; and the dependency closure of the solution and the goal, minus the toolchain and `Submission.*`, is REPLAYED through the kernel (a package olean with a declaration added without kernel checking is rejected). It reports the imports Lean recorded for each module. Under `verify_time_limit_s`. |
| `leanchecker` | `leanchecker` replays the submission's modules through the kernel (catches declarations added without kernel checking). Under `verify_time_limit_s`. |
| `score` | `score/score.py` at the task's scoring point (the two-stage canonical flow), keeping the scored gate netlist; a depth over the task's budget rejects |
| `postsynth` | `check/postsynth.py` (see "Rules" and "Post-synthesis modes" below): ls-sv (`svgolf-eval`, built in the `trusted` stage) and Verilator on the scored netlist agree on every vector of the run's set (`stages.postsynth.mode`: `light`, the default, a subset; or `full`, the task's whole `postsynth` budget); fail closed; a rejection is a bug report. The netlist model is built once per run, concurrently with ls-sv's evaluation (about 1.5 to 2 s of `verilator` + `make -j 2`, whatever the netlist), and the netlist side then costs about 0.4 microseconds per vector: the stage is ls-sv-bound. Measured standalone (2026-10-29, `check/postsynth.py`, unloaded; Icarus before, Verilator after): `_example` 0.3 s, 2.5 s; `add` (4132 vectors) 1.3 s, 2.0 s; the former 16-bit divider's goalpost (4543 vectors) 26.2 s, 19.9 s; `mul` reference (330 vectors) 46.0 s, 44.0 s. A small design pays the fixed build; a big one gains what Icarus spent per vector (about 1 ms on the former 16-bit divider). The process tree peaks at about 0.5 GB while the model compiles (`SVGOLF_VERILATOR_JOBS=1`: 0.4 GB, 1.4 s slower), 0.2 GB before |
| `ppa` | `score/ppa.py` (see "Scoring" and `score/PPA.md`): the EXTRA sky130 columns of the very netlist the `score` stage kept and `postsynth` verified (no second synthesis): `area_um2_sky130`, `delay_ps_sky130`, `unit_depth`, the cell histogram, and the hashes of its inputs, as the result key `ppa` and the stage `stages.ppa` (`mode`, `seconds`, and `mapped_seconds`); since 2026-11-01 it adds, inside a weighed `ppa`, the sub-object `mapped` (flow A1': a real `abc -liberty` mapping of the canonical RTLIL of the same score run, `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, cells, histogram, cell levels; `{"available": false, "reason": ...}` for a design it cannot map, never a failure of the check). `--ppa auto` (the default) weighs it when the pinned liberty is present and otherwise records `ppa: {"available": false, "reason": ...}` with one line on stderr; `--ppa require` makes an absent or wrong liberty an infrastructure error (exit status 2, before any other work): competitions, `leaderboard.py add`/`verify --full` and `tests/run.py` (where the liberty exists) use it; `--ppa off` adds no key and no stage. A design the pinned flow cannot weigh (a cell outside its table, an undriven net, an x/z bit that a gate or an output reads, ...) carries its reason in `ppa` and never fails the check; the reader understands the dead public-named wires Yosys leaves of techmapped cells, so run-time bit selects, variable shifts, `case` muxes, constant tables and `/` or `%` by a variable all weigh (`score/tests/ppa/idioms.json`). Infrastructure errors (exit status 2, no verdict) are: a liberty that `require` cannot open (absent, unreadable, not the pinned file), in `require` a defect of `ppa.py`, a depth/gate-count disagreement with the `score` stage or a repaired netlist that is not the scored circuit, and, in every mode, a netlist file that is not the one `postsynth` verified (`netlist_sha256` is compared with `stages.postsynth.netlist_sha256`). Since `sky130_a0_v2` (2026-11-04) the stage REJECTS one kind of design: one the repair (buffering only) cannot make electrically legal (`ppa: {"available": false, "illegal": true, "reason": ..., "legality": ...}`, the net named in the rejection; none is known on sky130). Nothing in `ppa` changes `accepted`, `stage` or any other field of a design whose netlist is legal (tested character for character against the checker from before the wiring, times, paths and tool identities aside: `tests/checker/test_ppa_wiring.py`). Measured (2026-10-31): 0.11 to 0.13 s under `auto` (the liberty's 12.8 MB are hashed and scanned for cells, about 0.10 s, then a few thousand gates are timed); under `--ppa require` the liberty is opened before the first stage, so `stages.ppa.seconds` is 0.00 to 0.02 s and the 0.10 s are spent up front; since `sky130_a0_v2` the repair is Python in `ppa.py`, 0.01 to 0.6 s per netlist, 1.3 s for matmul (two weighings and a read-back; 2026-11-04) |

**Post-synthesis modes** (2026-10-30). `check.py --postsynth light|full`, or
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

**The `ppa` stage and `--ppa {auto,off,require}`** (2026-10-31). The sky130 columns were wired in as
EXTRA, beside the GE board, and no submission that was accepted was rejected for them (superseded: decided 2026-11-03, the
board ranks them, see "Scoring"; 2026-11-04, a design the repair, buffering only, cannot make electrically legal is rejected
at this stage), and every other field of the result is what it was (with `--ppa off` the result is the old one
key for key and value for value; against the recorded old results only times, directories, tool identities, the
envelope hash and the comparator's constants count are not compared, and between `off` and `auto` of one
checkout only times and directories are not: `tests/checker/byte_identity.py`). The liberty (12.8 MB, `sky130_fd_sc_hd__tt_025C_1v80.lib`) is not in the
repository: fetch it once with `python3.12 score/ppa.py --fetch-liberty` (into `score/lib/`, git-ignored;
size and sha256 checked before it is moved into place), or point `$SVGOLF_SKY130_LIB` at a copy (the hash is
checked on every load). Without it `--ppa auto` still checks everything else and says so
(`ppa: {"available": false, "reason": "liberty not found: ..."}`; stderr: `ppa: not computed: ...`).
Since 2026-11-01 a weighed `ppa` block also carries `mapped`, flow **A1'** (a real `abc -liberty` mapping of the canonical RTLIL of
the same score run: one more Yosys process, 0.3 to 1.4 s on the references, checked against the scored netlist on 2048 input
vectors, then weighed by the same STA); `--ppa` semantics are unchanged (`off` maps nothing, `require` opens the liberty and the
mapped-flow pins before any work), a design the mapping cannot weigh has `mapped: {"available": false, "reason": ...}` and the check
goes on, a mapped netlist that is not the scored circuit is an infrastructure error in `require` only (`score/PPA.md`, "Wiring").

Set `SVGOLF_LEAN_WRAP` (or `--lean-wrap`) to prefix every `lake`/`lean`
call, e.g. with a slot-limiting wrapper; the time limit counts only the proof
compilation itself, not waiting for the wrapper (each Lean stage's record
says how long it waited, `waited`, apart from its `seconds`).
On a shared machine whose wrapper is a queue, add `SVGOLF_LEAN_WRAP_ONCE=1`:
`check.py` then takes the wrapper ONCE, around the whole run (it re-runs
itself behind the wrapper, and that run calls `lake` and `lean` directly), so
one check waits in the queue once instead of once per call (six or more in a
full check); the result says `lean_wrap: {"once": true, "waited": <s>}`. Without
it, the wrapper goes in front of each call, as before. `python3.12` is required
(pyslang and the extractor). The `postsynth` stage and the validation
scripts also need Verilator 5 (the measurements here are 5.042, recorded in
every postsynth result as `verilator`), a C++ compiler (`$CXX`, default
`c++`) and `make`; a missing tool is an infrastructure error, not a
rejection. The model's makefile includes Verilator's own `verilated.mk`,
which sets `CXX` and `LINK` itself (both `c++` in Homebrew's Verilator
5.042), and `make` takes those over the `$CXX` the stage passes in its
environment, so the compiler they name must be on `PATH` too: where `CXX`
named another compiler and no `g++` was on `PATH`, the build stopped with
"make: g++: No such file or directory" (2026-11-10). A model that the dynamic
loader cannot start (glibc's "error while loading shared libraries:
libatomic.so.1", 2026-11-11: a compiler installed outside the system trees,
under the Linux sandbox, which mounts only those and the model) is an
infrastructure error that names the library, never a rejection.
`SVGOLF_VERILATOR_JOBS` (default 2) sets the parallelism of the
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
| Linux | bubblewrap (`bwrap`): `--unshare-all --disable-userns --cap-drop ALL --clearenv`, a private `/tmp`, read-only mounts of exactly the Spec's trees (what is not mounted does not exist, and a Lean file finds no `/bin/sh`), `--bind` of the output directory | the self-test and the process-level tests (`tests/sandbox/test_sandbox.py`: tool specs, exec limits, secrets unreadable, writes confined, merged-`/usr` links) ran on Rocky Linux 9.8 with bwrap 0.6.3. **Lean was not run there**: the first Linux checker runs `tests/run.py --sandbox require`. So on Linux the sandbox is not yet checked end to end: an interpreter or tool outside the mounted trees can show as a refusal at `extract`, and Lean's CPU time is not measured inside it (2026-11-10) |

Needs unprivileged user namespaces on Linux (Debian `kernel.unprivileged_userns_clone=1`; Ubuntu 24.04's AppArmor restriction
needs a profile for `bwrap`). Inside `bwrap` a tool's own install tree is mounted (the directory above the `bin/` of its
resolved path), not every `PATH` entry: where a run stopped with `bwrap: execvp yosys: No such file or directory`
(2026-11-11), setting `SVGOLF_YOSYS` to the full path of the Yosys binary let it run.
Seatbelt cannot nest (`sandbox_apply: Operation not permitted`): a checker already inside
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
(decided 2026-11-01: no external solvers for now). A task's `allow_bv_decide` is
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
that is possible inside the compile's sandbox Spec, and a measurement found the minimum that would make it work: the toolchain's
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
  A concurrent build of Proglib's `LeanModels.Sv` oleans during a check
  trips it (the check rejects; rerun it).
* **Frontends.** ls-sv reads the design through slang (pyslang 11); Yosys
  through its own `read_verilog -sv`. The source gate makes them read the
  same text with no tool-specific annotation; a design one accepts and the
  other does not is rejected at the corresponding stage. Two tools that give
  the same text DIFFERENT meanings are refused statically where the
  difference is known and its source can be named exactly (the
  `unique`/`unique0`/`priority` qualifiers and x/z literal digits in the
  gate, every other source of an x it knows in the `fourstate` stage, at the
  points the checker probes), and caught by
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
  time above, and the baselines' post-synthesis checks (Kogge-Stone at 15 s;
  the 16-bit Dadda netlists, test material since 2026-11-12, at 83 to 162 s; the
  parametric Dadda baseline of `mul` at 803 s of the 900 s cap, measured 2026-11-12)
  multiply with them. A future
  evaluator for `design.sem` that is faster than `run2` is what would buy
  bigger budgets. `svgolf-eval` is compiled code (no `implemented_by`,
  `extern` or `csimp` in the `LeanModels.Sv` closure it imports); its gap to
  the kernel's `design.sem` is `toExpr` faithfulness and the compiler.
* **The x rules are decided at the probed points, over ls-sv's one resolution** (the universal-correctness
  audit, 2026-11-06; what is open, until ls-sv's every-resolution semantics lands and the statement quantifies
  over every resolution of every x). The statement covers every parameter value in range and resolves an x the
  simulator's way ("Rules"), so the Python rules carry the rest, and they decide it at the points the checker
  probes: the `fourstate` stage runs at the scoring point and the task's probe and backstop points (since
  2026-11-06; `undriven_offpoint.sv`, undriven only away from `N = 16`, is refused at `N = 1`), and a design
  whose x source exists only at a value nobody probes (`N = 5` for `add`, say) still passes. The same holds for
  the loader's own guards that run beside `sem` at the probed points only: 32-bit agreement of `int`
  constants (an `int` localparam that wraps at an unprobed `N` builds another design there) and the
  generate-guard evaluation. The family tasks bound their range so that every width and `int` localparam
  the interface implies stays below `2^31`, the values an `int` holds (decided 2026-11-06), so the port
  widths of `sem N` agree with a real elaboration at every `N` in range; an `int` expression the interface
  does not imply (an internal `N * N`) is checked at the probed points only. The
  statement leaves one choice to the simulator's resolution: the update order of a copy of a variable an
  `always_comb` block writes (ls-sv's alias guard refuses a continuous copy, at the probed points only,
  and admits a separate `always_comb` copy at every point). The power-up value of a combinational loop
  was a second one until 2026-11-06; the statement's `LoopFree` conjunct now refuses every loop and every
  latch, at every `N`. The CLOCKED kinds leave no choice at power-up
  (their statements are final: the arbiter's since 2026-11-07, matmul's and the sorter's since 2026-11-08):
  the claims hold from every 0/1 power-up value of every register and variable, 2-state ones included
  ("Rules", every power-up state), so ls-sv's own start (IEEE's 0 for a 2-state register, x for a 4-state one)
  plays no part, and no construct may create an `x` from known operands (`XSafe`). Run-time `/ % **`
  are no longer a gap: every task bans them ("Rules").
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
  `sv_interface`, since 2026-10-30; before it each tactic proof applied the soundness theorem
  `CombView.Summary.sound` by hand (23 lines). The elaboration and `check.py` columns above are the
  measurements before 2026-10-30 (the later measurements are in PROVING.md, section 11); the code-line
  column is the current file (before 2026-10-30: 107, 235, 594, 446 and 546 lines for the five tactic references;
  before 2026-10-31, when `sv_bridge` and the 2-D rule of `sv_cover` replaced the multiplier references' glue
  theorem and coverage macros: 84, 213, 571, 423 and 522; those measurements are in PROVING.md, section 11).
* **The imports** of the tactic proofs are on the checker's allowlist
  already (`LeanModels.Sv.*`); `tests/imports/test_allowlist.py` pins that, and
  that the tactic library's own imports stay on it.
  The unsafe tactic elaborators run at elaboration only: the staged build, the
  comparator (kernel acceptance, axioms walked through the kernel values, no
  `extern`/`implemented_by` in `Submission.*`) and the `leanchecker` replay
  accept both tactic proofs.

**The proof time limit** (`time_limit_s` of `task.json`) is **300 s, the same for every task**
(decided 2026-11-02, the value 2026-11-06; it replaces the 2026-10-30 rule `max(120, ceil(4 x T))`). It was
120 wall-clock seconds; it is 300 CPU seconds because CPU seconds count every elaboration thread
(Lean elaborates in parallel: the references use up to 3.5 CPU seconds per wall-clock second,
`fdivp_srt` 181.8 CPU s in 77.7 s; measured 2026-11-06, below). All proofs should be
checkable quickly, so the limit is a ceiling and does not follow how slow a reference happens to
be. If an honest proof needs longer, either that proof or our scaffolding is bad, and that is
what gets fixed.

**The limit counts CPU seconds, not wall-clock seconds** (decided 2026-11-05). It is the user
plus system time of the Lean process tree of the `solution` compile, every thread included, read
by the supervisor (`check/sandbox/supervisor.py --cpu-limit-s`: the process group polled while it
runs, every 0.1 s inside the sandbox, and at its end the resource usage of every process it waited
for) and never the time spent waiting for a Lean slot wrapper in front of it. So a loaded machine
does not push a proof over the limit, and a proof that uses two threads counts both. A proof that
WAITS instead of computing (a `sleep`, a blocked read) uses no CPU: for it the compile has a
**wall-clock backstop of 5 times the limit**, 1500 s (`check.py`'s `SOLUTION_WALL_FACTOR`). Why 5:
an honest proof's wall clock runs past its CPU time only while it waits for the machine, and the
worst ratio measured is about 4 (the `add_n` proof with `Mathlib.Tactic`, 82 to 94 s of wall
clock for 23.7 s of CPU while the machine swapped: "Mathlib in submissions"), so the backstop
stops a proof that sleeps or blocks within 25 minutes and leaves an honest one room on a loaded
machine. The result records both readings (`stages.solution.cpu_seconds` and the wall clock's
`seconds`, with `time_limit_counts: "cpu"` and `wall_limit_s`), the stderr line says
`Lean used 37.2 CPU s of the task's 300 s CPU limit (12%), in 29.5 s of wall clock`, and the
warning past half of the limit reads the CPU seconds. `tests/run.py`'s attacks `cpu_proof` (a
step that computes: stopped by the CPU limit) and `slow_proof` (a step that sleeps: stopped by
the backstop, with its CPU seconds under the limit) pin both ends.

T is the LARGEST of the controlled COLD runs of the slowest reference of a task, in CPU SECONDS:
`check.py`'s `stages.solution.cpu_seconds`, the compile of that reference's `Solution.lean` and nothing else (not the
stages around it, not waiting for the slot wrapper); the wall clock of the same runs (`stages.solution.seconds`) is
recorded beside it and only informs. The target is T at most 150 CPU s, a 2x margin for a slower machine. The runs
below were measured on 2026-11-06, three cold runs of every reference (`check.py --no-score`), because the runs recorded
before were wall-clock seconds, made before the limit counted CPU (they are in the history of
`score/time_limits.json`); those of `arbiter`, `matmul` and `sorter` on 2026-11-07, after the merge that brought the
arbiter and the proofs of `matmul_g1` and `sorter_ins` under the second clocked statement. CPU seconds do not follow the machine's load as the
wall clock does, but they are not independent of it either: in the sweep that started at a 1-minute load average of
about 13 the same proof took 13 to 32% more CPU seconds than in the sweeps below 6 (`fdivp_srt` 181.8 against 160.2
CPU s, `sbox_bp` 67.0 against 50.8), which the 2x margin covers. The recorded runs and what was controlled are in
`score/time_limits.json`; `python3.12 score/time_limits.py` prints the table, and `tests/run.py` (step `layout`)
fails when a `time_limit_s` is not 300, a T is over it, a run is not in CPU seconds or a reference that a task.json
lists has no runs, and it names every reference over the target, which does not fail.

| task | slowest reference: cold runs, CPU s (wall clock, s) | T (CPU s) | `time_limit_s` | before 2026-11-02 |
|---|---|--:|--:|--:|
| `_example` | `band_tactics.lean` (3.3, 3.1, 3.2; 2.5, 2.4, 2.4); then `band` 1.7, `band_lp` 1.7 | 3.3 | **300** | 120 |
| `clmul` | `clmul_n.lean` (10.4, 9.9, 10.0; 6.2, 5.9, 5.9) | 10.4 | **300** | 120 |
| `add` | `add_proc_m.lean` (12.3, 12.4, 11.2; 7.1, 7.2, 6.5); then `add_proc` 8.4, `add_mux` 7.0, `add_n` 6.2, `add_n_byhand` 4.7 | 12.4 | **300** | 120 |
| `arbiter` | `rr_mask.lean` (12.6, 12.7, 11.2; 9.8, 9.7, 4.1) | 12.7 | **300** | new |
| `sorter` | `sorter_ins.lean` (17.4, 17.4, 17.0; 5.1, 5.7, 5.2) | 17.4 | **300** | new |
| `matmul` | `matmul_g1.lean` (16.2, 17.5, 17.3; 7.7, 9.6, 11.6) | 17.5 | **300** | new |
| `mul` | `mul_tree.lean` (37.1, 34.8, 34.9; 28.7, 27.5, 25.7); then `mul_tree_h` 33.7, `mul_wallace` 31.6, `mul_n` 16.9, `mul_n_byhand` 14.6 | 37.1 | **300** | 400 |
| `aes_sbox` | `sbox_bp.lean` (67.0, 51.9, 50.8; 75.2, 52.0, 50.5); then `sbox_table` 26.0 | 67.0 | **300** | 215 |
| `fdivp` | `fdivp_srt.lean` (181.8, 160.5, 160.2; 77.7, 65.9, 64.4); then `fdivp_newton` 120.7, `fdivp` 82.2 | 181.8 | **300** | new |

Over the 150 CPU s target: `fdivp_srt` 181.8 CPU s (160.2 and 160.5 in the two quieter sweeps), the proof to improve,
or to drop as a reference; the fdivp references compile their whole proof library in the solution stage (since
2026-11-03 no task ships a prebuilt one). In wall-clock seconds, which the former 120 s limit counted, `mul_tree`,
`mul_tree_h` and `fdivp` were over its 60 s target. A timeout on a busy machine is re-run alone before it counts.

**When a proof hits the limit**, `check.py` says where the time went: the declaration the kernel finished last and how
far into the run, so that the time after it went to what follows it in the file, and the longest waits between
finished declarations (on stderr, in the `solution` rejection, and as `stages.solution.progress`):

```
solution: did not finish within the 20 s limit: Lean ran 20.0 s and was stopped
solution: where the time went: 63 declarations finished (and 5 auxiliary ones), the last `Submission.band_interface` 4.0 s into the run; the 16.0 s after it went to what follows it in the file, which had not finished
```

(measured 2026-11-05 with `check.py --time-limit 20` on the file of `tests/run.py`'s attack `slow_proof`: `band.lean`
with a step that sleeps before `solution`; on the same file the checker before this report said only `did not finish
within the 20 s limit`, and its result had no line of Lean's output). Since the limit counts CPU seconds the first line
names the limit that stopped the compile and gives both readings (measured 2026-11-06, `tests/run.py --attack
slow_proof,cpu_proof`, `--time-limit 10`): `did not finish within the 10 s CPU limit: Lean used 10.2 CPU s in 12.8 s of
wall clock and was stopped` for a step that computes (`cpu_proof`), `did not finish within the 50 s wall-clock backstop:
Lean used 1.9 CPU s of its 10 s CPU limit in 50.0 s and was stopped, so it waited (a `sleep`, blocked I/O, a machine too
loaded to run it)` for one that sleeps (`slow_proof`); the times of the second line are wall clock since the compile
started. An auxiliary
declaration (a tactic's temporary definition, an abstracted proof) is counted with the declaration it serves, and the
first declaration's wait includes the imports.

For this the solution is compiled with Lean's trace class `Kernel` on (`-Dtrace.Kernel=true`: one line per declaration
as the kernel finishes it, in file order), and Lean's stdout is a pseudo-terminal (the supervisor's `--pty`). Through a
pipe Lean buffers its output, and a compile stopped at the limit loses every line it printed (measured 2026-11-05).
The trace lines are removed from the messages the result keeps. A `#guard_msgs` around a declaration would see the
trace as one message more: a compile that fails with the trace showing anywhere but in its own lines is compiled once
more without it, and that verdict stands (`stages.solution.progress_retried`). A proof that uses over half of the CPU
limit gets the same longest waits in its warning.

What was controlled for the 2026-11-06 runs: an Apple M2 Pro (8 performance and 4 efficiency
cores), 16 GB, macOS 27.2, a shared laptop-class development machine on which other users' jobs ran throughout (load
average 2.8 to 13.2 when each run started; which cores ran a process was not controlled);
COLD per run means a new `check.py` process and a fresh staging directory for every run, the references of one task in
sequence inside one acquisition of the Lean slot wrapper (`LEAN_NUM_THREADS=2`, `nice 19`), three sweeps of all
tasks one after the other, with the project build warm and current and the OS file cache not purged; Lean
`v4.33.0-rc1`; `check.py --no-score` (no score and no post-synthesis, neither of which enters the proof time).

## Scoring

**The ranked score is sky130 A0'** (decided 2026-11-03): the scored netlist of the pinned flow below, each gate one sky130
cell, repaired by buffering only and weighed with the pinned `sky130_fd_sc_hd` liberty (`score/ppa.py`). Its two
numbers are the cell area in um^2 (`area_um2_sky130`, exact as `area_e4um2_sky130` in 1e-4 um^2) and the time in ps:
the critical-path delay (`delay_ps_sky130`) of a combinational design, `cycles` x the register-to-register period of a
clocked one (`check.py`'s clocked `time_ps`; a reactive task makes one decision per cycle, so `cycles` = 1 and its time
is the period). **The one ranked number is their product, area x time** in um2*ns
(decided 2026-11-05; `leaderboard/combined.py` defines it, exactly, in 1e-4 um^2 x ps), lower is better: par, the record
and "under par" use it, and the site's leaderboard orders by it. The Pareto frontier of the two ("Leaderboard"), area
in NAND2 gate equivalents (`area_mge`), depth (`ltp -noff`) and flow A1' are EXTRA columns for exploring: shown beside
the score, ranked by nothing. "Reproduce a score" (the end of this section, and
[score/PPA.md](score/PPA.md)'s section of that name) gives every ranked number again, bit for bit. sky130 is the
default course; the second course is ASAP7 placed and routed ("How the routed course is scored", at the end of this
section), whose input is the cells-only ASAP7 view ("The ASAP7 view").

**The build ratings use** (decided 2026-11-05). Every ranked number, on the boards and on the site, is made, or
reproduced bit for bit, by one build of the tools, and it is not a slower portable one:

* **Yosys 0.53** (git sha1 `53c22ab7c0ced80861c7536c5dae682c30fb5834`), the Homebrew build for macOS arm64, compiled
  by clang++ 17 with -O3 (version line `Yosys 0.53 (git sha1 53c22ab7c0ced80861c7536c5dae682c30fb5834, clang++
  17.0.0 -fPIC -O3)`; the `yosys` binary's sha256 `011e094340da48932dd0af17da0846519af24cee7de9ae84c11cc78753ab7732`);
* its **`yosys-abc`**, ABC 1.01 of 6 May 2025 (`UC Berkeley, ABC 1.01 (compiled May  6 2025 05:45:16)`; sha256
  `769348bb154a26d5d97cd877d086893b3c6a1c8242343a505025bad62c7fa653`);
* the liberty `sky130_fd_sc_hd__tt_025C_1v80.lib` (sha256
  `ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5`), `score/ppa.py` (sha256
  `2be8c01e931a3b640c1d3a4104ffe06d8fd3f0e48737d5222e78ed5f58747150`) and `score/ppa_pins.json` (`sky130_a0_v3`,
  sha256 `d66a6086a37a97f5985266057051979fb6a8a3c557d3ef9c42acc1b5e41502d8`), with the scripts `score/canon.ys`
  (`bbd11227d45dc1365f27597fd45c565fe721ba2648450588fc4fd983d00b367b`) and `score/svgolf.ys`
  (`ea58219d8ef14c3bad265218ee266ccdb709ac9d4dc5258edc34d51ee83a0445`).

Records made before this `score/ppa.py` (every record on the board on 2026-11-12) name an earlier file, sha256
`912031912c3e3f6790725161753e95415df34846bd8c27dde3eb707747ddbcbe`, in their checker files and as
`ppa_script_sha256`. The changes since then add the ASAP7 view (`--pdk asap7`, "The ASAP7 view", below; that file
was sha256 `1ef1b1c1904853711cbed9b3b5e275f333aade8f60361f8bbc61305c98c480ab`) and, on 2026-11-12, a summary line on
stderr after the JSON and `--latency` (with `--seq`: the line then shows area x cycles x period), and leave the
sky130 output identical: rescoring all 23 records with this file on 2026-11-12 reproduced every stored sky130 field
but that hash, and every ASAP7 number. So the records were not made again; `leaderboard.py verify` prints a note for the changed
file, and a note never changes a record's status. The ASAP7 view's numbers come from the same build and the same
`score/ppa.py`, with `score/ppa_pins_asap7.json` and its five pinned liberty files in place of the sky130 pins and
liberty.

The flow is deterministic on that build: the same design text gives the same area, time and netlist on every run
(measured 2026-11-05 on 52 designs, 826 runs). Another build of the same Yosys version can break ABC's ties differently
(ABC's mapper sorts with the C library's `qsort`, which is not stable): measured, under YoWASP's WebAssembly Yosys 0.53
(the same git sha1) three `fdivp` designs moved, by up to 2.9% in delay and 0.3% in area, and the other 49 were
identical. So a number you make on another platform may differ slightly from the board's; the same build gives it bit
for bit, and you can get as close to it as you like. The binaries and these measurements are data
(`score/reference_build.json`), which the site's rules page and every task's score card read;
`tests/site/test_rating_build.py` checks that this paragraph states them.

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

**Canonical layout: names, comments and layout never reach the score.**
With one Yosys process, the same circuit scored differently under a
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
  changes the numbering inside the canonical RTLIL, and with it the order of
  the gates ABC reads, so it can move the score: not the GE columns of the
  designs in `tests/expected.json`'s `canonical_layout` (the `canon` step
  checks them), but a flat netlist's and a proved multiplier's, by up to
  17.7% and 41% in sky130 delay (measured 2026-11-05; `tasks/aes_sbox/README.md`,
  Findings). Like commutation below, it is deterministic and the golfer's;
* COMMUTATION is scored: swapping the operands of every `& | ^ ^~ == != &&
  ||` is the same function but a different expression tree, and ABC starts
  from the tree it is given (`mul_n` 1962.576 → 2087.118 GE, the former
  16-bit divider's goalpost 2089.081 / 298 → 2046.093 / 300, Sklansky 127.658 / 28 → 124.992
  / 30). The score is a function of the design's expression structure: how
  you write `a & b` versus `b & a` is yours to golf. Decision
  (2026-10-29): accepted as golfable, not normalized. Measured on `mul_n` at
  `N = 16`: one swapped operand moves the score by at most 0.03%; swapping
  every commutative operand adds 6.3% area at the same depth. Yosys hands
  ABC the same network in both cases (identical cell-type counts before
  ABC); ABC's mapping then picks different gate polarities (672 NAND / 269
  AND / 0 ORNOT against 298 / 449 / 181), because its tie-breaking follows
  the order in which it receives the nodes. It is a property of heuristic
  logic synthesis, not of the pinned flow.

**sky130 area and delay, two flows (A0' ranked since 2026-11-03, repaired since 2026-11-04: below).** Beside the extra GE
columns `(area_ge_v1, depth_v1)`, every check (unless `--ppa off`) records `ppa`, the scored netlist weighed with the real
`sky130_fd_sc_hd` liberty (`score/ppa.py`, [score/PPA.md](score/PPA.md)): `area_um2_sky130` (um^2, exact:
`area_e4um2_sky130` is the integer in 1e-4 um^2; the sum of the cell areas of the repaired netlist),
`delay_ps_sky130` (integer ps: the latest primary-output arrival of a graph-based NLDM static timing
analysis, every input driven by the task's input drive (default `sky130_fd_sc_hd__buf_8`) fed by a 50 ps ramp, every
output bit 10 fF, no wires), `unit_depth` (the GE
columns' depth), `cells_sky130` and `cell_hist_sky130`, with the hashes of the liberty, `ppa_pins.json`, `ppa.py` and the
weighed netlist, `setup` (the timing setup, its `input_drive` included), and `ppa_version` (`sky130_a0_v3` since 2026-11-04,
below). This is flow **A0'**: the pinned `abc -g`
netlist re-expressed gate for gate as sky130 cells, then repaired by buffering only (no cell resized); no new synthesis and no mapping,
so it is a function of the scored netlist (the one the GE columns count) and exact run to run. Beside it, as the sub-object `ppa.mapped`, flow **A1'**:
the canonical RTLIL of the same run mapped by a real `abc -liberty` run (the pinned Yosys script `score/ppa_mapped.ys`: Yosys
0.53's default ABC script, every ordinary sky130 cell and drive strength allowed, compound cells, no sizing pass), checked against the
scored netlist on a sample of input vectors and weighed by the very same STA: `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`
(integer ps), `mapped_cells_sky130_v1`, `mapped_cell_hist_sky130_v1`, `mapped_levels_sky130_v1`, with its own version
(`ppa_mapped_version` `sky130_a1_v1`) and hashes. A1' is closer to a fabricated chip and more sensitive to the mapper than A0': over the
18 reference and baseline designs `score/tests/ppa/designs.json` held when it was measured (2026-11-04) it is a median 0.93x the
repaired A0' in area and 1.04x in delay,
and on the four proved multipliers it puts the array multiplier last in area where GE and A0' put it first. A0' is the ranked score
(decided 2026-11-03); A1' is an unranked research column; their fields are never swapped silently; the measured tables are in
[score/PPA.md](score/PPA.md). The liberty is fetched, not vendored: `python3.12 score/ppa.py --fetch-liberty`. What they do
NOT claim: a fabricated chip's picoseconds (one library, one corner, no wires, a repair rather than timing closure, a 130 nm
process; the board ranks the exact integers of this model). **The numbers are not noisy.** The pinned flow is a
deterministic function of the design's text: the same file gives the same area, time and netlist on every run (measured
2026-11-05 on all 52 references, baselines, records and trial designs of the ranked tasks, 14 to 16 runs each: serial and six
at once, a dozen hash seeds, other temporary and working directories, two checkouts, two locales, other file names, two
install paths; every number and every netlist byte equal), so anyone who runs the pinned tools gets the board's number, and
there is no tie band and no best-of-k. The pinned tools include the Yosys and ABC BUILD ("The build ratings use", above):
another build of Yosys 0.53 can give other numbers on some designs (measured 2026-11-05: three fdivp designs, up to 2.9% in
delay), because ABC's mapper breaks ties in the order the C library's sort leaves them. What moves a
score is how the circuit is written, and that is the golf: names, comments, blank lines, whitespace and the file name never
change it (stage 1 erases them), while the order of an operator's operands, how a chain of XORs or ANDs is grouped and the
order of independent statements do, always the same way (commuting operands moved A0' area by up to 11% and delay by up to
32%; moving one generate block of a proved multiplier moved its area 12.6% and its delay 41%), because ABC's choices follow
the order of the gates it reads. None of it changes what the circuit computes (IEEE 1800 decides that: "Rules"). Trying gate
forms and orders against the pinned flow is legitimate golf. A1' is ONE ABC script, so "mapped" is not "the" mapped result
(between ABC scripts the same design's area moves a median 12% and delay 49%; commuting operands moves A1' area up to 15.5%
and delay up to 20%). A clocked task's design is weighed through the clocked flow (`--seq`: its
register-to-register period); every combinational idiom tried weighs once it reaches the stage, including run-time selects and shifts, `case` muxes and constant
tables, dividers (`score/tests/ppa/idioms.json`). Some designs do not reach it: the `postsynth` stage refuses a netlist whose dead
public-named wires are partly undriven (a known gap of that stage, not of the columns: `score/PPA.md`, "Known gap"; since 2026-11-11 an x
literal on a wire nothing reads is accepted).
`leaderboard.py pareto` lists the frontier of the A0' area and time (an exploration view: the ranked number is their product); `pareto --axes area_mge,depth` (or `area_um2_sky130_mapped_v1,mapped_delay_sky130_v1`)
prints the Pareto frontier over other columns (opt-in; see "Leaderboard").

**sky130 A0' is repaired, and an illegal netlist is rejected (`sky130_a0_v2`; decided 2026-11-03: sky130 A0' is the ranked
score; 2026-11-04: the repair step everywhere, buffering only, and designs that produce illegal netlists rejected).** Before it is weighed, the A0' netlist is REPAIRED
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
scoring point (2026-11-04): all legal, none rejected; three netlists need buffers (`fdivp_newton` 1, matmul G1 5, the matmul
duplication probe 2), so every other area is v1's to the 1e-4 um^2; combinational delays +0.0% to +60.7% (median +5.3%,
the driven inputs; `sbox_table`, whose inputs are heavily loaded, most); matmul's period 48,079 to 10,705 ps (its v1
tables were extrapolated). Every task keeps v1's area and delay orders and Pareto frontiers, except matmul, where the
flop-duplication probe (4.4x faster than the reference in v1) is now slower and leaves the frontier; score/PPA.md,
"Rankings under `sky130_a0_v2`".

**The input drive is the task's (`sky130_a0_v3`; decided 2026-11-04: each task chooses the drive that is more realistic or
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

**Loads per edge (`sky130_a0_v3`, before its release, 2026-11-04).** A load pin presents its `rise_capacitance` to a rising
edge and its `fall_capacitance` to a falling one, as OpenSTA reads them; the STA had loaded every net with the pins'
`capacitance` and was 0.5% to 2.8% off OpenSTA on the references. With the change it equals OpenSTA to 1 fs per arc
(`score/test_ppa_opensta.py` records OpenSTA's numbers). MEASURED on every reference and baseline at its scoring point:
every area unchanged, delays -0.30% to +1.32%, no delay order, area x time order or Pareto frontier changes; matmul's
period 10,705 to 10,696 ps (one of its five trees is now 2 x `buf_4`, 6 buffers, the same area), the sorter's 2,510 to
2,523. score/PPA.md, "The per-edge loads".

**Reproduce a score.** The ranked numbers (A0' area and time) are a pure function of the design text, the pinned flow and
tool build, the pins and the task's scoring point and input drive, and each is reproduced bit for bit by one command from the repository's root (Python 3.12 with `pyslang`, `Yosys 0.53 (git sha1
53c22ab7c0ce…)` and the `yosys-abc` beside it on `PATH`):

```
python3.12 score/ppa.py --fetch-liberty                     # once: the pinned liberty (sha256 ef34f999…5d23d5) into score/lib/
python3.12 score/ppa.py SOLUTION.sv --task tasks/<name> --no-mapped --json out.json --netlist scored.v --repaired-netlist repaired.v
python3.12 score/ppa.py SOLUTION.sv --task tasks/matmul --seq --latency 4   # a clocked task (stderr: area x 4 cycles x period)
python3.12 score/ppa.py SOLUTION.sv --task tasks/arbiter --seq              # a clocked task, reactive (one decision per cycle)
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

### The ASAP7 view

**sky130 is the default; ASAP7 cells only is the routed course's input** (decided 2026-11-09; 2026-11-12). From
2026-11-09 the site's selector showed every golf score on sky130 or on these cells-only ASAP7 numbers; since 2026-11-12
its second course is ASAP7 placed and routed ("How the routed course is scored", below), which places and routes the
netlist this view weighs. The cells-only numbers stay: they are the netlist the routed course places, the period of its
clock, and a column of each record page ("cells only (A0′)", with the wire cost against it); `leaderboard.py board --pdk
asap7` prints their boards. The records keep their sky130 columns; GE and depth do not depend on the library.

**How ASAP7 is scored.** The same scored netlist as sky130's score (the pinned flow does not depend on the library),
weighed by `score/ppa.py --pdk asap7` (flow A0', `asap7_a0_v1`): each gate its least-area ASAP7 build, repaired by
buffering only, an illegal netlist rejected, no wires and no place and route (like sky130's score), timed by the same
static analysis. The area is in um^2 (exact in
1e-5 um^2), the time in ps (the critical-path delay; on a clocked task cycles x the register-to-register period). The
library is asap7sc7p5t rev 28 (RVT, typical corner, 0.70 V, 25 C): five liberty files of The OpenROAD Project's
OpenROAD-flow-scripts (commit `a1a6c3ff`, each file with its BSD 3-Clause licence header), fetched at pinned hashes,
never vendored (decided 2026-11-10).

**What ASAP7 is, and its quirks.** ASAP7 is a predictive 7 nm library made for research: it has never been fabricated,
so no chip can confirm its numbers, where sky130 is a real 130 nm process. What it forces on the scorer, each choice
pinned with its reason in `score/ppa_pins_asap7.json`:

* it has no MUX, A&!B or A|!B cell, so those gates cost two cells each (an inverter in front);
* its x1 flip-flop has only an inverted output, so every flop gets an inverter forming Q;
* its timing tables start above the smallest input loads, so a read below a table's grid is read at the grid's floor
  (counted, and a floored delay errs slow) where sky130 rejects the netlist; above a grid the rule is sky130's;
* its timing setup is scaled from sky130's by the same reasons: a 20 ps input ramp, 2.5 fF per output bit, every input
  driven by `BUFx8`;
* its tie cells declare no capacitance limit, so one is pinned.

The two libraries order the designs by area almost alike (a sky130 area is 63 to 72 times the ASAP7 one) and differ on
time, because they price AND, OR, XOR and MUX against NAND differently; so area x time can reorder close designs, and
does on the `add` and `mul` boards.

**Where the numbers live.** Not in the records, whose hash and address would change for a column that is a pure
function of the netlist they already pin: in `leaderboard/asap7/<task>.json`, one entry per design file a task's pages
show or will show (every record, proved reference and baseline), bound to its record by the canonical text, the canonical RTLIL, the
GE columns, the cycles and the scored netlist. `leaderboard.py asap7 --write` measures them (a new or re-seeded record
needs it), `leaderboard.py asap7` checks them, and `asap7 --rescore` and `verify` weigh them again and require the same
numbers, bit for bit. A design the ASAP7 view would show without a bound entry is "not ranked" or "–" there, never a
sky130 number, and the site build warns about it (fatal under `--strict`, so a published site has the whole view)
([leaderboard/README.md](leaderboard/README.md), "The ASAP7 view"; [score/PPA.md](score/PPA.md), "ASAP7: an alternative
library", has every choice and measurement).

```bash
python3.12 score/ppa.py --pdk asap7 --fetch-liberty                                 # once: the five pinned files
python3.12 score/ppa.py SOLUTION.sv --task tasks/<name> --pdk asap7 --no-mapped     # a design's ASAP7 numbers
python3.12 leaderboard/leaderboard.py board --task <name> --pdk asap7               # the ASAP7 board
```

### How the routed course is scored

**The second course is ASAP7 placed and routed** (decided 2026-11-11 and 2026-11-12). The course selector in the top
bar of every page, "Course", offers sky130 (the default) and ASAP7 · placed and routed (since 2026-11-13 the front page's
too: one control in one place).
On the routed course every golf score of the site is the routed one: the boards and their order, par, the record and
under par, the score chart, the area-time plots and each record's overview. The browser remembers the choice (where it
allows it) and the address carries it: `?pdk=asap7pnr`, and `?pdk=sky130` once a reader has chosen a course. An old
address with `?pdk=asap7`, the cells-only view this course replaced, shows the routed course and says so. Without
JavaScript the site shows sky130. Both courses are ranked when the site is built, by `leaderboard.py`'s own functions
(`board --pdk asap7pnr`), under the same rules (area x time, par, ties); a score on one course is never compared with a
score on the other. The netlist cards, the scaling view and the task texts stay sky130's, each labelled so on the routed
course.

**The flow.** Each design's ASAP7 netlist (the repaired netlist of "The ASAP7 view", above) is placed and routed by
OpenROAD-flow-scripts from one pinned image (`openroad/orfs`, used by digest, x86-64 only) in its minimal flow `min_v1`:
a floorplan at 40% core utilisation, placement, a clocked task's clock tree, routing, then the flow's own equivalence
check. Nothing optimises the design for speed (no timing-driven placement, no timing repair): the flow adds only what a
working layout needs, buffers on slow or overloaded wires and a clocked task's clock tree. Each job runs with two threads
on two CPUs, an 8 GB memory cap and no network. `score/pnr/pins.json` pins the image's digests, the flow and its
variables, the job's shape, the sha256 of the scripts that write each job's `config.mk` and SDC, and the rules below; a
result made under other pins is stale and shows no number.

**The score.** Area: the cells of the routed netlist by the ASAP7 liberty (the buffers and clock tree the flow adds
included; tap and fill cells and the die not), exact in 1e-5 um^2. Time: the clock period minus the worst setup slack,
with the wires extracted from the layout, at the typical corner, rounded half-even to whole ps; on a clocked task, times
the cycles. **Score = area x time** in um^2 x ns, lower is better; ties, par, the record and under par work as on sky130.
Par is the routed score of the task's par design (`leaderboard/par.json`); while that design is not routed, the routed
course has no par for the task.

**One run, one seed.** Placement starts from a number, the seed. The rule (decided 2026-11-11): each design is placed and
routed once, at one seed, and that run is its score: the seed its submission names, else a seed drawn at random once and
kept with it, so that it is not chosen after the boards are seen. Every design routed so far (2026-11-11 to 2026-11-13)
ran at seed 1. A design's request can name a seed before its run:
`leaderboard.py asap7pnr --request --task <name> --design FILE --seed N --write` stores it with the design (without
`--seed`, a seed is drawn from the operating system's random source and stored); a stored request is never changed,
and the run itself is still made by the maintainers on the course host. Another seed moves a score by about one per
cent (measured on the first records: 0 to 2.8% between seeds 1, 2 and 3).

**What a run must pass.** The flow finishes; the router reports no design-rule violation; and the flow's equivalence
check prints that the routed netlist is identical to the one it read (the course requires that line, not merely the
absence of an error). Recorded, not scored: hold violations (no hold repair is run, and clocked designs end with some)
and slow-signal (max-slew) warnings, whose count a record page names.

**What the equivalence check shows.** The flow's equivalence check compares the routed netlist with the netlist the run
was given: it shows that place and route preserved the run's input, not that the input was the design's netlist (the
runs of the two changed netlists below both passed it). That the input is the design's ASAP7 netlist is checked by
sha256: the placed netlist's hash must be the entry's and the ASAP7 view's, and a run of a changed netlist is refused
there (the design shows "unbound", the file check "not the entry's netlist_sha256"). A negative control was run on
2026-11-13: in add's and in sorter's par design one gate was changed, and the same equivalence tool, with the flow's own
configuration, reported "Circuits are DIFFERENT" for the routed changed netlist against the unchanged one (4 of 4 cases:
both designs, each against the netlist file the course binds and against the flow's own copy of it) and "Circuits are
IDENTICAL" for the routed unchanged netlists (4 of 4). The tool exits 0 either way; its verdict is read from its log, as
the flow does. This control is not a pinned step of every run.

**What is not checked.** Hold timing, other corners, and power are not scored: this is a predictive library at one
corner, not sign-off. Every routed number comes from one host type (x86-64 Linux, Intel Xeon, the image unpacked into a
rootless chroot); docker, other x86-64 hosts and Apple silicon are not measured. The tools that write a job's
`config.mk` and SDC, run it in the pinned image by digest, draw its picture and collect its result are in `score/pnr/`
([score/pnr/README.md](score/pnr/README.md)): they write the `config.mk` and SDC of every committed run byte for byte,
and they rebuild a committed table from a stored run, but no run has been made with their container runner yet, so a
run made again from the repository alone is expected, not yet shown, to give the committed numbers.

**Not routed yet.** A record is placed and routed after it is recorded, on a course host. Until its run is in
`leaderboard/asap7pnr/<task>.json`, bound to its design file (its sha256), to its ASAP7 netlist, to the task's scoring
point and to the current pins, the routed course lists it under "Not ranked" with the reason ("not routed yet: place
and route pending" while it has no run) and shows a dash: never a cells-only number or an older one in its place.
Since 2026-11-13 every design the tasks show (52 design files: records, references and baselines, the 13 matmul
architecture records included) has a routed score.

**The layout picture.** Each routed design's record page, and par's, shows the layout of its scored run in the
netlist card's Layout tab, beside the schematic, on the routed course only (decided 2026-11-13: on sky130 no ASAP7
layout is shown): drawn by OpenROAD's own renderer from the run's final database, power and ground wires not
drawn, at most 1600 px (a 640 px thumbnail on the page); its caption names the seed and the die size.

**Where it lives.** `leaderboard/asap7pnr/<task>.json` (one entry per design file: every run's numbers and the hashes
of the files it wrote) and the pictures under `site/layouts/<task>/`, outside every record hash. `leaderboard.py
asap7pnr` checks them offline ([leaderboard/README.md](leaderboard/README.md), "The routed course";
[score/PPA.md](score/PPA.md), "ASAP7 placed and routed", has every pin and where the ASAP7 files come from).

```bash
python3.12 leaderboard/leaderboard.py asap7pnr                                     # check the routed results offline
python3.12 leaderboard/leaderboard.py board --task <name> --pdk asap7pnr            # the routed board
```

### Other sizes

The board ranks each task at one size, its scoring point. The task page's "Compare the designs" and a record's "Area
against time" also show the designs at the task's other sizes, chosen with **Size** (decided 2026-11-13): every
record's design file synthesized by the same pinned flow at the sizes of `leaderboard/sizes.json`
(`leaderboard/sizes/<task>.json`, written by `leaderboard.py sizes --write`; the references and baselines that are no
record by `score/points.py`). These numbers are measured, not ranked: par, the record and "under par" stay at the
scoring size, and a chart at another size says "not ranked". A design not measured at a size (a run past the 900 s or
6 GiB limit, a record newer than the data) is left out there and counted under the chart. The explorer's X axis
"Size" draws each design's score against the size on log axes, one line per design, to show which designs scale
better. The routed course is measured at the scoring size only ([leaderboard/README.md](leaderboard/README.md),
"Other sizes").

## The banlist

`score/banlist.py` runs two independent checks, both driven by the task's
`banlist.operators` plus the run-time `/ % **` that every task bans
(`ALWAYS_BANNED`, since 2026-11-06: "Rules"), on the source gate's canonical text:

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
* the **backstop** (Yosys) runs `proc; opt` at the backstop points and
  rejects every cell of the banned operators' types (`$add $sub $neg $mul
  $div $divfloor $mod $modfloor $pow`, plus `$alu $macc $macc_v2 $lcu $fa`
  when any of `+ - *` is banned). Then, in a task that bans `+` or `-`
  (decided 2026-11-05), it runs `alumacc` on the same design and rejects
  every `$alu $macc $macc_v2 $lcu $fa` cell that `alumacc` built: a run-time
  ordering comparison (`$lt $le $gt $ge`) becomes Yosys's adder (`$alu`) in
  tasks that ban `+` and `-` (`a > ~b` IS the carry out of `a + b`;
  `tests/add/baselines/cmp_carry.sv` builds a whole adder that way). Equality
  (`$eq $ne $eqx $nex`: `alumacc` builds no `$alu` for it), comparisons Yosys
  folds as constants (over parameters and genvars) and a comparator built
  from `& | ^ ~` stay allowed; a task that bans neither `+` nor `-` (the
  divider) keeps every comparison. It reports the cell's source location (a
  lowered comparison's own). The front check does not look at comparisons.

Note that run-time index arithmetic is arithmetic: `a[j + 1]` with a signal
`j`, `v[sel -: 4]` and `x[sel*W +: W]` build `$add`/`$sub`/`$mul` cells and
are rejected under an arithmetic banlist.

## Leaderboard

`leaderboard/leaderboard.py` (documented in full in
[leaderboard/README.md](leaderboard/README.md); Python 3, standard library
only) turns an accepted submission into a **record** and ranks the records
on the sky130 A0' score: the area in um^2 and the time in ps, whose product, area x time, is the one
ranked number (decided 2026-11-05; "Scoring"). `board` and `export` list the records by it, lowest first
(`#` is the rank, as on the site); the Pareto layer of the two factors is an exploration column beside the
GE area and depth, and `pareto` lists their frontier, also for exploring.

```bash
# record it: runs check.py on the pair and writes the record only if it is ACCEPTED, into
# leaderboard/data/add/, the directory a pull request adds (--data-dir DIR: a private trial elsewhere)
python3.12 leaderboard/leaderboard.py add --task add --player YOUR_HANDLE --assisted-by "TOOL OR MODEL" \
    --sv solution.sv --lean Solution.lean
# hand it in: the pull request that adds the record's three files (--dry-run: the steps, nothing sent)
python3.12 leaderboard/leaderboard.py submit --task add --record HASH
python3.12 leaderboard/leaderboard.py pareto --task add        # the (sky130 area, time) frontier (exploration)
python3.12 leaderboard/leaderboard.py pareto --task add --axes area_mge,depth      # opt-in: the frontier over other columns (here GE)
python3.12 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1   # ... over flow A1''s columns
python3.12 leaderboard/leaderboard.py board  --task add       # the table by area x time (--format json too)
python3.12 leaderboard/leaderboard.py board  --task add --pdk asap7   # the same on ASAP7 (the site's ASAP7 view)
python3.12 leaderboard/leaderboard.py verify                  # re-verify every stored record
python3.12 leaderboard/leaderboard.py export --out LEADERBOARD.md   # all tasks, Markdown
```

* **How a record reaches the board.** There is no submission server: `add` writes a record on your machine and
  sends nothing. To hand in a record, `leaderboard.py submit` opens a pull request that adds its three files; a
  check on the pull request verifies every record and runs the full check on the added ones, and a maintainer
  re-makes the ranked number on the rating build when the pull request is merged. `submit` first checks the
  record with `verify --offline` and refuses a failed, stale or light one; the pull request's text gives the
  task, the handle, `assisted_by` and the record's board line (its place on the board as the site shows it), in
  the parts of `.github/pull_request_template.md`. The check is `leaderboard/pr_check.py`, which the
  repository's `records` workflow runs on every pull request that touches `leaderboard/data/` or
  `leaderboard/writeups/`: it refuses one that changes anything but added records and added or improved writeups
  ("Writeups" below; `submit` takes a record's writeup along when there is one), and writes each added record's
  board line and the outcome to the job summary. `leaderboard/data/<task>/` is where `add` writes without `--data-dir`, and what a pull request adds;
  `--data-dir DIR` keeps a private trial out of it.
  **That directory takes only a record whose check the board ran itself** (decided 2026-11-06, the
  universal-correctness audit): `add` refuses `--from-check` (a stored result, never re-run) and `--sandbox off` there, and a check that did not run in the OS sandbox
  (`sandbox.active`); both options stay for a `--data-dir` trial.
* **A record** is one JSON file per accepted submission,
  `leaderboard/data/<task>/<record_hash>.json`, with the submitted `.sv` and
  `.lean` copied next to it. It holds the player handle, `assisted_by`, the
  sha256 of both files and of the source gate's canonical text, the GE
  columns (`score`: `area_mge` in integer milli-GE, depth, gate counts, scoring point), the
  checker's identity (the svGolf and Proglib revisions, `svgolf_revision` and
  `lean_surfaces_revision`, Lean toolchain, Yosys
  and Verilator versions, the sha256 of the two scripts, the GE table and the
  checker's files), the proof's facts (axioms, build seconds, code lines,
  imports, tactics), the optional `ppa` object (check.py's sky130 columns, flow A0', THE RANKED SCORE, and inside it the
  optional sub-object `mapped`, flow A1', see "Scoring"; a record made before them has no such key and stays valid but is
  not ranked until it is backfilled, and a
  `leaderboard.py` from before the `ppa` key treats a record that has one as corrupt: update every reader first; one
  from before `mapped` accepts it) and `record_hash`, the sha256 of the record's canonical
  JSON. A clocked task's record (since 2026-11-07; the `arbiter`'s) names the clocked flow (`checker.flow`
  `"seq"`: `score/svgolf_seq.ys` and `score/ge_seq.json`, whose GE table prices the flip-flop), and its
  `postsynth` holds every post-synthesis point with every seed's cycles, power-ups and draw
  (leaderboard/README.md). `add` refuses anything `check.py` does not accept at every stage, a result `check.py` marks
  INCOMPLETE (`complete: false`, with the reasons in `incomplete`: `--no-score`, a light post-synthesis
  check, `--no-trusted-build`, a `--time-limit` other than the task's), a result without
  `stages.trusted` (the run did not build the trusted modules, so its comparator checked the goal
  against whatever statement was on disk) and a solution stage that did not run under the task's own
  CPU limit, or was stopped at a limit. A failed, timed-out or incomplete check establishes nothing
  ("Rules").
* **How a record is verified.** `verify --offline` re-hashes the record and
  the stored files and rechecks the area arithmetic (milliseconds), and checks
  that each routed table of the routed course is well-formed and every layout
  picture it records is its file (a table that is not fails it); plain
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
  full. **A light record never ranks** (decided 2026-11-06): its check was incomplete,
  so the boards list it under "Not ranked" with that reason, whatever its score; it
  is a legitimate local record, and not on a separate board.
* **`assisted_by`** is the list of tools and AI systems that helped write the
  design or the proof, as free text (`["Claude (Anthropic)", "a proof assistant"]`);
  empty means unassisted. It is the submitter's word, shown next to every
  entry, and `--unassisted` ranks only the entries with an empty list. It does
  not change the ranking otherwise.
* **The boards weigh the sky130 score** (decided 2026-11-03; its product, area x time, is the ranked number since
  2026-11-05). `board` and `export` rank the records by the product of the A0' area
  (`ppa.area_e4um2_sky130`, exact in 1e-4 um^2) and time (`ppa.delay_ps_sky130`; a clocked record's `score.time_ps`,
  cycles x period) and show the Pareto layer of the two, the GE area and depth as extra columns; `pareto` lists the
  frontier of the two. A record is ranked only if it carries the columns and
  they are comparable: weighed under the current `ppa_version`, liberty and pins file, and under the task's input drive
  now. The others are listed as "Not ranked" with the reason; a record without sky130 columns (made before them, or with
  `--ppa off`) is not ranked until it is backfilled (checked again under `--ppa require`). `pareto --axes` (any of
  `area_mge`, `depth`, `area_um2_sky130`, `time_ps`, `delay_ps_sky130`, `unit_depth`, `cells_sky130`, and flow A1''s
  `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1`, `mapped_levels_sky130_v1`) is the
  opt-in n-dimensional frontier over other columns (`--axes area_um2_sky130,time_ps` is `pareto`'s; ties kept, areas
  compared as exact integers); records without them, or computed under another `ppa_version`/liberty/pins (or, for the
  mapped axes, another `ppa_mapped_version`/script/pins), are listed as "not shown" with the reason. The boards print no
  confidence band and need none: the ranked numbers are exact integers and deterministic (the same design text gives
  the same numbers on every run of the pinned flow), so equal products tie and every other difference ranks.
* **Policy: area x time ranks; the Pareto frontier is for exploring; no budget
  by default.** The ranked number is a record's area x time (decided 2026-11-05:
  par, the record, "under par" and the board's order use it). The board lists the
  records by it, lowest first; equal products share a rank (1, 1, 3) and are
  listed as the site lists them (the smaller GE area, then the smaller depth,
  then the earlier date, then the record hash), so the order is the same on
  every machine. Each row names its Pareto layer of the two factors, an
  exploration column (`pareto` prints layer 1): a record is on the
  frontier iff no other record is at least as good on both sky130 area and
  time and strictly better on one; ties are kept. A task author may add a depth budget
  (`leaderboard.depth_budget` in `task.json`, ranking only; or the checker's
  own `scoring.depth_budget`, which rejects; on the unit depth): the board
  then also ranks the best area x time under it and flags the entries over
  it. No task has one today. Scores are comparable exactly when the pinned
  flow, the scoring point, the sky130 pins and the task's input drive agree,
  so the board ranks only records checked under the current ones and lists
  the rest as "Not ranked" until they are submitted again.

**Par is one design per task** (decided 2026-11-12: only the simplest algorithm is par; the other designs are
entries trying to win the golf). `leaderboard/par.json` names it, one line per task: `add`'s ripple-carry adder `add_n`,
`mul`'s array multiplier `mul_n`, `clmul`'s array `clmul_n`, `aes_sbox`'s 256-entry table `sbox_table`, `fdivp`'s
restoring divider `fdivp`, `matmul`'s `matmul_g1`, `sorter`'s insertion-cell array `sorter_ins`, `arbiter`'s
`rr_mask`, and the tutorial's one design `band`. Par's records are the only records under `svgolf-reference`
(below); par is their score. Every other design the maintainers proved, the other references task.json lists and
the baselines of `tests/<task>/baselines/` without a banned operator, is an ENTRY: it joins the board as a record
under a handle of its own, like any player's, and is ranked with the players' records; the site shows it once that
record exists, and until then not at all (never as a reference or baseline line).

The baselines with an operator the task bans are **not** records: proved comparison designs (decided 2026-11-12:
every design the site shows has a kernel-checked proof, its `.lean` beside it in `tests/<task>/baselines/`), never
entries, never ranked and never par. Each is proved with the task's operator banlist lifted (`check.py
--lift-banlist`, which never accepts: "banned operator: proved, not an entry"), and `check.py` without the option
rejects it. At the scoring point (the ranked sky130 A0' area and time from `score/tests/ppa/expected_ppa.json`,
the extra GE area and depth from `tests/expected.json`):

| task | design | sky130 um^2, ps | GE, depth |
|---|---|---|---|
| `add` | comparison-carry adder, Yosys's `$alu` through run-time comparisons (banned since 2026-11-05; proved with the banlist lifted) | 857.072, 1965 | 195.975, 17 |
| `add` | Yosys's own `{cout, s} = a + b + cin` (banned `+`; proved with the banlist lifted) | 497.9776, 3143 | 117.994, 33 |
| `mul` | Yosys's own `p = a * b` (banned `*`; proved with the banlist lifted) | 8825.9648, 6261 | 2081.227, 59 |

The board is seeded with entries the maintainers made with AI assistance (each record names the tools),
each proved and scored like any entry: they are ordinary entries and can be beaten. There are no outside
entries yet. Par's records are the first
records (`svgolf-reference`,
`assisted_by` `["Claude (Anthropic)"]`, notes `reference solution`;
`leaderboard.py seed-references` records them again, par's design only, and only it records under that handle
(decided 2026-11-12: `add`, `submit` and the pull-request check refuse the handle, `add` refuses it for any other
design, and par comes only from par's design); on 2026-11-12 the records of the other references (`band_lp`,
`sbox_bp`, `fdivp_newton`, `fdivp_srt`, `mul_tree_h`) left the board, to come back as entries; the records of
`leaderboard/data` were re-seeded under `sky130_a0_v3` on 2026-11-04, with the
same design and proof files, so they carry the ranked columns, again on
2026-11-05 after the checker's own files changed, with the same files and numbers,
and on 2026-11-06 after the statement change, from the proofs updated for the
parameter range, with the same designs and numbers).

### Writeups

**Write up your submission** (decided 2026-11-13). The record proves that a design is correct and what it scores;
a writeup tells the story, as a write-up post after a competition does: what the idea is, why it scores as it
does, how the proof goes and what did not work. Every golfer and every agent is asked for one with each pull
request of a record; a record without one is still accepted.

A writeup is one Markdown file, `leaderboard/writeups/<record_hash>.md`, named by the full hash of its record.
Start from `leaderboard/writeups/TEMPLATE.md`. Its first line is `# <title>`: the submission's short title, plain
text of at most 60 characters, the name of the idea ("Kogge-Stone prefix adder", "Carry-save tree, ripple final
adder", "Strassen, one level"). The site shows the title as the record page's heading, under the player in a
task's submissions list and in every chart's tooltip, and the rest of the file as the record page's writeup card.
A good writeup has:

* **the approach**: the circuit's architecture and its trick, the area/time trade-off it makes;
* **the key insight**: why it beats, or does not beat, par and the record before it;
* **the numbers**: area, time, cycles and score, and what dominates them (the cells, the critical path);
* **the proof strategy**: the structure of the proof, its invariants and key lemmas, the tactics that did the work;
* **the dead ends**: variants that scored worse, proofs that did not go through, and why.

The file lies outside the record: no field of the record and none of its hashes name it, so adding a writeup or
improving one later never changes a record, its hash or its rank, and a pull request may add a writeup to a record
already on the board. `leaderboard.py verify --offline` checks each writeup: it names a record, it is UTF-8 with
Unix newlines and no control or bidirectional-override character, its first line is the title within its length,
it is at most 200 kB, it carries none of the site's internal markers (`site/config.json`'s denylist: a writeup is
shown as the site's own text), and its body stays inside the site's Markdown subset: headings, paragraphs, lists,
code spans and fenced code, emphasis, tables and links to `http` or `https` addresses; no raw HTML (it is shown as
text), no images, no block quotes. The site renders it with everything escaped. A record without a writeup shows
its design file's name as its title and a short "No writeup yet" card. The writeups of the first records were
written by the maintainers from each record's design and proof files, and say so at their end.

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
  every baseline naming a proof file that exists, and the generated
  netlists of `tests/<task>/unproved/` (test material, no proof) and the
  generated baseline proof reproducible from their generators;
* `build`: `lake build` (SvGolf, tasks, tests), so every refutation of a
  negative design is re-checked by the kernel, its design re-extracted by
  `load_sv` when anything it depends on changed (but the three that do not build
  at the pinned library yet, "Building", which `negatives` builds);
* `unit`: `score/test_score.py`, `score/test_srcgate.py`,
  `score/banlist.py --selftest`, `score/fourstate.py --selftest`, and
  `tests/checker/test_advisories.py` (the oracles against independent arithmetic, the
  functional comparison and its warning, the `--tactics` classification, `dev_hint`,
  the stripped `SVGOLF_ELAPSED` line, the post-synthesis mode selection and light
  vector set, the generated `Submission.Design` text: no Lean, 46 tests),
  `tests/checker/test_design_stage.py` (the `design` stage rejecting an Unsupported
  construct, on check.py's real early stages with a fake Lean: 5 tests), `score/test_ppa.py`
  (the sky130 columns, stage 1: the netlist reader on escaped identifiers and dead wires, the eight idiom
  designs of `score/tests/ppa/idioms.json` with goldens; flow A1': the mapped netlist weighed by the same STA, the equivalence
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
  Proglib that made a tactic module import something off the list fails
  here, not in every reference proof; and the import closure of `Mathlib`,
  8,643 package modules in eight roots, recomputed from the package sources, so a
  Mathlib bump that reaches a package the checker does not admit fails here; the
  glued-import headers; `SvGolf/CoreSimp.lean` lists exactly the checker's package roots), and the
  sandbox's own tests ("Sandbox" under "Checking"): `tests/sandbox/test_env.py` (the environment
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
  scores (but the three `only_n16.sv`, rejected at `design` with the loader's
  pinned refusal while the pinned library refuses them, "Building"); and each refutation
  that does not build yet, built alone, failing with its pinned refusal;
* `baselines`: every baseline scored (`score.py` applies no banlist, so a
  banned-operator baseline is scored "with the banlist lifted"), the
  banlist's verdict as expected, token identity where claimed, the 4-state
  rules passing at every scored point, and the post-synthesis check passing (`check/postsynth.py`, at the scoring point;
  `--full`: at every scored point), so no legitimate design is falsely
  rejected;
* `baseline-proofs`: every baseline with its proof through `check.py`
  (decided 2026-11-12: every design the site shows is proved): accepted, or
  for a banned-operator baseline `check.py --lift-banlist` ending at the
  pseudo-stage `lifted` (proved, not an entry) with the task's banlist
  rejecting it; the axioms within the task's allowed set, the full
  post-synthesis check, the score as in `tests/expected.json`;
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
  Unsupported node (the latent function-local x, the two latches, and
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
* `sandbox`: the sandbox against real attacks, each through `check.py --sandbox require` on `_example`
  (skipped, with a message, where the machine has no mechanism): `host_naive` (the 2026-10-31 finding: with
  `--sandbox off` ACCEPTED and the file outside the stage exists, the control that shows the attack is real;
  with the sandbox REJECTED at `solution`, "operation not permitted", no file), `host_catching` (every
  action tried and every failure caught, so the file compiles either way: with `--sandbox off` the marker is
  written, a loopback listener hears a connection and the tripwire rejects the overwritten `Design.olean`; with
  the sandbox ACCEPTED, every action but the harmless listing of the scrubbed environment BLOCKED, no marker, no connection),
  `host_memory_bomb`, `host_output_flood` (a flood to `/dev/fd/1`, past `#eval`'s capture) and `host_cpu_bomb`
  (stopped by the supervisor's memory limit, output cap and the task's wall clock), and the two tripwire attacks with
  the sandbox ON. `tests/run.py --sandbox require` runs EVERY step's `check.py` calls with it.

Runtime: the whole suite takes an hour or more on a laptop, and waiting for the Lean slot comes on top on a
machine where another job holds it. Of its parts (measured 2026-10-29, when the suite had fewer tasks): `add`'s
`validate.py` is 3 minutes, 90 s of them the C++ builds of 45 designs-and-widths at about 2 s each; a `check.py`
run takes 10 to 60 s, the `mul` reference about 90 s with its postsynth stage, the 16-bit Dadda netlists'
postsynth checks (then baselines, test material since 2026-11-12) 83 and 162 s, and that of the
parametric Dadda baseline (2026-11-12) about 800 s, in the `baselines` and again in the `baseline-proofs` step; the build is 45 s to 90 s when the refutations re-elaborate (a changed design,
task, extractor, or a comment in a `.sv`). `--full` adds hours (`fdivp`'s
exhaustive steps, the `mul` reference's full plan, `add`'s full
`validate.py` and `verilator.py`, and the postsynth checks of every baseline
at every scored point).

The sky130 columns add about 60 s to that (measured 2026-10-31, again after the review fixes): the `ppa` step
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

| task | statement | par's design, and the other proved designs | score at the scoring point: sky130 A0' um^2, ps (their product, area x time, is the ranked number); GE, depth (extra) |
|---|---|---|---|
| `_example` | N-bit bitwise AND (toy) | `assign y = a & b;`, for-all-`N` proof | 100.096 um^2, 280 ps; 21.328 GE, depth 1 |
| `add` | N-bit adder with carry, `{cout, s} = a + b + cin`; bans `+ - * / % **` | par: ripple carry from gates, for-all-`N` proof (with the sv_comb tactics, and by hand as `add_n_byhand`); proved Sklansky and Kogge-Stone prefix adders, entries (`tests/add/baselines`), and two proved banned-operator designs as baselines | ripple (par) 460.4416 um^2, 2611 ps; 112.0 GE, depth 33. Sklansky 541.7696, 2451; 127.658, 28. Kogge-Stone 641.8656, 2064; 149.652, 24 (Yosys's own `+`: 497.9776, 3143; 117.994, 33) |
| `mul` | N-bit unsigned multiplier, `p = a * b` on `2N` bits; bans `+ - * / % **` | par: the array multiplier (AND partial products, ripple-carry rows of full adders), for-all-`N` proof (with the sv_comb tactics, and by hand as `mul_n_byhand`); entries: three proved tree references and a Dadda tree with a ripple-carry final adder, one design for every `N`, proved by hand (`tests/mul/baselines`); Yosys's own `*` as a proved banned-operator baseline | array (par) 8290.4512 um^2, 10907 ps; 1962.576 GE, depth 88. The proved tree `mul_tree_h`, an entry: 8563.2128, 5992; 2025.905, 62 (Dadda + ripple, an entry: 8230.3936, 5461; 1953.585, 61. Yosys's own `*`: 8825.9648, 6261; 2081.227, 59) |
| `fdivp` | IEEE 754 division PARAMETRIC in the format, `fdiv #(W, P)` on `W + P` bits for every `W >= 2`, `P >= 2`, round to nearest even, canonical NaN, subnormals (`SvGolf.IEEE754.divide`); bans `/ % **` | a word-level netlist of 34 sites (linear normalizer and `P + 2` restoring steps as generate families), Verilator-validated on all 66 formats with `W + P <= 14` and both 2^32-pair formats and **proved for every format** (`tasks/fdivp/README.md`; one self-contained proof over `LeanModels.Sv.Lib`: the spec's facts, the certificate, the math layer, the glue `Glue.chain`, `OutN_fdivBits`); binary16 is the instance `(5, 11)` (the former 16-bit task, removed 2026-11-03, is folded in): par, restoring division; entries: the fragment-friendly D2 (`tests/fdivp/baselines`), a second proved reference, a Newton-Raphson divider (a logarithmic number of Newton steps over the run-time `*`), not competitive, and a third, a radix-4 SRT divider adapted from CORE-V Wally (carry-save remainder, digit selection by table constants, on-the-fly conversion), the fastest | par 9675.5296 um^2, 37984 ps; 2166.076 GE, depth 289 at `(5, 11)` (Newton 33824.9408, 40031; 7892.452, 252; SRT: 12356.8512, 27592; 2787.652, 189) |
| `aes_sbox` | the AES S-box (FIPS 197 Section 5.1.1), `y = S(x)` on 8 bits, defined algebraically (inverse in GF(2^8), then the affine map), fixed size; NO operator banned; the post-synthesis check is exhaustive (all 256 inputs) | par: a proved 256-entry `case` table; entries: the Boyar-Peralta 113-gate circuit, validated (Verilator, all 256 inputs; gate for gate against the authors' netlist file), scored and **proved** (113 plain sites: `sv_structure` and `sv_equations` decide the obligations of a flat netlist instead of normalising them, `PROVING.md` section 12), and the proved depth-16 Boyar-Peralta circuit (`tests/aes_sbox/baselines`) | `case` table (par) 3445.8048 um^2, 2288 ps; 786.894 GE, depth 11 (fixed size). 113-gate circuit 892.1056, 4297; 200.986, 21. Depth-16 circuit 952.1632, 3670; 216.322, 18 |
| `clmul` | N-bit carry-less multiplier (product of polynomials over GF(2)), `p = a (x) b` on `2N-1` bits; bans run-time `+ - *` | the N x N AND/XOR array (`mul_n`'s shape without carries), validated (Verilator, exhaustive to `N = 8`; the Lean spec equals the oracle on every pair to `N = 7`), scored and **proved** for every `N` (`sv_structure`/`sv_equations`/`sv_cover`/`sv_bridge`, 206 code lines, `solution` stage 7.7 s), par; proved schoolbook-tree and Karatsuba designs, entries (`tests/clmul/baselines`); 18 real-world styles under `tests/clmul/attacks` (`tasks/clmul/README.md`, "How people write clmul") | 3429.5392 um^2, 1114 ps; 772.267 GE, depth 6 at `N = 16`; Karatsuba (`kara_lv`, 4-bit base) 2732.6208, 1810; 616.626, 8 |
| `arbiter` | a fair N-client arbiter, CLOCKED and REACTIVE (`ReactTask`, kind `react-family`): per cycle at most one grant, only to a requester, someone whenever anyone requests (G1 to G3), no grant out of reset (G0), and a client that requests `N` cycles in a row granted within them (G4, `K = N - 1`, tight), from every power-up state, Moore outputs, no environment assumption; every `N >= 1` with `N*N < 2^31`; bans `/ % **` | a registered mask round-robin (own code), **proved** for every `N` through `ReactTask.satisfiedAt_of_rank` (an invariant and a rank: `PROVING.md` section 20); the adapted OpenTitan `prim_arbiter_tree` behind an output register and a rotating priority by simulation (`tests/arbiter/designs`); 17 attacks (`tests/arbiter/attacks`); listed and ranked, par the reference's record (`tasks/arbiter/README.md`) | 769.488 um^2, 2826 ps (the register-to-register period, one decision per cycle; 16 flops); 188.979 GE, depth 17 at `N = 8`. OpenTitan tree 668.1 um^2, 1454 ps (an earlier flow version, not proved) |
| `matmul` | N x N signed matrix multiplication, CLOCKED with a declared latency (`TxTask`, kind `tx-family`): `C = A * B` over `W`-bit two's-complement entries, every sum wrapping at `AccW` bits, behind a start/done handshake, from every power-up state, Moore outputs; every `N, W, AccW >= 1` with `N*N*W < 2^31`, `N*N*AccW < 2^31`; bans `/ % **` | `N*N` parallel multiply-accumulate units and one step counter (own code), latency `N`, **proved** for every point through `TxTask.satisfiedAtV2_of_phases` (a phase model: `PROVING.md` section 19); 7 attacks (`tests/matmul/attacks`); listed and ranked (decided 2026-11-08), par the reference's record (`tasks/matmul/README.md`) | 87173.6064 um^2, 4 x 10696 ps = 42784 ps (the latency in cycles x the register-to-register period; 802 flops); 20783.15 GE, depth 61 at `(N, W, AccW) = (4, 8, 32)` |
| `sorter` | a streaming sorter of N unsigned W-bit values, CLOCKED with a declared latency (`StreamTask`, kind `stream-family`): the values in on `N` consecutive `in_valid` cycles, the same values out ascending (duplicates kept) on `N` `out_valid` cycles, from every power-up state, Moore outputs; every `N, W >= 1` with `N*W < 2^31`; bans `/ % **` | an insertion-cell array adapted from andrewpeck/cell-sort (MIT), latency `2N`, **proved** for every point through `StreamTask.satisfiedAtV2_of_phases` (`PROVING.md` section 19); 8 attacks (`tests/sorter/attacks`); listed and ranked (decided 2026-11-08), par the reference's record (`tasks/sorter/README.md`) | 5512.7872 um^2, 16 x 2523 ps = 40368 ps (81 flops); 1288.819 GE, depth 15 at `(N, W) = (8, 8)` |
