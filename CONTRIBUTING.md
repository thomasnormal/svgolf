# Contributing to svGolf

For a competitor or an outside contributor. svGolf is a zk.golf-style competition for SystemVerilog: for each task
you write a circuit, prove in Lean that it meets the task's trusted statement, and are scored by a pinned synthesis
flow weighed on the sky130 standard cells: area in um^2 and time in ps, the ranked score (decided 11/03), with area in
NAND2 gate equivalents and depth as extra columns; `score/PPA.md`, "Reproduce a score", gives every number again. [README.md](README.md) has the rules and the checker in full;
this page is the route through them: how to play, how to extend the tool when a design needs something it cannot
read yet, and what you may and may not touch.

| you want to | read |
|---|---|
| submit a design and a proof for a task | sections 1 to 6 |
| make ls-sv (the SystemVerilog semantics) understand a construct | section 7 |
| change a task statement, the checker or the scoring | section 8 |
| run the regression | section 9 |

Every command and path below exists in this tree (checked when this page was written); numbers come from
README.md or PLAN2.md unless stated.

## 1. What you need

* A clone of this repository (it uses lean-surfaces' `LeanModels.Sv` library, the Lake git dependency
  `lean-models` at the revision `lakefile.toml` pins).
* **Python 3.12** (`python3.12`; the extractor needs `pyslang`), **Yosys 0.53** (the scores are comparable only
  when the pinned flow's hashes agree: `tests/expected.json`, key `flow`), **Verilator 5** (the post-synthesis
  check), a C++ compiler and `make`.
* **Lean** through elan, toolchain `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Build the trusted part
  once: `lake build SvGolf tasks svgolf-eval` (`check.py` does this itself in its `trusted` stage unless
  you pass `--no-trusted-build`). No Mathlib is built; a solution that imports it needs the Mathlib build
  (`.lake/packages/*/.lake/build`, from `lake exe cache get`; README.md "Mathlib in submissions") to be present.
* An operating-system sandbox mechanism: macOS `sandbox-exec` (always there), Linux `bubblewrap` (`bwrap`, with
  unprivileged user namespaces). `check.py` runs the submission's Lean, the extractor, Yosys and Verilator inside it
  by default (`--sandbox auto`, says on stderr when it cannot); `--sandbox require` makes its absence an error, as
  for official runs (README.md, "Sandbox"). It cannot nest on macOS: inside another Seatbelt sandbox it is "not available".
* A machine with memory to spare: the reference machine is a 16 GB laptop and Lean jobs are heavy. See section 9
  for the etiquette.

## 2. Pick a task and read its README

| task | status | kind | banned operators | proof time limit | proved references |
|---|---|---|---|---|---|
| `_example` | ready | every `N` | `+ - * / % **`, run-time `< <= > >=` | 300 CPU s | `band`, `band_lp` |
| `add` | ready | every `N` | `+ - * / % **`, run-time `< <= > >=` | 300 CPU s | `add_n`, `add_proc`, `add_proc_m`, `add_mux`, `add_n_byhand` |
| `mul` | ready | every `N` | `+ - * / % **`, run-time `< <= > >=` | 300 CPU s | five (`mul_n` .. `mul_tree_h`) |
| `aes_sbox` | ready | fixed size, 8 bit | `/ % **` (every task bans them) | 300 CPU s | `sbox_bp` (113 gates) |
| `clmul` | ready | every `N` | `+ - * / % **`, run-time `< <= > >=` | 300 CPU s | `clmul_n` (the array without carries) |
| `fdivp` | ready | every `W, P` (two parameters; binary16 is `(5, 11)`) | `/ % **` | 300 CPU s | `fdivp` (a word-level netlist of 34 sites) |
| `arbiter` | ready | clocked, reactive: every `N` (`N*N < 2^31`) | `/ % **` | 300 CPU s | `rr_mask` (a registered mask round-robin) |
| `matmul` | ready | clocked, transaction, a declared latency: every `N, W, AccW` (`N*N*W < 2^31`, `N*N*AccW < 2^31`) | `/ % **` | 300 CPU s | `matmul_g1` (`N*N` multiply-accumulate units, latency `N`) |
| `sorter` | ready | clocked, stream, a declared latency: every `N, W` (`N*W < 2^31`) | `/ % **` | 300 CPU s | `sorter_ins` (an insertion-cell array, latency `2N`) |

(from each `tasks/<name>/task.json`; a task that bans `+` or `-` also bans the run-time ordering comparisons
`< <= > >=`, decided 2026-11-05: Yosys builds each as its own adder, an `$alu`; equality and comparisons over
parameters stay allowed.) Start with `_example`, then `add`: a one-line function, a complete
for-every-width proof to start from, and an (area, delay) frontier to golf. `fdivp` is a far goalpost (proved for every format, but a hard
first task). `arbiter` is the first clocked task: a controller whose statement holds on every cycle of every input
trace, not a function. Its README's "Start a new design" and PROVING.md section 20 are the route; its score is the
area, flip-flops included, times the register-to-register clock period, one decision per cycle.
`matmul` and `sorter` are clocked with a latency: the proof also proves the cycle count the solution declares,
and the score is the area times that count times the clock period. Their READMEs' "Start a new design" and
PROVING.md section 19 are the route; there `check.py --unproved` also takes `--latency n`, the latency you mean
to claim.

Read, in this order: `tasks/<name>/README.md` (the module header you must implement, the statement in words, the
banned operators, the scoring point); `tasks/<name>/Spec.lean` (the TRUSTED statement; the README is a gloss of it);
`reference/` (a proved design and its proof: the model for yours); `oracle.py` (a Python function of the task, used for
an advisory check, not trusted). `task.json` fields are documented in README.md, "A task directory". For golf headroom,
the README's "Leaderboard" table lists scores of designs that are not records (prefix adders, Dadda trees).

## 3. The edit-check loop with `check.py`

Run from the repository's root. The module header, port names, order and widths must be the task's exactly.

| command | what it does | cost |
|---|---|---|
| `python3.12 check.py tasks/add solution.sv --unproved` | every stage that needs no proof (source gate, extraction, banlist, 4-state rules, the generated `Submission.Design`, score, post-synthesis); stops at the pseudo-stage `unproved`; never accepts | about 15 s |
| `... --unproved --tactics` | also asks the `sv_comb` tactics whether they can read the design (`tactics.in_fragment`, with the refusal message); advisory | +2 s, one Lean job |
| `... --unproved --stage-dir DIR` | keeps the staged design, so you can compile probe files against it (`sv_structure?`, `sv_equations?`) | |
| `python3.12 check.py tasks/add solution.sv Solution.lean` | the whole check, post-synthesis in `light` mode | about a minute |
| `... --postsynth full` (or `SVGOLF_POSTSYNTH=full`) | the post-synthesis stage on the task's whole vector budget: what verification and the leaderboard run | longer, per task |
| `... --keep` / `--stage-dir DIR` | the result's `dev_hint` is the command that recompiles only your `Solution.lean`: the fast inner loop for the proof | |
| `python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped [--path]` | the golfing inner loop: the ranked numbers alone (sky130 um^2 and ps, whose product is ranked, with the GE columns; `--path` the critical path; the source gate and Yosys, no banlist, no ls-sv, no Lean; needs the pinned liberty, `--fetch-liberty`) | about 2 s |
| `python3.12 score/score.py solution.sv --task tasks/add` | the GE columns alone (Yosys, no Lean) | seconds |
| `python3.12 check/postsynth.py --task tasks/add solution.sv` | the post-synthesis check alone, at any `--point N=32` | needs `svgolf-eval` built |

`check.py` prints JSON: `accepted`, the failing `stage` and `errors`, `stages`, `score`, and the advisory
`warnings` (a functional mismatch against the task's oracle, with the first failing input), `dev_hint`, `tactics`.
The stages in order are `imports`, `source`, `extract`, `banlist`, `fourstate`, `trusted`, `design`, `solution`,
`integrity`, `comparator`, `leanchecker`, `score`, `postsynth`, `ppa` (README.md, "Checking", has one line per stage).
A functionally wrong design passes everything before the proof and then fails it with an opaque type mismatch, so
run `--unproved` first: it compares your design with the oracle. Environment: `SVGOLF_LEAN_WRAP` (a prefix for every
`lake`/`lean` call), `SVGOLF_PYTHON`, `SVGOLF_POSTSYNTH`, `SVGOLF_SANDBOX` (`off`, `auto`, `require`; the flag `--sandbox`
wins). The checker puts your Lean file in a sandbox that denies the network, every read outside its inputs, every
write outside one output directory and every other program, so a proof that needs the host (a file, a socket) cannot
be checked: it fails at `solution` with "operation not permitted". `lake env lean` for your own proof loop (the
`dev_hint`) is NOT sandboxed.

## 4. Writing the proof

[PROVING.md](PROVING.md) is the guide; read its sections 0 to 2 and 4 before anything else (for a clocked task:
section 0, then section 19, or 20 for `arbiter`), and do not copy it. It
covers the loop, the four obligations of a settled-state proof, what the tactics accept and refuse, and when to fall
back to a by-hand proof. Two complete tactic proofs are the models: `tasks/add/reference/add_n.lean` (every `N`, 84
code lines) and `tasks/aes_sbox/reference/sbox_bp.lean` (a fixed-size flat netlist). The whole file is a submission
`Solution.lean` that imports `Submission.Design` and proves `theorem Submission.solution : Submission.Goal`
(`Submission.Goal Submission.lat` for `matmul` and `sorter`, which declare a latency: README.md, "Submitting").

The shape of an `add_n`-style proof (a family, every `N`):

```lean
-- (illustrative: the structure of tasks/add/reference/add_n.lean)
theorem add_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)                          -- small arithmetic goals, one tag each
theorem add_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by sv_interface
theorem solution : Goal := by
  intro N hN
  obtain ⟨hc, ha⟩ := add_struct N hN.1
  refine CombTask.satisfiedAt_of_comb (add_interface N hN.1 hc) hc ha ?_
  intro st heqs hs v hv                              -- a settled state with known inputs
  ...                                                -- unpack the inputs from hv
  sv_equations                                       -- eq_c_1 .. eq_cout_1, known_*, then obligations
  · exact add_final ..                               -- YOUR arithmetic lemma: the only mathematics
  all_goals first | (intros; omega) | sv_cover | (refine inKnown_ofBitVec hA ?_; omega) | fail "unclosed"
```

The shape of a flat-netlist proof (fixed size, no loop, no parameter: `aes_sbox`):

```lean
-- (illustrative: the structure of tasks/aes_sbox/reference/sbox_bp.lean)
theorem bp_struct : CombDesign design.sem ∧ Acyclic design.sem := by
  sv_structure (rank := rippleRank (fun p => bpRank.getD p 0) (fun _ _ _ => 0))   -- decided: no goal left
theorem bp_interface (hc : CombDesign design.sem) : task.Interface 0 design.sem := by sv_interface
set_option maxHeartbeats 1000000 in
theorem solution : Goal := by
  obtain ⟨hc, ha⟩ := bp_struct
  refine CombTask.satisfiedAt_of_comb (bp_interface hc) hc ha ?_
  intro st heqs hs v hv
  ...
  sv_equations                    -- main goal and inputsKnown only; width and cover are decided
  · ... gok_chain eq_y14_1 ... eq_y_8       -- the 113 equations by stable name, into ONE induction
  case inputsKnown => exact inKnown_ofBitVec hv (by omega)
```

Points that save time: the rank is a site's depth in the dependency graph; keep the arithmetic as a lemma stated
with exactly the printed `eq_*` as hypotheses; use the stable names `eq_<signal>_<k>`; if `--tactics` says
`in_fragment: false`, the design is legal but the tactics cannot read it, and a by-hand proof (PROVING.md section 5) or
a different design is the route; if you need a construct the tactics do not read, section 7. Axioms of a proof must
be the three standard ones: end the file with the `#print axioms` check the references carry.

## 5. The rules that bite

(README.md, "Rules", is the full text.)

* **Proofs are symbolic and parametric.** When a task is `N`-bit the statement covers every `N` in its range and so
  must the proof: induction on bit indices, `BitVec` algebra, the tactics. Checking a few `N` is not a proof.
* **No `sorry`/`admit`, no new axioms.** Only the task's `allowed_axioms` (normally `propext`, `Classical.choice`,
  `Quot.sound`), no `extern`/`implemented_by`. The comparator walks the dependencies through kernel values.
* **No `native_decide`, no `bv_decide`.** The checker rejects `native_decide` outright, and `bv_decide` because it
  runs an external SAT solver, which the checker does not support (decided 2026-11-01; README.md, "`bv_decide`":
  a task's `allow_bv_decide` is `false`, `true` is an infrastructure error; the comparator's re-verification of its
  certificate is kept, dormant). `decide +kernel`, `omega`, `simp` or a symbolic proof are the tools for fixed-size
  subgoals. In an ls-sv feature PR (section 7) the repository ruling applies (`AGENTS.md`): not banned,
  discouraged, in the order symbolic proof, kernel `decide`, decide-class tactics, and a use carries its
  `#print axioms` and a one-line justification at the use site.
* **Imports:** `Init`, `Std`, `Lean`, `LeanModels.Sv.*`, `SvGolf.*`, `tasks.*`, plus `Submission.Design`, and
  Mathlib with the packages it imports (`Mathlib`, `Batteries`, `Aesop`, `Qq`, `ProofWidgets`, `Plausible`,
  `ImportGraph`, `LeanSearchClient`; README.md, "Mathlib in submissions"); nothing else (no `Examples.*`, no
  `LeanModels.Python.*`). One `.sv` and one `.lean` file.
* **The proof time limit** is 300 s of CPU time for every task (the Lean process's user + system seconds, decided
  2026-11-05, the value 2026-11-06: CPU seconds count every elaboration thread; a wall-clock backstop of 5 times it stops a proof that waits), a ceiling that does not follow the
  references. A reference over it
  is a defect of that proof or of the scaffolding, and that is what gets fixed; the target is at most 150 CPU s.
  `python3.12 score/time_limits.py` prints the table. A design much heavier than the references can overrun and is
  rejected at `solution`.
* **Banned operators are per task** (the operator that IS the task, and whatever Yosys turns into the same cell).
  Constant arithmetic (parameters, genvar steps, index arithmetic) is always allowed.
* **One program for both tools.** The proof reads the design through slang, the score reads it through Yosys; the
  source gate makes them read one text: no preprocessor directives other than `` `timescale `` and
  `` `default_nettype ``, no attributes, no tool pragma comments, no `unique`/`priority`, no `x`/`z`/`?` digits in a
  literal (except casez/casex item wildcards).
* **No `x` or `z` may arise** (the `fourstate` stage): no unknown constant, no select out of its range, no undriven net,
  no conflicting drivers, no logic loop.
* **The sky130 netlist must be electrically legal** (the `ppa` stage, `sky130_a0_v3`). The ranked sky130 area and delay are
  taken on the scored netlist after the checker's own repair, BUFFERING ONLY: every net over its driver's limits (a load over
  `max_capacitance`, a transition over `max_transition`, a load past the timing tables) gets a balanced tree of `buf_*` cells,
  inputs (each driven by the task's input drive), flop Q nets and nets driving output bits (10 fF per bit) included, and the constant tie
  cell is replicated; no cell is resized, so a legal netlist keeps its area. A netlist the repair cannot make legal is
  rejected at stage `ppa` with the net named (an input by its port bit, a register by its Q net, what it drives as output bits
  or pins); none is known on sky130. The trees are built to their limits, not for speed: a net with a heavy load is slow, and
  if you want it faster, restructure it yourself (a register or a gate per group of loads). `score/PPA.md`, "The repair and
  the legality check".
* **The inputs are driven by the task's input drive** (`sky130_a0_v3`): `task.json` `input_drive`, one of the cells of
  `score/ppa_pins.json` `timing.input_drive.allowed` (buffers, inverters, a register's Q), default
  `sky130_fd_sc_hd__buf_8` (every task today). A NEW task names its drive only when its inputs come from something other
  than an on-chip bus or register (state the reason in its README); a name outside the list fails `tests/run.py`'s layout
  step and is an infrastructure error in `check.py`. Changing the default or the list changes `ppa_version` and every golden.
  The record's `ppa.setup.input_drive` names it; `score/PPA.md`, "The input drive". To reproduce any recorded number by
  hand: `score/PPA.md`, "Reproduce a score".
* **Post-synthesis is `light` by default and `full` for anything official.** The check simulates ls-sv and the scored
  netlist on the same vectors. `light` is a deterministic subset of `full`, so a light rejection is always a full
  rejection; `leaderboard.py add` and `verify`, the regression and competition runs use `full`. A light result is not
  an official one.
* **A disagreement between ls-sv and Yosys on a design is a bug report we want**, not an exploit; send the failing
  vectors the checker prints.

## 6. The leaderboard and the record file

```bash
python3.12 leaderboard/leaderboard.py add --task add --player YOUR_HANDLE --assisted-by "TOOL OR MODEL" \
    --sv solution.sv --lean Solution.lean      # runs check.py in FULL mode; writes leaderboard/data/add/
                                               # (what a pull request adds); --data-dir DIR: a private trial
python3.12 leaderboard/leaderboard.py board  --task add            # the table by area x time (md or json)
python3.12 leaderboard/leaderboard.py pareto --task add            # the (area, time) frontier, for exploring
python3.12 leaderboard/leaderboard.py verify --offline            # hashes and area arithmetic, milliseconds
python3.12 leaderboard/leaderboard.py verify                      # also rescores (seconds, no Lean)
python3.12 leaderboard/leaderboard.py verify --full               # re-runs check.py on every stored pair
```

There is **no submission server yet**: `add` writes a record on your machine and sends nothing. A record is
self-verifying through `verify --full`, which re-runs the whole check (the faster levels do not re-derive a clocked
record's latency from its proof), so a pull request carrying the record directory is a possible hand-off, but how
records reach a public board is an open decision (README.md, "Leaderboard"); until it is taken, use `--data-dir` so
your records stay out of the repository's own.

A record is one JSON file, `data/<task>/<record_hash>.json`, with your `.sv` and `.lean` copied next to it
(`leaderboard/README.md` has the full schema, `svgolf-leaderboard-record/1`):

| key | meaning |
|---|---|
| `task`, `player`, `submitted_at` | the task, your handle (`[A-Za-z0-9][A-Za-z0-9._-]{0,31}`), the date |
| `assisted_by` | free-text list of tools and AI systems that helped; empty means unassisted (`--unassisted` ranks only those) |
| `files` | base names and sha256 of the exact bytes of both files; `canonical_sha256` of the source gate's text |
| `score` | the extra GE columns: `area_mge` (integer milli-GE, exact), `area_ge`, `depth`, `num_gates`, `gates`, the scoring point, `rtlil_sha256` |
| `ppa` | the ranked score: the sky130 A0' columns, `area_e4um2_sky130` (1e-4 um^2) and `delay_ps_sky130` (a clocked record: `score.time_ps`, cycles x period), with the hashes they were weighed under and `setup.input_drive` |
| `checker` | who judged: the svgolf and proglib (formerly lean-surfaces) revisions (`svgolf_revision`, `lean_surfaces_revision`), Lean toolchain, Yosys and Verilator versions, hashes of the pinned scripts, the GE table and the checker's own files |
| `proof` | axioms, `build_seconds`, code `lines`, `imports`, `tactics` found in the file |
| `postsynth` | point, vectors, mode (`full`, or `light` for a marked local record), seed |
| `record_hash` | sha256 of the canonical JSON of the rest; it is the file name |

The ranked number is area x time, the sky130 A0' area times the time (A0' decided 11/03, the product 11/05), lower is
better; `leaderboard.py board` and `export` list the records by it (decided 2026-11-05; `#` is the rank, equal products
share one, listed as the site lists them), with the Pareto layer of the two factors, the GE area and depth as extra
columns (`pareto` prints the frontier, an exploration view, ties kept); no depth budget unless a task
sets one. Records are append-only and tamper-evident, not tamper-proof. A record made under another version of the
pinned flow, the sky130 pins or the task's input drive, or one without sky130 columns, is listed as "not ranked". To
reproduce a recorded number bit for bit: `score/PPA.md`, "Reproduce a score".

## 7. Adding an SV feature to ls-sv by pull request

Contestants may add a construct ls-sv does not read yet, and **the maintainers approve every such PR**. Because the ls-sv
semantics defines what "the design" means in a task's statement, a feature is not done when it parses: it counts as
supported only when all of the following exist (PLAN2.md, track T2). The precedents to read are `git show --stat
d9eba5b2` (binary `~^`, 35 files) and `5a4c4cc5` (genvar step `i = i + 1`).

| step | what | where |
|---|---|---|
| 1 semantics | the symbolic-tier semantics of the construct, with its width, signedness and four-state rule stated and cited | `LeanModels/Sv/`; the tier's rules are `docs/sv-charter.md`, and a feature gets its own `docs/sv-<feature>.md` |
| 2 extractor lowering | slang node to envelope node, or a lowering to nodes that already exist; a loud `Unsupported` for what you do not handle; unit tests | `extractors/sv/extract.py`, `extractors/sv/test_*.py`, `docs/sv-envelope-schema.md` |
| 3 differential cases | rows in `harness/sv/cases2.json` with a `measured` field saying what each simulator printed, small sources under `Examples/system-verilog/sem2/<name>/` (with the generated envelope `.sv.json` and an `agree.lean` checking the loaded design); include `x`/`z` stimulus whenever the rule has a four-state half | `harness/sv/cases2.json`, `Examples/system-verilog/sem2/` |
| 4 the Xcelium pin | Xcelium is the reference simulator, pinned as data so that nobody needs it to run the harness: refresh the rows' traces on an Xcelium host through `harness/sv/xcelium_batch.py` (`prepare`, then `run`; one `xrun` at a time), commit the diff of `harness/sv/xcelium_golden.json`; `diff_test2.py --golden --case NAME` then reports `XREF-MATCH`. Procedure and etiquette: `docs/sv-xcelium-reference.md`. The pin needs access to the maintainers' Xcelium host; the process for an outside contributor without it is not written down, so list the rows that still need a pin in the PR and let a maintainer decide how to run them | `harness/sv/` |
| 5 a small proof | an `Examples/system-verilog/<name>/` proof that uses the construct end to end (the `xnor_n` proof for `~^`) | `Examples/system-verilog/` |
| 6 the refusal register | the construct is a row of `docs/sv-refusals.json` (category `later`): narrow its `trigger` to what is still refused and add a `notes` line saying which of steps 1 to 5 have landed; then `python3 tools/gen_sv_refusals.py --write` regenerates `docs/sv-refusals.md` (svGolf's `REFUSALS.md` is what the register at the pinned revision renders, `tools/gen_sv_refusals.py --emit-svgolf`), and `python3 tools/gen_sv_refusals.py --check` must be green (it also fails if code and register disagree) | `docs/sv-refusals.json`, `tools/gen_sv_refusals.py` |
| 7 docs | an entry in `docs/sv-changelog.md` (the next free number; the file is edited by several people, so check the top when you push), a feature note if the construct is large (`docs/sv-xnor.md` is the model) | `docs/` |

Rules for the PR: touch only ls-sv paths (`LeanModels/Sv`, `extractors/sv`, `harness/sv`, `docs/sv-*`,
`Examples/system-verilog`); changes to svGolf go to this repository, separately. Build the modules you touched and the Examples that
import them, and run the harness rows you added. Never whitelist a differential mismatch to make it pass: an `XREF-DIFF`
is a model bug to report (a recorded tool split is a declared disagreement, `docs/sv-oracle-disagreements.md`,
which the maintainers decide), and where Xcelium departs from explicit LRM text and the other tools follow the LRM, the
policy is to refuse loudly, not to follow Xcelium (`docs/sv-xcelium-audit.md`). Commit
subjects are short and imperative, one logical change per commit; the PR says what, why, and how to test it.

## 8. Trusted and untrusted, and changing the trusted parts

| part | status | where |
|---|---|---|
| the task statements | **trusted** | `tasks/<name>/Spec.lean`, the statement helpers `SvGolf/Task.lean`, the IEEE 754 spec `tasks/fdivp/IEEE754.lean` |
| the checker and the scoring flow | **trusted** (a tripwire protects it during a check; its file hashes are in every record) | `check.py`, `check/` (including the sandbox, `check/sandbox/`), `score/` (`ge.json`, `canon.ys`, `svgolf.ys`) |
| the ls-sv semantics and extractor | **trusted by construction** (they define the meaning of a design; the backstops are the differential harness and the post-synthesis check) | `LeanModels/Sv/`, `extractors/sv/` |
| proof helpers, the `sv_comb` tactics, `CombLib`, the proof library `LeanModels.Sv.Lib` | untrusted; they only produce terms the kernel re-checks | `SvGolf/Comb.lean`, `LeanModels/Sv/Comb*`, `LeanModels/Sv/Lib/` |
| references, oracles, tests | untrusted (a wrong oracle gives a wrong warning, never a wrong verdict) | `tasks/*/reference/`, `tasks/*/oracle.py`, `tasks/*/spec_validate/`, `tests/` |

A pull request to a trusted file is a **statement change**, and the practice of this repository is:

* it is reviewed and approved by the maintainers, and prepared as a diff or a draft, never edited in place without that
  (PLAN2.md, risks; `design/fdiv-param/Task.lean.patch` is the example);
* a new or changed `Spec.lean` comes with a written review for the maintainers (the precedent is `tasks/aes_sbox/REVIEW.md`:
  the statement in words, its sources, the cheating surfaces and their defences), non-vacuity checks (the input names are distinct; a witness in
  range; golden values by `decide`), refutations of the wrong designs (`tests/<task>/negative/Refute.lean`), and its
  entries in `tests/expected.json`;
* a change to the scoring flow or the checker moves hashes: scores in `tests/expected.json` and every README that
  quotes one change with it (`python3.12 tests/run.py --update-scores`, then review the diff), and the records on the
  board are re-issued against the new files;
* do not edit checker files while a regression is running (the tripwire rejects the run: `check/sandbox/**` is
  fingerprinted too);
* a new `subprocess` call in the checker, the scorer or the post-synthesis stage that touches submitted text goes
  through `sandbox.run` (`check/sandbox/`) with a `Spec` that lists what it may read and write, and any other call
  passes `env=sandbox.scrubbed_env()`: `tests/sandbox/test_env.py` fails on a call that inherits the checker's environment.

A new task is a directory `tasks/<name>/`, a directory `tests/<name>/`, an entry in `tests/expected.json`, and the
imports in `tasks.lean`/`tests.lean` (README.md, "A task directory"); `tests/run.py` step `layout` checks it all.

## 9. The regression, and the Lean slot

```bash
python3.12 tests/run.py                                   # everything; exit 0 iff all pass
python3.12 tests/run.py --only add --skip attacks         # one task, a step skipped
python3.12 tests/run.py --skip build,modes,references,drafts,negatives,baselines,validate,attacks   # no Lean
python3.12 tests/run.py --full                            # with the heavy simulation plans (hours)
```

Steps: `layout`, `build`, `unit`, `leaderboard`, `modes`, `canon`, `references`, `drafts`, `negatives`, `baselines`,
`validate`, `attacks`, `sandbox`. `--sandbox {off,auto,require}` is handed to every `check.py` call (default `auto`; the
`sandbox` step always uses `require` and skips, with a message, where there is no mechanism). The no-Lean selection above runs `layout`, `unit`, `leaderboard` and `canon`: 44 checks in
about 75 s. The whole suite is 386 checks and took 3154 s on the last merged tree (PLAN2.md): plan for most of an
hour. The unit tests need no Lean and run directly: `python3.12 score/test_score.py`, `score/test_srcgate.py`, `tests/checker/test_advisories.py`,
`tests/leaderboard/test_leaderboard.py`, `tests/imports/test_allowlist.py`.

**Lean-slot etiquette.** At most one Lean or `lake` process at a time on a shared or small machine; it is the one
scarce resource (the reference machine is a 16 GB laptop). Run with `LEAN_NUM_THREADS=2` and `nice -n 19`,
prefer `lake build <Module>` or `lake env lean <file>` to a full build, and put your queueing wrapper in
`SVGOLF_LEAN_WRAP`: `check.py`, `leaderboard.py` and `tests/run.py` call it themselves, so run `tests/run.py` WITHOUT
the wrapper around it. An edit of a `LeanModels.Sv` tactic module rebuilds everything that imports it, so batch such
edits. Do not rebuild the library while a `check.py` run is going: its integrity tripwire sees the changed oleans
and rejects the run (rerun it).

## 10. Where the documents are

| document | what |
|---|---|
| [README.md](README.md) | the rules, the layout, the checker stages, scoring, the banlist, the leaderboard, the tests |
| [PROVING.md](PROVING.md) | how to prove a task with the `sv_comb` tactics; what they accept and refuse |
| [REFUSALS.md](REFUSALS.md) | every refusal the checker and ls-sv make, why, and what to write instead (generated from `docs/sv-refusals.json`) |
| [PLAN2.md](PLAN2.md), [PLAN.md](PLAN.md) | the lead's plans: work packages, decisions taken, open questions |
| [leaderboard/README.md](leaderboard/README.md) | records, verification, boards |
| `tasks/<name>/README.md`, `REVIEW.md` | a task's text, and the review of its trusted statement |
| `design/` | design notes (always-comb, fdiv-param, ppa, sequential, week-2 tasks, word-level operators) |
| lean-surfaces' `docs/sv-*.md` | the ls-sv documents: charter, envelope schema, refusal register, Xcelium reference, changelog |
