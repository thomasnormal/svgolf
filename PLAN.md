# svGolf — 7-day plan (2026-10-27 → 2026-11-02)

> **Week 2 (10/30 to 11/5): see [PLAN2.md](PLAN2.md)** (better tactics, proof API and speed, wider SystemVerilog in ls-sv,
> new tasks and references, the parametric floating-point divider). This file records the first seven days.

svGolf is a zk.golf-style competition for SystemVerilog. Players write a
circuit, prove it correct in Lean against a trusted spec under the ls-sv
semantics, and are scored on synthesized area and depth.

Work happens on branch `svgolf-prep`, which is based on `github/master`.
Status marks: `[x]` done, `[~]` in progress, `[ ]` to do.

## Decisions so far

- **Layout.** Golf code (scoring, checker, challenges, specs) lives in
  `svgolf/`. General semantics and proof work lives in `LeanModels/Sv/`.
- **No Xcelium dependency (10/28).** Access isn't guaranteed, so the
  harness and checker rely on open tools (Verilator, Yosys; Icarus is an
  optional witness).
  Xcelium on a licensed host is fine for one-off checks.
- **Integrate small and often (decided 10/29).** "Keep merging/pushing/pulling
  regularly, so you can work together with the other agent, rather than
  stepping on each other's toes." The daily-rebase rule of 10/28 lapsed, and
  the branch fell 234 commits behind. From now on: fetch at the start of
  every work block and after every workflow; integrate each verified ls-sv
  change into `github/master` in the isolated worktree and push without
  force; then merge master back into `svgolf-prep`. A session cron reports
  divergence every two hours. `svgolf/` stays off main.
- **Keep svGolf separate (10/28).** No svGolf entries in lean-surfaces'
  `lakefile.toml` or `LeanModels.lean`. `svgolf/` may move to its own
  repository later, so it should only depend on lean-surfaces like an
  outside user would.
- **Correctness.** Lean proves correctness only. Proofs are symbolic and
  parametric (for all N) wherever the task is n-bit. `bv_decide` is allowed
  for fixed-size subcases under the time limit. `native_decide` is banned.
- **Score.** A pinned Yosys + ABC script, shipped with each challenge:
  - area in NAND2 gate equivalents (from `stat`);
  - depth (from `ltp`);
  - area is scored under a depth budget, or an (area, depth) Pareto
    frontier is kept.
- **Operator banlist, per task.** The multiplier task bans `* + - / % **`,
  because Yosys merges `+` chains into the same `$macc` cell as `*`. The
  floating-point divider bans `/ %`. Most tasks ban nothing.
- **No restrictions beyond the banlist.** Where ls-sv and Yosys disagree, we
  want bug reports. A post-synthesis simulation check surfaces them.
- **Synthesis tool (10/28).** Yosys + ABC for now.
- **Self-reading `always_comb` is refused (10/28).** An `always_comb` that, on
  some path, reads a bit before writing it and then writes that bit later
  on the same path is refused loudly. IEEE 1800-2023 §9.2.2.2.1, Icarus
  and Xcelium give the stale value; Verilator and Yosys give the
  combinational one. No answer is safe, so we refuse.
- **Start small, let tasks drive features (10/28).** The first tasks
  (`_example`, `add`, `mul`, `fdiv16`) are small and solvable, so that they
  run the whole pipeline end to end: spec, reference SV, proof, checker,
  score. Harder tasks come later. Every SV feature a task needs and lacks,
  in ls-sv or in the synthesis flow, becomes a work item. Each task's
  README records what it needed and which gaps it hit.
- **Contestants may add features by PR (10/28).** A contestant who wants an
  SV feature ls-sv lacks can add it in a PR to lean-surfaces, and the maintainers
  approves every such PR. The semantics is trusted, so a feature PR must
  come with differential cases against the open oracles (Icarus,
  Verilator, Yosys `sim`). Any disagreement is either fixed or recorded as
  a declared divergence. The post-synthesis simulation check is the
  per-submission backstop. Leaderboard entries record the lean-surfaces
  revision they were checked against, and a bump re-checks all of them.
- **`unique` / `priority` (10/28).** The source gate refuses `unique`,
  `unique0` and `priority`, because Yosys reads them as don't-cares and a
  violated `unique case` scores 0 GE. Once the post-synthesis check is
  shown to catch that exploit, the refusal is lifted.
- **`unique` / `priority` carry proof obligations (decided 10/28).** In
  ls-sv, a violated `unique` / `unique0` / `priority` claim becomes a
  run-time error, not a warning. It is checked on the settled state, so
  glitches during settling don't count; the LRM likewise defers these
  violation reports. `Terminates2` then makes every proof show that the
  claim holds on every reachable settled state. Today Sem2 runs the first
  match and keeps the qualifier only as data, and the symbolic extractor
  refuses `unique if` and most `unique case` forms. This is work package
  WP5. Once it lands, the gate refusal goes regardless of the
  post-synthesis result.
- **v0 refuses `unique` / `unique0` / `priority` (decided 10/29).** "No
  reason to support fancy keywords like that in v0." The post-synthesis
  check catches only gross violations, by sampling, so the refusal stays.
  WP5 is deferred until after v0.
- **Simulators (decided 10/29).** svGolf simulation testing uses Verilator
  (post-synthesis check, validate scripts), not Icarus. When building ls-sv,
  Xcelium is the reference (run on a licensed Xcelium host),
  and its results are pinned as golden data in the repo so that nothing
  requires access to it. Icarus is an optional 4-state witness. DONE 10/29:
  `svgolf/check/postsynth.py` and every `tests/*/validate` script now simulate
  with Verilator (2-state: the x/z defence stays in the source gate, the
  `fourstate` stage and ls-sv's 4-state outputs; README.md "Rules"). Xcelium:
  all 428 simulated differential rows are pinned from 24.03-s004
  (`harness/sv/xcelium_golden.json`, commit `6dcb5bff`); 392 match the model,
  36 differ, 31 of them partially out-of-range selects. In progress:
  classifying and triaging the differences.
- **Post-synthesis vector salt (decided 10/29).** Competition runs set a
  secret `SVGOLF_POSTSYNTH_SALT` so that players cannot steer the random
  vectors. Local runs keep the empty default and stay reproducible; the seed
  is always recorded.
- **Floating-point spec (10/27).** Every NaN result is the canonical quiet
  NaN (0x7E00 at binary16). All five rounding modes are defined; challenges
  use round-to-nearest-even. Full subnormals, no flush-to-zero. Exception
  flags stay out of version 1.

## Coordination with the off-prem SV agent

- An off-prem SV-lane agent works on the M0/timed tier: `SStmt`,
  `SelfCheck`, the extractor's non-symbolic modes and the census. It pushes
  every finished item straight to `github/master`.
- It has agreed to stay clear of F1/F2/F3/P1/P2.
- The overlap is `extractors/sv/extract.py`, which both lanes edit, and
  `harness/sv/`. Rebase `svgolf-prep` at least daily, and land F-items
  upstream early so the branches don't drift apart.
- We fixed the red `LeanModels/Sv/Load.lean` and the stale `SelfCheck.Out`
  record unpacks. Tell the off-prem agent before pushing, so it doesn't fix
  them in parallel.
- First rebase onto `github/master` done 10/28. The only conflict was in
  the dated entries of `docs/sv-charter.md`; we kept both sides.
- Message ready for the off-prem agent (in the scratchpad as
  `msg-offprem-extractor-flake.md`). It covers a hash-seed-dependent
  extractor test flake caused by module-level state, and our one-line edit
  to `replication/proof.lean` (`fde9ed8e`).

## Day 1 — Tue 10/27

- [x] Design2 proof layer and the for-all-N ripple-adder proof, committed
  (`b5c78289` after the rebase).
- [x] **Track A, fix red master, SV side.** The Python lane is being fixed on
  another machine. Committed as `895cbe7f`, `26552cb2` and
  `779cc6bc` (after the rebase); push awaits the maintainers' OK.
  - [x] `LeanModels/Sv/Load.lean`: add the missing `timedAccesses` arms for
    `distUniformAssign`, `strobe`, `severity` and `fatal`.
  - [x] Update six SV example proofs that still unpacked `SelfCheck.Out`
    with four fields; commit 86b9c5f7 (2026-10-23) added `pending`.
  - [x] Add an `svEnvelopes` input to `lakefile.toml` so SV envelopes are
    tracked by the build.
  - [x] Sweep-build the SV lane: 285 of 295 modules build. The other 10 are
    blocked only by the Python lane (via `import LeanModels`) or by
    in-progress gap work.
- [~] **Track B, ls-sv gaps.**
  - [x] F1: nested selects on multi-dimensional packed arrays (`e39932f7`).
  - [x] F2: part-selects whose base depends on parameters (`e39932f7`).
  - [x] F3: module instances, flattened at instantiation, with a one-driver
    rule (`e39932f7`).
  - [x] P1: concatenation targets in the settle theorem (`e39932f7`).
  - [x] P2: `always_comb` in the settle theorem (`e39932f7`).
  - [x] Round 2 (`2e8c8b28`):
    - unsized integer constants now take the width at the instantiated
      parameter values;
    - explicitly typed nets are refused;
    - literal-label and `$bits` selects are exact or loud;
    - case items are compared at the width of the widest item (§12.5);
    - structs and unpacked arrays whose layout depends on a parameter are
      refused;
    - the one-driver rule covers flat tops and procedural writers;
    - divergence records added.
  - [~] Round 3 (done 10/28, green, not committed): WP4, CX and FOLDS
    implemented. Each lane still had open majors after its repair round,
    two of them regressions round 3 introduced (fold widths for
    self-determined roots and for INT-class targets). Round 4 closes them
    before round 3 is committed:
    - the two fold regressions;
    - a genvar-initializer case where the oracles split and the model
      silently follows Icarus;
    - output-port initializers in non-ANSI form;
    - a declaration initializer next to an `always_comb` writer, which
      Xcelium rejects;
    - wrong claims in the alias docs.
  - [x] Round 4 (done 10/29, green, not committed). It closed those items,
    but its final verifiers found new silent wrong values: one regression
    from round 4's own fix (2-state targets narrower than their
    initializer), typedef widths fixed at the defaults, untyped-parameter
    width splits, and two silent picks newly admitted where the tools
    split (port actuals, unsized signed literals).
  - [x] Round 5 (done 10/29, committed with rounds 3–4 as one ls-sv commit):
    outcome. Green: SV module build, `diff_test2` 626 cases with 0 failures,
    re-extraction 265 same / 0 diff. Not clean: both lanes' second
    verifiers still found silent-wrong shapes (enum members at a context
    width, sized signed literals in a family, port actuals), mostly
    pre-existing at HEAD. The corpus audit (1124 design/top pairs, many
    parameter points, vs Icarus and the Yosys netlist and HEAD) found no
    point that is silently wrong now where HEAD was loud or right, except
    two intended shifts and 12 newly admitted points inside the declared
    Yosys case-item-width reading. It also found 7 silent-wrong designs and
    5 silent-pick classes, 3 and 3 of them new and undeclared, and 1526
    points that are newly loud (coverage cost, for example every untyped
    `localparam K = N - 1`). Open items go to a register, not to another
    round, unless the maintainers decide otherwise.
  - Round 5 design (REFUSAL-ONLY): Fixes may only add loud
    refusals, revert to HEAD behaviour, or correct a value shown equal to
    Icarus, the Yosys netlist and slang on a parameter sweep. No shape may
    become newly admitted. It ends with a corpus audit: every verifier
    repro from rounds 2–5 plus the sem2 fixtures, at many parameter points,
    model vs Icarus vs Yosys netlist (vs HEAD where affordable). Rounds 3–5
    are committed after that.
    - [x] WP4: refuse self-reading `always_comb` bodies, with an
      idempotence theorem; retires round 2's declared divergence.
    - [x] CX: a cross-check at several parameter values. Re-extract at a
      value P and compare the two instantiations at P, so that a value
      computed at the defaults and reused elsewhere refuses loudly. Runs in
      `load_design_sv2` and in the harness, with a hook for the svGolf
      checker.
    - [~] FOLDS: fix the known cases of values computed at the defaults:
      - sign extension (§11.8.2);
      - selects of vector parameters;
      - a guard against ranges that flip or collapse (N = 0);
      - `$high`/`$size` on general ranges.
  - [ ] F3b: recursive module instantiation. Moved to Day 6 (10/29).
- [x] **Track C, floating-point spec** (`2b597c53`). `svgolf/spec/IEEE754.lean`
  defines division for every format, with all five rounding modes and 43
  golden vectors. Five properties are proved for every format: nearest with
  ties to even, the overflow threshold, never NaN on numbers, the sign
  rule, and uniqueness. Validated with 57.4M evaluations against two
  independent stdlib-Python oracles and Lean's float model, and 17.8M more
  by an independent reviewer: 0 mismatches. Checked by
  `svgolf/spec/validate/check.sh`, not by `lake build`, because `svgolf/`
  is not a lake library yet.

## Day 2 — Wed 10/28

- [~] Land Track A. Not done: the full triad
  (`lake build && docs_check && diff_test`) has not been run on the branch.
  The SV sweep, `diff_test2` and `docs_check` ran separately, and the Python
  lane is red upstream. Nothing is pushed, which waits for the maintainers' OK;
  upstream agents push every few minutes. Rounds 3–5 and `svgolf/` are
  uncommitted.
- [x] Rebase `svgolf-prep` onto `github/master` (10/28; all 351 SV modules
  build). Repeat daily: the upstream SV agent is actively changing
  `extractors/sv/extract.py`.
- [~] Start the `svgolf/` skeleton (10/28–10/29):
  - [x] `score/`: pinned Yosys script, GE weight table, `ltp` depth, and a
    report as JSON. Scoring is now two-stage and canonical, so formatting
    no longer changes a score.
  - [x] `score/banlist`: the operator check on the source (pyslang), with a
    backstop in the Yosys script that rejects forbidden `$macc`, `$mul` or
    `$alu` cells. Review holes fixed.
  - [x] `score/postsynth`: simulate the Yosys netlist in Verilator on random
    and edge vectors, and compare against `run2`. A mismatch is logged as an
    ls-sv or Yosys bug report. Done (226 checks pass). The first version
    let a design through with a constant that has some x/z bits in a `case`
    item or `==`; the source gate and the `fourstate` stage now refuse every
    x/z source statically (Verilator is 2-state, so the netlist side cannot
    see an x). ls-sv `run2` is now the bottleneck (131 ms per vector on mul).
- Also done beyond the list (10/28–10/29): the checker with its source
  gate and the undriven-clock fix; tasks `_example`, `add` (proved for
  all N), `mul` (proved for all N) and `fdiv16` (draft, partial proof);
  the `tests/` restructure with `load_sv`; ls-sv rounds 3–5 (round 5 in
  progress).

## Day 3 — Thu 10/29

- [x] Track B: F2 and P2 (round 1, `e39932f7`; hardened by rounds 2–5, round 6
  in progress).
- [x] Checker v0, a Python driver (`svgolf/check.py`, `d7699a3f`; stages: imports,
  source gate, extract, banlist, fourstate, design, proof build, comparator,
  leanchecker, score, postsynth):
  - [x] Run the pinned extractor on the submitted `.sv`; never accept a
    player's `.json`.
  - [x] Build the submission under a wall-clock limit.
  - [x] Run a Lean comparator program (`check/Comparator.lean`) that:
    - [x] checks the challenge theorems' types match the reference exactly;
    - [x] collects axioms against the allowed set. The `bv_decide`
      statement-shape rule was dropped: a verifier showed a hand-declared
      axiom of that shape could forge a proof, so the checker refuses any
      task that enables `bv_decide` until the certificate can be verified;
    - [x] rejects `implemented_by` and `extern`.
  - [x] Then run scoring and the post-synthesis check (Verilator, `24aab622`).
- [x] **`sv_comb`, the ls-sv analogue of `py_vcgen`, for parametric
  combinational designs: BUILT (10/29), on `github/master` since `759422d9`.**
  Design: `docs/sv-comb-design.md` (principles, status, limits), census:
  `docs/sv-comb-census.md`, plain-Lean drafts: `svgolf/design/`. It never
  discharges the player's arithmetic: it reduces the structure and the
  equations of a design to explicit goals. Four stages, all independently
  verified (no blocker or major):
  1. `sv_structure` (+ `sv_structure?`, `using hc`, rank / `lexRank` over
     stable site identities, `sv_rowmajor`): `CombDesign` and `Acyclic` of
     `X.sem N` for every N. Adder: 2 tactic lines each; array multiplier
     (nested loops, 2-D arrays, part-select and concat targets): 2 lines plus
     a 13-line rank key (`maxHeartbeats 400000`).
  2. The x-free knownness theorem (`CombKnownBits`, `CombKnownThm`): proved
     once for the x-free fragment.
  3. `sv_equations` (+ `sv_equations?`, `sv_cover`): the netlist view, the
     pointwise Boolean equations with the SV gate shape preserved, and the
     knownness of every site, derived from the real `sem N`.
  4. Complete for-all-N correctness proofs from the real design: ripple adder
     108 code lines (by hand 537), array multiplier 197 (by hand 1380); the
     tampered adders are accepted by the tactics and rejected by the proofs.
  Limits (honest): flat top; no `always_comb` bodies, instances or
  edge-triggered processes in the fragment; the multiplier's six nested 2-D
  coverage goals are closed by hand (about 65 lines; `sv_cover`'s witness
  search does not reach them); no separate `sv_known` / `sv_bitvec` tactics
  (knownness is delivered inside `sv_equations`); several fragment errors are
  not source-located; signed and 2-state declarations are refused; the tactic
  library is about 6000 lines, written once. Not done and deliberately
  deferred: reflected checkers (principle 9), module instances, `always_comb`.
  - [x] Ideal adder and multiplier drafts, the shared bit-function library
    (`svgolf/design/`), the obligation census, the producer contracts.
  - [x] `sv_structure` prototype `797efb68`, multiplier extension and
    knownness, `sv_equations` (stage 2 `5dc8ce22`, adapted to upstream's
    2-state tier).
  - [x] ls-sv PUSHED TO MAIN 10/29 evening (`759422d9`, fast-forward, no force):
    three commits on `github/master` (round 6 and the 2-state tier fixes; sv_comb
    stage 2; the refusal register), `1bb0874f..759422d9`, no `svgolf/` path.
    Verified before the push on the combined tree of the golf branch, the
    2-state tier and master: all 60 `LeanModels.Sv` modules build; 418 of 427
    `Examples/system-verilog` modules build (the other 9 import the umbrella
    `LeanModels`, blocked by upstream's red `LeanModels/Python/PayloadBlind.lean`,
    identical on clean master); the extractor suite passes (2103) and is now
    deterministic under all hash seeds (a leaked M0 global made symbolic
    refusal texts depend on test order: fixed in `process_symbolic`); the full
    differential run has 0 FAIL and 0 ERROR (387 verified, 15 declared, 258
    loud) with the golden comparison 419 match, 6 declared, 1 known difference.
    The refusal register works with and without `svgolf/` (the check skips the
    svGolf half when the directory is absent). `svgolf-prep` was
    fast-forwarded onto the merged tree (`72c737ae`), so master is its ancestor.
    svgolf ADAPTED to the merged ls-sv (10/29 evening): the four hand-built
    `CombDesign`s (`add_n`, `mul_n`, `band`, `band_lp`) gained the 5-line
    `inFourState` field (their declarations are all 4-state, `rfl` per
    declaration); nothing else in `svgolf/` needed a change. `lake build`
    green; `tests/run.py --skip validate` 226/226 (same counts as before) and
    the quick validate plans 14/14; every check line is identical to the
    pre-merge Verilator-era run, so no expectation and no score moved. Still
    open: re-prove the references with `sv_structure`/`sv_equations`.
  - [x] Round 6 DONE 10/29 (`5dff1111`, on `svgolf-prep`; not yet on main):
    all three lanes passed independent verification (lane A after one repair).
    Full differential run with `--golden`: 0 FAIL, 0 ERROR; differences from the
    Xcelium pin fell from 36 to 1 (`dyn32`, a value change outside a
    refusal-only round: the model reads a 32-bit unsigned run-time base as
    signed). Recorded gaps: the alias guard runs beside `name.sem` (so an
    unprobed parameter point does not carry `AlwaysComb:alias-read`); two
    net-to-net neighbours of the refused shape still zero-extend where Xcelium
    z-fills (`.i(n[0])`, `.i(s[1:0])`); `_sym_net_bound_actual` fails open on a
    slang API error; the wide-index refusal is judged at the default point in
    the extractor. The divergence register's `sv_div_1` guard fails on any
    tree with a committed Xcelium fixture (already on clean master): needs a
    decision from whoever owns that row.
  - [x] Refusal register (`e0fc4b45`): `docs/sv-refusals.{json,md}`,
    `svgolf/REFUSALS.md`, `tools/gen_sv_refusals.py` with a completeness
    check (198 ls-sv entries, 58 svGolf). Classifications as later or never
    that the maintainers have not decided are marked `proposed` and need their review.
  - [x] (history) Round 6 (workflow `lssv-xcelium-refusals`; ls-sv, driven by
    the Xcelium audit `6926622f`): in every one of the 36 differing rows
    Xcelium itself departs from explicit LRM text, so Xcelium is the
    reference but not infallible. Decisions taken: refuse constant-base
    partially out-of-range part-selects (reads and writes), narrow net
    actuals into wider net input ports and run-time bit-select indexes wider
    than 32 bits; declare the run-time-base part-select departure; add an
    always_comb alias guard (two declared Icarus departures become
    refusals); keep the pin on Xcelium's default flags (no `-ii_val`).
    Refusal-only.
  - [x] Stage 2 DONE 10/29 (workflow `sv-comb-stage2`, all lanes verified by
    independent agents, no blocker/major): `sv_structure` extended to the array
    multiplier; the x-free knownness theorem; `sv_equations` (netlist view with
    knownness) and complete for-all-N correctness proofs of the ripple adder
    (108 lines against 537) and the array multiplier (197 against 1380), both
    from the real `sem N`, with tampered-design negatives. See the Status in
    `docs/sv-comb-design.md`. Open: automate the six 2-D coverage goals of the
    multiplier (about 65 hand lines), source-located fragment errors, a
    separate `sv_known`, module instances / `always_comb` / the sequential
    layer. Integration into main is in progress.
  - [x] (history) Stage 2 (workflow `sv-comb-stage2`): lane M extends
    `sv_structure` to the array multiplier (nested loops, 2-D arrays,
    part-select/concat targets, `lexRank` end to end, `using hc`, example
    moved into `Examples/`); lane K proves the x-free knownness theorem;
    then lane E builds `sv_equations` (the netlist view) for the adder and
    the multiplier. Each lane is verified by an independent agent.

## Day 4 — Fri 10/30

- [x] Track B: F3, module instances (round 1, `e39932f7`; flat top, one level
  of instances; recursion is F3b below).
- [x] `sv_comb` v1 on the ripple adder and the array multiplier (stage 2,
  pushed to main in `17205bef`..`759422d9`). The hand proof disappears almost
  entirely: adder 537 → 108 code lines, multiplier 1380 → 197. Details in
  `docs/sv-comb-design.md` Status.
- [-] Fixed-size side-condition checkers run by `decide` (`combDesignB`,
  `acyclicB`, the `LVec.toNat?` twin, kernel time on 1000 processes):
  DEFERRED by design (principle 9 of `docs/sv-comb-design.md`: plain tactic
  first, reflection later). Revisit when a task needs more than a few hundred
  processes (fdiv16 has 77: the plain tactic should suffice once
  `always_comb` bodies are in the `sv_equations` fragment).

## Day 5 — Sat 10/31

- [~] **Challenge 1: N-bit unsigned multiplier** (task `mul`).
  - [x] Challenge file: for-all-N statement (`p = a * b`) with the interface,
    `Unclocked` and `Terminates2` (`tasks/mul/Spec.lean`).
  - [x] Banlist (`* + - / % **`) and scoring at N = 16.
  - [ ] Depth budget: not set; the default is the (area, depth) Pareto
    frontier, with an optional per-task `depth_budget` (the maintainers to decide the
    value, open question below).
  - [x] Allowed axioms (`propext`, `Classical.choice`, `Quot.sound`).
  - [ ] Time limit calibrated from a measured reference proof; proof-effort
    baseline recorded (hand proof 1380 lines vs `sv_comb` proof 197 lines).
  - [x] Reference solution: an array multiplier with a for-all-N proof
    (`tasks/mul/reference/mul_n.lean`, by hand). To do: re-prove it with the
    `sv_comb` tactics so that the reference shows the intended workflow, and
    allow the tactic library in the checker's import allowlist.
  - [x] The whole pipeline runs end to end through the checker.

## Day 6 — Sun 11/1

- [-] Sequential layer (settle and cycle theory for `always_ff`): DEFERRED
  (decided 10/29: combinational tasks first).
- [~] **Challenge 2 draft: binary16 divider** (task `fdiv16`, status `draft`).
  - [x] Spec packaged (`spec/IEEE754.lean`, validated on 47.8M vectors and
    the reference on all 2^32 pairs), banlist `/ %`.
  - [x] Reference SV validated by simulation (Verilator, all 2^32 pairs).
  - [x] Statement decided: fixed binary16, no parameter. `bv_decide` stays
    out while the checker cannot verify its certificates.
  - [x] The certificate bridge `fdiv16 a b = c ↔ cert16 a b c` (M2a in
    `tasks/fdiv16/PROOF_PLAN.md`): PROVED 10/29 (`tasks/fdiv16/Cert16.lean`,
    543 lines, standard axioms, statement of `Cert16Bridge` and `cert16`
    unchanged, no counterexample found). `fdiv16_cert` is what the reference
    proof will consume.
  - [ ] The reference proof itself (M2b/M3 and the design layer, 1500–3000
    lines): not today. Needs `always_comb` bodies and the 2-D `rem` array in
    the `sv_equations` fragment.
- [-] F3b, recursive module instantiation: DEFERRED (no task needs it).

## Day 7 — Mon 11/2

- [x] Dry run (10/29 night): two independent agents played svGolf from the public
  material only, A on `add`, B on `mul`; both were ACCEPTED with for-all-N tactic proofs
  in 25 and 32 minutes (about 5 minutes of that was waiting for the shared Lean slot).
  A: stride-2 lookahead adder 127.324 GE / depth 31 (148 proof lines), stride-4 lookahead
  160.654 / 26 (218 lines). B: carry-save array multiplier with a ripple final adder
  1960.577 GE / depth 60 (368 code lines), better than the reference (1962.576 / 88) on
  both axes. Friction logs: the two `FRICTION.md` files (summary in "Dry-run findings" below).
  - [x] Write a Dadda or Wallace multiplier, prove it, submit it, get a score: DONE, a WALLACE TREE
    (WP-E, 10/30): `tasks/mul/reference/mul_wallace.{sv,lean}`, parametric in N, proved for ALL N >= 1 with
    the sv_comb tactics, accepted by `check.py` (re-run by the lead). The design is the queue form of the
    Wallace algorithm on a flat TAPE of M = 3N-1 rows of 2N bits (one 2-D array): rows 0..N-1 are the
    partial products, row N an all-zero dummy row (so N = 1 needs no case split), and CSA number g
    (g = 0 .. N-2) reads tape rows 3g, 3g+1, 3g+2 and writes the sum row N+1+2g and the carry row N+2+2g
    (shifted left by one, mod 2^(2N)); N-1 three-to-two carry-save adder rows leave two rows, which a 2N-bit
    ripple adder adds. Every index and bound is affine in g and N (no localparam, no division, no
    conditional generate, no stage count), two generate levels deep, six labelled blocks; log_{3/2}
    depth in CSA levels. Proof: invariant "the sum of the live window [3g, N+1+2g) is a*b mod 2^(2N)" by
    induction on g (446 code lines: arithmetic 205, structure 18, ports 23, glue 115, equations and
    coverage 81; 37 s to elaborate). **2113.894 GE / depth 62 at N = 16** (482.974 / 30 at N = 8,
    8767.595 / 124 at N = 32); simulated at every N = 1..33. The first tree design is kept as a second
    log-depth entry: `mul_tree` (heap-indexed binary tree of 4:2 compressors, WP-D), 2034.904 / 63, 594
    lines, 79 s. At N = 16 against the Dadda + ripple baseline (1953.585 / 61, not a proved entry): the
    Wallace tape is 8.2% larger, the heap tree 4.2%; both are 26 and 25 gates shallower than the array
    reference (1962.576 / 88). The area gap is the greedy whole-row grouping spending a half adder at both
    edges of every row where a column-wise Dadda schedule spends almost none (three tape variants tried,
    none better). Only the COLUMN-WISE Dadda schedule (non-affine column heights) is still open, see
    "Open questions for the maintainers". One library change was needed for the heap tree: `AutoObl`'s loop-count
    bound `sum + 60` became `4 * sum + 60` (`CombViewThm`/`CombViewSound`, on main `559fbf9e`). The mul
    proof time limit is 840 s by the README rule (10 x the slowest reference compile, 79.3 s for
    `mul_tree`, rounded up to 60 s); revert to 600 if you prefer (the Wallace tape alone would allow it).
  - [x] Log every friction point (fixes: docs `c4a37bdc`, checker side WP-C `e2b323f2`).
- [x] Leaderboard format: JSON records, Pareto frontier, `assisted_by` field
  (`b22db566`: `svgolf/leaderboard/`, 57 tests, four seeded references; tamper-
  evident records, three verification levels, optional depth budget).
- [x] `svgolf/README.md`: rules, scoring, axiom policy, how to reproduce a
  score locally, a Quick start, the proving guide (`PROVING.md`), the refusal
  register link, the leaderboard section and the advisory outputs.
- [x] Checker side of the dry-run friction (WP-C, `e2b323f2`): the advisory
  functional oracle (`stages.postsynth.functional`, `warnings`), `--unproved
  --tactics`, `dev_hint` with the Lean wrapper, no `SVGOLF_ELAPSED` in errors.
- [~] Final triad (10/30): `tests/run.py` ALL steps 275/275 (layout, build, unit,
  leaderboard, canon, references, drafts, negatives, baselines, validate,
  attacks) with the tree multiplier and the library change; `docs_check` ok; the
  refusal register `--check` ok; svgolf `lake build` green; the changed tactic
  modules and the ripple_add / mul_array comb proofs rebuild on current master.
  NOT fully green: the repo-root `lake build` (re-run after the last merge,
  4342 jobs) fails in 6 `Examples.python.*` modules (rsa_inverse, nested_flow,
  clock_lab, string_repeat, divmod_lab, bench_statistics; 13 an hour earlier,
  so the Python lane's own agent is repairing it). That red is the Python lane's, not svGolf's:
  `LeanModels/Python`, `Examples/python`, `extractors/python`, `lakefile.toml`
  and `lean-toolchain` are byte-identical to github/master. Everything else,
  all of `LeanModels.Sv` and `Examples/system-verilog` included, builds. Not
  rerun after the last merge: `harness/sv/diff_test2.py` (no `LeanModels/Sv`
  semantics or `harness/sv` change since the last verified run; the one library
  change is an obligation bound).
- [x] Summary for the maintainers (in the session).

## Come back to (follow-ups recorded 10/29)

- **`sv_comb` limits (decided 10/29: "we should make sure to come back to this").**
  In priority order, each with what it unlocks:
  1. `always_comb` bodies in the `sv_equations` fragment (procedural `if` /
     `case` chains with blocking assigns). Unlocks fdiv16 (its datapath has an
     `always_comb` special-case table) and most idiomatic RTL. The settle
     lowering exists (`Comb2Proc`, `CombGuard2`); the netlist view and the
     knownness fragment do not cover it yet.
  2. Module instances (`Hier2`, `Hier2Gen`) in `sv_structure` / `sv_equations`
     (flat top only today), then recursive instances (F3b).
  3. Edge-triggered processes: the sequential layer (`always_ff`, registers,
     reset), which needs a sequential task statement too.
  4. Smaller: automate the multiplier's six 2-D coverage goals (about 65 hand
     lines); a separate `sv_known` / `sv_bitvec`; source-located fragment
     errors; reflected checkers (`combDesignB` / `acyclicB`) if proofs get
     slow; `Nat` instead of `Int` index goals.
- **From the dry run (10/29), by what the contestants hit.** Tactic library
  (`LeanModels/Sv`, goes to main):
  1. Fragment width for real tree multipliers and prefix adders: `localparam` /
     constant functions, non-affine bounds and indices (`N/2`, `i >> l`), conditional
     generate, 3-D packed arrays, nesting depth beyond two. Then a column-weight
     arithmetic library next to `ripple_row` (the proof-side invariant is the harder half).
  2. `sv_cover`: dedupe read occurrences (a 4-term lookahead lists `pp[i]` four times),
     extend the witness search to "affine index into a family window" (all that two
     six-line helper lemmas did for A), and make `first | ...` closers name the failing
     goal. The mul reference still closes six nested 2-D coverage goals by hand.
  3. A tactic for the ports/interface step (a 23-line recipe in every proof today).
  4. `sv_equations` could emit the final statement ("glue lemma"): B transcribed 12
     hypotheses by hand, and each typo costs a 40 s compile; literal/concatenation assigns
     come out in a raw form.
  5. Messages: an instance should say "instances are outside the fragment" (today:
     `cannot read a load_design_sv2 family`); `maxHeartbeats` hits name `simp`, not the
     tactic; design-stage refusals wrap the useful phrase in temp paths.
  6. Parity: `ls-sv` refuses a genvar step `i = i + 1`; accepting it removes a rule from
     the README (the register row `AssignmentExpression (genvar step)` says why it is refused).
- **Optional: the ls-sv M0 operator table on Xcelium** (register row
  `sv-div-1`, a provenance row, not a known defect). Run the per-operator
  four-state table on the Xcelium host, commit the results as a fixture, diff them
  against `Basic.lean`. Cheap minimum: make the row's guard test for the
  operator-table fixture instead of any file named for Xcelium
  (`harness/sv_divergence_probe.py`), so the register is green and honest.
- **The `never` section of the refusal register** (11 entries proposed):
  discuss with the maintainers.

## Task ladder (10/28)

Each next task adds roughly one new feature, so whatever breaks points at
that feature. Feature gaps go into the task's README and become work items.

| Task | Bans | New feature it exercises |
|---|---|---|
| `_example` (bitwise AND) | `+ - * / % **` | the pipeline itself |
| `add` | `+ - * / % **` | generate loops, carry chains, for-all-N induction |
| `mul` | `* + - / % **` | 2-D generate, partial-product arrays |
| popcount | `+ -` | `always_comb` loops with a procedural accumulator; compressor trees |
| leading-zero count / priority encoder | none | `casez` wildcards, priority logic, `$clog2` outputs |
| barrel shifter | `<< >> <<< >>>` | generate-if, log-depth mux trees, parameters derived from `$clog2` |
| comparator / max | `< > <= >=` | signed vs unsigned, ripple vs tree |
| ~~serial multiplier~~ | `* + -` | deferred (decided 10/29: "keep things combinatorial to begin with"). Needs a clocked `always_ff` and a sequential task statement (Day 6 layer). |
| `fdiv16` | `/ %` | all of the above together |

**Before the next task: the post-synthesis simulation check.** Since
contestants may change the semantics by PR, this check (ls-sv versus the
synthesized netlist on random and corner vectors) is the backstop against
a wrong feature PR, an old ls-sv gap, or a Yosys quirk. It moves ahead of
new tasks.

**Layout cleanup (10/28, after the tasks workflow lands).**
- A task folder holds only what a player needs: `task.json`, `Spec.lean`,
  `README.md`, and the sample solution with its proof in `reference/`.
- `reference/` holds only PROVED solutions, each `<stem>.sv` paired with
  `<stem>.lean`. `tests/run.py` enforces that `check.py` accepts every one.
  Unproved, simulation-only designs (the Sklansky and Kogge-Stone adders,
  the Dadda multipliers) move to `tests/<name>/baselines/`. A task with no
  proved reference yet (`fdiv16`) is marked `"status": "draft"` in
  `task.json`.
- Tests move to `svgolf/tests/`:
  - the runner (was `tasks/check_all.py`);
  - expected reference scores (was `reference/score.json`);
  - negative designs and their `Refute.lean`;
  - the `validate/` simulation checks;
  - the score records the READMEs cite.
- Extractor output is never committed. `load_sv` extracts at elaboration
  time into `svgolf/.lake/envelopes/`, keyed by a hash of the `.sv`, and
  Lake rebuilds when a `.sv` changes.

**Fixed (10/28): an undriven clock.** `CombTask.SatisfiedAt` now requires
`Unclocked d` (no edge-phase process) beside `Terminates2`. All four task
references re-checked. The original report follows.
`logic clk; always_ff @(posedge clk) y <= a & b;` with `clk` never driven
satisfies `CombTask` and scores 0 GE. ls-sv runs every edge-phase process
once per cycle whatever its clock (the charter's "single-clock gap", not
started), while every simulator leaves `y` at x. Fix on the svGolf side,
once the tasks workflow lands: `CombTask` requires that no process is
edge-phase, and the reference proofs close that by `decide`. The ls-sv
fix comes with the sequential layer.

## Challenge ideas (backlog)

Ideas modelled on zk.golf's list, plus classic gate-minimisation problems.
Parametric (for-all-N) challenges stress the proofs; fixed-size ones stress
area and can be proved by `decide`.

**Parametric**
- Prefix adder, banning `+` and `-`. The Kogge-Stone / Brent-Kung /
  Sklansky trade-off gives a real area-depth frontier.
- Popcount.
- Leading-zero count (needed by the floating-point divider).
- Barrel shifter.
- Carry-less (GF(2)) multiplier, as used in GHASH. Karatsuba pays off here.
- Integer divider and square root.
- Comparator.

- Sorting network for 2^k inputs of width W, for all k and W:
  - Families: bitonic or Batcher odd-even merge.
  - Proof via the 0-1 principle.
  - Score at n = 8 or 16.
  - Needs F1/F2 (indexing `x[i*W +: W]`), or recursive module instantiation
    (see F3b).
- Integer divider `q = x / y`, `r = x % y`, banning `/` and `%`. This is the
  stepping stone to the floating-point divider.
- IEEE divider for every format `(e, p)`, scored at binary16. It is built
  from parametric pieces: the integer divider, leading-zero count and
  rounding.

**Fixed size**
- AES S-box, with Boyar-Peralta-style circuits as the bar to beat.
- 8-input sorting network (19 comparators is optimal), as a fixed-size
  area-only track next to the parametric one.
- CRC-32 over a byte or word.
- Hamming / SECDED encoder and decoder. The spec is a property: decoding
  corrects any single-bit error.

**Crypto rounds** (spec is the FIPS reference written in Lean `BitVec`)
- Keccak-f round, which uses only bitwise operators.
- SHA-256 compression.
- ChaCha / BLAKE3 quarter-round.

**Scoring tracks** (the analogue of zk.golf running one function under
several cost models)
- Area.
- Depth.
- AND-count with XOR free (multiplicative complexity).

## Open questions for the maintainers

**Defaults in force in v0 until the maintainers decide** (the build does not wait on them; each is a
one-line change):
- `mul` proof time limit: **900 s**, the README rule applied as written (10 x the slowest reference
  compile, 86.5 s for `mul_tree_h` (79.3 s for `mul_tree`), rounded up to 60 s). 600 s would also hold
  for the other references; changing it is one number in `tasks/mul/task.json`.
- Depth budget: **none** (the board keeps the (area, depth) Pareto frontier; `leaderboard.depth_budget`
  and `scoring.depth_budget` exist and are unused).
- Record hand-off: **local records only** (`leaderboard.py add --data-dir`), documented in the README;
  a pull request carrying the record directory is the proposed public route, not built.

**Needs the maintainers' own decision** (they said they would decide these, so they are not defaulted): the `never`
section of the refusal register, row `sv-div-1`, the undeclared `dyn32` Xcelium difference.

**Not this plan's lane:** the six red `Examples.python.*` modules of the repo-root `lake build`
(the Python lane's own agent is repairing it; `LeanModels/Python` and `Examples/python` are
byte-identical to github/master); the "Come back to" section below (`always_comb` bodies,
module instances, the sequential layer, `localparam` atoms), which the maintainers scheduled for after
this build, and the column-wise Dadda schedule that needs the last of them.

- **Column-wise DADDA multiplier for all N (the Day 7 item is DONE as a Wallace tape and a
  heap-indexed 4:2 tree, see above; this is the remaining, harder shape).** What it
  takes, measured by the dry run (contestant B probed the tactics one construct at a
  time; the checker admits all of them, `sv_structure` refuses each): a log-many stage
  count (`localparam L = $clog2(N)`), non-affine bounds and indices (`N/2`, `N >> l`,
  column heights from the Dadda sequence), conditional generate, 3-D packed arrays
  (stage x column x position) and three or more nested generate levels. That is a
  widening of the `sv_comb` fragment (`CombView*`, `CombEq*` in `LeanModels/Sv`,
  which goes to main), plus a column-weight arithmetic library next to `ripple_row`
  whose invariant is the harder half; I estimate days, not hours, and it competes
  with `always_comb` bodies (needed by `fdiv16`) for the same machinery. Options:
  (a) fund it now, as the next work package; (b) take the carry-save array
  multiplier the dry run produced (1960.577 GE / depth 60, already better than the
  reference and within 0.4% of the Dadda + ripple baseline's 1953.585 / 61, whose
  depth is set by the final ripple adder, not by the tree) as the v0 `mul`
  showcase and put the Dadda tree on the task ladder as a later task; (c) a
  by-hand proof for a padded power-of-two tree, which skips the tactics but needs
  an ls-sv `localparam`/conditional-generate walk like the Sklansky baseline's. The
  heap tree changes the picture: it shows how far the CURRENT fragment already goes (an
  unproved variant with ceil(N/2) leaves through `localparam H = (N+1)/2` would score
  2025.9 / 62 at N = 16, 3.7% above Dadda + ripple, and needs `localparam` as an affine
  atom in the tactics), so the value of the widening is now a few percent of area, not a
  new depth class.
- Push the Track A repair (Python lane and `Load.lean`) straight to
  `github/master`, or open a PR?
- How does a record reach the public board? Today `leaderboard.py add` only writes a
  record on the contestant's machine (the README says so and shows `--data-dir`); a pull
  request carrying the record directory is the obvious hand-off (records are self-verifying
  with `verify --full`), but nothing else exists: no server, no submission format beyond the
  record, and no rule for who re-verifies.
- Must challenge proofs be parametric (for all N), with the score taken at
  N = 16?
- Depth budget for the 16-bit multiplier: for example, the depth of Yosys's
  own `a*b` (30 at N = 8)?
- ~~Floating-point oracle: allow SoftFloat/TestFloat?~~ Not needed: two
  independent stdlib-Python oracles plus Lean's float model.

## Status line (WP-B, 10/29): tactic references, proof-effort baseline, PROVING.md

The `add` and `mul` references are re-proved with the `sv_comb` tactics (107 and 235 code lines; the by-hand
proofs, 509 and 1385, stay as `*_byhand.{sv,lean}` pairs and are checked too), both pairs accepted by
`check.py`; the proof time limits are now 300 s (`add`) and 600 s (`mul`) by the rule in `README.md`
("Proof effort"); the import allowlist already admitted `LeanModels.Sv.*` and is now tested
(`tests/imports/test_allowlist.py`); the guide is `PROVING.md`. Day 5's "time limit calibrated" and "re-prove
with the tactics" items are done; the open limits (ports step by hand, 2-D coverage goals by hand, fragment) are
in `PROVING.md`, section 7.
