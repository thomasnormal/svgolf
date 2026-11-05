# WP-H3, gate 2: `fdivp` is a TASK (package, checker, baselines, attacks, validation)

Status: NOTE, 2026-11-02, branch `wph3g2` (off `wph3` `478c766b`, which contains `wplin`). Continues `H3-G2-NOTE.md`. MEASURED =
I ran it. Timings are those of a loaded shared machine and are not claims; the proof time limit is a PLACEHOLDER.

## 0. Summary

1. **`tasks/fdivp/` is a registered READY task**: `task.json` (comb-family, parameters `W` then `P`, ranges `2 <= W`, `2 <= P`, scoring
   point `(5, 11)`, banlist `/ % **`, probe points `(2,2) (2,3) (3,2) (3,4) (4,5) (5,11) (8,8) (8,24)`, `time_limit_s` 600 =
   PLACEHOLDER with an entry in `score/time_limits.json` whose `references` is `null`), `README.md`, `REVIEW.md` (the trusted `Spec.lean`,
   six questions for the maintainers), `oracle.py` (the independent exact-rational oracle of `hunt/fdiv_oracle.py` plus `oracle(params, inputs)`),
   `Spec.lean` (docstring only), the reference. `lake build tasks` builds all of it, `DpG0..5` as a whole (49 jobs, MEASURED).
2. **`check.py` accepts the reference through every stage at the two-parameter point** (MEASURED): score 2166.076 GE, depth 289, 1515 gates;
   `solution` 28.8 s, comparator 42 s (axioms `propext`, `Classical.choice`, `Quot.sound`), `leanchecker` 21 s, postsynth FULL 4443 vectors (ls-sv
   12 ms per vector), the advisory oracle agrees on all 4443, `design` checked 6 points free of unsupported nodes, `ppa` with the pinned liberty
   (9675.5 um^2, 37768 ps; mapped 8266.7 um^2).
3. **The only part of `check.py` that was not n-ary is `tactics_probe_text`** (one parameter or none): it now states
   `example (W : Nat) (P : Nat) : CombDesign (design.sem W P)` for any number of parameters (10 lines in `check.py`, one test in
   `tests/checker/test_advisories.py`); `--unproved --tactics` on the reference then answers `in_fragment: true` (1.4 s). Everything else took two
   parameters unchanged: the extractor's parameter check (by name and order), `probe_points`/`scoring.params`/`backstop_points` strings
   (`W=5,P=11`), the banlist and fourstate points, `unsupported_check_points`, `svgolf-eval`'s point, the oracle's `params`, `score.py`.
4. **Baselines need not pass `design`.** D1 (1911.446 GE, depth 300, the natural form with `$clog2`, `2**`, replication) passes the source gate,
   the banlist (its `/` and `**` are in constant expressions) and `fourstate`, so it is scored; ls-sv cannot run it, so it carries
   `postsynth_points: []` with the reason (as `clmul`'s 32-bit baselines). D2 (2314.058, 295) and the flat `fdiv16` under the parametric header
   (1944.775, 303; right at `(5, 11)` only) also pass the post-synthesis check. `tests/fdivp/baselines/`.
5. **Five attacks** (`tests/fdivp/attacks/`), each the reference with ONE change, passing every stage up to the proof and failing the reference's
   proof at the application of `chain`: `inc_tie_odd`, `dsh_wrap64` (right on all 2^32 pairs of `(5, 11)`, wrong from `W = 7`), `ew_narrow` (right at
   `(5, 11)`, `(8, 24)`, `(11, 53)`, wrong when `P` is large against `W`), `zero_by_zero_inf` (exactly 4 pairs), `rr_sticky_dropped`. The two
   format-dependent ones are invisible to the post-synthesis check AND to the advisory oracle at the scoring point: only the proof sees them.
   Four negatives (`div_op` rejected at `banlist`; `rm_pin`, `status_flag` by the interface conjunct; `const_nan`).
6. **Validation** (`tests/fdivp/validate`, records in `tests/fdivp/results`): the four oracle implementations agree; the reference equals the C++ oracle
   on all 66 formats with `W + P <= 14`, on all 2^32 pairs of `(5, 11)` and `(8, 8)`, and on 200,000 corner-rich vectors at 12 larger formats up
   to `(11, 53)`, `(2, 62)`: 0 mismatches. `tests/run.py --only fdivp` passes its steps layout, references, negatives, baselines, validate (quick), attacks
   (MEASURED; the other steps are task-independent).

## 1. Findings

* **A worktree can reuse the shared build** with `cp -Rc` (APFS clone, 2 s, no space): `.lake/build`, `.lake/config`, a symlink for
  `.lake/packages`, and `svgolf/.lake`; `lake build --no-build SvGolf` then answers "up to date (29 jobs)", and only the modules that differ
  (here the five WP-LIN tactic modules and the new `DpG*`) rebuild. `check.py`'s `trusted` stage in a fresh worktree is the build of whatever
  differs (1075 s here).
* **Hold the Lean slot for a BATCH, not per call**: `check.py --lean-wrap $SLOT` queues every Lean call behind other users' 40-minute jobs (a
  check run took 8 to 20 minutes of waiting); `$SLOT bash batch.sh`, with `check.py` WITHOUT the wrapper inside, ran six designs in 7 minutes.
* **`Fmt(w, p)` of `spec/validate/oracle.py` is slow to construct** (0.2 s: a lazily built table); construct it once per format. The Fraction
  oracle is slow at formats with a huge exponent range (`(20, 12)`: `2^(2^19)`), so the oracle-agreement step does not sample those.
* Statement order moves the score of a netlist (as for `fdiv16`, `aes_sbox`): decided to stay; `fdivp` is NOT in `canonical_layout`.

## 2. Open

* **`time_limit_s`**: the rule `max(120, ceil(4 T))` on three cold `solution` runs of the reference on a quiet machine (load < 10). The uncontrolled run
  took 28.8 s, so the rule would give 120 s (floor) if the quiet T is below 30 s.
* The five `cover` closers and the heartbeat limits (300k structure, 500k solution) assume WP-LIN; on a tree without it the reference fails at `solution`.
* `tests/run.py --full` (hours) runs the full validation plan; the recorded exhaustive results are those of the gate-1 runs (same design bytes).
