# Proved designs of task `mul` besides the references: a banned-operator baseline and an entry

Every design here comes with a kernel-checked proof of the task's statement for every `N` in range, its `.lean`
beside it (decided 2026-11-12: every design the site shows is proved). The one with an operator the task bans
(`yosys_mul.sv`) is a BASELINE: a comparison design, never ranked, never par and never an entry. The one without
(`dadda_rc.sv`) is an ENTRY (decided 2026-11-12: par is one design per task, the simplest algorithm,
`leaderboard/par.json`: here the array `mul_n`; every other proved design is an entry), recorded on the board under a
handle of its own like any player's, and shown on the site once that record exists. `tests/run.py`, step
`baseline-proofs`, checks each proof through
`check.py`, with the standard axioms only.

* `yosys_mul.sv` + `yosys_mul.lean`: `assign p = a * b;`, Yosys's own multiplier, the baseline to beat. It uses
  the run-time `*` the task's banlist forbids, so its proof is checked with that banlist lifted (`check.py
  --lift-banlist`, which ends at the pseudo-stage `lifted`: proved, not an entry); the banlist rejects it, and it
  is scored with the banlist lifted. The proof reads the product with the `sv_comb` tactics (both factors
  zero-extended to `2N` bits, IEEE 1800-2017 11.6.1, 11.8.2) and closes it with the Spec's `fn_eq_mul`.
* `dadda_rc.sv` + `dadda_rc.lean` (since 2026-11-12): a Dadda tree with a ripple-carry final adder, ONE design for
  every `N`. The columns of partial products are compressed by full and half adders down to two rows, stage by
  stage, in generate loops whose bounds are closed forms of `N`, the stage and the column (the stage count and the
  Dadda heights are constant `?:` chains, so every generate header is an `int` constant expression); a ripple-carry
  adder adds the two rows. At `N = 8` and `16` it has the cells of the one-width netlists
  `tests/mul/unproved/dadda_rc_<N>.sv` (equal AND, OR and XOR counts before ABC), and at `N = 8, 16, 32` their
  scores, gate mix included. Proved by hand, without the tactics: the column ledger (the weighted sum of the bits is
  `a * b` before the first stage and unchanged by every stage), the generate nest expanded at symbolic `N`,
  acyclicity from a rank of each write window, then the settled state by induction over the stages and over the
  carries of the final adder; about 3,900 lines. Measured 2026-11-12 on an Apple M2 Pro (`check.py --postsynth
  full`, accepted): `solution` 47 to 48 CPU s of the task's 300; the full post-synthesis check (330 vectors) 803 s
  of the task's 900 s cap, the slowest stage of its check. That stage is a wall-clock limit: on the same machine
  under a heavy load from other jobs (1-minute load 15 to 23) it took over 900 s once and failed closed.

Validation: every design on `tests/mul/validate/sim.py`'s quick plan in `tests/run.py` (the full plan with
`--full`).

| design | N = 4 | N = 8 | N = 16 | N = 32 |
|---|---|---|---|---|
| `yosys_mul.sv` | | 468.637 / 30 | 2081.227 / 59 | 8639.254 / 110 |
| `dadda_rc.sv` | 87.661 / 13 | 445.978 / 29 | 1953.585 / 61 | 8153.020 / 125 |
| reference (`tasks/mul/reference/mul_n.sv`, proved) | | 447.976 / 40 | 1962.576 / 88 | 8191.648 / 184 |

(area in NAND2 GE / depth in gates; every number, with its gate mix, is in `tests/expected.json`, which
`tests/run.py` checks.)

The Dadda trees `dadda_rc_<N>.sv` and `dadda_ks_<N>.sv` were baselines here until 2026-11-12. Each is a flat
netlist for ONE width, so no proof of the for-all-`N` statement can exist for it: they are test material in
`tests/mul/unproved/` now, shown nowhere on the site, with their generator `gen_dadda.py`. The parametric
`dadda_rc.sv` replaces the ripple-carry ones (on the site once its record exists). The same tree with a Kogge-Stone final adder is proved
too, but not added: its full post-synthesis check took 893 s of the 900 s cap on the machine above and overran the
cap in three later runs there (2026-11-12). Another proved design joins as `dadda_rc.sv` did: the `.sv` and its
`.lean` here, an entry in `tests/expected.json` (`tasks.mul.baselines`, `lean` naming the proof, the points to
score at, whose numbers `tests/run.py --update-scores` writes), the proof checked by `tests/run.py`'s step
`baseline-proofs`, a row in its validation, then the derived data re-measured (`score/points.py measure --task
mul`, `leaderboard.py asap7 --write --task mul`, the PPA goldens of `score/tests/ppa/designs.json` through
`score/ppa_validate.py table`); one without a banned operator is an entry, so it is shown once a record under a
handle of its own holds it (`leaderboard.py add`), and one with a banned operator needs a sentence for it in
`site/content/tasks/mul.json` (`baselines`).
