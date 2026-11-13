# `tests/fdivp/baselines/`: a proved design besides the references, an entry

Every design here comes with a kernel-checked proof of the task's statement for every `(W, P)` in range, its
`.lean` beside it (decided 2026-11-12: every design the site shows is proved). It uses no banned operator, so it is
an ENTRY (decided 2026-11-12: par is one design per task, the simplest algorithm, `leaderboard/par.json`: here the
restoring divider `fdivp`; every other proved design is an entry), recorded on the board under a handle of its own
like any player's, and shown on the site once that record exists. `tests/run.py`, step `baseline-proofs`, checks the
proof through `check.py` (accepted, standard axioms only).

| design | what | score at `(5, 11)` | at `(8, 24)` |
|---|---|---|---|
| `fdivp_d2.sv` + `fdivp_d2.lean` | D2, the fragment-friendly form (gate 0 of WP-H3: about 90 plain sites, a linear normalizer and denormalizer), the same function as the reference D3 by the same algorithm with an offset exponent. Proved with the `sv_comb` tactics on all 90 sites and D3's math layer; the tactics' cost grows as `n^2` in the sites, so its solution stage takes 164.8 CPU s of the task's 300 (measured 2026-11-12 on an Apple M2 Pro; 221 to 225 CPU s on a slower Linux machine on 2026-11-11), where the reference folds the same form into 34 sites | 2314.058, 295 | 9813.601, 1279 |

It is validated by Verilator (`tests/fdivp/validate/validate.py`, step `validate` of `tests/run.py`) on the small
formats exhaustively and at `(5, 11)` sampled (and, in the gate-0 record, on all 66 formats with `W + P <= 14` and
both 2^32-pair formats). `tests/run.py` also scores it, checks the banlist verdict, the 4-state rules and the
post-synthesis check (`postsynth_points` in `tests/expected.json`).

D1 (`fdivp_d1.sv`, the natural parametric form, which ls-sv does not run yet) and the flat binary16 divider
(`flat_binary16.sv`, right at `(5, 11)` only) were baselines here until 2026-11-12: neither has a proof, so they
are test material in `tests/fdivp/unproved/` now, shown nowhere on the site.
