# `tests/fdivp/baselines/`: scored designs that are never accepted

| design | what | score at `(5, 11)` | at `(8, 24)` |
|---|---|---|---|
| `fdivp_d1.sv` | D1, the natural parametric divider (gate 0 of WP-H3): `$clog2`, `2**`, replication, sized localparams, a logarithmic normalizer and shifter; passes the source gate, the banlist (its `/` and `**` are in constant expressions) and `fourstate`; ls-sv cannot run it (an unsupported node), so there is no post-synthesis check and no proof | 1911.446 GE, depth 300 | 7450.536, 1256 |
| `fdivp_d2.sv` | D2, the fragment-friendly form (about 90 plain sites, a linear normalizer and denormalizer): inside the tactic fragment, not proved (its tactics cost grows as `n^2` in the sites without WP-LIN) | 2314.058, 295 | 9813.601, 1279 |
| `flat_binary16.sv` | the flat binary16 reference of the former 16-bit task (removed 2026-11-03; binary16 is `(5, 11)` here) under the parametric header: right at `(5, 11)` ONLY, simulated and scored there | 1944.775, 303 | n/a |

All three are validated by Verilator (`tests/fdivp/validate/validate.py`, step `validate` of `tests/run.py`): D1 and D2 on the
small formats exhaustively and at `(5, 11)` sampled (and, in the gate-0 record, on all 66 formats with `W + P <= 14` and both
2^32-pair formats), the flat one at `(5, 11)`. A baseline need not pass the `design` stage: `tests/run.py` scores it with the
banlist lifted, checks the banlist verdict, the 4-state rules, and the post-synthesis check where ls-sv can run it
(`postsynth_points` in `tests/expected.json`).
