# Proved designs of task `add` besides the references: two entries and two banned-operator baselines

Every design here comes with a kernel-checked proof of the task's statement for every `N` in range (decided
2026-11-12: every design the site shows is proved), its `.lean` beside it. The two with an operator the task bans
(`cmp_carry.sv`, `plus.sv`) are BASELINES: comparison designs, never ranked, never par and never entries. The two
without (`add_n_sklansky.sv`, `add_n_kogge_stone.sv`) are ENTRIES (decided 2026-11-12: par is one design per task,
the simplest algorithm, `leaderboard/par.json`; every other proved design is an entry), recorded on the board under a
handle of their own like any player's, and shown on the site once that record exists. `tests/run.py`, step
`baseline-proofs`, checks each
proof through `check.py` (accepted; the ones with an operator the task bans with `check.py --lift-banlist`,
which ends at the pseudo-stage `lifted`: proved, not an entry), with the standard axioms only. Their scores at
`N = 16, 32, 64` (gate mix included) are in `tests/expected.json` and re-measured by `tests/run.py`, which also
checks the banlist's verdict (it passes the prefix adders, rejects `cmp_carry.sv` and `plus.sv`);
`tasks/add/README.md`, "Scores", has the table and the (area, depth) frontier.

* `add_n_sklansky.sv` + `add_n_sklansky.lean`: a Sklansky parallel-prefix adder (127.658 GE, depth 28 at
  `N = 16`), proved by hand: the `sv_comb` tactics refuse a conditional generate inside the inner generate loop,
  so the proof instantiates the design at symbolic `N`, gives one driver per bit, a rank computed from the process
  and the settled state by induction on the level. Its prefix mathematics is `add_n_sklansky_core.lean` (section
  `SklCore`), which the proof copies.
* `add_n_kogge_stone.sv` + `add_n_kogge_stone.lean`: a Kogge-Stone parallel-prefix adder (149.652 GE, depth 24),
  proved the same way, its prefix mathematics on `LeanModels.Sv.Lib.Prefix`.
* `cmp_carry.sv` + `cmp_carry.lean`: every carry a run-time comparison, i.e. Yosys's own adder (`alumacc` builds
  each comparison as an `$alu`), so the banlist rejects it since 2026-11-05 (195.975 GE, depth 17;
  `tests/add/validate/README.md` explains why it is here). Proved with the tactics (each carry is
  `[A_i + B_i + cin >= 2^i]`, which follows the ripple recurrence), checked with the banlist lifted.

Yosys's own `assign {cout, s} = a + b + cin;`, the baseline to beat (117.994 GE, depth 33), is
`tests/add/negative/plus.sv`: a negative design (the banlist rejects its run-time `+`) that `tests/expected.json`
also lists as a baseline. Its proof is `plus.lean` here (by hand: the tactics refuse the concatenation target
`{cout, s}`), checked with the banlist lifted.

All of them are simulated by `tests/add/validate/` (Verilator and ls-sv's `run2` against `a + b + cin`, the scored
netlists in Verilator, and the two prefix adders in bulk, also in Verilator), and `tests/run.py` runs the checker's
post-synthesis check on each (`check/postsynth.py`: ls-sv and the scored netlist agree at `N = 16`; `--full`: at
32 and 64 too).
