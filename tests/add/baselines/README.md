# Baselines for task `add` (NOT entries)

Designs that are scored but never accepted: none of them has a proof, so
none is an svGolf entry. Their scores at `N = 16, 32, 64` (gate mix included)
are in `tests/expected.json` and re-measured by `tests/run.py`, which also
checks that the banlist passes them; `tasks/add/README.md`, "Scores", has the
table and the (area, depth) frontier.

* `add_n_sklansky.sv`: a Sklansky parallel-prefix adder (127.658 GE, depth 28
  at `N = 16`);
* `add_n_kogge_stone.sv`: a Kogge-Stone parallel-prefix adder (149.652 GE,
  depth 24);
* `cmp_carry.sv`: a policy probe, every carry a run-time comparison
  (195.975 GE, depth 17; `tests/add/validate/README.md` explains why it is
  here).

Yosys's own `assign {cout, s} = a + b + cin;`, the baseline to beat
(117.994 GE, depth 33), is `tests/add/negative/plus.sv`: a negative design
(the banlist rejects its run-time `+`) that `tests/expected.json` also lists
as a baseline, scored with the banlist lifted.

All of them are simulated by `tests/add/validate/` (Verilator and ls-sv's
`run2` against `a + b + cin`, the scored netlists in Verilator, and the two
prefix adders in bulk, also in Verilator), and `tests/run.py` runs the checker's post-synthesis
check on each (`check/postsynth.py`: ls-sv and the scored netlist agree at
`N = 16`; `--full`: at 32 and 64 too). The prefix adders pass every `check.py` stage up to
`comparator` with a placeholder proof; what they lack is the for-all-`N`
proof (`tasks/add/README.md`, "Next goalposts"). For the Sklansky adder the
mathematics of that proof is `add_n_sklansky_core.lean` (section `SklCore`, the
future reference's arithmetic; it moves into `tasks/add/reference/` with the
design once ls-sv's tactics take the natural source).
