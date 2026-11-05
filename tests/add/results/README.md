# `add`: measurement records

The logs of the last FULL validation runs, cited by `tests/add/validate/README.md`:
`validate.log` (`validate.py`), `verilator.log` (`verilator.py`, five runs) and
`postsynth.log` (`postsynth.py`). They are kept verbatim from the runs, which
predate the 10/28 layout: a path in them is relative to the old task
directory `tasks/add/`, so `reference/add_n.sv` is today's
`tasks/add/reference/add_n.sv`, `reference/add_n_sklansky.sv` and
`reference/add_n_kogge_stone.sv` are in `tests/add/baselines/`,
`negative/plus.sv` is `tests/add/negative/plus.sv`, and `validate/cmp_carry.sv`
is `tests/add/baselines/cmp_carry.sv`. The designs themselves did not change.

HISTORICAL as to the simulator: `validate.log` and `postsynth.log` were made
with Icarus Verilog 12, before svGolf moved to Verilator (decision 10/29); the
`icarus_bad` / `ic_vs_run2` keys in `validate.log` are that script version's.
`verilator.log` is Verilator 5.042 throughout. The logs stay as the record of
those runs; the scripts now simulate with Verilator (`tests/add/validate/README.md`).

The scores of every design are not here but in `tests/expected.json`, which
`tests/run.py` re-measures on every run.
