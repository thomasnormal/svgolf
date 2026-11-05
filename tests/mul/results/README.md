# `mul`: measurement records

`check.json` is `check.py`'s full output on the reference
(`tasks/mul/reference/mul_n.sv` with `mul_n.lean`; recorded before the 10/28
layout, under the proof's former file name): accepted, axioms `propext`,
`Quot.sound`, `Classical.choice`, and the stage timings `tasks/mul/README.md`
cites. The scores are in `tests/expected.json`, which `tests/run.py`
re-measures on every run (and `tests/run.py` re-runs `check.py` on the
reference every time).
