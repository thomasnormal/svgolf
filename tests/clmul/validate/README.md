# Validation of task `clmul`

* `validate.py` (quick; no Verilator): the oracle (`tasks/clmul/oracle.py`, shift-and-XOR) equals an independent
  implementation by Kronecker substitution on every pair at `N <= 6` and on random pairs up to `N = 100`; the
  published anchors (`(x+1)^2`, `(1+...+x^15)^2`, and FIPS 197 Section 4.2's `{57} * {83} = {c1}` and
  `{57} * {13} = {fe}` after reduction modulo `0x11b`); commutativity, distributivity over XOR and the
  `x`-shift law; and, through Lean (`Dump.lean`, run by `lake env lean --run`; skipped with `--no-lean`), the
  TRUSTED spec `task.fn` equals the oracle on every pair at `N = 1 .. 7` (21 844 pairs) and on sample pairs at
  larger `N` up to 64.
* `sim.py` (Verilator): a design against the carry-less product computed by whole-word shift-and-XOR in
  `tb.sv`; plans `quick` (exhaustive `N <= 4`, 100 random pairs at `N = 8, 9`) and `full` (exhaustive `N <= 8`,
  100 000 random pairs at `N = 9, 12, 13, 16, 24, 31, 32, 33, 48, 64`); `--width N` for one width (the per-width
  baselines); `--bad` inverts the verdict for the wrong designs.
