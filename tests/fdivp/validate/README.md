# `tests/fdivp/validate/`: simulation of the `fdivp` designs against independent oracles

`validate.py` is the entry point (`python3.12 tests/fdivp/validate/validate.py --plan quick|full`, or `--design SV
--formats W,P ... [--bad] [--exhaustive] [--samples N]` for one design); `tests/run.py` runs it in the step `validate`
(`fdivp_validation` in `tests/run.py` lists the rows). It needs Verilator and a C++ compiler, not Lean.

| file | what |
|---|---|
| `oracle.h` | the C++ oracle `oracle_div(W, P, a, b)`: exact round-to-nearest-even division for any format with `W + P <= 64`, 128-bit integers, the quotient rounded at the spacing of its binade (a third implementation, independent of the spec and of the Python ones) |
| `tb_fdivp.cpp` | Verilator testbench: exhaustive over a slice of `a`, or sampled (corner patterns, uniform, near-tie and near-overflow exponents), against `oracle.h` |
| `tb_vec.cpp`, `gen_vec.py` | the same from a pre-generated vector file (random, exponent-boundary, tie-shaped, corner operands); `gen_vec.py` also checks `oracle_int` against the `Fraction` oracle on a subset and the Python model against `oracle_int` |
| `run_v.py`, `run_vec.py` | build the Verilator model of a design at `(W, P)` (`-GW -GP`) and run it (one JSON line) |
| `fdivp_model.py` | `oracle_int` (exact integers: the quotient in units of the least subnormal), `oracle_frac` (the repository's `tasks/fdivp/spec_validate/oracle.py`, validated against the Lean spec), `model` (the natural design D1 in Python), `model3` (the reference's netlist in Python) |
| `oracle_dump.cpp` | dumps `oracle.h` over all pairs of a format, for the step `oracles` |
| `model_vs_oracle.py` | the Python model of the reference against `oracle_int` on every pair of the formats up to a bound |
| `fmts_all.txt` | the 66 formats with `W + P <= 14` |

The step `oracles` ties four implementations of the function together (`tasks/fdivp/oracle.py` in exact `Fraction`
arithmetic, `oracle_int`, `tasks/fdivp/spec_validate/oracle.py`, `oracle.h`) before the designs are compared with `oracle.h`:
their agreement is the evidence for the oracle the designs are tested against, and the PROOF of the reference
(`OutN_fdivBits`) then makes every simulated pair a test of the Lean spec `divide` at that format.

Plans: `quick` (about a minute) = oracles on `W + P <= 8`, the reference exhaustively at 12 formats, 20,000 corner-rich
pairs at four large formats; `full` (hours) = oracles to `W + P <= 10`, the reference exhaustively at the 66 formats with
`W + P <= 14` and at `(5, 11)`, `(8, 8)` (2^32 pairs each, 4 slices), 200,000 pairs at 12 formats up to `(11, 53)`, `(2, 62)`.
The records of the full plan are in `tests/fdivp/results/`.
