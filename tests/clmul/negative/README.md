# Task `clmul`: negative designs

Designs the task must reject. Each is a plausible wrong carry-less multiplier (or a right one that breaks a
rule); the evidence that the statement rejects it is in `Refute.lean` (a kernel-checked theorem turning a
concrete run, or a port mismatch, into `¬ Statement`, whose hypothesis is checked by `#guard`, i.e. by Lean's
interpreter running ls-sv), and `tests/expected.json` (the task's `negatives`) names the `check.py` stage each
is rejected at when submitted with the task's first reference (`tests/run.py` runs them).

**Waits for the int32 port round.** The pinned ls-sv's loader refuses `only_n16.sv` (`PDesign.int32Agrees`:
at the defaults an INT-class constant expression leaves the 32-bit range), so `Refute.lean` does not build at
the pin. It is unchanged and not in the default `lake build` (`tests.lean` does not import it); `tests/run.py`'s
`negatives` step builds it alone and checks that it fails with that refusal (`PENDING_REFUTES`; the svGolf
README, "Building"). The `check.py` rejections in the table do not depend on it.

| design | bug | evidence | rejected at |
|---|---|---|---|
| `top_shift.sv` | **wrong bit**: the top `N-1` output bits are read one position too low, `r[N-1][m]` instead of `r[N-1][m+1]` | `#guard` on the `run2` counterexample at `N = 2`, `a = b = 3`: `p = 3'b001`, not `3'b101`; `topShift_refuted` | `solution` |
| `drop_top.sv` | **off-by-one**: every row `i >= 1` drops its top term (`r[i][N-1] = 1'b0`) | `#guard` at `N = 2`, `a = b = 3`: `p = 3'b001`; `dropTop_refuted` | `solution` |
| `or_accumulate.sv` | **wrong gate**: the rows accumulate with OR, not XOR | `#guard` at `N = 2`, `a = b = 3`: `p = 3'b111`; `orAccumulate_refuted` | `solution` |
| `reversed_p.sv` | **bit orientation**: coefficient `k` at `p[2N-2-k]` (GHASH's reflected convention); right at `N = 1` | `#guard` at `N = 2`, `a = b = 1`: `p = 3'b100`, not `3'b001`; `reversedP_refuted` | `solution` |
| `wide_out.sv` | **interface**: `p` is `2N` bits with a constant-zero top bit (the VALUE is right) | `#guard` on the output ports at `N = 1`; `wideOut_refuted` (the interface conjunct) | `solution` |
| `only_n16.sv` | **works only for some `N`**: the reference array at `N = 16`, `p = 0` elsewhere; at the scoring point it IS the reference (same score) | `#guard` at `N = 1`, `a = b = 1`: `p = 0`; `onlyN16_refuted` | `solution` |
| `plus_xor.sv` | **banned operator**: the XOR of every row is a one-bit run-time `+` (the carry is truncated away): a CORRECT multiplier | front check and Yosys backstop (`$add`) | `banlist` |
| `kronecker_mul.sv` | **banned operator**: Kronecker substitution, `sp = sa * sb` on the bit-spread operands, parities read back: a CORRECT multiplier for `N < 128` | front check and Yosys backstop (`$mul`) | `banlist` |

Both banlist designs synthesize to exactly the reference's netlist at `N = 16` (772.267 GE, depth 6: Yosys
folds the zero bits of the spread operands, and a one-bit `+` is an XOR), so the ban protects the task, not the
score.

Why interpreter evidence only for the four loop designs: their counterexamples need the generate loops
instantiated at a concrete `N`, which the kernel cannot evaluate (measured for `mul`: `tests/mul/negative`),
and instantiating the loops symbolically would repeat the reference proof's structure part for each design.
Verilator reproduces every one of them (`tests/clmul/validate/sim.py DESIGN --plan quick --bad`, which exits
0 iff some point shows a mismatch; `wide_out`, `plus_xor` and `kronecker_mul` are functionally right and are
simulated as such). `only_n16` and `wide_out` are wrong at `N = 1`, the other four at `N = 2`.

## Loading the designs

`Refute.lean` loads each design with `load_sv` (`SvGolf/LoadSv.lean`), which extracts it at elaboration time
through `check/envelope.py` into the cache `.lake/envelopes/`; no envelope is committed. To look at one by hand
(from the repository's root): `python3.12 check/envelope.py tests/clmul/negative/or_accumulate.sv`.
