# Task `mul`: negative designs

Designs the task must reject. Each is a plausible wrong multiplier; the
evidence that the statement rejects it is in `Refute.lean` (kernel-checked
theorems where noted, interpreter-checked counterexamples otherwise), and
`tests/expected.json` (the task's `negatives`) names the `check.py` stage each
is rejected at when submitted with the reference proof
`tasks/mul/reference/mul_n.lean` (`tests/run.py` runs them).

**Does not build at the pinned library yet.** The pinned ls-sv's loader refuses `only_n16.sv` (`PDesign.int32Agrees`:
at the defaults an INT-class constant expression leaves the 32-bit range), so `Refute.lean` does not build at
the pin. It is unchanged and not in the default `lake build` (`tests.lean` does not import it); `tests/run.py`'s
`negatives` step builds it alone and checks that it fails with that refusal (`PENDING_REFUTES`; the svGolf
README, "Building"). The `check.py` rejections in the table do not depend on it, but the same refusal stops
`check.py` on `only_n16.sv` itself one stage early: at the pin it is rejected at `design`, not at the table's
`solution`, and the `negatives` step pins that while the pinned library refuses it (`PENDING_STAGES`).

| design | bug | evidence | rejected at |
|---|---|---|---|
| `drop_carry.sv` | **off-by-one carry**: every adder row drops its carry-out (`s[i][N] = 1'b0`) | `#guard` on the `run2` counterexample at `N = 2`, `a = b = 3`: `p = 1`, not `9`, plus the kernel-checked `dropCarry_refuted_of_run` (that run ⇒ `¬ Statement`); Verilator agrees | `solution` |
| `top_shift.sv` | **wrong bit**: the top half is `s[N-1][N-1:0]` instead of `[N:1]` | `#guard` on the `run2` counterexample at `N = 1`, `a = b = 1`: `p = 3`, not `1`, plus the kernel-checked `topShift_refuted_of_run`; Verilator agrees | `solution` |
| `narrow_out.sv` | **interface trick**: `p` is `2N-1` bits (correct at `N = 1`, where every product fits, wrong from `N = 2` on) | theorem `narrowOut_refuted` (the interface conjunct at `N = 1`) | `solution` |
| `only_n16.sv` | **works only for some `N`**: the reference circuit at `N = 16`, `p = 0` otherwise. At the scoring point it IS the reference: it scores exactly 1962.576 GE, depth 88, and passes 10 000 random Verilator vectors at `N = 16` | theorem `onlyN16_refuted` (a concrete run at `N = 1`, `decide +kernel`) | `solution` |
| `mul_star.sv` | **banned operator**: `assign p = a * b;` (a correct multiplier) | front check and Yosys backstop (`$mul`) | `banlist` |

Why the two loop bugs have interpreter evidence only: their counterexamples
need the generate loops instantiated at a concrete `N`. The kernel cannot
evaluate that (measured: `expandList2 … = .ok …` is not provable by `rfl`,
and `Res`/`Process2` have no `DecidableEq` for `decide +kernel`; the
declaration stage needs `simp` too), and instantiating the loops
symbolically would repeat the reference proof's Part 1 for each design.
`only_n16` escapes this because at `N = 1` its generate-if takes the
loop-free else branch. The counterexamples are `CombTask.counterexample` evaluated by Lean's
interpreter (`#guard`), which is exactly the hypothesis of
`CombTask.not_computes_of_counterexample`: a kernel check of the same
`decide` would make them theorems. Verilator 5.042 reproduces both
(`sim.py --width N`, 10/29; Icarus 12 did on 10/28): `drop_carry`:
`N = 2, a = 3, b = 3, p = 1`; `N = 3, a = 5, b = 7, p = 3`; `top_shift`:
`N = 1, a = 1, b = 1, p = 3`. Exhaustively at `N = 1..4` (Verilator, 10/29;
the same result as the Icarus development run of 10/28): `drop_carry` is correct at `N = 1` (no adder row) and
wrong from `N = 2`; `top_shift` and `only_n16` are wrong from `N = 1`;
`narrow_out` is correct at `N = 1` and wrong from `N = 2`; `mul_star` is
correct everywhere (it is rejected by the banlist only).

## Loading the designs

`Refute.lean` loads each design with `load_sv` (`SvGolf/LoadSv.lean`), which
extracts it at elaboration time through `check/envelope.py` (the source gate,
then the pinned extractor with the task's probe points, exactly as `check.py`
does) into the cache `.lake/envelopes/`; no envelope is committed. `lake
build` re-elaborates `Refute.lean` when a design changes. To look at an
envelope by hand (from the repository's root):

```bash
python3.12 check/envelope.py tests/mul/negative/drop_carry.sv   # prints the cached envelope's path
```
