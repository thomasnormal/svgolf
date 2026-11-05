# Validation of the trusted IEEE 754 spec (`tasks/fdivp/IEEE754.lean`)

Untrusted tooling: the differential validation of `SvGolf.IEEE754.divide`, the trusted spec of the task `fdivp`
(`../IEEE754.lean`; what it says is in `../README.md`, "The trusted spec"). The spec was validated as `svgolf/spec/` and
moved into the task on 2026-11-03 with its content unchanged; the five characterization theorems it states are proved
in the task's reference proof (`../reference/fdivp.lean`, section `IEEE754Proofs`, checked by `check.py` like any
submission).

| file | content |
|---|---|
| `oracle.py` | independent Python oracles (standard library only); not the task's advisory `../oracle.py` |
| `validate.py` | differential test driver |
| `Run.lean` | batch runner: evaluates the spec (or Lean core's float model) on a file of operand pairs |
| `check.sh` | Lean checks: `lake build tasks.fdivp.IEEE754` (the spec, its golden vectors and `decide`s) and the runner |

## How it was validated

There are four implementations, and every comparison is bit-exact (NaN results are canonical
in all four).

* **spec**: `SvGolf.IEEE754.divide`, evaluated by `Run.lean` (`lean --run`).
* **core**: Lean core's logical float model, `Float.Model.UnpackedFloat.div` (Lean FRO, in
  the v4.33.0-rc1 toolchain). It is an independent implementation, used only as an
  oracle and never imported by the spec. It supports roundTiesToEven only.
* **A**: `oracle.div_exact`, exact `fractions.Fraction` arithmetic for any format and all
  five modes. It decodes by the §3.4 formulas into rationals, searches the quotient's binade,
  compares exact distances to both neighbours, and decides overflow after unbounded rounding,
  self-checked against the §4.3.1 threshold sentence. It encodes through a table that inverts
  the decoder.
* **B**: `oracle.div_hw16`/`div_hw32`, the CPU's binary64 division followed by CPython's
  `struct` 'e' (`_PyFloat_Pack2`) or 'f' (C cast) rounding. It supports roundTiesToEven
  only. Double rounding is harmless here because 53 ≥ 2p + 2 for p = 11 and p = 24.

All oracles were written for this task in Python 3 standard library only. No external code
was downloaded, built or run (no SoftFloat/TestFloat).

Results of the full run (`python3.9 validate.py`, 2026-10-27, about 30 minutes, at `svgolf/spec/validate/`),
repeated after the last change to the spec's code (the named `zero` encoder):
**57,366,801 spec evaluations, 0 mismatches** in every comparison, and every mutant caught.
Later edits were docstring-only; the final build gives byte-identical results to the validated
build on 1M random binary16 pairs in both roundTiesToEven and roundTowardZero.

| group | vectors | comparisons |
|---|---|---|
| oracle self-check | all 65,536 binary16 patterns; 200,632 binary32 patterns | A's decode/encode = CPython `struct` 'e'/'f' |
| toy formats, exhaustive | every pattern pair of 12 formats (`w`,`p` ≤ 6, `k` ≤ 8): 309,504 pairs | spec = A in all 5 modes; spec = core (RNE) |
| binary16 S0–S5, RNE | **47,759,897** | spec = core and spec = B on every vector; spec = A on 40,000 per set |
| binary16, all modes | 1,003,736 per mode (samples of every set, all of S0 and S4) | spec = A in all 5 modes; 2,750 S4 vectors separate RNE from RNA |
| binary32 | 399,424 specials², 1M random, 780,000 boundary-exponent, 100,000 constructed ties | spec = core = B (RNE); spec = A on samples, all 5 modes |
| mutants | 10 classic divider bugs | each disagrees with the spec somewhere |

The binary16 sets:

* **S0**: specials × specials, every datum class pair, both signs.
* **S1**: every one of the 65,536 patterns × every special (and the transpose), about 20.7M.
* **S2**: all 2^20 trailing-significand pairs at 9 exponent pairs. These sweep the quotient
  through overflow, the normal range, the subnormal/normal boundary and underflow to zero.
* **S3**: all trailing-significand pairs with one or both operands subnormal.
* **S4**: 18,772 constructed exact-tie and near-tie quotients in the subnormal range. For
  division, exact rounding ties can only occur there: a quotient of two p-bit significands is
  never a (p+1)-bit odd midpoint. The run checks that these vectors really separate
  roundTiesToEven from roundTiesToAway.
* **S5**: 5M uniform random pairs (seeded).

Two paths of `round` are covered by the proofs only, never by a test vector. A quotient of two
p-bit significands never falls in (maxFinite, 2^(emax+1)), and a normal-range quotient never
rounds up into the next binade (the max-subnormal → min-normal step is the one exception). So the
overflow threshold itself and the round-up-to-the-next-binade path rest on
`DivideOverflowsAtThreshold` and the proofs, not on differential testing.

The 10 mutants are: flush-to-zero, ties-away, 0/0 → ∞, ∞/0 → NaN, NaN sign = XOR, NaN payload
propagation, RNE overflow → max finite, zero results always +0, no sticky bit, and the
subnormal threshold off by one.

The spec file also carries 43 hand-derived golden vectors (`#guard`), each labelled with its
clause, and 4 kernel-`decide` checks.

### Re-running

The spec is the module `tasks.fdivp.IEEE754` of the svgolf Lake project (library `tasks`), so the Lean side is an
ordinary build; its five characterization theorems are proved in the reference proof, which `check.py` checks
(`tests/run.py --only fdivp`, step `references`). From the repository's root (Python 3.9 matches the repo's harness pin;
any Python 3 works):

```bash
lake build tasks.fdivp.IEEE754                            # spec + golden vectors + kernel decides
tasks/fdivp/spec_validate/check.sh                        # the same build, plus compiling the runner
python3 tasks/fdivp/spec_validate/validate.py --quick     # smoke test, ~11 min, ~13M spec evaluations
python3 tasks/fdivp/spec_validate/validate.py             # full run, ~30 min, ~57M spec evaluations
```

Both scripts accept `LEAN_WRAP` (a prefix for every `lake` call, such as a slot-limiting
wrapper); `validate.py` also accepts `FPSPEC_OUT` (a scratch directory for the vector files;
the default is `<tmpdir>/fpspec_out`). `validate.py --only oracle,toy,b16,b16modes,b32,mutants`
selects groups. `validate.py` builds `tasks.fdivp.IEEE754` with `lake build` and runs
`lake env lean --run tasks/fdivp/spec_validate/Run.lean` from the repository's root. The module was `spec.IEEE754`
(`svgolf/spec/IEEE754.lean`) until 2026-11-03, and `svgolf.spec.IEEE754` while the spec was compiled by hand from the
repository root; the file has no import, and each move changed only the importers' import lines, no byte of it (sha256
`4819c7290aa152f18c16706da82f086c0994cc285bde3fb6e6391449ae6c987b`, `REVIEW.md`). On 2026-11-04 the binary16 and binary32 instances were
renamed after their formats (`divBinary16`, `divBinary32`; `divide` unchanged; sha256
`ea783e2a80d8cfc63b65087c7de0fac92ea584352817a0ea6e38239aa2726218`, `REVIEW.md`).
