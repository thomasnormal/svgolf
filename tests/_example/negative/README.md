# `_example`: designs that must be rejected

Each design here tries one way to satisfy a weaker statement than the task's
without computing `a & b` on an exact `a`/`b`/`y` interface. Every Lean-level
case is REFUTED in `Refute.lean` (built by `lake build`): a kernel-checked
proof of `¬ SvGolf.Tasks.Example.Statement <design>.sem`, standard axioms only.

| design | what it tries | how it fails | refutation |
|---|---|---|---|
| `or_gate.sv` | a wrong function, `y = a \| b` | at `N = 1`, `a = 1`, `b = 0`, the snapshot has `y = 1` | `orGate_refuted` (one concrete run) |
| `reads_x.sv` | reads an undriven net: `y = a & b & ~z` | `z` is `x`, so `y = x` when `a = b = 1`; the checker refuses it before any proof, at the `fourstate` stage (Yosys `check`: `z` is used but undriven) | `readsX_refuted` (one concrete run) |
| `wide_out.sv` | an `N+1`-bit output port | the interface conjunct pins `y` at `N` bits | `wideOut_refuted` |
| `extra_in.sv` | a hidden input `en` (`y = en ? a & b : 0`) | the interface conjunct pins the inputs to `a`, `b` | `extraIn_refuted` |
| `arith_and.sv` | the right function through `(a + b) - (a \| b)` | banned run-time `+` and `-` (banlist, before Lean) | none needed: it satisfies the statement, and `score/banlist.py` rejects it |

`tests/expected.json` lists these under the task's `negatives` with the
checker stage each must fail at; `tests/run.py` runs `check.py` on them with
the reference proof `tasks/_example/reference/band.lean` (which does not prove
the statement for a different design, so the Lean-level cases fail at the
`solution` stage, except `reads_x.sv`, which the `fourstate` stage refuses
first; the refutations above show that no proof could succeed).

## Loading the designs

`Refute.lean` loads each design with `load_sv` (`SvGolf/LoadSv.lean`), which
extracts it at elaboration time through `check/envelope.py` (the source gate,
then the pinned extractor with the task's probe points, exactly as `check.py`
does) into the cache `.lake/envelopes/`; no envelope is committed. `lake
build` re-elaborates `Refute.lean` when a design changes. To look at an
envelope by hand (from the repository's root):

```bash
python3.12 check/envelope.py tests/_example/negative/or_gate.sv   # prints the cached envelope's path
```
