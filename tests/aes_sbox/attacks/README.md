# `aes_sbox`: attacks on the checker

Designs where ls-sv and Yosys could read one text differently, specialised to a table-shaped task. Each goes
through `check.py --unproved` and must be rejected at the stage `tests/expected.json` gives. Where it says
`postsynth_alone: rejects`, the post-synthesis check with the source gate and the fourstate stage bypassed
also rejects it. Because the input space is 256 values and the fixed vectors plus the task `corners` are all 256 of them, that check
is EXHAUSTIVE here in both modes (measured: 256 of 256 vectors, light and full), so an attack that differs on
a single input is rejected, which no sampling check could promise.

| design | trick | stage | post-synthesis alone |
|---|---|---|---|
| `case_missing_x.sv` | a table that omits `S(0x53)` and sends it to `default: y = 8'bx`: Yosys may choose any value there | `source` (x literal digit) | rejects: differs on exactly 1 of 256 inputs |
| `case_missing_nodefault.sv` | the same without a default: an inferred latch | `fourstate` | (the scorer cannot price a latch: an infrastructure error, not a verdict) |
| `unique_case_partial.sv` | `unique case` over a table with a missing entry, no default | `source` (qualifier) | rejects: 1 of 256 |
| `unique_zero_ge.sv` | a correct S-box, then `unique case (1'b1)` with an arm that never matches: ls-sv keeps the S-box, Yosys drives a constant (0 GE) | `source` (qualifier) | rejects: 256 of 256 |

ADVISORY entries (in `tests/expected.json`, `advisory: true`: they refuse nothing) pin the checker's advisory
outputs for this task: `tactics_reference` (the reference is inside the `sv_comb` tactic fragment and the
oracle agrees with it on all 256 inputs), `table_unproved` (the `case` table loads with no unsupported node and
reaches the end of `check.py --unproved`; its `--tactics` verdict is recorded) and `functional_no_constant`,
`functional_one_entry`, `functional_reversed_bits`, `functional_inverse_sbox` (the four functionally wrong
negative designs reach `unproved` and the task's oracle reports the disagreement of ls-sv's outputs in ONE
warning: the ls-sv-level evidence that they are wrong, since the negatives run against the reference proof
only fail to compile).

Not here, on purpose: a casez design with `?` wildcards. It is a legal (and, for this function, useless)
way to write the table; the casez forms that are tricks (`x` digits in an item) are the source gate's, tested
by `score/tests/gate/casez_x_item.sv`, and `===` against an x literal is `tests/add/attacks/eqx_x.sv`'s
class; neither gains anything new on a function of one 8-bit input.
