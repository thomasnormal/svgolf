# `tests/fdivp/negative/`: designs the checker must reject

Each is submitted with the first reference's proof (D3, `reference/fdivp.lean`; `tests/expected.json`, `negatives`) and rejected at the stage given there.

| design | what it tries | stage |
|---|---|---|
| `div_op.sv` | the reference with the restoring-division family replaced by run-time `/` and `%` (right at every format: exhaustive at the small formats) | `banlist`: banned `/`, `%` (front check) and `$div`, `$mod` cells (Yosys backstop) |
| `rm_pin.sv` | the reference plus an input `rtz` that is never read | `solution`: `sv_interface` refuses the ports (the interface conjunct) |
| `status_flag.sv` | the reference plus an output `inexact` (constant 0) | `solution`: the interface conjunct |
| `wide_q.sv` | the reference with `q` one bit wider (`W + P + 1` bits, the top bit 0): a wider `q` (the former 16-bit task's `inexact_flag.sv` had a 17-bit `q`) | `solution`: the interface conjunct |
| `const_nan.sv` | `q` = the canonical quiet NaN always (right only on the NaN-producing pairs) | `solution` |

## The Lean evidence (`Refute.lean`, built by `lake build`, library `tests`)

The refutations of the former 16-bit task (`constNan_refuted`, `rmPin_refuted`, `inexactFlag_refuted`) are ported to the
two-parameter statement at the smallest format `(2, 2)`, in `clmul`'s shape: a kernel-checked theorem "IF this concrete run
disagrees with the task (`CombTask.counterexample … = true`), or IF the ports differ from the task's, at one format in
range, THEN `¬ Statement`" (`refuted_of_run`, `refuted_of_ports`), and a `#guard` checking the hypothesis with Lean's
interpreter (compiled `instantiateGD2` and `run2`; NOT the kernel: a generate expansion does not reduce by `decide +kernel`,
so the former task's fully kernel-evaluated `constNan_refuted` is now conditional on a `#guard`). Axioms `propext`,
`Classical.choice`, `Quot.sound` (pinned by `#guard_msgs` on `#print axioms`).

* `constNan_refuted`: `1 / 1` at `(2, 2)` (`0b0010 / 0b0010`) is `0b0010`, the design gives the NaN `0b0111`.
* `rmPin_refuted`, `statusFlag_refuted`, `wideQ_refuted`: the ports differ at `(2, 2)` (the interface conjunct).

`div_op.sv` is refused by the banlist, not by the statement (it computes the right function).
