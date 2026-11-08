import SvGolf.Task
import SvGolf.Comb
import SvGolf.TaskSeq
import SvGolf.TaskReact
import SvGolf.Seq
import SvGolf.XFree
import SvGolf.SeqV2
import SvGolf.React
import SvGolf.RoundRobin
import SvGolf.LoadSv
import SvGolf.CoreSimp
-- The ls-sv proof libraries the references import (see the last paragraph below).
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombExhaustiveTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.Known2
import LeanModels.Sv.Lib
import LeanModels.Sv.Mono2
import LeanModels.Sv.ProcNoQualified
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.SeqProfile

/-!
# svGolf — the framework library

* `SvGolf.Task` — the TRUSTED task-statement helpers (`CombTask`,
  `CombTask.Statement`): what every challenge statement is built from.
* `SvGolf.TaskSeq` — TRUSTED text in two parts (its Status lists them): FINAL
  (decided 2026-11-07), the primitives the reactive kind shares (the clock
  discipline `ClockedBy`, the reset release, txtask-v2's power-up runs and
  rule 3, `XSafe`); a DRAFT, the cycle-exact `SeqTask`, the transaction
  statement `TxTask` and `StreamTask` of the sequential tasks, and txtask-v2's
  tx/stream half.
* `SvGolf.TaskReact` — TRUSTED text, final (decided 2026-11-07; written 2026-11-05): the
  reactive kind `ReactTask` (a controller that runs for ever: a safety monitor and bounded
  response over the whole input trace, Moore outputs; since 2026-11-06 txtask-v2's rules 2 and 3:
  the claims from every power-up state, no x-creating construct), whose first task is
  `tasks/arbiter`.
* `SvGolf.Comb` — untrusted, kernel-checked proof helpers: the reduction of a
  statement to one settled-state lemma for comb designs, the non-vacuity
  theorem, and refutation by a concrete counterexample run.
* `SvGolf.Seq` — untrusted, kernel-checked proof helpers for the DRAFT
  sequential statements: the reduction to one-cycle lemmas
  (`SeqTask.satisfiedAt_of_cycle`) and `CombTask` as `SeqTask`'s
  one-point-state case.
* `SvGolf.XFree` — untrusted, kernel-checked: the x-free lemma of txtask-v2's rule 3
  (`xfree_expr`, `xfree_stmt`, `xfree_cycle`, `xfree_runsAt`): with known inputs, a known state
  and no x-creating construct (`XSafe`), every value ls-sv's evaluator computes is known, so no
  decision of a run from a power-up state reads an `x`.
* `SvGolf.SeqV2` — untrusted, kernel-checked proof helpers for the
  txtask-v2 statements of `SvGolf.TaskSeq`: the v2 reductions
  (`SeqTask.satisfiedAtV2_of_cycle`, `TxTask.satisfiedAtV2_of_phases`,
  `StreamTask.satisfiedAtV2_of_phases`: the v1 reductions' data, the shape
  holding at every power-up state), `TerminatesPU.of_invariant`, the power-up
  states of a declaration list (`powerUp_cons`, `powerUps`), and rule 1's
  `MooreOutDep.of_noComb` and checker `mooreOutDepB` (`MooreOutDep.of_check`).
* `SvGolf.React` — untrusted, kernel-checked proof helpers for the reactive kind
  (2026-11-05): the reduction `ReactTask.satisfiedAt_of_rank` (a rank model whose shape every
  power-up state has: one-cycle reset and step obligations with a rank that drops at every
  triggered, unanswered step), the window argument `ReactTask.responds_of_rank`,
  `ReactTask.snapshots_known` (the x-free lemma on the statement's runs), and
  `mooreOut_of_combTargets`.
* `SvGolf.RoundRobin` — untrusted, kernel-checked word-level facts for round-robin arbiters, for
  every width: the lowest set bit `x &&& (~~~x + 1)`, the thermometer above a one-hot, the mask
  round-robin's pick and next mask with its one-step theorem in the cyclic distance.
* `SvGolf.CoreSimp` — the `sv_core_simp` command: the sv_comb tactics see Lean core's simp
  set again after an `import Mathlib.Tactic` (README.md, "Mathlib in submissions").
* `SvGolf.LoadSv` — the `load_sv` command: load a design from its `.sv` file,
  extracted at elaboration time through svGolf's one extraction path
  (`check/envelope.py`) into a cache under `.lake/envelopes/`. The negative
  designs' refutations (`tests/<name>/negative/Refute.lean`) use it.

The checker's comparator (`check/Comparator.lean`) is a script, not part of
this library. See `README.md`.

The `LeanModels.Sv` imports above are every `LeanModels.Sv` module that a
reference proof (`tasks/*/reference/*.lean`, `tests/*/reference/*.lean`)
names in its imports. Nothing in this library uses them. They are here so
that building this library (`lake build`, and the checker's `trusted` stage
`lake build SvGolf tasks svgolf-eval`) builds their oleans. A solution's
compile only reads oleans, so a module that no build target reaches is
missing on a fresh checkout: "object file … does not exist". A working tree
that built the module some other way hides this. The comb tactic library was
built only by lean-surfaces' `tools/check_sv_chain.sh`, and the sequential
library (`SeqProfile`, `SeqFamily`, `Seq2Cycle`, `NbaCommit`) by nothing.
Add a new reference's `LeanModels.Sv` imports here.
-/
