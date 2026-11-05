import SvGolf.Task
import SvGolf.Comb
import SvGolf.TaskSeq
import SvGolf.Seq
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
* `SvGolf.TaskSeq` — DRAFT of trusted text, for review: the clock
  discipline `ClockedBy`, the cycle-exact `SeqTask` and the transaction
  statement `TxTask` of the sequential tasks.
* `SvGolf.Comb` — untrusted, kernel-checked proof helpers: the reduction of a
  statement to one settled-state lemma for comb designs, the non-vacuity
  theorem, and refutation by a concrete counterexample run.
* `SvGolf.Seq` — untrusted, kernel-checked proof helpers for the DRAFT
  sequential statements: the reduction to one-cycle lemmas
  (`SeqTask.satisfiedAt_of_cycle`) and `CombTask` as `SeqTask`'s
  one-point-state case.
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
