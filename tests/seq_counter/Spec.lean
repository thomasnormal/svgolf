import SvGolf.TaskSeq

/-!
# The counter, a `seq-family` FIXTURE task (PLAN4 Gate 2)

Not a task of the competition: the positive fixture of the clocked checker (`check.py` kind
`seq-family`, `tests/seq_counter/task.json`). The `SeqTask` is the design study's `cntTask`
(`design/sequential/CounterCycle.lean`) over the trusted text `SvGolf/TaskSeq.lean`: an `N`-bit
up-counter with enable `en`, synchronous active-high reset `rst`, clock `clk`, registered output
`q`.

**txtask-v2 (DRAFT, 2026-11-05).** The fixture states the v2 statement
`SeqTask.StatementV2`: txtask-v1's interface and clock discipline, the claim and termination from
every power-up state (rule 2), Moore outputs (`MooreOutDep`, rule 1) and no x-creating construct
(`XSafe`, rule 3). The negative twins of the soundness probe (H1, F1) and of round 1's attack (W1 to
W4) are refuted against it in `tests/seq_counter/negative/Refute.lean`, and the maintainers' acceptance
table is `tests/seq_counter/negative/Table.lean`.
-/

namespace SvGolf.Tests.SeqCounter

open LeanModels.Sv

/-- **The counter task.** -/
def task : SeqTask where
  inRange N := 1 ≤ N
  clk := some "clk"
  rst := some ("rst", true)
  inputs _ := [("en", 1)]
  outputs N := [("q", N)]
  State N := BitVec N
  init N := 0#N
  step N s := fun (en, ()) => if en = 1#1 then s + 1#N else s
  obs _ s := fun _ => (s, ())

/-- **The challenge statement** for the design family `sem N` (txtask-v2). -/
abbrev Statement (sem : Nat → Design2) : Prop := task.StatementV2 sem

end SvGolf.Tests.SeqCounter
