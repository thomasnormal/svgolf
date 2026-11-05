import SvGolf.TaskSeq

/-!
# The counter, a `seq-family` FIXTURE task (PLAN4 Gate 2)

Not a task of the competition: the positive fixture of the clocked checker (`check.py` kind
`seq-family`, `tests/seq_counter/task.json`). The `SeqTask` is the design study's `cntTask`
(`design/sequential/CounterCycle.lean`) over the frozen trusted text `SvGolf/TaskSeq.lean`
(txtask-v1): an `N`-bit up-counter with enable `en`, synchronous active-high reset `rst`, clock
`clk`, registered output `q`.
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

/-- **The challenge statement** for the design family `sem N`. -/
abbrev Statement (sem : Nat → Design2) : Prop := task.Statement sem

end SvGolf.Tests.SeqCounter
