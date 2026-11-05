import ClmulNested
import PriEnc
import PopCount

/-!
# The E statements have no `run2` in their chain (WS3) — a build-time check, untrusted

For each loop design's `statement_E0` (the task over E-core-0), the transitive closure of the
constants its type and proof use contains none of `run2`'s execution and observation constants
(`run2Names`): the chain is E's. The `run2` statement `ClmulNested.statement` is the control: its
closure must contain them, so the check is not vacuous. Compiled by `compile-loop.sh`; a violation
is a build error.
-/

open Lean

namespace SvGolf.Design.Loop.NoRun2

/-- `run2`'s execution semantics and its observation backend. -/
def run2Names : List Name :=
  [``LeanModels.Sv.execStmt2, ``LeanModels.Sv.execStmts2, ``LeanModels.Sv.evalExpr2,
   ``LeanModels.Sv.runCombProcess2, ``LeanModels.Sv.combPass2, ``LeanModels.Sv.combSettle2,
   ``LeanModels.Sv.cycleStep2, ``LeanModels.Sv.run2, ``LeanModels.Sv.Runs2, ``LeanModels.Sv.Models2,
   ``LeanModels.Sv.Terminates2, ``LeanModels.Sv.Loop2.Denotes, ``LeanModels.Sv.Observe.Obs_run2]

/-- The `run2` constants in the transitive closure of `root` (type and value). -/
def run2Hits (root : Name) : CoreM (List Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array Name := #[root]
  let mut hits : List Name := []
  while 0 < stack.size do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if run2Names.contains n then hits := n :: hits
    if let some ci := env.find? n then
      for m in ci.type.getUsedConstants do stack := stack.push m
      if let some v := ci.value? (allowOpaque := true) then
        for m in v.getUsedConstants do stack := stack.push m
  return hits

#eval show CoreM Unit from do
  for n in run2Names do
    unless (← getEnv).contains n do throwError "run2 constant {n} not found: the check would be vacuous"
  unless !(← run2Hits ``SvGolf.Design.LoopG1.statement).isEmpty do
    throwError "control failed: the run2 statement's chain shows no run2 constant"
  for root in [``SvGolf.Design.LoopG1.statement_E0, ``SvGolf.Design.LoopG2.PriEnc.statement_E0,
      ``SvGolf.Design.LoopG2.PopCount.statement_E0] do
    let hits ← run2Hits root
    unless hits.isEmpty do throwError "{root} has run2 in its chain: {hits}"

end SvGolf.Design.Loop.NoRun2
