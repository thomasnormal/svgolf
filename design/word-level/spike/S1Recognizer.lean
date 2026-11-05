import LeanModels.Sv.Ingest2
import LeanModels.Sv.CombProcTactic

/-!
B2 spike, part 1 (scratch, no tree edit): what the recognizer sees of `assign y = a + b` today.
Envelopes: `env/*.sv.json` (python3.12 svgolf/check/envelope.py, symbolic mode).
-/
open LeanModels.Sv LeanModels.Sv.CombView

load_design_sv2 addw4 from "svgolf/design/word-level/spike/env/addw4.sv.json"
load_design_sv2 addw5 from "svgolf/design/word-level/spike/env/addw5.sv.json"
load_design_sv2 addw3 from "svgolf/design/word-level/spike/env/addw3.sv.json"
load_design_sv2 addwc from "svgolf/design/word-level/spike/env/addwc.sv.json"

def procs (d : PDesign) := d.processes

#eval procs addw4.pdesign
#eval procs addw5.pdesign
#eval procs addw3.pdesign

/-- the rhs of the first assign -/
def rhs0 (d : PDesign) : PExpr :=
  match d.processes.head? with
  | some (.assign _ v) => v
  | _ => .int 0

def msg : Except String (List Acc) → String
  | .ok a => s!"ok {a.length} reads"
  | .error e => s!"ERR: {e}"

#eval msg (rdsOf? [] (rhs0 addw4.pdesign))
#eval msg (rdsOf? [] (rhs0 addw5.pdesign))
#eval msg (rdsOf? [] (rhs0 addw3.pdesign))
-- the operands, one level down (what `leafRd?` would see once `+` is a node)
def ops (e : PExpr) : List PExpr :=
  match e with
  | .binary _ l r => [l, r]
  | .resize _ a => [a]
  | _ => []
#eval (ops (rhs0 addw5.pdesign)).map fun e => msg (rdsOf? [] e)
#eval (ops (rhs0 addw3.pdesign)).map fun e => msg (rdsOf? [] e)
#eval (ops (rhs0 addw3.pdesign)).map fun e => (ops e).map fun e => msg (rdsOf? [] e)
