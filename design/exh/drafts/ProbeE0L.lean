import SvGolf.LoadSv
import tasks.aes_sbox.Spec
import LeanModels.Sv.CombExhaustive

/-! G-E0, the evaluation cost alone: the Design2 evaluator on a LITERAL copy of `bp.sem` (materialized by
compiled evaluation and re-parsed), since `X.sem` itself does not reduce in the kernel. -/

set_option Elab.async false
open Lean Elab Command in
elab "count_hb " "in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  let h1 ← IO.getNumHeartbeats
  logInfo m!"HB {h1 - h0}"

load_sv bp from "tasks/aes_sbox/reference/sbox_bp.sv"

open LeanModels.Sv LeanModels.Sv.Exh

def localSt (off wd : String → Nat) (e : Nat) (ns : List String) : SvState :=
  ns.map fun n => (n, LVec.ofBoolFn (wd n) fun i => e.testBit (off n + i))

def stepP (d : Design2) (off wd : String → Nat) (e : Nat) : Process2 → Nat
  | .assign t ex => match t.window? d with
    | some (n, lo, w) => match evalPure2 (localSt off wd e (ex.reads.map ReadWin.name)) ex with
        | .ok v => orBits e (off n + lo) (fun k => (v.resizeU w).boolAt k) w
        | _ => e
    | none => e
  | _ => e

def runP (d : Design2) (off wd : String → Nat) : List Process2 → Nat → Nat
  | [], e => e
  | p :: ps, e => runP d off wd ps (stepP d off wd e p)

def layD (d : Design2) : List (String × Nat) :=
  (d.decls.toList.foldl (fun (acc : List (String × Nat) × Nat) dc =>
    (acc.1 ++ [(dc.name, acc.2)], acc.2 + dc.width)) ([], 0)).1

open Lean Elab Command Term Meta in
/-- `materialize X from e`: evaluate `e` (compiled), print it with `Repr`, parse it back, define `X`. -/
elab "materialize " id:ident " from " t:term : command => do
  let s ← liftTermElabM do
    let e ← elabTerm t (some (mkConst ``LeanModels.Sv.Design2))
    let v ← unsafe evalExpr LeanModels.Sv.Design2 (mkConst ``LeanModels.Sv.Design2) e
    pure (toString (repr v))
  match Parser.runParserCategory (← getEnv) `term s with
  | .error err => throwError "parse: {err}"
  | .ok stx => elabCommand (← `(def $id : LeanModels.Sv.Design2 := $(⟨stx⟩)))

materialize DL from bp.sem

def offL (n : String) : Nat := ((layD DL).lookup n).getD 0
def wdL (n : String) : Nat := (DL.declWidth n).getD 0

#eval DL.processes.size
#eval (List.range 8).map fun j => (runP DL offL wdL DL.processes.toList ((0x53 : Nat) <<< offL "x")).testBit (offL "y" + j)

count_hb in
theorem probeL : ∀ n : Fin 256, ∀ j : Fin 8,
    (runP DL offL wdL DL.processes.toList (n.val <<< offL "x")).testBit (offL "y" + j.val) =
      (SvGolf.Tasks.AesSbox.sbox (BitVec.ofFin n)).getLsbD j.val := by
  decide +kernel
