import SvGolf.LoadSv
import tasks.aes_sbox.Spec
import LeanModels.Sv.CombExhaustive

/-! G-E0, the Design2 alternative: each assign evaluated by `evalPure2` on a LOCAL state built from the packed
environment (only its read names), so that the window-level congruence `evalPure2_congr_reads` applies. -/

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

def D : Design2 := bp.sem
def offD (n : String) : Nat := ((layD D).lookup n).getD 0
def wdD (n : String) : Nat := (D.declWidth n).getD 0
def procs : List Process2 := D.processes.toList

#eval procs.length
#eval (List.range 8).map fun j => (runP D offD wdD procs ((0x53 : Nat) <<< offD "x")).testBit (offD "y" + j)
#eval (SvGolf.Tasks.AesSbox.sbox 0x53#8)

count_hb in
theorem probeD : ∀ n : Fin 256, ∀ j : Fin 8,
    (runP D offD wdD procs (n.val <<< offD "x")).testBit (offD "y" + j.val) =
      (SvGolf.Tasks.AesSbox.sbox (BitVec.ofFin n)).getLsbD j.val := by
  decide +kernel
