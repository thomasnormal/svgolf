import SvGolf.LoadSv
import tasks.aes_sbox.Spec
import LeanModels.Sv.CombExhaustive

set_option Elab.async false
open Lean Elab Command in
elab "count_hb " "in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  let h1 ← IO.getNumHeartbeats
  logInfo m!"HB {h1 - h0}"

load_sv bp from "tasks/aes_sbox/reference/sbox_bp.sv"

open LeanModels.Sv LeanModels.Sv.Exh LeanModels.Sv.CombView

def S : CombView.Summary := match bp.pdesign.summary with | .ok s => s | .error _ => default
def σ0 : String → Int := S.val []
def off : String → Nat := layout S σ0
def wd : String → Nat := S.dw σ0
def net : List BSite := sitesOf S σ0 (List.range S.lsites.length)

#eval S.lsites.length
#eval (S.lsites.map (·.hdrs.length)).sum
#eval (layoutL S σ0).take 12
#eval (List.range 8).map fun j => (run off wd net ((0x53 : Nat) <<< off "x")).testBit (off "y" + j)
#eval (SvGolf.Tasks.AesSbox.sbox 0x53#8)

count_hb in
theorem probe : ∀ n : Fin 256, ∀ j : Fin 8,
    (run off wd net (n.val <<< off "x")).testBit (off "y" + j.val) =
      (SvGolf.Tasks.AesSbox.sbox (BitVec.ofFin n)).getLsbD j.val := by
  decide +kernel
