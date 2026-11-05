import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2Proc
open LeanModels.Sv

load_design_sv2 acc_xor from "acc_xor.sv.json"
load_design_sv2 acc_if from "acc_if.sv.json"
load_design_sv2 acc_nested from "acc_nested.sv.json"

def say (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "rows.log" .append
  h.putStrLn s
  h.flush

/-- each step timed and logged as it finishes -/
def row (name : String) (N : Nat) (mk : Nat → Design2) : IO Unit := do
  let t0 ← IO.monoMsNow
  let d := mk N
  let np := d.processes.size
  let t1 ← IO.monoMsNow
  say s!"{name} N={N}: instantiate {t1-t0}ms processes={np}"
  let uns := d.hasUnsupported
  let t2 ← IO.monoMsNow
  say s!"{name} N={N}: hasUnsupported={uns} {t2-t1}ms"
  let ok := if uns then false else d.lowerComb.isSome
  let t3 ← IO.monoMsNow
  say s!"{name} N={N}: lowerComb={ok} {t3-t2}ms"

#eval show IO Unit from do
  say "start"
  for N in [1, 2, 4, 8, 16, 32, 64, 126, 127, 200] do row "xor" N acc_xor.sem
#eval show IO Unit from do
  for N in [1, 2, 4, 6, 8, 10, 12, 14] do row "if" N acc_if.sem
#eval show IO Unit from do
  for N in [1, 2, 3, 4, 5, 6] do row "nested" N acc_nested.sem
