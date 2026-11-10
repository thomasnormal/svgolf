import tests.sorter.negative.Refute

/-!
# Task `sorter`: kernel refutations of generated mutants of the reference (untrusted, kernel-checked; 2026-11-08)

Nothing here is part of the trusted base. `tests/mutate.py` generates the mutants of
`tasks/sorter/reference/sorter_ins.sv` from Slang's syntax tree, and `tests/sorter/mutants/classify.py` (the engine
`tests/txsweep.py`) sorts them: killed by the task's checks, proved equivalent to the reference, or a survivor
(`tests/sorter/mutants/MANIFEST.json`). This file refutes a SAMPLE of the killed ones by the statement itself, for
EVERY latency function, each by ONE run that the kernel evaluates (`Refute.lean`'s `stream_refuted`: a reset, one
transaction, the run to rest, then any number of idle entries; or `early_refuted`; or a structural conjunct), at
`(N, W) = (2, 2)`, from a named power-up state. Each theorem is stated for every design family whose instance at
`(2, 2)` is the hand-built twin.

Each mutant's source is in `tests/sorter/mutants/<id>.sv` (the generator's output under a three-line header); its
twin `<id>D` is the reference's twin `refD` (`Refute.lean`) with the one mutated node changed, and is checked equal
to the instance at `(2, 2)` of the design `load_sv` loads (`#guard reprStr …`, as for the reference's twin).

| mutant | operator | edit (sorter_ins.sv) | clause | refutation |
|---|---|---|---|---|
| m005 | CRP (index) | `input logic [W-2:0] in_data` | `Interface`: `in_data` is 1 bit wide | `m005_refuted` |
| m038 | CRP (index) | the push test reads `data[(k+2)*W +: W]` | `XSafe`: the select is past the vector, an `x` literal | `m038_refuted` |
| m020 | NEG | the cell's `if (in_valid)` becomes `if (!(in_valid))` | on `2, 3` it emits `2, 2` | `m020_refuted` |
| m026 | ROR | the push test `in_data > data[(k+1)*W +: W]` becomes `==` | on `2, 3` it emits `3, 3` | `m026_refuted` |
| m040 | DEL | the push `data[k*W +: W] <= data[(k+1)*W +: W]` deleted | on `2, 3` it emits `0, 3` | `m040_refuted` |
| m061 | DEL | the store `data[k*W +: W] <= in_data` deleted | on `3, 2` it emits `0, 3` | `m061_refuted` |
| m075 | DEL | the token shift `tok[k] <= tok[k+1]` deleted | on `2, 3` it emits nothing, for ever | `m075_refuted` |
| m093 | DEL | the token reset `tok[k] <= 1'b0` deleted | from the power-up `tok = 11`, `out_valid` = 1 before any start | `m093_refuted` |
| m099 | NEG | the top cell's `if (in_valid)` negated | on `2, 3` it emits `0, 0` | `m099_refuted` |
| m141 | DEL | the top token's load `tok[N-1] <= in_valid` deleted | on `2, 3` it emits nothing, for ever | `m141_refuted` |
| m178 | DEL | `out_valid <= tok[0]` deleted | on `2, 3` it emits nothing, for ever | `m178_refuted` |
| m180 | DEL | `out_data <= data[0 +: W]` deleted | on `2, 3` it emits `0, 0` (out_data keeps its power-up 0) | `m180_refuted` |

All twelve are rejected by check.py's stages that need no proof (the manifest records the stage and the point:
`extract` for m005, `fourstate` for m038 and m180, `postsynth` for the others).
-/

namespace SvGolf.Tasks.Sorter.Mutants

open LeanModels.Sv SvGolf SvGolf.Tasks.Sorter.Refute

/-- `!(e)`. -/
def notE (e : Expr2) : Expr2 := .unary .lnot e

/-! ## The twins (one node each) -/

/-- m005: `in_data` declared one bit narrower (`[W-2:0]`); the loader widens every read of it to the 2-bit
context (`resize`). -/
def m005D : Design2 :=
  let ie : Expr2 := .resize 2 (.ident "in_data")
  sWithD (sDecls.set! 4 { name := "in_data", width := 1, isInput := true })
    (topWith (ins := topInsE ie)) outRef
    (cellWith (ins := cellInsW (gtE ie (dR 2)) cellPush (gtE ie (dR 0)) (dW 0 ie)))

/-- m038: the push test reads past `data` (an `x` literal at `N = 2`). -/
def m038D : Design2 :=
  sWith topRef outRef (cellWith (ins := cellInsW (gtE (.ident "in_data") (.lit ⟨#[.lx, .lx]⟩)) cellPush cellT2 cellStore))

def m020D : Design2 := sWith topRef outRef (cellWith (cond := notE (.ident "in_valid")))
def m026D : Design2 :=
  sWith topRef outRef (cellWith (ins := cellInsW (.binary .eq (.ident "in_data") (dR 2)) cellPush cellT2 cellStore))
def m040D : Design2 := sWith topRef outRef (cellWith (ins := cellInsW cellT1 nop cellT2 cellStore))
def m061D : Design2 := sWith topRef outRef (cellWith (ins := cellInsW cellT1 cellPush cellT2 nop))
def m075D : Design2 := sWith topRef outRef (cellWith (tok := nop))
def m093D : Design2 := sWith topRef outRef (cellWith (rst := .block #[dW 0 (c2 0), nop]))
def m099D : Design2 := sWith (topWith (cond := notE (.ident "in_valid"))) outRef cellRef
def m141D : Design2 := sWith (topWith (tok := nop)) outRef cellRef
def m178D : Design2 := sWith topRef (outP nop outOd outRst) cellRef
def m180D : Design2 := sWith topRef (outP outOv nop outRst) cellRef

load_sv m005L from "tests/sorter/mutants/m005.sv"
load_sv m038L from "tests/sorter/mutants/m038.sv"
load_sv m020L from "tests/sorter/mutants/m020.sv"
load_sv m026L from "tests/sorter/mutants/m026.sv"
load_sv m040L from "tests/sorter/mutants/m040.sv"
load_sv m061L from "tests/sorter/mutants/m061.sv"
load_sv m075L from "tests/sorter/mutants/m075.sv"
load_sv m093L from "tests/sorter/mutants/m093.sv"
load_sv m099L from "tests/sorter/mutants/m099.sv"
load_sv m141L from "tests/sorter/mutants/m141.sv"
load_sv m178L from "tests/sorter/mutants/m178.sv"
load_sv m180L from "tests/sorter/mutants/m180.sv"

-- the hand-built twins are the loaded designs at the refutations' point
#guard reprStr (m005L.sem 2 2) == reprStr m005D
#guard reprStr (m038L.sem 2 2) == reprStr m038D
#guard reprStr (m020L.sem 2 2) == reprStr m020D
#guard reprStr (m026L.sem 2 2) == reprStr m026D
#guard reprStr (m040L.sem 2 2) == reprStr m040D
#guard reprStr (m061L.sem 2 2) == reprStr m061D
#guard reprStr (m075L.sem 2 2) == reprStr m075D
#guard reprStr (m093L.sem 2 2) == reprStr m093D
#guard reprStr (m099L.sem 2 2) == reprStr m099D
#guard reprStr (m141L.sem 2 2) == reprStr m141D
#guard reprStr (m178L.sem 2 2) == reprStr m178D
#guard reprStr (m180L.sem 2 2) == reprStr m180D

/-! ## The refutations, for every latency function -/

/-- **m005 is rejected** (`Interface`): its input port `in_data` is 1 bit wide at `(2, 2)`. -/
theorem m005_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m005D) :
    ¬ Statement sem lat :=
  refuted_of_sat (fun _ hs => absurd hs.1.1 (by decide +kernel)) sem lat hd

/-- **m038 is rejected** (rule 3, `XSafe`): the out-of-range select is an `x` literal. -/
theorem m038_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m038D) :
    ¬ Statement sem lat :=
  refuted_of_sat (fun _ hs => absurd hs.2.2.2.2.2 (by decide +kernel)) sem lat hd

theorem m020_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m020D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m026_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m026D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m040_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m040D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m061_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m061D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 3#2 2#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **m075 is rejected**: no value is ever emitted; the run is at rest with `out_valid` = 0 after the prefix. -/
theorem m075_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m075D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-- **m093 is rejected** (the guarantee's "0 before the first start"): from the power-up with both tokens 1, the
reset clears only the top token, and the snapshot after the release shows `out_valid` = 1 with no start. -/
theorem m093_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m093D) :
    ¬ Statement sem lat :=
  refuted_of (early_refuted_of_check (powerUp_onesAt _ ["tok"])
    (rows := (true, false, false, 0#2) :: List.replicate 3 (idle 2)) (c := 1) (by decide +kernel)) sem lat hd

theorem m099_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m099D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m141_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m141D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m178_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m178D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

theorem m180_refuted (sem : Nat → Nat → Design2) (lat : Nat → Nat → Nat) (hd : sem 2 2 = m180D) :
    ¬ Statement sem lat :=
  refuted_of (stream_refuted_of_check (powerUp_zeros _) (rows := rowsTxn 2#2 3#2) (s := 1) (by decide +kernel))
    sem lat hd

/-! ## Executable reading (`#guard`, not a proof): the reference passes the run each mutant fails -/

/-- The values the snapshots `s .. s + n - 1` of `tr` emit (2-bit). -/
def emittedOf (tr : List SvState) (s n : Nat) : List (BitVec 2) :=
  ((obsList 2 tr s n).filter (·.1)).map (·.2)

#guard emittedOf (trAt refD (zeros refD) ((rowsTxn 2#2 3#2).map ent)) 1 9 == Sorter.sortAsc [2#2, 3#2]
#guard emittedOf (trAt refD (zeros refD) ((rowsTxn 3#2 2#2).map ent)) 1 9 == Sorter.sortAsc [3#2, 2#2]
#guard emittedOf (trAt m020D (zeros m020D) ((rowsTxn 2#2 3#2).map ent)) 1 9 == [2#2, 2#2]
#guard emittedOf (trAt m075D (zeros m075D) ((rowsTxn 2#2 3#2).map ent)) 1 9 == []
#guard (trAt refD (onesAt refD ["tok"]) (((true, false, false, 0#2) :: List.replicate 3 (idle 2)).map ent))[1]?.map
  (bitOf · "out_valid") == some false

#print axioms m005_refuted
#print axioms m038_refuted
#print axioms m020_refuted
#print axioms m026_refuted
#print axioms m040_refuted
#print axioms m061_refuted
#print axioms m075_refuted
#print axioms m093_refuted
#print axioms m099_refuted
#print axioms m141_refuted
#print axioms m178_refuted
#print axioms m180_refuted

end SvGolf.Tasks.Sorter.Mutants
