import tests.matmul.negative.Refute

/-!
# Task `matmul`: kernel refutations of generated mutants of the reference (untrusted, kernel-checked; 2026-11-08)

Nothing here is part of the trusted base. `tests/mutate.py` generates the mutants of
`tasks/matmul/reference/matmul_g1.sv` from Slang's syntax tree, and `tests/matmul/mutants/classify.py` (the engine
`tests/txsweep.py`) sorts them: killed by the task's checks, proved equivalent to the reference, proved correct
(not equivalent: another latency, or `done` before the first start, which the statement allowed until 2026-11-09),
or a survivor (`tests/matmul/mutants/MANIFEST.json`; its verdicts predate 2026-11-09). This file refutes a SAMPLE of
the killed ones by the statement itself, for EVERY latency function, each by ONE run that the kernel evaluates
(`Refute.lean`: `hold_refuted`, the snapshot at `done` does not hold `A·B`; `never_refuted`, the run comes to rest
without `done`), at `(N, W, AccW) = (2, 2, 4)`, from a named power-up state, with `A = [[-1, 1], [-2, 1]]`,
`B = [[1, -1], [-2, 1]]` held from a start at entry 1. Each theorem is stated for every design family whose instance
at `(2, 2, 4)` is the hand-built twin.

Since 2026-11-09 the statement asks `done` = 0 from the release up to the first start (`TxTask.Guar`), so the
manifest's CORRECT-SMALL mutants that raise `done` before any start are wrong; four of them are refuted here by
`early_refuted` (`Refute.lean`: a run with no start whose snapshot after the release shows `done` = 1). m025, m027,
m031 and m033 write the same reset values as m026 and m032 with other literals (`'1`, `~('1 >> 1)`).

Each mutant's source is in `tests/matmul/mutants/<id>.sv` (the generator's output under a three-line header); its
twin `<id>D` is the reference's twin `refD 4` (`Refute.lean`) with the one mutated node changed (in all four
accumulator processes, for an edit in the generate body), checked equal to the loaded instance (`#guard reprStr …`).

| mutant | operator | edit (matmul_g1.sv) | clause | refutation |
|---|---|---|---|---|
| m055 | DEL | `a_sh <= A` at the start deleted | `done` at snapshot 3 with `C = 0` | `m055_refuted` |
| m074 | SOR | `a_sh >> W` becomes `a_sh << W` | `done` at 3 with the wrong `C` | `m074_refuted` |
| m089 | NEG | `if (k == N - 1)` becomes `if (!(k == N - 1))` | `done` at 2, after one step | `m089_refuted` |
| m091 | ROR | `k == N - 1` becomes `k != N - 1` | `done` at 2, after one step | `m091_refuted` |
| m113 | DEL | the clear `C[…] <= '0` at the start deleted | from the power-up `C` all ones, `C` is off at `done` | `m113_refuted` |
| m120 | CRP | the clear writes `'1` | `C` starts at -1 | `m120_refuted` |
| m127 | DEL | the accumulation `C[…] <= C[…] + …` deleted | `done` at 3 with `C = 0` | `m127_refuted` |
| m134 | AOR | `C + a*b` becomes `C - a*b` | `done` at 3 with `-A·B` | `m134_refuted` |
| m047 | DEL | `busy <= 1'b1` at the start deleted | at rest without `done`, for ever | `m047_refuted` |
| m105 | DEL | `done <= 1'b1` at the last step deleted | at rest without `done`, for ever | `m105_refuted` |
| m019 | NEG | `if (rst)` becomes `if (!(rst))` | every entry with `rst` = 0 resets: never `done` | `m019_refuted` |
| m032 | RST | the reset writes `done <= 1'b1` | `done` = 1 at snapshot 1, no start | `m032_refuted` |
| m029 | DEL | the reset's `done <= 1'b0` deleted | from the power-up with `done` = 1: `done` = 1 at snapshot 1, no start | `m029_refuted` |
| m026 | RST | the reset writes `busy <= 1'b1` | a phantom transaction: `done` = 1 at snapshot 2, no start | `m026_refuted` |
| m023 | DEL | the reset's `busy <= 1'b0` deleted | from the power-up with `busy` = 1: `done` = 1 at snapshot 2, no start | `m023_refuted` |

The first eleven are rejected by check.py's stages that need no proof, at `postsynth` (the manifest records the
point). The last four were CORRECT-SMALL under the statement before 2026-11-09, which asked only that `done` be
known before the first start.
-/

namespace SvGolf.Tasks.Matmul.Mutants

open LeanModels.Sv SvGolf SvGolf.Tasks.Matmul.Refute
open SvGolf.Tasks.Sorter.Refute (trAt zeros onesAt powerUp_zeros powerUp_onesAt bitOf)

/-- The accumulator processes with the clear `clr i j` and the update `upd i j`. -/
def macWith (clr upd : Nat → Nat → Stmt2) (i j : Nat) : Process2 := macP (clr i j) (upd i j)
def clr0 (i j : Nat) : Stmt2 := cW 4 i j (.lit (LVec.ofNat 4 0))
def updAdd (i j : Nat) : Stmt2 := cW 4 i j (macE .add 4 i j)

/-! ## The twins (one node each) -/

def m055D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS (startW stBusy stDone stK nop stB) stepS) (macRef 4)
def m074D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS startS
  (stepW stepK (asg "a_sh" (.binary (.shl false) (.ident "a_sh") (l32 2))) stepB stepCond finS)) (macRef 4)
def m089D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS startS
  (stepW stepK stepA stepB (.unary .lnot stepCond) finS)) (macRef 4)
def m091D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS startS
  (stepW stepK stepA stepB (.binary .ne (.ident "k") (.binary .sub (l32 2) (l32 1))) finS)) (macRef 4)
def m113D : Design2 := mWith 4 ctrlRef (macWith (fun _ _ => nop) updAdd)
def m120D : Design2 := mWith 4 ctrlRef (macWith (fun i j => cW 4 i j (.lit (LVec.ofNat 4 15))) updAdd)
def m127D : Design2 := mWith 4 ctrlRef (macWith clr0 fun _ _ => nop)
def m134D : Design2 := mWith 4 ctrlRef (macWith clr0 fun i j => cW 4 i j (macE .sub 4 i j))
def m047D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS (startW nop stDone stK stA stB) stepS) (macRef 4)
def m105D : Design2 := mWith 4 (ctrlP (.ident "rst") rstS startS
  (stepW stepK stepA stepB stepCond (.block #[asg "busy" (l1 0), nop]))) (macRef 4)
def m019D : Design2 := mWith 4 (ctrlP (.unary .lnot (.ident "rst")) rstS startS stepS) (macRef 4)
def m032D : Design2 :=
  mWith 4 (ctrlP (.ident "rst") (.block #[asg "busy" (l1 0), asg "done" (l1 1), asg "k" (l32 0)]) startS stepS) (macRef 4)
def m029D : Design2 :=
  mWith 4 (ctrlP (.ident "rst") (.block #[asg "busy" (l1 0), nop, asg "k" (l32 0)]) startS stepS) (macRef 4)
def m026D : Design2 :=
  mWith 4 (ctrlP (.ident "rst") (.block #[asg "busy" (l1 1), asg "done" (l1 0), asg "k" (l32 0)]) startS stepS) (macRef 4)
def m023D : Design2 :=
  mWith 4 (ctrlP (.ident "rst") (.block #[nop, asg "done" (l1 0), asg "k" (l32 0)]) startS stepS) (macRef 4)

load_sv m055L from "tests/matmul/mutants/m055.sv"
load_sv m074L from "tests/matmul/mutants/m074.sv"
load_sv m089L from "tests/matmul/mutants/m089.sv"
load_sv m091L from "tests/matmul/mutants/m091.sv"
load_sv m113L from "tests/matmul/mutants/m113.sv"
load_sv m120L from "tests/matmul/mutants/m120.sv"
load_sv m127L from "tests/matmul/mutants/m127.sv"
load_sv m134L from "tests/matmul/mutants/m134.sv"
load_sv m047L from "tests/matmul/mutants/m047.sv"
load_sv m105L from "tests/matmul/mutants/m105.sv"
load_sv m019L from "tests/matmul/mutants/m019.sv"
load_sv m032L from "tests/matmul/mutants/m032.sv"
load_sv m029L from "tests/matmul/mutants/m029.sv"
load_sv m026L from "tests/matmul/mutants/m026.sv"
load_sv m023L from "tests/matmul/mutants/m023.sv"

-- the hand-built twins are the loaded designs at the refutations' point
#guard reprStr (m055L.sem 2 2 4) == reprStr m055D
#guard reprStr (m074L.sem 2 2 4) == reprStr m074D
#guard reprStr (m089L.sem 2 2 4) == reprStr m089D
#guard reprStr (m091L.sem 2 2 4) == reprStr m091D
#guard reprStr (m113L.sem 2 2 4) == reprStr m113D
#guard reprStr (m120L.sem 2 2 4) == reprStr m120D
#guard reprStr (m127L.sem 2 2 4) == reprStr m127D
#guard reprStr (m134L.sem 2 2 4) == reprStr m134D
#guard reprStr (m047L.sem 2 2 4) == reprStr m047D
#guard reprStr (m105L.sem 2 2 4) == reprStr m105D
#guard reprStr (m019L.sem 2 2 4) == reprStr m019D
#guard reprStr (m032L.sem 2 2 4) == reprStr m032D
#guard reprStr (m029L.sem 2 2 4) == reprStr m029D
#guard reprStr (m026L.sem 2 2 4) == reprStr m026D
#guard reprStr (m023L.sem 2 2 4) == reprStr m023D

/-! ## The refutations, for every latency function -/

theorem m055_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m055D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

theorem m074_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m074D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

theorem m089_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m089D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 2) (c := 2)
    (by decide +kernel)) sem lat hd

theorem m091_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m091D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 2) (c := 2)
    (by decide +kernel)) sem lat hd

/-- **m113 is rejected** from the power-up with `C` all ones (no clear at the start: the products are added to it;
the reset does not touch `C`). -/
theorem m113_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m113D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_onesAt _ ["C"]) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3)
    (c := 3) (by decide +kernel)) sem lat hd

theorem m120_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m120D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

theorem m127_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m127D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

theorem m134_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m134D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (hold_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6) (c' := 3) (c := 3)
    (by decide +kernel)) sem lat hd

/-- **m047 is rejected**: never busy, so `done` never rises; the run is at rest from the start on. -/
theorem m047_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m047D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (never_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6)
    (by decide +kernel)) sem lat hd

/-- **m105 is rejected**: the last step clears `busy` but never sets `done`; then the run is at rest. -/
theorem m105_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m105D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (never_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6)
    (by decide +kernel)) sem lat hd

/-- **m019 is rejected**: every entry with `rst` = 0 takes the reset branch, so `done` never rises. -/
theorem m019_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m019D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (never_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (s := 1) (n := 6)
    (by decide +kernel)) sem lat hd

/-! ## `done` before the first start (decided 2026-11-09), for every latency function -/

/-- **m032 is rejected**: the reset sets `done`, so the snapshot after the release shows `done` = 1 before any start
(the review's counter-design of 2026-11-08, generated). -/
theorem m032_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m032D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (early_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (n := 3) (c := 1)
    (by decide +kernel)) sem lat hd

/-- **m029 is rejected** from the power-up with `done` = 1: the reset no longer clears it. -/
theorem m029_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m029D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (early_refuted_of_check (powerUp_onesAt _ ["done"]) (a := matA) (b := matB) (n := 3) (c := 1)
    (by decide +kernel)) sem lat hd

/-- **m026 is rejected**: the reset sets `busy`, so after the release the design counts `N` steps of a transaction
nobody started and shows `done` = 1 at snapshot 2. -/
theorem m026_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m026D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (early_refuted_of_check (powerUp_zeros _) (a := matA) (b := matB) (n := 4) (c := 2)
    (by decide +kernel)) sem lat hd

/-- **m023 is rejected** from the power-up with `busy` = 1: the reset no longer clears it (as m026 from there). -/
theorem m023_refuted (sem : Nat → Nat → Nat → Design2) (lat : Nat → Nat → Nat → Nat) (hd : sem 2 2 4 = m023D) :
    ¬ Statement sem lat :=
  refuted_of aw4 (early_refuted_of_check (powerUp_onesAt _ ["busy"]) (a := matA) (b := matB) (n := 4) (c := 2)
    (by decide +kernel)) sem lat hd

-- the reference passes the same runs: `done` = 0 at every snapshot of a run with no start (from both power-ups)
#guard ((List.range 4).map fun c => (trAt (refD 4) (zeros (refD 4)) ((txnRows matA matB 0 4).map ment))[c]?.map
  (bitOf · "done")) == [some false, some false, some false, some false]
#guard ((List.range 4).map fun c => (trAt (refD 4) (onesAt (refD 4) ["done", "busy"])
  ((txnRows matA matB 0 4).map ment))[c]?.map (bitOf · "done")) == [some false, some false, some false, some false]

#print axioms m055_refuted
#print axioms m074_refuted
#print axioms m089_refuted
#print axioms m091_refuted
#print axioms m113_refuted
#print axioms m120_refuted
#print axioms m127_refuted
#print axioms m134_refuted
#print axioms m047_refuted
#print axioms m105_refuted
#print axioms m019_refuted
#print axioms m032_refuted
#print axioms m029_refuted
#print axioms m026_refuted
#print axioms m023_refuted

end SvGolf.Tasks.Matmul.Mutants
