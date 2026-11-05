import CounterInst
import LeanModels.Sv.SeqProfile

/-!
# The counter through the generic clock step (PLAN4 Gate 1, step 5) — *provisional over `run2`*

The counter loaded from `cnt.sv` (`cntSv.sem N`, equal to `cntD N` at every `N ≥ 1` by P's
`cnt_sem_eq`, the per-design agreement: Gate 1's declared fallback for 2c) goes through the generic
FF-only clock step:

1. `cntD_profile`: the counter is in the decidable FF-only profile, at symbolic `N` (`rfl`).
2. `cnt_sem_clockStep`: one cycle of the LOADED design is the clock step (`cycleStep2_profile`):
   inputs applied, the process's updates computed on that state, committed once.
3. `cnt_clockStep`: evaluated, the clock step is the counter's next state (`cntNext`): the
   per-design equations. Together they re-derive `cnt_cycle`'s closed form for `cntSv.sem N`
   without a hand proof of the cycle (`cnt_sem_cycle`).

Not in any lake library; compiled in a scratch copy with `CounterInst`'s imports.
-/

namespace SvGolf.Seq.Counter

open LeanModels.Sv

theorem cntD_profile (N : Nat) : (cntD N).ffOnlyProfileB = true := by
  first
  | rfl
  | simp [Design2.ffOnlyProfileB, Design2.ffDisjB, cntD, Stmt2.nbaOnly, Stmt2.optNbaOnly,
      Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Lhs2.window?, Design2.declWidth, Design2.inputNames,
      Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins, Process2.procWins]

/-- The counter's update on a state of its shape, by its enable and reset. -/
theorem cnt_upd (N F : Nat) (hF : 12 ≤ F) (c r e q : LVec) :
    runEdgeProcess2 F (S c r e q) [] ((cntD N).processes[0]'(by simp [cntD])) =
      .ok (S c r e q,
        if r.condTrue then [("q", 0, (LVec.replicate N .l0).resizeU q.width)]
        else if e.condTrue then [("q", 0, (q.add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU q.width)]
        else []) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 12 := ⟨F - 12, by omega⟩
  by_cases hr : r.condTrue = true
  · simp [cntD, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, S, SvState.lookup, hr]
  · by_cases he : e.condTrue = true
    · simp [cntD, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, S, SvState.lookup,
        hr, he, evalBinOp]
    · simp [cntD, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, S, SvState.lookup,
        hr, he]

/-- **The loaded counter's cycle is the generic clock step**, at every `N ≥ 1`. -/
theorem cnt_sem_clockStep (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (inputs : SvState)
    (c r e q : LVec) (k F : Nat) (hF : 12 ≤ F) :
    cycleStep2 (cntSv.sem N) σ F inputs (S c r e q) k =
      .ok (clockStep (cntD N) F (applyInputs2 (cntD N) inputs (S c r e q)) (cntD N).edgeIndices,
        k + 3) := by
  rw [cnt_sem_eq N hN]
  refine cycleStep2_profile (cntD_profile N) σ inputs _ k (fun i p hp => ?_) ?_ (by omega)
  · have hi : i = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hp).1
      simp [cntD] at this; omega
    subst hi
    obtain rfl : p = (cntD N).processes[0]'(by simp [cntD]) := by
      rw [Array.getElem?_eq_getElem (by simp [cntD])] at hp; exact (Option.some.inj hp).symm
    rw [apply_cnt]
    exact ⟨_, cnt_upd N F hF _ _ _ _⟩
  · rw [apply_cnt]; simp [S]

/-- **The clock step evaluated**: the counter's next state. -/
theorem cnt_clockStep (N F : Nat) (hF : 12 ≤ F) (c r e q : LVec) :
    clockStep (cntD N) F (S c r e q) (cntD N).edgeIndices = S c r e (cntNext N r e q) := by
  have he : (cntD N).edgeIndices = [0] := cntD_edgeIndices N
  have hu : (cntD N).ffUpd F (S c r e q) 0 =
      if r.condTrue then [("q", 0, (LVec.replicate N .l0).resizeU q.width)]
      else if e.condTrue then [("q", 0, (q.add ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU q.width)]
      else [] := by
    simp only [Design2.ffUpd, Array.getElem?_eq_getElem (show 0 < (cntD N).processes.size by simp [cntD]),
      cnt_upd N F hF]
  simp only [clockStep, he, List.flatMap_cons, List.flatMap_nil, List.append_nil, hu]
  by_cases hr : r.condTrue = true
  · simp [hr, cntNext, commitNba2, S, SvState.lookup, SvState.set]
  · by_cases he' : e.condTrue = true
    · simp [hr, he', cntNext, commitNba2, S, SvState.lookup, SvState.set]
    · simp [hr, he', cntNext, commitNba2]

/-- **`cnt_cycle`'s closed form for the loaded counter**, through the generic theorem. -/
theorem cnt_sem_cycle (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (inputs : SvState)
    (c r e q : LVec) (k F : Nat) (hF : 12 ≤ F) :
    cycleStep2 (cntSv.sem N) σ F inputs (S c r e q) k =
      .ok (S (appIn inputs "clk" c) (appIn inputs "rst" r) (appIn inputs "en" e)
        (cntNext N (appIn inputs "rst" r) (appIn inputs "en" e) q), k + 3) := by
  rw [cnt_sem_clockStep N hN σ inputs c r e q k F hF, apply_cnt, cnt_clockStep N F hF]

#print axioms cntD_profile
#print axioms cnt_sem_clockStep
#print axioms cnt_clockStep
#print axioms cnt_sem_cycle

end SvGolf.Seq.Counter
