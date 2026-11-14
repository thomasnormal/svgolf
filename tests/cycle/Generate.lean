import SvGolf.LoadSv
import SvGolf.Cycle

/-!
# `sv_mirror` and `sv_cycle` (`SvGolf.Cycle`): one design they cover, and the shapes they refuse

* `shift0.sv`: a shift register of `N` stages of `W` bits (one `always_ff` for stage 0, a generate loop of
  `N` stages, one for the output). The generated opening block is checked end to end: the mirror, the
  agreement, the profile, the clock step at symbolic `N` and `W`, power-up and the initial state; then a
  fact about the generated next state, proved from it as a player would.
* Refusals, each naming the construct: an `always_comb` process (`comb_ff.sv`), a continuous assignment
  (`assign.sv`), a generate loop that does not start at 0 (`shift.sv`), `sv_cycle` before `sv_mirror`.
  (A generate `if` is refused too, by name, but the pinned loader refuses the small design written for it
  first, so it has no test here.)
-/

namespace SvGolf.Tests.Cycle

open LeanModels.Sv SvGolf SvGolf.Cycle

/-! ## 1. A shift register, generated end to end -/

load_sv shiftD from "tests/cycle/designs/shift0.sv" (top := "shift0")

sv_mirror sh := shiftD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- Stage `0` writes `s[0 +: W]`, stage `k + 1` writes `s[(k+1)*W +: W]`, the output register `q`. -/
theorem sh_disj (N W : Nat) : (sh.procs N W).Pairwise ProcDisj := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) (pairwise_map_range fun k k' h _ => ?_))
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact ProcDisj.of_all (by simp [sh.p0, sh.p1, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps])
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
      have : W ≤ (k + 1) * W := Nat.le_mul_of_pos_left W (by omega)
      exact ProcDisj.of_all (by simp [sh.p0, sh.g_stage, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
    exact ProcDisj.of_all (by simp [sh.p1, sh.g_stage, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
      Lhs2.drvWins, DrvWin.overlaps])
  · have := Nat.mul_le_mul_right W (show k + 1 + 1 ≤ k' + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact ProcDisj.of_all (by simp [sh.g_stage, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
      Lhs2.drvWins, DrvWin.overlaps] <;> omega)

sv_cycle sh using sh_disj N W

/-- The generated clock step, as the player uses it: any schedule, any stimulus, any fuel from its bound. -/
example (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (σ : ScheduleOracle) (e : SvState) (clk rst d q s : LVec) :
    cycleStep2 (shiftD.sem N W) σ 30 e (sh.St clk rst d q s) 0 =
      .ok (sh.next N W (appIn e "clk" clk) (appIn e "rst" rst) (appIn e "d" d) q s, 3) :=
  sh.cycle N W hN hW σ e clk rst d q s 0 30 (Nat.le_refl _)

/-- A fact about the generated next state, from its definitions alone: with `rst` high every stage's
update is the zero window, whatever the state. -/
theorem sh_reset_stage (N W k : Nat) (clk d q s : LVec) :
    sh.g_stageQ N W k clk (knownBit true) d q s = [("s", (k + 1) * W, (LVec.ofBitVec 0#W).resizeU W)] := by
  simp [sh.g_stageQ]

/-- info: 'SvGolf.Tests.Cycle.sh.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sh.cycle

/-- info: 'SvGolf.Tests.Cycle.sh.powerUp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sh.powerUp

/-! ## 2. Refusals: a shape the generator does not cover is an error that names it -/

load_sv combD from "tests/cycle/designs/comb_ff.sv" (top := "comb_ff")

/--
error: sv_mirror: refused: a `LeanModels.Sv.PProcess.alwaysComb` process (only `always_ff` processes are covered: an `always_comb` or an `assign` has no FF-only clock step)
-/
#guard_msgs in
sv_mirror cf := combD (N : Nat) (hN : 1 ≤ N)

load_sv assignD from "tests/cycle/designs/assign.sv" (top := "assign_ff")

/--
error: sv_mirror: refused: a `LeanModels.Sv.PProcess.assign` process (only `always_ff` processes are covered: an `always_comb` or an `assign` has no FF-only clock step)
-/
#guard_msgs in
sv_mirror af := assignD (N : Nat) (hN : 1 ≤ N)

load_sv shift1D from "tests/cycle/designs/shift.sv" (top := "shift")

/--
error: sv_mirror: refused: generate loop `g_stage` does not start at 0 (only `for (g = 0; g < e; g++)` is covered)
-/
#guard_msgs in
sv_mirror s1 := shift1D (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/--
error: sv_cycle: `SvGolf.Tests.Cycle.nothing.instantiate` does not exist: run `sv_mirror nothing := …` first
-/
#guard_msgs in
sv_cycle nothing using sh_disj

end SvGolf.Tests.Cycle
