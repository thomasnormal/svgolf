import SvGolf.LoadSv
import SvGolf.Cycle

/-!
# `sv_mirror` and `sv_cycle` (`SvGolf.Cycle`): the designs they cover, and the shapes they refuse

* `shift0.sv`: a shift register of `N` stages of `W` bits (one `always_ff` for stage 0, a generate loop of
  `N` stages, one for the output). The generated opening block is checked end to end: the mirror, the
  agreement, the profile, the clock step at symbolic `N` and `W`, power-up and the initial state; then a
  fact about the generated next state, proved from it as a player would.
* `oddshapes.sv`: shapes covered exactly that a careless generator could get wrong: non-zero reset values, a
  signed register read through a signed comparison (`scmpVal`), a register no process writes, a generate loop
  whose bound `N - 1` is zero at `N = 1`.
* `clash.sv`: generate blocks labelled like the commands' own names (`procs`; `p0Q`, the updates of process 0):
  the generated names step aside.
* `square.sv`: a window beyond `sv_disch` (nonlinear in the genvar): refused with the condition printed; a
  `sorry` window tactic is refused too, a real one is accepted.
* `comb_ff.sv`, `assign.sv`: one comb process (an `always_comb`, a continuous assignment) beside a register:
  the comb settle and the cycle generated end to end.
* `lpcmp.sv`: a localparam chosen by a comparison of the parameters: refused with the comparison printed, and
  generated under each case hypothesis.
* Refusals, each naming the construct: two comb processes (`comb2.sv`), a comb process inside a generate loop
  (`combgen.sv`), a generate loop that does not start at 0 (`shift.sv`), a blocking assignment in an
  `always_ff` (`blocking.sv`), an asynchronous reset (`areset.sv`), a plain `always @(posedge clk)`
  (`plain.sv`), a nonblocking write to a dynamic index (`dynidx.sv`), a loop bound that can be negative under
  the hypotheses, parameters given out of order, a hypothesis or a disjointness term containing `sorry`, an
  ill-typed disjointness term, a prefix already in use, `sv_cycle` before `sv_mirror`. (A generate `if`, two
  clocks and a process writing an input are refused too, by name, but the pinned loader refuses the small
  designs written for them first, at load time; an x literal is refused earlier still, by the source gate.)
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

/-- error: sv_mirror: `SvGolf.Tests.Cycle.sh.env` already exists (an earlier `sv_mirror sh` or a declaration of
yours): choose another name than `sh` -/
#guard_msgs (whitespace := lax) in
sv_mirror sh := shiftD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- error: sv_mirror: the binder `W` is in the position of the design's parameter `N`: give the parameters in the
design's order, (N W : Nat) -/
#guard_msgs (whitespace := lax) in
sv_mirror shw := shiftD (W N : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- error: sv_mirror: the hypothesis `h` contains `sorry` -/
#guard_msgs in
sv_mirror shs := shiftD (N W : Nat) (h : (sorry : Prop))

/-! ## 2. Shapes covered exactly -/

load_sv oddD from "tests/cycle/designs/oddshapes.sv" (top := "oddshapes")

/-- error: sv_mirror: refused: the bound of generate loop `g_s` is not proved to be the `Nat` `N - 1` under the
hypotheses (a bound such as `N - 1` needs a hypothesis that keeps it non-negative, e.g. `1 ≤ N`) -/
#guard_msgs (whitespace := lax) in
sv_mirror od0 := oddD (N W : Nat) (hW : 1 ≤ W)

sv_mirror od := oddD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- The family is empty at `N = 1` (its bound `N - 1` is zero there). -/
example (W : Nat) : od.procs 1 W = [od.p0 1 W, od.p1 1 W] := by simp [od.procs]

/-- `acc` and `q` (process 0), the low window of `s` (process 1), window `k + 1` of `s` (stage `k`). -/
theorem od_disj (N W : Nat) : (od.procs N W).Pairwise ProcDisj := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) (pairwise_map_range fun k k' h _ => ?_))
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact ProcDisj.of_nameLists (ns := ["acc", "q"]) (ms := ["s"])
        (by simp [od.p0, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins])
        (by simp [od.p1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]) (by decide)
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
      exact ProcDisj.of_nameLists (ns := ["acc", "q"]) (ms := ["s"])
        (by simp [od.p0, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins])
        (by simp [od.g_s, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins]) (by decide)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hp
    have : W ≤ (k + 1) * W := Nat.le_mul_of_pos_left W (by omega)
    exact ProcDisj.of_all (by simp [od.p1, od.g_s, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps] <;> omega)
  · have := Nat.mul_le_mul_right W (show k + 1 + 1 ≤ k' + 1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact ProcDisj.of_all (by simp [od.g_s, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps] <;> omega)

/-- error: Unknown identifier `od_disj_typo` -/
#guard_msgs in
sv_cycle od using od_disj_typo N W

/-- error: sv_cycle: the disjointness term contains `sorry` (a lemma of yours may be unfinished while you work;
the command's argument may not) -/
#guard_msgs (whitespace := lax) in
sv_cycle od using sorry

sv_cycle od using od_disj N W

/-- The reset values, as written (`5` at `acc`'s width, a fill of ones at `q`'s). -/
theorem od_reset (N W : Nat) (clk d q acc s idle : LVec) :
    od.p0Q N W clk (knownBit true) d q acc s idle =
      [("acc", 0, (LVec.ofInt W 5).resizeU acc.width), ("q", 0, (LVec.ofBitVec (BitVec.allOnes W)).resizeU q.width)] := by
  simp [od.p0Q]

/-- The signed comparison, as the semantics evaluates it (`scmpVal`, any values, `x` included). -/
theorem od_run (N W : Nat) (clk d q acc s idle : LVec) :
    od.p0Q N W clk (knownBit false) d q acc s idle =
      [("acc", 0, ((scmpVal .lt d acc).ternary (acc.sub d) d).resizeU acc.width), ("q", 0, acc.resizeU q.width)] := by
  simp [od.p0Q]

/-- No process writes `idle`: the next state keeps it. -/
theorem od_idle (N W : Nat) (clk rst d q acc s idle : LVec) :
    ∀ u ∈ od.p0Q N W clk rst d q acc s idle ++ (od.p1Q N W clk rst d q acc s idle ++
      (List.range (N - 1)).flatMap fun k => od.g_sQ N W k clk rst d q acc s idle), u.1 ≠ "idle" := by
  rintro ⟨n, lo, v⟩ hu rfl
  simp only [od.p0Q, od.p1Q, od.g_sQ] at hu
  split at hu <;> simp at hu

/-- info: 'SvGolf.Tests.Cycle.od.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms od.cycle

/-! ## 3. Labels that would clash with the generated names -/

load_sv clashD from "tests/cycle/designs/clash.sv" (top := "clash")

sv_mirror cl := clashD (N : Nat) (hN : 1 ≤ N)

/-- The two blocks are `cl.procs_1` and `cl.p0Q_1`. -/
example (N : Nat) : cl.procs N = cl.p0 N :: (List.map (cl.procs_1 N) (List.range N) ++
    List.map (cl.p0Q_1 N) (List.range N)) := rfl

theorem cl_disj (N : Nat) : (cl.procs N).Pairwise ProcDisj := by
  refine .cons (fun p hp => ?_) (List.pairwise_append.mpr ⟨pairwise_map_range fun k k' h _ => ?_,
    pairwise_map_range fun k k' h _ => ?_, fun p hp q hq => ?_⟩)
  · simp only [List.mem_append, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;>
      exact ProcDisj.of_all (by simp [cl.p0, cl.procs_1, cl.p0Q_1, Process2.procWins, Stmt2.drvWins,
        Lhs2.drvWins, DrvWin.overlaps])
  · exact ProcDisj.of_all (by simp [cl.procs_1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps] <;> omega)
  · exact ProcDisj.of_all (by simp [cl.p0Q_1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps] <;> omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨k', -, rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_range] at hk
    exact ProcDisj.of_all (by simp [cl.procs_1, cl.p0Q_1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps] <;> omega)

sv_cycle cl using cl_disj N

/-- The updates of process 0 (`cl.p0Q`) and of the block labelled `p0Q` (`cl.p0Q_1Q`) are different
definitions. -/
example (N k : Nat) (clk d q s : LVec) :
    cl.p0Q N clk d q s = [("q", 0, d.resizeU q.width)] ∧
      cl.p0Q_1Q N k clk d q s = [("s", N + k, (d.extract k 1).resizeU 1)] := by
  simp [cl.p0Q, cl.p0Q_1Q]

/-! ## 4. A window beyond `sv_disch`: the player's tactic, never a `sorry` -/

load_sv squareD from "tests/cycle/designs/square.sv" (top := "square")

/-- error: sv_mirror: cannot instantiate the process of generate block `g_sq`: the condition
  ↑k * ↑k * ↑W + ↑W - 1 < ↑(↑N * ↑N * ↑W - 1).natAbs + 1
is neither proved nor refuted by `sv_disch`. If it is a window of a register family inside its vector, give a
tactic that proves it with `sv_mirror X (window := by …) := …` (it runs on the condition, with the genvars and
their bounds in scope). -/
#guard_msgs (whitespace := lax) in
sv_mirror sq0 := squareD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- error: sv_mirror: cannot instantiate the process of generate block `g_sq`: the condition
  ↑k * ↑k * ↑W + ↑W - 1 < ↑(↑N * ↑N * ↑W - 1).natAbs + 1
is neither proved nor refuted by `sv_disch`. If it is a window of a register family inside its vector, give a
tactic that proves it with `sv_mirror X (window := by …) := …` (it runs on the condition, with the genvars and
their bounds in scope). -/
#guard_msgs (whitespace := lax) in
sv_mirror sq1 (window := by sorry) := squareD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

-- The window `k*k*W + W ≤ N*N*W`, from `k*k < N*N` (the condition is stated over `Int`: the casts are pulled
-- out first).
sv_mirror sq (window := by
    have := Nat.mul_le_mul_right W (Nat.mul_lt_mul'' ‹_ < N› ‹_ < N›)
    rw [Nat.succ_mul] at this
    simp only [← Int.natCast_mul, ← Int.natCast_one, ← Int.natCast_add, Int.ofNat_le, Int.ofNat_lt]
    omega) := squareD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

/-- info: 'SvGolf.Tests.Cycle.sq.instantiate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sq.instantiate

/-! ## 5. One comb process beside the registers -/

load_sv combD from "tests/cycle/designs/comb_ff.sv" (top := "comb_ff")

sv_mirror cf := combD (N : Nat) (hN : 1 ≤ N)

/-- The comb block writes `t`, the register `q`. -/
theorem cf_disj (N : Nat) : (cf.procs N).Pairwise ProcDisj := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) .nil) <;> simp at hp <;> subst hp <;>
    exact ProcDisj.of_all (by simp [cf.p0, cf.p1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps])

sv_cycle cf using cf_disj N

/-- The comb block's value (`t = a & b` at `t`'s width) and the generated cycle, as a player uses them: from
any state, `q` takes the settled `t` of the applied inputs, `t` is settled again. -/
example (N : Nat) (clk a b q t : LVec) : cf.comb_t N clk a b q t = (a.and b).resizeU t.width := rfl

example (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (e : SvState) (clk a b q t : LVec) :
    ∃ k', cycleStep2 (combD.sem N) σ 32 e (cf.St clk a b q t) 0 =
      .ok (cf.next N (appIn e "clk" clk) (appIn e "a" a) (appIn e "b" b) q t, k') :=
  cf.cycle N hN σ e clk a b q t 0 32 (Nat.le_refl _)

/-- info: 'SvGolf.Tests.Cycle.cf.cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms cf.cycle

load_sv assignD from "tests/cycle/designs/assign.sv" (top := "assign_ff")

sv_mirror af := assignD (N : Nat) (hN : 1 ≤ N)

theorem af_disj (N : Nat) : (af.procs N).Pairwise ProcDisj := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) .nil) <;> simp at hp <;> subst hp <;>
    exact ProcDisj.of_all (by simp [af.p0, af.p1, Process2.procWins, Stmt2.drvWins, Lhs2.drvWins,
      DrvWin.overlaps])

sv_cycle af using af_disj N

example (N : Nat) (clk a b q t : LVec) : af.comb_t N clk a b q t = (a.or b).resizeU t.width := rfl

/-- info: 'SvGolf.Tests.Cycle.af.settle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms af.settle

/-! ## 6. A localparam chosen by a comparison of the parameters: one mirror per case -/

load_sv lpD from "tests/cycle/designs/lpcmp.sv" (top := "lpcmp")

/-- error: sv_mirror: refused: the parameter environment depends on the comparison
  W < N
of the parameters (a localparam chosen by it): give the case as a hypothesis, `(h : <the comparison>)`, and a
second `sv_mirror` under `(h : ¬ <the comparison>)` for the other case -/
#guard_msgs (whitespace := lax) in
sv_mirror lp0 := lpD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

sv_mirror lpA := lpD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (h : W < N)

sv_mirror lpB := lpD (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (h : ¬ W < N)

/-- Under each case `r` is declared at its own width: `N - W` bits, or one. -/
example (N W : Nat) : lpA.decls N W = [{ name := "clk", width := 1, isInput := true },
      { name := "d", width := W, isInput := true }, { name := "q", width := W, isOutput := true },
      { name := "r", width := N - W }] ∧
    lpB.decls N W = [{ name := "clk", width := 1, isInput := true },
      { name := "d", width := W, isInput := true }, { name := "q", width := W, isOutput := true },
      { name := "r", width := 1 }] := ⟨rfl, rfl⟩

/-- `sv_window` with a genvar bounded by `N - 1` (bumped by 2, the bump spelled out for `omega`): the window of
row `k + 1` of a row-major family, the shape of matmul record 4a4d9cd6's array rows. -/
example (N AccW k j : Nat) (hN : 1 ≤ N) (hk : k < N - 1) (hj : j < N) :
    ((k + 1) * N + j) * AccW + AccW ≤ N * N * AccW := by
  sv_window

/-! ## 7. Refusals: a shape the generator does not cover is an error that names it -/

load_sv comb2D from "tests/cycle/designs/comb2.sv" (top := "comb2")

/-- error: sv_mirror: refused: a second comb process (a continuous assignment (`assign`)): one `always_comb` or
`assign` beside the `always_ff` processes is covered; several need the settle in every schedule order of runs
that read each other's outputs (a lemma that every order of `combPass2` reaches the same fixpoint, from an
acyclic order of the comb processes), which is not proved yet -/
#guard_msgs (whitespace := lax) in
sv_mirror c2 := comb2D (N : Nat) (hN : 1 ≤ N)

load_sv combgenD from "tests/cycle/designs/combgen.sv" (top := "combgen")

/-- error: sv_mirror: refused: an `always_comb` process inside generate block `g_and`: a family of comb processes
is not covered (their settle in every schedule order needs the commutation of their runs over a permutation,
`combPass2` of a family, which is not proved yet) -/
#guard_msgs (whitespace := lax) in
sv_mirror cg := combgenD (N : Nat) (hN : 1 ≤ N)

load_sv shift1D from "tests/cycle/designs/shift.sv" (top := "shift")

/--
error: sv_mirror: refused: generate loop `g_stage` does not start at 0 (only `for (g = 0; g < e; g++)` is covered)
-/
#guard_msgs in
sv_mirror s1 := shift1D (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)

load_sv blockingD from "tests/cycle/designs/blocking.sv" (top := "blocking")

/-- error: sv_mirror: refused: a blocking assignment (`=`) to `t` in the module's process 0 (in source order):
the FF-only clock step takes nonblocking assignments (`<=`) only (`Stmt2.nbaOnly`) -/
#guard_msgs (whitespace := lax) in
sv_mirror bl := blockingD (N : Nat) (hN : 1 ≤ N)

load_sv aresetD from "tests/cycle/designs/areset.sv" (top := "areset")

/-- error: sv_mirror: refused: an asynchronous reset (`always_ff @(posedge clk or negedge rst_n)`): the clock
step's reset-event phase is not covered; only `always_ff @(posedge clk)` with a synchronous reset (an `if` in the
body) is -/
#guard_msgs (whitespace := lax) in
sv_mirror ar := aresetD (N : Nat) (hN : 1 ≤ N)

load_sv plainD from "tests/cycle/designs/plain.sv" (top := "plain")

/-- error: sv_mirror: refused: a plain `always @(posedge clk)` process: only `always_ff` processes are covered -/
#guard_msgs in
sv_mirror pl := plainD (N : Nat) (hN : 1 ≤ N)

load_sv dynidxD from "tests/cycle/designs/dynidx.sv" (top := "dynidx")

/-- error: sv_mirror: refused: a nonblocking assignment to a dynamic index `q[…]` in the module's process 0 (in
source order): the target is not a static window (`Stmt2.nbaStaticB`) -/
#guard_msgs (whitespace := lax) in
sv_mirror dy := dynidxD (N : Nat) (hN : 1 ≤ N)

/--
error: sv_cycle: `SvGolf.Tests.Cycle.nothing.instantiate` does not exist: run `sv_mirror nothing := …` first
-/
#guard_msgs in
sv_cycle nothing using sh_disj

end SvGolf.Tests.Cycle
