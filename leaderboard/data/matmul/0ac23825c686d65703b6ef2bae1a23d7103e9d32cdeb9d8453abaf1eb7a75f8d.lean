import Submission.Design
import SvGolf.Cycle
-- svgolf-latency: 4
namespace Submission
open LeanModels.Sv SvGolf

def c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

def mmDecls (wa wc wb : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "k", width := 32 }, { name := "busy", width := 1 },
   { name := "a_next", width := wa }, { name := "b_next", width := wa },
   { name := "a_bus", width := wb }, { name := "b_bus", width := wb }]

abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.ofBitVec 0#32),
      nb "a_next" (LVec.ofBitVec 0#(N*N*W)), nb "b_next" (LVec.ofBitVec 0#(N*N*W))])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.ofBitVec 0#32),
        .nbaAssign (.ident "a_next") (.binary (.shr false) (.ident "A") (c32 W)),
        .nbaAssign (.ident "b_next") (.binary (.shr false) (.ident "B") (.binary .mul (c32 N) (c32 W)))])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "k") (.binary .add (.ident "k") (.lit (LVec.ofBitVec 1#32))),
          .nbaAssign (.ident "a_next") (.binary (.shr false) (.ident "a_next") (c32 W)),
          .nbaAssign (.ident "b_next") (.binary (.shr false) (.ident "b_next") (.binary .mul (c32 N) (c32 W))),
          .ifStmt (.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none]) none)))))

def mmBusA (N W : Nat) (i : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.slice "a_bus" (i*W) W) (.lit (LVec.ofBitVec 0#W)))
    (some (.ifStmt (.ident "start")
      (.nbaAssign (.slice "a_bus" (i*W) W) (.slice (.ident "A") (i*N*W) W))
      (some (.ifStmt (.ident "busy")
        (.nbaAssign (.slice "a_bus" (i*W) W) (.slice (.ident "a_next") (i*N*W) W)) none)))))

def mmBusB (N W : Nat) (j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.nbaAssign (.slice "b_bus" (j*W) W) (.lit (LVec.ofBitVec 0#W)))
    (some (.ifStmt (.ident "start")
      (.nbaAssign (.slice "b_bus" (j*W) W) (.slice (.ident "B") (j*W) W))
      (some (.ifStmt (.ident "busy")
        (.nbaAssign (.slice "b_bus" (j*W) W) (.slice (.ident "b_next") (j*W) W)) none)))))

def mmCell (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "C" ((i*N+j)*AccW) AccW) (.lit (LVec.ofBitVec 0#AccW)))
    (some (.ifStmt (.ident "busy")
      (.nbaAssign (.slice "C" ((i*N+j)*AccW) AccW)
        (.resize AccW (.binary .add
          (.resize (AccW+W) (.slice (.ident "C") ((i*N+j)*AccW) AccW))
          (.binary .mul (sext "a_bus" AccW (i*W) W) (sext "b_bus" AccW (j*W) W))))) none)))

def mmBusAs (N W : Nat) : List Process2 := (List.range N).map (mmBusA N W)
def mmBusBs (N W : Nat) : List Process2 := (List.range N).map (mmBusB N W)
def mmCells (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => mmCell N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N*N*W) (N*N*AccW) (N*W)).toArray
  processes := (mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW).toArray


abbrev Rng32 (N W AccW : Nat) : Prop :=
  N < 46341 ∧ W < 2147483648 ∧ AccW < 2147483648

theorem rng32_of {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hNW : N * N * W < 2 ^ 31) (hNA : N * N * AccW < 2 ^ 31) : Rng32 N W AccW := by
  have h2 := Nat.le_mul_of_pos_right (N * N) hW
  have h3 := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  have h4 := Nat.le_mul_of_pos_left AccW (Nat.mul_pos hN hN)
  refine ⟨Nat.lt_of_not_le fun h => ?_, by omega, by omega⟩
  have := Nat.mul_le_mul h h
  omega

sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hN46 : N < 46341)

/-- The generated mirror is the hand-written one (the literals of `mmD` are written in the generator's forms). -/
theorem mmG_D (N W AccW : Nat) : mmG.D N W AccW = mmD N W AccW := by
  have ha : mmG.g_a_bus N W AccW = mmBusA N W := by funext i; simp [mmG.g_a_bus, mmBusA]
  have hb : mmG.g_b_bus N W AccW = mmBusB N W := by funext j; simp [mmG.g_b_bus, mmBusB]
  have hc : mmG.g_cell N W AccW = fun i j => mmCell N W AccW i j := by
    funext i j; simp [mmG.g_cell, mmCell, sext]
  simp [mmG.D, mmD, mmG.decls, mmDecls, mmG.procs, mmG.p0, mmCtrl, mmBusAs, mmBusBs, mmCells, c32, nb, ha, hb, hc]

end Submission

namespace Submission
open LeanModels.Sv SvGolf

theorem ctrl_busA (N W AccW i : Nat) : ProcDisj (mmCtrl N W) (mmBusA N W i) := by
  apply ProcDisj.of_nameLists (ns := ["busy", "done", "k", "a_next", "b_next"]) (ms := ["a_bus"])
  · simp [mmCtrl, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmBusA, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp

theorem ctrl_busB (N W AccW j : Nat) : ProcDisj (mmCtrl N W) (mmBusB N W j) := by
  apply ProcDisj.of_nameLists (ns := ["busy", "done", "k", "a_next", "b_next"]) (ms := ["b_bus"])
  · simp [mmCtrl, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmBusB, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp

theorem ctrl_cell (N W AccW i j : Nat) : ProcDisj (mmCtrl N W) (mmCell N W AccW i j) := by
  apply ProcDisj.of_nameLists (ns := ["busy", "done", "k", "a_next", "b_next"]) (ms := ["C"])
  · simp [mmCtrl, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmCell, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, sext]
  · simp

theorem busA_busB (N W AccW i j : Nat) : ProcDisj (mmBusA N W i) (mmBusB N W j) := by
  apply ProcDisj.of_names (n := "a_bus") (n' := "b_bus") (by decide)
  · simp [mmBusA, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmBusB, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]

theorem busA_cell (N W AccW i i' j : Nat) : ProcDisj (mmBusA N W i) (mmCell N W AccW i' j) := by
  apply ProcDisj.of_names (n := "a_bus") (n' := "C") (by decide)
  · simp [mmBusA, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmCell, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, sext]

theorem busB_cell (N W AccW i j j' : Nat) : ProcDisj (mmBusB N W j) (mmCell N W AccW i j') := by
  apply ProcDisj.of_names (n := "b_bus") (n' := "C") (by decide)
  · simp [mmBusB, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]
  · simp [mmCell, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, sext]

theorem cell_proc_wins (N W AccW i j : Nat) : (mmCell N W AccW i j).procWins = [("C", some ((i*N+j)*AccW, AccW)), ("C", some ((i*N+j)*AccW, AccW))] := by
  simp [mmCell, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, sext]

theorem cell_cell (N W AccW i j i' j' : Nat) (h : i*N+j ≠ i'*N+j') : ProcDisj (mmCell N W AccW i j) (mmCell N W AccW i' j') := by
  intro a ha b hb
  rw [cell_proc_wins N W AccW i j] at ha
  rw [cell_proc_wins N W AccW i' j'] at hb
  simp only [List.mem_cons] at ha hb
  all_goals simp_all [DrvWin.overlaps_rowMajor h]


theorem busA_busA (N W AccW i i' : Nat) (h : i < i') : ProcDisj (mmBusA N W i) (mmBusA N W i') := by
  have hw := rowMajor_le (K := W) h
  simp [mmBusA, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
  omega

theorem busB_busB (N W AccW j j' : Nat) (h : j < j') : ProcDisj (mmBusB N W j) (mmBusB N W j') := by
  have hw := rowMajor_le (K := W) h
  simp [mmBusB, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
  omega

theorem mm_pairwise (N W AccW : Nat) : (mmD N W AccW).processes.toList.Pairwise
    (fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false) := by
  simp only [mmD, List.toList_toArray, mmBusAs, mmBusBs, mmCells]
  refine List.Pairwise.cons ?_ ?_
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp; exact ctrl_busA N W AccW i
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp; exact ctrl_busB N W AccW j
    · obtain ⟨i, hi, hq⟩ := List.mem_flatMap.mp hp
      obtain ⟨j, hj, heqj⟩ := List.mem_map.mp hq
      subst p
      exact ctrl_cell N W AccW i j
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
      · exact pairwise_map_range (fun i i' h _ => busA_busA N W AccW i i' h)
      · exact pairwise_map_range (fun j j' h _ => busB_busB N W AccW j j' h)
      · intro p hp q hq
        simp only [List.mem_map, List.mem_range] at hp hq
        obtain ⟨i, -, rfl⟩ := hp; obtain ⟨j, -, rfl⟩ := hq
        exact busA_busB N W AccW i j
    · exact pairwise_rowMajor (fun i j i' j' hi hi' hj hj' h => cell_cell N W AccW i j i' j' (by omega))
    · intro p hp q hq
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
        obtain ⟨i', hi', hq'⟩ := List.mem_flatMap.mp hq
        obtain ⟨j, hj', heqj⟩ := List.mem_map.mp hq'
        subst q
        exact busA_cell N W AccW i i' j
      · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hp
        obtain ⟨i, hi, hq'⟩ := List.mem_flatMap.mp hq
        obtain ⟨j', hj', heqj⟩ := List.mem_map.mp hq'
        subst q
        exact busB_cell N W AccW i j j'

theorem mm_profile (N W AccW : Nat) : (mmD N W AccW).ffOnlyProfileB = true := by
  simp only [Design2.ffOnlyProfileB, Bool.and_eq_true]
  refine ⟨?_, ffDisjB_of_pairwise (by exact mm_pairwise N W AccW)⟩
  simp [mmD, mmCtrl, mmBusAs, mmBusBs, mmCells, mmBusA, mmBusB, mmCell, nb,
    List.all_append, List.all_flatMap, List.all_map, Stmt2.nbaOnly, Stmt2.optNbaOnly,
    Stmt2.listNbaOnly, Stmt2.nbaStaticB, Stmt2.optNbaStaticB, Stmt2.listNbaStaticB,
    Lhs2.window?, Design2.declWidth, Design2.inputNames, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins, mmDecls]

end Submission

namespace Submission
open LeanModels.Sv SvGolf

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames
      (mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW) = true := by
  apply driversOk_of_ff ?_ ?_ (by simpa [mmD, List.append_assoc] using mm_pairwise N W AccW)
  · intro p hp
    simp only [List.mem_cons, List.mem_append, mmBusAs, mmBusBs, mmCells,
      List.mem_map, List.mem_flatMap, List.mem_range] at hp
    rcases hp with ((rfl | ⟨i, hi, heq⟩) | ⟨j, hj, heq⟩) | ⟨i, hi, j, hj, heq⟩
    · exact ⟨_, _, rfl⟩
    · cases heq
      exact ⟨_, _, rfl⟩
    · cases heq
      exact ⟨_, _, rfl⟩
    · cases heq
      exact ⟨_, _, rfl⟩
  · intro n hn
    simp only [List.mem_flatMap] at hn
    rcases hn with ⟨p, hp, hpn⟩
    simp only [List.mem_cons, List.mem_append, mmBusAs, mmBusBs, mmCells,
      List.mem_map, List.mem_flatMap, List.mem_range] at hp
    rcases hp with ((rfl | ⟨i, hi, heq⟩) | ⟨j, hj, heq⟩) | ⟨i, hi, j, hj, heq⟩
    · revert n
      simp [mmCtrl, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign] at *
      decide
    · cases heq
      revert n
      simp [mmBusA, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign] at *
      decide
    · cases heq
      revert n
      simp [mmBusB, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign] at *
      decide
    · cases heq
      revert n
      simp [mmCell, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
        Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign] at *
      decide


theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) : design.sem N W AccW = mmD N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror
    (mmG.instantiate N W AccW hN hW hA (by have := hR32.1; omega)
      hR32.2.1 hR32.2.2 hR32.1)
    (mmG_D N W AccW) (by exact mm_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by
      simp [mmD, mmCtrl, mmBusAs, mmBusBs, mmCells, mmBusA, mmBusB, mmCell,
        SvGolf.Cycle.notComb]))

end Submission
namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

def MS (ck r s a b dn c k bz an bn ab bb : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c),
    ("k", k), ("busy", bz), ("a_next", an), ("b_next", bn), ("a_bus", ab), ("b_bus", bb)]

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz an bn ab bb : LVec) :
    applyInputs2 (mmD N W AccW) e (MS ck r s a b dn c k bz an bn ab bb) =
      MS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz an bn ab bb := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS, appIn, h1, h2, h3, h4, h5, SvState.set]

abbrev wr (n : String) (old v : LVec) : String × Nat × LVec := (n, 0, v.resizeU old.width)

def ctrlQ (N W : Nat) (r s a b dn k bz an bn : LVec) : NbaQueue2 :=
  if r.condTrue then [wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l0]⟩, wr "k" k (LVec.replicate 32 .l0),
    wr "a_next" an (LVec.replicate (a.width) .l0), wr "b_next" bn (LVec.replicate (b.width) .l0)]
  else if s.condTrue then [wr "busy" bz ⟨#[.l1]⟩, wr "done" dn ⟨#[.l0]⟩, wr "k" k (LVec.replicate 32 .l0),
    wr "a_next" an (a.shr (LVec.ofInt 32 (W : Int))),
    wr "b_next" bn (b.shr (LVec.ofInt 32 ((N*W : Nat) : Int)))]
  else if bz.condTrue then
    if (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue then
      [wr "k" k (k.add (LVec.ofInt 32 1)), wr "a_next" an (an.shr (LVec.ofInt 32 (W : Int))),
        wr "b_next" bn (bn.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))),
        wr "busy" bz ⟨#[.l0]⟩, wr "done" dn ⟨#[.l1]⟩]
    else [wr "k" k (k.add (LVec.ofInt 32 1)), wr "a_next" an (an.shr (LVec.ofInt 32 (W : Int))),
      wr "b_next" bn (bn.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int))))]
  else []

def busAQ (N W : Nat) (r s bz A an ab : LVec) (i : Nat) : NbaQueue2 :=
  if r.condTrue then [("a_bus", i*W, (LVec.replicate W .l0).resizeU W)]
  else if s.condTrue then [("a_bus", i*W, A.extract (i*N*W) W)]
  else if bz.condTrue then [("a_bus", i*W, an.extract (i*N*W) W)] else []

def busBQ (N W : Nat) (r s bz B bn bb : LVec) (j : Nat) : NbaQueue2 :=
  if r.condTrue then [("b_bus", j*W, (LVec.replicate W .l0).resizeU W)]
  else if s.condTrue then [("b_bus", j*W, B.extract (j*W) W)]
  else if bz.condTrue then [("b_bus", j*W, bn.extract (j*W) W)] else []

def sxv (v : LVec) (AccW lo W : Nat) : LVec :=
  LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[v.extract (lo + W - 1) 1]), v.extract lo W]

def cellV (N W AccW i j : Nat) (c ab bb : LVec) : LVec :=
  (((c.extract ((i*N+j)*AccW) AccW).resizeU (AccW+W)).add
    ((sxv ab AccW (i*W) W).mul (sxv bb AccW (j*W) W))).resizeU AccW

def cellQ (N W AccW : Nat) (s bz c ab bb : LVec) (i j : Nat) : NbaQueue2 :=
  if s.condTrue then [("C", (i*N+j)*AccW, (LVec.replicate AccW .l0).resizeU AccW)]
  else if bz.condTrue then [("C", (i*N+j)*AccW, cellV N W AccW i j c ab bb)] else []

theorem ctrl_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz an bn ab bb : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz an bn ab bb) [] (mmCtrl N W) =
      .ok (MS ck r s a b dn c k bz an bn ab bb, ctrlQ N W r s a b dn k bz an bn) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ
  have hprod : (LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)) =
      LVec.ofInt 32 ((N : Int) * W) := by simp [LVec.ofInt_eq_ofBitVec, BitVec.ofInt_mul]
  have hone : LVec.ofBitVec 1#32 = LVec.ofInt 32 1 := by decide
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [mmCtrl, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, wr, h1, h2, h3, h4, hprod, hone]

theorem busA_run (N W i F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz an bn ab bb : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz an bn ab bb) [] (mmBusA N W i) =
      .ok (MS ck r s a b dn c k bz an bn ab bb, busAQ N W r s bz a an ab i) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold busAQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    simp [mmBusA, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, h1, h2, h3, LVec.width_extract, LVec.width_resizeU]
  all_goals first | rfl | rw [LVec.resizeU_of_width]
  all_goals try exact LVec.width_extract _ _ _

theorem busB_run (N W j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz an bn ab bb : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz an bn ab bb) [] (mmBusB N W j) =
      .ok (MS ck r s a b dn c k bz an bn ab bb, busBQ N W r s bz b bn bb j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold busBQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    simp [mmBusB, runEdgeProcess2, execStmt2, evalExpr2, resolveLhs2, readSignal, MS,
      SvState.lookup, evalBinOp, h1, h2, h3, LVec.width_extract, LVec.width_resizeU]
  all_goals first | rfl | rw [LVec.resizeU_of_width]
  all_goals try exact LVec.width_extract _ _ _

theorem cell_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz an bn ab bb : LVec) :
    runEdgeProcess2 F (MS ck r s a b dn c k bz an bn ab bb) [] (mmCell N W AccW i j) =
      .ok (MS ck r s a b dn c k bz an bn ab bb, cellQ N W AccW s bz c ab bb i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold cellQ
  by_cases h1 : s.condTrue = true <;> by_cases h2 : bz.condTrue = true <;>
    simp [mmCell, sext, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS, SvState.lookup, evalBinOp, cellV, sxv, h1, h2, LVec.width_extract, LVec.width_resizeU]
  all_goals first | rfl | rw [LVec.resizeU_of_width]
  all_goals try exact LVec.width_resizeU _ _

def mmQ (N W AccW : Nat) (r s a b dn c k bz an bn ab bb : LVec) : NbaQueue2 :=
  ctrlQ N W r s a b dn k bz an bn ++
    (List.range N).flatMap (fun i => busAQ N W r s bz a an ab i) ++
    (List.range N).flatMap (fun j => busBQ N W r s bz b bn bb j) ++
    (List.range N).flatMap (fun i => (List.range N).flatMap (fun j => cellQ N W AccW s bz c ab bb i j))

def mmNext (N W AccW : Nat) (ck r s a b dn c k bz an bn ab bb : LVec) : SvState :=
  commitNba2 (MS ck r s a b dn c k bz an bn ab bb) (mmQ N W AccW r s a b dn c k bz an bn ab bb)

theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) (σ : ScheduleOracle) (e : SvState)
    (ck r s a b dn c k bz an bn ab bb : LVec) (kk F : Nat) (hF : 30 ≤ F) :
    cycleStep2 (design.sem N W AccW) σ F e (MS ck r s a b dn c k bz an bn ab bb) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb, kk + 3) := by
  have hedge : ∀ p ∈ (mmD N W AccW).processes.toList, p.isEdgePhase = true := by
    intro p hp
    simp only [mmD, List.toList_toArray, List.mem_cons, List.mem_append, mmBusAs, mmBusBs, mmCells,
      List.mem_map, List.mem_flatMap, List.mem_range] at hp
    rcases hp with ((rfl | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨i, hi, hq⟩
    · rfl
    · rfl
    · rfl
    · obtain ⟨i, hi, hq⟩ := hq
      obtain ⟨j, hj, rfl⟩ := hq
      rfl
  rw [mm_sem_eq N W AccW hN hW hA hR32,
    cycleStep2_profile (mm_profile N W AccW) σ e _ kk ?_ ?_ (by omega), apply_mm, clockStep,
    flatMap_ffUpd F _ hedge]
  · simp only [mmD, List.toList_toArray, List.flatMap_cons, List.flatMap_append, ctrl_run N W F hF,
      mmBusAs, mmBusBs, mmCells, List.flatMap_map, List.flatMap_assoc, busA_run N W _ F hF,
      busB_run N W _ F hF, cell_run N W AccW _ _ F hF, mmNext, mmQ]
  · intro i p hp
    rw [apply_mm]
    have hm : p ∈ mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW :=
      List.mem_of_getElem? (by simpa [mmD] using hp :
        (mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW)[i]? = some p)
    simp only [List.mem_cons, List.mem_append, mmBusAs, mmBusBs, mmCells,
      List.mem_map, List.mem_flatMap, List.mem_range] at hm
    rcases hm with ((hctrl | ⟨j, hj, heq⟩) | ⟨j, hj, heq⟩) | ⟨i', hi', j, hj, heq⟩
    · cases hctrl
      exact ⟨ctrlQ N W (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
        (appIn e "B" b) dn k bz an bn,
        ctrl_run N W F hF (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
          (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb⟩
    · cases heq
      exact ⟨busAQ N W (appIn e "rst" r) (appIn e "start" s) bz
          (appIn e "A" a) an ab j,
        busA_run N W j F hF (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
          (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb⟩
    · cases heq
      exact ⟨busBQ N W (appIn e "rst" r) (appIn e "start" s) bz
          (appIn e "B" b) bn bb j,
        busB_run N W j F hF (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
          (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb⟩
    · cases heq
      exact ⟨cellQ N W AccW (appIn e "start" s) bz c ab bb i' j,
        cell_run N W AccW i' j F hF (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
          (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb⟩
  · rw [apply_mm]; simp [MS]

attribute [local simp] condTrue_knownBit

def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r =>
    BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

def busAAt (N W : Nat) {n : Nat} (A : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV W N fun i => BitVec.extractLsb' ((i * N + t) * W) W A)

def busBAt (N W : Nat) {n : Nat} (B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV W N fun j => BitVec.extractLsb' ((t * N + j) * W) W B)

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B (t + 1) i j = psum N W A B t i j +
      Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) :
    Tasks.Matmul.product N W AccW a b =
      packBV AccW (N * N) fun r =>
        BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl



/-- The sign bit of a packed word is the sign bit of its entry. -/
theorem packBV_sign {W n : Nat} (hW : 1 ≤ W) (v : Nat → BitVec W) {r : Nat} (hr : r < n) :
    BitVec.extractLsb' (r * W + W - 1) 1 (packBV W n v) = BitVec.extractLsb' (W - 1) 1 (v r) := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  have hq0 : q = 0 := by omega
  subst q
  simp only [BitVec.getLsbD_extractLsb']
  have hword := extractLsb'_packBV (n := n) v hr
  have hbits := congrArg (fun x : BitVec W => x.getLsbD (W - 1)) hword
  simp only [BitVec.getLsbD_extractLsb'] at hbits
  have hWlt : W - 1 < W := by omega
  simp [hWlt] at hbits
  rw [Nat.add_sub_assoc (by omega)]
  first | exact hbits | (simp [hWlt]; exact hbits) | simpa [hWlt] using hbits | (rw [hbits]; simp [BitVec.getLsbD_eq_getElem hWlt])

/-- The top bit of an entry, read from the whole vector. -/
theorem extract_sign {n : Nat} (A : BitVec n) (X W : Nat) (hW : 1 ≤ W) :
    BitVec.extractLsb' (W - 1) 1 (BitVec.extractLsb' X W A) = BitVec.extractLsb' (X + W - 1) 1 A := by
  apply BitVec.eq_of_getLsbD_eq
  intro q hq
  have hq0 : q = 0 := by omega
  subst hq0
  have hWlt : W - 1 < W := by omega
  simp [BitVec.getLsbD_extractLsb', hWlt, Nat.add_sub_assoc hW]

theorem setWidth_add_mul_signExtend {m n w : Nat} (h : m ≤ n) (x : BitVec m)
    (a b : BitVec w) :
    (x.setWidth n + a.signExtend n * b.signExtend n).setWidth m =
      x + BitVec.ofInt m (a.toInt * b.toInt) := by
  rw [BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq,
    BitVec.setWidth_mul _ _ h, Lib.setWidth_signExtend_of_le _ h,
    Lib.setWidth_signExtend_of_le _ h, BitVec.ofInt_mul]
  rfl

/-- One busy step of a cell: the accumulator gains the term `A[i][t] * B[t][j]`. -/
theorem cell_step {N W AccW : Nat} (hW : 1 ≤ W) (A B : BitVec (N * N * W)) {t i j : Nat}
    (hi : i < N) (hj : j < N) :
    cellV N W AccW i j (accC N W AccW A B t) (busAAt N W A t) (busBAt N W B t) =
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 1) i j)) := by
  have hd : (i * N + j) / N = i := by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have ha : i * W + W ≤ N * W := by have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hb : j * W + W ≤ N * W := by have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have sa := (packBV_sign hW (fun i => BitVec.extractLsb' ((i * N + t) * W) W A) hi).trans (extract_sign A _ W hW)
  have sb := (packBV_sign hW (fun j => BitVec.extractLsb' ((t * N + j) * W) W B) hj).trans (extract_sign B _ W hW)
  have wa := extractLsb'_packBV (n := N) (fun i => BitVec.extractLsb' ((i * N + t) * W) W A) hi
  have wb := extractLsb'_packBV (n := N) (fun j => BitVec.extractLsb' ((t * N + j) * W) W B) hj
  have wc := extractLsb'_packBV (n := N * N) (fun r => BitVec.ofInt AccW (psum N W A B t (r / N) (r % N))) hr
  simp only [hd, hm] at wc
  simp (disch := omega) only [cellV, sxv, accC, busAAt, busBAt, LVec.extract_ofBitVec, wa, wb, wc, sa, sb,
    LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.resizeU_of_width (LVec.width_resizeU _ _),
    LVec.resizeU_of_width (LVec.width_extract _ _ _), LVec.add_ofBitVec, BitVec.setWidth_eq,
    setWidth_add_mul_signExtend, psum_succ, BitVec.ofInt_add, Tasks.Matmul.entry]

section commit
variable {ck r s a b dn c k bz an bn ab bb : LVec} {lo : Nat} {v : LVec}
theorem nb_busy : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("busy", lo, v) =
    MS ck r s a b dn c k (bz.insertAt lo v) an bn ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_done : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("done", lo, v) =
    MS ck r s a b (dn.insertAt lo v) c k bz an bn ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_k : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("k", lo, v) =
    MS ck r s a b dn c (k.insertAt lo v) bz an bn ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_an : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("a_next", lo, v) =
    MS ck r s a b dn c k bz (an.insertAt lo v) bn ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bn : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("b_next", lo, v) =
    MS ck r s a b dn c k bz an (bn.insertAt lo v) ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_ab : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("a_bus", lo, v) =
    MS ck r s a b dn c k bz an bn (ab.insertAt lo v) bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]
theorem nb_bb : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("b_bus", lo, v) =
    MS ck r s a b dn c k bz an bn ab (bb.insertAt lo v) := by simp [nbaStep, MS, SvState.lookup, SvState.set]
end commit

theorem commit_C {ck r s a b dn k bz an bn ab bb : LVec} : ∀ {q : NbaQueue2},
    (∀ u ∈ q, u.1 = "C") → ∀ c,
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb) q =
      MS ck r s a b dn (q.foldl (fun acc u => acc.insertAt u.2.1 u.2.2) c) k bz an bn ab bb
  | [], _, _ => rfl
  | ⟨n,lo,v⟩ :: q, h, c => by
    obtain rfl : n = "C" := h _ List.mem_cons_self
    rw [commitNba2_cons, List.foldl_cons, ← commit_C (fun u hu => h u (List.mem_cons_of_mem _ hu))]
    congr 1

theorem rowMajor_map {N AccW : Nat} {q : Nat → Nat → NbaQueue2} (g : Nat → LVec)
    (h : ∀ i j, i < N → j < N → q i j = [("C", (i*N+j)*AccW, g (i*N+j))]) :
    (List.range N).flatMap (fun i => (List.range N).flatMap (q i)) =
      (List.range (N*N)).map (fun r => ("C", r*AccW, g r)) := by
  suffices ∀ M, M ≤ N → (List.range M).flatMap (fun i => (List.range N).flatMap (q i)) =
      (List.range (M*N)).map (fun r => ("C", r*AccW, g r)) from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [CombView.flatMap_congr' fun j hj => h M j (by omega) (List.mem_range.mp hj)]
    congr 1
    induction (List.range N) with
    | nil => rfl
    | cons a l ih' => rw [List.flatMap_cons, ih']; rfl

theorem commit_map (AccW : Nat) (g : Nat → LVec) (n : Nat) {ck r s a b dn c k bz an bn ab bb : LVec} :
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb)
      ((List.range n).map (fun r => ("C", r*AccW, g r))) =
      MS ck r s a b dn (LVec.insertEntries AccW g n c) k bz an bn ab bb := by
  rw [commit_C (by simp), List.foldl_map]
  rfl

/-! ## g38h: the queues' names -/

theorem ctrlQ_names (N W : Nat) (r s a b dn k bz an bn : LVec) :
    ∀ u ∈ ctrlQ N W r s a b dn k bz an bn, u.1 ∈ ["busy", "done", "k", "a_next", "b_next"] := by
  unfold ctrlQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [h1, h2, h3, h4, wr]

theorem busAQ_names (N W : Nat) (r s bz A an ab : LVec) (i : Nat) :
    ∀ u ∈ busAQ N W r s bz A an ab i, u.1 = "a_bus" := by
  unfold busAQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    simp [h1, h2, h3]

theorem busBQ_names (N W : Nat) (r s bz B bn bb : LVec) (j : Nat) :
    ∀ u ∈ busBQ N W r s bz B bn bb j, u.1 = "b_bus" := by
  unfold busBQ
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;> by_cases h3 : bz.condTrue = true <;>
    simp [h1, h2, h3]

theorem cellQ_names (N W AccW : Nat) (s bz c ab bb : LVec) (i j : Nat) :
    ∀ u ∈ cellQ N W AccW s bz c ab bb i j, u.1 = "C" := by
  unfold cellQ
  by_cases h1 : s.condTrue = true <;> by_cases h2 : bz.condTrue = true <;> simp [h1, h2]

/-- The data part of the cycle's queue (buses and cells). -/
def dataQ (N W AccW : Nat) (r s a b c bz an bn ab bb : LVec) : NbaQueue2 :=
  (List.range N).flatMap (fun i => busAQ N W r s bz a an ab i) ++
    (List.range N).flatMap (fun j => busBQ N W r s bz b bn bb j) ++
    (List.range N).flatMap (fun i => (List.range N).flatMap (fun j => cellQ N W AccW s bz c ab bb i j))

theorem mmQ_eq (N W AccW : Nat) (r s a b dn c k bz an bn ab bb : LVec) :
    mmQ N W AccW r s a b dn c k bz an bn ab bb =
      ctrlQ N W r s a b dn k bz an bn ++ dataQ N W AccW r s a b c bz an bn ab bb := by
  simp only [mmQ, dataQ, List.append_assoc]

theorem dataQ_names (N W AccW : Nat) (r s a b c bz an bn ab bb : LVec) :
    ∀ u ∈ dataQ N W AccW r s a b c bz an bn ab bb, u.1 = "a_bus" ∨ u.1 = "b_bus" ∨ u.1 = "C" := by
  intro u hu
  simp only [dataQ, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with (⟨i, -, hu⟩ | ⟨j, -, hu⟩) | ⟨i, -, j, -, hu⟩
  · exact .inl (busAQ_names _ _ _ _ _ _ _ _ _ u hu)
  · exact .inr (.inl (busBQ_names _ _ _ _ _ _ _ _ _ u hu))
  · exact .inr (.inr (cellQ_names _ _ _ _ _ _ _ _ _ _ u hu))

theorem mmQ_names (N W AccW : Nat) (r s a b dn c k bz an bn ab bb : LVec) :
    ∀ u ∈ mmQ N W AccW r s a b dn c k bz an bn ab bb,
      u.1 ∈ ["busy", "done", "k", "a_next", "b_next", "a_bus", "b_bus", "C"] := by
  intro u hu
  rw [mmQ_eq, List.mem_append] at hu
  rcases hu with hu | hu
  · have := ctrlQ_names _ _ _ _ _ _ _ _ _ _ _ u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with h | h | h | h | h <;> simp [h]
  · rcases dataQ_names _ _ _ _ _ _ _ _ _ _ _ _ _ u hu with h | h | h <;> simp [h]

def Wd (N W AccW : Nat) (dn c k bz an bn ab bb : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N*N*AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  an.width = N*N*W ∧ bn.width = N*N*W ∧ ab.width = N*W ∧ bb.width = N*W

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz an bn ab bb, st = MS ck r s a b dn c k bz an bn ab bb ∧
    Wd N W AccW dn c k bz an bn ab bb

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz an bn ab bb : LVec)
    (hw : Wd N W AccW dn c k bz an bn ab bb) :
    I N W AccW (mmNext N W AccW ck r s a b dn c k bz an bn ab bb) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := hw
  have hnd : ((MS ck r s a b dn c k bz an bn ab bb).map Prod.fst).Nodup := by
    simp [MS]
  unfold I
  rw [mmNext, commitNba2_eq_map_of_names hnd (mmQ_names N W AccW r s a b dn c k bz an bn ab bb)]
  refine ⟨ck, r, s, a, b, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [Wd, width_nbaFold, h1, h2, h3, h4, h5, h6, h7, h8]

theorem mm_noq (N W AccW : Nat) :
    (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmCtrl, mmBusAs, mmBusBs, mmCells, mmBusA, mmBusB, mmCell, nb,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1,
    .xVec (N * N * AccW), .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W),
    .xVec (N * W), .xVec (N * W), ?_, by simp [Wd]⟩
  simp [initState2, mmD, mmDecls, MS]

theorem mm_terminates (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) :
    Terminates2 (design.sem N W AccW) := by
  refine Terminates2.of_invariant (I N W AccW) (mm_init N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
    (by
      apply run2ClockGuard_ok_of_profile
      rw [mm_sem_eq N W AccW hN hW hA hR32]
      exact mm_profile N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e
      ck r s a b dn c k bz an bn ab bb kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz an bn ab bb hw⟩

theorem MS_inj {ck r s a b dn c k bz an bn ab bb ck' r' s' a' b' dn' c' k' bz' an' bn' ab' bb' : LVec}
    (h : MS ck r s a b dn c k bz an bn ab bb = MS ck' r' s' a' b' dn' c' k' bz' an' bn' ab' bb') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ an = an' ∧ bn = bn' ∧ ab = ab' ∧ bb = bb' := by
  simp only [MS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem next_idle (N W AccW : Nat) (ck a b dn c k an bn ab bb : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) an bn ab bb =
      MS ck (knownBit false) (knownBit false) a b dn c k (knownBit false) an bn ab bb := by
  have hq : mmQ N W AccW (knownBit false) (knownBit false) a b dn c k
      (knownBit false) an bn ab bb = [] := by
    simp [mmQ, ctrlQ, busAQ, busBQ, cellQ, condTrue_knownBit]
  rw [mmNext, hq]
  rfl

/-! ## g38h: commits per register family -/

section commit2
variable {ck r s a b dn c k bz an bn ab bb : LVec}

theorem nb_C {lo : Nat} {v : LVec} : nbaStep (MS ck r s a b dn c k bz an bn ab bb) ("C", lo, v) =
    MS ck r s a b dn (c.insertAt lo v) k bz an bn ab bb := by simp [nbaStep, MS, SvState.lookup, SvState.set]

theorem commit_ab_l (f : Nat → Nat) (g : Nat → LVec) : ∀ (l : List Nat) (ab : LVec),
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb) (l.map fun x => ("a_bus", f x, g x)) =
      MS ck r s a b dn c k bz an bn (l.foldl (fun z x => z.insertAt (f x) (g x)) ab) bb
  | [], _ => rfl
  | x :: l, ab => by rw [List.map_cons, commitNba2_cons, nb_ab, commit_ab_l f g l]; rfl

theorem commit_bb_l (f : Nat → Nat) (g : Nat → LVec) : ∀ (l : List Nat) (bb : LVec),
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb) (l.map fun x => ("b_bus", f x, g x)) =
      MS ck r s a b dn c k bz an bn ab (l.foldl (fun z x => z.insertAt (f x) (g x)) bb)
  | [], _ => rfl
  | x :: l, bb => by rw [List.map_cons, commitNba2_cons, nb_bb, commit_bb_l f g l]; rfl

/-- Commit the row-bus writes: `a_bus` gets its `N` words, nothing else moves. -/
theorem commit_ab (W : Nat) (g : Nat → LVec) (n : Nat) :
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb) ((List.range n).map fun x => ("a_bus", x * W, g x)) =
      MS ck r s a b dn c k bz an bn (LVec.insertEntries W g n ab) bb := by
  rw [commit_ab_l]; rfl

/-- Commit the column-bus writes. -/
theorem commit_bb (W : Nat) (g : Nat → LVec) (n : Nat) :
    commitNba2 (MS ck r s a b dn c k bz an bn ab bb) ((List.range n).map fun x => ("b_bus", x * W, g x)) =
      MS ck r s a b dn c k bz an bn ab (LVec.insertEntries W g n bb) := by
  rw [commit_bb_l]; rfl

/-- A queue that writes only the buses and `C` leaves the control registers alone (values not tracked). -/
theorem commit_rest : ∀ (q : NbaQueue2), (∀ u ∈ q, u.1 = "a_bus" ∨ u.1 = "b_bus" ∨ u.1 = "C") →
    ∀ (c ab bb : LVec), ∃ c' ab' bb', commitNba2 (MS ck r s a b dn c k bz an bn ab bb) q =
      MS ck r s a b dn c' k bz an bn ab' bb'
  | [], _, c, ab, bb => ⟨c, ab, bb, rfl⟩
  | ⟨n, lo, v⟩ :: q, h, c, ab, bb => by
    rw [commitNba2_cons]
    have hq := fun u hu => h u (List.mem_cons_of_mem _ hu)
    rcases h _ List.mem_cons_self with hn | hn | hn
    · obtain rfl : n = "a_bus" := hn
      rw [nb_ab]; exact commit_rest q hq _ _ _
    · obtain rfl : n = "b_bus" := hn
      rw [nb_bb]; exact commit_rest q hq _ _ _
    · obtain rfl : n = "C" := hn
      rw [nb_C]; exact commit_rest q hq _ _ _
end commit2

/-! ## g38h: the buses' contents -/

/-- Loading every row-bus word from the first column of a known matrix register. -/
theorem busA_feed {N W : Nat} (X : BitVec (N * N * W)) (ab : LVec) (hab : ab.width = N * W) :
    LVec.insertEntries W (fun i => (LVec.ofBitVec X).extract (i * N * W) W) N ab =
      LVec.ofBitVec (packBV W N fun i => BitVec.extractLsb' (i * N * W) W X) := by
  rw [← LVec.insertEntries_ofBitVec _ ab hab]
  refine LVec.insertEntries_congr ab N fun i hi => LVec.extract_ofBitVec _ ?_
  have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (j := 0) hi (by omega)
  simpa using this

/-- Loading every column-bus word from the first row of a known matrix register. -/
theorem busB_feed {N W : Nat} (X : BitVec (N * N * W)) (bb : LVec) (hbb : bb.width = N * W) :
    LVec.insertEntries W (fun j => (LVec.ofBitVec X).extract (j * W) W) N bb =
      LVec.ofBitVec (packBV W N fun j => BitVec.extractLsb' (j * W) W X) := by
  rw [← LVec.insertEntries_ofBitVec _ bb hbb]
  refine LVec.insertEntries_congr bb N fun j hj => LVec.extract_ofBitVec _ ?_
  have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (by omega) hj
  simpa using this

theorem busAAt_width (N W : Nat) {n : Nat} (A : BitVec n) (t : Nat) : (busAAt N W A t).width = N * W := by
  simp [busAAt]

theorem busBAt_width (N W : Nat) {n : Nat} (B : BitVec n) (t : Nat) : (busBAt N W B t).width = N * W := by
  simp [busBAt]

theorem accC_width (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) :
    (accC N W AccW A B t).width = N * N * AccW := by
  simp [accC]

/-- The row bus after `a_next = A >>> ((t+1)·W)` is loaded: column `t+1` of `A`. -/
theorem busA_shift {N W : Nat} (A : BitVec (N * N * W)) (t : Nat) (ab : LVec) (hab : ab.width = N * W) :
    LVec.insertEntries W (fun i => (LVec.ofBitVec (A >>> ((t + 1) * W))).extract (i * N * W) W) N ab =
      busAAt N W A (t + 1) := by
  rw [busA_feed _ ab hab, busAAt]
  congr 2; funext i
  rw [Lib.extractLsb'_ushiftRight]
  congr 1
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  first | done | omega

/-- The column bus after `b_next = B >>> ((t+1)·N·W)` is loaded: row `t+1` of `B`. -/
theorem busB_shift {N W : Nat} (B : BitVec (N * N * W)) (t : Nat) (bb : LVec) (hbb : bb.width = N * W) :
    LVec.insertEntries W (fun j => (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract (j * W) W) N bb =
      busBAt N W B (t + 1) := by
  rw [busB_feed _ bb hbb, busBAt]
  congr 2; funext j
  rw [Lib.extractLsb'_ushiftRight]
  congr 1
  simp only [Nat.add_mul, Nat.mul_assoc, Nat.one_mul]
  first | done | omega

/-! ## g38h: the control in a busy cycle -/

theorem ctrl_busy {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31) (A B : BitVec (N * N * W))
    {t : Nat} (ht : t < N) (ck a b c ab bb : LVec) :
    commitNba2 (MS ck (knownBit false) (knownBit false) a b (knownBit false) c (LVec.ofBitVec (BitVec.ofNat 32 t))
      (knownBit true) (LVec.ofBitVec (A >>> ((t + 1) * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) ab bb)
      (ctrlQ N W (knownBit false) (knownBit false) a b (knownBit false) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
        (LVec.ofBitVec (A >>> ((t + 1) * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W))))) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N))) c (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
      (knownBit (decide (t + 1 ≠ N))) (LVec.ofBitVec (A >>> ((t + 1) * W + W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W) + N * W))) ab bb := by
  have hNW0 : N * W ≤ N * N * W := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hN
  have hNW : N * W < 2 ^ 32 := by simp only [Nat.reducePow] at hr ⊢; omega
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW', Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW]
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [ctrlQ, wr, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
    BitVec.ofInt_natCast, BitVec.ofInt_ofNat, h1', LVec.mul_ofBitVec, LVec.sub_ofBitVec,
    LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq, Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN'),
    LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW, ← BitVec.shiftRight_add]
  by_cases hf : t + 1 = N <;>
    simp [hf, commitNba2_cons, commitNba2_nil, nb_k, nb_an, nb_bn, nb_busy, nb_done,
      LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1, BitVec.ofNat_add_ofNat]

/-! ## g38h: the busy step (the invariant on `k`) -/

theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hr : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) (accC N W AccW A B t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec (A >>> ((t + 1) * W)))
      (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) (busAAt N W A t) (busBAt N W B t) =
    MS ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N))) (accC N W AccW A B (t + 1))
      (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ N)))
      (LVec.ofBitVec (A >>> ((t + 1 + 1) * W))) (LVec.ofBitVec (B >>> ((t + 1 + 1) * (N * W))))
      (busAAt N W A (t + 1)) (busBAt N W B (t + 1)) := by
  have hqA : (List.range N).flatMap (fun i => busAQ N W (knownBit false) (knownBit false) (knownBit true) a
        (LVec.ofBitVec (A >>> ((t + 1) * W))) (busAAt N W A t) i) =
      (List.range N).map (fun i => ("a_bus", i * W, (LVec.ofBitVec (A >>> ((t + 1) * W))).extract (i * N * W) W)) :=
    flatMap_range_singleton (fun i _ => by simp [busAQ])
  have hqB : (List.range N).flatMap (fun j => busBQ N W (knownBit false) (knownBit false) (knownBit true) b
        (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))) (busBAt N W B t) j) =
      (List.range N).map (fun j => ("b_bus", j * W, (LVec.ofBitVec (B >>> ((t + 1) * (N * W)))).extract (j * W) W)) :=
    flatMap_range_singleton (fun j _ => by simp [busBQ])
  have hqC := rowMajor_map (N := N) (AccW := AccW)
    (q := fun i j => cellQ N W AccW (knownBit false) (knownBit true) (accC N W AccW A B t)
      (busAAt N W A t) (busBAt N W B t) i j)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B (t + 1) (r / N) (r % N))))
    (fun i j hi hj => by
      have hd : (i * N + j) / N = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
      have hm : (i * N + j) % N = j := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
      simp only [cellQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, cell_step hW A B hi hj, hd, hm])
  rw [mmNext, mmQ, commitNba2_append, commitNba2_append, commitNba2_append,
    ctrl_busy hN hW hr A B ht, hqA, commit_ab, hqB, commit_bb, hqC, commit_map,
    busA_shift A t _ (busAAt_width ..), busB_shift B t _ (busBAt_width ..),
    LVec.insertEntries_ofBitVec
      (fun r => BitVec.ofInt AccW (psum N W A B (t + 1) (r / N) (r % N))) _ (accC_width ..),
    Nat.succ_mul (t + 1) W, Nat.succ_mul (t + 1) (N * W)]
  rfl

/-! ## g38h: reset and start -/

theorem next_reset {N W AccW : Nat} (ck s a b dn c k bz an bn ab bb : LVec)
    (hw : Wd N W AccW dn c k bz an bn ab bb) :
    ∃ c' k' an' bn' ab' bb', mmNext N W AccW ck (knownBit true) s a b dn c k bz an bn ab bb =
      MS ck (knownBit true) s a b (knownBit false) c' k' (knownBit false) an' bn' ab' bb' := by
  obtain ⟨h1, -, -, h4, -, -, -, -⟩ := hw
  rw [mmNext, mmQ_eq, commitNba2_append]
  simp only [ctrlQ, condTrue_knownBit, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, nb_an, nb_bn, wr, h1, h4, LVec.resizeU_one_l0]
  obtain ⟨c', ab', bb', h⟩ := commit_rest (dataQ N W AccW (knownBit true) s a b c bz an bn ab bb)
    (dataQ_names N W AccW _ _ _ _ _ _ _ _ _ _) c ab bb
  have hd : dn.insertAt 0 (knownBit false) = knownBit false := LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : bz.insertAt 0 (knownBit false) = knownBit false := LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [h, hd, hb]
  exact ⟨c', _, _, _, ab', bb', rfl⟩

theorem next_start {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) (ck dn c k bz an bn ab bb : LVec)
    (hw : Wd N W AccW dn c k bz an bn ab bb) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) dn c k bz an bn ab bb =
      MS ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false)
        (accC N W AccW A B 0) (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true)
        (LVec.ofBitVec (A >>> ((0 + 1) * W))) (LVec.ofBitVec (B >>> ((0 + 1) * (N * W))))
        (busAAt N W A 0) (busBAt N W B 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  have hqA : (List.range N).flatMap (fun i => busAQ N W (knownBit false) (knownBit true) bz (LVec.ofBitVec A)
        an ab i) =
      (List.range N).map (fun i => ("a_bus", i * W, (LVec.ofBitVec A).extract (i * N * W) W)) :=
    flatMap_range_singleton (fun i _ => by simp [busAQ])
  have hqB : (List.range N).flatMap (fun j => busBQ N W (knownBit false) (knownBit true) bz (LVec.ofBitVec B)
        bn bb j) =
      (List.range N).map (fun j => ("b_bus", j * W, (LVec.ofBitVec B).extract (j * W) W)) :=
    flatMap_range_singleton (fun j _ => by simp [busBQ])
  have hqC := rowMajor_map (N := N) (AccW := AccW)
    (q := fun i j => cellQ N W AccW (knownBit true) bz c ab bb i j)
    (fun r => LVec.ofBitVec (BitVec.ofInt AccW (psum N W A B 0 (r / N) (r % N))))
    (fun i j hi hj => by simp [cellQ, psum])
  have hNW_le : N * W ≤ N * N * W := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_left _ hN
  have hNW32 : N * W < 2 ^ 32 := by simp only [Nat.reducePow] at hNW ⊢; omega
  have hW32 : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW32
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW32]
  have hyNW : (BitVec.ofNat 32 (N * W)).toNat = N * W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNW32]
  rw [mmNext, mmQ, commitNba2_append, commitNba2_append, commitNba2_append]
  simp only [ctrlQ, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, commitNba2_cons, commitNba2_nil, nb_busy,
    nb_done, nb_k, nb_an, nb_bn, wr, h1, h3, h4, h5, h6, LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.replicate_l0,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq, LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, LVec.shr_ofBitVec,
    hyW, hyNW]
  rw [hqA, commit_ab, hqB, commit_bb, hqC, commit_map, busA_feed A ab h7, busB_feed B bb h8,
    LVec.insertEntries_ofBitVec _ _ h2, LVec.insertAt_zero_of_width_eq (by simp [h1]),
    LVec.insertAt_zero_of_width_eq (by simp [h3]), LVec.insertAt_zero_of_width_eq (by simp [h4]),
    LVec.insertAt_zero_of_width_eq (by simp [h5]), LVec.insertAt_zero_of_width_eq (by simp [h6])]
  simp [accC, busAAt, busBAt]


/-
g38 RESERVE (lead helper, 2026-11-20): the phases, x-safety and `solution`, proved on your definitions after handovers 1-3.
This part is YOURS to write (transplant of your g61 record). Open this file only for a piece that has stopped you
after three different tries, and take that piece only. With all of it pasted after handover 3 the checker at the
new range accepts g38 (standard axioms).
-/

/-! ## g38h: the protocol phases -/

set_option maxHeartbeats 1000000

/-- The state `t` busy cycles after a start with operands `A`, `B`. -/
def BusyAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b, st = MS ck r s a b (knownBit false) (accC N W AccW A B t) (LVec.ofBitVec (BitVec.ofNat 32 t))
    (knownBit true) (LVec.ofBitVec (A >>> ((t + 1) * W))) (LVec.ofBitVec (B >>> ((t + 1) * (N * W))))
    (busAAt N W A t) (busBAt N W B t)

/-- Finished with `A`, `B`: `done` = 1 and `C` the product. -/
def FinAt (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k an bn ab bb, st = MS ck r s a b (knownBit true)
    (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k (knownBit false) an bn ab bb

/-- One cycle from a state of the shape, evaluated (`mm_cycle`). -/
def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz an bn ab bb, prev = MS ck r s a b dn c k bz an bn ab bb ∧
    Wd N W AccW dn c k bz an bn ab bb ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz an bn ab bb

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hR32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, an, bn, ab, bb, rfl, hw⟩ hc
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, an, bn, ab, bb, rfl, hw, (Prod.mk.inj (cycleStep2_det hc
      (mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c kk bz an bn ab bb k 30 (Nat.le_refl _)))).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz an bn ab bb hw
  Ready st := ∃ ck r s a b c k an bn ab bb,
    st = MS ck r s a b (knownBit false) c k (knownBit false) an bn ab bb
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt N W AccW x.1 x.2.1 t st
  Fin x st := FinAt N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, an, bn, ab, bb, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, an, bn, ab, bb, rfl⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨c', k', an', bn', ab', bb', h⟩ := next_reset (appIn e "clk" ck) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn c k bz an bn ab bb hw
    rw [h]
    exact ⟨_, _, _, _, _, c', k', an', bn', ab', bb', rfl⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb,
      next_start hN hW hNW _ _ _ dn c k bz an bn ab bb hw]
    exact .inr ⟨N - 1, by omega, 0, by omega, _, _, _, _, _, rfl⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', hb⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s,
      next_step (AccW := AccW) hN hW hNW x.1 x.2.1 (t := t) (by omega)]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', an', bn', ab', bb', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', an', bn', ab', bb', hb⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_next", "b_next", "a_bus", "b_bus"] :
      List String).Nodup
    decide⟩

theorem mm_proc_mem {N W AccW : Nat} {p : Process2}
    (hp : p ∈ mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW) :
    p = mmCtrl N W ∨ (∃ i, i < N ∧ p = mmBusA N W i) ∨ (∃ j, j < N ∧ p = mmBusB N W j) ∨
      ∃ i j, i < N ∧ j < N ∧ p = mmCell N W AccW i j := by
  simp only [List.mem_cons, List.mem_append, mmBusAs, mmBusBs, mmCells,
    List.mem_map, List.mem_flatMap, List.mem_range] at hp
  rcases hp with ((rfl | ⟨i, hi, rfl⟩) | ⟨j, hj, rfl⟩) | ⟨i, hi, j, hj, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨i, hi, rfl⟩)
  · exact .inr (.inr (.inl ⟨j, hj, rfl⟩))
  · exact .inr (.inr (.inr ⟨i, j, hi, hj, rfl⟩))

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW := by simpa [mmD] using hp
  rcases mm_proc_mem hm with rfl | ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmCtrl, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmBusA, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, mmBusB, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]
  · simp [Tasks.Matmul.task, mmCell, sext, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact MooreOutDep.of_noComb (combDeps_of_ffOnly (FFOnly.ofProfile (mm_profile N W AccW)))
    (by simp [mmD, mmDecls, Design2.outputNames, Design2.inputNames])

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) (st : SvState)
    (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA hR32] at h
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨k, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨an, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bn, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨ab, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨bb, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain rfl := powerUp_nil.mp h13
  exact ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, w6, w7, w8, w9, w10, w11, w12, w13⟩

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW) (mm_powerUp N W AccW hN hW hA hR32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, an, bn, ab, bb, rfl, hw⟩
  exact ⟨_, _, mm_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz an bn ab bb kk 30 (Nat.le_refl _),
    mmNext_I N W AccW _ _ _ _ _ dn c k bz an bn ab bb hw⟩

theorem lvec_l0_known : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem ctrl_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (mmCtrl N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmCtrl, nb, c32, mmD, mmDecls,
    lvec_l0_known, lvec_l1_known, LVec.replicate_l0, LVec.ofInt]

theorem busA_xsafe {N W AccW i : Nat} (hi : i < N) : xsProc (mmD N W AccW) (mmBusA N W i) = true := by
  have hb : i * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have ha : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (j := 0) hi (by omega)
    simpa using this
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmBusA, mmD, mmDecls,
    LVec.replicate_l0, ha, hb]

theorem busB_xsafe {N W AccW j : Nat} (hj : j < N) : xsProc (mmD N W AccW) (mmBusB N W j) = true := by
  have hb : j * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have ha : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (N := N) (w := W) (i := 0) (by omega) hj
    simpa using this
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmBusB, mmD, mmDecls,
    LVec.replicate_l0, ha, hb]

theorem cell_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (mmCell N W AccW i j) = true := by
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have ha : i * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hb : j * W + W ≤ N * W := by
    have := Nat.mul_le_mul_right W (show j + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have ha1 : i * W + W - 1 + 1 ≤ N * W := by omega
  have hb1 : j * W + W - 1 + 1 ≤ N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmCell, sext, mmD, mmDecls,
    LVec.replicate_l0, hC, ha, hb, ha1, hb1]

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ mmCtrl N W :: mmBusAs N W ++ mmBusBs N W ++ mmCells N W AccW := by simpa [mmD] using hp
  rcases mm_proc_mem hm with rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · exact ctrl_xsafe N W AccW
  · exact busA_xsafe hi
  · exact busB_xsafe hj
  · exact cell_xsafe hW hi hj

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hNW : N * N * W < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hW127) (by decide)
  have hNA : N * N * AccW < 2 ^ 31 := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.mul_le_mul hN256 hN256) hA64) (by decide)
  have hR32 : Rng32 N W AccW := rng32_of hN hW hA hNW hNA
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface N W AccW hN hW hA hR32)
    (mm_disciplined N W AccW hN hW hA hR32) (mm_terminatesPU N W AccW hN hW hA hR32) hN
    (model N W AccW hN hW hA hR32 hNW) (mm_powerUp N W AccW hN hW hA hR32) (mm_moore N W AccW hN hW hA hR32)
    (mm_xsafe N W AccW hN hW hA hR32)



end Submission
