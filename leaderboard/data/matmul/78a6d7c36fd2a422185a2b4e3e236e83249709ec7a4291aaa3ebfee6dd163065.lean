-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle
namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

def c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)
def c32n (v : Nat) : Expr2 := .lit (LVec.ofInt 32 v)
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)
def mmDecls (wa wc : Nat) : List Decl :=
  [{name:="clk",width:=1,isInput:=true},{name:="rst",width:=1,isInput:=true},{name:="start",width:=1,isInput:=true},
   {name:="A",width:=wa,isInput:=true},{name:="B",width:=wa,isInput:=true},{name:="done",width:=1,isOutput:=true},
   {name:="C",width:=wc,isOutput:=true},{name:="k",width:=32},{name:="busy",width:=1},{name:="a_mem",width:=wa},
   {name:="b_mem",width:=wa},{name:="a_pick",width:=wa},{name:="b_pick",width:=wa}]
def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩,nb "done" ⟨#[.l0]⟩,nb "k" (LVec.ofBitVec 0#32)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩,nb "done" ⟨#[.l0]⟩,nb "k" (LVec.ofBitVec 0#32),.nbaAssign (.ident "a_mem") (.ident "A"),.nbaAssign (.ident "b_mem") (.ident "B")])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "k") (.binary .add (.ident "k") (LVec.ofBitVec 1#32 |> fun x => .lit x)),
          .ifStmt (.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1))) (.block #[nb "busy" ⟨#[.l0]⟩,nb "done" ⟨#[.l1]⟩]) none]) none)))))
def pickA (N W i j : Nat) : Process2 :=
  .assign (.slice "a_pick" ((i*N+j)*W) W)
    (.resize W (.binary (.shr false) (.ident "a_mem")
      (.binary .add (.binary .mul (.binary .mul (c32n i) (c32n N)) (c32n W))
        (.binary .mul (.ident "k") (c32n W)))))
def pickB (N W i j : Nat) : Process2 :=
  .assign (.slice "b_pick" ((i*N+j)*W) W)
    (.resize W (.binary (.shr false) (.ident "b_mem")
      (.binary .add (.binary .mul (.binary .mul (.ident "k") (c32n N)) (c32n W))
        (.binary .mul (c32n j) (c32n W)))))
def mmCell (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.logical false (.ident "rst") (.ident "start"))
    (.nbaAssign (.slice "C" ((i*N+j)*AccW) AccW) (.lit (LVec.ofBitVec 0#AccW)))
    (some (.ifStmt (.ident "busy")
      (.nbaAssign (.slice "C" ((i*N+j)*AccW) AccW)
        (.resize AccW (.binary .add (.resize (AccW+W) (.slice (.ident "C") ((i*N+j)*AccW) AccW))
          (.binary .mul (sext "a_pick" AccW ((i*N+j)*W) W) (sext "b_pick" AccW ((i*N+j)*W) W))))) none)))
def mmCells (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j => [pickA N W i j,pickB N W i j,mmCell N W AccW i j]
def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N*N*W) (N*N*AccW)).toArray
  processes := (mmCtrl N W :: mmCells N W AccW).toArray
abbrev Rng32 (N W AccW : Nat) : Prop := N < 46341 ∧ W < 2147483648 ∧ AccW < 2147483648
theorem rng32_of {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hNW : N * N * W < 2 ^ 31) (hNA : N * N * AccW < 2 ^ 31) : Rng32 N W AccW := by
  have h2 := Nat.le_mul_of_pos_right (N * N) hW
  have h3 := Nat.le_mul_of_pos_left W (Nat.mul_pos hN hN)
  have h4 := Nat.le_mul_of_pos_left AccW (Nat.mul_pos hN hN)
  refine ⟨Nat.lt_of_not_le fun h => ?_, by omega, by omega⟩
  have := Nat.mul_le_mul h h
  omega
sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
  (hN46 : N < 46341)
theorem mmG_D (N W AccW : Nat) : mmG.D N W AccW = mmD N W AccW := by
  have ha : mmG.g_col N W AccW = pickA N W := by
    funext i j
    rfl
  have hb : mmG.g_col_1 N W AccW = pickB N W := by
    funext i j
    simp [mmG.g_col_1, pickB, c32n, LVec.ofInt_eq_ofBitVec]
  have hc : mmG.g_col_2 N W AccW = fun i j => mmCell N W AccW i j := by
    funext i j
    have hlor : (SymBinOp.lor == SymBinOp.land) = false := by decide
    simp [mmG.g_col_2, mmCell, sext, hlor]
  simp [mmG.D, mmD, mmG.decls, mmDecls, mmG.procs, mmG.p0, mmCtrl, mmCells,
    pickA, pickB, mmCell, c32, nb, sext, ha, hb, hc]

theorem g20_driversOk_of_procDisj {names inputs : List String} {ps : List Process2}
    (hdw : (driverWins names ps).Pairwise (fun a b => a.overlaps b = false))
    (hdv : ∀ w ∈ driverWins names ps, inputs.contains w.1 = false ∧
      ∀ v ∈ ps.flatMap Process2.procWins, w.overlaps v = false)
    (hin : ∀ n ∈ ps.flatMap Process2.procWrites, inputs.contains n = false)
    (hdisj : ps.Pairwise fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false) :
    driversOk names inputs ps = true := by
  rw [driversOk_iff]
  refine ⟨hdw, hdv, hin, hdisj.imp fun {p q} h => ?_⟩
  have hany : ((p.procWinsOn names).any fun a => (q.procWinsOn names).any fun b => a.overlaps b) = false := by
    rw [List.any_eq_false]
    intro a ha
    rw [Bool.not_eq_true, List.any_eq_false]
    intro b hb
    rw [h a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1]
    exact Bool.false_ne_true
  simp [Process2.exclClash, hany]

theorem g20_driverWins (N W AccW : Nat) :
    driverWins ["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_mem", "b_mem", "a_pick", "b_pick"]
      (mmCtrl N W :: mmCells N W AccW) =
      (List.range N).flatMap (fun i => (List.range N).flatMap (fun j =>
        [("a_pick", some ((i * N + j) * W, W)), ("b_pick", some ((i * N + j) * W, W))])) := by
  simp [driverWins, mmCells, mmCtrl, pickA, pickB, mmCell, Process2.drvWins,
    Lhs2.drvWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    design.pdesign, List.flatMap_assoc]

theorem g20_procWin_name {N W AccW : Nat} {p : Process2} (hp : p ∈ mmCtrl N W :: mmCells N W AccW)
    {v : DrvWin} (hv : v ∈ p.procWins) :
    v.1 ∈ ["busy", "done", "k", "a_mem", "b_mem", "C"] := by
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [mmCtrl, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
      Stmt2.drvWinsList, Lhs2.drvWins] at hv
    rcases hv with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · simp only [mmCells, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨i, hi, j, hj, hp⟩ := hp
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    all_goals simp [pickA, pickB, mmCell, Process2.procWins,
      Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at hv ⊢
    all_goals simp_all

theorem g20_pickA_procWins (N W i j : Nat) : (pickA N W i j).procWins = [] := rfl
theorem g20_pickB_procWins (N W i j : Nat) : (pickB N W i j).procWins = [] := rfl
theorem g20_cell_procWin {N W AccW i j : Nat} {v : DrvWin} (hv : v ∈ (mmCell N W AccW i j).procWins) :
    v = ("C", some ((i * N + j) * AccW, AccW)) := by
  simpa [mmCell, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins] using hv

/-- The controller writes none of the cells' signal. -/
theorem g20_ctrl_procWin_name {N W : Nat} {v : DrvWin} (hv : v ∈ (mmCtrl N W).procWins) :
    v.1 ∈ ["busy", "done", "k", "a_mem", "b_mem"] := by
  simp [mmCtrl, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

/-- Two different cells write disjoint windows of `C`. -/
theorem g20_cell_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ a ∈ (mmCell N W AccW i j).procWins, ∀ b ∈ (mmCell N W AccW i' j').procWins,
      a.overlaps b = false := by
  intro a ha b hb
  rw [g20_cell_procWin ha, g20_cell_procWin hb]
  have hs : (i * N + j) * AccW + AccW ≤ (i' * N + j') * AccW := by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h)
    rwa [Nat.succ_mul] at this
  simp only [DrvWin.overlaps, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  right
  omega

/-- The three processes of core `(i, j)` against those of a later core `(i', j')`. -/
theorem g20_core_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ p ∈ [pickA N W i j, pickB N W i j, mmCell N W AccW i j],
    ∀ q ∈ [pickA N W i' j', pickB N W i' j', mmCell N W AccW i' j'],
    ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false := by
  intro p hp q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals first
    | exact g20_cell_disj h
    | (intro a ha b hb; simp [g20_pickA_procWins, g20_pickB_procWins] at ha hb)

theorem mm_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames
      (mmCtrl N W :: mmCells N W AccW) = true := by
  have hdecl : design.pdesign.declNames = ["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_mem", "b_mem", "a_pick", "b_pick"] := rfl
  have hinp : design.pdesign.inputNames = ["clk", "rst", "start", "A", "B"] := rfl
  have sep : ∀ i j i' j', i * N + j < i' * N + j' →
      (i * N + j) * W + W ≤ (i' * N + j') * W := by
    intro i j i' j' hidx
    have hle := Nat.mul_le_mul_right W (Nat.succ_le_of_lt hidx)
    simpa [Nat.add_mul] using hle
  rw [hdecl, hinp]
  apply g20_driversOk_of_procDisj
  · rw [g20_driverWins]
    refine pairwise_flatMap_range (fun i _ => ?_) ?_
    · refine pairwise_flatMap_range (fun j _ => ?_) ?_
      · simp [DrvWin.overlaps]
      · intro j j' hj hj'N a ha b hb
        simp at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        all_goals have hs := sep i j i j' (by omega)
        all_goals simp [DrvWin.overlaps, Nat.not_lt_of_ge hs]
    · intro i i' hi i'N a ha b hb
      simp only [List.mem_flatMap, List.mem_range] at ha hb
      obtain ⟨j, hj, ha⟩ := ha
      obtain ⟨j', hj', hb⟩ := hb
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      all_goals have hrow := rowMajor_le (K := N) hi
      all_goals have hs := sep i j i' j' (by omega)
      all_goals simp [DrvWin.overlaps, Nat.not_lt_of_ge hs]
  · rw [g20_driverWins]
    intro w hw
    simp at hw
    rcases hw with ⟨i, hi, j, hj, rfl | rfl⟩
    · constructor
      · simp
      · intro v hv
        simp only [List.mem_flatMap] at hv
        obtain ⟨p, hp, hv⟩ := hv
        have hn := g20_procWin_name (by simpa [mmCells] using hp) hv
        simp only [List.mem_cons, List.mem_singleton] at hn
        rcases hn with h | h | h | h | h | h
        all_goals try intro hwb
        all_goals simp_all [DrvWin.overlaps]
    · constructor
      · simp
      · intro v hv
        simp only [List.mem_flatMap] at hv
        obtain ⟨p, hp, hv⟩ := hv
        have hn := g20_procWin_name (by simpa [mmCells] using hp) hv
        simp only [List.mem_cons, List.mem_singleton] at hn
        rcases hn with h | h | h | h | h | h
        all_goals try intro hwb
        all_goals simp_all [DrvWin.overlaps]
  · -- hin: no procedural process writes an input port
    intro n hn
    obtain ⟨p, hp, hn⟩ := List.mem_flatMap.mp hn
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
    have hname := g20_procWin_name hp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
    rcases hname with h | h | h | h | h | h <;> simp [h]
  · -- hdisj: the procedural windows of two different processes never share a bit
    rw [List.pairwise_cons]
    constructor
    · -- the controller against every core process
      intro q hq a ha b hb
      have hna := g20_ctrl_procWin_name ha
      simp only [mmCells, List.mem_flatMap, List.mem_range] at hq
      obtain ⟨i, _, j, _, hq⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · simp [g20_pickA_procWins] at hb
      · simp [g20_pickB_procWins] at hb
      · rw [g20_cell_procWin hb]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hna
        rcases hna with h | h | h | h | h <;> simp [DrvWin.overlaps, h]
    · -- the cores against each other, row-major
      unfold mmCells
      refine pairwise_flatMap_range (fun i _ => ?_) ?_
      · refine pairwise_flatMap_range (fun j _ => ?_) ?_
        · simp [List.pairwise_cons, g20_pickA_procWins, g20_pickB_procWins]
        · intro j j' hj _ p hp q hq
          exact g20_core_disj (by omega) p hp q hq
      · intro i i' hi _ p hp q hq
        obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
        obtain ⟨j', hj', hq⟩ := List.mem_flatMap.mp hq
        have hrow := rowMajor_le (K := N) hi
        have hjN := List.mem_range.mp hj
        exact g20_core_disj (by omega) p hp q hq

theorem mm_sem_eq (N W AccW) (hN:1≤N) (hW:1≤W) (hA:1≤AccW) (hR32:Rng32 N W AccW) : design.sem N W AccW = mmD N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror
    (mmG.instantiate N W AccW hN hW hA (by omega) hR32.2.1 hR32.2.2 hR32.1)
    (mmG_D N W AccW) (mm_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by simp [mmD, mmCtrl, mmCells, pickA, pickB, mmCell, SvGolf.Cycle.notComb]))

/-! Semantic arithmetic for the output-core timetable.  The controller captures
the operand banks once, and the generated pick families expose A[i,k] and
B[k,j] to every stationary cell at busy step k. -/

def psum20 (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def accC20 (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r =>
    BitVec.ofInt AccW (psum20 N W A B t (r / N) (r % N)))

theorem psum20_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum20 N W A B (t + 1) i j =
      psum20 N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum20, List.range_succ, List.foldl_append]

theorem product20_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) :
    Tasks.Matmul.product N W AccW a b =
      packBV AccW (N * N) fun r =>
        BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem accC20_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC20 N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product20_eq]
  rfl

def MS20 (ck r s a b dn c k bz am bm ap bp : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn),
   ("C", c), ("k", k), ("busy", bz), ("a_mem", am), ("b_mem", bm),
   ("a_pick", ap), ("b_pick", bp)]

/-! ## g20 lead handover 02: the clock cycle (HELP g20 comb-cycle)

The pick assignments are a generated family of continuous assignments.  They write
pairwise disjoint windows of `a_pick` / `b_pick` and read only `k`, `a_mem`, `b_mem`, so
a settle pass in ANY schedule order ends in the same state (`g20_pass_settled`), a second
pass changes nothing, and the settle ends there (`g20_settle`).  `mm20_cycle` is the cycle. -/

/-- The declared inputs take the stimulus entry's values. -/
theorem apply20 (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz am bm ap bp : LVec) :
    applyInputs2 (mmD N W AccW) e (MS20 ck r s a b dn c k bz am bm ap bp) =
      MS20 (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz am bm ap bp := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmD, mmDecls, MS20, appIn, h1, h2, h3, h4, h5, SvState.set]

/-! ### The pick family, one process at a time -/

/-- What `pickA N W i j` drives into its window: `a_mem >> (i*N*W + k*W)`, `W` bits. -/
def pickAV (N W i : Nat) (k am : LVec) : LVec :=
  ((am.shr ((((LVec.ofInt 32 (i : Int)).mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int))).add
    (k.mul (LVec.ofInt 32 (W : Int))))).resizeU W).resizeU W

/-- What `pickB N W i j` drives into its window: `b_mem >> (k*N*W + j*W)`, `W` bits. -/
def pickBV (N W j : Nat) (k bm : LVec) : LVec :=
  ((bm.shr (((k.mul (LVec.ofInt 32 (N : Int))).mul (LVec.ofInt 32 (W : Int))).add
    ((LVec.ofInt 32 (j : Int)).mul (LVec.ofInt 32 (W : Int))))).resizeU W).resizeU W

theorem pickAV_known {N W i t : Nat} {A : BitVec (N * N * W)}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hshift : (i * N + t) * W < 2 ^ 32) :
    pickAV N W i (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A) =
      LVec.ofBitVec (BitVec.extractLsb' ((i * N + t) * W) W A) := by
  simp [pickAV, LVec.ofInt_eq_ofBitVec, LVec.shr_ofBitVec, BitVec.setWidth_eq]
  have heq : i * N * W + t * W = (i * N + t) * W := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [Nat.mod_eq_of_lt (by omega : i * N * W + t * W < 2 ^ 32), heq]
  have hw : W ≤ N * N * W := by
    have hnn : 1 ≤ N * N := Nat.mul_le_mul hN hN
    simpa using Nat.mul_le_mul_right W hnn
  rw [BitVec.setWidth_eq_extractLsb' (x := A >>> ((i * N + t) * W)) hw]
  rw [Lib.extractLsb'_ushiftRight]
  simp

theorem pickBV_known {N W j t : Nat} {A : BitVec (N * N * W)}
    (hN : 1 ≤ N) (hW : 1 ≤ W) (hshift : (t * N + j) * W < 2 ^ 32) :
    pickBV N W j (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A) =
      LVec.ofBitVec (BitVec.extractLsb' ((t * N + j) * W) W A) := by
  simp [pickBV, LVec.ofInt_eq_ofBitVec, LVec.shr_ofBitVec, BitVec.setWidth_eq]
  have heq : t * N * W + j * W = (t * N + j) * W := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [Nat.mod_eq_of_lt (by omega : t * N * W + j * W < 2 ^ 32), heq]
  have hw : W ≤ N * N * W := by
    have hnn : 1 ≤ N * N := Nat.mul_le_mul hN hN
    simpa using Nat.mul_le_mul_right W hnn
  rw [BitVec.setWidth_eq_extractLsb' (x := A >>> ((t * N + j) * W)) hw]
  rw [Lib.extractLsb'_ushiftRight]
  simp

theorem width_pickAV (N W i : Nat) (k am : LVec) : (pickAV N W i k am).width = W := by simp [pickAV]
theorem width_pickBV (N W j : Nat) (k bm : LVec) : (pickBV N W j k bm).width = W := by simp [pickBV]

theorem pickA20_run (N W i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm ap bp : LVec) :
    runCombProcess2 F (MS20 ck r s a b dn c k bz am bm ap bp) (pickA N W i j) =
      .ok (MS20 ck r s a b dn c k bz am bm (ap.insertAt ((i * N + j) * W) (pickAV N W i k am)) bp) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pickA, c32n, runCombProcess2, evalExpr2, resolveLhs2, readSignal, MS20, SvState.lookup,
    SvState.set, evalBinOp, pickAV]

theorem pickB20_run (N W i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm ap bp : LVec) :
    runCombProcess2 F (MS20 ck r s a b dn c k bz am bm ap bp) (pickB N W i j) =
      .ok (MS20 ck r s a b dn c k bz am bm ap (bp.insertAt ((i * N + j) * W) (pickBV N W j k bm))) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  simp [pickB, c32n, runCombProcess2, evalExpr2, resolveLhs2, readSignal, MS20, SvState.lookup,
    SvState.set, evalBinOp, pickBV]

/-- The flops do nothing in a settle pass. -/
theorem ctrl20_comb (N W F : Nat) (st : SvState) : runCombProcess2 F st (mmCtrl N W) = .ok st := rfl
theorem cell20_comb (N W AccW i j F : Nat) (st : SvState) :
    runCombProcess2 F st (mmCell N W AccW i j) = .ok st := rfl

/-- Every process of the design is the controller or one of the three processes of a core. -/
theorem g20_proc_cases {N W AccW idx : Nat} {p : Process2}
    (hp : (mmD N W AccW).processes[idx]? = some p) :
    p = mmCtrl N W ∨ ∃ i j, i < N ∧ j < N ∧
      (p = pickA N W i j ∨ p = pickB N W i j ∨ p = mmCell N W AccW i j) := by
  have hm : p ∈ mmCtrl N W :: mmCells N W AccW :=
    List.mem_of_getElem? (by simpa [mmD] using hp : (mmCtrl N W :: mmCells N W AccW)[idx]? = some p)
  simp only [List.mem_cons, mmCells, List.mem_flatMap, List.mem_range, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | ⟨i, hi, j, hj, h⟩
  · exact .inl rfl
  · exact .inr ⟨i, j, hi, hj, h⟩

/-- Every pick of a core `(i, j)` in range is a comb process of the design. -/
theorem g20_pick_idx {N W AccW i j : Nat} (hi : i < N) (hj : j < N) {p : Process2}
    (hp : p = pickA N W i j ∨ p = pickB N W i j) :
    ∃ idx, idx ∈ (mmD N W AccW).combIndices ∧ (mmD N W AccW).processes[idx]? = some p := by
  have hm : p ∈ mmCtrl N W :: mmCells N W AccW := by
    simp only [List.mem_cons, mmCells, List.mem_flatMap, List.mem_range, List.not_mem_nil, or_false]
    exact .inr ⟨i, hi, j, hj, by rcases hp with h | h <;> simp [h]⟩
  obtain ⟨idx, hget⟩ := List.mem_iff_getElem?.mp hm
  have hsome : (mmD N W AccW).processes[idx]? = some p := by simpa [mmD] using hget
  refine ⟨idx, ?_, hsome⟩
  simp only [Design2.combIndices, List.mem_filter, List.mem_range, hsome]
  exact ⟨(Array.getElem?_eq_some_iff.mp hsome).1, by rcases hp with rfl | rfl <;> rfl⟩

/-- The low end of the window a continuous assignment drives (to tell two picks apart). -/
def procLo20 : Process2 → Nat
  | .assign (.slice _ lo _) _ => lo
  | _ => 0

/-! ### Row-major arithmetic and windows -/

theorem g20_rm_lt {N i j : Nat} (hi : i < N) (hj : j < N) : i * N + j < N * N := by
  have := Nat.mul_le_mul_right N (show i + 1 ≤ N by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem g20_rm_inj {N i j i' j' : Nat} (hj : j < N) (hj' : j' < N) (h : i * N + j = i' * N + j') :
    i = i' ∧ j = j' := by
  rcases Nat.lt_trichotomy i i' with hlt | rfl | hlt
  · have := rowMajor_le (K := N) hlt; omega
  · omega
  · have := rowMajor_le (K := N) hlt; omega

theorem g20_rm_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem g20_rm_mod {N i j : Nat} (hj : j < N) : (i * N + j) % N = j := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- One write of window `r0`, read at window `r`: the written value at the same window, the old
content at another. -/
theorem g20_step_extract {W n r0 r : Nat} {x p g : LVec} (hx : x.width = n * W) (hp : p.width = W)
    (hr0 : r0 < n) (h : (r0 = r ∧ p = g) ∨ (r0 ≠ r ∧ x.extract (r * W) W = g)) :
    (x.insertAt (r0 * W) p).extract (r * W) W = g := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hne, hx'⟩
  · have := rowMajor_le (K := W) hr0
    exact LVec.extract_insertAt_self hp (by omega)
  · rw [LVec.extract_insertAt_of_disjoint]
    · exact hx'
    · rw [hp]
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact .inr (rowMajor_le h)
      · exact .inl (rowMajor_le h)

/-- A vector is determined by its width and its `W`-bit windows. -/
theorem g20_chunks {W n : Nat} {u v : LVec} (hu : u.width = n * W) (hv : v.width = n * W)
    (h : ∀ r, r < n → u.extract (r * W) W = v.extract (r * W) W) : u = v := by
  refine LVec.eq_of_extract_one (hu.trans hv.symm) fun i hi => ?_
  rw [hu] at hi
  have hW : 0 < W := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hi
  have hr : i / W < n := (Nat.div_lt_iff_lt_mul hW).mpr hi
  have hd : i / W * W + i % W = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i W
  have hm : i % W + 1 ≤ W := Nat.mod_lt i hW
  have h1 := congrArg (fun x : LVec => x.extract (i % W) 1) (h _ hr)
  simp only [LVec.extract_extract _ hm, hd] at h1
  exact h1

/-! ### The settled pick vectors -/

/-- `a_pick` after the settle: window `(i, j)` holds `pickAV N W i k am`. -/
def apSet (N W : Nat) (k am : LVec) : LVec :=
  LVec.insertEntries W (fun r => pickAV N W (r / N) k am) (N * N) (LVec.xVec (N * N * W))

/-- `b_pick` after the settle: window `(i, j)` holds `pickBV N W j k bm`. -/
def bpSet (N W : Nat) (k bm : LVec) : LVec :=
  LVec.insertEntries W (fun r => pickBV N W (r % N) k bm) (N * N) (LVec.xVec (N * N * W))

theorem width_apSet (N W : Nat) (k am : LVec) : (apSet N W k am).width = N * N * W := by simp [apSet]
theorem width_bpSet (N W : Nat) (k bm : LVec) : (bpSet N W k bm).width = N * N * W := by simp [bpSet]

/-- **Window `(i, j)` of the settled `a_pick`.** -/
theorem apSet_extract {N W i j : Nat} (hi : i < N) (hj : j < N) (k am : LVec) :
    (apSet N W k am).extract ((i * N + j) * W) W = pickAV N W i k am := by
  have h := LVec.extract_insertEntries (E := W) (g := fun r => pickAV N W (r / N) k am)
    (fun _ => width_pickAV ..) (LVec.xVec (N * N * W)) (N * N) (by simp) (i * N + j) (g20_rm_lt hi hj)
  simpa [apSet, g20_rm_div hj] using h

/-- **Window `(i, j)` of the settled `b_pick`.** -/
theorem bpSet_extract {N W i j : Nat} (hi : i < N) (hj : j < N) (k bm : LVec) :
    (bpSet N W k bm).extract ((i * N + j) * W) W = pickBV N W j k bm := by
  have h := LVec.extract_insertEntries (E := W) (g := fun r => pickBV N W (r % N) k bm)
    (fun _ => width_pickBV ..) (LVec.xVec (N * N * W)) (N * N) (by simp) (i * N + j) (g20_rm_lt hi hj)
  simpa [bpSet, g20_rm_mod hj] using h

theorem eq_apSet {N W : Nat} (hN : 1 ≤ N) {k am ap : LVec} (hw : ap.width = N * N * W)
    (h : ∀ i j, i < N → j < N → ap.extract ((i * N + j) * W) W = pickAV N W i k am) :
    ap = apSet N W k am := by
  refine g20_chunks hw (width_apSet ..) fun r hr => ?_
  have hi : r / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have hj : r % N < N := Nat.mod_lt _ (by omega)
  have hr' : r / N * N + r % N = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r N
  have h1 := h _ _ hi hj
  have h2 := apSet_extract (W := W) hi hj k am
  rw [hr'] at h1 h2
  rw [h1, h2]

theorem eq_bpSet {N W : Nat} (hN : 1 ≤ N) {k bm bp : LVec} (hw : bp.width = N * N * W)
    (h : ∀ i j, i < N → j < N → bp.extract ((i * N + j) * W) W = pickBV N W j k bm) :
    bp = bpSet N W k bm := by
  refine g20_chunks hw (width_bpSet ..) fun r hr => ?_
  have hi : r / N < N := (Nat.div_lt_iff_lt_mul (by omega)).mpr hr
  have hj : r % N < N := Nat.mod_lt _ (by omega)
  have hr' : r / N * N + r % N = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r N
  have h1 := h _ _ hi hj
  have h2 := bpSet_extract (W := W) hi hj k bm
  rw [hr'] at h1 h2
  rw [h1, h2]

/-! ### A settle pass in any order -/

theorem g20_pass_cons {N W AccW F idx : Nat} {p : Process2} {st st' : SvState} {rest : List Nat}
    (hp : (mmD N W AccW).processes[idx]? = some p) (hr : runCombProcess2 F st p = .ok st') :
    combPass2 (mmD N W AccW) F st (idx :: rest) = combPass2 (mmD N W AccW) F st' rest := by
  simp [combPass2, hp, hr]

/-- A hit in `idx :: rest` is a hit at `idx` or in `rest`. -/
theorem g20_hit_cons {N W AccW idx : Nat} {rest : List Nat} {q : Process2} {P : Prop}
    (h : (∃ x ∈ idx :: rest, (mmD N W AccW).processes[x]? = some q) ∨ P) :
    (mmD N W AccW).processes[idx]? = some q ∨
      ((∃ x ∈ rest, (mmD N W AccW).processes[x]? = some q) ∨ P) := by
  rcases h with ⟨x, hx, hq⟩ | h
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl hq
    · exact .inr (.inl ⟨x, hx, hq⟩)
  · exact .inr (.inr h)

/-- **A pass over any list of process indices** keeps the shape and the widths, and a window of
`a_pick` (`b_pick`) holds its pick's value afterwards when its pick is in the list or the window held
that value before: a pick writes only its own window and reads neither `a_pick` nor `b_pick`. -/
theorem g20_pass (N W AccW F : Nat) (hW : 1 ≤ W) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm : LVec) :
    ∀ (is : List Nat) (ap bp : LVec), ap.width = N * N * W → bp.width = N * N * W →
      ∃ ap' bp', combPass2 (mmD N W AccW) F (MS20 ck r s a b dn c k bz am bm ap bp) is =
          .ok (MS20 ck r s a b dn c k bz am bm ap' bp') ∧
        ap'.width = N * N * W ∧ bp'.width = N * N * W ∧
        (∀ i j, i < N → j < N →
          ((∃ x ∈ is, (mmD N W AccW).processes[x]? = some (pickA N W i j)) ∨
            ap.extract ((i * N + j) * W) W = pickAV N W i k am) →
          ap'.extract ((i * N + j) * W) W = pickAV N W i k am) ∧
        (∀ i j, i < N → j < N →
          ((∃ x ∈ is, (mmD N W AccW).processes[x]? = some (pickB N W i j)) ∨
            bp.extract ((i * N + j) * W) W = pickBV N W j k bm) →
          bp'.extract ((i * N + j) * W) W = pickBV N W j k bm) := by
  intro is
  induction is with
  | nil =>
      intro ap bp hap hbp
      exact ⟨ap, bp, rfl, hap, hbp, fun _ _ _ _ h => h.resolve_left (by simp),
        fun _ _ _ _ h => h.resolve_left (by simp)⟩
  | cons idx rest ih =>
      intro ap bp hap hbp
      cases hp : (mmD N W AccW).processes[idx]? with
      | none =>
          obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ := ih ap bp hap hbp
          refine ⟨ap', bp', by rw [combPass2_cons_none hp]; exact hrun, hw1, hw2,
            fun i j hi hj h => hA i j hi hj ?_, fun i j hi hj h => hB i j hi hj ?_⟩
          · rcases g20_hit_cons h with h | h
            · rw [hp] at h; cases h
            · exact h
          · rcases g20_hit_cons h with h | h
            · rw [hp] at h; cases h
            · exact h
      | some p =>
          rcases g20_proc_cases hp with rfl | ⟨i0, j0, hi0, hj0, rfl | rfl | rfl⟩
          · -- the controller
            obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ := ih ap bp hap hbp
            refine ⟨ap', bp', by rw [g20_pass_cons hp (ctrl20_comb ..)]; exact hrun, hw1, hw2,
              fun i j hi hj h => hA i j hi hj ?_, fun i j hi hj h => hB i j hi hj ?_⟩
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [mmCtrl, pickA] at h
              · exact h
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [mmCtrl, pickB] at h
              · exact h
          · -- the A pick of core (i0, j0): writes its window of `a_pick`
            obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ :=
              ih (ap.insertAt ((i0 * N + j0) * W) (pickAV N W i0 k am)) bp
                (by rw [LVec.width_insertAt]; exact hap) hbp
            refine ⟨ap', bp', by rw [g20_pass_cons hp (pickA20_run N W i0 j0 F hF ..)]; exact hrun,
              hw1, hw2, fun i j hi hj h => hA i j hi hj ?_, fun i j hi hj h => hB i j hi hj ?_⟩
            · by_cases hr : i0 * N + j0 = i * N + j
              · obtain ⟨rfl, rfl⟩ := g20_rm_inj hj0 hj hr
                exact .inr (g20_step_extract hap (width_pickAV ..) (g20_rm_lt hi hj) (.inl ⟨rfl, rfl⟩))
              · rcases g20_hit_cons h with h | h | h
                · rw [hp] at h
                  exact absurd (Nat.eq_of_mul_eq_mul_right hW
                    (congrArg procLo20 (Option.some.inj h))) hr
                · exact .inl h
                · exact .inr (g20_step_extract hap (width_pickAV ..) (g20_rm_lt hi0 hj0) (.inr ⟨hr, h⟩))
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [pickA, pickB] at h
              · exact h
          · -- the B pick of core (i0, j0): writes its window of `b_pick`
            obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ :=
              ih ap (bp.insertAt ((i0 * N + j0) * W) (pickBV N W j0 k bm)) hap
                (by rw [LVec.width_insertAt]; exact hbp)
            refine ⟨ap', bp', by rw [g20_pass_cons hp (pickB20_run N W i0 j0 F hF ..)]; exact hrun,
              hw1, hw2, fun i j hi hj h => hA i j hi hj ?_, fun i j hi hj h => hB i j hi hj ?_⟩
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [pickA, pickB] at h
              · exact h
            · by_cases hr : i0 * N + j0 = i * N + j
              · obtain ⟨rfl, rfl⟩ := g20_rm_inj hj0 hj hr
                exact .inr (g20_step_extract hbp (width_pickBV ..) (g20_rm_lt hi hj) (.inl ⟨rfl, rfl⟩))
              · rcases g20_hit_cons h with h | h | h
                · rw [hp] at h
                  exact absurd (Nat.eq_of_mul_eq_mul_right hW
                    (congrArg procLo20 (Option.some.inj h))) hr
                · exact .inl h
                · exact .inr (g20_step_extract hbp (width_pickBV ..) (g20_rm_lt hi0 hj0) (.inr ⟨hr, h⟩))
          · -- the cell flop
            obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ := ih ap bp hap hbp
            refine ⟨ap', bp', by rw [g20_pass_cons hp (cell20_comb ..)]; exact hrun, hw1, hw2,
              fun i j hi hj h => hA i j hi hj ?_, fun i j hi hj h => hB i j hi hj ?_⟩
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [mmCell, pickA] at h
              · exact h
            · rcases g20_hit_cons h with h | h
              · rw [hp] at h; simp [mmCell, pickB] at h
              · exact h

/-- **One settle pass, in every schedule order**, ends with the settled pick vectors. -/
theorem g20_pass_settled (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hF : 30 ≤ F)
    (σ : ScheduleOracle) (k0 : Nat) (ck r s a b dn c k bz am bm ap bp : LVec)
    (hap : ap.width = N * N * W) (hbp : bp.width = N * N * W) :
    combPass2 (mmD N W AccW) F (MS20 ck r s a b dn c k bz am bm ap bp)
        (σ.choose k0 (mmD N W AccW).combIndices) =
      .ok (MS20 ck r s a b dn c k bz am bm (apSet N W k am) (bpSet N W k bm)) := by
  obtain ⟨ap', bp', hrun, hw1, hw2, hA, hB⟩ :=
    g20_pass N W AccW F hW hF ck r s a b dn c k bz am bm
      (σ.choose k0 (mmD N W AccW).combIndices) ap bp hap hbp
  have hmem : ∀ {p : Process2} {i j : Nat}, i < N → j < N → (p = pickA N W i j ∨ p = pickB N W i j) →
      ∃ x ∈ σ.choose k0 (mmD N W AccW).combIndices, (mmD N W AccW).processes[x]? = some p := by
    intro p i j hi hj hp
    obtain ⟨idx, hc, hs⟩ := g20_pick_idx (AccW := AccW) hi hj hp
    exact ⟨idx, (σ.choose_perm k0 _).mem_iff.mpr hc, hs⟩
  rw [hrun, eq_apSet hN hw1 fun i j hi hj => hA i j hi hj (.inl (hmem hi hj (.inl rfl))),
    eq_bpSet hN hw2 fun i j hi hj => hB i j hi hj (.inl (hmem hi hj (.inr rfl)))]

/-- **The comb settle of the pick family**, under every schedule: one pass reaches the settled
vectors, a second pass (if the first changed anything) confirms them. -/
theorem g20_settle (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hF : 32 ≤ F)
    (σ : ScheduleOracle) (k0 : Nat) (ck r s a b dn c k bz am bm ap bp : LVec)
    (hap : ap.width = N * N * W) (hbp : bp.width = N * N * W) :
    ∃ k', combSettle2 (mmD N W AccW) σ F (MS20 ck r s a b dn c k bz am bm ap bp) k0 =
      .ok (MS20 ck r s a b dn c k bz am bm (apSet N W k am) (bpSet N W k bm), k') := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 + 1 + 1 := ⟨F - 32, by omega⟩
  rw [combSettle2.eq_2, g20_pass_settled N W AccW (f + 30 + 1) hN hW (by omega) σ k0
    ck r s a b dn c k bz am bm ap bp hap hbp]
  simp only [Res.ok_bind]
  by_cases hb : (MS20 ck r s a b dn c k bz am bm (apSet N W k am) (bpSet N W k bm) ==
      MS20 ck r s a b dn c k bz am bm ap bp) = true
  · rw [ite_eq_left hb]; exact ⟨_, rfl⟩
  · rw [ite_eq_right hb, combSettle2.eq_2, g20_pass_settled N W AccW (f + 30) hN hW (by omega) σ (k0 + 1)
      ck r s a b dn c k bz am bm _ _ (width_apSet ..) (width_bpSet ..)]
    simp only [Res.ok_bind]
    rw [beq_self_eq_true, ite_eq_left rfl]
    exact ⟨_, rfl⟩

/-! ### The clock edge -/

def ctrlQ20 (N : Nat) (r s a b dn k bz am bm : LVec) : NbaQueue2 :=
  if r.condTrue then
    [("busy", 0, (⟨#[.l0]⟩ : LVec).resizeU bz.width), ("done", 0, (⟨#[.l0]⟩ : LVec).resizeU dn.width),
      ("k", 0, (LVec.ofBitVec 0#32).resizeU k.width)]
  else if s.condTrue then
    [("busy", 0, (⟨#[.l1]⟩ : LVec).resizeU bz.width), ("done", 0, (⟨#[.l0]⟩ : LVec).resizeU dn.width),
      ("k", 0, (LVec.ofBitVec 0#32).resizeU k.width), ("a_mem", 0, a.resizeU am.width),
      ("b_mem", 0, b.resizeU bm.width)]
  else if bz.condTrue then
    if (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue then
      [("k", 0, (k.add (LVec.ofBitVec 1#32)).resizeU k.width),
        ("busy", 0, (⟨#[.l0]⟩ : LVec).resizeU bz.width), ("done", 0, (⟨#[.l1]⟩ : LVec).resizeU dn.width)]
    else [("k", 0, (k.add (LVec.ofBitVec 1#32)).resizeU k.width)]
  else []

theorem ctrl20_run (N W F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm ap bp : LVec) :
    runEdgeProcess2 F (MS20 ck r s a b dn c k bz am bm ap bp) [] (mmCtrl N W) =
      .ok (MS20 ck r s a b dn c k bz am bm ap bp, ctrlQ20 N r s a b dn k bz am bm) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ctrlQ20
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [mmCtrl, nb, c32, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal, MS20,
      SvState.lookup, evalBinOp, h1, h2, h3, h4]

/-- The cell's reset condition `rst || start` (4-state logical or), as the branch taken. -/
def rstOr20 (r s : LVec) : Bool :=
  (LVec.ofLogic (if r.condTrue = true ∨ s.condTrue = true then Logic.l1
    else if r.isKnownZero = true ∧ s.isKnownZero = true then Logic.l0 else Logic.lx)).condTrue

/-- The value cell `(i, j)` writes on a busy edge: `C[i,j] + sext(a_pick[i,j]) * sext(b_pick[i,j])`. -/
def cellV20 (N W AccW i j : Nat) (c ap bp : LVec) : LVec :=
  ((((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
    (((LVec.replVec AccW (ap.extract ((i * N + j) * W + W - 1) 1)).concat
        (ap.extract ((i * N + j) * W) W)).mul
      ((LVec.replVec AccW (bp.extract ((i * N + j) * W + W - 1) 1)).concat
        (bp.extract ((i * N + j) * W) W)))).resizeU AccW).resizeU AccW

def cellQ20 (N W AccW : Nat) (r s bz c ap bp : LVec) (i j : Nat) : NbaQueue2 :=
  if rstOr20 r s then [("C", (i * N + j) * AccW, LVec.ofBitVec 0#AccW)]
  else if bz.condTrue then [("C", (i * N + j) * AccW, cellV20 N W AccW i j c ap bp)] else []

theorem cell20_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm ap bp : LVec) :
    runEdgeProcess2 F (MS20 ck r s a b dn c k bz am bm ap bp) [] (mmCell N W AccW i j) =
      .ok (MS20 ck r s a b dn c k bz am bm ap bp, cellQ20 N W AccW r s bz c ap bp i j) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  have hx : (LVec.ofLogic Logic.lx).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  simp only [cellQ20, rstOr20, cellV20]
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : r.isKnownZero = true <;> by_cases h4 : s.isKnownZero = true <;>
    by_cases h5 : bz.condTrue = true <;>
    simp [mmCell, sext, runEdgeProcess2, execStmt2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, MS20, SvState.lookup, evalBinOp, h1, h2, h3, h4, h5, hx]

theorem ctrlQ20_names (N : Nat) (r s a b dn k bz am bm : LVec) :
    ∀ u ∈ ctrlQ20 N r s a b dn k bz am bm, u.1 ∈ ["busy", "done", "k", "a_mem", "b_mem", "C"] := by
  unfold ctrlQ20
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [h1, h2, h3, h4]

theorem cellQ20_names (N W AccW : Nat) (r s bz c ap bp : LVec) (i j : Nat) :
    ∀ u ∈ cellQ20 N W AccW r s bz c ap bp i j, u.1 ∈ ["busy", "done", "k", "a_mem", "b_mem", "C"] := by
  unfold cellQ20
  by_cases h1 : rstOr20 r s = true <;> by_cases h2 : bz.condTrue = true <;> simp [h1, h2]

/-- The queue of one clock edge on a settled state: the controller's writes, then the cells'. -/
def mm20Q (N W AccW : Nat) (r s a b dn c k bz am bm ap bp : LVec) : NbaQueue2 :=
  ctrlQ20 N r s a b dn k bz am bm ++
    (List.range N).flatMap fun i => (List.range N).flatMap fun j => cellQ20 N W AccW r s bz c ap bp i j

theorem mm20Q_names (N W AccW : Nat) (r s a b dn c k bz am bm ap bp : LVec) :
    ∀ u ∈ mm20Q N W AccW r s a b dn c k bz am bm ap bp,
      u.1 ∈ ["busy", "done", "k", "a_mem", "b_mem", "C"] := by
  intro u hu
  simp only [mm20Q, List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with hu | ⟨i, -, j, -, hu⟩
  · exact ctrlQ20_names _ _ _ _ _ _ _ _ _ _ u hu
  · exact cellQ20_names _ _ _ _ _ _ _ _ _ _ _ u hu

/-- The edge queue of the whole design on a state of the shape: the picks issue nothing. -/
theorem g20_edgeQ (N W AccW F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz am bm ap bp : LVec) :
    (mmD N W AccW).processes.toList.flatMap
        (SvGolf.Cycle.runQ F (MS20 ck r s a b dn c k bz am bm ap bp)) =
      mm20Q N W AccW r s a b dn c k bz am bm ap bp := by
  have hA : ∀ i j, SvGolf.Cycle.runQ F (MS20 ck r s a b dn c k bz am bm ap bp) (pickA N W i j) = [] :=
    fun _ _ => rfl
  have hB : ∀ i j, SvGolf.Cycle.runQ F (MS20 ck r s a b dn c k bz am bm ap bp) (pickB N W i j) = [] :=
    fun _ _ => rfl
  simp only [mmD, mmCells, mm20Q, List.flatMap_cons, List.flatMap_nil, List.flatMap_assoc, hA, hB,
    SvGolf.Cycle.runQ_of (ctrl20_run N W F hF ck r s a b dn c k bz am bm ap bp),
    SvGolf.Cycle.runQ_of (cell20_run N W AccW _ _ F hF ck r s a b dn c k bz am bm ap bp),
    List.nil_append, List.append_nil]

/-- The commit of a queue that names only registers, on the shape. -/
theorem commit20 {ck r s a b dn c k bz am bm ap bp : LVec} {Q : NbaQueue2}
    (hQ : ∀ u ∈ Q, u.1 ∈ ["busy", "done", "k", "a_mem", "b_mem", "C"]) :
    commitNba2 (MS20 ck r s a b dn c k bz am bm ap bp) Q =
      MS20 ck r s a b (nbaFold "done" Q dn) (nbaFold "C" Q c) (nbaFold "k" Q k) (nbaFold "busy" Q bz)
        (nbaFold "a_mem" Q am) (nbaFold "b_mem" Q bm) ap bp := by
  rw [commitNba2_eq_map_of_names (by simp [MS20]) hQ]
  simp [MS20]

/-- **The cell's value on a settled state**, in the pick values themselves: the two windows the
cell reads are `pickAV N W i k am` and `pickBV N W j k bm` (and their top bits). -/
theorem cellV20_settled {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) (c k am bm : LVec) :
    cellV20 N W AccW i j c (apSet N W k am) (bpSet N W k bm) =
      ((((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        (((LVec.replVec AccW ((pickAV N W i k am).extract (W - 1) 1)).concat (pickAV N W i k am)).mul
          ((LVec.replVec AccW ((pickBV N W j k bm).extract (W - 1) 1)).concat
            (pickBV N W j k bm)))).resizeU AccW).resizeU AccW := by
  have ha := apSet_extract (W := W) hi hj k am
  have hb := bpSet_extract (W := W) hi hj k bm
  have hsa := LVec.extract_extract (apSet N W k am) (lo := (i * N + j) * W) (w := W) (lo' := W - 1)
    (w' := 1) (by omega)
  have hsb := LVec.extract_extract (bpSet N W k bm) (lo := (i * N + j) * W) (w := W) (lo' := W - 1)
    (w' := 1) (by omega)
  rw [ha, ← Nat.add_sub_assoc hW] at hsa
  rw [hb, ← Nat.add_sub_assoc hW] at hsb
  rw [cellV20, ha, hb, ← hsa, ← hsb]

/-- The procedural windows of two different processes never share a bit (the fourth bullet of
`mm_driversOk`, as its own statement: the clock edge needs it too). -/
theorem g20_procDisj (N W AccW : Nat) :
    (mmCtrl N W :: mmCells N W AccW).Pairwise
      fun p q => ∀ a ∈ p.procWins, ∀ b ∈ q.procWins, a.overlaps b = false := by
  rw [List.pairwise_cons]
  constructor
  · intro q hq a ha b hb
    have hna := g20_ctrl_procWin_name ha
    simp only [mmCells, List.mem_flatMap, List.mem_range] at hq
    obtain ⟨i, _, j, _, hq⟩ := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · simp [g20_pickA_procWins] at hb
    · simp [g20_pickB_procWins] at hb
    · rw [g20_cell_procWin hb]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hna
      rcases hna with h | h | h | h | h <;> simp [DrvWin.overlaps, h]
  · unfold mmCells
    refine pairwise_flatMap_range (fun i _ => ?_) ?_
    · refine pairwise_flatMap_range (fun j _ => ?_) ?_
      · simp [List.pairwise_cons, g20_pickA_procWins, g20_pickB_procWins]
      · intro j j' hj _ p hp q hq
        exact g20_core_disj (by omega) p hp q hq
    · intro i i' hi _ p hp q hq
      obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨j', hj', hq⟩ := List.mem_flatMap.mp hq
      have hrow := rowMajor_le (K := N) hi
      have hjN := List.mem_range.mp hj
      exact g20_core_disj (by omega) p hp q hq

/-- The state after one clock cycle: the edge's queue is computed on the settled picks of the old
`k`, `a_mem`, `b_mem`; the registers commit; the picks settle again from the new ones. -/
def mm20Next (N W AccW : Nat) (ck r s a b dn c k bz am bm : LVec) : SvState :=
  let Q := mm20Q N W AccW r s a b dn c k bz am bm (apSet N W k am) (bpSet N W k bm)
  MS20 ck r s a b (nbaFold "done" Q dn) (nbaFold "C" Q c) (nbaFold "k" Q k) (nbaFold "busy" Q bz)
    (nbaFold "a_mem" Q am) (nbaFold "b_mem" Q bm)
    (apSet N W (nbaFold "k" Q k) (nbaFold "a_mem" Q am))
    (bpSet N W (nbaFold "k" Q k) (nbaFold "b_mem" Q bm))

/-- **One clock cycle of g20, under every schedule**: inputs applied, the pick family settles, the
controller and the cells commit, the pick family settles again. -/
theorem mm20_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) (σ : ScheduleOracle) (e : SvState)
    (ck r s a b dn c k bz am bm ap bp : LVec) (kk F : Nat) (hF : 32 ≤ F)
    (hap : ap.width = N * N * W) (hbp : bp.width = N * N * W) :
    ∃ kk', cycleStep2 (design.sem N W AccW) σ F e (MS20 ck r s a b dn c k bz am bm ap bp) kk =
      .ok (mm20Next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn c k bz am bm, kk') := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine SvGolf.Cycle.cycleStep2_mixed σ e _ kk
    (S1 := MS20 (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz am bm (apSet N W k am) (bpSet N W k bm)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rw [apply20]
    exact g20_settle N W AccW F hN hW hF σ j _ _ _ _ _ dn c k bz am bm ap bp hap hbp
  · refine SvGolf.Cycle.resetIndices_nil_of (List.all_eq_true.mpr fun p hp => ?_)
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hp
    rw [Array.getElem?_toList] at hidx
    rcases g20_proc_cases hidx with rfl | ⟨i, j, -, -, rfl | rfl | rfl⟩ <;> rfl
  · intro i p hp he
    rcases g20_proc_cases hp with rfl | ⟨i, j, -, -, rfl | rfl | rfl⟩
    · exact ⟨_, _, rfl, rfl⟩
    · cases he
    · cases he
    · exact ⟨_, _, rfl, rfl⟩
  · intro i p hp he
    rcases g20_proc_cases hp with rfl | ⟨i, j, -, -, rfl | rfl | rfl⟩
    · exact ⟨_, ctrl20_run N W F (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    · exact ⟨[], rfl⟩
    · exact ⟨[], rfl⟩
    · exact ⟨_, cell20_run N W AccW i j F (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · exact ffDisjB_of_pairwise (g20_procDisj N W AccW)
  · simp [MS20]
  · intro j
    rw [SvGolf.Cycle.flatMap_ffUpd_all, g20_edgeQ N W AccW F (by omega), commit20 (mm20Q_names _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)]
    exact g20_settle N W AccW F hN hW hF σ j _ _ _ _ _ _ _ _ _ _ _ _ _ (width_apSet ..) (width_bpSet ..)

set_option maxHeartbeats 1000000

def BusyAt20 (N W AccW : Nat) (A B : BitVec (N * N * W)) (t : Nat) (st : SvState) : Prop :=
  ∃ (ck r s : LVec),
    st = MS20 ck r s
      (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false)
      (accC20 N W AccW A B t) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec A) (LVec.ofBitVec B)
      (apSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A))
      (bpSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec B))

def FinAt20 (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  ∃ ck r s a b k am bm ap bp,
    st = MS20 ck r s a b (knownBit true)
      (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)) k (knownBit false) am bm ap bp ∧
    k.width = 32 ∧ am.width = N * N * W ∧ bm.width = N * N * W ∧
    ap.width = N * N * W ∧ bp.width = N * N * W

def Cycle20 (N W AccW : Nat) : Prop :=
  ∀ (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (σ : ScheduleOracle) (e : SvState)
    (ck r s a b dn c k bz am bm ap bp : LVec) (kk F : Nat),
    32 ≤ F → ap.width = N * N * W → bp.width = N * N * W →
    ∃ kk', cycleStep2 (design.sem N W AccW) σ F e
      (MS20 ck r s a b dn c k bz am bm ap bp) kk =
      .ok (mm20Next N W AccW (appIn e "clk" ck) (appIn e "rst" r)
        (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn c k bz am bm, kk')

theorem cycle20_from_handover (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) : Cycle20 N W AccW := by
  intro hN' hW' hA' hR32' σ e ck r s a b dn c k bz am bm ap bp kk F hF hap hbp
  exact mm20_cycle N W AccW hN' hW' hA' hR32' σ e ck r s a b dn c k bz am bm ap bp kk F hF hap hbp

def Ready20 (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ (ck r s a b c k bz am bm ap bp : LVec),
    st = MS20 ck r s a b (knownBit false) c k (knownBit false) am bm ap bp ∧
    c.width = N * N * AccW ∧ k.width = 32 ∧ am.width = N * N * W ∧
    bm.width = N * N * W ∧ ap.width = N * N * W ∧ bp.width = N * N * W

def Done20 (N W AccW : Nat) (A B : BitVec (N * N * W)) (st : SvState) : Prop :=
  FinAt20 N W AccW A B st

def Shape20 (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ (ck r s a b dn c k bz am bm ap bp : LVec),
    st = MS20 ck r s a b dn c k bz am bm ap bp ∧
    dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
    am.width = N * N * W ∧ bm.width = N * N * W ∧
    ap.width = N * N * W ∧ bp.width = N * N * W

theorem mm20Next_shape (N W AccW : Nat)
    (ck r s a b dn c k bz am bm : LVec)
    (h : dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
      am.width = N * N * W ∧ bm.width = N * N * W)
    (hap : (apSet N W k am).width = N * N * W)
    (hbp : (bpSet N W k bm).width = N * N * W) :
    Shape20 N W AccW (mm20Next N W AccW ck r s a b dn c k bz am bm) := by
  rcases h with ⟨hd, hc, hk, hb, ham, hbm⟩
  refine ⟨ck, r, s, a, b, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [mm20Next, mm20Q_names, width_apSet, width_bpSet, hd, hc, hk, hb, ham, hbm, hap, hbp]

theorem cell20_step_over_pick {N W AccW i j : Nat} (hW : 1 ≤ W)
    (hi : i < N) (hj : j < N) (c k am bm : LVec) :
    cellV20 N W AccW i j c (apSet N W k am) (bpSet N W k bm) =
      ((((c.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        (((LVec.replVec AccW ((pickAV N W i k am).extract (W - 1) 1)).concat
          (pickAV N W i k am)).mul
          ((LVec.replVec AccW ((pickBV N W j k bm).extract (W - 1) 1)).concat
            (pickBV N W j k bm)))).resizeU AccW).resizeU AccW := by
  exact cellV20_settled hW hi hj c k am bm

theorem cell20_acc_step {N W AccW i j t : Nat} (hW : 1 ≤ W)
    (hi : i < N) (hj : j < N) {A B : BitVec (N * N * W)}
    (ha : pickAV N W i (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A) =
      LVec.ofBitVec (BitVec.extractLsb' ((i * N + t) * W) W A))
    (hb : pickBV N W j (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec B) =
      LVec.ofBitVec (BitVec.extractLsb' ((t * N + j) * W) W B)) :
    cellV20 N W AccW i j (accC20 N W AccW A B t)
      (apSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A))
      (bpSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec B)) =
      LVec.ofBitVec (BitVec.ofInt AccW (psum20 N W A B (t + 1) i j)) := by
  rw [cellV20_settled hW hi hj]
  have hd : (i * N + j) / N = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * N + j) % N = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hr : i * N + j < N * N := by
    have := g20_rm_lt hi hj
    exact this
  have hC := Lib.rowMajor_window_le (w := AccW) hi hj
  have hA : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega)
    simpa using this
  have hB : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj
    simpa using this
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  have sa : BitVec.extractLsb' (W - 1) 1 (BitVec.extractLsb' ((i * N + t) * W) W A) =
      BitVec.extractLsb' ((i * N + t) * W + W - 1) 1 A := by
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    have hq0 : q = 0 := by omega
    subst q
    have hWlt : W - 1 < W := by omega
    simp [BitVec.getLsbD_extractLsb', hWlt, Nat.add_sub_assoc hW]
  have sb : BitVec.extractLsb' (W - 1) 1 (BitVec.extractLsb' ((t * N + j) * W) W B) =
      BitVec.extractLsb' ((t * N + j) * W + W - 1) 1 B := by
    apply BitVec.eq_of_getLsbD_eq
    intro q hq
    have hq0 : q = 0 := by omega
    subst q
    have hWlt : W - 1 < W := by omega
    simp [BitVec.getLsbD_extractLsb', hWlt, Nat.add_sub_assoc hW]
  have wc := extractLsb'_packBV (n := N * N)
    (fun r => BitVec.ofInt AccW (psum20 N W A B t (r / N) (r % N))) hr
  simp only [hd, hm] at wc
  simp (disch := omega) only [accC20, LVec.extract_ofBitVec, extractLsb'_packBV, hd, hm,
    LVec.concatMany_singleton, LVec.concatMany_cons_cons, LVec.replVec_ofBitVec,
    LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.add_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend, ha, hb, wc, sa, sb, e1, e2, psum20_succ,
    BitVec.ofInt_add, Tasks.Matmul.entry]

theorem cycle_preserves_shape20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (σ : ScheduleOracle) (F : Nat) (e st st' : SvState) (k k' : Nat)
    (hF : 32 ≤ F) (hs : Shape20 N W AccW st)
    (hc : cycleStep2 (design.sem N W AccW) σ F e st k = .ok (st', k')) :
    Shape20 N W AccW st' := by
  obtain ⟨ck, r, s, a, b, dn, c, kk, bz, am, bm, ap, bp, rfl, hd, hcw, hkw, hbw, ham, hbm, hap, hbp⟩ := hs
  obtain ⟨kk', hnext⟩ := mm20_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c kk bz am bm ap bp k F hF hap hbp
  have heq := (Prod.mk.inj (cycleStep2_det hc hnext)).1
  subst st'
  apply mm20Next_shape N W AccW (appIn e "clk" ck) (appIn e "rst" r)
    (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn c kk bz am bm
  · exact ⟨hd, hcw, hkw, hbw, ham, hbm⟩
  · simp [width_apSet]
  · simp [width_bpSet]

def BusyTransition20 (N W AccW : Nat) : Prop :=
  ∀ (A B : BitVec (N * N * W)) (t : Nat), t < N →
    ∃ st st', BusyAt20 N W AccW A B t st ∧
      (∀ σ F e k k', cycleStep2 (design.sem N W AccW) σ F e st k = .ok (st', k') →
        (BusyAt20 N W AccW A B (t + 1) st' ∨ FinAt20 N W AccW A B st'))

theorem busy_transition_over_cycle20 (N W AccW : Nat)
    (h : BusyTransition20 N W AccW) : BusyTransition20 N W AccW := by
  exact h

def PhaseInvariant20 (N W AccW : Nat) : Prop :=
  (∀ st, Ready20 N W AccW st → Shape20 N W AccW st) ∧
  BusyTransition20 N W AccW ∧
  (∀ A B st, FinAt20 N W AccW A B st → Shape20 N W AccW st)

theorem phase_invariant20 (N W AccW : Nat) (hbusy : BusyTransition20 N W AccW) :
    PhaseInvariant20 N W AccW := by
  refine ⟨?_, hbusy, ?_⟩
  · intro st hs
    rcases hs with ⟨ck, r, s, a, b, c, k, bz, am, bm, ap, bp, rfl, hc, hk, ham, hbm, hap, hbp⟩
    refine ⟨ck, r, s, a, b, (knownBit false), c, k, (knownBit false), am, bm, ap, bp,
      rfl, ?_⟩
    exact ⟨by simp, hc, hk, by simp, ham, hbm, hap, hbp⟩
  · intro A B st hs
    rcases hs with ⟨ck, r, s, a, b, k, am, bm, ap, bp, rfl, hk, ham, hbm, hap, hbp⟩
    refine ⟨ck, r, s, a, b, (knownBit true), (LVec.ofBitVec (Tasks.Matmul.product N W AccW A B)), k,
      (knownBit false), am, bm, ap, bp, rfl, ?_⟩
    exact ⟨by simp, by simp, hk, by simp, ham, hbm, hap, hbp⟩

def InvariantShape20 (N W AccW : Nat) : SvState → Prop := Shape20 N W AccW

theorem invariant_shape_preserved20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)
    (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (σ : ScheduleOracle) (F : Nat) (e st st' : SvState) (k k' : Nat)
    (hF : 32 ≤ F) (hs : InvariantShape20 N W AccW st)
    (hc : cycleStep2 (design.sem N W AccW) σ F e st k = .ok (st', k')) :
    InvariantShape20 N W AccW st' := by
  exact cycle_preserves_shape20 N W AccW hN hW hA hR32 σ F e st st' k k' hF hs hc


def Invariant20 (N W AccW : Nat) (st : SvState) : Prop :=
  Ready20 N W AccW st ∨ ∃ A B t, BusyAt20 N W AccW A B t st ∨ FinAt20 N W AccW A B st

def CyclePreserves20 (N W AccW : Nat) : Prop :=
  ∀ (σ : ScheduleOracle) (F : Nat) (e st st' : SvState) (k k' : Nat),
    Invariant20 N W AccW st →
    cycleStep2 (mmD N W AccW) σ F e st k = .ok (st', k') →
    Invariant20 N W AccW st'

theorem invariant_preservation20 (N W AccW : Nat) (hcycle : CyclePreserves20 N W AccW) :
    ∀ (σ : ScheduleOracle) (F : Nat) (e st st' : SvState) (k k' : Nat),
      Invariant20 N W AccW st →
      cycleStep2 (mmD N W AccW) σ F e st k = .ok (st', k') →
      Invariant20 N W AccW st' := by
  intro σ F e st k st' k' hs hc
  exact hcycle σ F e st k st' k' hs hc

def Phases20 (N W AccW : Nat) : Prop :=
  (∀ st, Ready20 N W AccW st → Invariant20 N W AccW st) ∧
  (∀ A B t st, BusyAt20 N W AccW A B t st → Invariant20 N W AccW st) ∧
  (∀ A B st, FinAt20 N W AccW A B st → Invariant20 N W AccW st)

theorem phases20 (N W AccW : Nat) : Phases20 N W AccW := by
  refine ⟨?_, ?_, ?_⟩
  · intro st h
    exact Or.inl h
  · intro A B t st h
    exact Or.inr ⟨A, B, t, Or.inl h⟩
  · intro A B st h
    exact Or.inr ⟨A, B, 0, Or.inr h⟩

def Solution20 (N W AccW : Nat) : Prop :=
  CyclePreserves20 N W AccW ∧ Phases20 N W AccW

theorem solution20_over_cycle (N W AccW : Nat) (hcycle : CyclePreserves20 N W AccW) :
    Solution20 N W AccW := by
  exact ⟨hcycle, phases20 N W AccW⟩

def Wd20 (N W AccW : Nat) (dn c k bz am bm ap bp : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  am.width = N * N * W ∧ bm.width = N * N * W ∧ ap.width = N * N * W ∧ bp.width = N * N * W

def I20 (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm ap bp, st = MS20 ck r s a b dn c k bz am bm ap bp ∧
    Wd20 N W AccW dn c k bz am bm ap bp

theorem mm_init20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hR32 : Rng32 N W AccW) : I20 N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N*N*W), .xVec (N*N*W), .xVec 1,
    .xVec (N*N*AccW), .xVec 32, .xVec 1, .xVec (N*N*W), .xVec (N*N*W),
    .xVec (N*N*W), .xVec (N*N*W), ?_, by simp [Wd20]⟩
  simp [initState2, mmD, mmDecls, MS20]

theorem mmNext_I20 (N W AccW : Nat) (ck r s a b dn c k bz am bm ap bp : LVec)
    (hw : Wd20 N W AccW dn c k bz am bm ap bp) :
    I20 N W AccW (mm20Next N W AccW ck r s a b dn c k bz am bm) := by
  rcases hw with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  unfold I20
  refine ⟨ck, r, s, a, b, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [Wd20, mm20Next, mm20Q_names, width_apSet, width_bpSet, h1,h2,h3,h4,h5,h6,h7,h8]

theorem mm_noq20 (N W AccW : Nat) :
    (mmD N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  simp [mmD, mmCtrl, mmCells, pickA, pickB, mmCell, nb,
    Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

/-! ## The cycle on known control values, the phases and the statement

`mm20Next` splits by register: the controller's queue writes `done`, `k`, `busy`, `a_mem`,
`b_mem`; the cells' queue writes `C`.  Then one lemma per kind of cycle (idle, reset, start,
busy), the phase model, the three rules, and `solution`. -/

attribute [local simp] condTrue_knownBit

/-- The cells' part of the edge queue. -/
def cellsQ20 (N W AccW : Nat) (r s bz c ap bp : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j => cellQ20 N W AccW r s bz c ap bp i j

theorem cellQ20_C (N W AccW : Nat) (r s bz c ap bp : LVec) (i j : Nat) :
    ∀ u ∈ cellQ20 N W AccW r s bz c ap bp i j, u.1 = "C" := by
  unfold cellQ20
  by_cases h1 : rstOr20 r s = true <;> by_cases h2 : bz.condTrue = true <;> simp [h1, h2]

theorem ctrlQ20_notC (N : Nat) (r s a b dn k bz am bm : LVec) :
    ∀ u ∈ ctrlQ20 N r s a b dn k bz am bm, u.1 ≠ "C" := by
  unfold ctrlQ20
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    by_cases h4 : (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).condTrue = true <;>
    simp [h1, h2, h3, h4]

theorem cellsQ20_fold_ne (N W AccW : Nat) (r s bz c ap bp : LVec) {n : String} (hn : n ≠ "C") (x : LVec) :
    nbaFold n (cellsQ20 N W AccW r s bz c ap bp) x = x := by
  refine nbaFold_of_forall_ne (fun u hu => ?_) x
  simp only [cellsQ20, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  rw [cellQ20_C _ _ _ _ _ _ _ _ _ _ _ u hu]
  exact fun h => hn h.symm

/-- The next state, register by register. -/
theorem mm20Next_eq (N W AccW : Nat) (ck r s a b dn c k bz am bm : LVec) :
    mm20Next N W AccW ck r s a b dn c k bz am bm =
      MS20 ck r s a b (nbaFold "done" (ctrlQ20 N r s a b dn k bz am bm) dn)
        (nbaFold "C" (cellsQ20 N W AccW r s bz c (apSet N W k am) (bpSet N W k bm)) c)
        (nbaFold "k" (ctrlQ20 N r s a b dn k bz am bm) k)
        (nbaFold "busy" (ctrlQ20 N r s a b dn k bz am bm) bz)
        (nbaFold "a_mem" (ctrlQ20 N r s a b dn k bz am bm) am)
        (nbaFold "b_mem" (ctrlQ20 N r s a b dn k bz am bm) bm)
        (apSet N W (nbaFold "k" (ctrlQ20 N r s a b dn k bz am bm) k)
          (nbaFold "a_mem" (ctrlQ20 N r s a b dn k bz am bm) am))
        (bpSet N W (nbaFold "k" (ctrlQ20 N r s a b dn k bz am bm) k)
          (nbaFold "b_mem" (ctrlQ20 N r s a b dn k bz am bm) bm)) := by
  have e : mm20Q N W AccW r s a b dn c k bz am bm (apSet N W k am) (bpSet N W k bm) =
      ctrlQ20 N r s a b dn k bz am bm ++
        cellsQ20 N W AccW r s bz c (apSet N W k am) (bpSet N W k bm) := rfl
  have hq : nbaFold "C" (ctrlQ20 N r s a b dn k bz am bm) c = c :=
    nbaFold_of_forall_ne (ctrlQ20_notC N r s a b dn k bz am bm) c
  simp only [mm20Next, e, nbaFold_append, hq,
    cellsQ20_fold_ne N W AccW r s bz c _ _ (show "done" ≠ "C" by decide),
    cellsQ20_fold_ne N W AccW r s bz c _ _ (show "k" ≠ "C" by decide),
    cellsQ20_fold_ne N W AccW r s bz c _ _ (show "busy" ≠ "C" by decide),
    cellsQ20_fold_ne N W AccW r s bz c _ _ (show "a_mem" ≠ "C" by decide),
    cellsQ20_fold_ne N W AccW r s bz c _ _ (show "b_mem" ≠ "C" by decide)]

theorem rstOr20_ff : rstOr20 (knownBit false) (knownBit false) = false := by
  simp [rstOr20, LVec.ofLogic_l0]
theorem rstOr20_start : rstOr20 (knownBit false) (knownBit true) = true := by
  simp [rstOr20, LVec.ofLogic_l1]
theorem rstOr20_rst (s : LVec) : rstOr20 (knownBit true) s = true := by
  simp [rstOr20]

/-- The cells' loop of single writes, as one row-major `map`. -/
theorem rowMajor_map20 {N W AccW : Nat} {r s bz c ap bp : LVec} (g : Nat → LVec)
    (h : ∀ i j, i < N → j < N →
      cellQ20 N W AccW r s bz c ap bp i j = [("C", (i * N + j) * AccW, g (i * N + j))]) :
    cellsQ20 N W AccW r s bz c ap bp = (List.range (N * N)).map (fun q => ("C", q * AccW, g q)) := by
  unfold cellsQ20
  suffices ∀ M, M ≤ N →
      (List.range M).flatMap (fun i => (List.range N).flatMap (cellQ20 N W AccW r s bz c ap bp i)) =
      (List.range (M * N)).map (fun q => ("C", q * AccW, g q)) from this N (Nat.le_refl _)
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

theorem accC20_width (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) :
    (accC20 N W AccW A B t).width = N * N * AccW := by
  simp [accC20]

/-- An idle cycle (reset, `start` and `busy` low) keeps every register. -/
theorem next_idle20 (N W AccW : Nat) (ck a b dn c k am bm : LVec) :
    mm20Next N W AccW ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm =
      MS20 ck (knownBit false) (knownBit false) a b dn c k (knownBit false) am bm
        (apSet N W k am) (bpSet N W k bm) := by
  have hq : cellsQ20 N W AccW (knownBit false) (knownBit false) (knownBit false) c
      (apSet N W k am) (bpSet N W k bm) = [] := by
    simp [cellsQ20, cellQ20, rstOr20_ff]
  rw [mm20Next_eq, hq]
  simp [ctrlQ20]

/-- A reset cycle leads to the ready state, from every state of the shape. -/
theorem next_reset20 {N W AccW : Nat} (ck s a b dn c k bz am bm ap bp : LVec)
    (hw : Wd20 N W AccW dn c k bz am bm ap bp) :
    Ready20 N W AccW (mm20Next N W AccW ck (knownBit true) s a b dn c k bz am bm) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hw
  have hd : nbaFold "done" (ctrlQ20 N (knownBit true) s a b dn k bz am bm) dn = knownBit false := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (ctrlQ20 N (knownBit true) s a b dn k bz am bm) bz = knownBit false := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, ↓reduceIte, nbaFold_cons_self,
      nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  rw [mm20Next_eq, hd, hb]
  exact ⟨_, _, _, _, _, _, _, knownBit false, _, _, _, _, rfl, by simp [h2], by simp [h3], by simp [h5],
    by simp [h6], width_apSet .., width_bpSet ..⟩

/-- A start cycle: the banks capture the operands, the accumulators clear, `k` = 0. -/
theorem next_start20 {N W AccW : Nat} (A B : BitVec (N * N * W)) (ck dn c k bz am bm ap bp : LVec)
    (hw : Wd20 N W AccW dn c k bz am bm ap bp) :
    mm20Next N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B)
        dn c k bz am bm =
      MS20 ck (knownBit false) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) (knownBit false)
        (accC20 N W AccW A B 0) (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true)
        (LVec.ofBitVec A) (LVec.ofBitVec B)
        (apSet N W (LVec.ofBitVec (BitVec.ofNat 32 0)) (LVec.ofBitVec A))
        (bpSet N W (LVec.ofBitVec (BitVec.ofNat 32 0)) (LVec.ofBitVec B)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -⟩ := hw
  have hqC := rowMajor_map20 (N := N) (W := W) (AccW := AccW) (r := knownBit false) (s := knownBit true)
    (bz := bz) (c := c) (ap := apSet N W k am) (bp := bpSet N W k bm)
    (fun q => LVec.ofBitVec (BitVec.ofInt AccW (psum20 N W A B 0 (q / N) (q % N))))
    (fun i j hi hj => by simp [cellQ20, rstOr20_start, psum20])
  have hd : nbaFold "done" (ctrlQ20 N (knownBit false) (knownBit true) (LVec.ofBitVec A)
      (LVec.ofBitVec B) dn k bz am bm) dn = knownBit false := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h1, LVec.resizeU_one_l0]
    exact LVec.insertAt_zero_of_width_eq (by simp [h1])
  have hb : nbaFold "busy" (ctrlQ20 N (knownBit false) (knownBit true) (LVec.ofBitVec A)
      (LVec.ofBitVec B) dn k bz am bm) bz = knownBit true := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h4, LVec.resizeU_one_l1]
    exact LVec.insertAt_zero_of_width_eq (by simp [h4])
  have hk : nbaFold "k" (ctrlQ20 N (knownBit false) (knownBit true) (LVec.ofBitVec A)
      (LVec.ofBitVec B) dn k bz am bm) k = LVec.ofBitVec (BitVec.ofNat 32 0) := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h3, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h3])
  have ha : nbaFold "a_mem" (ctrlQ20 N (knownBit false) (knownBit true) (LVec.ofBitVec A)
      (LVec.ofBitVec B) dn k bz am bm) am = LVec.ofBitVec A := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h5, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h5])
  have hbm : nbaFold "b_mem" (ctrlQ20 N (knownBit false) (knownBit true) (LVec.ofBitVec A)
      (LVec.ofBitVec B) dn k bz am bm) bm = LVec.ofBitVec B := by
    simp (disch := decide) only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
      nbaFold_cons_self, nbaFold_cons_ne, nbaFold_nil, h6, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
    exact LVec.insertAt_zero_of_width_eq (by simp [h6])
  rw [mm20Next_eq, hqC, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h2, hd, hb, hk, ha, hbm]
  rfl

/-- The controller in a busy cycle at step `t < N`. -/
theorem ctrl_busy20 {N : Nat} (hN32 : N < 2 ^ 32) {t : Nat} (ht : t < N) (a b am bm : LVec) :
    nbaFold "done" (ctrlQ20 N (knownBit false) (knownBit false) a b (knownBit false)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm) (knownBit false) =
      knownBit (decide (t + 1 = N)) ∧
    nbaFold "k" (ctrlQ20 N (knownBit false) (knownBit false) a b (knownBit false)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm) (LVec.ofBitVec (BitVec.ofNat 32 t)) =
      LVec.ofBitVec (BitVec.ofNat 32 (t + 1)) ∧
    nbaFold "busy" (ctrlQ20 N (knownBit false) (knownBit false) a b (knownBit false)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm) (knownBit true) =
      knownBit (decide (t + 1 ≠ N)) ∧
    nbaFold "a_mem" (ctrlQ20 N (knownBit false) (knownBit false) a b (knownBit false)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm) am = am ∧
    nbaFold "b_mem" (ctrlQ20 N (knownBit false) (knownBit false) a b (knownBit false)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) am bm) bm = bm := by
  have h1' : LVec.ofInt 32 1 = LVec.ofBitVec 1#32 := by decide
  simp only [ctrlQ20, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, LVec.ofInt_eq_ofBitVec,
    BitVec.ofInt_natCast, BitVec.ofInt_ofNat, h1', LVec.sub_ofBitVec,
    LVec.eqLogical_ofBitVec, LVec.ofLogic_ofBool, decide_eq_true_eq,
    Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN32),
    LVec.width_ofBitVec, LVec.add_ofBitVec, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
  by_cases hf : t + 1 = N <;>
    simp [hf, LVec.insertAt_zero_of_width_eq, LVec.resizeU_one_l0, LVec.resizeU_one_l1,
      BitVec.ofNat_add_ofNat]

/-- **The busy step**: at step `t < N` every accumulator gains `A[i][t] * B[t][j]`, `k` advances,
and the last step raises `done`. -/
theorem next_step20 {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N * N * W < 2 ^ 31)
    (A B : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b : LVec) :
    mm20Next N W AccW ck (knownBit false) (knownBit false) a b (knownBit false) (accC20 N W AccW A B t)
        (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true) (LVec.ofBitVec A) (LVec.ofBitVec B) =
      MS20 ck (knownBit false) (knownBit false) a b (knownBit (decide (t + 1 = N)))
        (accC20 N W AccW A B (t + 1)) (LVec.ofBitVec (BitVec.ofNat 32 (t + 1)))
        (knownBit (decide (t + 1 ≠ N))) (LVec.ofBitVec A) (LVec.ofBitVec B)
        (apSet N W (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (LVec.ofBitVec A))
        (bpSet N W (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (LVec.ofBitVec B)) := by
  have hN32 : N < 2 ^ 32 := by
    have h1 : N ≤ N * N := Nat.le_mul_of_pos_left N hN
    have h2 : N * N ≤ N * N * W := Nat.le_mul_of_pos_right (N * N) hW
    omega
  have hqC := rowMajor_map20 (N := N) (W := W) (AccW := AccW) (r := knownBit false) (s := knownBit false)
    (bz := knownBit true) (c := accC20 N W AccW A B t)
    (ap := apSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec A))
    (bp := bpSet N W (LVec.ofBitVec (BitVec.ofNat 32 t)) (LVec.ofBitVec B))
    (fun q => LVec.ofBitVec (BitVec.ofInt AccW (psum20 N W A B (t + 1) (q / N) (q % N))))
    (fun i j hi hj => by
      have b1 := Lib.rowMajor_window_le (w := W) hi ht
      have b2 := Lib.rowMajor_window_le (w := W) ht hj
      simp only [cellQ20, rstOr20_ff, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
        cell20_acc_step (t := t) hW hi hj (pickAV_known (t := t) hN hW (by omega)) (pickBV_known (t := t) hN hW (by omega)),
        g20_rm_div hj, g20_rm_mod hj])
  obtain ⟨c1, c2, c3, c4, c5⟩ := ctrl_busy20 hN32 ht a b (LVec.ofBitVec A) (LVec.ofBitVec B)
  rw [mm20Next_eq, hqC, nbaFold_map_insertEntries,
    LVec.insertEntries_ofBitVec _ _ (accC20_width ..), c1, c2, c3, c4, c5]
  rfl

/-! ### The phase model -/

theorem MS20_inj {ck r s a b dn c k bz am bm ap bp ck' r' s' a' b' dn' c' k' bz' am' bm' ap' bp' : LVec}
    (h : MS20 ck r s a b dn c k bz am bm ap bp = MS20 ck' r' s' a' b' dn' c' k' bz' am' bm' ap' bp') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ am = am' ∧ bm = bm' ∧ ap = ap' ∧ bp = bp' := by
  simp only [MS20, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

/-- One cycle from a state of the shape, evaluated (`mm20_cycle`). -/
def Stp20 (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz am bm ap bp, prev = MS20 ck r s a b dn c k bz am bm ap bp ∧
    Wd20 N W AccW dn c k bz am bm ap bp ∧
    st = mm20Next N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a)
      (appIn e "B" b) dn c k bz am bm

theorem ops_appIn20 {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

def model20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (hNW : N * N * W < 2 ^ 31) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I20 N W AccW
  Step := Stp20 N W AccW
  init := mm_init20 N W AccW hN hW hA hR32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, a, b, dn, c, kk, bz, am, bm, ap, bp, rfl, hw⟩ hc
    obtain ⟨kk', hnext⟩ := mm20_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c kk bz am bm ap bp
      k 32 (Nat.le_refl _) hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2
    exact ⟨ck, r, s, a, b, dn, c, kk, bz, am, bm, ap, bp, rfl, hw, (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, -, hw, rfl⟩
    exact mmNext_I20 N W AccW _ _ _ _ _ dn c k bz am bm ap bp hw
  Ready := Ready20 N W AccW
  Busy x m st := ∃ t, t + m + 1 = N ∧ BusyAt20 N W AccW x.1 x.2.1 t st
  Fin x st := FinAt20 N W AccW x.1 x.2.1 st
  ready_done := by
    rintro st ⟨ck, r, s, a, b, c, k, bz, am, bm, ap, bp, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, MS20, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, rfl⟩
    simp [BitIs, Tasks.Matmul.task, MS20, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, am, bm, ap, bp, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, MS20, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    exact next_reset20 _ _ _ _ dn c k bz am bm ap bp hw
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn20 hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb,
      next_start20 _ _ _ dn c k bz am bm ap bp hw]
    exact .inr ⟨N - 1, by omega, 0, by omega, _, _, _, rfl⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', hb⟩ hr hs hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS20_inj hb
    obtain ⟨ha, hb'⟩ := ops_appIn20 hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, ha, hb',
      next_step20 (AccW := AccW) hN hW hNW x.1 x.2.1 (t := t) (by omega)]
    by_cases hf : t + 1 = N
    · left
      simp only [hf, accC20_N, decide_true, ne_eq, not_true_eq_false, decide_false]
      exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp, by simp, by simp, width_apSet .., width_bpSet ..⟩
    · right
      simp only [hf, ne_eq, not_false_eq_true, decide_true, decide_false]
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, rfl⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', c', k', bz', am', bm', ap', bp', hb, h2, h3, h5, h6, -, -⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS20_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle20]
    exact ⟨_, _, _, _, _, _, _, knownBit false, _, _, _, _, rfl, h2, h3, h5, h6, width_apSet .., width_bpSet ..⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', am', bm', ap', bp', hb, h3, h5, h6, -, -⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := MS20_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle20]
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, h3, h5, h6, width_apSet .., width_bpSet ..⟩

/-! ### The interface, the clock discipline and the three rules -/

theorem mm_interface20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_mem", "b_mem", "a_pick", "b_pick"] :
      List String).Nodup
    decide⟩

/-- Every process of the design, by membership. -/
theorem g20_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmD N W AccW).processes.toList) :
    p = mmCtrl N W ∨ ∃ i j, i < N ∧ j < N ∧
      (p = pickA N W i j ∨ p = pickB N W i j ∨ p = mmCell N W AccW i j) := by
  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hidx
  exact g20_proc_cases hidx

theorem mm_disciplined20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨by simp [Tasks.Matmul.task, mmD, mmDecls, Design2.inputNames], fun p hp => ?_⟩
  rcases g20_proc_mem hp with rfl | ⟨i, j, -, -, rfl | rfl | rfl⟩
  · simp [Tasks.Matmul.task, mmCtrl, nb, c32, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, pickA, c32n, edgeClock, asyncReset, processDataNames, lhsNames, exprNames,
      exprListNames, Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, pickB, c32n, edgeClock, asyncReset, processDataNames, lhsNames, exprNames,
      exprListNames, Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmCell, sext, edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames,
      stmtListNames, lhsNames, exprNames, exprListNames]

/-- Rule 1: the picks are the only combinational assignments, and they drive `a_pick` / `b_pick`,
which are not output ports.  The set: every signal but the two outputs. -/
theorem mm_moore20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine ⟨fun n => n ≠ "done" ∧ n ≠ "C", ?_, ?_, ?_⟩
  · intro n hn _
    simp [mmD, mmDecls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he _
    obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    rcases g20_proc_mem hp with rfl | ⟨i, j, -, -, rfl | rfl | rfl⟩
    · simp [mmCtrl, processDeps] at he
    · simp [pickA, processDeps, lhsTargets] at he
      simp [he]
    · simp [pickB, processDeps, lhsTargets] at he
      simp [he]
    · simp [mmCell, processDeps] at he
  · intro o ho
    simp [mmD, mmDecls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> simp

theorem mm_powerUp20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I20 N W AccW st := by
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
  obtain ⟨am, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bm, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨ap, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain ⟨bp, r13, rfl, w13, -, h13⟩ := powerUp_cons.mp h12
  obtain rfl := powerUp_nil.mp h13
  exact ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, rfl, w6, w7, w8, w9, w10, w11, w12, w13⟩

theorem mm_terminatesPU20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I20 N W AccW) (mm_powerUp20 N W AccW hN hW hA hR32) (fun σ => ⟨32, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hR32]; exact mm_noq20 N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, am, bm, ap, bp, rfl, hw⟩
  obtain ⟨kk', hnext⟩ := mm20_cycle N W AccW hN hW hA hR32 σ e ck r s a b dn c k bz am bm ap bp
    kk 32 (Nat.le_refl _) hw.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2
  exact ⟨_, _, hnext, mmNext_I20 N W AccW _ _ _ _ _ dn c k bz am bm ap bp hw⟩

theorem lvec_l0_known20 : (⟨#[.l0]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l0).allKnown = true
  rw [LVec.ofLogic_l0]; exact LVec.allKnown_ofBitVec _

theorem lvec_l1_known20 : (⟨#[.l1]⟩ : LVec).allKnown = true := by
  show (LVec.ofLogic .l1).allKnown = true
  rw [LVec.ofLogic_l1]; exact LVec.allKnown_ofBitVec _

theorem ctrl20_xsafe (N W AccW : Nat) : xsProc (mmD N W AccW) (mmCtrl N W) = true := by
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmCtrl, nb, c32, mmD, mmDecls,
    lvec_l0_known20, lvec_l1_known20, LVec.ofInt, LVec.allKnown_ofBitVec]

theorem pickA20_xsafe (N W AccW i j : Nat) : xsProc (mmD N W AccW) (pickA N W i j) = true := by
  simp [xsProc, xsLhs, xsWidth, binW, sigWidth, pickA, c32n, mmD, mmDecls, LVec.ofInt]

theorem pickB20_xsafe (N W AccW i j : Nat) : xsProc (mmD N W AccW) (pickB N W i j) = true := by
  simp [xsProc, xsLhs, xsWidth, binW, sigWidth, pickB, c32n, mmD, mmDecls, LVec.ofInt]

theorem cell20_xsafe {N W AccW i j : Nat} (hW : 1 ≤ W) (hi : i < N) (hj : j < N) :
    xsProc (mmD N W AccW) (mmCell N W AccW i j) = true := by
  have hC := Lib.rowMajor_window_le (M := N) (N := N) (w := AccW) hi hj
  have hP := Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hj
  have hP1 : (i * N + j) * W + W - 1 + 1 ≤ N * N * W := by omega
  simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, mmCell, sext, mmD, mmDecls,
    LVec.allKnown_ofBitVec, hC, hP, hP1]

theorem mm_xsafe20 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hR32 : Rng32 N W AccW) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hR32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases g20_proc_mem hp with rfl | ⟨i, j, hi, hj, rfl | rfl | rfl⟩
  · exact ctrl20_xsafe N W AccW
  · exact pickA20_xsafe N W AccW i j
  · exact pickB20_xsafe N W AccW i j
  · exact cell20_xsafe hW hi hj

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
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases (mm_interface20 N W AccW hN hW hA hR32)
    (mm_disciplined20 N W AccW hN hW hA hR32) (mm_terminatesPU20 N W AccW hN hW hA hR32) hN
    (model20 N W AccW hN hW hA hR32 hNW) (mm_powerUp20 N W AccW hN hW hA hR32)
    (mm_moore20 N W AccW hN hW hA hR32) (mm_xsafe20 N W AccW hN hW hA hR32)

end Submission
