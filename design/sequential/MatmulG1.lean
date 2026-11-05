import SvGolf.LoadSv
import LeanModels.Sv.Gen2
import LeanModels.Sv.Hier2Gen
import LeanModels.Sv.SeqProfile
import LeanModels.Sv.SeqFamily

/-!
# matmul G1: the protocol-independent core (PLAN4 Gate 3, A's half; WIP)

`tasks/matmul/reference/matmul_g1.sv`: `N²` multiply-accumulate units, one step counter `k`.
1. **Agreement** (`mm_sem_eq`): the loaded family `mmSv.sem N W AccW` IS the hand-built `mmD`, at
   every `N, W, AccW ≥ 1` (the 2c recipe: P's `CounterInst` stages, the nested generate
   expanded as in `Examples/system-verilog/mul2d/gen.lean`).
2. **Profile** (`mm_profile_probes`): `mmD` is FF-only at the four probe points (kernel `rfl`).
3. **Invariant**: continued, staged against check.py's `Submission.Design`, in the complete reference
   `tasks/matmul/reference/matmul_g1.lean` (the clock step, the invariant, the protocol).

Not in any lake library; compiled standalone (`cd svgolf && lake env lean design/sequential/MatmulG1.lean`).
-/

namespace SvGolf.Seq.Matmul

open LeanModels.Sv

load_sv mmSv from "tasks/matmul/reference/matmul_g1.sv" (top := "matmul")
  (probes := "N=1,W=1,AccW=1;N=2,W=3,AccW=5;N=3,W=4,AccW=8;N=4,W=8,AccW=32")

/-! ## The hand-built family -/

/-- A 32-bit constant. -/
abbrev c32 (v : Int) : Expr2 := .lit (LVec.ofInt 32 v)

/-- `{{AccW{x[lo+W-1]}}, x[lo +: W]}`: entry `x[lo +: W]` sign-extended by `AccW` bits. -/
def sext (x : String) (AccW lo W : Nat) : Expr2 :=
  .concat #[.repl AccW (.concat #[.slice (.ident x) (lo + W - 1) 1]), .slice (.ident x) lo W]

/-- The PE at `(i, j)`: clear on `start`, else accumulate `a_sh[i][0] * b_sh[0][j]` while `busy`. -/
def mmPE (N W AccW i j : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "start")
    (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW) (.lit (LVec.replicate AccW .l0)))
    (some (.ifStmt (.ident "busy")
      (.nbaAssign (.slice "C" ((i * N + j) * AccW) AccW)
        (.resize AccW (.binary .add (.resize (AccW + W) (.slice (.ident "C") ((i * N + j) * AccW) AccW))
          (.binary .mul (sext "a_sh" AccW (i * N * W) W) (sext "b_sh" AccW (j * W) W)))))
      none)))

/-- A nonblocking write of a constant. -/
abbrev nb (n : String) (v : LVec) : Stmt2 := .nbaAssign (.ident n) (.lit v)

/-- The control: `busy`, `done`, the step counter `k`, the operand shift registers. -/
def mmCtrl (N W : Nat) : Process2 :=
  .alwaysFF "clk" (.ifStmt (.ident "rst")
    (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0)])
    (some (.ifStmt (.ident "start")
      (.block #[nb "busy" ⟨#[.l1]⟩, nb "done" ⟨#[.l0]⟩, nb "k" (LVec.replicate 32 .l0),
        .nbaAssign (.ident "a_sh") (.ident "A"), .nbaAssign (.ident "b_sh") (.ident "B")])
      (some (.ifStmt (.ident "busy")
        (.block #[.nbaAssign (.ident "k") (.binary .add (.ident "k") (c32 1)),
          .nbaAssign (.ident "a_sh") (.binary (.shr false) (.ident "a_sh") (c32 W)),
          .nbaAssign (.ident "b_sh") (.binary (.shr false) (.ident "b_sh") (.binary .mul (c32 N) (c32 W))),
          .ifStmt (.binary .eq (.ident "k") (.binary .sub (c32 N) (c32 1)))
            (.block #[nb "busy" ⟨#[.l0]⟩, nb "done" ⟨#[.l1]⟩]) none])
        none)))))

/-- The declarations, `A`/`B`/`a_sh`/`b_sh` at `wa` bits and `C` at `wc`. -/
def mmDecls (wa wc : Nat) : List Decl :=
  [{ name := "clk", width := 1, isInput := true }, { name := "rst", width := 1, isInput := true },
   { name := "start", width := 1, isInput := true }, { name := "A", width := wa, isInput := true },
   { name := "B", width := wa, isInput := true }, { name := "done", width := 1, isOutput := true },
   { name := "C", width := wc, isOutput := true }, { name := "k", width := 32 },
   { name := "busy", width := 1 }, { name := "a_sh", width := wa }, { name := "b_sh", width := wa }]

/-- The PEs, row-major. -/
def mmPEs (N W AccW : Nat) : List Process2 :=
  (List.range N).flatMap fun i => (List.range N).map fun j => mmPE N W AccW i j

def mmD (N W AccW : Nat) : Design2 where
  name := "matmul"
  decls := (mmDecls (N * N * W) (N * N * AccW)).toArray
  processes := (mmCtrl N W :: mmPEs N W AccW).toArray

/-! ## Agreement: the stages of `instantiate2` -/

def mmScope (N W AccW : Int) : IEnv :=
  { vals := [("N", N), ("W", W), ("AccW", AccW)], pwidths := [("N", 32), ("W", 32), ("AccW", 32)] }

def mmEnv (N W AccW : Int) : IEnv :=
  { mmScope N W AccW with dims := dimTable (mmScope N W AccW) mmSv.pdesign.decls }

theorem mm_paramEnv (N W AccW : Int) :
    mmSv.pdesign.paramEnv2 [N, W, AccW] = .ok (mmEnv N W AccW) := rfl

def mmElems : List (String × Nat) :=
  ["clk", "rst", "start", "A", "B", "done", "C", "k", "busy", "a_sh", "b_sh"].map (·, 1)

theorem mm_decls (N W AccW : Int) :
    buildDecls (mmEnv N W AccW) mmSv.pdesign.decls =
      .ok (mmDecls ((N * N * W - 1).natAbs + 1) ((N * N * AccW - 1).natAbs + 1)) := by
  simp [mmSv.pdesign, buildDecls, instDecl, PType.width_packed_cons, PDim.width, evalInt,
    mmEnv, mmScope, List.lookup, mmDecls, Gen2.except_ok_bind]

theorem mm_elems (N W AccW : Int) : buildElems (mmEnv N W AccW) mmSv.pdesign.decls = .ok mmElems := by
  simp [mmSv.pdesign, buildElems, PType.width_packed_cons, PDim.width, evalInt, mmEnv,
    mmScope, List.lookup, mmElems, Gen2.except_ok_bind]

/-- The instantiation environment. -/
abbrev mmE (N W AccW : Nat) : IEnv :=
  (mmEnv N W AccW).withDecls (mmDecls (N * N * W) (N * N * AccW))

theorem mm_ctrl (N W AccW : Nat) :
    mmSv.pdesign.processes.map (instProcess2 (mmE N W AccW) mmElems) = [mmCtrl N W] := by
  sv2_inst_simp [instStmt2, instStmts2, mmSv.pdesign, mmEnv, mmScope, mmDecls, mmElems, mmCtrl,
    dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
    PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, divOperandWidth2,
    instDivOperand2, fitDivOperand2]
  try and_intros
  all_goals first | rfl | decide

theorem cast3 (a b c : Nat) : ((a * b * c : Nat) : Int) = (a : Int) * b * c := by simp

theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem natAbs_pred {x : Nat} (h : 0 < x) : ((x : Int) - 1).natAbs + 1 = x := by omega

/-- Entry `(i, j)` of an `N×N` array of `w`-bit entries lies inside it. -/
theorem win_le {N w i j : Nat} (hi : i < N) (hj : j < N) : (i * N + j) * w + w ≤ N * N * w := by
  have h : i * N + j + 1 ≤ N * N := by
    have := Nat.mul_le_mul_right N (show i + 1 ≤ N by omega); rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have := Nat.mul_le_mul_right w h; rwa [Nat.add_mul, Nat.one_mul] at this

/-- The PE template (the process inside `g_row`/`g_col`). -/
def peT : PProcess :=
  match mmSv.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [.genFor _ _ _ _ _ _ [.process p]]] => p
  | _ => .alwaysFF "" (.block [])

/-- The label facts of an in-range window `[x, x + w)` of a `y`-bit vector, from `Nat` ones. -/
theorem win_facts (x y : Int) {lo w c : Nat} (h : lo + w ≤ c) (hw : 0 < w) (hx : (lo : Int) = x)
    (hy : (c : Int) = y) : 0 ≤ x ∧ x.toNat = lo ∧ x + w - 1 < y ∧ 1 ≤ x + w ∧ (x + w).toNat = lo + w :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩
theorem win_min (a : Int) {w : Int} (h : 0 < w) : min (a + w - 1) a = a := by omega
theorem win_max (a : Int) {w : Int} (h : 0 < w) : max (a + w - 1) a = a + w - 1 := by omega
theorem win_wid (a w : Int) : a + w - 1 - a + 1 = w := by omega

/-- The `sv2_inst_simp` set of the PE template (with the window facts in scope). -/
macro "pe_simp" : tactic => `(tactic| sv2_inst_simp [peT, evalSized, ctype, evalAt,
  SymBinOp.constClass, PExpr.pushedTarget, PExpr.readsSignal, PExpr.readsSignalList, except_pure,
  win_min, win_max, win_wid, instStmt2, mmSv.pdesign, mmEnv, mmScope, mmDecls, mmElems, mmPE, sext,
  dimTable, dimTableStep, PType.width_packed_cons, PDim.width, ctxOpWidth2, rigidMax2,
  PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, LVec.width, *])

theorem pe_inst (N W AccW i j : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hi : i < N)
    (hj : j < N) :
    instProcess2 (((mmE N W AccW).bindVal "i" i).bindVal "j" j) mmElems peT =
      mmPE N W AccW i j := by
  have pW := Nat.mul_pos (Nat.mul_pos hN hN) hW
  have pA := Nat.mul_pos (Nat.mul_pos hN hN) hA
  have hW0 : (0 : Int) < W := by omega
  have hA0 : (0 : Int) < AccW := by omega
  have hNW : (1 : Int) ≤ N * N * W := by have := cast3 N N W; omega
  have hNA : (1 : Int) ≤ N * N * AccW := by have := cast3 N N AccW; omega
  have hcA : ((N : Int) * N * W - 1).natAbs + 1 = N * N * W := by rw [← cast3]; exact natAbs_pred pW
  have hcC : ((N : Int) * N * AccW - 1).natAbs + 1 = N * N * AccW := by
    rw [← cast3]; exact natAbs_pred pA
  have hC := win_facts (((i : Int) * N + j) * AccW) (N * N * AccW) (win_le (w := AccW) hi hj) hA
    (by simp) (by simp)
  have ha := win_facts ((i : Int) * N * W) (N * N * W) (win_le (w := W) (j := 0) hi (by omega)) hW
    (by simp) (by simp)
  have hb := win_facts ((j : Int) * W) (N * N * W) (win_le (w := W) (i := 0) (by omega) hj) hW
    (by simp) (by simp)
  have hA1 : 0 < AccW := hA
  have hW1 : 0 < W := hW
  have hWne : ¬ W = 0 := by omega
  have hmode : (PartMode.up == PartMode.range) = false := rfl
  have hlt1 : ¬ AccW + W < AccW := by omega
  have hle1 : ¬ AccW + W ≤ AccW := by omega
  pe_simp
  -- `simp` cannot use `instExpr2`'s `resize` equation (measured): unfold it by hand.
  repeat (unfold instExpr2; pe_simp)

/-- `for (g = 0; g < N; g++) body`. -/
def genN (lbl g : String) (body : List GenItem) : GenItem :=
  .genFor (some lbl) g (.int 0) (.binary .slt (.genvarRef g) (.paramRef "N" none))
    (.unary .inc (.genvarRef g)) (some 4) body

theorem mm_gens_src : mmSv.pdesign.generates = [genN "g_row" "i" [genN "g_col" "j" ([peT].map .process)]] :=
  rfl

theorem n_bound {env : IEnv} {N : Nat} (h : env.vals.lookup "N" = some (N : Int)) (g : String)
    (hg : g ≠ "N") (i : Int) : evalInt (env.bindVal g i) (.paramRef "N" none) = .ok (N : Int) ∧
      (PExpr.paramRef "N" none).isInt (env.bindVal g i) = true := by
  have h' : (env.bindVal g i).vals.lookup "N" = some (N : Int) := by
    simp [IEnv.bindVal, List.lookup, h, beq_false_of_ne (Ne.symm hg)]
  exact ⟨evalInt_paramRef_of h', isInt_paramRef_of h'⟩

/-- **The nested generate expands to the row-major PEs** (`mul2d_pp_expand`'s route). -/
theorem mm_gens (N W AccW F : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) (hF : N < F) :
    expandList2 (mmE N W AccW) mmElems F mmSv.pdesign.generates = .ok (mmPEs N W AccW) := by
  have hNv : (mmE N W AccW).vals.lookup "N" = some (N : Int) := rfl
  rw [mm_gens_src]
  apply expandList2_singleton_ok
  rw [genN, GenItem.expand2_genFor_ascending_flatMap (N := (N : Int))
      (f := fun v => (intRange 0 N).flatMap fun w =>
        [peT].map (instProcess2 (((mmE N W AccW).bindVal "i" v).bindVal "j" w) mmElems))
      (evalInt_int 0) (fun v => (n_bound hNv "i" (by decide) v).2)
      (fun v => (n_bound hNv "i" (by decide) v).1) (by simpa using hF)]
  · simp only [intRange_zero, List.flatMap_map, Int.sub_zero, Int.toNat_natCast, List.map_cons,
      List.map_nil, Gen2.flatMap_singleton_map, mmPEs]
    congr 1
    simp only [List.flatMap_def]
    congr 1
    refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
    exact pe_inst N W AccW i j hN hW hA (List.mem_range.mp hi) (List.mem_range.mp hj)
  · intro v _ _
    apply expandList2_singleton_ok
    have hv : ((mmE N W AccW).bindVal "i" v).vals.lookup "N" = some (N : Int) := by
      simp [IEnv.bindVal, List.lookup, hNv]
    rw [genN, GenItem.expand2_genFor_ascending_processes (N := (N : Int)) (evalInt_int 0)
      (fun w => (n_bound hv "j" (by decide) w).2) (fun w => (n_bound hv "j" (by decide) w).1)
      (by simpa using hF)]
    simp

theorem mm_instantiate2 (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    mmSv.pdesign.instantiate2 [(N : Int), W, AccW] (PDesign.surfaceFuel [(N : Int), W, AccW]) =
      .ok (mmSv.pdesign.assemble2 (mmEnv N W AccW) (mmDecls (N * N * W) (N * N * AccW)) mmElems
        (mmPEs N W AccW)) := by
  have hd := mm_decls N W AccW
  rw [← cast3, natAbs_pred (Nat.mul_pos (Nat.mul_pos hN hN) hW), ← cast3,
    natAbs_pred (Nat.mul_pos (Nat.mul_pos hN hN) hA)] at hd
  refine PDesign.instantiate2_of_ok rfl (mm_paramEnv _ _ _) hd (mm_elems _ _ _)
    (mm_gens N W AccW _ hN hW hA ?_)
  simp only [PDesign.surfaceFuel, List.map, List.sum_cons, List.sum_nil, Int.natAbs_natCast]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by omega) (Nat.le_mul_self _)) (Nat.le_add_right _ _)

theorem mm_processes (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    (mmSv.pdesign.instantiateD2 [(N : Int), W, AccW]).processes.toList =
      mmCtrl N W :: mmPEs N W AccW := by
  rw [PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA), PDesign.assemble2_processes,
    mm_ctrl]
  simp [mmSv.pdesign]

/-- Two PEs write disjoint windows of `C`. -/
theorem pe_disj {N W AccW i j i' j' : Nat} (h : i * N + j < i' * N + j') :
    ∀ a ∈ (mmPE N W AccW i j).procWins, ∀ b ∈ (mmPE N W AccW i' j').procWins,
      a.overlaps b = false := by
  have := rowMajor_le (K := AccW) h
  simp [mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Lhs2.drvWins]
  omega

theorem mm_driversOk (N W AccW : Nat) :
    driversOk mmSv.pdesign.declNames mmSv.pdesign.inputNames (mmCtrl N W :: mmPEs N W AccW) = true := by
  have hpe : ∀ p ∈ mmPEs N W AccW, ∃ i j, p = mmPE N W AccW i j := by
    intro p hp
    simp only [mmPEs, List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨i, -, j, -, rfl⟩ := hp
    exact ⟨i, j, rfl⟩
  apply driversOk_of_ff
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨_, _, rfl⟩
    · obtain ⟨i, j, rfl⟩ := hpe p hp; exact ⟨_, _, rfl⟩
  · simp only [List.mem_flatMap, List.mem_cons]
    rintro n ⟨p, hp | hp, hn⟩
    all_goals first | subst hp | obtain ⟨i, j, rfl⟩ := hpe p hp
    all_goals revert n; simp [mmCtrl, mmPE, Process2.procWrites, Process2.procWins, Stmt2.drvWins,
      Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins]; all_goals decide
  · refine List.Pairwise.cons (fun p hp => ?_) (pairwise_flatMap_range (fun i _ => ?_) ?_)
    · obtain ⟨i, j, rfl⟩ := hpe p hp
      simp [mmCtrl, mmPE, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins]
    · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ h => pe_disj (by omega))
    · intro i i' hii _ a ha b hb
      simp only [List.mem_map, List.mem_range] at ha hb
      obtain ⟨j, hj, rfl⟩ := ha
      obtain ⟨j', -, rfl⟩ := hb
      exact pe_disj (by have := rowMajor_le (K := N) hii; omega)

/-- **The loaded family is `mmD`**, at every `(N, W, AccW)` with positive parameters. -/
theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW) :
    mmSv.sem N W AccW = mmD N W AccW := by
  have h1 : mmSv.sem N W AccW = mmSv.pdesign.instantiateD2 [(N : Int), W, AccW] := by
    show mmSv.pdesign.instantiateGD2 [(N : Int), W, AccW] = _
    exact PDesign.instantiateGD2_of_driversOk (by rw [mm_processes N W AccW hN hW hA]; exact mm_driversOk N W AccW)
  rw [h1, PDesign.instantiateD2_of_ok (mm_instantiate2 N W AccW hN hW hA)]
  simp only [PDesign.assemble2, mm_ctrl, mmD]
  simp [mmSv.pdesign]

#print axioms mm_sem_eq
/-- **The FF-only profile at the probe points** (kernel evaluation; symbolic `N` is open). -/
theorem mm_profile_probes : (mmD 1 1 1).ffOnlyProfileB = true ∧ (mmD 2 3 5).ffOnlyProfileB = true ∧
    (mmD 3 4 8).ffOnlyProfileB = true ∧ (mmD 4 8 32).ffOnlyProfileB = true := ⟨rfl, rfl, rfl, rfl⟩

#print axioms mm_profile_probes

end SvGolf.Seq.Matmul
