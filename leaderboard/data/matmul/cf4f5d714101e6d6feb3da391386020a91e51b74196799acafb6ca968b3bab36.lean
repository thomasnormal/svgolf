-- svgolf-latency: 4
import Submission.Design
import SvGolf.Cycle

namespace Submission
open LeanModels.Sv SvGolf

def lat (N _W _AccW : Nat) : Nat := N

/-! ## 1. Mirror, disjointness, and one-driver agreement -/

sv_mirror mmG := design (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)

theorem mmG_disj (N W AccW : Nat) :
    (mmG.procs N W AccW).Pairwise ProcDisj := by
  have sepA : ∀ a b : Nat, a < b → a * AccW + AccW ≤ b * AccW := fun _ _ h => by
    have := Nat.mul_le_mul_right AccW (Nat.succ_le_of_lt h); rwa [Nat.succ_mul] at this
  simp only [mmG.procs, List.pairwise_cons]
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at hq
    rcases hq with rfl | ⟨i, -, j, -, rfl⟩ <;>
      exact ProcDisj.of_all (by simp [mmG.p0, mmG.p1, mmG.g_mem,
        Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨i, -, j, -, rfl⟩ := hq
    exact ProcDisj.of_all (by simp [mmG.p1, mmG.g_mem,
      Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
      Lhs2.drvWins, DrvWin.overlaps])
  · exact pairwise_rowMajor fun i j i' j' _ _ _ _ h => by
      have hA := sepA (i * N + j) (i' * N + j') h
      exact ProcDisj.of_all (by simp [mmG.g_mem,
        Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps] <;> omega)

theorem mm_proc_mem {N W AccW : Nat} {p : Process2} (hp : p ∈ (mmG.D N W AccW).processes.toList) :
    p = mmG.p0 N W AccW ∨ p = mmG.p1 N W AccW ∨
      ∃ i j, i < N ∧ j < N ∧ p = mmG.g_mem N W AccW i j := by
  simp only [mmG.D, List.toList_toArray, mmG.procs, List.mem_cons, List.mem_flatMap,
    List.mem_map, List.mem_range] at hp
  rcases hp with rfl | rfl | ⟨i, hi, j, hj, rfl⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr ⟨i, j, hi, hj, rfl⟩)

theorem mmG_driverWins (N W AccW : Nat) :
    driverWins design.pdesign.declNames (mmG.procs N W AccW) = [("C", none)] := by
  have hnil : ((List.range N).flatMap fun i => (List.range N).map (mmG.g_mem N W AccW i)).flatMap
      (fun p => p.drvWins.filter fun w => design.pdesign.declNames.contains w.1) = [] := by
    rw [List.flatMap_eq_nil_iff]
    intro p hp
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
    obtain ⟨i, -, j, -, rfl⟩ := hp
    simp [mmG.g_mem, Process2.drvWins]
  simp only [driverWins, mmG.procs, List.flatMap_cons, hnil, List.append_nil]
  simp [mmG.p0, mmG.p1, Process2.drvWins, Lhs2.drvWins, design.pdesign, PDesign.declNames]

theorem mmG_driversOk (N W AccW : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (mmG.procs N W AccW) = true := by
  refine SvGolf.Cycle.driversOk_of_procDisj ?_ ?_ ?_ (mmG_disj N W AccW)
  · rw [mmG_driverWins]; simp
  · intro w hw
    rw [mmG_driverWins] at hw
    simp only [List.mem_singleton] at hw; subst hw
    refine ⟨by decide, fun v hv => ?_⟩
    simp only [List.mem_flatMap] at hv
    obtain ⟨p, hp, hv⟩ := hv
    have hp' : p ∈ (mmG.D N W AccW).processes.toList := by simpa [mmG.D] using hp
    rcases mm_proc_mem hp' with rfl | rfl | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, Process2.procWins] at hv
    · revert v; simp [mmG.p1, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
        Lhs2.drvWins, DrvWin.overlaps]
    · simp [mmG.g_mem, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins] at hv
      rcases hv with rfl | rfl <;> simp [DrvWin.overlaps]
  · intro n hn
    simp only [List.mem_flatMap] at hn
    obtain ⟨p, hp, hn⟩ := hn
    have hp' : p ∈ (mmG.D N W AccW).processes.toList := by simpa [mmG.D] using hp
    rcases mm_proc_mem hp' with rfl | rfl | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, Process2.procWrites, Process2.procWins] at hn
    · revert n; simp [mmG.p1, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign, PDesign.inputNames]
    · revert n; simp [mmG.g_mem, Process2.procWrites, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
        Stmt2.drvWinsList, Lhs2.drvWins, design.pdesign, PDesign.inputNames]

theorem mm_sem_eq (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    design.sem N W AccW = mmG.D N W AccW :=
  SvGolf.Cycle.sem_eq_of_mirror
    (mmG.instantiate N W AccW hN hW hA hN32 hW32 hA32) rfl
    (mmG_driversOk N W AccW)
    (SvGolf.Cycle.aliasGuard_of_allNotComb (by
      rw [List.all_eq_true]; intro p hp
      rcases mm_proc_mem hp with rfl | rfl | ⟨i, j, -, -, rfl⟩ <;>
        simp [mmG.p0, mmG.p1, mmG.g_mem, SvGolf.Cycle.notComb]))

/-! ## 2. Closed-form single clock cycle (`cycleStep2_mixed`) -/

def St (ck r s a b dn c k bz ab bb pb : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("start", s), ("A", a), ("B", b), ("done", dn), ("C", c),
    ("k", k), ("busy", bz), ("a_bank", ab), ("b_bank", bb), ("pim_bank", pb)]

def Wd (N W AccW : Nat) (dn c k bz ab bb pb : LVec) : Prop :=
  dn.width = 1 ∧ c.width = N * N * AccW ∧ k.width = 32 ∧ bz.width = 1 ∧
  ab.width = N * N * W ∧ bb.width = N * N * W ∧ pb.width = N * N * AccW

def I (N W AccW : Nat) (st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ab bb pb,
    st = St ck r s a b dn c k bz ab bb pb ∧ Wd N W AccW dn c k bz ab bb pb

theorem apply_mm (N W AccW : Nat) (e : SvState) (ck r s a b dn c k bz ab bb pb : LVec) :
    applyInputs2 (mmG.D N W AccW) e (St ck r s a b dn c k bz ab bb pb) =
      St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn c k bz ab bb pb := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "start" <;> cases h4 : SvState.lookup e "A" <;>
    cases h5 : SvState.lookup e "B" <;>
    simp [mmG.D, mmG.decls, St, appIn, h1, h2, h3, h4, h5, SvState.set]

theorem resizeU_self (v : LVec) : v.resizeU v.width = v := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.resizeU, LVec.width, Array.getElem?_ofFn]
  by_cases hi : i < v.bits.size
  · simp [hi]
  · simp [hi]

theorem comb_run (N W AccW f : Nat) (hf : 2 ≤ f) (ck r s a b dn c k bz ab bb pb : LVec)
    (hc : c.width = pb.width) :
    runCombProcess2 f (St ck r s a b dn c k bz ab bb pb) (mmG.p0 N W AccW) =
      .ok (St ck r s a b dn pb k bz ab bb pb) := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
  simp [mmG.p0, runCombProcess2, evalExpr2, readSignal, resolveLhs2, St, SvState.lookup, SvState.set,
    hc, resizeU_self, LVec.insertAt_zero_of_width_eq]

def p1Q (N W : Nat) (r s a b dn k bz ab bb : LVec) : NbaQueue2 :=
  if r.condTrue then
    [("busy", 0, ({ bits := #[Logic.l0] } : LVec).resizeU bz.width),
     ("done", 0, ({ bits := #[Logic.l0] } : LVec).resizeU dn.width),
     ("k", 0, (LVec.ofBitVec 0#32).resizeU k.width),
     ("a_bank", 0, (LVec.ofBitVec 0#(N * N * W)).resizeU ab.width),
     ("b_bank", 0, (LVec.ofBitVec 0#(N * N * W)).resizeU bb.width)]
  else if s.condTrue then
    [("busy", 0, ({ bits := #[Logic.l1] } : LVec).resizeU bz.width),
     ("done", 0, ({ bits := #[Logic.l0] } : LVec).resizeU dn.width),
     ("k", 0, (LVec.ofBitVec 0#32).resizeU k.width),
     ("a_bank", 0, a.resizeU ab.width),
     ("b_bank", 0, b.resizeU bb.width)]
  else if bz.condTrue then
    [("busy", 0, (LVec.ofLogic (k.neLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).resizeU bz.width),
     ("done", 0, (LVec.ofLogic (k.eqLogical ((LVec.ofInt 32 (N : Int)).sub (LVec.ofInt 32 1)))).resizeU dn.width),
     ("k", 0, (k.add (LVec.ofBitVec 1#32)).resizeU k.width),
     ("a_bank", 0, (ab.shr (LVec.ofInt 32 (W : Int))).resizeU ab.width),
     ("b_bank", 0, (bb.shr ((LVec.ofInt 32 (N : Int)).mul (LVec.ofInt 32 (W : Int)))).resizeU bb.width)]
  else []

def lorCond (r s : LVec) : Bool :=
  (LVec.ofLogic
    (if (SymBinOp.lor == SymBinOp.land) = true then
      if (r.isKnownZero || s.isKnownZero) = true then Logic.l0
      else if (r.condTrue && s.condTrue) = true then Logic.l1 else Logic.lx
    else
      if (r.condTrue || s.condTrue) = true then Logic.l1
      else if (r.isKnownZero && s.isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue

def memQ (N W AccW i j : Nat) (r s bz ab bb pb : LVec) : NbaQueue2 :=
  if lorCond r s then
    [("pim_bank", (i * N + j) * AccW, (LVec.ofBitVec 0#AccW).resizeU AccW)]
  else if bz.condTrue then
    [("pim_bank", (i * N + j) * AccW,
      ((((pb.extract ((i * N + j) * AccW) AccW).resizeU (AccW + W)).add
        ((LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[ab.extract (i * N * W + W - 1) 1]),
            ab.extract (i * N * W) W]).mul
          (LVec.concatMany #[LVec.replVec AccW (LVec.concatMany #[bb.extract (j * W + W - 1) 1]),
            bb.extract (j * W) W]))).resizeU AccW).resizeU AccW)]
  else []

def allMemQ (N W AccW : Nat) (r s bz ab bb pb : LVec) : NbaQueue2 :=
  (List.range N).flatMap fun i => (List.range N).flatMap fun j =>
    memQ N W AccW i j r s bz ab bb pb

theorem p1_run (N W AccW F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ab bb pb : LVec) :
    runEdgeProcess2 F (St ck r s a b dn c k bz ab bb pb) [] (mmG.p1 N W AccW) =
      .ok (St ck r s a b dn c k bz ab bb pb, p1Q N W r s a b dn k bz ab bb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold p1Q
  by_cases h1 : r.condTrue = true <;> by_cases h2 : s.condTrue = true <;>
    by_cases h3 : bz.condTrue = true <;>
    simp [mmG.p1, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal,
      St, SvState.lookup, evalBinOp, h1, h2, h3]

theorem g_mem_run (N W AccW i j F : Nat) (hF : 30 ≤ F) (ck r s a b dn c k bz ab bb pb : LVec) :
    runEdgeProcess2 F (St ck r s a b dn c k bz ab bb pb) [] (mmG.g_mem N W AccW i j) =
      .ok (St ck r s a b dn c k bz ab bb pb, memQ N W AccW i j r s bz ab bb pb) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold memQ lorCond
  by_cases h1 : (LVec.ofLogic
    (if (SymBinOp.lor == SymBinOp.land) = true then
      if (r.isKnownZero || s.isKnownZero) = true then Logic.l0
      else if (r.condTrue && s.condTrue) = true then Logic.l1 else Logic.lx
    else
      if (r.condTrue || s.condTrue) = true then Logic.l1
      else if (r.isKnownZero && s.isKnownZero) = true then Logic.l0 else Logic.lx)).condTrue = true <;>
    by_cases h2 : bz.condTrue = true
  all_goals
    simp only [h1, h2, ↓reduceIte]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
    simp [mmG.g_mem, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, evalExprs2, resolveLhs2,
      readSignal, St, SvState.lookup, evalBinOp, h1, h2]

def mmNext (N W AccW : Nat) (ck r s a b dn k bz ab bb pb : LVec) : SvState :=
  St ck r s a b
    (nbaFold "done" (p1Q N W r s a b dn k bz ab bb) dn)
    (nbaFold "pim_bank" (allMemQ N W AccW r s bz ab bb pb) pb)
    (nbaFold "k" (p1Q N W r s a b dn k bz ab bb) k)
    (nbaFold "busy" (p1Q N W r s a b dn k bz ab bb) bz)
    (nbaFold "a_bank" (p1Q N W r s a b dn k bz ab bb) ab)
    (nbaFold "b_bank" (p1Q N W r s a b dn k bz ab bb) bb)
    (nbaFold "pim_bank" (allMemQ N W AccW r s bz ab bb pb) pb)

@[simp] theorem nbaFold_width (s : String) : ∀ (q : NbaQueue2) (v : LVec), (nbaFold s q v).width = v.width
  | [], _ => rfl
  | u :: q, v => by rw [nbaFold_cons, nbaFold_width s q]; split <;> simp

theorem nbaFold_disj (s : String) : ∀ (q : NbaQueue2) (v : LVec),
    (∀ u ∈ q, u.1 ≠ s) → nbaFold s q v = v
  | [], _, _ => rfl
  | u :: q, v, h => by
    rw [nbaFold_cons, ite_eq_right (h u List.mem_cons_self)]
    exact nbaFold_disj s q v fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem allMemQ_only_pb (N W AccW : Nat) (r s bz ab bb pb : LVec) :
    ∀ u ∈ allMemQ N W AccW r s bz ab bb pb, u.1 = "pim_bank" := by
  intro u hu
  simp only [allMemQ, List.mem_flatMap] at hu
  obtain ⟨i, -, j, -, hu⟩ := hu
  unfold memQ at hu
  by_cases h1 : lorCond r s = true
  · simp [h1] at hu; rw [hu]
  · by_cases h2 : bz.condTrue = true
    · simp [h1, h2] at hu; rw [hu]
    · simp [h1, h2] at hu

theorem commit_mm (N W AccW : Nat) (ck r s a b dn c k bz ab bb pb : LVec) :
    commitNba2 (St ck r s a b dn c k bz ab bb pb)
      (p1Q N W r s a b dn k bz ab bb ++ allMemQ N W AccW r s bz ab bb pb) =
    St ck r s a b
      (nbaFold "done" (p1Q N W r s a b dn k bz ab bb) dn)
      c
      (nbaFold "k" (p1Q N W r s a b dn k bz ab bb) k)
      (nbaFold "busy" (p1Q N W r s a b dn k bz ab bb) bz)
      (nbaFold "a_bank" (p1Q N W r s a b dn k bz ab bb) ab)
      (nbaFold "b_bank" (p1Q N W r s a b dn k bz ab bb) bb)
      (nbaFold "pim_bank" (allMemQ N W AccW r s bz ab bb pb) pb) := by
  have h1 : ∀ (q : NbaQueue2) (ck r s a b dn c k bz ab bb pb : LVec),
      (∀ u ∈ q, u.1 ∈ ["done", "k", "busy", "a_bank", "b_bank", "pim_bank"]) →
      commitNba2 (St ck r s a b dn c k bz ab bb pb) q =
        St ck r s a b
          (nbaFold "done" q dn) c (nbaFold "k" q k)
          (nbaFold "busy" q bz) (nbaFold "a_bank" q ab) (nbaFold "b_bank" q bb)
          (nbaFold "pim_bank" q pb) := by
    intro q; induction q with
    | nil => intros; rfl
    | cons u q ih =>
      intro ck r s a b dn c k bz ab bb pb hmem
      obtain ⟨n, lo, v⟩ := u
      have hn : n ∈ ["done", "k", "busy", "a_bank", "b_bank", "pim_bank"] := hmem _ List.mem_cons_self
      have hq := fun u hu => hmem u (List.mem_cons_of_mem _ hu)
      rw [commitNba2_cons]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      simp only [St] at ih
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [nbaStep, St, SvState.lookup, SvState.set, nbaFold_cons,
          ih _ _ _ _ _ _ _ _ _ _ _ _ hq]
  have hp_mem : ∀ u ∈ p1Q N W r s a b dn k bz ab bb, u.1 ∈ ["done", "k", "busy", "a_bank", "b_bank"] := by
    intro u hu; unfold p1Q at hu
    split at hu
    · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
    · split at hu
      · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
      · split at hu
        · simp at hu; rcases hu with rfl | rfl | rfl | rfl | rfl <;> simp
        · simp at hu
  have hm_mem := allMemQ_only_pb N W AccW r s bz ab bb pb
  have hall : ∀ u ∈ p1Q N W r s a b dn k bz ab bb ++ allMemQ N W AccW r s bz ab bb pb,
      u.1 ∈ ["done", "k", "busy", "a_bank", "b_bank", "pim_bank"] := by
    intro u hu
    rcases List.mem_append.mp hu with h | h
    · have := hp_mem u h; simp at this ⊢; rcases this with h | h | h | h | h <;> simp [h]
    · simp [hm_mem u h]
  rw [h1 _ _ _ _ _ _ _ _ _ _ _ _ _ hall]
  have hfold_app : ∀ s q1 q2 v, nbaFold s (q1 ++ q2) v = nbaFold s q2 (nbaFold s q1 v) := by
    intro s q1 q2 v; simp [nbaFold, List.foldl_append]
  have hp_nopb : ∀ u ∈ p1Q N W r s a b dn k bz ab bb, u.1 ≠ "pim_bank" := by
    intro u hu; have := hp_mem u hu; simp at this; rcases this with h | h | h | h | h <;> simp [h]
  simp only [hfold_app]
  rw [nbaFold_disj "done" _ _ (fun u hu => by rw [hm_mem u hu]; decide),
    nbaFold_disj "k" _ _ (fun u hu => by rw [hm_mem u hu]; decide),
    nbaFold_disj "busy" _ _ (fun u hu => by rw [hm_mem u hu]; decide),
    nbaFold_disj "a_bank" _ _ (fun u hu => by rw [hm_mem u hu]; decide),
    nbaFold_disj "b_bank" _ _ (fun u hu => by rw [hm_mem u hu]; decide),
    nbaFold_disj "pim_bank" _ _ hp_nopb]

theorem mm_cycle (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (σ : ScheduleOracle) (e : SvState) (ck r s a b dn c k bz ab bb pb : LVec)
    (hcw : c.width = N * N * AccW) (hpbw : pb.width = N * N * AccW) (kk F : Nat) (hF : 30 ≤ F) :
    ∃ kk', cycleStep2 (design.sem N W AccW) σ F e (St ck r s a b dn c k bz ab bb pb) kk =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn k bz ab bb pb, kk') := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  have hcomb := SvGolf.Cycle.combIndices_of_split (d := mmG.D N W AccW)
    (pre := []) (P := mmG.p0 N W AccW)
    (post := mmG.p1 N W AccW :: (List.range N).flatMap fun i => (List.range N).map (mmG.g_mem N W AccW i))
    (by simp [mmG.D, mmG.procs]) (by simp [mmG.p0, Process2.isCombPhase])
    rfl (by
      rw [List.all_eq_true]; intro p hp
      simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at hp
      rcases hp with rfl | ⟨i, -, j, -, rfl⟩ <;> simp [mmG.p1, mmG.g_mem, Process2.isCombPhase])
  have hset1 : ∀ j, ∃ k', combSettle2 (mmG.D N W AccW) σ F
      (applyInputs2 (mmG.D N W AccW) e (St ck r s a b dn c k bz ab bb pb)) j =
      .ok (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b)
        dn pb k bz ab bb pb, k') := by
    intro j
    rw [apply_mm]
    exact SvGolf.Cycle.combSettle2_single hcomb.1 hcomb.2 σ (K := 2) (by omega)
      (fun f hf => comb_run N W AccW f hf _ _ _ _ _ dn c k bz ab bb pb (by omega))
      (fun f hf => comb_run N W AccW f hf _ _ _ _ _ dn pb k bz ab bb pb rfl) j
  have hreset : ∀ a1 b1, (mmG.D N W AccW).resetIndices a1 b1 = [] := by
    intro a1 b1
    unfold Design2.resetIndices
    rw [List.filter_eq_nil_iff]
    intro idx hidx
    simp only [List.mem_range] at hidx
    have hget : (mmG.D N W AccW).processes[idx]? = some (mmG.D N W AccW).processes[idx] :=
      Array.getElem?_eq_getElem hidx
    have hmem : (mmG.D N W AccW).processes[idx] ∈ (mmG.D N W AccW).processes.toList :=
      Array.getElem_mem_toList hidx
    rw [hget]
    rcases mm_proc_mem hmem with h | h | ⟨i, j, -, -, h⟩ <;>
      simp [h, mmG.p0, mmG.p1, mmG.g_mem]
  have hff : ∀ (idx : Nat) (p : Process2), (mmG.D N W AccW).processes[idx]? = some p →
      p.isEdgePhase = true → ∃ clk_ b_, p = .alwaysFF clk_ b_ ∧ b_.nbaOnly = true := by
    intro idx p hp hedge
    have hmem : p ∈ (mmG.D N W AccW).processes.toList :=
      List.mem_of_getElem? (by rwa [← Array.getElem?_toList] at hp)
    rcases mm_proc_mem hmem with rfl | rfl | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, Process2.isEdgePhase] at hedge
    · exact ⟨_, _, rfl, by simp [Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly]⟩
    · exact ⟨_, _, rfl, by simp [Stmt2.nbaOnly, Stmt2.optNbaOnly, Stmt2.listNbaOnly]⟩
  have hrun : ∀ (idx : Nat) (p : Process2), (mmG.D N W AccW).processes[idx]? = some p →
      p.isEdgePhase = true →
      ∃ q, runEdgeProcess2 F (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb) [] p =
        .ok (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
          (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb, q) := by
    intro idx p hp hedge
    have hmem : p ∈ (mmG.D N W AccW).processes.toList :=
      List.mem_of_getElem? (by rwa [← Array.getElem?_toList] at hp)
    rcases mm_proc_mem hmem with rfl | rfl | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, Process2.isEdgePhase] at hedge
    · exact ⟨_, p1_run N W AccW F hF _ _ _ _ _ dn pb k bz ab bb pb⟩
    · exact ⟨_, g_mem_run N W AccW i j F hF _ _ _ _ _ dn pb k bz ab bb pb⟩
  have hd : (mmG.D N W AccW).ffDisjB = true :=
    ffDisjB_of_pairwise (by simpa [mmG.D] using (mmG_disj N W AccW).imp fun {p q} h =>
      fun a b ha a' b' hb => h (a, b) ha (a', b') hb)
  have hnd : ((St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb).map Prod.fst).Nodup := by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "a_bank", "b_bank", "pim_bank"] : List String).Nodup
    decide
  have hupd : (mmG.D N W AccW).edgeIndices.flatMap
      ((mmG.D N W AccW).ffUpd F (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb)) =
      p1Q N W (appIn e "rst" r) (appIn e "start" s) (appIn e "A" a) (appIn e "B" b) dn k bz ab bb ++
      allMemQ N W AccW (appIn e "rst" r) (appIn e "start" s) bz ab bb pb := by
    have hF1 : ∃ f, F = f + 1 := ⟨F - 1, by omega⟩
    obtain ⟨f, hFeq⟩ := hF1
    have hp0Q : SvGolf.Cycle.runQ F (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb) (mmG.p0 N W AccW) = [] := by
      rw [hFeq]; simp [SvGolf.Cycle.runQ, mmG.p0, runEdgeProcess2]
    rw [SvGolf.Cycle.flatMap_ffUpd_all]
    simp only [mmG.D, List.toList_toArray, mmG.procs, List.flatMap_cons]
    rw [hp0Q, List.nil_append]
    simp only [SvGolf.Cycle.runQ, p1_run N W AccW F hF, List.flatMap_assoc, List.flatMap_map,
      g_mem_run N W AccW _ _ F hF, allMemQ]
  have hset2 : ∀ j, ∃ k', combSettle2 (mmG.D N W AccW) σ F
      (commitNba2 (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb)
        ((mmG.D N W AccW).edgeIndices.flatMap
          ((mmG.D N W AccW).ffUpd F (St (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
            (appIn e "A" a) (appIn e "B" b) dn pb k bz ab bb pb)))) j =
      .ok (mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
        (appIn e "A" a) (appIn e "B" b) dn k bz ab bb pb, k') := by
    intro j
    rw [hupd, commit_mm]
    exact SvGolf.Cycle.combSettle2_single hcomb.1 hcomb.2 σ (K := 2) (by omega)
      (fun f hf => comb_run N W AccW f hf _ _ _ _ _ _ pb _ _ _ _ _ (by rw [nbaFold_width]))
      (fun f hf => comb_run N W AccW f hf _ _ _ _ _ _ _ _ _ _ _ _ rfl) j
  exact SvGolf.Cycle.cycleStep2_mixed σ e _ kk hset1 hreset hff hrun hd hnd hset2

/-! ## 3. Arithmetic and state transitions -/

def psum (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) : Int :=
  (List.range t).foldl (fun acc k =>
    acc + Tasks.Matmul.entry W A (i * N + k) * Tasks.Matmul.entry W B (k * N + j)) 0

def accC (N W AccW : Nat) {n : Nat} (A B : BitVec n) (t : Nat) : LVec :=
  LVec.ofBitVec (packBV AccW (N * N) fun r =>
    BitVec.ofInt AccW (psum N W A B t (r / N) (r % N)))

theorem psum_succ (N W : Nat) {n : Nat} (A B : BitVec n) (t i j : Nat) :
    psum N W A B (t + 1) i j =
      psum N W A B t i j + Tasks.Matmul.entry W A (i * N + t) * Tasks.Matmul.entry W B (t * N + j) := by
  simp [psum, List.range_succ, List.foldl_append]

theorem product_eq (N W AccW : Nat) {n : Nat} (a b : BitVec n) :
    Tasks.Matmul.product N W AccW a b =
      packBV AccW (N * N) fun r =>
        BitVec.ofInt AccW (Tasks.Matmul.dot N W a b (r / N) (r % N)) :=
  (packBV_eq_ofNat ..).symm

theorem accC_N (N W AccW : Nat) {n : Nat} (A B : BitVec n) :
    accC N W AccW A B N = LVec.ofBitVec (Tasks.Matmul.product N W AccW A B) := by
  rw [product_eq]; rfl

theorem knownBit_false_eq : knownBit false = ⟨#[.l0]⟩ := by
  symm; rw [knownBit, LVec.eq_ofBitVec_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  decide

theorem knownBit_true_eq : knownBit true = ⟨#[.l1]⟩ := by
  symm; rw [knownBit, LVec.eq_ofBitVec_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by omega
  decide

@[simp] theorem width_knownBit (b : Bool) : (knownBit b).width = 1 := by simp [knownBit]

theorem isKnownZero_knownBit (b : Bool) : (knownBit b).isKnownZero = !b := by
  cases b
  · rw [knownBit_false_eq, LVec.isKnownZero, ← Array.all_toList]; rfl
  · rw [knownBit_true_eq, LVec.isKnownZero, ← Array.all_toList]; rfl

theorem lorCond_knownBit (b1 b2 : Bool) : lorCond (knownBit b1) (knownBit b2) = (b1 || b2) := by
  unfold lorCond
  have hne : (SymBinOp.lor == SymBinOp.land) = false := by decide
  have hl0 : (LVec.ofLogic Logic.l0).condTrue = false := by simp [LVec.ofLogic, LVec.condTrue]
  have hl1 : (LVec.ofLogic Logic.l1).condTrue = true := by simp [LVec.ofLogic, LVec.condTrue]
  cases b1 <;> cases b2 <;>
    simp only [hne, condTrue_knownBit, isKnownZero_knownBit, Bool.false_eq_true, ↓reduceIte,
      Bool.not_false, Bool.or_true, Bool.or_false, Bool.and_self, hl0, hl1]

theorem lorCond_true_left (x : LVec) : lorCond (knownBit true) x = true := by
  unfold lorCond
  have hne : (SymBinOp.lor == SymBinOp.land) = false := by decide
  have hl1 : (LVec.ofLogic Logic.l1).condTrue = true := by simp [LVec.ofLogic, LVec.condTrue]
  simp only [hne, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, Bool.true_or, hl1]

theorem rowMajor_div {N i j : Nat} (hj : j < N) : (i * N + j) / N = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]

theorem flatMap_range_singleton {N : Nat} {α : Type} (f : Nat → List α) {g : Nat → α}
    (h : ∀ j, j < N → f j = [g j]) :
    (List.range N).flatMap f = (List.range N).map g := by
  rw [CombView.flatMap_congr' (fun j hj => h j (List.mem_range.mp hj))]
  induction (List.range N) with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem flatMap_range_rowMajor {N : Nat} {α : Type} {f : Nat → Nat → List α} (g : Nat → α)
    (h : ∀ i j, i < N → j < N → f i j = [g (i * N + j)]) :
    ((List.range N).flatMap fun i => (List.range N).flatMap (f i)) =
      (List.range (N * N)).map g := by
  suffices ∀ M, M ≤ N → ((List.range M).flatMap fun i => (List.range N).flatMap (f i)) =
      (List.range (M * N)).map g from this N (Nat.le_refl _)
  intro M; induction M with
  | zero => intro _; simp
  | succ M ih =>
    intro hM
    rw [List.range_succ, List.flatMap_append, ih (by omega), Nat.succ_mul, List.range_add,
      List.map_append, List.map_map]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [flatMap_range_singleton _ fun j hj => h M j (by omega) hj]
    rfl

theorem nbaFold_map_insertEntries (s : String) (AccW : Nat) (g : Nat → LVec) (n : Nat) (c : LVec) :
    nbaFold s ((List.range n).map fun r => (s, r * AccW, g r)) c = LVec.insertEntries AccW g n c := by
  unfold nbaFold LVec.insertEntries
  rw [List.foldl_map]
  simp

theorem mm_init (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    I N W AccW (initState2 (design.sem N W AccW)) := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨.xVec 1, .xVec 1, .xVec 1, .xVec (N * N * W), .xVec (N * N * W), .xVec 1,
    .xVec (N * N * AccW), .xVec 32, .xVec 1, .xVec (N * N * W), .xVec (N * N * W),
    .xVec (N * N * AccW),
    by simp [initState2, mmG.D, mmG.decls, St],
    by simp [Wd]⟩

theorem mmNext_I (N W AccW : Nat) (ck r s a b dn c k bz ab bb pb : LVec)
    (hw : Wd N W AccW dn c k bz ab bb pb) :
    I N W AccW (mmNext N W AccW ck r s a b dn k bz ab bb pb) := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hw
  exact ⟨ck, r, s, a, b, _, _, _, _, _, _, _, rfl,
    by rw [nbaFold_width, h1], by rw [nbaFold_width, h7], by rw [nbaFold_width, h3],
    by rw [nbaFold_width, h4], by rw [nbaFold_width, h5], by rw [nbaFold_width, h6],
    by rw [nbaFold_width, h7]⟩

theorem St_inj {ck r s a b dn c k bz ab bb pb ck' r' s' a' b' dn' c' k' bz' ab' bb' pb' : LVec}
    (h : St ck r s a b dn c k bz ab bb pb = St ck' r' s' a' b' dn' c' k' bz' ab' bb' pb') :
    dn = dn' ∧ c = c' ∧ k = k' ∧ bz = bz' ∧ ab = ab' ∧ bb = bb' ∧ pb = pb' := by
  simp only [St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2

theorem next_reset (N W AccW : Nat) (ck s a b dn c k bz ab bb pb : LVec)
    (hw : Wd N W AccW dn c k bz ab bb pb) :
    ∃ k' ab' bb' pb',
      mmNext N W AccW ck (knownBit true) s a b dn k bz ab bb pb =
        St ck (knownBit true) s a b (knownBit false) pb' k' (knownBit false) ab' bb' pb' ∧
      Wd N W AccW (knownBit false) pb' k' (knownBit false) ab' bb' pb' := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hw
  let qp := p1Q N W (knownBit true) s a b dn k bz ab bb
  let qm := allMemQ N W AccW (knownBit true) s bz ab bb pb
  refine ⟨nbaFold "k" qp k, nbaFold "a_bank" qp ab, nbaFold "b_bank" qp bb, nbaFold "pim_bank" qm pb, ?_, ?_⟩
  · unfold mmNext
    have hdn : nbaFold "done" qp dn = knownBit false := by
      simp [qp, p1Q, nbaFold, h1, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    have hbz : nbaFold "busy" qp bz = knownBit false := by
      simp [qp, p1Q, nbaFold, h4, LVec.resizeU_one_l0, LVec.insertAt_zero_of_width_eq]
    rw [hdn, hbz]
  · exact ⟨by simp, by rw [nbaFold_width, h7], by rw [nbaFold_width, h3], by simp,
      by rw [nbaFold_width, h5], by rw [nbaFold_width, h6], by rw [nbaFold_width, h7]⟩

theorem next_idle (N W AccW : Nat) (ck a b dn k ab bb pb : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b dn k (knownBit false) ab bb pb =
      St ck (knownBit false) (knownBit false) a b dn pb k (knownBit false) ab bb pb := by
  have hqm : allMemQ N W AccW (knownBit false) (knownBit false) (knownBit false) ab bb pb = [] := by
    unfold allMemQ
    have : ∀ i j, memQ N W AccW i j (knownBit false) (knownBit false) (knownBit false) ab bb pb = [] := by
      intro i j; simp [memQ, lorCond_knownBit]
    simp [this]
  unfold mmNext
  rw [hqm]
  simp [p1Q, nbaFold]

theorem next_start {N W AccW : Nat} (ck : LVec) (Av Bv : BitVec (N * N * W))
    (dn c k bz ab bb pb : LVec) (hw : Wd N W AccW dn c k bz ab bb pb) :
    mmNext N W AccW ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      dn k bz ab bb pb =
    St ck (knownBit false) (knownBit true) (LVec.ofBitVec Av) (LVec.ofBitVec Bv)
      (knownBit false) (accC N W AccW Av Bv 0) (LVec.ofBitVec (BitVec.ofNat 32 0)) (knownBit true)
      (LVec.ofBitVec (Av >>> (0 * W))) (LVec.ofBitVec (Bv >>> (0 * (N * W))))
      (accC N W AccW Av Bv 0) := by
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := hw
  have hqm : allMemQ N W AccW (knownBit false) (knownBit true) bz ab bb pb =
      (List.range (N * N)).map fun r =>
        ("pim_bank", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv 0 (r / N) (r % N)))) := by
    refine flatMap_range_rowMajor _ fun i j _ _ => ?_
    simp [memQ, lorCond_knownBit, LVec.resizeU_ofBitVec, BitVec.setWidth_eq, psum]
  unfold mmNext
  rw [hqm, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ h7]
  simp only [p1Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
    nbaFold, List.foldl_cons, List.foldl_nil, h1, h3, h4, h5, h6,
    LVec.resizeU_one_l0, LVec.resizeU_one_l1, LVec.resizeU_ofBitVec, BitVec.setWidth_eq,
    LVec.insertAt_zero_of_width_eq, LVec.width_ofBitVec, Nat.zero_mul, BitVec.ushiftRight_zero]
  simp [accC, LVec.insertAt_zero_of_width_eq, h1, h3, h5, h6]

theorem pe_step {N W AccW : Nat} (hW : 1 ≤ W) (Av Bv : BitVec (N * N * W))
    {t i j : Nat} (hi : i < N) (hj : j < N) :
    memQ N W AccW i j (knownBit false) (knownBit false) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      (accC N W AccW Av Bv t) =
    [("pim_bank", (i * N + j) * AccW,
      LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) ((i * N + j) / N) ((i * N + j) % N))))] := by
  have hd : (i * N + j) / N = i := rowMajor_div hj
  have hm : (i * N + j) % N = j := Nat.mul_add_mod_of_lt hj
  have hr : i * N + j < N * N := by have := Lib.rowMajor_window_le (w := 1) hi hj; simp at this; omega
  have ha : i * N * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (N := N) (w := W) (j := 0) hi (by omega); simpa using this
  have hb : j * W + W ≤ N * N * W := by
    have := Lib.rowMajor_window_le (M := N) (w := W) (i := 0) (by omega) hj; simpa using this
  have hc := Lib.rowMajor_window_le (w := AccW) hi hj
  have e1 : t * W + i * N * W = (i * N + t) * W := by rw [Nat.add_mul, Nat.add_comm]
  have e2 : t * (N * W) + j * W = (t * N + j) * W := by rw [Nat.add_mul, Nat.mul_assoc]
  simp (disch := omega) only [memQ, lorCond_knownBit, Bool.or_self, condTrue_knownBit,
    Bool.false_eq_true, ↓reduceIte, accC,
    LVec.extract_ofBitVec, extractLsb'_packBV, hd, hm, LVec.concatMany_singleton, LVec.concatMany_cons_cons,
    LVec.replVec_ofBitVec, LVec.concat_ofBitVec, LVec.ofBitVec_replicate_append_eq_signExtend hW,
    LVec.mul_ofBitVec, LVec.resizeU_ofBitVec, LVec.add_ofBitVec, BitVec.setWidth_eq,
    Lib.setWidth_add_mul_signExtend, Lib.extractLsb'_ushiftRight, e1, e2, psum_succ, BitVec.ofInt_add,
    Tasks.Matmul.entry]

theorem next_step {N W AccW : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW32 : N * W < 2 ^ 32)
    (Av Bv : BitVec (N * N * W)) {t : Nat} (ht : t < N) (ck a b : LVec) :
    mmNext N W AccW ck (knownBit false) (knownBit false) a b
      (knownBit false) (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      (accC N W AccW Av Bv t) =
    St ck (knownBit false) (knownBit false) a b
      (knownBit (decide (t + 1 = N))) (accC N W AccW Av Bv (t + 1))
      (LVec.ofBitVec (BitVec.ofNat 32 (t + 1))) (knownBit (decide (t + 1 ≠ N)))
      (LVec.ofBitVec (Av >>> ((t + 1) * W))) (LVec.ofBitVec (Bv >>> ((t + 1) * (N * W))))
      (accC N W AccW Av Bv (t + 1)) := by
  have hW' : W < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left W hN) hNW32
  have hN' : N < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right N hW) hNW32
  have hyW : (BitVec.ofNat 32 W).toNat = W := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW']
  have hyNW : (BitVec.ofNat 32 N * BitVec.ofNat 32 W).toNat = N * W := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hW',
      Nat.mod_eq_of_lt hN', Nat.mod_eq_of_lt hNW32]
  have hqm : allMemQ N W AccW (knownBit false) (knownBit false) (knownBit true)
      (LVec.ofBitVec (Av >>> (t * W))) (LVec.ofBitVec (Bv >>> (t * (N * W))))
      (accC N W AccW Av Bv t) =
      (List.range (N * N)).map fun r =>
        ("pim_bank", r * AccW, LVec.ofBitVec (BitVec.ofInt AccW (psum N W Av Bv (t + 1) (r / N) (r % N)))) :=
    flatMap_range_rowMajor _ fun i j hi hj => pe_step hW Av Bv hi hj
  unfold mmNext
  rw [hqm, nbaFold_map_insertEntries, LVec.insertEntries_ofBitVec _ _ (by simp [accC])]
  have hne : ∀ (x y : BitVec 32), (LVec.ofBitVec x).neLogical (LVec.ofBitVec y) = Logic.ofBool (!decide (x = y)) := by
    intro x y; simp [LVec.neLogical, LVec.eqLogical_ofBitVec]
  simp only [p1Q, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte,
    LVec.ofInt_eq_ofBitVec, BitVec.ofInt_natCast, BitVec.ofInt_ofNat,
    LVec.mul_ofBitVec, LVec.sub_ofBitVec, LVec.eqLogical_ofBitVec, hne,
    LVec.ofLogic_ofBool,
    Lib.ofNat_eq_ofNat_sub_one_iff ht (Nat.le_of_lt hN'),
    LVec.width_ofBitVec, LVec.shr_ofBitVec, LVec.add_ofBitVec,
    LVec.resizeU_ofBitVec, BitVec.setWidth_eq, hyW, hyNW,
    ← BitVec.shiftRight_add, BitVec.ofNat_add_ofNat, Nat.succ_mul]
  simp [nbaFold, LVec.insertAt_zero_of_width_eq, knownBit, accC]

/-! ## 4. Phase model -/

def Stp (N W AccW : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s a b dn c k bz ab bb pb,
    prev = St ck r s a b dn c k bz ab bb pb ∧
    Wd N W AccW dn c k bz ab bb pb ∧
    st = mmNext N W AccW (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "A" a) (appIn e "B" b) dn k bz ab bb pb

theorem ops_appIn {N W AccW : Nat} {e : SvState} {x : Tasks.Matmul.task.Ops (N, W, AccW)}
    (h : HoldAll e (Tasks.Matmul.task.operands (N, W, AccW)) x) (a b : LVec) :
    appIn e "A" a = LVec.ofBitVec x.1 ∧ appIn e "B" b = LVec.ofBitVec x.2.1 := by
  simp only [Tasks.Matmul.task, HoldAll] at h; simp [appIn, h.1, h.2.1]

def model (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) (hNW32 : N * W < 2 ^ 32) :
    Tasks.Matmul.task.PhaseModel (N, W, AccW) N (design.sem N W AccW) where
  Shape := I N W AccW
  Step := Stp N W AccW
  init := mm_init N W AccW hN hW hA hN32 hW32 hA32
  cycle := by
    rintro σ F e prev kk st kk' ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, hw⟩ hc
    obtain ⟨kk2, hnext⟩ := mm_cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
      ck r s a b dn c k bz ab bb pb hw.2.1 hw.2.2.2.2.2.2 kk 30 (Nat.le_refl _)
    exact ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, hw,
      (Prod.mk.inj (cycleStep2_det hc hnext)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, -, hw, rfl⟩
    exact mmNext_I N W AccW _ _ _ _ _ dn c k bz ab bb pb hw
  Ready st := ∃ ck r s a b k ab bb pb,
    st = St ck r s a b (knownBit false) pb k (knownBit false) ab bb pb ∧
    Wd N W AccW (knownBit false) pb k (knownBit false) ab bb pb
  Busy x m st := ∃ t, t + m + 1 = N ∧ ∃ ck r s a b,
    st = St ck r s a b (knownBit false) (accC N W AccW x.1 x.2.1 t)
      (LVec.ofBitVec (BitVec.ofNat 32 t)) (knownBit true)
      (LVec.ofBitVec (x.1 >>> (t * W))) (LVec.ofBitVec (x.2.1 >>> (t * (N * W))))
      (accC N W AccW x.1 x.2.1 t)
  Fin x st := ∃ ck r s a b k ab bb,
    st = St ck r s a b (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      k (knownBit false) ab bb (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1)) ∧
    Wd N W AccW (knownBit true) (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
      k (knownBit false) ab bb (LVec.ofBitVec (Tasks.Matmul.product N W AccW x.1 x.2.1))
  ready_done := by
    rintro st ⟨ck, r, s, a, b, k, ab, bb, pb, rfl, -⟩
    simp [BitIs, Tasks.Matmul.task, St, SvState.lookup]
  busy_done := by
    rintro x m st ⟨t, -, ck, r, s, a, b, rfl⟩
    simp [BitIs, Tasks.Matmul.task, St, SvState.lookup]
  fin_done := by
    rintro ⟨A, B, ⟨⟩⟩ st ⟨ck, r, s, a, b, k, ab, bb, rfl, -⟩
    simp [BitIs, HoldAll, Tasks.Matmul.task, St, SvState.lookup]
  reset := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, -, hw, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨k', ab', bb', pb', heq, hw'⟩ := next_reset N W AccW _ _ _ _ dn c k bz ab bb pb hw
    exact ⟨_, _, _, _, _, k', ab', bb', pb', heq, hw'⟩
  start := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, -, hw, rfl⟩ - hr hs hx
    obtain ⟨ha, hb⟩ := ops_appIn hx a b
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit true from BitIs.appIn_eq hs s, ha, hb]
    exact .inr ⟨N - 1, by omega, 0, by omega, _, _, _, _, _,
      next_start (appIn e "clk" ck) x.1 x.2.1 dn c k bz ab bb pb hw⟩
  busy := by
    rintro e prev st x m - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, -, rfl⟩
      ⟨t, ht, ck', r', s', a', b', hb⟩ hr hs -
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s]
    have hstep := next_step (AccW := AccW) hN hW hNW32 x.1 x.2.1 (t := t) (by omega)
      (appIn e "clk" ck) (appIn e "A" a) (appIn e "B" b)
    by_cases hf : t + 1 = N
    · left
      simp only [hf, decide_true, ne_eq, not_true_eq_false, decide_false, accC_N] at hstep
      exact ⟨_, _, _, _, _, _, _, _, hstep,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · right
      simp only [hf, decide_false, ne_eq, not_false_eq_true, decide_true] at hstep
      exact ⟨m - 1, by omega, t + 1, by omega, _, _, _, _, _, hstep⟩
  hold_ready := by
    rintro e prev st - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', ab', bb', pb', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, k, ab, bb, pb, rfl, hw⟩
  hold_fin := by
    rintro e prev st x - ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, -, rfl⟩
      ⟨ck', r', s', a', b', k', ab', bb', hb, hw⟩ hr hs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "start" s = knownBit false from BitIs.appIn_eq hs s, next_idle]
    exact ⟨_, _, _, _, _, k, ab, bb, rfl, hw⟩

/-! ## 5. Interface, discipline, and the three v2 rules -/

theorem mm_interface (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Interface (N, W, AccW) (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "A", "B", "done", "C", "k", "busy",
      "a_bank", "b_bank", "pim_bank"] : List String).Nodup
    decide⟩

theorem mm_disciplined (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    Tasks.Matmul.task.Disciplined (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨by simp [Tasks.Matmul.task, mmG.D, mmG.decls, Design2.inputNames], fun p hp => ?_⟩
  rcases mm_proc_mem hp with rfl | rfl | ⟨i, j, -, -, rfl⟩
  · simp [Tasks.Matmul.task, mmG.p0, edgeClock, asyncReset, processDataNames,
      lhsNames, exprNames, Process2.isEdgePhase]
  · simp [Tasks.Matmul.task, mmG.p1, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames]
  · simp [Tasks.Matmul.task, mmG.g_mem, edgeClock, asyncReset, processDataNames, stmtNames,
      stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames]

theorem mm_moore (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    MooreOutDep (design.sem N W AccW) [] := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine ⟨fun n => n ≠ "done" ∧ n ≠ "C" ∧ n ≠ "pim_bank", ?_, ?_, ?_⟩
  · intro n hn _
    simp [mmG.D, mmG.decls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he hsrc
    obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    rcases mm_proc_mem hp with rfl | rfl | ⟨i, j, -, -, rfl⟩
    · simp [mmG.p0, processDeps, lhsTargets, exprNames] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨r, hr, hpr⟩ := hsrc
      simp [lhsNames] at hr
      rcases hr with rfl | rfl
      · exact absurd rfl hpr.2.1
      · exact absurd rfl hpr.2.2
    · simp [mmG.p1, processDeps] at he
    · simp [mmG.g_mem, processDeps] at he
  · intro o ho
    simp [mmG.D, mmG.decls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> simp

theorem mm_powerUp (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648)
    (st : SvState) (h : PowerUp (design.sem N W AccW) st) : I N W AccW st := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32] at h
  have h' : st.map Prod.fst = (mmG.decls N W AccW).map Decl.name ∧
      ∀ b ∈ st.zip (mmG.decls N W AccW), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true := h
  rw [mmG.decls] at h'
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h'
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨s, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨a, r4, rfl, -, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨b, r5, rfl, -, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨dn, r6, rfl, w6, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨c, r7, rfl, w7, -, h7⟩ := powerUp_cons.mp h6
  obtain ⟨k, r8, rfl, w8, -, h8⟩ := powerUp_cons.mp h7
  obtain ⟨bz, r9, rfl, w9, -, h9⟩ := powerUp_cons.mp h8
  obtain ⟨ab, r10, rfl, w10, -, h10⟩ := powerUp_cons.mp h9
  obtain ⟨bb, r11, rfl, w11, -, h11⟩ := powerUp_cons.mp h10
  obtain ⟨pb, r12, rfl, w12, -, h12⟩ := powerUp_cons.mp h11
  obtain rfl := powerUp_nil.mp h12
  exact ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, w6, w7, w8, w9, w10, w11, w12⟩

theorem mm_noq (N W AccW : Nat) :
    (mmG.D N W AccW).processes.toList.any Process2.hasQualifiedCase = false := by
  rw [List.any_eq_false]
  intro p hp
  rcases mm_proc_mem hp with rfl | rfl | ⟨i, j, -, -, rfl⟩ <;>
    simp [mmG.p0, mmG.p1, mmG.g_mem, Process2.hasQualifiedCase, Stmt2.hasQualifiedCase,
      Stmt2.listHasQualifiedCase]

theorem mm_terminatesPU (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    TerminatesPU (design.sem N W AccW) := by
  refine TerminatesPU.of_invariant (I N W AccW)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32) (fun σ => ⟨30, ?_⟩)
    (by rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]; exact mm_noq N W AccW)
  rintro e _ kk ⟨ck, r, s, a, b, dn, c, k, bz, ab, bb, pb, rfl, hw⟩
  obtain ⟨kk', hnext⟩ := mm_cycle N W AccW hN hW hA hN32 hW32 hA32 σ e
    ck r s a b dn c k bz ab bb pb hw.2.1 hw.2.2.2.2.2.2 kk 30 (Nat.le_refl _)
  exact ⟨_, _, hnext, mmNext_I N W AccW _ _ _ _ _ dn c k bz ab bb pb hw⟩

theorem mm_xsafe (N W AccW : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hA : 1 ≤ AccW)
    (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hA32 : AccW < 2147483648) :
    XSafe (design.sem N W AccW) := by
  rw [mm_sem_eq N W AccW hN hW hA hN32 hW32 hA32]
  refine List.all_eq_true.mpr fun p hp => ?_
  rcases mm_proc_mem hp with rfl | rfl | ⟨i, j, hi, hj, rfl⟩
  · simp [xsProc, xsLhs, xsWidth, sigWidth, mmG.p0, mmG.D, mmG.decls]
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth, mmG.p1, mmG.D, mmG.decls,
      LVec.allKnown_l0, LVec.allKnown_l1, LVec.ofInt, LVec.allKnown_ofBitVec]
  · have hA' : i * N * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hi hN
    have hB' : j * W + W ≤ N * N * W := by simpa using Lib.rowMajor_window_le (M := N) (N := N) (w := W) hN hj
    have hA1 : i * N * W + W - 1 + 1 ≤ N * N * W := by omega
    have hB1 : j * W + W - 1 + 1 ≤ N * N * W := by omega
    have hP' : (i * N + j) * AccW + AccW ≤ N * N * AccW := Lib.rowMajor_window_le hi hj
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth,
      mmG.g_mem, mmG.D, mmG.decls, LVec.allKnown_ofBitVec, hA', hB', hA1, hB1, hP']

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W, AccW⟩ := p
  obtain ⟨hN, hN256, hW, hW127, hA, hA64⟩ :
    1 ≤ N ∧ N ≤ 256 ∧ 1 ≤ W ∧ W ≤ 127 ∧ 1 ≤ AccW ∧ AccW ≤ 64 := hp
  have hN32 : N < 2147483648 := by omega
  have hW32 : W < 2147483648 := by omega
  have hA32 : AccW < 2147483648 := by omega
  have hNW32 : N * W < 2 ^ 32 := by
    have : N * W ≤ 256 * 127 := Nat.mul_le_mul hN256 hW127
    omega
  exact Tasks.Matmul.task.satisfiedAtV2_of_phases
    (mm_interface N W AccW hN hW hA hN32 hW32 hA32)
    (mm_disciplined N W AccW hN hW hA hN32 hW32 hA32)
    (mm_terminatesPU N W AccW hN hW hA hN32 hW32 hA32) hN
    (model N W AccW hN hW hA hN32 hW32 hA32 hNW32)
    (mm_powerUp N W AccW hN hW hA hN32 hW32 hA32)
    (mm_moore N W AccW hN hW hA hN32 hW32 hA32)
    (mm_xsafe N W AccW hN hW hA hN32 hW32 hA32)

end Submission
