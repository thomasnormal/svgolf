import Submission.Design
import SvGolf.Cycle
import SvGolf.Seq
import SvGolf.React
import SvGolf.RoundRobin

namespace Submission
open LeanModels.Sv SvGolf

/-! ## 1. Mirror and agreement with `design.sem` -/

abbrev Rng32 (N : Nat) : Prop := N < 2147483648

theorem rng32_of {N : Nat} (hN : 1 ≤ N) (hNN : N * N < 2 ^ 31) : Rng32 N := by
  have := Nat.le_mul_of_pos_right N hN
  show N < 2147483648
  omega

sv_mirror arbG := design (N : Nat) (hN : 1 ≤ N) (hN32 : N < 2147483648)

theorem arb_driversOk (N : Nat) :
    driversOk design.pdesign.declNames design.pdesign.inputNames (arbG.procs N) = true := by
  simp [driversOk, driverWins, Process2.drvWins, Process2.procWins, Process2.procWrites,
    Process2.exclusive, Process2.exclClash, Process2.procWinsOn, procExclusiveOk,
    drvWinsDisjoint, DrvWin.overlaps, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList,
    Lhs2.drvWins, arbG.procs, arbG.p0, arbG.p1, arbG.p2, design.pdesign,
    PDesign.declNames, PDesign.inputNames]

theorem arb_aliasOk (N : Nat) : (arbG.D N).aliasGuard = arbG.D N :=
  SvGolf.Cycle.aliasGuard_of_allNotComb rfl

theorem arb_sem_eq (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : design.sem N = arbG.D N :=
  SvGolf.Cycle.sem_eq_of_mirror (arbG.instantiate N hN hR32) rfl (arb_driversOk N) (arb_aliasOk N)

/-! ## 2. Closed-form single cycle -/

def SS (ck r q g v m ex : LVec) : SvState :=
  [("clk", ck), ("rst", r), ("req", q), ("gnt", g), ("valid", v), ("mask", m), ("ext", ex)]

theorem apply_arb (N : Nat) (e : SvState) (ck r q g v m ex : LVec) :
    applyInputs2 (arbG.D N) e (SS ck r q g v m ex) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v m ex := by
  unfold applyInputs2
  rw [← Array.foldl_toList]
  cases h1 : SvState.lookup e "clk" <;> cases h2 : SvState.lookup e "rst" <;>
    cases h3 : SvState.lookup e "req" <;>
    simp [arbG.D, arbG.decls, SS, appIn, h1, h2, h3, SvState.set]

theorem insertAt_zero_full (v p : LVec) (h : p.width = v.width) : v.insertAt 0 p = p := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.insertAt, Array.getElem?_ofFn]
  by_cases hi : i < v.width
  · have hp : i < p.bits.size := by simp only [LVec.width] at h hi; omega
    simp only [hi, ↓reduceDIte, Array.getElem?_eq_getElem hp]
    simp [h, hi, Array.getElem?_eq_getElem hp]
  · have hp : p.bits.size ≤ i := by simp only [LVec.width] at h hi; omega
    simp only [hi, ↓reduceDIte, Array.getElem?_eq_none hp]

theorem width_resizeU' (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

def ExV (v m ex : LVec) : LVec := (LVec.concatMany #[v, m]).resizeU ex.width

def GnV (N : Nat) (g ex : LVec) : LVec :=
  ((ex.extract 1 N).and (ex.extract 0 N).not).resizeU g.width

@[simp] theorem ExV_width (v m ex : LVec) : (ExV v m ex).width = ex.width := width_resizeU' _ _
@[simp] theorem GnV_width (N : Nat) (g ex : LVec) : (GnV N g ex).width = g.width := width_resizeU' _ _

theorem p0_run (N F : Nat) (hF : 10 ≤ F) (ck r q g v m ex : LVec) :
    runCombProcess2 F (SS ck r q g v m ex) (arbG.p0 N) =
      .ok (SS ck r q g v m (ExV v m ex)) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  simp [arbG.p0, ExV, LVec.concatMany, runCombProcess2, evalExpr2, evalExprs2, resolveLhs2,
    readSignal, SS, SvState.lookup, SvState.set, insertAt_zero_full]

theorem p1_run (N F : Nat) (hN : 1 ≤ N) (hF : 10 ≤ F) (ck r q g v m ex : LVec) :
    runCombProcess2 F (SS ck r q g v m ex) (arbG.p1 N) =
      .ok (SS ck r q (GnV N g ex) v m ex) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 10 := ⟨F - 10, by omega⟩
  have hmin : (min (↑N : Int) 1).toNat = 1 := by omega
  simp [arbG.p1, GnV, hmin, runCombProcess2, evalExpr2, resolveLhs2, readSignal,
    SS, SvState.lookup, SvState.set, insertAt_zero_full]

theorem perm_01 {l : List Nat} (h : l.Perm [0, 1]) :
    l = [0, 1] ∨ l = [1, 0] := by
  have hlen : l.length = 2 := h.length_eq
  match l with
  | [x, y] =>
    have hx : x ∈ [0, 1] := h.subset (by simp)
    have hy : y ∈ [0, 1] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd (h.count_eq 1) (by decide)
    · exact .inl rfl
    · exact .inr rfl
    · exact absurd (h.count_eq 0) (by decide)
  | [] | [_] | _ :: _ :: _ :: _ => simp at hlen

def combS (N : Nat) (ck r q g v m ex : LVec) : SvState :=
  SS ck r q (GnV N g (ExV v m ex)) v m (ExV v m ex)

theorem settle_arb (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (F k : Nat) (hF : 20 ≤ F)
    (ck r q g v m ex : LVec) :
    ∃ k', combSettle2 (arbG.D N) σ F (SS ck r q g v m ex) k =
      .ok (combS N ck r q g v m ex, k') := by
  have hci : (arbG.D N).combIndices = [0, 1] := rfl
  have hp0 : (arbG.D N).processes[0]? = some (arbG.p0 N) := rfl
  have hp1 : (arbG.D N).processes[1]? = some (arbG.p1 N) := rfl
  have hpass01 : ∀ f', 10 ≤ f' → ∀ ck r q g v m ex,
      combPass2 (arbG.D N) f' (SS ck r q g v m ex) [0, 1] = .ok (combS N ck r q g v m ex) := by
    intro f' hf' ck r q g v m ex
    simp only [combPass2, hp0, hp1, p0_run N f' hf', p1_run N f' hN hf', Res.ok_bind, combS]
  have hpass10 : ∀ f', 10 ≤ f' → ∀ ck r q g v m ex,
      combPass2 (arbG.D N) f' (SS ck r q g v m ex) [1, 0] =
        .ok (SS ck r q (GnV N g ex) v m (ExV v m ex)) := by
    intro f' hf' ck r q g v m ex
    simp only [combPass2, hp0, hp1, p0_run N f' hf', p1_run N f' hN hf', Res.ok_bind]
  have hpass_any : ∀ f', 10 ≤ f' → ∀ ck r q g v m ex j,
      combPass2 (arbG.D N) f' (SS ck r q g v m ex) (σ.choose j (arbG.D N).combIndices) =
        .ok (combS N ck r q g v m ex) ∨
      combPass2 (arbG.D N) f' (SS ck r q g v m ex) (σ.choose j (arbG.D N).combIndices) =
        .ok (SS ck r q (GnV N g ex) v m (ExV v m ex)) := by
    intro f' hf' ck r q g v m ex j
    have hperm := σ.choose_perm j (arbG.D N).combIndices
    rw [hci] at hperm
    rcases perm_01 hperm with h | h
    · rw [hci, h]; exact .inl (hpass01 f' hf' ck r q g v m ex)
    · rw [hci, h]; exact .inr (hpass10 f' hf' ck r q g v m ex)
  have hfix : ∀ f', 10 ≤ f' → ∀ j,
      combPass2 (arbG.D N) f' (combS N ck r q g v m ex) (σ.choose j (arbG.D N).combIndices) =
        .ok (combS N ck r q g v m ex) := by
    intro f' hf' j
    unfold combS
    have hperm := σ.choose_perm j (arbG.D N).combIndices
    rw [hci] at hperm
    rcases perm_01 hperm with h | h
    · rw [hci, h, hpass01 f' hf']; simp only [combS, ExV, GnV, width_resizeU']
    · rw [hci, h, hpass10 f' hf']; simp only [ExV, GnV, width_resizeU']
  have hstep2 : ∀ f', 10 ≤ f' → ∀ j,
      combPass2 (arbG.D N) f' (SS ck r q (GnV N g ex) v m (ExV v m ex))
        (σ.choose j (arbG.D N).combIndices) = .ok (combS N ck r q g v m ex) := by
    intro f' hf' j
    have hperm := σ.choose_perm j (arbG.D N).combIndices
    rw [hci] at hperm
    rcases perm_01 hperm with h | h
    · rw [hci, h, hpass01 f' hf']; simp only [combS, ExV, GnV, width_resizeU']
    · rw [hci, h, hpass10 f' hf']; simp only [combS, ExV, GnV, width_resizeU']
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 20 := ⟨F - 20, by omega⟩
  rw [combSettle2.eq_2]
  rcases hpass_any (f + 19) (by omega) ck r q g v m ex k with h1 | h1
  · rw [h1]; simp only [Res.ok_bind]
    by_cases hb : (combS N ck r q g v m ex == SS ck r q g v m ex) = true
    · simp only [hb, ite_true]; exact ⟨k + 1, rfl⟩
    · simp only [hb]
      rw [combSettle2.eq_2, hfix (f + 18) (by omega)]
      simp only [Res.ok_bind, beq_self_eq_true, ite_true]; exact ⟨k + 2, rfl⟩
  · rw [h1]; simp only [Res.ok_bind]
    by_cases hb : (SS ck r q (GnV N g ex) v m (ExV v m ex) == SS ck r q g v m ex) = true
    · have heq : SS ck r q (GnV N g ex) v m (ExV v m ex) = SS ck r q g v m ex := eq_of_beq hb
      have hex : ExV v m ex = ex := by
        simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at heq
        exact heq.2
      simp only [hb, ite_true]
      refine ⟨k + 1, ?_⟩
      simp only [combS, hex]
    · simp only [hb]
      rw [combSettle2.eq_2, hstep2 (f + 18) (by omega)]
      simp only [Res.ok_bind]
      by_cases hb2 : (combS N ck r q g v m ex == SS ck r q (GnV N g ex) v m (ExV v m ex)) = true
      · simp only [hb2, ite_true]; exact ⟨k + 2, rfl⟩
      · simp only [hb2]
        rw [combSettle2.eq_2, hfix (f + 17) (by omega)]
        simp only [Res.ok_bind, beq_self_eq_true, ite_true]; exact ⟨k + 3, rfl⟩

def nextMaskV (N : Nat) (q m : LVec) : LVec :=
  LVec.ternary (.ofLogic ((q.and m).neLogical (LVec.ofBitVec 0#N)))
    (((q.and m).xor ((q.and m).sub (({ bits := #[Logic.l1] } : LVec).resizeU N))).not)
    ((q.xor (q.sub (({ bits := #[Logic.l1] } : LVec).resizeU N))).not)

def ffQ (N : Nat) (r q v m : LVec) : NbaQueue2 :=
  if r.condTrue then
    [("valid", 0, ({ bits := #[Logic.l0] } : LVec).resizeU v.width),
     ("mask", 0, (LVec.ofBitVec 0#N).resizeU m.width)]
  else
    [("valid", 0, (LVec.ofLogic (q.neLogical (LVec.ofBitVec 0#N))).resizeU v.width),
     ("mask", 0, (nextMaskV N q m).resizeU m.width)]

theorem p2_run (N F : Nat) (hF : 30 ≤ F) (ck r q g v m ex : LVec) :
    runEdgeProcess2 F (SS ck r q g v m ex) [] (arbG.p2 N) =
      .ok (SS ck r q g v m ex, ffQ N r q v m) := by
  obtain ⟨f, rfl⟩ : ∃ f, F = f + 30 := ⟨F - 30, by omega⟩
  unfold ffQ nextMaskV
  by_cases h1 : r.condTrue = true <;>
    simp [arbG.p2, runEdgeProcess2, execStmt2, execStmts2, evalExpr2, resolveLhs2, readSignal,
      SS, SvState.lookup, evalBinOp, h1]

def Vv (N : Nat) (r q v : LVec) : LVec :=
  if r.condTrue then ({ bits := #[Logic.l0] } : LVec).resizeU v.width
  else (LVec.ofLogic (q.neLogical (LVec.ofBitVec 0#N))).resizeU v.width

def Mv (N : Nat) (r q m : LVec) : LVec :=
  if r.condTrue then (LVec.ofBitVec 0#N).resizeU m.width
  else (nextMaskV N q m).resizeU m.width

@[simp] theorem Vv_width (N : Nat) (r q v : LVec) : (Vv N r q v).width = v.width := by
  unfold Vv; split <;> exact width_resizeU' _ _

@[simp] theorem Mv_width (N : Nat) (r q m : LVec) : (Mv N r q m).width = m.width := by
  unfold Mv; split <;> exact width_resizeU' _ _

theorem commit_ff (N : Nat) (ck r q g v m ex : LVec) :
    commitNba2 (SS ck r q g v m ex) (ffQ N r q v m) =
      SS ck r q g (Vv N r q v) (Mv N r q m) ex := by
  unfold ffQ Vv Mv
  by_cases h1 : r.condTrue = true <;>
    simp [h1, commitNba2, SS, SvState.lookup, SvState.set, insertAt_zero_full]

def arbNext (N : Nat) (e : SvState) (ck r q g v m ex : LVec) : SvState :=
  combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
    (GnV N g (ExV v m ex)) (Vv N (appIn e "rst" r) (appIn e "req" q) v)
    (Mv N (appIn e "rst" r) (appIn e "req" q) m) (ExV v m ex)

theorem arb_cycle (N : Nat) (hN : 1 ≤ N) (σ : ScheduleOracle) (e : SvState)
    (ck r q g v m ex : LVec) (kk F : Nat) (hF : 64 ≤ F) :
    ∃ k', cycleStep2 (arbG.D N) σ F e (SS ck r q g v m ex) kk =
      .ok (arbNext N e ck r q g v m ex, k') := by
  have hF' : 20 ≤ F := by omega
  obtain ⟨k1, h1⟩ := settle_arb N hN σ F kk hF' (appIn e "clk" ck) (appIn e "rst" r)
    (appIn e "req" q) g v m ex
  obtain ⟨k2, h2⟩ := settle_arb N hN σ F (k1 + 1) hF' (appIn e "clk" ck) (appIn e "rst" r)
    (appIn e "req" q) (GnV N g (ExV v m ex))
    (Vv N (appIn e "rst" r) (appIn e "req" q) v)
    (Mv N (appIn e "rst" r) (appIn e "req" q) m) (ExV v m ex)
  have hE : edgePass2 (arbG.D N) F
      (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v m ex) []
      (σ.choose k1 (arbG.D N).edgeIndices) =
      .ok (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v m ex,
        ffQ N (appIn e "rst" r) (appIn e "req" q) v m) := by
    have hchoose : σ.choose k1 (arbG.D N).edgeIndices = [2] :=
      List.perm_singleton.mp (σ.choose_perm k1 [2])
    rw [hchoose]
    simp only [edgePass2, combS, show (arbG.D N).processes[2]? = some (arbG.p2 N) from rfl,
      p2_run N F (by omega), Res.ok_bind]
  have hC : commitNba2 (combS N (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q) g v m ex)
      (ffQ N (appIn e "rst" r) (appIn e "req" q) v m) =
      SS (appIn e "clk" ck) (appIn e "rst" r) (appIn e "req" q)
        (GnV N g (ExV v m ex)) (Vv N (appIn e "rst" r) (appIn e "req" q) v)
        (Mv N (appIn e "rst" r) (appIn e "req" q) m) (ExV v m ex) :=
    commit_ff N _ _ _ _ v m _
  have hre : ∀ a b, (arbG.D N).resetIndices a b = [] := fun _ _ => rfl
  refine ⟨k2, ?_⟩
  simp only [cycleStep2, apply_arb, h1, Res.ok_bind, Res.pure_eq, hre, hE, hC, h2]
  rfl

/-! ## 3. Shape invariant -/

def Shp (N : Nat) (st : SvState) : Prop :=
  ∃ ck r q g v m ex, st = SS ck r q g v m ex ∧
    g.width = N ∧ v.width = 1 ∧ m.width = N ∧ ex.width = N + 1

theorem width_xVec (w : Nat) : (LVec.xVec w).width = w := by
  simp [LVec.xVec, LVec.replicate, LVec.width]

theorem arb_init (N : Nat) : Shp N (initState2 (arbG.D N)) :=
  ⟨LVec.xVec 1, LVec.xVec 1, LVec.xVec N, LVec.xVec N, LVec.xVec 1, LVec.xVec N, LVec.xVec (N + 1),
    rfl, width_xVec N, width_xVec 1, width_xVec N, width_xVec (N + 1)⟩

theorem arbNext_shp {N : Nat} {e : SvState} {ck r q g v m ex : LVec}
    (hg : g.width = N) (hv : v.width = 1) (hm : m.width = N) (hex : ex.width = N + 1) :
    Shp N (arbNext N e ck r q g v m ex) :=
  ⟨_, _, _, _, _, _, _, rfl, by simp [hg], by simp [hv], by simp [hm], by simp [hex]⟩

def Stp (N : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r q g v m ex, prev = SS ck r q g v m ex ∧
    (g.width = N ∧ v.width = 1 ∧ m.width = N ∧ ex.width = N + 1) ∧
    st = arbNext N e ck r q g v m ex

/-! ## 4. BitVec arithmetic for thermometer mask and grant decoding -/

theorem carry_sub_one_iff {w : Nat} (s : BitVec w) :
    ∀ i, i < w → ((s ^^^ (s - 1#w)).getLsbD i = true ↔ ∀ j, j < i → s.getLsbD j = false) := by
  generalize ht : s - 1#w = t
  have hs : s = t + 1#w := by rw [← ht]; exact (BitVec.sub_add_cancel s 1#w).symm
  have hlow : ∀ n, n ≤ w →
      ((∀ j, j < n → s.getLsbD j = false) ↔ (∀ j, j < n → t.getLsbD j = true)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn' : n ≤ w := by omega
      have hbit : s.getLsbD n = (t.getLsbD n ^^ (if n = 0 then true else BitVec.carry n t 1#w false)) := by
        rw [hs, BitVec.getLsbD_add (by omega : n < w)]
        cases n with
        | zero => simp [BitVec.carry_zero, show (1#w).getLsbD 0 = true from by simp [show 0 < w by omega]]
        | succ m =>
          have h1m : (1#w).getLsbD (m + 1) = false := by simp
          simp [h1m]
      constructor
      · intro h j hj
        have hprev : ∀ m, m < n → t.getLsbD m = true :=
          (ih hn').mp (fun m hm => h m (by omega))
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | hjeq
        · exact hprev j hlt
        · rw [hjeq]
          have hsn : s.getLsbD n = false := h n (Nat.lt_succ_self n)
          rw [hbit] at hsn
          cases n with
          | zero => simp at hsn; exact hsn
          | succ m =>
            have hc : BitVec.carry (m + 1) t 1#w false = true := by
              rw [BitVec.carry_succ_one _ _ (by omega), decide_eq_true_iff]
              intro k hk; simp [hprev k (by omega)]
            simp [hc] at hsn; exact hsn
      · intro h j hj
        have hprev : ∀ m, m < n → s.getLsbD m = false :=
          (ih hn').mpr (fun m hm => h m (by omega))
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | hjeq
        · exact hprev j hlt
        · rw [hjeq, hbit, h n (Nat.lt_succ_self n)]
          cases n with
          | zero => rfl
          | succ m =>
            have hc : BitVec.carry (m + 1) t 1#w false = true := by
              rw [BitVec.carry_succ_one _ _ (by omega), decide_eq_true_iff]
              intro k hk; simp [h k (by omega)]
            simp [hc]
  intro i hi
  rw [BitVec.getLsbD_xor, hlow i (Nat.le_of_lt hi)]
  cases i with
  | zero =>
    have hs0 : s.getLsbD 0 = !t.getLsbD 0 := by
      rw [hs, BitVec.getLsbD_add hi, BitVec.carry_zero]
      simp [hi]
    rw [hs0]; cases t.getLsbD 0 <;> simp
  | succ m =>
    have hsm : s.getLsbD (m + 1) = (t.getLsbD (m + 1) ^^ BitVec.carry (m + 1) t 1#w false) := by
      rw [hs, BitVec.getLsbD_add hi]; simp
    rw [hsm]
    have hxor : ∀ a b : Bool, ((a ^^ b) ^^ a) = b := by decide
    rw [hxor, BitVec.carry_succ_one _ _ (by omega), decide_eq_true_iff]
    constructor <;> (intro h j hj; exact h j (by omega))

theorem not_xor_sub_one_zero {w : Nat} : ~~~((0#w) ^^^ ((0#w) - 1#w)) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and,
    Bool.not_eq_false']
  exact (carry_sub_one_iff (0#w) i hi).mpr (fun j _ => BitVec.getLsbD_zero)

theorem not_xor_sub_one_of_isLow {w k : Nat} {s : BitVec w} (hk : RoundRobin.IsLow s k) :
    ~~~(s ^^^ (s - 1#w)) = ~~~((BitVec.twoPow w k <<< 1) - 1#w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [RoundRobin.getLsbD_thermo hk.lt, BitVec.getLsbD_not]
  by_cases hki : k < i
  · have hfalse : (s ^^^ (s - 1#w)).getLsbD i = false := by
      cases hb : (s ^^^ (s - 1#w)).getLsbD i
      · rfl
      · have := (carry_sub_one_iff s i hi).mp hb k hki
        exact absurd (hk.1.symm.trans this) (by decide)
    rw [hfalse]; simp [hi, hki]
  · have htrue : (s ^^^ (s - 1#w)).getLsbD i = true :=
      (carry_sub_one_iff s i hi).mpr fun j hj => hk.2 j (by omega)
    rw [htrue]; simp [hi, hki]

def arbMask {w : Nat} (x m : BitVec w) : BitVec w :=
  if x &&& m = 0#w then ~~~(x ^^^ (x - 1#w)) else ~~~((x &&& m) ^^^ ((x &&& m) - 1#w))

theorem arbMask_eq_zero {w : Nat} (m : BitVec w) : arbMask 0#w m = 0#w := by
  unfold arbMask
  simp only [BitVec.zero_and, ↓reduceIte]
  exact not_xor_sub_one_zero

theorem arbMask_eq_next {w : Nat} {x m : BitVec w} (hx : x ≠ 0#w) :
    arbMask x m = RoundRobin.next x m := by
  have hs : RoundRobin.sel x m ≠ 0#w := fun h => hx (RoundRobin.sel_eq_zero.1 h)
  obtain ⟨k, hk⟩ := RoundRobin.exists_isLow hs
  have hpk : RoundRobin.pick x m = BitVec.twoPow w k := by
    rw [RoundRobin.pick_eq_isolate, RoundRobin.isolate_eq_twoPow hk]
  have hpne : RoundRobin.pick x m ≠ 0#w := fun h => hx (RoundRobin.pick_eq_zero.1 h)
  simp only [RoundRobin.next, hpne, ↓reduceIte]
  rw [hpk]
  unfold arbMask
  unfold RoundRobin.sel at hk
  by_cases hm : x &&& m = 0#w
  · simp only [hm, ↓reduceIte] at hk ⊢; exact not_xor_sub_one_of_isLow hk
  · simp only [hm, ↓reduceIte] at hk ⊢; exact not_xor_sub_one_of_isLow hk

theorem thermo_zero (w : Nat) : RoundRobin.Thermo (0#w) w :=
  ⟨Nat.le_refl w, fun i hi => by simp [Nat.not_le.mpr hi]⟩

def decGnt {N : Nat} (v : Bool) (mk : BitVec N) : BitVec N :=
  ((BitVec.ofBool v ++ mk).extractLsb' 1 N) &&& ~~~mk

theorem decGnt_false_zero {N : Nat} : decGnt false (0#N) = 0#N := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [decGnt, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true, Bool.true_and, Bool.not_false,
    Bool.and_true]
  by_cases h : 1 + i < N <;> simp [h]

theorem decGnt_pick {N : Nat} (x mk : BitVec N) :
    decGnt (decide (x ≠ 0#N)) (arbMask x mk) = RoundRobin.pick x mk := by
  by_cases hx : x = 0#N
  · subst hx
    simp only [ne_eq, not_true_eq_false, decide_false, arbMask_eq_zero, decGnt_false_zero]
    exact (RoundRobin.pick_eq_zero.2 rfl).symm
  · have hs : RoundRobin.sel x mk ≠ 0#N := fun h => hx (RoundRobin.sel_eq_zero.1 h)
    obtain ⟨k, hk⟩ := RoundRobin.exists_isLow hs
    have hpk : RoundRobin.pick x mk = BitVec.twoPow N k := by
      rw [RoundRobin.pick_eq_isolate, RoundRobin.isolate_eq_twoPow hk]
    have hmk : arbMask x mk = ~~~((BitVec.twoPow N k <<< 1) - 1#N) := by
      rw [arbMask_eq_next hx]
      have hpne : RoundRobin.pick x mk ≠ 0#N := fun h => hx (RoundRobin.pick_eq_zero.1 h)
      simp only [RoundRobin.next, hpne, ↓reduceIte]
      rw [hpk]
    rw [hpk, hmk, show decide (x ≠ 0#N) = true from decide_eq_true hx]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [decGnt, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
      BitVec.getLsbD_not, BitVec.getLsbD_twoPow, hi, decide_true, Bool.true_and,
      RoundRobin.getLsbD_thermo hk.lt]
    by_cases h1 : 1 + i < N
    · simp only [h1, ↓reduceIte]
      by_cases hik : k = i
      · subst hik; simp [hi]
      · by_cases hlt : k < i <;> simp [hik, hlt] <;> omega
    · have hiN : i + 1 = N := by omega
      have hki : k ≤ i := by have := hk.lt; omega
      have h0 : 1 + i - N = 0 := by omega
      simp only [h1, ↓reduceIte, h0, BitVec.getLsbD_ofBool, decide_true, Bool.true_and]
      by_cases hik : k = i
      · subst hik; simp [hi]
      · have hlt : k < i := by omega
        simp [hik, hlt]

theorem arb_step {N : Nat} {x mk : BitVec N} {e : Nat} (hm : RoundRobin.Thermo mk e) :
    ∃ e', RoundRobin.Thermo (arbMask x mk) e' ∧
      ∀ i, i < N → x.getLsbD i = true → (RoundRobin.pick x mk).getLsbD i = false →
        RoundRobin.dist N e' i < RoundRobin.dist N e i := by
  by_cases hx : x = 0#N
  · subst hx
    refine ⟨N, ?_, fun i _ hi _ => ?_⟩
    · rw [arbMask_eq_zero]; exact thermo_zero N
    · rw [BitVec.getLsbD_zero] at hi; exact absurd hi (by decide)
  · rw [arbMask_eq_next hx]
    exact RoundRobin.step hm

/-! ## 5. Evaluation of `arbNext` on known values -/

theorem one_resize {N : Nat} :
    (({ bits := #[Logic.l1] } : LVec)).resizeU N = LVec.ofBitVec (1#N) := by
  have h : ({ bits := #[Logic.l1] } : LVec) = LVec.ofBitVec (BitVec.ofBool true) := LVec.ofLogic_l1
  rw [h, LVec.resizeU_ofBitVec]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem ExV_val {N : Nat} (v : Bool) (mk : BitVec N) (ex : LVec) (hex : ex.width = N + 1) :
    ExV (knownBit v) (LVec.ofBitVec mk) ex = LVec.ofBitVec (BitVec.ofBool v ++ mk) := by
  have hcat : LVec.concatMany #[knownBit v, LVec.ofBitVec mk] =
      LVec.ofBitVec (BitVec.ofBool v ++ mk) := by
    have hkv : knownBit v = LVec.ofBitVec (BitVec.ofBool v) := rfl
    rw [hkv]
    simpa [LVec.concatMany, LVec.concat] using LVec.concat_ofBitVec (BitVec.ofBool v) mk
  unfold ExV
  rw [hcat, hex, LVec.resizeU_ofBitVec]
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.getElem?_ofBitVec]
  by_cases h1 : i < N + 1
  · have h2 : i < 1 + N := by omega
    simp [h1, h2]
  · have h2 : ¬ i < 1 + N := by omega
    simp [h1, h2]

theorem GnV_val {N : Nat} (v : Bool) (mk : BitVec N) (g : LVec) (hg : g.width = N) :
    GnV N g (LVec.ofBitVec (BitVec.ofBool v ++ mk)) = LVec.ofBitVec (decGnt v mk) := by
  have h1 : 1 + N ≤ 1 + N := Nat.le_refl _
  have h0 : 0 + N ≤ 1 + N := by omega
  have hex0 : (BitVec.ofBool v ++ mk).extractLsb' 0 N = mk := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_append, hi]
  unfold GnV decGnt
  rw [LVec.extract_ofBitVec _ h1, LVec.extract_ofBitVec _ h0, hex0,
    LVec.not_ofBitVec, LVec.and_ofBitVec, hg, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem Vv_reset {N : Nat} {v : LVec} (q : LVec) (hv : v.width = 1) :
    Vv N (knownBit true) q v = knownBit false := by
  simp [Vv, hv, LVec.resizeU_one_l0, knownBit]

theorem Mv_reset {N : Nat} {m : LVec} (q : LVec) (hm : m.width = N) :
    Mv N (knownBit true) q m = LVec.ofBitVec 0#N := by
  simp [Mv, hm]

theorem Vv_run {N : Nat} {v : LVec} (x : BitVec N) (hv : v.width = 1) :
    Vv N (knownBit false) (LVec.ofBitVec x) v = knownBit (decide (x ≠ 0#N)) := by
  simp only [Vv, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, hv]
  have hne : (LVec.ofBitVec x).neLogical (LVec.ofBitVec 0#N) = Logic.ofBool (decide (x ≠ 0#N)) := by
    simp only [LVec.neLogical, LVec.eqLogical_ofBitVec]
    by_cases h : x = 0#N <;> simp [h, Logic.not]
  rw [hne, LVec.ofLogic_ofBool, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem Mv_run {N : Nat} (x mk : BitVec N) :
    Mv N (knownBit false) (LVec.ofBitVec x) (LVec.ofBitVec mk) = LVec.ofBitVec (arbMask x mk) := by
  simp only [Mv, nextMaskV, arbMask, condTrue_knownBit, Bool.false_eq_true, ↓reduceIte, one_resize]
  by_cases h : x &&& mk = 0#N <;>
    simp [h, LVec.and_ofBitVec, LVec.sub_ofBitVec, LVec.xor_ofBitVec, LVec.not_ofBitVec,
      LVec.neLogical, LVec.eqLogical_ofBitVec, LVec.ternary, LVec.ofLogic, Logic.not,
      LVec.condTrue, LVec.isKnownZero, LVec.resizeU_ofBitVec, BitVec.setWidth_eq]

theorem arbNext_reset {N : Nat} {e : SvState} {ck r q g v m ex : LVec} {x : BitVec N}
    (hb : BitIs e "rst" true) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hg : g.width = N) (hv : v.width = 1) (hm : m.width = N) (hex : ex.width = N + 1) :
    arbNext N e ck r q g v m ex =
      SS (appIn e "clk" ck) (knownBit true) (LVec.ofBitVec x)
        (LVec.ofBitVec (decGnt false 0#N)) (knownBit false) (LVec.ofBitVec 0#N)
        (LVec.ofBitVec (BitVec.ofBool false ++ 0#N)) := by
  have hr : appIn e "rst" r = knownBit true := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  unfold arbNext combS
  rw [hr, hq', Vv_reset _ hv, Mv_reset _ hm,
    ExV_val false 0#N (ExV v m ex) (by rw [ExV_width, hex]),
    GnV_val false 0#N (GnV N g (ExV v m ex)) (by rw [GnV_width, hg])]

theorem arbNext_run {N : Nat} {e : SvState} {ck r q g v m ex : LVec} {x mk : BitVec N}
    (hb : BitIs e "rst" false) (hq : SvState.lookup e "req" = some (LVec.ofBitVec x))
    (hm : m = LVec.ofBitVec mk) (hg : g.width = N) (hv : v.width = 1) (hex : ex.width = N + 1) :
    arbNext N e ck r q g v m ex =
      SS (appIn e "clk" ck) (knownBit false) (LVec.ofBitVec x)
        (LVec.ofBitVec (decGnt (decide (x ≠ 0#N)) (arbMask x mk)))
        (knownBit (decide (x ≠ 0#N))) (LVec.ofBitVec (arbMask x mk))
        (LVec.ofBitVec (BitVec.ofBool (decide (x ≠ 0#N)) ++ arbMask x mk)) := by
  subst hm
  have hr : appIn e "rst" r = knownBit false := BitIs.appIn_eq hb r
  have hq' : appIn e "req" q = LVec.ofBitVec x := by simp only [appIn, hq, Option.getD_some]
  unfold arbNext combS
  rw [hr, hq', Vv_run x hv, Mv_run x mk,
    ExV_val _ _ (ExV v (LVec.ofBitVec mk) ex) (by rw [ExV_width, hex]),
    GnV_val _ _ (GnV N g (ExV v (LVec.ofBitVec mk) ex)) (by rw [GnV_width, hg])]

/-! ## 5. Rank model -/

def bvOf (N : Nat) (n : String) (st : SvState) : BitVec N :=
  BitVec.ofNat N ((SvState.lookup st n).getD (LVec.xVec N)).toNat

theorem bvOf_gnt {N : Nat} {ck r q v m ex : LVec} {g : BitVec N} :
    bvOf N "gnt" (SS ck r q (LVec.ofBitVec g) v m ex) = g := by
  simp [bvOf, SS, SvState.lookup, BitVec.ofNat_toNat]

theorem bvOf_mask {N : Nat} {ck r q g v ex : LVec} {mk : BitVec N} :
    bvOf N "mask" (SS ck r q g v (LVec.ofBitVec mk) ex) = mk := by
  simp [bvOf, SS, SvState.lookup, BitVec.ofNat_toNat]

theorem SS_mask {ck r q g v m ex ck' r' q' g' v' m' ex' : LVec}
    (h : SS ck r q g v m ex = SS ck' r' q' g' v' m' ex') : m = m' := by
  simp only [SS, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact h.2.2.2.2.2.1

open Classical in
noncomputable def edgeOf {N : Nat} (mk : BitVec N) : Nat :=
  if h : ∃ e, RoundRobin.Thermo mk e then Classical.choose h else 0

theorem edgeOf_eq {N : Nat} {mk : BitVec N} {e : Nat} (h : RoundRobin.Thermo mk e) :
    edgeOf mk = e := by
  have hex : ∃ e, RoundRobin.Thermo mk e := ⟨e, h⟩
  simp only [edgeOf, hex, ↓reduceDIte]
  exact (Classical.choose_spec hex).unique h

def ArbInv (N : Nat) (st : SvState) : Prop :=
  ∃ (ck : LVec) (b v : Bool) (x mk : BitVec N) (e : Nat),
    st = SS ck (knownBit b) (LVec.ofBitVec x) (LVec.ofBitVec (decGnt v mk)) (knownBit v)
      (LVec.ofBitVec mk) (LVec.ofBitVec (BitVec.ofBool v ++ mk)) ∧
    RoundRobin.Thermo mk e

theorem pick_grants {N : Nat} (x mk : BitVec N) : Tasks.Arbiter.Grants x (RoundRobin.pick x mk) :=
  ⟨fun _ _ hi hj => RoundRobin.pick_atMostOne hi hj, fun _ hi => RoundRobin.pick_sub hi,
    fun hx h => hx (RoundRobin.pick_eq_zero.1 h)⟩

noncomputable def model (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.RankModel N (N - 1) (design.sem N) where
  Shape := Shp N
  Step := Stp N
  init := by rw [arb_sem_eq N hN hR32]; exact arb_init N
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, q, g, v, m, ex, rfl, hw⟩ hc
    rw [arb_sem_eq N hN hR32] at hc
    obtain ⟨k2, h2⟩ := arb_cycle N hN σ e ck r q g v m ex k 64 (Nat.le_refl _)
    exact ⟨ck, r, q, g, v, m, ex, rfl, hw, (Prod.mk.inj (cycleStep2_det hc h2)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, q, g, v, m, ex, -, ⟨hg, hv, hm, hex⟩, rfl⟩
    exact arbNext_shp hg hv hm hex
  Inv := fun _ st => ArbInv N st
  out := fun st => (bvOf N "gnt" st, ())
  shows := by
    rintro - st ⟨ck, b, v, x, mk, e, rfl, -⟩
    show SvState.lookup _ "gnt" = some (LVec.ofBitVec (bvOf N "gnt" _)) ∧ True
    rw [bvOf_gnt]
    exact ⟨by simp [SS, SvState.lookup], trivial⟩
  rank := fun o st => RoundRobin.dist N (edgeOf (bvOf N "mask" st)) o.val
  rank_le := by
    rintro o - st ⟨ck, b, v, x, mk, e, rfl, hth⟩
    show RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val ≤ N - 1
    rw [bvOf_mask, edgeOf_eq hth]
    exact RoundRobin.dist_le hth.1 o.isLt
  reset := by
    rintro e prev st ⟨x, ⟨⟩⟩ - ⟨ck, r, q, g, v, m, ex, -, ⟨hg, hv, hm, hex⟩, rfl⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    rw [arbNext_reset hb hq hg hv hm hex]
    refine ⟨⟨_, true, false, x, 0#N, N, rfl, thermo_zero N⟩, ?_⟩
    show bvOf N "gnt" _ = 0#N
    rw [bvOf_gnt, decGnt_false_zero]
  step := by
    rintro e prev st - ⟨x, ⟨⟩⟩ - ⟨ck, r, q, g, v, m, ex, rfl, ⟨hg, hv, hm, hex⟩, rfl⟩
      ⟨ck', b', v', xp, mk, ed, hprev, hth⟩ hb hx
    have hq : SvState.lookup e "req" = some (LVec.ofBitVec x) := hx.1
    have hmm : m = LVec.ofBitVec mk := SS_mask hprev
    have hmask : bvOf N "mask" (SS ck r q g v m ex) = mk := by rw [hmm, bvOf_mask]
    rw [arbNext_run hb hq hmm hg hv hex]
    obtain ⟨e', hth', hprog⟩ := arb_step (x := x) hth
    refine ⟨⟨_, false, decide (x ≠ 0#N), x, arbMask x mk, e', rfl, hth'⟩, ?_, fun o ho => ?_⟩
    · show Tasks.Arbiter.Grants x (bvOf N "gnt" _)
      rw [bvOf_gnt, decGnt_pick]
      exact pick_grants x mk
    · have ho' : x.getLsbD o.val = true := ho
      by_cases hp : (RoundRobin.pick x mk).getLsbD o.val = true
      · left
        show (bvOf N "gnt" _).getLsbD o.val = true
        rw [bvOf_gnt, decGnt_pick]
        exact hp
      · right
        show RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val <
          RoundRobin.dist N (edgeOf (bvOf N "mask" _)) o.val
        rw [bvOf_mask, hmask, edgeOf_eq hth', edgeOf_eq hth]
        exact hprog o.val o.isLt ho' (by simpa using hp)

/-! ## 6. Interface, discipline, Moore, power-up, termination, XSafe, and main theorem -/

theorem arb_interface (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.Interface N (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "req", "gnt", "valid", "mask", "ext"] : List String).Nodup
    decide⟩

theorem arb_moore (N : Nat) : MooreOut (arbG.D N) := by
  refine ⟨fun n => n = "clk" ∨ n = "rst" ∨ n = "req", ?_, ?_, ?_⟩
  · intro n hn
    simp [arbG.D, arbG.decls, Design2.inputNames] at hn
    exact hn
  · intro p hp hcomb ⟨n, hn, hSn⟩ m hm
    simp only [arbG.D, List.toList_toArray, arbG.procs, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl | rfl
    · simp [arbG.p0, processDataNames, lhsNames, exprNames, exprListNames] at hn
      rcases hn with rfl | rfl | rfl <;> simp at hSn
    · simp [arbG.p1, processDataNames, lhsNames, exprNames] at hn
      rcases hn with rfl | rfl <;> simp at hSn
    · simp [arbG.p2, Process2.isCombPhase] at hcomb
  · intro o ho
    simp [arbG.D, arbG.decls, Design2.outputNames] at ho
    subst ho; decide

theorem arb_disciplined (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) :
    Tasks.Arbiter.task.Disciplined (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  refine ⟨⟨by simp [Tasks.Arbiter.task, arbG.D, arbG.decls, Design2.inputNames], fun p hp => ?_⟩,
    arb_moore N⟩
  simp only [arbG.D, List.toList_toArray, arbG.procs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp [Tasks.Arbiter.task, arbG.p0, arbG.p1, arbG.p2, edgeClock, asyncReset, processDataNames,
      stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames, exprListNames,
      Process2.isEdgePhase]

theorem arb_powerUp (N : Nat) : ∀ st, PowerUp (arbG.D N) st → Shp N st := by
  intro st h
  have h' : st.map Prod.fst = (arbG.decls N).map Decl.name ∧
      ∀ b ∈ st.zip (arbG.decls N), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true := h
  rw [arbG.decls] at h'
  obtain ⟨ck, r1, rfl, -, -, h1⟩ := powerUp_cons.mp h'
  obtain ⟨r, r2, rfl, -, -, h2⟩ := powerUp_cons.mp h1
  obtain ⟨q, r3, rfl, -, -, h3⟩ := powerUp_cons.mp h2
  obtain ⟨g, r4, rfl, hg, -, h4⟩ := powerUp_cons.mp h3
  obtain ⟨v, r5, rfl, hv, -, h5⟩ := powerUp_cons.mp h4
  obtain ⟨m, r6, rfl, hm, -, h6⟩ := powerUp_cons.mp h5
  obtain ⟨ex, r7, rfl, hex, -, h7⟩ := powerUp_cons.mp h6
  obtain rfl := powerUp_nil.mp h7
  exact ⟨ck, r, q, g, v, m, ex, rfl, hg, hv, hm, hex⟩

theorem arb_terminates (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : TerminatesPU (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  refine TerminatesPU.of_invariant (Shp N) (arb_powerUp N) (fun σ => ⟨64, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, q, g, v, m, ex, rfl, hg, hv, hm, hex⟩
    obtain ⟨k', h⟩ := arb_cycle N hN σ e ck r q g v m ex kk 64 (Nat.le_refl _)
    exact ⟨_, _, h, arbNext_shp hg hv hm hex⟩
  · simp [arbG.D, arbG.procs, arbG.p0, arbG.p1, arbG.p2,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem arb_xsafe (N : Nat) (hN : 1 ≤ N) (hR32 : Rng32 N) : XSafe (design.sem N) := by
  rw [arb_sem_eq N hN hR32]
  have hmin : (min (↑N : Int) 1).toNat = 1 := by omega
  simp [XSafe, xsafeB, arbG.D, arbG.decls, arbG.procs, arbG.p0, arbG.p1, arbG.p2,
    xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, xsWidthList, binW, sigWidth, hmin,
    LVec.allKnown_l0, LVec.allKnown_l1, LVec.allKnown_ofBitVec, Nat.add_comm]

theorem solution : Goal := by
  intro N hN
  obtain ⟨hN1, hNN⟩ := hN
  have hR32 : Rng32 N := rng32_of hN1 hNN
  exact Tasks.Arbiter.task.satisfiedAt_of_rank (arb_interface N hN1 hR32)
    (arb_disciplined N hN1 hR32) (arb_terminates N hN1 hR32) (model N hN1 hR32)
    (fun st h => arb_powerUp N st (by rw [arb_sem_eq N hN1 hR32] at h; exact h))
    (arb_xsafe N hN1 hR32)

end Submission
