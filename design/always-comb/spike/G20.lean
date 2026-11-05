import LeanModels.Sv.CombViewThm
import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.CombGuard2Sound
import LeanModels.Sv.CombKnownThm
import LeanModels.Sv.Ingest2

namespace LeanModels.Sv

mutual
/-- No dynamic or literal element select (`index` node): after instantiation every CONSTANT select is a slice. -/
def Expr2.idxFree : Expr2 → Bool
  | .index .. => false
  | .lit _ | .ident _ | .unsupported _ _ => true
  | .unary _ a | .resizeSigned _ a | .squash2 a | .repl _ a | .reduce _ a | .resize _ a
  | .slice a _ _ => a.idxFree
  | .binary _ l r | .scmp _ l r | .logical _ l r => l.idxFree && r.idxFree
  | .ternary c t f => c.idxFree && t.idxFree && f.idxFree
  | .concat parts => Expr2.listIdxFree parts.toList
termination_by structural e => e

def Expr2.listIdxFree : List Expr2 → Bool
  | [] => true
  | e :: es => e.idxFree && Expr2.listIdxFree es
termination_by structural es => es
end

namespace CombProcSpike
open CombGuard

/-! A tree of `if/else` over leaf right-hand sides, all assigning ONE target `tgt` (a whole signal or a constant slice; its window is `W`): the S1 body shape. -/
inductive PTree where
  | leaf (e : Expr2)
  | ite (c : Expr2) (a b : PTree)

/-- The statement a tree stands for. -/
def PTree.toStmt (tgt : Lhs2) : PTree → Stmt2
  | .leaf e => .blockingAssign tgt e
  | .ite c a b => .ifStmt c (a.toStmt tgt) (some (b.toStmt tgt))

/-- The whole `begin ... end` body. -/
def PTree.body (tgt : Lhs2) (t : PTree) : Stmt2 := .block #[t.toStmt tgt]

/-- The lowered right-hand side of the window. -/
def PTree.low (w : Nat) : PTree → Expr2
  | .leaf e => .resize w e
  | .ite c a b => Expr2.joinIte (Expr2.ifGuard c) (a.low w) (b.low w)

/-- Well-formedness of every expression of the tree. -/
def PTree.wf (d : Design2) : PTree → Prop
  | .leaf e => e.wfB d = true
  | .ite c a b => c.wfB d = true ∧ a.wf d ∧ b.wf d

/-! ## Helper: substitution into the empty symbolic state is the identity -/

theorem wfB_iff (d : Design2) (e : Expr2) :
    e.wfB d = true ↔ e.unsupportedFree = true ∧ ∀ x ∈ e.idents, x ∈ d.symNames := by
  simp [Expr2.wfB, List.all_eq_true]

theorem listWfB_iff (d : Design2) (l : List Expr2) :
    Expr2.listWfB d l = true ↔ Expr2.listUnsupportedFree l = true ∧ ∀ x ∈ Expr2.listIdents l, x ∈ d.symNames := by
  simp [Expr2.listWfB, List.all_eq_true]

theorem symSubst_nil_aux (d : Design2) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.wfB d = true → e.symSubst d [] = some e) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listWfB d l = true →
      Expr2.listSymSubst d [] l = some l) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hw => ?_, fun l hl hw => ?_⟩
    · rw [wfB_iff] at hw
      obtain ⟨hu, hi⟩ := hw
      have sub : ∀ a : Expr2, a.size < n → a.unsupportedFree = true → (∀ x ∈ a.idents, x ∈ d.symNames) →
          a.symSubst d [] = some a := fun a ha hu hi => ihe a ha ((wfB_iff d a).2 ⟨hu, hi⟩)
      cases e with
      | lit v => simp [Expr2.symSubst]
      | ident m =>
          have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
          simp [Expr2.symSubst, this, SymState.readWhole, SymState.writesName]
      | unsupported k t => simp [Expr2.unsupportedFree] at hu
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp [Expr2.symSubst, sub a (by omega) hu hi]
      | binary op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | scmp op l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | logical b l r =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub l (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub r (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | index a i w =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub a (by omega) hu.1 (fun x hx => hi x (Or.inl hx)),
            sub i (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | ternary c t f =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.idents, List.mem_append] at hi
          simp [Expr2.symSubst, sub c (by omega) hu.1.1 (fun x hx => hi x (Or.inl (Or.inl hx))),
            sub t (by omega) hu.1.2 (fun x hx => hi x (Or.inl (Or.inr hx))),
            sub f (by omega) hu.2 (fun x hx => hi x (Or.inr hx))]
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          by_cases hid : ∃ m, a = .ident m
          · obtain ⟨m, rfl⟩ := hid
            have : m ∈ d.symNames := hi m (by simp [Expr2.idents])
            simp [Expr2.symSubst, Expr2.sliceSubst, this, SymState.readWin, SymState.findCover,
              SymState.overlapsAny]
          · have hs : ∀ r, Expr2.sliceSubst d [] a lo w r = r.map fun b => Expr2.slice b lo w := by
              intro r; cases a <;> simp_all [Expr2.sliceSubst]
            have ih := sub a (by omega) hu hi
            simp [Expr2.symSubst, hs, ih]
      | concat parts =>
          simp only [Expr2.size] at he
          simp only [Expr2.unsupportedFree] at hu
          simp only [Expr2.idents] at hi
          have := ihl parts.toList (by omega) ((listWfB_iff d _).2 ⟨hu, hi⟩)
          simp [Expr2.symSubst, this]
    · cases l with
      | nil => simp [Expr2.listSymSubst]
      | cons e es =>
          rw [listWfB_iff] at hw
          obtain ⟨hu, hi⟩ := hw
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listUnsupportedFree, Bool.and_eq_true] at hu
          simp only [Expr2.listIdents, List.mem_append] at hi
          have h1 := ihe e (by omega) ((wfB_iff d e).2 ⟨hu.1, fun x hx => hi x (Or.inl hx)⟩)
          have h2 := ihl es (by omega) ((listWfB_iff d es).2 ⟨hu.2, fun x hx => hi x (Or.inr hx)⟩)
          simp [Expr2.listSymSubst, h1, h2]

theorem symSubst_nil (d : Design2) (e : Expr2) (h : e.wfB d = true) : e.symSubst d [] = some e :=
  (symSubst_nil_aux d (e.size + 1)).1 e (Nat.lt_succ_self _) h

#print axioms symSubst_nil


/-! ## A1: the symbolic execution -/

theorem symExec_tree (d : Design2) (tgt : Lhs2) (W : Win) (hsw : tgt.symWin d = some W) :
    ∀ t : PTree, t.wf d → (t.toStmt tgt).symExec d [] = some [(W, t.low W.2.2)] := by
  intro t
  induction t with
  | leaf e =>
      intro (h1 : e.wfB d = true)
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, h1, symSubst_nil d e h1, hsw, SymState.write,
        SymState.findCover, SymState.overlapsAny]
  | ite c a b iha ihb =>
      intro ⟨h1, ha, hb⟩
      simp [PTree.toStmt, PTree.low, Stmt2.symExec, Stmt2.symExecOpt, h1, symSubst_nil d c h1, iha ha, ihb hb,
        SymState.join, SymState.joinWins, Win.allDisjoint, SymState.lookupOr, SymState.findWin]

#print axioms symExec_tree

/-! ## A2: no self-read of the lowered equation -/

/-- No read of any expression of the tree overlaps the window. -/
def PTree.noRead (W : Win) : PTree → Prop
  | .leaf e => ∀ r ∈ e.reads, r.overlaps W = false
  | .ite c a b => (∀ r ∈ c.reads, r.overlaps W = false) ∧ a.noRead W ∧ b.noRead W

theorem low_reads (W : Win) (w : Nat) :
    ∀ t : PTree, t.noRead W → ∀ r ∈ (t.low w).reads, r.overlaps W = false := by
  intro t
  induction t with
  | leaf e => intro h r hr; exact h r (by simpa [PTree.low, Expr2.reads] using hr)
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ r hr
      simp only [PTree.low, Expr2.joinIte] at hr
      split at hr
      · exact iha ha r hr
      · simp only [Expr2.reads, Expr2.ifGuard, List.mem_append, List.not_mem_nil, or_false] at hr
        rcases hr with (hr | hr) | hr
        · exact hc r hr
        · exact iha ha r hr
        · exact ihb hb r hr

theorem selfReadFree_tree (W : Win) (w : Nat) (t : PTree) (h : t.noRead W) :
    SymState.selfReadFree [(W, t.low w)] = true := by
  simp only [SymState.selfReadFree, List.map_cons, List.map_nil, Expr2.listReads, List.append_nil,
    List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true, Bool.not_eq_true']
  exact fun r hr => low_reads W w t h r hr

/-! ## A4: the driven windows -/

theorem drvWins_tree (tgt : Lhs2) :
    ∀ t : PTree, ∀ x ∈ (t.toStmt tgt).drvWins, x ∈ tgt.drvWins := by
  intro t
  induction t with
  | leaf e => intro x hx; simpa [PTree.toStmt, Stmt2.drvWins] using hx
  | ite c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.drvWins, Stmt2.drvWinsOpt, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx

/-! ## A3: the self-read guard admits the body -/

/-- Every read window of every expression of the tree meets the window in zero bits. -/
def PTree.noRdW (wd : String → Option Nat) (W : BWin) : PTree → Prop
  | .leaf e => ∀ r ∈ e.rdW wd, (BWin.inter r W).2.2 = 0
  | .ite c a b => (∀ r ∈ c.rdW wd, (BWin.inter r W).2.2 = 0) ∧ a.noRdW wd W ∧ b.noRdW wd W

theorem BWin.subAll_nil_of_zero (a : BWin) (h : a.2.2 = 0) : ∀ M : List BWin, BWin.subAll a M = [] := by
  intro M
  induction M generalizing a with
  | nil => simp [BWin.subAll, h]
  | cons b bs ih =>
      simp only [BWin.subAll, BWin.sub]
      split
      · -- same signal
        have h1 : ¬ a.2.1 < min (a.2.1 + a.2.2) b.2.1 := by omega
        have h2 : ¬ max a.2.1 (b.2.1 + b.2.2) < a.2.1 + a.2.2 := by omega
        simp [h1, h2]
      · simp [h]

theorem readsViol_none (M A R : List BWin) (W : BWin) (hA : ∀ x ∈ A, x = W)
    (hR : ∀ r ∈ R, (BWin.inter r W).2.2 = 0) : readsViol M A R = none := by
  unfold readsViol
  rw [List.findSome?_eq_none_iff]
  intro r hr
  rw [List.findSome?_eq_none_iff]
  intro x hx
  have := hA x hx
  subst this
  rw [BWin.subAll_nil_of_zero _ (hR r hr)]
  rfl

theorem mayW_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W]) :
    ∀ t : PTree, ∀ x ∈ (t.toStmt tgt).mayW wd, x = W := by
  intro t
  induction t with
  | leaf e => intro x hx; simpa [PTree.toStmt, Stmt2.mayW, hm] using hx
  | ite c a b iha ihb =>
      intro x hx
      simp only [PTree.toStmt, Stmt2.mayW, Stmt2.optMayW, List.mem_append] at hx
      rcases hx with hx | hx
      · exact iha x hx
      · exact ihb x hx

theorem combViol_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) :
    ∀ t : PTree, t.noRdW wd W → ∀ (M A : List BWin), (∀ x ∈ A, x = W) →
      (t.toStmt tgt).combViol wd M A = none := by
  intro t
  induction t with
  | leaf e =>
      intro h M A hA
      simp only [PTree.toStmt, Stmt2.combViol, hm, hr, List.append_nil]
      apply readsViol_none M _ _ W
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with rfl | hx
        · rfl
        · exact hA x hx
      · exact h
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ M A hA
      simp only [PTree.toStmt, Stmt2.combViol, Stmt2.optCombViol]
      rw [readsViol_none M _ _ W _ hc, iha ha M A hA, ihb hb M A hA]
      · rfl
      · intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact mayW_tree wd tgt W hm a x hx
        · exact mayW_tree wd tgt W hm b x (by simpa [PTree.toStmt, Stmt2.optMayW] using hx)
        · exact hA x hx

theorem combAdmits_tree (wd : String → Option Nat) (tgt : Lhs2) (W : Win) (hm : tgt.mayW wd = [W])
    (hr : tgt.rdW wd = []) (t : PTree) (h : t.noRdW wd W) :
    (t.body tgt).combAdmits wd = true := by
  unfold Stmt2.combAdmits
  have : (t.body tgt).combViol wd [] [] = none := by
    have h0 := combViol_tree wd tgt W hm hr t h [] [] (by simp)
    simp [PTree.body, Stmt2.combViol, Stmt2.listCombViol, Stmt2.listMayW, h0]
  rw [this]; rfl

#print axioms combAdmits_tree
#print axioms selfReadFree_tree
#print axioms drvWins_tree

/-! ## The Boolean semantics of the lowered equation (the netlist-view shape) -/

/-- The Boolean semantics of the tree. -/
def PTree.bit (d : Design2) (env : String → Nat → Bool) : PTree → Nat → Bool
  | .leaf e => fun k => e.xfBits d env k
  | .ite c a b => fun k => if c.xfBits d env 0 then a.bit d env k else b.bit d env k

/-- Every leaf is `w` bits wide, every condition 1 bit, in the x-free fragment. -/
def PTree.xfOk (d : Design2) (w : Nat) : PTree → Prop
  | .leaf e => e.xfWidth d = some w
  | .ite c a b => c.xfWidth d = some 1 ∧ a.xfOk d w ∧ b.xfOk d w

theorem ifGuard_xfWidth (d : Design2) (c : Expr2) (h : c.xfWidth d = some 1) :
    (Expr2.ifGuard c).xfWidth d = some 1 := by
  simp [Expr2.ifGuard, Expr2.xfWidth, h, XF.same, LVec.ofLogic, LVec.knownB, LVec.width, Logic.isKnown]

theorem ifGuard_xfBits (d : Design2) (env : String → Nat → Bool) (c : Expr2) (h : c.xfWidth d = some 1) (k : Nat) :
    (Expr2.ifGuard c).xfBits d env k = c.xfBits d env 0 := by
  simp [Expr2.ifGuard, Expr2.xfBits, Expr2.xfWidth, h, XF.eqv, XF.red, XF.any, LVec.ofLogic, LVec.boolAt]

theorem low_xfWidth (d : Design2) (w : Nat) :
    ∀ t : PTree, t.xfOk d w → (t.low w).xfWidth d = some w := by
  intro t
  induction t with
  | leaf e => intro h; simp only [PTree.low, Expr2.xfWidth, PTree.xfOk] at *; simp [h]
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩
      simp only [PTree.low, Expr2.joinIte]
      split
      · exact iha ha
      · simp [Expr2.xfWidth, ifGuard_xfWidth d c hc, iha ha, ihb hb, XF.same]

theorem low_xfBits (d : Design2) (env : String → Nat → Bool) (w : Nat) :
    ∀ t : PTree, t.xfOk d w → ∀ k, k < w → (t.low w).xfBits d env k = t.bit d env k := by
  intro t
  induction t with
  | leaf e => intro h k hk; simp [PTree.low, PTree.bit, Expr2.xfBits, PTree.xfOk] at *; simp [h, hk]
  | ite c a b iha ihb =>
      intro ⟨hc, ha, hb⟩ k hk
      simp only [PTree.low, Expr2.joinIte]
      split
      · rename_i hs
        have hab := Expr2.eq_of_same _ _ hs
        have h1 := iha ha k hk
        have h2 := ihb hb k hk
        rw [← hab] at h2
        have h3 : a.bit d env k = b.bit d env k := h1.symm.trans h2
        simp [PTree.bit, h1, h3]
      · simp [Expr2.xfBits, ifGuard_xfWidth d c hc, ifGuard_xfBits d env c hc, iha ha k hk, ihb hb k hk, PTree.bit, XF.any]


/-- A read window that does not overlap the write window meets it in zero bits (BWin form). -/
theorem inter_zero_of_win (n : String) (lo w : Nat) (W : Win)
    (h : (ReadWin.win n lo w).overlaps W = false) : (BWin.inter (n, lo, w) W).2.2 = 0 := by
  obtain ⟨m, l', w'⟩ := W
  simp only [ReadWin.overlaps, Win.overlaps_eq_false] at h
  simp only [BWin.inter]
  split
  · rename_i hn; subst hn; simp at h ⊢; omega
  · rfl

theorem inter_zero_of_whole (wd : String → Option Nat) (n : String) (W : Win)
    (h : (ReadWin.whole n).overlaps W = false) : (BWin.inter (whole wd n) W).2.2 = 0 := by
  obtain ⟨m, l', w'⟩ := W
  simp only [ReadWin.overlaps, beq_eq_false_iff_ne] at h
  simp [BWin.inter, whole, h]

theorem rdW_of_reads_aux (wd : String → Option Nat) (W : Win) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → e.idxFree = true → (∀ r ∈ e.reads, r.overlaps W = false) →
      ∀ x ∈ e.rdW wd, (BWin.inter x W).2.2 = 0) ∧
    (∀ l : List Expr2, Expr2.listSize l < n → Expr2.listIdxFree l = true →
      (∀ r ∈ Expr2.listReads l, r.overlaps W = false) →
      ∀ x ∈ Expr2.listRdW wd l, (BWin.inter x W).2.2 = 0) := by
  intro n
  induction n with
  | zero => exact ⟨fun e h => by omega, fun l h => by omega⟩
  | succ n ih =>
    obtain ⟨ihe, ihl⟩ := ih
    refine ⟨fun e he hi hr x hx => ?_, fun l hl hi hr x hx => ?_⟩
    · cases e with
      | lit v => simp [Expr2.rdW] at hx
      | unsupported k t => simp [Expr2.rdW] at hx
      | ident m =>
          simp only [Expr2.rdW, List.mem_singleton] at hx; subst hx
          exact inter_zero_of_whole wd m W (hr _ (by simp [Expr2.reads]))
      | unary op a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | resizeSigned w a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | squash2 a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | repl k a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | reduce op a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | resize w a =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihe a (by omega) hi (by simpa [Expr2.reads] using hr) x (by simpa [Expr2.rdW] using hx)
      | binary op l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | scmp op l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | logical b l r =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe l (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihe r (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | index a i w => simp [Expr2.idxFree] at hi
      | ternary c t f =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree, Bool.and_eq_true] at hi
          simp only [Expr2.reads, List.mem_append] at hr
          simp only [Expr2.rdW, List.mem_append] at hx
          rcases hx with hx | hx | hx
          · exact ihe c (by omega) hi.1.1 (fun r' h => hr r' (Or.inl (Or.inl h))) x hx
          · exact ihe t (by omega) hi.1.2 (fun r' h => hr r' (Or.inl (Or.inr h))) x hx
          · exact ihe f (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx
      | slice a lo w =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          cases a with
          | ident m =>
              simp only [Expr2.rdW, sliceRd, List.mem_singleton] at hx; subst hx
              exact inter_zero_of_win m lo w W (hr _ (by simp [Expr2.reads, Expr2.sliceReads]))
          | _ =>
              rename_i a'
              first
              | (exact ihe _ (by omega) hi (by simpa [Expr2.reads, Expr2.sliceReads] using hr) x
                  (by simpa [Expr2.rdW, sliceRd] using hx))
      | concat parts =>
          simp only [Expr2.size] at he; simp only [Expr2.idxFree] at hi
          exact ihl parts.toList (by omega) hi (by simpa [Expr2.reads] using hr) x
            (by simpa [Expr2.rdW] using hx)
    · cases l with
      | nil => simp [Expr2.listRdW] at hx
      | cons e es =>
          simp only [Expr2.listSize] at hl
          simp only [Expr2.listIdxFree, Bool.and_eq_true] at hi
          simp only [Expr2.listReads, List.mem_append] at hr
          simp only [Expr2.listRdW, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ihe e (by omega) hi.1 (fun r' h => hr r' (Or.inl h)) x hx
          · exact ihl es (by omega) hi.2 (fun r' h => hr r' (Or.inr h)) x hx

theorem rdW_of_reads (wd : String → Option Nat) (W : Win) (e : Expr2) (hi : e.idxFree = true)
    (hr : ∀ r ∈ e.reads, r.overlaps W = false) : ∀ x ∈ e.rdW wd, (BWin.inter x W).2.2 = 0 :=
  (rdW_of_reads_aux wd W (e.size + 1)).1 e (Nat.lt_succ_self _) hi hr


/-- The tree has no `index` node. -/
def PTree.idxFree : PTree → Prop
  | .leaf e => e.idxFree = true
  | .ite c a b => c.idxFree = true ∧ a.idxFree ∧ b.idxFree

/-- The window-level (`ReadWin`) non-overlap, which is what the summary's `noSelfRead` obligation gives,
implies the bit-level one the self-read guard walks. -/
theorem noRdW_of_noRead (wd : String → Option Nat) (W : Win) :
    ∀ t : PTree, t.idxFree → t.noRead W → t.noRdW wd W := by
  intro t
  induction t with
  | leaf e => exact fun hi h => rdW_of_reads wd W e hi h
  | ite c a b iha ihb =>
      intro ⟨hi, ha, hb⟩ ⟨hc, hna, hnb⟩
      exact ⟨rdW_of_reads wd W c hi hc, iha ha hna, ihb hb hnb⟩

/-! ## S-B: the template instantiates to a tree -/

/-- The template tree (over `PExpr`). -/
inductive PT where
  | leaf (v : PExpr)
  | ite (c : PExpr) (a b : PT)

def PT.toPStmt (t : PLhs) : PT → PStmt
  | .leaf v => .blockingAssignL t v
  | .ite c a b => .ifStmt c (a.toPStmt t) (some (b.toPStmt t))

/-- The template body: `begin <tree> end`. -/
def PT.toProc (t : PLhs) (pt : PT) : PProcess := .alwaysComb (.block [pt.toPStmt t])

/-- Its instantiation as a tree of `Expr2`. -/
def PT.low (E : IEnv) (elems : List (String × Nat)) (w : Nat) : PT → PTree
  | .leaf v => .leaf (fitExpr2 E elems (some w) v)
  | .ite c a b => .ite (instExpr2 E elems none c) (a.low E elems w) (b.low E elems w)

theorem instStmt2_tree {E : IEnv} {elems : List (String × Nat)} {t : PLhs} {tgt : Lhs2} {w : Nat}
    (h : instLhs2 E elems t = .ok (tgt, w)) :
    ∀ pt : PT, instStmt2 E elems (pt.toPStmt t) = (pt.low E elems w).toStmt tgt := by
  intro pt
  induction pt with
  | leaf v => simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, h]
  | ite c a b iha ihb => simp [PT.toPStmt, PT.low, PTree.toStmt, instStmt2, iha, ihb]

theorem instProcess2_tree {E : IEnv} {elems : List (String × Nat)} {t : PLhs} {tgt : Lhs2} {w : Nat}
    (h : instLhs2 E elems t = .ok (tgt, w)) (pt : PT) :
    instProcess2 E elems (pt.toProc t) =
      combGuardProc (fun n => E.widths.lookup n) ((pt.low E elems w).body tgt) := by
  simp [PT.toProc, instProcess2, instStmt2, instStmts2, instStmt2_tree h pt, PTree.body]

/-! ## S-C (generic form): the lowering of an instantiated tree -/

theorem lower_tree (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hrd : t.noRdW wd W) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.body tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) := by
  rw [combGuardProc_of_admits (combAdmits_tree wd tgt W hm hr t hrd)]
  have h1 : (t.body tgt).symExec d [] = some [(W, t.low W.2.2)] := by
    simp [PTree.body, Stmt2.symExec, Stmt2.symExecList, symExec_tree d tgt W hsw t hwf]
  simp [Process2.lowerComb, h1, selfReadFree_tree W W.2.2 t hno, SymState.toAssign, SymState.target,
    SymState.rhs]

/-- The final form: ONE non-overlap hypothesis (window level) and no index nodes. -/
theorem lower_tree' (d : Design2) (wd : String → Option Nat) (tgt : Lhs2) (W : Win)
    (hsw : tgt.symWin d = some W) (hm : tgt.mayW wd = [W]) (hr : tgt.rdW wd = []) (t : PTree)
    (hwf : t.wf d) (hix : t.idxFree) (hno : t.noRead W) :
    Process2.lowerComb d (combGuardProc wd (t.body tgt)) =
      some (.assign (.concat [W.lhs]) (.concat #[t.low W.2.2])) :=
  lower_tree d wd tgt W hsw hm hr t hwf (noRdW_of_noRead wd W t hix hno) hno

/-! ## S-C (concrete): the `add_proc` carry cell at symbolic `N` and bit `k` -/

/-- `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];` -/
def carryPT : PT :=
  .ite (.bitSel (.ident "p") (.genvarRef "i"))
    (.leaf (.bitSel (.ident "c") (.genvarRef "i")))
    (.leaf (.bitSel (.ident "a") (.genvarRef "i")))

def carryLhs : PLhs := .bitSel "c" (.binary (.m0 .add) (.genvarRef "i") (.int 1))

/-- The design's declarations (the lowering only reads the names and widths). -/
def apDesign (N : Nat) : Design2 where
  name := "add_proc"
  decls := #[
    { name := "a", width := N, isInput := true },
    { name := "b", width := N, isInput := true },
    { name := "cin", width := 1, isInput := true },
    { name := "s", width := N, isOutput := true },
    { name := "cout", width := 1, isOutput := true },
    { name := "c", width := N + 1 },
    { name := "p", width := N }]
  processes := #[]

theorem ap_symNames (N : Nat) : (apDesign N).symNames = ["a", "b", "cin", "s", "cout", "c", "p"] := rfl

theorem ap_declWidth_c (N : Nat) : (apDesign N).declWidth "c" = some (N + 1) := by
  simp [Design2.declWidth, apDesign]

theorem carry_lowers (N k : Nat) (hk : k < N) (E : IEnv) (elems : List (String × Nat))
    (hc : elems.lookup "c" = some 1) (ha : elems.lookup "a" = some 1) (hp : elems.lookup "p" = some 1)
    (hi : E.vals.lookup "i" = some (k : Int)) :
    Process2.lowerComb (apDesign N) (instProcess2 E elems (carryPT.toProc carryLhs)) =
      some (.assign (.concat [.slice "c" (k + 1) 1])
        (.concat #[Expr2.ternary
          (Expr2.ifGuard (.slice (.ident "p") k 1))
          (.resize 1 (.slice (.ident "c") k 1)) (.resize 1 (.slice (.ident "a") k 1))])) := by
  -- the index `i + 1` evaluates to `k + 1`
  have hev1 : evalInt E (.binary (.m0 .add) (.genvarRef "i") (.int 1)) = .ok ((k : Int) + 1) := by
    have := (CombView.affOf?_sound (E := E) (σ := fun n => if n = "i" then (k : Int) else 0)
      (.binary (.m0 .add) (.genvarRef "i") (.int 1))
      ⟨[("i", 1)], 1⟩ (by simp [CombView.affOf?, CombView.affBin, CombView.Aff.add, CombView.Aff.var, CombView.Aff.const])
      (by intro n hn; simp [CombView.Aff.names] at hn; subst hn; simpa using hi)).2
    simpa [CombView.Aff.eval, CombView.Aff.evalTerms, Int.add_comm] using this
  have hev0 : evalInt E (.genvarRef "i") = .ok (k : Int) := evalInt_genvarRef_of hi
  have hlhs : instLhs2 E elems carryLhs =
      .ok (Win.lhs ("c", k + 1, 1), 1) := by
    have := instLhs2_bitSel (env := E) (elems := elems) hc hev1 (by omega)
    simpa [carryLhs, Win.lhs] using this
  rw [instProcess2_tree hlhs]
  -- the instantiated tree
  have hlow : carryPT.low E elems 1 =
      .ite (.slice (.ident "p") k 1) (.leaf (.slice (.ident "c") k 1)) (.leaf (.slice (.ident "a") k 1)) := by
    simp [carryPT, PT.low, instExpr2_bitSel_ident _ hp hev0 (by omega), fitExpr2_bitSel_ident hc hev0 (by omega),
      fitExpr2_bitSel_ident ha hev0 (by omega)]
  have hsw : (Win.lhs ("c", k + 1, 1)).symWin (apDesign N) = some ("c", k + 1, 1) := by
    simp [Lhs2.symWin, Win.lhs, Lhs2.window?, ap_declWidth_c N]; omega
  rw [hlow, lower_tree' (apDesign N) _ (Win.lhs ("c", k + 1, 1)) ("c", k + 1, 1) hsw
    (by simp [Win.lhs, Lhs2.mayW]) (by simp [Win.lhs, Lhs2.rdW])]
  · simp [PTree.low, Expr2.joinIte, Expr2.same, Win.lhs]
  · simp [PTree.wf, Expr2.wfB, Expr2.unsupportedFree, Expr2.idents, ap_symNames]
  · simp [PTree.idxFree, Expr2.idxFree]
  · simp [PTree.noRead, Expr2.reads, Expr2.sliceReads, ReadWin.overlaps, Win.overlaps]

#print axioms carry_lowers
#print axioms lower_tree'
#print axioms noRdW_of_noRead
#print axioms instProcess2_tree
#print axioms low_xfWidth
#print axioms low_xfBits
#print axioms symSubst_nil

end CombProcSpike

/-! ## The template really is the ingested one -/

load_design_sv2 add_proc from "svgolf/design/always-comb/fixtures/add_proc.sv.json"

open CombProcSpike in
#guard match add_proc.pdesign.generates with
  | [.genFor _ _ _ _ _ _ [_, .process p, _]] => p == carryPT.toProc carryLhs
  | _ => false

end LeanModels.Sv
