-- svgolf-latency: 15
import Submission.Design
import SvGolf.Cycle
import SvGolf.SeqV2

/-!
# Proof of `sorter/n1`: shared-comparator SOP insertion sorter without output register, latency `2N - 1`

Proved for every `(N, W)` with `1 ≤ N`, `1 ≤ W`, `N * W < 2^31` under `SvGolf.Tasks.Sorter.Statement`
(`StreamTask.StatementV2`).
-/

namespace Submission

open LeanModels.Sv SvGolf SvGolf.Cycle

/-- Latency: `2N - 1` (`15` at `N = 8`), the Moore lower bound. -/
def lat (N _W : Nat) : Nat := 2 * N - 1

/-! ## 1. Mirror, disjointness, and single-cycle step via `sv_mirror` / `sv_cycle` -/

abbrev Rng32 (N W : Nat) : Prop :=
  N < 2147483648 ∧ W < 2147483648 ∧ N * W < 2147483648

theorem rng32_of {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N * W < 2 ^ 31) : Rng32 N W := by
  have h1 : N ≤ N * W := Nat.le_mul_of_pos_right N hW
  have h2 : W ≤ N * W := Nat.le_mul_of_pos_left W hN
  refine ⟨?_, ?_, ?_⟩ <;> (show _ < 2147483648; omega)

sv_mirror soG := design (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W)
  (hN32 : N < 2147483648) (hW32 : W < 2147483648) (hNW : N * W < 2147483648)

theorem soG_disj (N W : Nat) :
    (soG.procs N W).Pairwise WinDisj := by
  have h1 : ∀ k ∈ List.range N, WinDisj (soG.p0 N W) (soG.gen_cmp N W k) := fun _ _ =>
    WinDisj.of_all (by simp [soG.p0, soG.gen_cmp, allWins, Process2.drvWins, Process2.procWins,
      Lhs2.drvWins, DrvWin.overlaps])
  have h2 : ∀ k ∈ List.range (N - 1), WinDisj (soG.p0 N W) (soG.gen_cell N W k) := fun _ _ =>
    WinDisj.of_all (by simp [soG.p0, soG.gen_cell, allWins, Process2.drvWins, Process2.procWins,
      Stmt2.drvWins, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  have h3 : ∀ k ∈ List.range N, WinDisj (soG.p1 N W) (soG.gen_cmp N W k) := fun _ _ =>
    WinDisj.of_all (by simp [soG.p1, soG.gen_cmp, allWins, Process2.drvWins, Process2.procWins,
      Lhs2.drvWins, DrvWin.overlaps])
  have h4 : ∀ k ∈ List.range (N - 1), WinDisj (soG.p1 N W) (soG.gen_cell N W k) := fun _ _ =>
    WinDisj.of_all (by simp [soG.p1, soG.gen_cell, allWins, Process2.drvWins, Process2.procWins,
      Stmt2.drvWins, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  have h5 : ∀ k ∈ List.range N, WinDisj (soG.p2 N W) (soG.gen_cmp N W k) := fun _ _ =>
    WinDisj.of_all (by simp [soG.p2, soG.gen_cmp, allWins, Process2.drvWins, Process2.procWins,
      Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  have h6 : ∀ k ∈ List.range (N - 1), WinDisj (soG.p2 N W) (soG.gen_cell N W k) := fun k hk => by
    rw [List.mem_range] at hk
    have hdisj : k * W + W ≤ (N - 1) * W := by
      have := Nat.mul_le_mul_right W (show k + 1 ≤ N - 1 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
    exact WinDisj.of_all (by
      simp [soG.p2, soG.gen_cell, allWins, Process2.drvWins, Process2.procWins,
        Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
      omega)
  have h7 : (List.map (soG.gen_cmp N W) (List.range N)).Pairwise WinDisj := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun {a b} hab => WinDisj.of_all (by
      simp [soG.gen_cmp, allWins, Process2.drvWins, Process2.procWins, Lhs2.drvWins, DrvWin.overlaps]
      omega)
  have h8 : (List.map (soG.gen_cell N W) (List.range (N - 1))).Pairwise WinDisj := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun {a b} hab => by
      have hdisj : a * W + W ≤ b * W := by
        have := Nat.mul_le_mul_right W (show a + 1 ≤ b by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      exact WinDisj.of_all (by
        simp [soG.gen_cell, allWins, Process2.drvWins, Process2.procWins,
          Stmt2.drvWins, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
        omega)
  have h9 : ∀ p ∈ List.map (soG.gen_cmp N W) (List.range N),
      ∀ q ∈ List.map (soG.gen_cell N W) (List.range (N - 1)), WinDisj p q := by
    intro p hp q hq
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hq
    exact WinDisj.of_all (by
      simp [soG.gen_cmp, soG.gen_cell, allWins, Process2.drvWins, Process2.procWins,
        Stmt2.drvWins, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  simp only [soG.procs, List.pairwise_cons, List.mem_cons, List.mem_append, List.mem_map]
  refine ⟨?_, ?_, ?_, List.pairwise_append.mpr ⟨h7, h8, h9⟩⟩
  · rintro p (rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact WinDisj.of_all (by simp [soG.p0, soG.p1, allWins, Process2.drvWins, Lhs2.drvWins, DrvWin.overlaps])
    · exact WinDisj.of_all (by simp [soG.p0, soG.p2, allWins, Process2.drvWins, Process2.procWins,
        Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · exact h1 k hk
    · exact h2 k hk
  · rintro p (rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact WinDisj.of_all (by simp [soG.p1, soG.p2, allWins, Process2.drvWins, Process2.procWins,
        Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
    · exact h3 k hk
    · exact h4 k hk
  · rintro p (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact h5 k hk
    · exact h6 k hk

sv_cycle soG using soG_disj N W

/-! ## 2. 4-state `LVec` masking and queue helpers -/

theorem width_resizeU' (v : LVec) (w : Nat) : (v.resizeU w).width = w := by
  simp [LVec.resizeU, LVec.width]

theorem resizeU_eq_self {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.resizeU, Array.getElem?_ofFn]
  by_cases hi : i < w
  · have hi' : i < v.bits.size := by simp only [LVec.width] at h; omega
    simp [hi, Array.getElem?_eq_getElem hi']
  · have hi' : v.bits.size ≤ i := by simp only [LVec.width] at h; omega
    simp [hi, Array.getElem?_eq_none hi']

theorem extract_self {v : LVec} {w : Nat} (h : v.width = w) : v.extract 0 w = v := by
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.extract, Array.getElem?_ofFn]
  by_cases hi : i < w
  · have hi' : i < v.bits.size := by simp only [LVec.width] at h; omega
    simp [hi, Array.getElem?_eq_getElem hi']
  · have hi' : v.bits.size ≤ i := by simp only [LVec.width] at h; omega
    simp [hi, Array.getElem?_eq_none hi']

theorem concatMany_single (v : LVec) : LVec.concatMany #[v] = v := by
  simp [LVec.concatMany]

theorem ofLogic_l0_eq : LVec.ofLogic Logic.l0 = knownBit false := by
  apply LVec.ext_getElem?; intro i; cases i <;> simp [knownBit, LVec.ofLogic, LVec.ofBitVec_bits]
theorem ofLogic_l1_eq : LVec.ofLogic Logic.l1 = knownBit true := by
  apply LVec.ext_getElem?; intro i; cases i <;> simp [knownBit, LVec.ofLogic, LVec.ofBitVec_bits]

theorem isKnownZero_ofLogic_l0 : (LVec.ofLogic Logic.l0).isKnownZero = true := by
  simp [LVec.isKnownZero, LVec.ofLogic]
theorem isKnownZero_ofLogic_l1 : (LVec.ofLogic Logic.l1).isKnownZero = false := by
  simp [LVec.isKnownZero, LVec.ofLogic]
theorem condTrue_ofLogic_l1 : (LVec.ofLogic Logic.l1).condTrue = true := by
  simp [LVec.condTrue, LVec.ofLogic]

theorem isKnownZero_knownBit (b : Bool) : (knownBit b).isKnownZero = !b := by
  cases b
  · rw [← ofLogic_l0_eq]; exact isKnownZero_ofLogic_l0
  · rw [← ofLogic_l1_eq]; exact isKnownZero_ofLogic_l1

theorem condTrue_knownBit' (b : Bool) : (knownBit b).condTrue = b := condTrue_knownBit b

theorem lnot_knownBit (b : Bool) : LVec.ofLogic (knownBit b).lnot = knownBit (!b) := by
  cases b <;>
    simp [LVec.lnot, isKnownZero_knownBit, condTrue_knownBit', ofLogic_l0_eq, ofLogic_l1_eq]

theorem resizeU_one_knownBit (b : Bool) : (knownBit b).resizeU 1 = knownBit b :=
  resizeU_eq_self (by simp [knownBit])

theorem repl_zero_and {W : Nat} (v : LVec) (hv : v.width = W) :
    (LVec.replVec W (knownBit false)).and v = LVec.ofBitVec 0#W := by
  have h0 : LVec.replVec W (knownBit false) = LVec.ofBitVec 0#W := by
    have hk : knownBit false = LVec.ofBitVec (BitVec.ofBool false) := rfl
    rw [hk, LVec.replVec_ofBitVec]
    apply LVec.ext_getElem?
    intro i
    simp only [LVec.getElem?_ofBitVec]
    by_cases hi : i < W
    · simp [hi]
    · simp [hi]
  rw [h0]
  have hw0 : (LVec.ofBitVec 0#W).width = v.width := by simp [hv]
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.and, LVec.zipWith, hw0, ↓reduceIte, LVec.ofBitVec_bits, Array.getElem?_zipWith,
    Array.getElem?_ofFn]
  by_cases hi : i < W
  · have hi' : i < v.bits.size := by simp only [LVec.width] at hv; omega
    simp only [hi, ↓reduceDIte, Array.getElem?_eq_getElem hi', Option.map_some, BitVec.getLsbD_zero]
    cases v.bits[i] <;> rfl
  · have hi' : v.bits.size ≤ i := by simp only [LVec.width] at hv; omega
    simp [hi, Array.getElem?_eq_none hi']

theorem repl_one_and_bv {W : Nat} (bv : BitVec W) :
    (LVec.replVec W (knownBit true)).and (LVec.ofBitVec bv) = LVec.ofBitVec bv := by
  have h1 : LVec.replVec W (knownBit true) = LVec.ofBitVec (BitVec.allOnes W) := by
    have hk : knownBit true = LVec.ofBitVec (BitVec.ofBool true) := rfl
    rw [hk, LVec.replVec_ofBitVec]
    apply LVec.ext_getElem?
    intro i
    simp only [LVec.getElem?_ofBitVec]
    by_cases hi : i < W
    · simp [hi, Nat.mod_one]
    · simp [hi]
  rw [h1]
  have hw1 : (LVec.ofBitVec (BitVec.allOnes W)).width = (LVec.ofBitVec bv).width := by simp
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.and, LVec.zipWith, hw1, ↓reduceIte, LVec.ofBitVec_bits, Array.getElem?_zipWith,
    Array.getElem?_ofFn]
  by_cases hi : i < W
  · simp only [hi, ↓reduceDIte, Option.map_some, BitVec.getLsbD_allOnes, decide_true]
    cases bv.getLsbD i <;> rfl
  · simp [hi]

theorem or_zero_right_bv {W : Nat} (bv : BitVec W) :
    (LVec.ofBitVec bv).or (LVec.ofBitVec 0#W) = LVec.ofBitVec bv := by
  have hw0 : (LVec.ofBitVec bv).width = (LVec.ofBitVec 0#W).width := by simp
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.or, LVec.zipWith, hw0, ↓reduceIte, LVec.ofBitVec_bits, Array.getElem?_zipWith,
    Array.getElem?_ofFn]
  by_cases hi : i < W
  · simp only [hi, ↓reduceDIte, Option.map_some, BitVec.getLsbD_zero]
    cases bv.getLsbD i <;> rfl
  · simp [hi]

theorem or_zero_left_bv {W : Nat} (bv : BitVec W) :
    (LVec.ofBitVec 0#W).or (LVec.ofBitVec bv) = LVec.ofBitVec bv := by
  have hw0 : (LVec.ofBitVec 0#W).width = (LVec.ofBitVec bv).width := by simp
  apply LVec.ext_getElem?
  intro i
  simp only [LVec.or, LVec.zipWith, hw0, ↓reduceIte, LVec.ofBitVec_bits, Array.getElem?_zipWith,
    Array.getElem?_ofFn]
  by_cases hi : i < W
  · simp only [hi, ↓reduceDIte, Option.map_some, BitVec.getLsbD_zero]
    cases bv.getLsbD i <;> rfl
  · simp [hi]

theorem mul_add_le_mul {a b W : Nat} (h : a < b) : a * W + W ≤ b * W := by
  have := Nat.mul_le_mul_right W (show a + 1 ≤ b by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  exact this

theorem nbaFold_none {n : String} (q : NbaQueue2) (x : LVec)
    (h : ∀ u ∈ q, u.1 ≠ n) : nbaFold n q x = x :=
  nbaFold_of_forall_ne h x

/-! ## 3. Settled comb signals and next-state register slices -/

theorem comb_out_valid_eq (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck r s iv id ov od dt tk g : LVec) (hov : ov.width = 1) :
    soG.comb_out_valid N W ck r s iv id ov od dt tk g = (tk.extract 0 1).resizeU 1 := by
  have hmem : ("out_valid", 0, (tk.extract 0 1).resizeU 1) ∈
      soG.combQ N W ck r s iv id ov od dt tk g := by
    simp [soG.combQ, soG.p0C, hov]
  have he := extract_nbaFold_of_mem (x := ov)
    (soG.combQ_disj N W hN hW hR32.1 hR32.2.1 hR32.2.2 ck r s iv id ov od dt tk g)
    hmem (by rw [width_resizeU', hov]; omega)
  rw [width_resizeU'] at he
  have hw : (soG.comb_out_valid N W ck r s iv id ov od dt tk g).width = 1 := by
    simp [soG.comb_out_valid, width_nbaFold, hov]
  rw [← extract_self hw]
  exact he

theorem comb_out_data_eq (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck r s iv id ov od dt tk g : LVec) (hod : od.width = W) :
    soG.comb_out_data N W ck r s iv id ov od dt tk g = (dt.extract 0 W).resizeU W := by
  have hmem : ("out_data", 0, (dt.extract 0 W).resizeU W) ∈
      soG.combQ N W ck r s iv id ov od dt tk g := by
    simp [soG.combQ, soG.p1C, hod]
  have he := extract_nbaFold_of_mem (x := od)
    (soG.combQ_disj N W hN hW hR32.1 hR32.2.1 hR32.2.2 ck r s iv id ov od dt tk g)
    hmem (by rw [width_resizeU', hod]; omega)
  rw [width_resizeU'] at he
  have hw : (soG.comb_out_data N W ck r s iv id ov od dt tk g).width = W := by
    simp [soG.comb_out_data, width_nbaFold, hod]
  rw [← extract_self hw]
  exact he

def gBit (W : Nat) (iv id dt tk : LVec) (k : Nat) : LVec :=
  (LVec.ofLogic
    (if ((LVec.ofLogic
          (if (iv.isKnownZero || (tk.extract k 1).isKnownZero) = true then Logic.l0
           else if (iv.condTrue && (tk.extract k 1).condTrue) = true then Logic.l1
           else Logic.lx)).isKnownZero ||
         (LVec.ofLogic (id.lt (dt.extract (k * W) W))).isKnownZero) = true then Logic.l0
     else if ((LVec.ofLogic
          (if (iv.isKnownZero || (tk.extract k 1).isKnownZero) = true then Logic.l0
           else if (iv.condTrue && (tk.extract k 1).condTrue) = true then Logic.l1
           else Logic.lx)).condTrue &&
         (LVec.ofLogic (id.lt (dt.extract (k * W) W))).condTrue) = true then Logic.l1
     else Logic.lx)).resizeU 1

theorem comb_g_extract (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck r s iv id ov od dt tk g : LVec) (hg : g.width = N) {k : Nat} (hk : k < N) :
    (soG.comb_g N W ck r s iv id ov od dt tk g).extract k 1 = gBit W iv id dt tk k := by
  have hland : (SymBinOp.land == SymBinOp.land) = true := rfl
  have hmem : ("g", k, gBit W iv id dt tk k) ∈ soG.combQ N W ck r s iv id ov od dt tk g := by
    simp only [soG.combQ, List.mem_append, List.mem_flatMap, List.mem_range]
    right; right
    refine ⟨k, hk, ?_⟩
    simp only [soG.gen_cmpC, gBit, hland, ↓reduceIte, List.mem_singleton]
  have hw : (gBit W iv id dt tk k).width = 1 := width_resizeU' _ 1
  have he := extract_nbaFold_of_mem (x := g)
    (soG.combQ_disj N W hN hW hR32.1 hR32.2.1 hR32.2.2 ck r s iv id ov od dt tk g)
    hmem (by rw [hw, hg]; omega)
  rw [hw] at he
  exact he

theorem gBit_iv_false (W : Nat) (id dt tk : LVec) (k : Nat) :
    gBit W (knownBit false) id dt tk k = knownBit false := by
  simp only [gBit, isKnownZero_knownBit, Bool.not_false, Bool.true_or, ↓reduceIte,
    isKnownZero_ofLogic_l0, ofLogic_l0_eq, resizeU_one_knownBit]

theorem gBit_tk_false (W : Nat) (iv id dt tk : LVec) (k : Nat)
    (ht : tk.extract k 1 = knownBit false) :
    gBit W iv id dt tk k = knownBit false := by
  simp only [gBit, ht, isKnownZero_knownBit, Bool.not_false, Bool.or_true, Bool.true_or, ↓reduceIte,
    isKnownZero_ofLogic_l0, ofLogic_l0_eq, resizeU_one_knownBit]

theorem gBit_known {W : Nat} (x d : BitVec W) (dt tk : LVec) (k : Nat)
    (ht : tk.extract k 1 = knownBit true) (hd : dt.extract (k * W) W = .ofBitVec d) :
    gBit W (knownBit true) (.ofBitVec x) dt tk k = knownBit (decide (x < d)) := by
  have hlt : (LVec.ofBitVec x).lt (LVec.ofBitVec d) = Logic.ofBool (decide (x < d)) := by
    simp [LVec.lt_ofBitVec, BitVec.lt_def]
  by_cases hxd : x < d
  · simp [gBit, ht, hd, hlt, hxd, Logic.ofBool, isKnownZero_knownBit, condTrue_knownBit',
      isKnownZero_ofLogic_l1, condTrue_ofLogic_l1, ofLogic_l1_eq, resizeU_one_knownBit]
  · simp [gBit, ht, hd, hlt, hxd, Logic.ofBool, isKnownZero_knownBit, condTrue_knownBit',
      isKnownZero_ofLogic_l0, isKnownZero_ofLogic_l1, ofLogic_l0_eq, resizeU_one_knownBit]

theorem edgeQ_eq (N W : Nat) (ck r s iv id ov od dt tk g : LVec) :
    soG.edgeQ N W ck r s iv id ov od dt tk g =
      soG.p2Q N W ck r s iv id ov od dt tk g ++
      (List.range (N - 1)).flatMap (fun k => soG.gen_cellQ N W k ck r s iv id ov od dt tk g) := by
  simp [soG.edgeQ, soG.p0Q, soG.p1Q, soG.gen_cmpQ]

theorem edgeQ_disj (N W : Nat)
    (ck r s iv id ov od dt tk g : LVec) :
    (soG.edgeQ N W ck r s iv id ov od dt tk g).Pairwise NbaDisj := by
  rw [edgeQ_eq]
  have hp2 : (soG.p2Q N W ck r s iv id ov od dt tk g).Pairwise NbaDisj := by
    unfold soG.p2Q
    split <;> simp [NbaDisj]
  have hcells : ((List.range (N - 1)).flatMap
      (fun k => soG.gen_cellQ N W k ck r s iv id ov od dt tk g)).Pairwise NbaDisj := by
    rw [List.pairwise_flatMap]
    refine ⟨fun k _ => ?_, ?_⟩
    · simp [soG.gen_cellQ, NbaDisj]
    · exact List.pairwise_lt_range.imp fun {a b} hab u hu v hv => by
        simp only [soG.gen_cellQ, List.mem_cons, List.not_mem_nil, or_false] at hu hv
        have hdisj : a * W + W ≤ b * W := mul_add_le_mul hab
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
          simp [NbaDisj] <;> omega
  rw [List.pairwise_append]
  refine ⟨hp2, hcells, fun u hu v hv => ?_⟩
  simp only [List.mem_flatMap, List.mem_range] at hv
  obtain ⟨k, hk, hv⟩ := hv
  have hdisj : k * W + W ≤ (N - 1) * W := mul_add_le_mul hk
  simp only [soG.gen_cellQ, List.mem_cons, List.not_mem_nil, or_false] at hv
  unfold soG.p2Q at hu
  split at hu
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
      simp [NbaDisj] <;> omega
  · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    subst hu
    rcases hv with rfl | rfl <;> simp [NbaDisj] <;> omega

theorem edgeQ_no_write (N W : Nat) (n : String) (hn1 : n ≠ "data") (hn2 : n ≠ "tok")
    (ck r s iv id ov od dt tk g : LVec) (x : LVec) :
    nbaFold n (soG.edgeQ N W ck r s iv id ov od dt tk g) x = x := by
  rw [edgeQ_eq]
  apply nbaFold_none
  intro u hu
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with hu | ⟨k, -, hu⟩
  · unfold soG.p2Q at hu
    split at hu
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Ne.symm hn1
      · exact Ne.symm hn2
    · simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      subst hu; exact Ne.symm hn2
  · simp only [soG.gen_cellQ, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact Ne.symm hn1
    · exact Ne.symm hn2

theorem next_tok_extract (N W : Nat)
    (ck r s iv id ov od dt tk g : LVec) (htk : tk.width = N)
    {k : Nat} (hk : k < N) :
    (nbaFold "tok" (soG.edgeQ N W ck r s iv id ov od dt tk g) tk).extract k 1 =
      if k + 1 < N then (r.ternary { bits := #[Logic.l0] } (tk.extract (k + 1) 1)).resizeU 1
      else (r.ternary { bits := #[Logic.l0] } iv).resizeU 1 := by
  by_cases hlt : k + 1 < N
  · simp only [hlt, ↓reduceIte]
    have hmem : ("tok", k, (r.ternary { bits := #[Logic.l0] } (tk.extract (k + 1) 1)).resizeU 1) ∈
        soG.edgeQ N W ck r s iv id ov od dt tk g := by
      rw [edgeQ_eq]
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      right
      refine ⟨k, by omega, ?_⟩
      simp [soG.gen_cellQ]
    have he := extract_nbaFold_of_mem (x := tk) (edgeQ_disj N W ck r s iv id ov od dt tk g) hmem
      (by rw [width_resizeU', htk]; omega)
    rw [width_resizeU'] at he; exact he
  · have hkeq : k = N - 1 := by omega
    subst hkeq
    simp only [hlt, ↓reduceIte]
    have hmem : ("tok", N - 1, (r.ternary { bits := #[Logic.l0] } iv).resizeU 1) ∈
        soG.edgeQ N W ck r s iv id ov od dt tk g := by
      rw [edgeQ_eq]
      simp only [List.mem_append]
      left
      unfold soG.p2Q
      split <;> simp
    have he := extract_nbaFold_of_mem (x := tk) (edgeQ_disj N W ck r s iv id ov od dt tk g) hmem
      (by rw [width_resizeU', htk]; omega)
    rw [width_resizeU'] at he; exact he

theorem next_data_extract_top_false (N W : Nat) (hN : 1 ≤ N)
    (ck r s iv id ov od dt tk g : LVec) (hdt : dt.width = N * W)
    (hg : g.extract (N - 1) 1 = knownBit false) :
    (nbaFold "data" (soG.edgeQ N W ck r s iv id ov od dt tk g) dt).extract ((N - 1) * W) W =
      id.resizeU W := by
  have hmem : ("data", (N - 1) * W, id.resizeU W) ∈ soG.edgeQ N W ck r s iv id ov od dt tk g := by
    rw [edgeQ_eq]
    simp only [List.mem_append]
    left
    simp only [soG.p2Q, hg, lnot_knownBit, Bool.not_false, condTrue_knownBit', ↓reduceIte,
      List.mem_append, List.mem_singleton, true_or]
  have hle : (N - 1) * W + W ≤ N * W := mul_add_le_mul (show N - 1 < N by omega)
  have he := extract_nbaFold_of_mem (x := dt) (edgeQ_disj N W ck r s iv id ov od dt tk g) hmem
    (by rw [width_resizeU', hdt]; exact hle)
  rw [width_resizeU'] at he; exact he

theorem next_data_extract_top_true (N W : Nat)
    (ck r s iv id ov od dt tk g : LVec)
    (hg : g.extract (N - 1) 1 = knownBit true) :
    (nbaFold "data" (soG.edgeQ N W ck r s iv id ov od dt tk g) dt).extract ((N - 1) * W) W =
      dt.extract ((N - 1) * W) W := by
  rw [edgeQ_eq]
  apply extract_nbaFold_of_disj
  intro u hu
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hu
  rcases hu with hu | ⟨k, hk, hu⟩
  · simp only [soG.p2Q, hg, lnot_knownBit, Bool.not_true, condTrue_knownBit', Bool.false_eq_true,
      ↓reduceIte, List.nil_append, List.mem_singleton] at hu
    subst hu; left; simp
  · simp only [soG.gen_cellQ, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · right; left; rw [width_resizeU']; exact mul_add_le_mul hk
    · left; simp

theorem cell_val_eval (W : Nat) (id dt g : LVec) (k : Nat)
    (b0 b1 : Bool) (h0 : g.extract k 1 = knownBit b0) (h1 : g.extract (k + 1) 1 = knownBit b1)
    (hmono : b0 = true → b1 = true) (res : BitVec W)
    (hres : (if b1 = false then dt.extract ((k + 1) * W) W
             else if b0 = false then id.extract 0 W
             else dt.extract (k * W) W) = LVec.ofBitVec res) :
    ((((LVec.replVec W (LVec.concatMany #[LVec.ofLogic (g.extract (k + 1) 1).lnot])).and
          (dt.extract ((k + 1) * W) W)).or
      ((LVec.replVec W
          (LVec.concatMany
            #[LVec.ofLogic
              (if (SymBinOp.land == SymBinOp.land) = true then
                if ((g.extract (k + 1) 1).isKnownZero ||
                    (LVec.ofLogic (g.extract k 1).lnot).isKnownZero) = true then Logic.l0
                else if ((g.extract (k + 1) 1).condTrue &&
                    (LVec.ofLogic (g.extract k 1).lnot).condTrue) = true then Logic.l1
                else Logic.lx
              else
                if ((g.extract (k + 1) 1).condTrue ||
                    (LVec.ofLogic (g.extract k 1).lnot).condTrue) = true then Logic.l1
                else if ((g.extract (k + 1) 1).isKnownZero &&
                    (LVec.ofLogic (g.extract k 1).lnot).isKnownZero) = true then Logic.l0
                else Logic.lx)])).and (id.extract 0 W))).or
      ((LVec.replVec W (LVec.concatMany #[g.extract k 1])).and (dt.extract (k * W) W))).resizeU W =
    LVec.ofBitVec res := by
  have hw0 : (dt.extract (k * W) W).width = W := LVec.width_extract _ _ _
  have hw1 : (dt.extract ((k + 1) * W) W).width = W := LVec.width_extract _ _ _
  have hwid : (id.extract 0 W).width = W := LVec.width_extract _ _ _
  have hland : (SymBinOp.land == SymBinOp.land) = true := rfl
  cases b1 <;> cases b0
  · simp only [↓reduceIte] at hres
    rw [h0, h1, hres]
    simp only [hland, lnot_knownBit, isKnownZero_knownBit, Bool.not_false, Bool.true_or, ↓reduceIte,
      concatMany_single, ofLogic_l0_eq]
    rw [repl_one_and_bv, repl_zero_and _ hwid, repl_zero_and _ hw0,
      or_zero_right_bv, or_zero_right_bv, resizeU_eq_self (by simp)]
  · exact absurd (hmono rfl) (by decide)
  · simp only [Bool.true_eq_false, ↓reduceIte] at hres
    rw [h0, h1, hres]
    simp only [hland, lnot_knownBit, isKnownZero_knownBit, condTrue_knownBit', Bool.not_true,
      Bool.not_false, Bool.or_self, Bool.and_self, Bool.false_eq_true, ↓reduceIte,
      concatMany_single, ofLogic_l1_eq]
    rw [repl_zero_and _ hw1, repl_one_and_bv, repl_zero_and _ hw0,
      or_zero_left_bv, or_zero_right_bv, resizeU_eq_self (by simp)]
  · simp only [Bool.true_eq_false, ↓reduceIte] at hres
    rw [h0, h1, hres]
    simp only [hland, lnot_knownBit, isKnownZero_knownBit, Bool.not_true, Bool.not_false,
      Bool.or_true, ↓reduceIte, concatMany_single, ofLogic_l0_eq]
    rw [repl_zero_and _ hw1, repl_zero_and _ hwid, repl_one_and_bv,
      or_zero_right_bv, or_zero_left_bv, resizeU_eq_self (by simp)]

theorem next_data_extract_cell (N W : Nat)
    (ck r s iv id ov od dt tk g : LVec) (hdt : dt.width = N * W)
    {k : Nat} (hk : k + 1 < N) (b0 b1 : Bool)
    (h0 : g.extract k 1 = knownBit b0) (h1 : g.extract (k + 1) 1 = knownBit b1)
    (hmono : b0 = true → b1 = true) (res : BitVec W)
    (hres : (if b1 = false then dt.extract ((k + 1) * W) W
             else if b0 = false then id.extract 0 W
             else dt.extract (k * W) W) = LVec.ofBitVec res) :
    (nbaFold "data" (soG.edgeQ N W ck r s iv id ov od dt tk g) dt).extract (k * W) W =
      LVec.ofBitVec res := by
  have hmem : ∃ v, ("data", k * W, v) ∈ soG.edgeQ N W ck r s iv id ov od dt tk g ∧
      v = LVec.ofBitVec res := by
    refine ⟨_, ?_, cell_val_eval W id dt g k b0 b1 h0 h1 hmono res hres⟩
    rw [edgeQ_eq]
    simp only [List.mem_append, List.mem_flatMap, List.mem_range]
    right
    refine ⟨k, by omega, ?_⟩
    simp [soG.gen_cellQ]
  obtain ⟨v, hmem, hv⟩ := hmem
  have hvw : v.width = W := by rw [hv]; simp
  have hle : k * W + W ≤ N * W := mul_add_le_mul (by omega)
  have he := extract_nbaFold_of_mem (x := dt) (edgeQ_disj N W ck r s iv id ov od dt tk g) hmem
    (by rw [hvw, hdt]; exact hle)
  rw [hvw] at he
  rw [he, hv]

/-! ## 4. Shape invariant and `sortAsc` arithmetic -/

def Shp (N W : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk g, st = soG.St ck r s iv id ov od dt tk g ∧
    (ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N ∧ g.width = N)

theorem next_shp (N W : Nat) (ck r s iv id ov od dt tk g : LVec)
    (hw : ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N ∧ g.width = N) :
    Shp N W (soG.next N W ck r s iv id ov od dt tk g) := by
  refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, ?_⟩
  simp [soG.comb_out_valid, soG.comb_out_data, soG.comb_g, width_nbaFold, hw]

theorem so_init (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Shp N W (initState2 (design.sem N W)) := by
  rw [soG.init N W hN hW hR32.1 hR32.2.1 hR32.2.2]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by simp⟩

theorem so_powerUp (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) (st : SvState)
    (h : PowerUp (design.sem N W) st) : Shp N W st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, -, -, -, -, -, h6, h7, h8, h9, h10⟩ :=
    soG.powerUp N W hN hW hR32.1 hR32.2.1 hR32.2.2 st h
  exact ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, h6, h7, h8, h9, h10⟩

open Tasks.Sorter (insertAsc sortAsc)

abbrev Srt {W : Nat} (l : List (BitVec W)) : Prop := l.Pairwise fun a b => a.toNat ≤ b.toNat

theorem mem_ins {W : Nat} (x y : BitVec W) : ∀ l, y ∈ insertAsc x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insertAsc]
  | b :: l => by unfold insertAsc; split <;> simp [mem_ins x y l, or_left_comm]

theorem srt_ins {W : Nat} (x : BitVec W) : ∀ l, Srt l → Srt (insertAsc x l)
  | [], _ => by simp [insertAsc]
  | b :: l, h => by
    have ⟨hb, hl⟩ := List.pairwise_cons.mp h
    unfold insertAsc
    split
    · next hx =>
      refine .cons (fun y hy => ?_) h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact Nat.le_trans hx (hb y hy)
    · next hx =>
      refine .cons (fun y hy => ?_) (srt_ins x l hl)
      rcases (mem_ins x y l).mp hy with rfl | hy
      · omega
      · exact hb y hy

theorem len_ins {W : Nat} (x : BitVec W) : ∀ l, (insertAsc x l).length = l.length + 1
  | [] => rfl
  | b :: l => by unfold insertAsc; split <;> simp [len_ins x l]

theorem len_sort {W : Nat} : ∀ l : List (BitVec W), (sortAsc l).length = l.length
  | [] => rfl
  | a :: l => by simp [sortAsc, len_ins, len_sort l]

theorem srt_sort {W : Nat} : ∀ l : List (BitVec W), Srt (sortAsc l)
  | [] => .nil
  | _ :: l => srt_ins _ _ (srt_sort l)

theorem ins_comm_lt {W : Nat} {a b : BitVec W} (h : a.toNat < b.toNat) :
    ∀ l, insertAsc a (insertAsc b l) = insertAsc b (insertAsc a l)
  | [] => by simp [insertAsc, Nat.le_of_lt h, Nat.not_le.mpr h]
  | c :: l => by
    by_cases hb : b.toNat ≤ c.toNat
    · simp [insertAsc, hb, Nat.le_of_lt h, Nat.not_le.mpr h, show a.toNat ≤ c.toNat by omega]
    · by_cases ha : a.toNat ≤ c.toNat
      · simp [insertAsc, hb, ha, Nat.not_le.mpr h]
      · simp [insertAsc, hb, ha, ins_comm_lt h l]

theorem ins_comm {W : Nat} (a b : BitVec W) (l : List (BitVec W)) :
    insertAsc a (insertAsc b l) = insertAsc b (insertAsc a l) := by
  rcases Nat.lt_trichotomy a.toNat b.toNat with h | h | h
  · exact ins_comm_lt h l
  · rw [BitVec.eq_of_toNat_eq h]
  · exact (ins_comm_lt h l).symm

theorem sort_snoc {W : Nat} (x : BitVec W) : ∀ l : List (BitVec W),
    sortAsc (l ++ [x]) = insertAsc x (sortAsc l)
  | [] => rfl
  | a :: l => by simp only [List.cons_append, sortAsc, sort_snoc x l]; exact ins_comm ..

theorem getD_mem {W : Nat} {L : List (BitVec W)} {i : Nat} (hi : i < L.length) :
    L.getD i 0 ∈ L := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem srt_getD_mono {W : Nat} : ∀ {L : List (BitVec W)}, Srt L →
    ∀ {i j}, i ≤ j → j < L.length → (L.getD i 0).toNat ≤ (L.getD j 0).toNat
  | [], _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | b :: L, hs, i, j, hij, hj => by
    have ⟨hb, hL⟩ := List.pairwise_cons.mp hs
    cases i with
    | zero =>
      cases j with
      | zero => exact Nat.le_refl _
      | succ j =>
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        exact hb _ (getD_mem (by simp at hj; omega))
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getD_cons_succ]
        exact srt_getD_mono hL (by omega) (by simp at hj; omega)

theorem getD_insertAsc {W : Nat} (x : BitVec W) : ∀ (L : List (BitVec W)), Srt L →
    ∀ i, i ≤ L.length →
      (insertAsc x L).getD i 0 =
        if i < L.length ∧ ¬ x < L.getD i 0 then L.getD i 0
        else if 0 < i ∧ x < L.getD (i - 1) 0 then L.getD (i - 1) 0
        else x
  | [], _, i, hi => by
    obtain rfl : i = 0 := by simp at hi; omega
    simp [insertAsc]
  | b :: L, hs, i, hi => by
    have ⟨hb, hL⟩ := List.pairwise_cons.mp hs
    unfold insertAsc
    by_cases hxb : x.toNat ≤ b.toNat
    · simp only [hxb, ↓reduceIte]
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.length_cons, Nat.zero_lt_succ, true_and,
          Nat.lt_irrefl, false_and, ↓reduceIte]
        by_cases hlt : x < b
        · simp only [hlt, not_true_eq_false, ↓reduceIte]
        · simp only [hlt, not_false_eq_true, ↓reduceIte]
          exact BitVec.eq_of_toNat_eq (by rw [BitVec.lt_def] at hlt; omega)
      | succ i =>
        simp only [List.getD_cons_succ, List.length_cons, Nat.add_sub_cancel, Nat.zero_lt_succ,
          true_and]
        have hiL : i ≤ L.length := by simp at hi; omega
        by_cases h1 : i < L.length ∧ ¬ x < L.getD i 0
        · rw [if_pos (show i + 1 < L.length + 1 ∧ ¬ x < L.getD i 0 from ⟨by omega, h1.2⟩)]
          have hle1 : b.toNat ≤ (L.getD i 0).toNat := hb _ (getD_mem h1.1)
          have hxi : (L.getD i 0).toNat ≤ x.toNat := by rw [BitVec.lt_def] at h1; omega
          cases i with
          | zero =>
            simp only [List.getD_cons_zero]
            exact BitVec.eq_of_toNat_eq (by omega)
          | succ j =>
            simp only [List.getD_cons_succ]
            have hle_j : b.toNat ≤ (L.getD j 0).toNat := hb _ (getD_mem (by omega))
            have hle_ji : (L.getD j 0).toNat ≤ (L.getD (j + 1) 0).toNat :=
              srt_getD_mono hL (by omega) h1.1
            exact BitVec.eq_of_toNat_eq (by omega)
        · have hnot1 : ¬ (i + 1 < L.length + 1 ∧ ¬ x < L.getD i 0) := fun h => h1 ⟨by omega, h.2⟩
          simp only [hnot1, ↓reduceIte]
          cases i with
          | zero =>
            simp only [List.getD_cons_zero]
            by_cases hlt : x < b
            · simp only [hlt, ↓reduceIte]
            · simp only [hlt, ↓reduceIte]
              exact BitVec.eq_of_toNat_eq (by rw [BitVec.lt_def] at hlt; omega)
          | succ j =>
            simp only [List.getD_cons_succ]
            have hle_j : b.toNat ≤ (L.getD j 0).toNat := hb _ (getD_mem (by omega))
            by_cases hlt : x < L.getD j 0
            · simp only [hlt, ↓reduceIte]
            · simp only [hlt, ↓reduceIte]
              exact BitVec.eq_of_toNat_eq (by rw [BitVec.lt_def] at hlt; omega)
    · simp only [hxb, ↓reduceIte]
      have hnb : ¬ x < b := by rw [BitVec.lt_def]; omega
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.length_cons, Nat.zero_lt_succ, true_and, hnb,
          not_false_eq_true, ↓reduceIte]
      | succ i =>
        simp only [List.getD_cons_succ, List.length_cons, Nat.add_sub_cancel, Nat.zero_lt_succ,
          true_and]
        rw [getD_insertAsc x L hL i (by simp at hi; omega)]
        cases i with
        | zero =>
          simp only [Nat.lt_irrefl, false_and, ↓reduceIte, List.getD_cons_zero, hnb,
            show (0 + 1 < L.length + 1) ↔ (0 < L.length) by omega]
        | succ j =>
          simp only [Nat.zero_lt_succ, true_and, Nat.add_sub_cancel, List.getD_cons_succ,
            show (j + 1 + 1 < L.length + 1) ↔ (j + 1 < L.length) by omega]

/-! ## 5. Hardware phase invariant and `StreamTask.PhaseModel` -/

def tokBit (N j k : Nat) : Bool := decide (N ≤ j + k ∧ j + k < 2 * N)

def ovb (N j : Nat) : Bool := decide (N ≤ j ∧ j < 2 * N)

theorem tokBit_zero (N j : Nat) : tokBit N j 0 = ovb N j := by
  simp [tokBit, ovb]

theorem tokBit_step {N j k : Nat} (b : Bool) (hb : b = decide (j < N)) (hk : k < N) :
    (if k + 1 < N then tokBit N j (k + 1) else b) = tokBit N (j + 1) k := by
  split
  · simp only [tokBit, decide_eq_decide]; omega
  · rw [hb]; simp only [tokBit, decide_eq_decide]; omega

def CellsOk (N W : Nat) (ys : List (BitVec W)) (j : Nat) (dt : LVec) : Prop :=
  dt.width = N * W ∧
  ∀ k, k < N → tokBit N j k = true →
    dt.extract (k * W) W = .ofBitVec ((sortAsc ys).getD (k + j - N) 0)

def TksOk (N : Nat) (f : Nat → Bool) (tk : LVec) : Prop :=
  tk.width = N ∧ ∀ k, k < N → tk.extract k 1 = knownBit (f k)

theorem next_reset_state (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck s iv id ov od dt tk g : LVec)
    (hov : ov.width = 1) (hdt : dt.width = N * W) (htk : tk.width = N) :
    ∃ ov' od' dt' tk' g',
      soG.next N W ck (knownBit true) s iv id ov od dt tk g =
        soG.St ck (knownBit true) s iv id ov' od' dt' tk' g' ∧
      ov' = knownBit false ∧ TksOk N (fun _ => false) tk' ∧ dt'.width = N * W := by
  unfold soG.next soG.comb
  have heq_ck := edgeQ_no_write N W "clk" (by decide) (by decide)
  have heq_r := edgeQ_no_write N W "rst" (by decide) (by decide)
  have heq_s := edgeQ_no_write N W "start" (by decide) (by decide)
  have heq_iv := edgeQ_no_write N W "in_valid" (by decide) (by decide)
  have heq_id := edgeQ_no_write N W "in_data" (by decide) (by decide)
  have heq_ov := edgeQ_no_write N W "out_valid" (by decide) (by decide)
  have heq_od := edgeQ_no_write N W "out_data" (by decide) (by decide)
  have heq_g := edgeQ_no_write N W "g" (by decide) (by decide)
  simp only [heq_ck, heq_r, heq_s, heq_iv, heq_id, heq_ov, heq_od, heq_g]
  let ovc := soG.comb_out_valid N W ck (knownBit true) s iv id ov od dt tk g
  let odc := soG.comb_out_data N W ck (knownBit true) s iv id ov od dt tk g
  let gc := soG.comb_g N W ck (knownBit true) s iv id ov od dt tk g
  let tk' := nbaFold "tok" (soG.edgeQ N W ck (knownBit true) s iv id ovc odc dt tk gc) tk
  let dt' := nbaFold "data" (soG.edgeQ N W ck (knownBit true) s iv id ovc odc dt tk gc) dt
  have htk'w : tk'.width = N := by simp [tk', width_nbaFold, htk]
  have hdt'w : dt'.width = N * W := by simp [dt', width_nbaFold, hdt]
  have htk' : TksOk N (fun _ => false) tk' := by
    refine ⟨htk'w, fun k hk => ?_⟩
    show (nbaFold "tok" _ tk).extract k 1 = knownBit false
    rw [next_tok_extract N W _ _ _ _ _ _ _ _ _ _ htk hk]
    split <;>
      simp only [LVec.ternary, condTrue_knownBit', ↓reduceIte, LVec.resizeU_one_l0, knownBit]
  have hovw : ovc.width = 1 := by simp [ovc, soG.comb_out_valid, width_nbaFold, hov]
  refine ⟨_, _, dt', tk', _, rfl, ?_, htk', hdt'w⟩
  rw [comb_out_valid_eq N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hovw, htk'.2 0 hN]
  exact resizeU_one_knownBit false

theorem next_run_drain (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck s id ov od dt tk g : LVec) (f : Nat → Bool)
    (hov : ov.width = 1) (hod : od.width = W)
    (hdt : dt.width = N * W) (htk : TksOk N f tk) (hg : g.width = N) :
    ∃ ov' od' dt' tk' g',
      soG.next N W ck (knownBit false) s (knownBit false) id ov od dt tk g =
        soG.St ck (knownBit false) s (knownBit false) id ov' od' dt' tk' g' ∧
      TksOk N (fun k => if k + 1 < N then f (k + 1) else false) tk' ∧
      dt'.width = N * W ∧
      (∀ k (v : BitVec W), k + 1 < N → dt.extract ((k + 1) * W) W = .ofBitVec v →
        dt'.extract (k * W) W = .ofBitVec v) ∧
      ov' = knownBit (if 1 < N then f 1 else false) ∧
      od' = dt'.extract 0 W := by
  unfold soG.next soG.comb
  have heq_ck := edgeQ_no_write N W "clk" (by decide) (by decide)
  have heq_r := edgeQ_no_write N W "rst" (by decide) (by decide)
  have heq_s := edgeQ_no_write N W "start" (by decide) (by decide)
  have heq_iv := edgeQ_no_write N W "in_valid" (by decide) (by decide)
  have heq_id := edgeQ_no_write N W "in_data" (by decide) (by decide)
  have heq_ov := edgeQ_no_write N W "out_valid" (by decide) (by decide)
  have heq_od := edgeQ_no_write N W "out_data" (by decide) (by decide)
  have heq_g := edgeQ_no_write N W "g" (by decide) (by decide)
  simp only [heq_ck, heq_r, heq_s, heq_iv, heq_id, heq_ov, heq_od, heq_g]
  let gc := soG.comb_g N W ck (knownBit false) s (knownBit false) id ov od dt tk g
  let ovc := soG.comb_out_valid N W ck (knownBit false) s (knownBit false) id ov od dt tk g
  let odc := soG.comb_out_data N W ck (knownBit false) s (knownBit false) id ov od dt tk g
  let tk' := nbaFold "tok" (soG.edgeQ N W ck (knownBit false) s (knownBit false) id ovc odc dt tk gc) tk
  let dt' := nbaFold "data" (soG.edgeQ N W ck (knownBit false) s (knownBit false) id ovc odc dt tk gc) dt
  have hgc : ∀ k, k < N → gc.extract k 1 = knownBit false := fun k hk => by
    show (soG.comb_g N W _ _ _ _ _ _ _ _ _ _).extract k 1 = knownBit false
    rw [comb_g_extract N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hg hk, gBit_iv_false]
  have htk' : TksOk N (fun k => if k + 1 < N then f (k + 1) else false) tk' := by
    refine ⟨by simp [tk', width_nbaFold, htk.1], fun k hk => ?_⟩
    show (nbaFold "tok" _ tk).extract k 1 = _
    rw [next_tok_extract N W _ _ _ _ _ _ _ _ _ _ htk.1 hk]
    by_cases hlt : k + 1 < N
    · simp only [hlt, ↓reduceIte]
      rw [htk.2 (k + 1) hlt]
      simp only [LVec.ternary, condTrue_knownBit', isKnownZero_knownBit, Bool.false_eq_true,
        Bool.not_false, ↓reduceIte, resizeU_one_knownBit]
    · simp only [hlt, ↓reduceIte, LVec.ternary, condTrue_knownBit', isKnownZero_knownBit,
        Bool.false_eq_true, Bool.not_false, resizeU_one_knownBit]
  have hdt'w : dt'.width = N * W := by simp [dt', width_nbaFold, hdt]
  have hdt'c : ∀ k (v : BitVec W), k + 1 < N → dt.extract ((k + 1) * W) W = .ofBitVec v →
      dt'.extract (k * W) W = .ofBitVec v := by
    intro k v hk hv
    show (nbaFold "data" _ dt).extract (k * W) W = .ofBitVec v
    exact next_data_extract_cell N W _ _ _ _ _ _ _ _ _ _ hdt hk false false
      (hgc k (by omega)) (hgc (k + 1) hk) (fun h => absurd h (by decide)) v (by simpa using hv)
  have hovw : ovc.width = 1 := by simp [ovc, soG.comb_out_valid, width_nbaFold, hov]
  have hodw : odc.width = W := by simp [odc, soG.comb_out_data, width_nbaFold, hod]
  refine ⟨_, _, dt', tk', _, rfl, htk', hdt'w, hdt'c, ?_, ?_⟩
  · rw [comb_out_valid_eq N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hovw, htk'.2 0 hN]
    exact resizeU_one_knownBit _
  · rw [comb_out_data_eq N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hodw]
    exact resizeU_eq_self (LVec.width_extract _ _ _)

theorem next_run_feed (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W)
    (ck s ov od dt tk g : LVec) (ys : List (BitVec W)) (j : Nat) (x : BitVec W)
    (hl : ys.length = j) (hj : j < N)
    (hov : ov.width = 1) (hod : od.width = W) (hg : g.width = N)
    (hdt : CellsOk N W ys j dt) (htk : TksOk N (tokBit N j) tk) :
    ∃ ov' od' dt' tk' g',
      soG.next N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ov od dt tk g =
        soG.St ck (knownBit false) s (knownBit true) (.ofBitVec x) ov' od' dt' tk' g' ∧
      TksOk N (tokBit N (j + 1)) tk' ∧
      CellsOk N W (ys ++ [x]) (j + 1) dt' ∧
      ov' = knownBit (ovb N (j + 1)) ∧
      od' = dt'.extract 0 W := by
  unfold soG.next soG.comb
  have heq_ck := edgeQ_no_write N W "clk" (by decide) (by decide)
  have heq_r := edgeQ_no_write N W "rst" (by decide) (by decide)
  have heq_s := edgeQ_no_write N W "start" (by decide) (by decide)
  have heq_iv := edgeQ_no_write N W "in_valid" (by decide) (by decide)
  have heq_id := edgeQ_no_write N W "in_data" (by decide) (by decide)
  have heq_ov := edgeQ_no_write N W "out_valid" (by decide) (by decide)
  have heq_od := edgeQ_no_write N W "out_data" (by decide) (by decide)
  have heq_g := edgeQ_no_write N W "g" (by decide) (by decide)
  simp only [heq_ck, heq_r, heq_s, heq_iv, heq_id, heq_ov, heq_od, heq_g]
  let gc := soG.comb_g N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ov od dt tk g
  let ovc := soG.comb_out_valid N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ov od dt tk g
  let odc := soG.comb_out_data N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ov od dt tk g
  let tk' := nbaFold "tok" (soG.edgeQ N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ovc odc dt tk gc) tk
  let dt' := nbaFold "data" (soG.edgeQ N W ck (knownBit false) s (knownBit true) (.ofBitVec x) ovc odc dt tk gc) dt
  let L := sortAsc ys
  have hLlen : L.length = j := by rw [len_sort, hl]
  have hLsrt : Srt L := srt_sort ys
  let gf : Nat → Bool := fun k => decide (N ≤ j + k ∧ x < L.getD (k + j - N) 0)
  have hgc : ∀ k, k < N → gc.extract k 1 = knownBit (gf k) := by
    intro k hk
    show (soG.comb_g N W _ _ _ _ _ _ _ _ _ _).extract k 1 = knownBit (gf k)
    rw [comb_g_extract N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hg hk]
    by_cases htkk : tokBit N j k = true
    · have hge : N ≤ j + k := by simp only [tokBit, decide_eq_true_eq] at htkk; omega
      have htk1 : tk.extract k 1 = knownBit true := by rw [htk.2 k hk, htkk]
      have hdk : dt.extract (k * W) W = .ofBitVec (L.getD (k + j - N) 0) := hdt.2 k hk htkk
      rw [gBit_known x _ dt tk k htk1 hdk]
      simp [gf, hge]
    · have htkf : tokBit N j k = false := by cases h : tokBit N j k <;> simp_all
      have hlt : ¬ N ≤ j + k := by simp only [tokBit, decide_eq_false_iff_not] at htkf; omega
      have htk0 : tk.extract k 1 = knownBit false := by rw [htk.2 k hk, htkf]
      rw [gBit_tk_false W _ _ dt tk k htk0]
      simp [gf, hlt]
  have hmono : ∀ k, k + 1 < N → gf k = true → gf (k + 1) = true := by
    intro k hk hg0
    simp only [gf, decide_eq_true_eq] at hg0 ⊢
    refine ⟨by omega, ?_⟩
    have hle := srt_getD_mono hLsrt (i := k + j - N) (j := k + 1 + j - N) (by omega) (by omega)
    rw [BitVec.lt_def] at hg0 ⊢; omega
  have htk' : TksOk N (tokBit N (j + 1)) tk' := by
    refine ⟨by simp [tk', width_nbaFold, htk.1], fun k hk => ?_⟩
    show (nbaFold "tok" _ tk).extract k 1 = _
    rw [next_tok_extract N W _ _ _ _ _ _ _ _ _ _ htk.1 hk]
    have hstep := tokBit_step (N := N) (j := j) (k := k) true (by simp [hj]) hk
    rw [← hstep]
    split
    · next hlt =>
      rw [htk.2 (k + 1) hlt]
      simp only [LVec.ternary, condTrue_knownBit', isKnownZero_knownBit, Bool.false_eq_true,
        Bool.not_false, ↓reduceIte, resizeU_one_knownBit]
    · simp only [LVec.ternary, condTrue_knownBit', isKnownZero_knownBit, Bool.false_eq_true,
        Bool.not_false, ↓reduceIte, resizeU_one_knownBit]
  have hxext : (LVec.ofBitVec x).extract 0 W = LVec.ofBitVec x := extract_self (by simp)
  have hdt' : CellsOk N W (ys ++ [x]) (j + 1) dt' := by
    refine ⟨by simp [dt', width_nbaFold, hdt.1], fun k hk hvk => ?_⟩
    show (nbaFold "data" _ dt).extract (k * W) W = _
    rw [sort_snoc]
    have hge : N ≤ j + 1 + k := by simp only [tokBit, decide_eq_true_eq] at hvk; omega
    let idx := k + (j + 1) - N
    have hidx : idx ≤ L.length := by omega
    rw [getD_insertAsc x L hLsrt idx hidx]
    by_cases hlt : k + 1 < N
    · have hidx_lt : idx < L.length := by omega
      have hidx_eq : k + 1 + j - N = idx := by omega
      have htk1 : tokBit N j (k + 1) = true := by simp only [tokBit, decide_eq_true_eq]; omega
      have hdt1 : dt.extract ((k + 1) * W) W = .ofBitVec (L.getD idx 0) := by
        rw [← hidx_eq]; exact hdt.2 (k + 1) hlt htk1
      by_cases hg1 : gf (k + 1) = false
      · have hnx : ¬ x < L.getD idx 0 := by
          simp only [gf, hidx_eq, decide_eq_false_iff_not] at hg1
          intro hx; exact hg1 ⟨by omega, hx⟩
        rw [next_data_extract_cell N W _ _ _ _ _ _ _ _ _ _ hdt.1 hlt
          (gf k) (gf (k + 1)) (hgc k hk) (hgc (k + 1) hlt) (hmono k hlt) (L.getD idx 0)
          (by simp only [hg1, ↓reduceIte, hdt1])]
        simp only [hidx_lt, hnx, not_false_eq_true, and_self, ↓reduceIte]
      · have hg1t : gf (k + 1) = true := by cases h : gf (k + 1) <;> simp_all
        have hx1 : x < L.getD idx 0 := by
          simp only [gf, hidx_eq, decide_eq_true_eq] at hg1t; exact hg1t.2
        by_cases hg0 : gf k = false
        · have hnot0 : ¬ (0 < idx ∧ x < L.getD (idx - 1) 0) := by
            rintro ⟨hpos, hx0⟩
            have hidx_m : k + j - N = idx - 1 := by omega
            simp only [gf, hidx_m, decide_eq_false_iff_not] at hg0
            exact hg0 ⟨by omega, hx0⟩
          rw [next_data_extract_cell N W _ _ _ _ _ _ _ _ _ _ hdt.1 hlt
            (gf k) (gf (k + 1)) (hgc k hk) (hgc (k + 1) hlt) (hmono k hlt) x
            (by simp only [hg1t, hg0, Bool.true_eq_false, ↓reduceIte, hxext])]
          simp only [hx1, not_true_eq_false, and_false, hnot0, ↓reduceIte]
        · have hg0t : gf k = true := by cases h : gf k <;> simp_all
          have hg0p : N ≤ j + k ∧ x < L.getD (k + j - N) 0 := by simpa [gf] using hg0t
          have hpos : 0 < idx := by omega
          have hidx_m : k + j - N = idx - 1 := by omega
          have htk0 : tokBit N j k = true := by simp only [tokBit, decide_eq_true_eq]; omega
          have hdt0 : dt.extract (k * W) W = .ofBitVec (L.getD (idx - 1) 0) := by
            rw [← hidx_m]; exact hdt.2 k hk htk0
          have hx0 : x < L.getD (idx - 1) 0 := by rw [← hidx_m]; exact hg0p.2
          rw [next_data_extract_cell N W _ _ _ _ _ _ _ _ _ _ hdt.1 hlt
            (gf k) (gf (k + 1)) (hgc k hk) (hgc (k + 1) hlt) (hmono k hlt) (L.getD (idx - 1) 0)
            (by simp only [hg1t, hg0t, Bool.true_eq_false, ↓reduceIte, hdt0])]
          simp only [hx1, not_true_eq_false, and_false, hpos, hx0, and_self, ↓reduceIte]
    · have hkeq : k = N - 1 := by omega
      subst hkeq
      have hnotlt : ¬ idx < L.length := by omega
      by_cases hgtop : gf (N - 1) = false
      · rw [next_data_extract_top_false N W hN _ _ _ _ _ _ _ _ _ _ hdt.1
          (by rw [hgc (N - 1) hk, hgtop])]
        rw [LVec.resizeU_ofBitVec, BitVec.setWidth_eq]
        have hnot0 : ¬ (0 < idx ∧ x < L.getD (idx - 1) 0) := by
          rintro ⟨hpos, hx0⟩
          have hidx_m : N - 1 + j - N = idx - 1 := by omega
          simp only [gf, hidx_m, decide_eq_false_iff_not] at hgtop
          exact hgtop ⟨by omega, hx0⟩
        simp only [hnotlt, false_and, ↓reduceIte, hnot0]
      · have hgtopt : gf (N - 1) = true := by cases h : gf (N - 1) <;> simp_all
        rw [next_data_extract_top_true N W _ _ _ _ _ _ _ _ _ _
          (by rw [hgc (N - 1) hk, hgtopt])]
        simp only [gf, decide_eq_true_eq] at hgtopt
        have hpos : 0 < idx := by omega
        have hidx_m : N - 1 + j - N = idx - 1 := by omega
        have htk0 : tokBit N j (N - 1) = true := by simp only [tokBit, decide_eq_true_eq]; omega
        have hdt0 : dt.extract ((N - 1) * W) W = .ofBitVec (L.getD (idx - 1) 0) := by
          rw [← hidx_m]; exact hdt.2 (N - 1) hk htk0
        have hx0 : x < L.getD (idx - 1) 0 := by rw [← hidx_m]; exact hgtopt.2
        simp only [hnotlt, false_and, ↓reduceIte, hpos, hx0, and_self, hdt0]
  have hovw : ovc.width = 1 := by simp [ovc, soG.comb_out_valid, width_nbaFold, hov]
  have hodw : odc.width = W := by simp [odc, soG.comb_out_data, width_nbaFold, hod]
  refine ⟨_, _, dt', tk', _, rfl, htk', hdt', ?_, ?_⟩
  · rw [comb_out_valid_eq N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hovw, htk'.2 0 hN, tokBit_zero]
    exact resizeU_one_knownBit _
  · rw [comb_out_data_eq N W hN hW hR32 _ _ _ _ _ _ _ _ _ _ hodw]
    exact resizeU_eq_self (LVec.width_extract _ _ _)

def Stp (N W : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk g, prev = soG.St ck r s iv id ov od dt tk g ∧
    (ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N ∧ g.width = N) ∧
    st = soG.next N W (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s)
      (appIn e "in_valid" iv) (appIn e "in_data" id) ov od dt tk g

theorem St_inj {ck r s iv id ov od dt tk g ck' r' s' iv' id' ov' od' dt' tk' g' : LVec}
    (h : soG.St ck r s iv id ov od dt tk g = soG.St ck' r' s' iv' id' ov' od' dt' tk' g') :
    ov = ov' ∧ od = od' ∧ dt = dt' ∧ tk = tk' := by
  simp only [soG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

theorem out_spec_eq {N W : Nat} (xs : List (BitVec W)) (hx : xs.length = N) :
    List.map (·.2) (List.filter (·.1)
      ((List.range N).map fun i => (ovb N (N + i), (sortAsc xs).getD (N + i - N) 0))) = sortAsc xs := by
  have h : ((List.range N).map fun i => (ovb N (N + i), (sortAsc xs).getD (N + i - N) 0)) =
      (List.range N).map fun i => (true, (sortAsc xs).getD i 0) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi; simp [ovb, show N + i - N = i by omega]; omega
  rw [h, List.filter_eq_self.mpr (by simp), List.map_map]
  exact List.ext_getElem (by simp [len_sort, hx]) fun i _ h2 => by simp [List.getElem?_eq_getElem h2]

open Tasks.Sorter in
def model (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    task.PhaseModel (N, W) (lat N W) (design.sem N W) where
  Shape := Shp N W
  Step := Stp N W
  init := so_init N W hN hW hR32
  cycle := by
    rintro σ F e prev k st k' ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, hw⟩ hc
    obtain ⟨k2, h2⟩ := soG.cycle N W hN hW hR32.1 hR32.2.1 hR32.2.2 σ e ck r s iv id ov od dt tk g k 32 (Nat.le_refl _)
    exact ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, hw, (Prod.mk.inj (cycleStep2_det hc h2)).1⟩
  shape := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, -, hw, rfl⟩
    exact next_shp N W _ _ _ _ _ ov od dt tk g hw
  Ready st := ∃ ck r s iv id od dt tk g,
    st = soG.St ck r s iv id (knownBit false) od dt tk g ∧
    TksOk N (fun _ => false) tk ∧ dt.width = N * W
  At ys j st := ∃ ck r s iv id od dt tk g,
    st = soG.St ck r s iv id (knownBit (ovb N j)) od dt tk g ∧
    TksOk N (tokBit N j) tk ∧ CellsOk N W ys j dt ∧ od = dt.extract 0 W
  out ys j := (ovb N j, (sortAsc ys).getD (j - N) 0)
  out_feed _ j hj := by have : j < N := hj; simp [ovb]; omega
  out_lat _ j _ hj := by have : 2 * N - 1 < j := hj; simp [ovb]; omega
  out_spec xs hx := by
    rw [show lat N W + 1 = N + N by simp [lat]; omega, task.emitted_add, task.emitted_nil ?_,
      List.nil_append]
    · exact out_spec_eq xs hx
    · intro k hk; simp [ovb]; omega
  ready_out := by
    rintro st ⟨ck, r, s, iv, id, od, dt, tk, g, rfl, -, -⟩
    simp [BitIs, task, soG.St, SvState.lookup]
  at_out := by
    rintro ys j st ⟨ck, r, s, iv, id, od, dt, tk, g, rfl, -, hdt, rfl⟩
    refine ⟨by simp [BitIs, task, soG.St, SvState.lookup], fun h => ?_⟩
    have htk0 : tokBit N j 0 = true := by rw [tokBit_zero]; exact h
    have hd0 := hdt.2 0 hN htk0
    simp only [Nat.zero_mul, Nat.zero_add] at hd0
    simp [StreamTask.DataIs, task, soG.St, SvState.lookup, hd0]
  reset := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, -, ⟨hov, -, hdt, htk, -⟩, rfl⟩ hr
    rw [show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r]
    obtain ⟨ov', od', dt', tk', g', hst, hov', htk', hdt'⟩ :=
      next_reset_state N W hN hW hR32 _ _ _ _ ov od dt tk g hov hdt htk
    subst hov'
    exact ⟨_, _, _, _, _, od', dt', tk', g', hst, htk', hdt'⟩
  hold := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, ⟨hov, hod, hdt, -, hg⟩, rfl⟩
      ⟨_, _, _, _, _, _, _, _, _, hb, htk, -⟩ hr - hiv
    obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨ov', od', dt', tk', g', hst, htk', hdt', -, hov', -⟩ :=
      next_run_drain N W hN hW hR32 _ _ _ ov od dt tk g (fun _ => false) hov hod hdt htk hg
    have hf : (fun k => if k + 1 < N then false else false) = fun _ => false := by
      funext k; split <;> rfl
    rw [hf] at htk'
    have hovf : ov' = knownBit false := by rw [hov']; split <;> rfl
    rw [hovf] at hst
    exact ⟨_, _, _, _, _, od', dt', tk', g', hst, htk', hdt'⟩
  start := by
    rintro e prev st - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, ⟨hov, hod, hdt, -, hg⟩, rfl⟩
      hp hr - hiv
    have ⟨f, htk, hf1⟩ : ∃ f : Nat → Bool, TksOk N f tk ∧ ∀ k, 1 ≤ k → f k = false := by
      rcases hp with ⟨_, _, _, _, _, _, _, _, _, hb, htk, -⟩ | ⟨xs, j, hl, ⟨_, _, _, _, _, _, _, _, _, hb, htk, -, -⟩, hk⟩
      · obtain ⟨-, -, rfl, rfl⟩ := St_inj hb; exact ⟨fun _ => false, htk, fun _ _ => rfl⟩
      · obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
        have hj : 2 * N - 1 ≤ j := Nat.le_of_not_lt fun hc => by
          have := hk (2 * N - 1) (by omega)
          simp only [ovb, decide_eq_false_iff_not] at this
          omega
        refine ⟨tokBit N j, htk, fun k hk1 => ?_⟩
        simp only [tokBit, decide_eq_false (by omega : ¬ (N ≤ j + k ∧ j + k < 2 * N))]
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨ov', od', dt', tk', g', hst, htk', hdt', -, hov', hod'⟩ :=
      next_run_drain N W hN hW hR32 _ _ _ ov od dt tk g f hov hod hdt htk hg
    have hovf : ov' = knownBit (ovb N 0) := by
      rw [hov']; simp only [ovb, show ¬ (N ≤ 0 ∧ 0 < 2 * N) by omega, decide_false]
      split
      · rw [hf1 1 (Nat.le_refl 1)]
      · rfl
    have htk0 : TksOk N (tokBit N 0) tk' := by
      refine ⟨htk'.1, fun k hk => ?_⟩
      rw [htk'.2 k hk]; simp only [tokBit, show ¬ (N ≤ 0 + k ∧ 0 + k < 2 * N) by omega, decide_false]
      split
      · rw [hf1 (k + 1) (by omega)]
      · rfl
    have hdt0 : CellsOk N W ([] : List (BitVec W)) 0 dt' :=
      ⟨hdt', fun k hk hvk => by simp only [tokBit, decide_eq_true_eq] at hvk; omega⟩
    rw [hovf] at hst
    exact ⟨_, _, _, _, _, od', dt', tk', g', hst, htk0, hdt0, hod'⟩
  feed := by
    rintro e prev st ys j x - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, ⟨hov, hod, -, -, hg⟩, rfl⟩
      ⟨_, _, _, _, _, _, _, _, _, hb, htk, hdt, -⟩ hl hj hr - hiv hx
    obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
    have hid : appIn e "in_data" id = .ofBitVec x := by
      simp only [appIn, show SvState.lookup e "in_data" = _ from hx, Option.getD_some]
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit true from BitIs.appIn_eq hiv iv, hid]
    obtain ⟨ov', od', dt', tk', g', hst, htk', hdt', hov', hod'⟩ :=
      next_run_feed N W hN hW hR32 _ _ ov od dt tk g ys j x hl hj hov hod hg hdt htk
    rw [hov'] at hst
    exact ⟨_, _, _, _, _, od', dt', tk', g', hst, htk', hdt', hod'⟩
  run := by
    rintro e prev st xs j - ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, ⟨hov, hod, hdt, -, hg⟩, rfl⟩
      ⟨_, _, _, _, _, _, _, _, _, hb, htk, hdtok, -⟩ hl hj hr - hiv
    have hj' : N ≤ j := hj
    obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
    rw [show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
      show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
    obtain ⟨ov', od', dt', tk', g', hst, htk', hdt'w, hdt'c, hov', hod'⟩ :=
      next_run_drain N W hN hW hR32 _ _ _ ov od dt tk g (tokBit N j) hov hod hdt htk hg
    have htk'' : TksOk N (tokBit N (j + 1)) tk' := by
      refine ⟨htk'.1, fun k hk => ?_⟩
      rw [htk'.2 k hk]
      dsimp only
      rw [tokBit_step false (by simp; omega) hk]
    have hdt'' : CellsOk N W xs (j + 1) dt' := by
      refine ⟨hdt'w, fun k hk hvk => ?_⟩
      have hlt : k + 1 < N := by simp only [tokBit, decide_eq_true_eq] at hvk; omega
      have hvk1 : tokBit N j (k + 1) = true := by simp only [tokBit, decide_eq_true_eq] at hvk ⊢; omega
      rw [hdt'c k _ hlt (hdtok.2 (k + 1) hlt hvk1)]
      congr 2; omega
    have hov'' : ov' = knownBit (ovb N (j + 1)) := by
      rw [hov', ← tokBit_zero, ← tokBit_step (N := N) (j := j) (k := 0) false (by simp; omega) hN]
    rw [hov''] at hst
    exact ⟨_, _, _, _, _, od', dt', tk', g', hst, htk'', hdt'', hod'⟩

/-! ## 6. Interface, discipline, Moore, termination, XSafe, and main theorem -/

theorem so_interface (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Tasks.Sorter.task.Interface (N, W) (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2.1 hR32.2.2]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "in_valid", "in_data", "out_valid", "out_data",
      "data", "tok", "g"] : List String).Nodup
    decide⟩

theorem so_disciplined (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Tasks.Sorter.task.Disciplined (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2.1 hR32.2.2]
  refine ⟨by simp [Tasks.Sorter.task, soG.D, soG.decls, Design2.inputNames], fun p hp => ?_⟩
  simp only [soG.D, List.toList_toArray, soG.procs, List.mem_cons, List.mem_append,
    List.mem_map] at hp
  rcases hp with rfl | rfl | rfl | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;>
    simp [Tasks.Sorter.task, soG.p0, soG.p1, soG.p2, soG.gen_cmp, soG.gen_cell, edgeClock,
      asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames,
      exprListNames, Process2.isEdgePhase]

theorem so_moore (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    MooreOutDep (design.sem N W) [] := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2.1 hR32.2.2]
  refine ⟨fun n => n = "clk" ∨ n = "rst" ∨ n = "start" ∨ n = "in_valid" ∨ n = "in_data" ∨ n = "g",
    ?_, ?_, ?_⟩
  · intro n hn _
    simp [soG.D, soG.decls, Design2.inputNames] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro e he ⟨r, hr, hSr⟩
    obtain ⟨p, hp, he⟩ := List.mem_flatMap.mp he
    simp only [soG.D, List.toList_toArray, soG.procs, List.mem_cons, List.mem_append,
      List.mem_map] at hp
    rcases hp with rfl | rfl | rfl | ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩
    · simp [soG.p0, processDeps, lhsTargets, lhsNames, exprNames] at he
      rcases he with ⟨rfl, rfl⟩
      simp at hr
      rcases hr with rfl | rfl <;> simp at hSr
    · simp [soG.p1, processDeps, lhsTargets, lhsNames, exprNames] at he
      rcases he with ⟨rfl, rfl⟩
      simp at hr
      rcases hr with rfl | rfl <;> simp at hSr
    · simp [soG.p2, processDeps] at he
    · simp [soG.gen_cmp, processDeps, lhsTargets] at he
      rcases he with ⟨rfl, _⟩; simp
    · simp [soG.gen_cell, processDeps] at he
  · intro o ho
    simp [soG.D, soG.decls, Design2.outputNames] at ho
    rcases ho with rfl | rfl <;> decide

theorem so_terminatesPU (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    TerminatesPU (design.sem N W) := by
  refine TerminatesPU.of_invariant (Shp N W) (so_powerUp N W hN hW hR32) (fun σ => ⟨32, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, s, iv, id, ov, od, dt, tk, g, rfl, hw⟩
    obtain ⟨k', hc⟩ := soG.cycle N W hN hW hR32.1 hR32.2.1 hR32.2.2 σ e ck r s iv id ov od dt tk g kk 32 (Nat.le_refl _)
    exact ⟨_, k', hc, next_shp N W _ _ _ _ _ ov od dt tk g hw⟩
  · rw [soG.sem_eq N W hN hW hR32.1 hR32.2.1 hR32.2.2]
    simp only [soG.D, List.toList_toArray, soG.procs, List.any_cons, List.any_append, List.any_map,
      Bool.or_eq_false_iff, List.any_eq_false, List.mem_range, Function.comp_apply]
    refine ⟨?_, ?_, ?_, fun _ _ => ?_, fun _ _ => ?_⟩ <;>
      simp [soG.p0, soG.p1, soG.p2, soG.gen_cmp, soG.gen_cell, Process2.hasQualifiedCase,
        Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

theorem so_xsafe (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    XSafe (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2.1 hR32.2.2]
  have hOut : W ≤ N * W := Nat.le_mul_of_pos_left W hN
  refine List.all_eq_true.mpr fun p hp => ?_
  simp only [soG.D, List.toList_toArray, soG.procs, List.mem_cons, List.mem_append,
    List.mem_map, List.mem_range] at hp
  rcases hp with rfl | rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · simp [soG.D, soG.decls, soG.p0, xsProc, xsLhs, xsWidth, sigWidth, hN]
  · simp [soG.D, soG.decls, soG.p1, xsProc, xsLhs, xsWidth, sigWidth, hOut]
  · simp [soG.D, soG.decls, soG.p2, xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, sigWidth,
      LVec.allKnown_l0, LVec.width, show N - 1 + 1 ≤ N by omega]
  · have hkW : k * W + W ≤ N * W := mul_add_le_mul hk
    simp [soG.D, soG.decls, soG.gen_cmp, xsProc, xsLhs, xsWidth, binW, sigWidth, hkW,
      show k + 1 ≤ N by omega]
  · have h1 : (k + 1) * W + W ≤ N * W := mul_add_le_mul (by omega)
    have h2 : k * W + W ≤ N * W := mul_add_le_mul (by omega)
    simp [soG.D, soG.decls, soG.gen_cell, xsProc, xsStmt, xsStmts, xsLhs, xsWidth,
      xsWidthList, binW, sigWidth, LVec.allKnown_l0, LVec.width, h1, h2, Nat.one_mul,
      show k + 1 ≤ N by omega, show k + 1 + 1 ≤ N by omega]

theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W⟩ := p
  obtain ⟨hN, hW, hNW32⟩ := hp
  have hR32 : Rng32 N W := rng32_of hN hW hNW32
  exact Tasks.Sorter.task.satisfiedAtV2_of_phases (so_interface N W hN hW hR32)
    (so_disciplined N W hN hW hR32) (so_terminatesPU N W hN hW hR32)
    hN (show N ≤ lat N W by simp [lat]; omega)
    (fun xs h => (len_sort xs).trans h) (model N W hN hW hR32)
    (so_powerUp N W hN hW hR32) (so_moore N W hN hW hR32) (so_xsafe N W hN hW hR32)

end Submission
