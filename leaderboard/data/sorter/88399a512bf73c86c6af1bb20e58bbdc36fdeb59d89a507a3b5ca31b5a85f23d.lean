-- svgolf-latency: 15
import Submission.Design
import SvGolf.Cycle
import LeanModels.Sv.SeqFamily
import LeanModels.Sv.Known2
import LeanModels.Sv.Mono2
import SvGolf.SeqV2

/-!
# Proof for task `sorter`: latency `2N - 1` insertion-cell sorter with direct Moore outputs

`solutions/sorter/solution.sv` stores `N` cells in `data[k*W +: W]` with valid tokens `tok[k]`,
and drives `out_valid = tok[0]` and `out_data = data[0 +: W]` directly from cell `0` (Moore outputs,
zero extra output register stage). Reset clears only `tok` via `(~rst) & ...`; empty cells
(`!tok[k]`) bypass their comparator term so uninitialized `data` bits never affect decisions or outputs.
-/

namespace Submission

open LeanModels.Sv SvGolf SvGolf.Cycle

/-- Latency: `2N - 1` cycles (`15` at the scoring point `(8, 8)`). -/
def lat (N _W : Nat) : Nat := 2 * N - 1

/-- Exact 32-bit `int` parameter range (`N, W < 2^31`). -/
abbrev Rng32 (N W : Nat) : Prop := N < 2147483648 ∧ W < 2147483648

theorem rng32_of {N W : Nat} (hN : 1 ≤ N) (hW : 1 ≤ W) (hNW : N * W < 2 ^ 31) : Rng32 N W := by
  have h1 := Nat.le_mul_of_pos_right N hW
  have h2 := Nat.le_mul_of_pos_left W hN
  exact ⟨by omega, by omega⟩

/-! ## 1. Mirror and cycle (`sv_mirror`, `sv_cycle`) -/

sv_mirror soG := design (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hN32 : N < 2147483648) (hW32 : W < 2147483648)

theorem cell_disj {N W k k' : Nat} (h : k < k') :
    WinDisj (soG.gen_cell N W k) (soG.gen_cell N W k') := by
  have := Nat.mul_le_mul_right W (show k + 1 ≤ k' by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  apply WinDisj.of_all
  simp [soG.gen_cell, allWins, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
  omega

theorem top_disj {N W k : Nat} (h : k + 1 < N) :
    WinDisj (soG.p2 N W) (soG.gen_cell N W k) := by
  have := Nat.mul_le_mul_right W (show k + 1 ≤ N - 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  apply WinDisj.of_all
  simp [soG.p2, soG.gen_cell, allWins, Process2.drvWins, Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt,
    Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps]
  omega

theorem soG_disj (N W : Nat) : (soG.procs N W).Pairwise WinDisj := by
  refine .cons (fun p hp => ?_) (.cons (fun p hp => ?_) (.cons (fun p hp => ?_) ?_))
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | rfl | ⟨k, -, rfl⟩ <;>
      exact WinDisj.of_all (by simp [soG.p0, soG.p1, soG.p2, soG.gen_cell, allWins, Process2.drvWins,
        Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · simp only [List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨k, -, rfl⟩ <;>
      exact WinDisj.of_all (by simp [soG.p1, soG.p2, soG.gen_cell, allWins, Process2.drvWins,
        Process2.procWins, Stmt2.drvWins, Stmt2.drvWinsOpt, Stmt2.drvWinsList, Lhs2.drvWins, DrvWin.overlaps])
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact top_disj (by have := List.mem_range.mp hk; omega)
  · exact List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem fun _ _ h => cell_disj h)

sv_cycle soG using soG_disj N W

/-! ## 2. Simplifying one cycle's commit and comb settle -/

theorem resizeU_eq_self {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  apply LVec.ext_getElem?
  intro i
  by_cases hi : i < w
  · have hi' : i < v.bits.size := by simp [LVec.width] at h; omega
    simp [LVec.resizeU, hi, hi']
  · have hi' : ¬ (i < v.bits.size) := by simp [LVec.width] at h; omega
    simp [LVec.resizeU, hi, Array.getElem?_eq_none (Nat.le_of_not_lt hi')]

theorem resizeU_extract_self (v : LVec) (lo W : Nat) : (v.extract lo W).resizeU W = v.extract lo W :=
  resizeU_eq_self (by simp)

/-- The state shape: every output and register holds its declared width. -/
def I (N W : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk, st = soG.St ck r s iv id ov od dt tk ∧
    ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N

/-- Stronger state shape on known stimuli: `in_valid` also has its declared width `1`. -/
def IK (N W : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk, st = soG.St ck r s iv id ov od dt tk ∧
    iv.width = 1 ∧ ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N

theorem appIn_iv_width {N W : Nat} {e : SvState} {iv : LVec}
    (hke : KnownEntry (soG.D N W) e) (hiv : iv.width = 1) :
    (appIn e "in_valid" iv).width = 1 := by
  have hmem : "in_valid" ∈ (soG.D N W).inputNames.toList := by
    simp [soG.D, soG.decls, Design2.inputNames]
  have h := hke "in_valid" hmem
  unfold appIn
  cases hl : SvState.lookup e "in_valid" with
  | none => exact hiv
  | some v =>
      rw [hl] at h
      have hsw : sigWidth (soG.D N W) "in_valid" = some 1 := by
        simp [sigWidth, soG.D, soG.decls]
      simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq, hsw, Option.some.injEq] at h
      exact h.2.symm

theorem p2Q_skip {n : String} (h1 : n ≠ "data") (h2 : n ≠ "tok")
    (N W : Nat) (ck r s iv id ov od dt tk x : LVec) :
    nbaFold n (soG.p2Q N W ck r s iv id ov od dt tk) x = x := by
  unfold soG.p2Q
  generalize (LVec.ofLogic _).condTrue = c
  cases c <;> simp [nbaFold, Ne.symm h1, Ne.symm h2]

theorem cellQ_skip {n : String} (h1 : n ≠ "data") (h2 : n ≠ "tok")
    (N W k : Nat) (ck r s iv id ov od dt tk x : LVec) :
    nbaFold n (soG.gen_cellQ N W k ck r s iv id ov od dt tk) x = x := by
  unfold soG.gen_cellQ
  generalize (LVec.ofLogic _).condTrue = c1
  cases c1
  · generalize (LVec.ofLogic _).condTrue = c2
    cases c2 <;> simp [nbaFold, Ne.symm h1, Ne.symm h2]
  · simp [nbaFold, Ne.symm h1, Ne.symm h2]

theorem edgeQ_skip {n : String} (h1 : n ≠ "data") (h2 : n ≠ "tok")
    (N W : Nat) (ck r s iv id ov od dt tk x : LVec) :
    nbaFold n (soG.edgeQ N W ck r s iv id ov od dt tk) x = x := by
  simp only [soG.edgeQ, soG.p0Q, soG.p1Q, List.nil_append, nbaFold_append]
  rw [p2Q_skip h1 h2]
  exact nbaFold_flatMap_eq_self (fun k y => cellQ_skip h1 h2 N W k ck r s iv id ov od dt tk y) _ _

theorem edgeQ_indep (N W : Nat) (ck r s iv id ov1 ov2 od1 od2 dt tk : LVec) :
    soG.edgeQ N W ck r s iv id ov1 od1 dt tk = soG.edgeQ N W ck r s iv id ov2 od2 dt tk := by
  simp only [soG.edgeQ, soG.p0Q, soG.p1Q, soG.p2Q, soG.gen_cellQ]

theorem comb_out_valid_eq (N W : Nat) (ck r s iv id ov od dt tk : LVec) (hov : ov.width = 1) :
    soG.comb_out_valid N W ck r s iv id ov od dt tk = tk.extract 0 1 := by
  simp [soG.comb_out_valid, soG.combQ, soG.p0C, soG.p1C, nbaFold, hov,
    LVec.insertAt_zero_of_width_eq, resizeU_extract_self]

theorem comb_out_data_eq (N W : Nat) (ck r s iv id ov od dt tk : LVec) (hod : od.width = W) :
    soG.comb_out_data N W ck r s iv id ov od dt tk = dt.extract 0 W := by
  simp [soG.comb_out_data, soG.combQ, soG.p0C, soG.p1C, nbaFold, hod,
    LVec.insertAt_zero_of_width_eq, resizeU_extract_self]

/-- Next `data` register value. -/
def nextData (N W : Nat) (ck r s iv id dt tk : LVec) : LVec :=
  nbaFold "data" (soG.edgeQ N W ck r s iv id (knownBit false) (LVec.xVec W) dt tk) dt

/-- Next `tok` register value. -/
def nextTok (N W : Nat) (ck r s iv id dt tk : LVec) : LVec :=
  nbaFold "tok" (soG.edgeQ N W ck r s iv id (knownBit false) (LVec.xVec W) dt tk) tk

theorem width_nextData (N W : Nat) (ck r s iv id dt tk : LVec) :
    (nextData N W ck r s iv id dt tk).width = dt.width := by
  simp [nextData, width_nbaFold]

theorem width_nextTok (N W : Nat) (ck r s iv id dt tk : LVec) :
    (nextTok N W ck r s iv id dt tk).width = tk.width := by
  simp [nextTok, width_nbaFold]

theorem soG_next_eq (N W : Nat) (ck r s iv id ov od dt tk : LVec)
    (hov : ov.width = 1) (hod : od.width = W) :
    soG.next N W ck r s iv id ov od dt tk =
      soG.St ck r s iv id
        ((nextTok N W ck r s iv id dt tk).extract 0 1)
        ((nextData N W ck r s iv id dt tk).extract 0 W)
        (nextData N W ck r s iv id dt tk)
        (nextTok N W ck r s iv id dt tk) := by
  unfold soG.next soG.comb
  rw [edgeQ_skip (by decide) (by decide), edgeQ_skip (by decide) (by decide),
    edgeQ_skip (by decide) (by decide), edgeQ_skip (by decide) (by decide),
    edgeQ_skip (by decide) (by decide), edgeQ_skip (by decide) (by decide),
    edgeQ_skip (by decide) (by decide)]
  rw [edgeQ_indep N W ck r s iv id _ (knownBit false) _ (LVec.xVec W) dt tk]
  have hov' : (soG.comb_out_valid N W ck r s iv id ov od dt tk).width = 1 := by
    rw [comb_out_valid_eq N W ck r s iv id ov od dt tk hov]; simp
  have hod' : (soG.comb_out_data N W ck r s iv id ov od dt tk).width = W := by
    rw [comb_out_data_eq N W ck r s iv id ov od dt tk hod]; simp
  rw [comb_out_valid_eq N W _ _ _ _ _ _ _ _ _ hov', comb_out_data_eq N W _ _ _ _ _ _ _ _ _ hod']
  rfl

theorem next_I {N W : Nat} (ck r s iv id ov od dt tk : LVec)
    (hw : ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N) :
    I N W (soG.next N W ck r s iv id ov od dt tk) := by
  rw [soG_next_eq N W ck r s iv id ov od dt tk hw.1 hw.2.1]
  exact ⟨ck, r, s, iv, id, _, _, _, _, rfl, by simp, by simp,
    by rw [width_nextData]; exact hw.2.2.1, by rw [width_nextTok]; exact hw.2.2.2⟩

theorem next_IK {N W : Nat} (ck r s iv id ov od dt tk : LVec)
    (hiv : iv.width = 1) (hw : ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N) :
    IK N W (soG.next N W ck r s iv id ov od dt tk) := by
  rw [soG_next_eq N W ck r s iv id ov od dt tk hw.1 hw.2.1]
  exact ⟨ck, r, s, iv, id, _, _, _, _, rfl, hiv, by simp, by simp,
    by rw [width_nextData]; exact hw.2.2.1, by rw [width_nextTok]; exact hw.2.2.2⟩

theorem so_powerUp (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) (st : SvState)
    (h : PowerUp (design.sem N W) st) : I N W st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, -, -, -, -, hov, hod, hdt, htk⟩ :=
    soG.powerUp N W hN hW hR32.1 hR32.2 st h
  exact ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hov, hod, hdt, htk⟩

theorem so_powerUpK (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) (st : SvState)
    (h : PowerUp (design.sem N W) st) : IK N W st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, -, -, hiv, -, hov, hod, hdt, htk⟩ :=
    soG.powerUp N W hN hW hR32.1 hR32.2 st h
  exact ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hiv, hov, hod, hdt, htk⟩

theorem so_terminatesPU (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    TerminatesPU (design.sem N W) := by
  refine TerminatesPU.of_invariant (I N W) (so_powerUp N W hN hW hR32) (fun σ => ⟨32, ?_⟩) ?_
  · rintro e _ kk ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hw⟩
    obtain ⟨k', hc⟩ := soG.cycle N W hN hW hR32.1 hR32.2 σ e ck r s iv id ov od dt tk kk 32 (Nat.le_refl _)
    exact ⟨_, k', hc, next_I _ _ _ _ _ _ _ _ _ hw⟩
  · rw [soG.sem_eq N W hN hW hR32.1 hR32.2]
    simp [soG.D, soG.procs, soG.p0, soG.p1, soG.p2, soG.gen_cell,
      Process2.hasQualifiedCase, Stmt2.hasQualifiedCase, Stmt2.listHasQualifiedCase]

/-! ## 3. Token updates (reset and shift) -/

/-- The tokens all `0`. -/
abbrev Z (W N : Nat) : LVec := .ofBitVec (packBV W N fun _ => 0)

/-- The tokens after a cycle without reset: shift down, `in_valid` in at the top. -/
def tstep (N : Nat) (b : Bool) (T : Nat → BitVec 1) (k : Nat) : BitVec 1 :=
  if k + 1 < N then T (k + 1) else BitVec.ofBool b

/-- `(0#1 & v)` resized to 1 bit is always `0#1` for any 1-bit `v` (even `x`). -/
theorem zero1_and_resize1 {v : LVec} (hv : v.width = 1) : ((LVec.ofBitVec 0#1).and v).resizeU 1 = .ofBitVec 0#1 := by
  apply LVec.ext_getElem?
  intro i
  cases i with
  | zero =>
      have hvs : v.bits.size = 1 := hv
      have h0s : (LVec.ofBitVec 0#1).bits.size = 1 := LVec.width_ofBitVec 0#1
      have h0 : (LVec.ofBitVec 0#1).bits[0]' (by omega) = .l0 := by
        rw [LVec.getElem_ofBitVec]; rfl
      simp [LVec.resizeU, LVec.and, LVec.zipWith, hv, hvs, h0s, h0, Logic.and]
  | succ i =>
      simp [LVec.resizeU, LVec.getElem?_ofBitVec]

theorem bv1_one_and (x : BitVec 1) : 1#1 &&& x = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  simp

theorem top_tok_reset (N W : Nat) (ck s iv id ov od dt tk x : LVec) (hiv : iv.width = 1) :
    nbaFold "tok" (soG.p2Q N W ck (knownBit true) s iv id ov od dt tk) x =
      x.insertAt ((N - 1) * 1) (.ofBitVec 0#1) := by
  unfold soG.p2Q
  generalize (LVec.ofLogic _).condTrue = c
  cases c <;> simp [nbaFold, knownBit, zero1_and_resize1 hiv]

theorem cell_tok_reset (N W k : Nat) (ck s iv id ov od dt tk x : LVec) :
    nbaFold "tok" (soG.gen_cellQ N W k ck (knownBit true) s iv id ov od dt tk) x =
      x.insertAt (k * 1) (.ofBitVec 0#1) := by
  have hew : (tk.extract (k + 1) 1).width = 1 := by simp
  unfold soG.gen_cellQ
  generalize (LVec.ofLogic _).condTrue = c1
  cases c1
  · generalize (LVec.ofLogic _).condTrue = c2
    cases c2 <;> simp [nbaFold, knownBit, zero1_and_resize1 hew]
  · simp [nbaFold, knownBit, zero1_and_resize1 hew]

/-- **Reset clears `tok` to all zeros** (for any 1-bit `in_valid`). -/
theorem nextTok_reset {N W : Nat} (hN : 1 ≤ N) (ck s iv id dt tk : LVec)
    (hiv : iv.width = 1) (htk : tk.width = N) :
    nextTok N W ck (knownBit true) s iv id dt tk = Z 1 N := by
  simp only [nextTok, soG.edgeQ, soG.p0Q, soG.p1Q, List.nil_append, nbaFold_append, nbaFold_flatMap,
    top_tok_reset _ _ _ _ _ _ _ _ _ _ _ hiv, cell_tok_reset]
  rw [LVec.foldl_range_insertAt_last hN _ tk (by simp),
    LVec.insertEntries_ofBitVec (fun _ => 0#1) tk (by simp [htk])]
  rfl

theorem top_tok_run {N W : Nat} (hN : 1 ≤ N) (b : Bool) (ck s id ov od dt tk : LVec) (u : Nat → BitVec 1) :
    nbaFold "tok" (soG.p2Q N W ck (knownBit false) s (knownBit b) id ov od dt tk) (.ofBitVec (packBV 1 N u)) =
      .ofBitVec (packBV 1 N (fun i => if i = N - 1 then BitVec.ofBool b else u i)) := by
  have hup := bvInsertAt_packBV u (BitVec.ofBool b) (show N - 1 < N by omega) (Nat.mul_one _).symm
  unfold soG.p2Q
  generalize (LVec.ofLogic _).condTrue = c
  cases c <;> simp [nbaFold, knownBit, bv1_one_and, hup]

theorem cell_tok_run {N W k : Nat} (hk : k + 1 < N) (ck s iv id ov od dt : LVec) (T u : Nat → BitVec 1) :
    nbaFold "tok" (soG.gen_cellQ N W k ck (knownBit false) s iv id ov od dt (.ofBitVec (packBV 1 N T)))
        (.ofBitVec (packBV 1 N u)) =
      .ofBitVec (packBV 1 N (fun i => if i = k then T (k + 1) else u i)) := by
  have e := extract_ofBitVec_packBV T hk (Nat.mul_one _).symm
  have hup := bvInsertAt_packBV u (T (k + 1)) (show k < N by omega) (Nat.mul_one k).symm
  unfold soG.gen_cellQ
  generalize (LVec.ofLogic _).condTrue = c1
  cases c1
  · generalize (LVec.ofLogic _).condTrue = c2
    cases c2 <;> simp [nbaFold, knownBit, e, bv1_one_and, hup]
  · simp [nbaFold, knownBit, e, bv1_one_and, hup]

/-- **Non-reset shifts `tok` down with `in_valid` entering at `N - 1`.** -/
theorem nextTok_run {N W : Nat} (hN : 1 ≤ N) (b : Bool) (T : Nat → BitVec 1) (ck s id dt : LVec) :
    nextTok N W ck (knownBit false) s (knownBit b) id dt (.ofBitVec (packBV 1 N T)) =
      .ofBitVec (packBV 1 N (tstep N b T)) := by
  simp only [nextTok, soG.edgeQ, soG.p0Q, soG.p1Q, List.nil_append, nbaFold_append, nbaFold_flatMap]
  rw [top_tok_run hN b,
    foldl_range_ofBitVec_packBV (W := 1) (N := N) _ (fun k => T (k + 1)) _ (N - 1) ?_]
  · refine congrArg _ (packBV_congr fun i hi => ?_)
    by_cases h : i < N - 1
    · simp [h, tstep, show i + 1 < N by omega]
    · obtain rfl : i = N - 1 := by omega
      simp [tstep, show ¬ (N - 1 + 1 < N) by omega]
  · intro k u' hk _
    exact cell_tok_run (by omega) _ _ _ _ _ _ _ T u'

/-! ## 4. Per-cell extraction from `nextData` -/

/-- A single `insertAt` on a disjoint slot leaves slot `i * W` unchanged. -/
theorem extract_insertAt_slot_ne {W i j : Nat} (hne : i ≠ j) (dt v : LVec) (hv : v.width = W) :
    (dt.insertAt (j * W) v).extract (i * W) W = dt.extract (i * W) W := by
  apply LVec.ext_getElem?
  intro b
  by_cases hb : b < W
  · have hdisj : ¬ (j * W ≤ i * W + b ∧ i * W + b < j * W + v.width) := by
      rw [hv]
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := Nat.mul_le_mul_right W (show i + 1 ≤ j by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      · have := Nat.mul_le_mul_right W (show j + 1 ≤ i by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
    by_cases hsz : i * W + b < dt.width
    · have hsz' : i * W + b < dt.bits.size := hsz
      simp [LVec.extract, LVec.insertAt, hb, hsz, hsz', hdisj, Array.getElem?_ofFn]
    · have hsz' : ¬ (i * W + b < dt.bits.size) := hsz
      simp [LVec.extract, LVec.insertAt, hb, hsz, hsz', Array.getElem?_ofFn]
  · simp [LVec.extract, hb]

/-- A single `insertAt` on slot `i * W` writes `v` into slot `i * W` (when `i * W + W ≤ dt.width`). -/
theorem extract_insertAt_slot_eq {W i : Nat} (dt v : LVec) (hv : v.width = W) (hdt : i * W + W ≤ dt.width) :
    (dt.insertAt (i * W) v).extract (i * W) W = v := by
  apply LVec.ext_getElem?
  intro b
  have hvs : v.bits.size = W := hv
  have hdts : i * W + W ≤ dt.bits.size := hdt
  by_cases hb : b < W
  · have h1 : i * W + b < dt.width := by omega
    have h2 : b < v.width := by rw [hv]; exact hb
    have hbv : b < v.bits.size := by omega
    simp [LVec.extract, LVec.insertAt, hb, h1, h2, hbv, Array.getElem?_ofFn]
  · simp [LVec.extract, hb, Array.getElem?_eq_none (show v.bits.size ≤ b by omega)]

/-- What `cell k` writes to slot `k * W` (or `none` if it holds). -/
def cellWrite (W k : Nat) (iv id dt tk : LVec) : Option LVec :=
  if (LVec.ofLogic
        (if (LVec.ofLogic
              (if (LVec.ofLogic iv.lnot).condTrue || (LVec.ofLogic (tk.extract (k + 1) 1).lnot).condTrue then
                Logic.l1
              else if (LVec.ofLogic iv.lnot).isKnownZero && (LVec.ofLogic (tk.extract (k + 1) 1).lnot).isKnownZero then
                Logic.l0
              else Logic.lx)).condTrue ||
            (LVec.ofLogic (id.ge (dt.extract ((k + 1) * W) W))).condTrue then
          Logic.l1
        else if (LVec.ofLogic
              (if (LVec.ofLogic iv.lnot).condTrue || (LVec.ofLogic (tk.extract (k + 1) 1).lnot).condTrue then
                Logic.l1
              else if (LVec.ofLogic iv.lnot).isKnownZero && (LVec.ofLogic (tk.extract (k + 1) 1).lnot).isKnownZero then
                Logic.l0
              else Logic.lx)).isKnownZero &&
            (LVec.ofLogic (id.ge (dt.extract ((k + 1) * W) W))).isKnownZero then
          Logic.l0
        else Logic.lx)).condTrue then
    some ((dt.extract ((k + 1) * W) W).resizeU W)
  else if (LVec.ofLogic
        (if (LVec.ofLogic (tk.extract k 1).lnot).condTrue || (LVec.ofLogic (id.ge (dt.extract (k * W) W))).condTrue then
          Logic.l1
        else if (LVec.ofLogic (tk.extract k 1).lnot).isKnownZero &&
            (LVec.ofLogic (id.ge (dt.extract (k * W) W))).isKnownZero then
          Logic.l0
        else Logic.lx)).condTrue then
    some (id.resizeU W)
  else none

/-- What `top` writes to slot `(N - 1) * W` (or `none` if it holds). -/
def topWrite (N W : Nat) (iv id dt tk : LVec) : Option LVec :=
  if (LVec.ofLogic
        (if iv.isKnownZero ||
            (LVec.ofLogic
              (if (LVec.ofLogic (tk.extract (N - 1) 1).lnot).condTrue ||
                  (LVec.ofLogic (id.ge (dt.extract ((N - 1) * W) W))).condTrue then
                Logic.l1
              else if (LVec.ofLogic (tk.extract (N - 1) 1).lnot).isKnownZero &&
                  (LVec.ofLogic (id.ge (dt.extract ((N - 1) * W) W))).isKnownZero then
                Logic.l0
              else Logic.lx)).isKnownZero then
          Logic.l0
        else if iv.condTrue &&
            (LVec.ofLogic
              (if (LVec.ofLogic (tk.extract (N - 1) 1).lnot).condTrue ||
                  (LVec.ofLogic (id.ge (dt.extract ((N - 1) * W) W))).condTrue then
                Logic.l1
              else if (LVec.ofLogic (tk.extract (N - 1) 1).lnot).isKnownZero &&
                  (LVec.ofLogic (id.ge (dt.extract ((N - 1) * W) W))).isKnownZero then
                Logic.l0
              else Logic.lx)).condTrue then
          Logic.l1
        else Logic.lx)).condTrue then
    some (id.resizeU W)
  else none

theorem nbaFold_p2Q_data (N W : Nat) (ck r s iv id ov od dt tk acc : LVec) :
    nbaFold "data" (soG.p2Q N W ck r s iv id ov od dt tk) acc =
      match topWrite N W iv id dt tk with
      | some v => acc.insertAt ((N - 1) * W) v
      | none => acc := by
  unfold soG.p2Q topWrite
  simp only [show (SymBinOp.land == SymBinOp.land) = true from rfl,
    show (SymBinOp.lor == SymBinOp.land) = false from rfl, ↓reduceIte, Bool.false_eq_true]
  generalize (LVec.ofLogic _).condTrue = c
  cases c <;> simp [nbaFold]

theorem nbaFold_cellQ_data (N W k : Nat) (ck r s iv id ov od dt tk acc : LVec) :
    nbaFold "data" (soG.gen_cellQ N W k ck r s iv id ov od dt tk) acc =
      match cellWrite W k iv id dt tk with
      | some v => acc.insertAt (k * W) v
      | none => acc := by
  unfold soG.gen_cellQ cellWrite
  simp only [show (SymBinOp.lor == SymBinOp.land) = false from rfl, ↓reduceIte, Bool.false_eq_true]
  generalize (LVec.ofLogic _).condTrue = c1
  cases c1
  · generalize (LVec.ofLogic _).condTrue = c2
    cases c2 <;> simp [nbaFold]
  · simp [nbaFold]

theorem width_topWrite {N W : Nat} {iv id dt tk v : LVec}
    (h : topWrite N W iv id dt tk = some v) : v.width = W := by
  unfold topWrite at h
  generalize (LVec.ofLogic _).condTrue = c at h
  cases c
  · simp at h
  · simp only [↓reduceIte, Option.some.injEq] at h; rw [← h]; simp

theorem width_cellWrite {W k : Nat} {iv id dt tk v : LVec}
    (h : cellWrite W k iv id dt tk = some v) : v.width = W := by
  unfold cellWrite at h
  generalize (LVec.ofLogic _).condTrue = c1 at h
  cases c1
  · generalize (LVec.ofLogic _).condTrue = c2 at h
    cases c2
    · simp at h
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h; rw [← h]; simp
  · simp only [↓reduceIte, Option.some.injEq] at h; rw [← h]; simp

/-- Folding `cellQ` updates over `List.range m` updates each slot `i < m` via `cellWrite` and leaves `i ≥ m` alone. -/
theorem foldl_cellQ_extract {N W : Nat} (ck r s iv id ov od dt tk : LVec) :
    ∀ (m : Nat) (acc : LVec), acc.width = N * W → ∀ (i : Nat), i < N →
      ((List.range m).foldl
        (fun a k => nbaFold "data" (soG.gen_cellQ N W k ck r s iv id ov od dt tk) a) acc).extract (i * W) W =
        if i < m then (cellWrite W i iv id dt tk).getD (acc.extract (i * W) W)
        else acc.extract (i * W) W
  | 0, acc, _, i, _ => by simp
  | m + 1, acc, hacc, i, hi => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, nbaFold_cellQ_data]
      have hwa : ((List.range m).foldl
          (fun a k => nbaFold "data" (soG.gen_cellQ N W k ck r s iv id ov od dt tk) a) acc).width = N * W := by
        clear hi
        induction m generalizing acc with
        | zero => exact hacc
        | succ m ih =>
            rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, width_nbaFold]
            exact ih acc hacc
      have ih := foldl_cellQ_extract ck r s iv id ov od dt tk m acc hacc i hi
      cases hc : cellWrite W m iv id dt tk with
      | none =>
          simp only
          rw [ih]
          by_cases him : i < m
          · simp [him, show i < m + 1 by omega]
          · by_cases heq : i = m
            · subst heq; simp [him, hc]
            · simp [him, show ¬ (i < m + 1) by omega]
      | some v =>
          have hv : v.width = W := width_cellWrite hc
          by_cases heq : i = m
          · subst heq
            have hbound : i * W + W ≤ N * W := rowMajor_le (K := W) hi
            rw [extract_insertAt_slot_eq _ v hv (by rw [hwa]; exact hbound)]
            simp [hc]
          · rw [extract_insertAt_slot_ne heq _ v hv, ih]
            by_cases him : i < m
            · simp [him, show i < m + 1 by omega]
            · simp [him, show ¬ (i < m + 1) by omega]

/-- **Slot `i` of `nextData`**: slot `N - 1` comes from `topWrite`, slot `i < N - 1` from `cellWrite`. -/
theorem extract_nextData {N W : Nat} (ck r s iv id dt tk : LVec) (hdt : dt.width = N * W)
    {i : Nat} (hi : i < N) :
    (nextData N W ck r s iv id dt tk).extract (i * W) W =
      if i + 1 < N then
        (cellWrite W i iv id dt tk).getD (dt.extract (i * W) W)
      else
        (topWrite N W iv id dt tk).getD (dt.extract (i * W) W) := by
  simp only [nextData, soG.edgeQ, soG.p0Q, soG.p1Q, List.nil_append, nbaFold_append, nbaFold_flatMap,
    nbaFold_p2Q_data]
  have htopW : (match topWrite N W iv id dt tk with
      | some v => dt.insertAt ((N - 1) * W) v | none => dt).width = N * W := by
    cases topWrite N W iv id dt tk <;> simp [hdt]
  rw [foldl_cellQ_extract _ _ _ _ _ _ _ _ _ (N - 1) _ htopW i hi]
  by_cases hlt : i < N - 1
  · have hlt' : i + 1 < N := by omega
    have hne : i ≠ N - 1 := by omega
    simp only [hlt, hlt', ↓reduceIte]
    cases ht : topWrite N W iv id dt tk with
    | none => rfl
    | some v => rw [extract_insertAt_slot_ne hne dt v (width_topWrite ht)]
  · have hlt' : ¬ (i + 1 < N) := by omega
    obtain rfl : i = N - 1 := by omega
    simp only [hlt, hlt', ↓reduceIte]
    cases ht : topWrite N W iv id dt tk with
    | none => rfl
    | some v =>
        have hbound : (N - 1) * W + W ≤ N * W := rowMajor_le (K := W) hi
        rw [extract_insertAt_slot_eq dt v (width_topWrite ht) (by rw [hdt]; exact hbound)]
        rfl

/-! ## 5. Evaluating `cellWrite` and `topWrite` on known control / valid data -/

theorem lnot_knownBit_false : (knownBit false).lnot = .l1 := by
  simp [knownBit, LVec.lnot]
theorem lnot_knownBit_true : (knownBit true).lnot = .l0 := by
  simp [knownBit, LVec.lnot]
theorem lnot_bv0 : (LVec.ofBitVec 0#1).lnot = .l1 := lnot_knownBit_false
theorem lnot_bv1 : (LVec.ofBitVec 1#1).lnot = .l0 := lnot_knownBit_true

theorem cellWrite_drain (W k : Nat) (id dt tk : LVec) :
    cellWrite W k (knownBit false) id dt tk = some (dt.extract ((k + 1) * W) W) := by
  simp [cellWrite, lnot_knownBit_false, resizeU_extract_self]

theorem cellWrite_load_empty {W k : Nat} {x d1 : BitVec W} (dt tk : LVec)
    (ht0 : tk.extract k 1 = .ofBitVec 0#1) (ht1 : tk.extract (k + 1) 1 = .ofBitVec 1#1)
    (hd1 : dt.extract ((k + 1) * W) W = .ofBitVec d1) :
    cellWrite W k (knownBit true) (.ofBitVec x) dt tk =
      some (.ofBitVec (if d1.toNat ≤ x.toNat then d1 else x)) := by
  by_cases h : d1.toNat ≤ x.toNat
  · have hle : d1 ≤ x := BitVec.le_def.mpr h
    simp [cellWrite, ht1, hd1, lnot_knownBit_true, lnot_bv1, h, hle]
  · have hle : ¬ d1 ≤ x := fun hc => h (BitVec.le_def.mp hc)
    simp [cellWrite, ht0, ht1, hd1, lnot_knownBit_true, lnot_bv0, lnot_bv1, h, hle]

theorem cellWrite_load_valid {W k : Nat} {x d0 d1 : BitVec W} (dt tk : LVec)
    (ht0 : tk.extract k 1 = .ofBitVec 1#1) (ht1 : tk.extract (k + 1) 1 = .ofBitVec 1#1)
    (hd0 : dt.extract (k * W) W = .ofBitVec d0) (hd1 : dt.extract ((k + 1) * W) W = .ofBitVec d1) :
    (cellWrite W k (knownBit true) (.ofBitVec x) dt tk).getD (dt.extract (k * W) W) =
      .ofBitVec (if d1.toNat ≤ x.toNat then d1 else if d0.toNat ≤ x.toNat then x else d0) := by
  by_cases h1 : d1.toNat ≤ x.toNat <;> by_cases h0 : d0.toNat ≤ x.toNat
  · have h1' : d1 ≤ x := BitVec.le_def.mpr h1
    simp [cellWrite, ht1, hd0, hd1, lnot_knownBit_true, lnot_bv1, h1, h1']
  · have h1' : d1 ≤ x := BitVec.le_def.mpr h1
    simp [cellWrite, ht1, hd0, hd1, lnot_knownBit_true, lnot_bv1, h1, h1']
  · have h1' : ¬ d1 ≤ x := fun hc => h1 (BitVec.le_def.mp hc)
    have h0' : d0 ≤ x := BitVec.le_def.mpr h0
    simp [cellWrite, ht0, ht1, hd0, hd1, lnot_knownBit_true, lnot_bv1, h1, h1', h0, h0']
  · have h1' : ¬ d1 ≤ x := fun hc => h1 (BitVec.le_def.mp hc)
    have h0' : ¬ d0 ≤ x := fun hc => h0 (BitVec.le_def.mp hc)
    simp [cellWrite, ht0, ht1, hd0, hd1, lnot_knownBit_true, lnot_bv1, h1, h1', h0, h0']

theorem topWrite_load_empty {N W : Nat} {x : BitVec W} (dt tk : LVec)
    (ht : tk.extract (N - 1) 1 = .ofBitVec 0#1) :
    topWrite N W (knownBit true) (.ofBitVec x) dt tk = some (.ofBitVec x) := by
  simp [topWrite, ht, lnot_bv0]

theorem topWrite_load_valid {N W : Nat} {x d : BitVec W} (dt tk : LVec)
    (ht : tk.extract (N - 1) 1 = .ofBitVec 1#1) (hd : dt.extract ((N - 1) * W) W = .ofBitVec d) :
    (topWrite N W (knownBit true) (.ofBitVec x) dt tk).getD (dt.extract ((N - 1) * W) W) =
      .ofBitVec (if d.toNat ≤ x.toNat then x else d) := by
  by_cases h : d.toNat ≤ x.toNat
  · have hle : d ≤ x := BitVec.le_def.mpr h
    simp [topWrite, ht, hd, lnot_bv1, h, hle]
  · have hle : ¬ d ≤ x := fun hc => h (BitVec.le_def.mp hc)
    simp [topWrite, ht, hd, lnot_bv1, h, hle]

/-! ## 6. Sorting arithmetic (`insertAsc` and `sortAsc`) -/

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

theorem sort_snoc {W : Nat} (x : BitVec W) : ∀ l : List (BitVec W), sortAsc (l ++ [x]) = insertAsc x (sortAsc l)
  | [] => rfl
  | a :: l => by simp only [List.cons_append, sortAsc, sort_snoc x l]; exact ins_comm ..

/-- Element `idx` of `insertAsc x S` for any sorted list `S` and `idx ≤ S.length`, matching the
hardware `in_data >= data[k]` insertion rule. -/
theorem getD_insertAsc {W : Nat} (x : BitVec W) : ∀ (S : List (BitVec W)), Srt S →
    ∀ idx, idx ≤ S.length →
      (insertAsc x S).getD idx 0 =
        if idx < S.length ∧ (S.getD idx 0).toNat ≤ x.toNat then S.getD idx 0
        else if idx = 0 ∨ (S.getD (idx - 1) 0).toNat ≤ x.toNat then x
        else S.getD (idx - 1) 0
  | [], _, idx, hi => by
      have : idx = 0 := by simp at hi; omega
      subst this; simp [insertAsc]
  | b :: L, hs, idx, hi => by
      have ⟨hb, hL⟩ := List.pairwise_cons.mp hs
      cases idx with
      | zero =>
          by_cases hbx : b.toNat ≤ x.toNat
          · by_cases hxb : x.toNat ≤ b.toNat
            · have heq : x = b := BitVec.eq_of_toNat_eq (by omega)
              subst heq; simp [insertAsc]
            · simp [insertAsc, hbx, hxb]
          · have hxb : x.toNat ≤ b.toNat := by omega
            simp [insertAsc, hbx, hxb]
      | succ i =>
          have hiL : i ≤ L.length := by simp at hi; omega
          by_cases hxb : x.toNat ≤ b.toNat
          · simp only [insertAsc, hxb, ↓reduceIte, List.getD_cons_succ, List.length_cons,
              Nat.add_lt_add_iff_right, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
              and_false, false_or]
            by_cases h1 : i < L.length ∧ (L.getD i 0).toNat ≤ x.toNat
            · simp only [h1.1, h1.2, and_self, ↓reduceIte]
              have hmem : L[i]'h1.1 ∈ L := List.getElem_mem h1.1
              have hbi : b.toNat ≤ (L[i]'h1.1).toNat := hb _ hmem
              have hLi : L.getD i 0 = L[i]'h1.1 := by simp [List.getD_eq_getElem?_getD, h1.1]
              cases i with
              | zero =>
                  rw [hLi] at h1 ⊢
                  simp only [List.getD_cons_zero]
                  exact BitVec.eq_of_toNat_eq (by omega)
              | succ j =>
                  have hj : j < L.length := by omega
                  have hbj : b.toNat ≤ (L[j]'hj).toNat := hb _ (List.getElem_mem hj)
                  have hji : (L[j]'hj).toNat ≤ (L[j + 1]'h1.1).toNat :=
                    (List.pairwise_iff_getElem.mp hL) j (j + 1) hj h1.1 (by omega)
                  have hLj : L.getD j 0 = L[j]'hj := by simp [List.getD_eq_getElem?_getD, hj]
                  simp only [List.getD_cons_succ, hLj, hLi] at h1 ⊢
                  exact BitVec.eq_of_toNat_eq (by omega)
            · simp only [h1, ↓reduceIte]
              by_cases h2 : ((b :: L).getD i 0).toNat ≤ x.toNat
              · simp only [h2, ↓reduceIte]
                cases i with
                | zero =>
                    simp only [List.getD_cons_zero] at h2 ⊢
                    exact BitVec.eq_of_toNat_eq (by omega)
                | succ j =>
                    have hj : j < L.length := by omega
                    have hbj : b.toNat ≤ (L[j]'hj).toNat := hb _ (List.getElem_mem hj)
                    have hLj : L.getD j 0 = L[j]'hj := by simp [List.getD_eq_getElem?_getD, hj]
                    simp only [List.getD_cons_succ, hLj] at h2 ⊢
                    exact BitVec.eq_of_toNat_eq (by omega)
              · simp only [h2, ↓reduceIte]
          · simp only [insertAsc, hxb, ↓reduceIte, List.getD_cons_succ, List.length_cons,
              Nat.add_lt_add_iff_right, Nat.add_sub_cancel, Nat.add_eq_zero_iff, Nat.one_ne_zero,
              and_false, false_or]
            rw [getD_insertAsc x L hL i hiL]
            cases i with
            | zero =>
                have hbx : b.toNat ≤ x.toNat := by omega
                simp [hbx]
            | succ j =>
                simp

/-! ## 7. Transaction invariant (`tokv`, `ovb`, `DataOK`) and step lemmas -/

/-- Token `k`, `j` cycles after a start. -/
def tokv (N j : Nat) (k : Nat) : BitVec 1 :=
  BitVec.ofBool (decide (N ≤ j + k ∧ j + k + 1 ≤ 2 * N))

/-- `out_valid`, `j` cycles after a start: `1` for `N ≤ j < 2N` (`N` valid cycles ending at `2N - 1`). -/
def ovb (N j : Nat) : Bool := decide (N ≤ j ∧ j < 2 * N)

/-- Valid cells hold `sortAsc ys` aligned at offset `j + k - N`; empty cells are unconstrained. -/
def DataOK {W : Nat} (N : Nat) (ys : List (BitVec W)) (j : Nat) (dt : LVec) : Prop :=
  dt.width = N * W ∧
  ∀ k, k < N → N ≤ j + k → j + k < 2 * N →
    dt.extract (k * W) W = .ofBitVec ((sortAsc ys).getD (j + k - N) 0)

theorem tok_step {N j k : Nat} (b : Bool) (hb : b = decide (j + 1 ≤ N)) (hk : k < N) :
    tstep N b (tokv N j) k = tokv N (j + 1) k := by
  simp only [tstep, tokv]; split
  · congr 1; simp only [decide_eq_decide]; omega
  · rw [hb]; congr 1; simp only [decide_eq_decide]; omega

theorem tokv_zero_eq_ovb (N j : Nat) : tokv N j 0 = BitVec.ofBool (ovb N j) := by
  simp only [tokv, ovb]; congr 1

theorem tokv_zero_eq_zero {N k : Nat} (hk : k < N) : tokv N 0 k = 0#1 := by
  simp only [tokv, Nat.zero_add]
  rw [decide_eq_false (by omega)]; rfl

/-- **Load step (`in_valid = 1`) preserves `DataOK`**, inserting `x` into `sortAsc ys`. -/
theorem dataOK_feed {N W j : Nat} (ys : List (BitVec W)) (x : BitVec W)
    (hj : j < N) (hl : ys.length = j) (ck s dt : LVec)
    (hD : DataOK N ys j dt) :
    DataOK N (ys ++ [x]) (j + 1)
      (nextData N W ck (knownBit false) s (knownBit true) (.ofBitVec x) dt (.ofBitVec (packBV 1 N (tokv N j)))) := by
  refine ⟨by rw [width_nextData]; exact hD.1, fun k hk hlo hhi => ?_⟩
  rw [extract_nextData _ _ _ _ _ _ _ hD.1 hk, sort_snoc]
  have hSlen : (sortAsc ys).length = j := (len_sort ys).trans hl
  have hidx : j + 1 + k - N ≤ (sortAsc ys).length := by omega
  rw [getD_insertAsc x (sortAsc ys) (srt_sort ys) (j + 1 + k - N) hidx]
  by_cases htop : k + 1 < N
  · simp only [htop, ↓reduceIte]
    have ht1 : (LVec.ofBitVec (packBV 1 N (tokv N j))).extract (k + 1) 1 = .ofBitVec 1#1 := by
      rw [extract_ofBitVec_packBV (tokv N j) htop (Nat.mul_one _).symm]
      simp [tokv, show N ≤ j + (k + 1) by omega, show j + (k + 1) + 1 ≤ 2 * N by omega]
    have hd1 : dt.extract ((k + 1) * W) W = .ofBitVec ((sortAsc ys).getD (j + 1 + k - N) 0) := by
      have := hD.2 (k + 1) htop (by omega) (by omega)
      rwa [show j + (k + 1) - N = j + 1 + k - N by omega] at this
    by_cases hempty : j + k < N
    · have ht0 : (LVec.ofBitVec (packBV 1 N (tokv N j))).extract k 1 = .ofBitVec 0#1 := by
        rw [extract_ofBitVec_packBV (tokv N j) hk (Nat.mul_one _).symm]
        simp [tokv, show ¬ (N ≤ j + k) by omega]
      rw [cellWrite_load_empty _ _ ht0 ht1 hd1]
      have h0 : j + 1 + k - N = 0 := by omega
      have hpos : 0 < (sortAsc ys).length := by omega
      simp [h0, hpos]
    · have ht0 : (LVec.ofBitVec (packBV 1 N (tokv N j))).extract k 1 = .ofBitVec 1#1 := by
        rw [extract_ofBitVec_packBV (tokv N j) hk (Nat.mul_one _).symm]
        simp [tokv, show N ≤ j + k by omega, show j + k + 1 ≤ 2 * N by omega]
      have hd0 : dt.extract (k * W) W = .ofBitVec ((sortAsc ys).getD (j + 1 + k - N - 1) 0) := by
        have := hD.2 k hk (by omega) (by omega)
        rwa [show j + k - N = j + 1 + k - N - 1 by omega] at this
      rw [cellWrite_load_valid _ _ ht0 ht1 hd0 hd1]
      have hlt : j + 1 + k - N < (sortAsc ys).length := by omega
      have hne : j + 1 + k - N ≠ 0 := by omega
      simp [hlt, hne]
  · simp only [htop, ↓reduceIte]
    obtain rfl : k = N - 1 := by omega
    have hidxEq : j + 1 + (N - 1) - N = j := by omega
    have hnotlt : ¬ (j + 1 + (N - 1) - N < (sortAsc ys).length) := by omega
    by_cases hj0 : j = 0
    · subst hj0
      have ht0 : (LVec.ofBitVec (packBV 1 N (tokv N 0))).extract (N - 1) 1 = .ofBitVec 0#1 := by
        rw [extract_ofBitVec_packBV (tokv N 0) hk (Nat.mul_one _).symm, tokv_zero_eq_zero hk]
      rw [topWrite_load_empty _ _ ht0]
      simp [hidxEq, hSlen]
    · have ht1 : (LVec.ofBitVec (packBV 1 N (tokv N j))).extract (N - 1) 1 = .ofBitVec 1#1 := by
        rw [extract_ofBitVec_packBV (tokv N j) hk (Nat.mul_one _).symm]
        simp [tokv, show N ≤ j + (N - 1) by omega, show j + (N - 1) + 1 ≤ 2 * N by omega]
      have hd0 : dt.extract ((N - 1) * W) W = .ofBitVec ((sortAsc ys).getD (j + 1 + (N - 1) - N - 1) 0) := by
        have := hD.2 (N - 1) hk (by omega) (by omega)
        rwa [show j + (N - 1) - N = j + 1 + (N - 1) - N - 1 by omega] at this
      rw [topWrite_load_valid _ _ ht1 hd0]
      have hne : j + 1 + (N - 1) - N ≠ 0 := by omega
      simp [hnotlt, hne]

/-- **Drain step (`in_valid = 0`) preserves `DataOK`**, shifting valid cells down by 1. -/
theorem dataOK_run {N W j : Nat} (xs : List (BitVec W)) (hj : N ≤ j) (ck s id dt tk : LVec)
    (hD : DataOK N xs j dt) :
    DataOK N xs (j + 1) (nextData N W ck (knownBit false) s (knownBit false) id dt tk) := by
  refine ⟨by rw [width_nextData]; exact hD.1, fun k hk hlo hhi => ?_⟩
  rw [extract_nextData _ _ _ _ _ _ _ hD.1 hk]
  have htop : k + 1 < N := by omega
  simp only [htop, ↓reduceIte, cellWrite_drain, Option.getD_some]
  have := hD.2 (k + 1) htop (by omega) (by omega)
  rwa [show j + (k + 1) - N = j + 1 + k - N by omega] at this

/-! ## 8. Known-stimulus phase induction (`FollowsPU`) -/

theorem St_inj {ck r s iv id ov od dt tk ck' r' s' iv' id' ov' od' dt' tk' : LVec}
    (h : soG.St ck r s iv id ov od dt tk = soG.St ck' r' s' iv' id' ov' od' dt' tk') :
    ov = ov' ∧ od = od' ∧ dt = dt' ∧ tk = tk' := by
  simp only [soG.St, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at h
  exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem out_spec_eq {N W : Nat} (xs : List (BitVec W)) (hx : xs.length = N) :
    List.map (·.2) (List.filter (·.1)
      ((List.range N).map fun i => (ovb N (N + i), (sortAsc xs).getD (N + i - N) 0))) = sortAsc xs := by
  have h : ((List.range N).map fun i => (ovb N (N + i), (sortAsc xs).getD (N + i - N) 0)) =
      (List.range N).map fun i => (true, (sortAsc xs).getD i 0) :=
    List.map_congr_left fun i hi => by
      have := List.mem_range.mp hi; simp [ovb, show N + i - N = i by omega]; omega
  rw [h, List.filter_eq_self.mpr (by simp), List.map_map]
  exact List.ext_getElem (by simp [len_sort, hx]) fun i _ h2 => by simp [List.getElem?_eq_getElem h2]

theorem tokv_done_shift {N j : Nat} (hj : 2 * N - 1 ≤ j) (hN : 1 ≤ N) :
    packBV 1 N (tstep N false (tokv N j)) = packBV 1 N (tokv N 0) := by
  refine packBV_congr fun k hk => ?_
  rw [tokv_zero_eq_zero hk]
  simp only [tstep, tokv]
  split
  · rw [decide_eq_false (by omega)]; rfl
  · rfl

theorem Z_extract0 {N : Nat} (hN : 1 ≤ N) : (Z 1 N).extract 0 1 = knownBit false := by
  unfold Z
  rw [extract_ofBitVec_packBV (fun _ => (0 : BitVec 1)) (show 0 < N by omega) (Nat.zero_mul 1).symm]
  rfl

/-- One cycle from a state of `IK N W` on a known entry `e`. -/
def StpK (N W : Nat) (e prev st : SvState) : Prop :=
  ∃ ck r s iv id ov od dt tk, prev = soG.St ck r s iv id ov od dt tk ∧
    iv.width = 1 ∧ ov.width = 1 ∧ od.width = W ∧ dt.width = N * W ∧ tk.width = N ∧
    KnownEntry (soG.D N W) e ∧
    st = soG.next N W (appIn e "clk" ck) (appIn e "rst" r) (appIn e "start" s) (appIn e "in_valid" iv)
      (appIn e "in_data" id) ov od dt tk

/-- Ready phase: `tok = 0`, `out_valid = 0`, `data` arbitrary of width `N * W`. -/
def ReadyS (N W : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id od dt, st = soG.St ck r s iv id (knownBit false) od dt (Z 1 N) ∧
    od.width = W ∧ dt.width = N * W

/-- Active phase `j` cycles after a `start` with inputs `ys`. -/
def AtS (N W : Nat) (ys : List (BitVec W)) (j : Nat) (st : SvState) : Prop :=
  ∃ ck r s iv id od dt, st = soG.St ck r s iv id (knownBit (ovb N j)) od dt
    (.ofBitVec (packBV 1 N (tokv N j))) ∧ od.width = W ∧ DataOK (W := W) N ys j dt ∧
    (ovb N j = true → od = .ofBitVec ((sortAsc (W := W) ys).getD (j - N) 0))

/-- Output schedule `j` cycles after a `start`. -/
def outS (N W : Nat) (ys : List (BitVec W)) (j : Nat) : Tasks.Sorter.task.Obs (N, W) :=
  (ovb N j, (sortAsc (W := W) ys).getD (j - N) 0)

theorem outS_spec {N W : Nat} (hN : 1 ≤ N) (xs : List (BitVec W)) (hx : xs.length = N) :
    Tasks.Sorter.task.emitted (N, W) ((List.range (lat N W + 1)).map (outS N W xs)) = sortAsc xs := by
  rw [show lat N W + 1 = N + N by simp [lat]; omega, Tasks.Sorter.task.emitted_add,
    Tasks.Sorter.task.emitted_nil ?_, List.nil_append]
  · exact out_spec_eq xs hx
  · intro k hk; simp [outS, ovb]; omega

theorem outS_eq_false_of_emitted {N W : Nat} (hN : 1 ≤ N) {xs : List (BitVec W)} (hx : xs.length = N)
    {n : Nat} (hn : N ≤ (Tasks.Sorter.task.emitted (N, W) ((List.range n).map (outS N W xs))).length) :
    ∀ j, n ≤ j → (outS N W xs j).1 = false := by
  have hV := (Tasks.Sorter.task.emitted_add (outS N W xs) n (lat N W + 1)).symm.trans
    ((Tasks.Sorter.task.emitted_stable (fun j hj => by simp [outS, ovb, lat] at *; omega)
      (Nat.le_add_left (lat N W + 1) n)).trans (outS_spec hN xs hx))
  have hW := congrArg List.length hV
  have hlen : (sortAsc xs).length = N := (len_sort xs).trans hx
  rw [List.length_append] at hW
  change (Tasks.Sorter.task.emitted (N, W) ((List.range n).map (outS N W xs))).length +
      (Tasks.Sorter.task.emitted (N, W) ((List.range (lat N W + 1)).map fun i => outS N W xs (n + i))).length =
      (sortAsc xs).length at hW
  rw [hlen] at hW
  intro j hj
  rcases Nat.lt_or_ge (j - n) (lat N W + 1) with h | h
  · have h0 := List.eq_nil_of_length_eq_zero (show (Tasks.Sorter.task.emitted (N, W)
      ((List.range (lat N W + 1)).map fun i => outS N W xs (n + i))).length = 0 by omega)
    simp only [StreamTask.emitted, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_map, List.mem_range] at h0
    simpa [show n + (j - n) = j by omega] using h0 _ ⟨j - n, h, rfl⟩
  · simp [outS, ovb]; simp [lat] at h; omega

theorem step_reset {N W : Nat} (hN : 1 ≤ N) {e prev st : SvState}
    (hs : StpK N W e prev st) (hr : BitIs e "rst" true) : ReadyS N W st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, -, hiv, h1, h2, h3, h4, hke, rfl⟩ := hs
  rw [soG_next_eq N W _ _ _ _ _ _ _ _ _ h1 h2,
    show appIn e "rst" r = knownBit true from BitIs.appIn_eq hr r,
    nextTok_reset hN _ _ _ _ _ _ (appIn_iv_width hke hiv) h4, Z_extract0 hN]
  exact ⟨_, _, _, _, _, _, _, rfl, by simp, by rw [width_nextData]; exact h3⟩

theorem step_hold {N W : Nat} (hN : 1 ≤ N) {e prev st : SvState}
    (hs : StpK N W e prev st) (hp : ReadyS N W prev)
    (hr : BitIs e "rst" false) (hiv : BitIs e "in_valid" false) : ReadyS N W st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, h1, h2, h3, -, -, rfl⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hb, -⟩ := hp
  obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
  rw [soG_next_eq N W _ _ _ _ _ _ _ _ _ h1 h2,
    show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
    show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv,
    nextTok_run hN false (fun _ => 0)]
  have hts : tstep N false (fun _ => 0) = fun _ => 0 := funext fun k => by simp [tstep]
  rw [hts, Z_extract0 hN]
  exact ⟨_, _, _, _, _, _, _, rfl, by simp, by rw [width_nextData]; exact h3⟩

theorem step_start {N W : Nat} (hN : 1 ≤ N) {e prev st : SvState}
    (hs : StpK N W e prev st)
    (hp : ReadyS N W prev ∨ ∃ xs j, AtS N W xs j prev ∧ ∀ k, j < k → (outS N W xs k).1 = false)
    (hr : BitIs e "rst" false) (hiv : BitIs e "in_valid" false) : AtS N W [] 0 st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, h1, h2, h3, -, -, rfl⟩ := hs
  rw [soG_next_eq N W _ _ _ _ _ _ _ _ _ h1 h2,
    show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
    show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv]
  have htk0 : nextTok N W (appIn e "clk" ck) (knownBit false) (appIn e "start" s)
      (knownBit false) (appIn e "in_data" id) dt tk = .ofBitVec (packBV 1 N (tokv N 0)) := by
    rcases hp with ⟨_, _, _, _, _, _, _, hb, -⟩ | ⟨xs, j, ⟨_, _, _, _, _, _, _, hb, -⟩, hk⟩
    · obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
      rw [nextTok_run hN false (fun _ => 0)]
      refine congrArg _ (packBV_congr fun k hk => ?_)
      rw [tokv_zero_eq_zero hk]; simp [tstep]
    · obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
      have hj : 2 * N - 1 ≤ j := Nat.le_of_not_lt fun hc => by
        have := hk (max (j + 1) N) (by omega); simp [outS, ovb] at this; omega
      rw [nextTok_run hN false (tokv N j), tokv_done_shift hj hN]
  rw [htk0]
  have hov0 : (LVec.ofBitVec (packBV 1 N (tokv N 0))).extract 0 1 = knownBit (ovb N 0) := by
    rw [extract_ofBitVec_packBV (tokv N 0) (show 0 < N by omega) (Nat.zero_mul 1).symm, tokv_zero_eq_ovb]
  rw [hov0]
  exact ⟨_, _, _, _, _, _, _, rfl, by simp,
    ⟨by rw [width_nextData]; exact h3, fun k hk hlo => by omega⟩,
    fun ho => by simp [ovb] at ho; omega⟩

theorem step_feed {N W : Nat} (hN : 1 ≤ N) {e prev st : SvState} {ys : List (BitVec W)} {j : Nat} {x : BitVec W}
    (hs : StpK N W e prev st) (hp : AtS N W ys j prev) (hl : ys.length = j) (hj : j < N)
    (hr : BitIs e "rst" false) (hiv : BitIs e "in_valid" true)
    (hx : Tasks.Sorter.task.DataIs (N, W) e "in_data" x) : AtS N W (ys ++ [x]) (j + 1) st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, h1, h2, -, -, -, rfl⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hb, -, hD, -⟩ := hp
  obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
  have hid : appIn e "in_data" id = .ofBitVec x := by
    simp only [appIn, show SvState.lookup e "in_data" = some (.ofBitVec x) from hx, Option.getD_some]
  rw [soG_next_eq N W _ _ _ _ _ _ _ _ _ h1 h2,
    show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
    show appIn e "in_valid" iv = knownBit true from BitIs.appIn_eq hiv iv,
    hid, nextTok_run hN true (tokv N j),
    packBV_congr fun k hk => tok_step true (by simp; omega) hk]
  have hD' := dataOK_feed (W := W) ys x hj hl (appIn e "clk" ck) (appIn e "start" s) dt hD
  have hov' : (LVec.ofBitVec (packBV 1 N (tokv N (j + 1)))).extract 0 1 = knownBit (ovb N (j + 1)) := by
    rw [extract_ofBitVec_packBV (tokv N (j + 1)) (show 0 < N by omega) (Nat.zero_mul 1).symm,
      tokv_zero_eq_ovb]
  rw [hov']
  refine ⟨_, _, _, _, _, _, _, rfl, by simp, hD', fun ho => ?_⟩
  have ho' : N ≤ j + 1 ∧ j + 1 < 2 * N := by simpa [ovb] using ho
  have h0 := hD'.2 0 (by omega) (by omega) (by omega)
  simpa using h0

theorem step_run {N W : Nat} (hN : 1 ≤ N) {e prev st : SvState} {xs : List (BitVec W)} {j : Nat}
    (hs : StpK N W e prev st) (hp : AtS N W xs j prev) (hj : N ≤ j)
    (hr : BitIs e "rst" false) (hiv : BitIs e "in_valid" false) : AtS N W xs (j + 1) st := by
  obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, -, h1, h2, -, -, -, rfl⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hb, -, hD, -⟩ := hp
  obtain ⟨-, -, rfl, rfl⟩ := St_inj hb
  rw [soG_next_eq N W _ _ _ _ _ _ _ _ _ h1 h2,
    show appIn e "rst" r = knownBit false from BitIs.appIn_eq hr r,
    show appIn e "in_valid" iv = knownBit false from BitIs.appIn_eq hiv iv,
    nextTok_run hN false (tokv N j),
    packBV_congr fun k hk => tok_step false (by simp; omega) hk]
  have hD' := dataOK_run (W := W) xs hj (appIn e "clk" ck) (appIn e "start" s) (appIn e "in_data" id) dt
    (.ofBitVec (packBV 1 N (tokv N j))) hD
  have hov' : (LVec.ofBitVec (packBV 1 N (tokv N (j + 1)))).extract 0 1 = knownBit (ovb N (j + 1)) := by
    rw [extract_ofBitVec_packBV (tokv N (j + 1)) (show 0 < N by omega) (Nat.zero_mul 1).symm,
      tokv_zero_eq_ovb]
  rw [hov']
  refine ⟨_, _, _, _, _, _, _, rfl, by simp, hD', fun ho => ?_⟩
  have ho' : N ≤ j + 1 ∧ j + 1 < 2 * N := by simpa [ovb] using ho
  have h0 := hD'.2 0 (by omega) (by omega) (by omega)
  simpa using h0

theorem readyS_out {N W : Nat} {st : SvState} (h : ReadyS N W st) :
    BitIs st Tasks.Sorter.task.outValid false := by
  obtain ⟨_, _, _, _, _, _, _, rfl, -⟩ := h; simp [BitIs, Tasks.Sorter.task, soG.St, SvState.lookup]

theorem atS_out {N W : Nat} {ys : List (BitVec W)} {j : Nat} {st : SvState} (h : AtS N W ys j st) :
    BitIs st Tasks.Sorter.task.outValid (outS N W ys j).1 ∧
      ((outS N W ys j).1 = true → Tasks.Sorter.task.DataIs (N, W) st Tasks.Sorter.task.outData (outS N W ys j).2) := by
  obtain ⟨_, _, _, _, _, _, _, rfl, -, -, hd⟩ := h
  exact ⟨by simp [BitIs, Tasks.Sorter.task, outS, soG.St, SvState.lookup],
    fun ho => by simp [StreamTask.DataIs, Tasks.Sorter.task, outS, soG.St, SvState.lookup, hd ho]⟩

/-- **Rule 2 (`FollowsPU`)**: from every power-up state on every known stimulus, the stream guarantee holds. -/
theorem so_followsPU (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Tasks.Sorter.task.FollowsPU (N, W) (lat N W) (design.sem N W) := by
  intro st0 hpu σ stim tr hks hr c1 h hrel hR
  let t := Tasks.Sorter.task
  have hrun : RunFrom (design.sem N W) σ st0 stim tr := hr.runFrom
  have h0K : IK N W st0 := so_powerUpK N W hN hW hR32 st0 hpu
  have hksD : KnownStim (soG.D N W) stim := by rwa [soG.sem_eq N W hN hW hR32.1 hR32.2] at hks
  have hIK : ∀ (c : Nat) (st : SvState), tr[c]? = some st → IK N W st := by
    intro c
    induction c with
    | zero =>
        intro st hst
        obtain ⟨F, e, prev, k, k', he, hp, hc⟩ := hrun.snapshot_step hst
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; subst hp
        obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hiv, hw⟩ := h0K
        obtain ⟨k'', hc'⟩ := soG.cycle N W hN hW hR32.1 hR32.2 σ e ck r s iv id ov od dt tk k 32 (Nat.le_refl _)
        have hst' := (Prod.mk.inj (cycleStep2_det hc hc')).1
        rw [hst']
        exact next_IK _ _ _ _ _ _ _ _ _ (appIn_iv_width (hksD e (List.mem_of_getElem? he)) hiv) hw
    | succ c ih =>
        intro st hst
        obtain ⟨F, e, prev, k, k', he, hp, hc⟩ := hrun.snapshot_step hst
        simp only [List.getElem?_cons_succ] at hp
        obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hiv, hw⟩ := ih prev hp
        obtain ⟨k'', hc'⟩ := soG.cycle N W hN hW hR32.1 hR32.2 σ e ck r s iv id ov od dt tk k 32 (Nat.le_refl _)
        have hst' := (Prod.mk.inj (cycleStep2_det hc hc')).1
        rw [hst']
        exact next_IK _ _ _ _ _ _ _ _ _ (appIn_iv_width (hksD e (List.mem_of_getElem? he)) hiv) hw
  have hstepOf : ∀ {c : Nat} {st : SvState}, tr[c]? = some st → ∃ e prev, stim[c]? = some e ∧
      (st0 :: tr)[c]? = some prev ∧ StpK N W e prev st := by
    intro c st hst
    obtain ⟨F, e, prev, k, k', he, hp, hc⟩ := hrun.snapshot_step hst
    have hprevK : IK N W prev := by
      cases c with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hp; exact hp ▸ h0K
      | succ c => simp only [List.getElem?_cons_succ] at hp; exact hIK c prev hp
    obtain ⟨ck, r, s, iv, id, ov, od, dt, tk, rfl, hiv, h1, h2, h3, h4⟩ := hprevK
    obtain ⟨k'', hc'⟩ := soG.cycle N W hN hW hR32.1 hR32.2 σ e ck r s iv id ov od dt tk k 32 (Nat.le_refl _)
    exact ⟨e, _, he, hp, ck, r, s, iv, id, ov, od, dt, tk, rfl, hiv, h1, h2, h3, h4,
      hksD e (List.mem_of_getElem? he), (Prod.mk.inj (cycleStep2_det hc hc')).1⟩
  obtain ⟨hc1, ⟨e0, he0, hb0⟩, hoff⟩ := hrel
  obtain ⟨c0, rfl⟩ : ∃ c0, c1 = c0 + 1 := ⟨c1 - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at he0
  have hsnap : ∀ c, c0 ≤ c → c < h → ∃ st, tr[c]? = some st := fun c h1 h2 => by
    obtain ⟨e, he⟩ : ∃ e, stim[c]? = some e := by
      rcases Nat.eq_or_lt_of_le h1 with rfl | h1 <;>
        first | exact ⟨e0, he0⟩ | exact (hoff c h1 h2).imp fun _ h => h.1
    exact hrun.exists_snapshot (List.getElem?_eq_some_iff.mp he).1
  have onE : ∀ {c e n b}, stim[c]? = some e → StimBit stim c n b → BitIs e n b := by
    rintro c e n b he ⟨e', he', hb⟩; rw [he, Option.some.injEq] at he'; subst he'; exact hb
  let NoStart (a b : Nat) : Prop := ∀ s, a < s → s ≤ b → ¬ StimBit stim s t.start true
  let Ph (s c : Nat) (st : SvState) : Prop :=
    ∃ ys : List (BitVec W), ys.length = min (c - s) N ∧ t.InputsAt (N, W) stim s ys ∧
      AtS N W ys (c - s) st ∧ t.Hist (p := (N, W)) tr s (c - s) (outS N W ys)
  let Inv (c : Nat) : Prop :=
    ∃ st, tr[c]? = some st ∧ ((ReadyS N W st ∧ NoStart c0 c) ∨
      ∃ s, c0 < s ∧ s ≤ c ∧ StimBit stim s t.start true ∧ NoStart s c ∧
        (∀ s0, c0 < s0 → s0 < s → StimBit stim s0 t.start true → s0 + N < s) ∧ Ph s c st)
  have idle_done : ∀ {s c : Nat} {st : SvState}, s ≤ c →
      (∃ obs : List (t.Obs (N, W)), s + obs.length ≤ c + 1 ∧ t.Shows (N, W) tr s obs ∧
        (t.emitted (N, W) obs).length = N) → Ph s c st →
      ∃ xs : List (BitVec W), xs.length = N ∧ t.InputsAt (N, W) stim s xs ∧ N ≤ c - s ∧
        AtS N W xs (c - s) st ∧ t.Hist (p := (N, W)) tr s (c - s) (outS N W xs) ∧
        ∀ j, c - s < j → (outS N W xs j).1 = false := by
    rintro s c st hsc ⟨obs, hl, hsh, hc⟩ ⟨ys, hy, hin, hat, hh⟩
    rw [t.shows_hist hh hsh (by omega)] at hc
    by_cases hlt : c - s < N
    · rw [t.emitted_nil (n := obs.length) fun k hk => by simp [outS, ovb]; omega] at hc
      simp at hc; omega
    · have hx : ys.length = N := by omega
      have hge : N ≤ (Tasks.Sorter.task.emitted (N, W) ((List.range obs.length).map (outS N W ys))).length :=
        Nat.le_of_eq hc.symm
      exact ⟨ys, hx, hin, by omega, hat, hh, fun j hj =>
        outS_eq_false_of_emitted hN hx (n := obs.length) hge j (by omega)⟩
  have closed : ∀ c st, (ReadyS N W st ∧ NoStart c0 c) ∨ (∃ s, c0 < s ∧ s ≤ c ∧ NoStart s c ∧
      (∀ s0, c0 < s0 → s0 < s → StimBit stim s0 t.start true → s0 + N < s) ∧ N ≤ c - s) →
      ∀ s0, c0 < s0 → s0 ≤ c → StimBit stim s0 t.start true → s0 + N ≤ c := by
    rintro c st (⟨-, hn⟩ | ⟨s, h1, h2, hn, hw, hge⟩) s0 h3 h4 hs0
    · exact absurd hs0 (hn s0 h3 h4)
    · rcases Nat.lt_trichotomy s0 s with h5 | rfl | h5
      · have := hw s0 h3 h5 hs0; omega
      · omega
      · exact absurd hs0 (hn s0 h5 h4)
  have G : ∀ n, c0 + n < h → Inv (c0 + n) := by
    intro n
    induction n with
    | zero =>
        intro hh
        obtain ⟨st, hst⟩ := hsnap c0 (Nat.le_refl _) hh
        obtain ⟨e, prev, he, -, hstp⟩ := hstepOf hst
        rw [he0, Option.some.injEq] at he; subst he
        exact ⟨st, hst, .inl ⟨step_reset hN hstp hb0, fun s h1 h2 => absurd h2 (by omega)⟩⟩
    | succ n ih =>
        show c0 + n + 1 < h → Inv (c0 + n + 1)
        intro hh
        obtain ⟨prev, hprev, hG⟩ := ih (by omega)
        have hle : c0 ≤ c0 + n := Nat.le_add_right _ _
        generalize c0 + n = c at hprev hG hh hle
        obtain ⟨st, hst⟩ := hsnap (c + 1) (by omega) hh
        obtain ⟨e, prev', he, hp, hstp⟩ := hstepOf hst
        rw [List.getElem?_cons_succ, hprev, Option.some.injEq] at hp; subst hp
        have hr0 : BitIs e t.rst false := onE he (hoff (c + 1) (by omega) hh)
        obtain ⟨⟨b, hb⟩, ⟨e', (v : BitVec W), he', hv⟩, hidle, hon, hoff'⟩ := hR (c + 1) (by omega) hh
        rw [he, Option.some.injEq] at he'; subst he'
        cases b with
        | true =>
            obtain ⟨hidl, hcl⟩ : (ReadyS N W prev ∨ ∃ xs j, AtS N W xs j prev ∧
                ∀ k, j < k → (outS N W xs k).1 = false) ∧ ∀ s0, c0 < s0 → s0 ≤ c → StimBit stim s0 t.start true →
                s0 + N ≤ c := by
              rcases hG with hrd | ⟨s, h1, h2, hs0, hn, hw, hph⟩
              · exact ⟨.inl hrd.1, closed c prev (.inl hrd)⟩
              · obtain ⟨xs, -, -, hge, hat, -, hnp⟩ :=
                  idle_done h2 (hidle hb s (by omega) (by omega) hs0) hph
                exact ⟨.inr ⟨xs, _, hat, hnp⟩, closed c prev (.inr ⟨s, h1, h2, hn, hw, hge⟩)⟩
            have hiv := onE he (hoff' fun s0 h1 h2 h3 hs0 => by
              have h3' : c + 1 ≤ s0 + N := h3
              have := hcl s0 (by omega) (by omega) hs0; omega)
            have hat := step_start hN hstp hidl hr0 hiv
            refine ⟨st, hst, .inr ⟨c + 1, by omega, Nat.le_refl _, hb, fun s h1 h2 => absurd h2 (by omega),
              fun s0 h1 h2 hs0 => by have := hcl s0 h1 (by omega) hs0; omega, [], by simp,
              (fun j v h => by cases h), (by rw [Nat.sub_self]; exact hat), fun k hk => ?_⟩⟩
            obtain rfl : k = 0 := by omega
            exact ⟨st, by simpa using hst, atS_out hat⟩
        | false =>
            have hns : ∀ a, NoStart a c → NoStart a (c + 1) := by
              intro a hn s h1 h2 hs'
              rcases Nat.lt_or_ge c s with h3 | h3
              · obtain rfl : s = c + 1 := by omega
                exact Bool.false_ne_true (StimBit.unique hb hs')
              · exact hn s h1 h3 hs'
            rcases hG with ⟨hrd, hn⟩ | ⟨s, h1, h2, hs, hn, hw, ys, hy, hin, hat, hh⟩
            · have hiv := onE he (hoff' fun s0 h3 h4 _ hs0' => hn s0 (by omega) (by omega) hs0')
              exact ⟨st, hst, .inl ⟨step_hold hN hstp hrd hr0 hiv, hns c0 hn⟩⟩
            have hidx : tr[s + (c - s + 1)]? = some st := by rw [show s + (c - s + 1) = c + 1 by omega]; exact hst
            refine ⟨st, hst, .inr ⟨s, h1, by omega, hs, hns s hn, hw, ?_⟩⟩
            dsimp only [Ph]
            rw [show c + 1 - s = c - s + 1 by omega]
            rcases Nat.lt_or_ge (c - s) N with hlt | hge
            · have hiv := onE he (hon s (by omega) (by omega) (by show c + 1 ≤ s + N; omega) hs)
              have hat' := step_feed hN hstp hat (by omega) hlt hr0 hiv hv
              have heAt : stim[s + 1 + ys.length]? = some e := by
                rw [show s + 1 + ys.length = c + 1 by omega]; exact he
              refine ⟨ys ++ [v], by rw [List.length_append, List.length_singleton]; omega,
                t.inputs_snoc hin ⟨e, heAt, hv⟩, hat',
                t.hist_snoc (fun k hk => ?_) hidx (atS_out hat')⟩
              obtain ⟨st', h3, h4, -⟩ := hh k hk
              have hfk : (outS N W ys k).1 = false := by simp [outS, ovb]; omega
              have hfk' : (outS N W (ys ++ [v]) k).1 = false := by simp [outS, ovb]; omega
              rw [hfk] at h4
              exact ⟨st', h3, by rwa [hfk'], fun h5 => by rw [hfk'] at h5; cases h5⟩
            · have hcl := closed c prev (.inr ⟨s, h1, h2, hn, hw, hge⟩)
              have hiv := onE he (hoff' fun s0 h3 h4 h5 hs0' => by
                have h5' : c + 1 ≤ s0 + N := h5
                have := hcl s0 (by omega) (by omega) hs0'; omega)
              have hat' := step_run hN hstp hat hge hr0 hiv
              exact ⟨ys, by omega, hin, hat', t.hist_snoc hh hidx (atS_out hat')⟩
  have hInv : ∀ c, c0 ≤ c → c < h → Inv c := fun c h1 h2 => by
    obtain ⟨n, rfl⟩ : ∃ n, c = c0 + n := ⟨c - c0, by omega⟩
    exact G n h2
  have key : ∀ s, c0 < s → StimBit stim s t.start true → ∀ c, s ≤ c → c < h →
      NoStart s c → ∃ st, tr[c]? = some st ∧ Ph s c st := by
    intro s hs hst c h1 h2 hn
    obtain ⟨st, hc, ⟨-, hn0⟩ | ⟨s0, h3, h4, hs0, hn0, -, hph⟩⟩ := hInv c (by omega) h2
    · exact absurd hst (hn0 s hs h1)
    · rcases Nat.lt_trichotomy s0 s with h5 | rfl | h5 <;>
        first | exact ⟨st, hc, hph⟩ | exact absurd hst (hn0 s h5 h1) | exact absurd hs0 (hn s0 h5 h4)
  refine ⟨fun c h1 h2 => ?_, fun c h1 h2 hn => ?_, fun s xs h1 h2 hs hx hin e h3 h4 hne he => ?_⟩
  · obtain ⟨st, hc, ⟨hrd, -⟩ | ⟨s, -, -, -, -, -, ys, -, -, hat, -⟩⟩ := hInv c (by omega) h2
    · exact ⟨false, st, hc, readyS_out hrd⟩
    · exact ⟨_, st, hc, (atS_out hat).1⟩
  · obtain ⟨st, hc, ⟨hrd, -⟩ | ⟨s, h3, h4, hs, -⟩⟩ := hInv c (by omega) h2
    · exact ⟨st, hc, readyS_out hrd⟩
    · exact absurd hs (hn s (by omega) h4)
  · have hlatEq : lat N W = 2 * N - 1 := rfl
    have hlatN : N ≤ lat N W := by omega
    have hxsLen : xs.length = N := hx
    obtain ⟨st, -, hph⟩ := key s (by omega) hs (e - 1) (by omega) (by omega) fun s' h5 h6 => hne s' h5 (by omega)
    obtain ⟨xs', hx', hin', hh, hnp⟩ : ∃ xs' : List (BitVec W), xs'.length = N ∧ t.InputsAt (N, W) stim s xs' ∧
        t.Hist (p := (N, W)) tr s (e - 1 - s) (outS N W xs') ∧ ∀ j, e - s ≤ j → (outS N W xs' j).1 = false := by
      rcases Nat.lt_or_ge e h with he' | he'
      · obtain ⟨xs', hx', hin', -, -, hh, hnp⟩ := idle_done (by omega) (by
          rw [show e - 1 + 1 = e by omega]; exact (hR e (by omega) he').2.2.1 (he he') s (by omega) (by omega) hs) hph
        exact ⟨xs', hx', hin', hh, fun j hj => hnp j (by omega)⟩
      · obtain ⟨ys, hy, hin', -, hh⟩ := hph
        exact ⟨ys, by omega, hin', hh, fun j hj => by simp [outS, ovb]; omega⟩
    have heqxs : xs' = xs := t.inputs_unique hin' hin (hx'.trans hxsLen.symm)
    subst heqxs
    refine ⟨(List.range (e - s)).map (outS N W xs'), by simp, fun k o hk => ?_,
      ((t.emitted_stable hnp (Nat.le_add_right _ (lat N W + 1))).symm.trans
        (t.emitted_stable (fun j hj => by simp [outS, ovb]; omega) (Nat.le_add_left _ _))).trans
        (outS_spec hN xs' hxsLen),
      fun k o hk hl => ?_⟩
    all_goals obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
    all_goals (simp only [List.length_map, List.length_range] at hlt
               simp only [List.getElem_map, List.getElem_range])
    · exact hh k (by omega)
    · simp [outS, ovb]; omega

/-! ## 9. Interface, discipline, Moore outputs (rule 1), `XSafe` (rule 3), and `solution` -/

theorem so_interface (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Tasks.Sorter.task.Interface (N, W) (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2]
  exact ⟨rfl, rfl, by
    show (["clk", "rst", "start", "in_valid", "in_data", "out_valid", "out_data", "data", "tok"] :
      List String).Nodup
    decide⟩

theorem so_disciplined (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    Tasks.Sorter.task.Disciplined (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2]
  refine ⟨by simp [Tasks.Sorter.task, soG.D, soG.decls, Design2.inputNames], fun p hp => ?_⟩
  have hm : p ∈ soG.procs N W := by simpa [soG.D] using hp
  simp only [soG.procs, List.mem_cons, List.mem_map] at hm
  rcases hm with rfl | rfl | rfl | ⟨k, -, rfl⟩ <;>
    simp [Tasks.Sorter.task, soG.p0, soG.p1, soG.p2, soG.gen_cell, Process2.isEdgePhase,
      edgeClock, asyncReset, processDataNames, stmtNames, stmtOptNames, stmtListNames, lhsNames, exprNames]

/-- **Rule 1 (`MooreOutDep`)**: the only combinational edges are `out_valid ← tok` and `out_data ← data`,
so no input reaches either output. -/
theorem so_moore (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    MooreOutDep (design.sem N W) [] := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2]
  refine ⟨fun n => n ∈ (["clk", "rst", "start", "in_valid", "in_data"] : List String),
    fun n hn _ => by simpa [soG.D, soG.decls, Design2.inputNames] using hn, ?_, ?_⟩
  · intro e he hr
    have hdeps : combDeps (soG.D N W) =
        [("out_valid", ["out_valid", "tok"]), ("out_data", ["out_data", "data"])] := by
      simp [combDeps, soG.D, soG.procs, soG.p0, soG.p1, soG.p2, soG.gen_cell,
        processDeps, lhsTargets, lhsNames, exprNames]
    rw [hdeps] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;>
      · obtain ⟨r, hr1, hr2⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr1
        rcases hr1 with rfl | rfl <;> simp at hr2
  · intro o ho hS
    have houts : (soG.D N W).outputNames.toList = ["out_valid", "out_data"] := by
      simp [soG.D, soG.decls, Design2.outputNames]
    rw [houts] at ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp at hS

/-- **Rule 3 (`XSafe`)**: every slice is in range and every bitwise operand has matching width. -/
theorem so_xsafe (N W : Nat) (hN : 1 ≤ N) (hW : 1 ≤ W) (hR32 : Rng32 N W) :
    XSafe (design.sem N W) := by
  rw [soG.sem_eq N W hN hW hR32.1 hR32.2]
  have hTop : (N - 1) * W + W ≤ N * W := rowMajor_le (K := W) (show N - 1 < N by omega)
  have hTopT : N - 1 + 1 ≤ N := by omega
  have hOut : W ≤ N * W := by
    have := rowMajor_le (K := W) (show 0 < N by omega); simpa using this
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm : p ∈ soG.procs N W := by simpa [soG.D] using hp
  simp only [soG.procs, List.mem_cons, List.mem_map, List.mem_range] at hm
  rcases hm with rfl | rfl | rfl | ⟨k, hk, rfl⟩
  · simp [xsProc, xsLhs, xsWidth, sigWidth, soG.p0, soG.D, soG.decls]; omega
  · simp [xsProc, xsLhs, xsWidth, sigWidth, soG.p1, soG.D, soG.decls, hOut]
  · simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth,
      soG.p2, soG.D, soG.decls, hTop, hTopT]
  · have h1 : (k + 1) * W + W ≤ N * W := rowMajor_le (K := W) (show k + 1 < N by omega)
    have h2 : k * W + W ≤ N * W := rowMajor_le (K := W) (show k < N by omega)
    have ht1 : k + 1 + 1 ≤ N := by omega
    have ht0 : k + 1 ≤ N := by omega
    simp [xsProc, xsStmt, xsStmts, xsOpt, xsLhs, xsWidth, binW, sigWidth,
      soG.gen_cell, soG.D, soG.decls, h1, h2, ht1, ht0]

/-- **Main theorem**: `solutions/sorter/solution.sv` satisfies `Tasks.Sorter.Statement` at latency `2N - 1`
(`15` at `(8, 8)`). -/
theorem solution : Goal lat := by
  refine ⟨fun p hp => ?_, rfl⟩
  obtain ⟨N, W⟩ := p
  obtain ⟨hN, hW, hNW32⟩ := hp
  have hR32 : Rng32 N W := rng32_of hN hW hNW32
  exact ⟨so_interface N W hN hW hR32,
    ⟨so_disciplined N W hN hW hR32, so_terminatesPU N W hN hW hR32⟩,
    by simp [lat]; omega,
    so_followsPU N W hN hW hR32,
    so_moore N W hN hW hR32,
    so_xsafe N W hN hW hR32⟩

end Submission
