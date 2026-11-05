import CounterCycle
import LeanModels.Sv.Kernel.Core1Edge

/-!
# The counter's cycle step, derived from E (D-X1h: the first R-CYCLE slice against the authority)

Not in any lake library and imported by nothing trusted. Compile with `compile-obsE.sh`
(`MODULES="SeqTask CounterCycle CounterE"`). P's files (`../sequential/CounterCycle.lean`) are read,
not edited.

**Status: derived from E** (E-core-1's edge fragment, `LeanModels/Sv/Kernel/Core1Edge.lean`).

The counter (`tests/seq_counter/reference/cnt.sv`) is one `always_ff @(posedge clk)` with a synchronous reset and
NBA-only body, no comb process. In E-core-1 it is `cntE N`: `cntD N`'s declarations, its body as an
edge process (`rstn := none`: a synchronous reset is data). A cycle of the harness
(`clockExpand`, disciplined by `clockExpand_disciplined`) is two slots:

1. `cnt_low`: a slot whose input events set the clock low (with any data) fires nothing and closes
   where it opens: the inputs are applied, nothing else changes.
2. `cnt_rise`: a slot whose only event is the clock rising closes, under EVERY legal schedule, with
   `q` replaced by P's `cntNext N r e q` (`r`, `e`, `q` the values the slot opens with), and the
   inputs unchanged. From `rEdge`.
3. `cnt_rise_step`: through P's `Rel`, the closed `q` is the spec state after `cntTask.step` (reset
   low) or `cntTask.init` (reset high): the counter's cycle-machine step, derived from E.

This is the cycle step only. The Obs-level inclusion over the E-core-1 backend `Obs_E1`, with the
clock port hidden, is `CounterEObs.lean` (`X1-NOTE.md` §12).
-/

namespace SvGolf.Arch.CntE

open LeanModels.Sv LeanModels.Sv.Kernel SvGolf.Seq SvGolf.Seq.Counter

/-- The counter's edge body (the body of `cntD N`'s one process). -/
def cntBody (N : Nat) : Stmt2 :=
  .ifStmt (.ident "rst")
    (.nbaAssign (.ident "q") (.lit (LVec.replicate N .l0)))
    (some (.ifStmt (.ident "en")
      (.nbaAssign (.ident "q") (.binary .add (.ident "q") (.resize N (.lit ⟨#[.l1]⟩))))
      none))

theorem cntD_processes (N : Nat) : (cntD N).processes = #[.alwaysFF "clk" (cntBody N)] := rfl

/-- **The counter in E-core-1.** -/
def cntE (N : Nat) : Elab1 :=
  { decls := (cntD N).decls, procs := #[{ clk := "clk", rstn := none, body := cntBody N }],
    name := "cnt" }

theorem cntE_four (N : Nat) : AllFour (cntE N).base := by
  intro dc hdc
  simp [cntE, cntD, Elab1.base] at hdc
  rcases hdc with rfl | rfl | rfl | rfl <;> rfl

theorem cntE_nodup (N : Nat) : ((cntE N).decls.toList.map Decl.name).Nodup := by
  simp [cntE, cntD]

/-- **The edge profile holds at every `N`** (the checks by `rfl` at a free `N`). -/
theorem cntE_profile (N : Nat) : EdgeProfile (cntE N) :=
  EdgeProfile.ofChecks (cntE_four N) (cntE_nodup N) rfl rfl rfl

/-! ## The slot where the clock rises -/

theorem cntE_next (N : Nat) (s : Store) :
    (cntE N).next s 0 = execFF (cntE N).design ((cntE N).base.view s) (cntBody N) := rfl

theorem cntE_declWidth_q (N : Nat) : (cntE N).design.declWidth "q" = some N := by
  simp [Design2.declWidth, Elab1.design, Elab1.base, Elab.toDesign2, cntE, cntD]

theorem cntE_window (N : Nat) :
    Lhs2.windows? (cntE N).design (.ident "q") = some [("q", 0, N)] := by
  simp [Lhs2.windows?, Lhs2.window?, Design2.declWidth, Elab1.design, Elab1.base,
    Elab.toDesign2, cntE, cntD]

/-- **The counter's updates**, computed on the store the slot opens with: reset, increment, or
none. -/
theorem cntE_queue {N : Nat} {s : Store} {r e q : LVec}
    (hr : SvState.lookup ((cntE N).base.view s) "rst" = some r)
    (he : SvState.lookup ((cntE N).base.view s) "en" = some e)
    (hq : SvState.lookup ((cntE N).base.view s) "q" = some q) :
    (cntE N).queue s [0] =
      if r.condTrue then [("q", 0, ((LVec.replicate N .l0).resizeU N).extract 0 N)]
      else if e.condTrue then
        [("q", 0, ((evalBinOp .add q ((⟨#[.l1]⟩ : LVec).resizeU N)).resizeU N).extract 0 N)]
      else [] := by
  simp only [Elab1.queue, Elab1.upd, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    cntE_next]
  by_cases hrc : r.condTrue = true
  · simp [cntBody, execFF, evalPure2, readSignal, hr, hrc, Lhs2.windows?, Lhs2.window?,
      cntE_declWidth_q, Win.placed, Win.sumWidth]
  · by_cases hec : e.condTrue = true
    · simp [cntBody, execFF, execFFOpt, evalPure2, readSignal, hr, he, hq, hrc, hec, Lhs2.windows?,
        Lhs2.window?, cntE_declWidth_q, Win.placed, Win.sumWidth, evalBinOp]
    · simp [cntBody, execFF, execFFOpt, evalPure2, readSignal, hr, he, hrc, hec]

theorem isPosedge_to_l0 (b : Logic) : isPosedge b .l0 = false := by cases b <;> rfl

/-- **A slot whose input events set the clock low fires nothing** and closes where it opens: the
inputs are applied, nothing else happens (the reset is synchronous: data). -/
theorem cnt_low (N : Nat) (ch : Choice) (c : Config1) (entry : SvState)
    (hlow : SvState.bit0 ((cntE N).base.view ((cntE N).base.applyInputs c.store entry)) "clk" = .l0) :
    SlotCloses1 (cntE N) ch (Config1.nextSlot (cntE N) c entry)
      (Config1.nextSlot (cntE N) c entry) := by
  have htr : (cntE N).triggered ((cntE N).base.view c.store)
      ((cntE N).base.view ((cntE N).base.applyInputs c.store entry)) = [] := by
    generalize (cntE N).base.view c.store = st at hlow ⊢
    generalize (cntE N).base.view ((cntE N).base.applyInputs c.store entry) = st' at hlow ⊢
    simp [Elab1.triggered, cntE, FF.fires, hlow, isPosedge_to_l0]
  have hnil : ch.choose c.k [] = [] := List.perm_nil.mp (ch.choose_perm _ [])
  refine ⟨.refl _, ?_⟩
  simp [step1, Config1.nextSlot, htr, hnil]

/-- A rising clock makes the counter's process the ready set. -/
theorem cnt_rise_open (N : Nat) {st st' : SvState} (h0 : SvState.bit0 st "clk" = .l0)
    (h1 : SvState.bit0 st' "clk" = .l1) : (cntE N).triggered st st' = [0] := by
  simp [Elab1.triggered, cntE, FF.fires, h0, h1, isPosedge]

/-- **The slot where the clock rises** (derived from E, by `rEdge`): under every legal schedule it
closes with `q` replaced by P's `cntNext N r e q`, every other signal unchanged. -/
theorem cnt_rise (N : Nat) (ch : Choice) {s : Store} (hT : (cntE N).base.Typed s) (k : Nat)
    {r e q : LVec} (hr : SvState.lookup ((cntE N).base.view s) "rst" = some r)
    (he : SvState.lookup ((cntE N).base.view s) "en" = some e)
    (hq : SvState.lookup ((cntE N).base.view s) "q" = some q) (hqw : q.width = N) :
    ∃ c', SlotCloses1 (cntE N) ch { store := s, active := [0], nba := [], k := k } c' ∧
      SvState.lookup ((cntE N).base.view c'.store) "q" = some (cntNext N r e q) ∧
      ∀ n, n ≠ "q" →
        SvState.lookup ((cntE N).base.view c'.store) n = SvState.lookup ((cntE N).base.view s) n := by
  obtain ⟨c', hcl, hview⟩ := rEdge (cntE_profile N) ch hT (act := [0]) (by simp)
    (fun p hp => by rw [List.mem_singleton.mp hp]; exact Nat.zero_lt_one) k
  refine ⟨c', hcl, ?_, fun n hn => ?_⟩
  · rw [hview, cntE_queue hr he hq]
    by_cases hrc : r.condTrue = true
    · simp [hrc, commitNba2, hq, cntNext, hqw]
    · by_cases hec : e.condTrue = true
      · simp [hrc, hec, commitNba2, hq, cntNext, hqw, evalBinOp, LVec.extract_zero_of_width]
      · simp [hrc, hec, commitNba2, hq, cntNext]
  · rw [hview]
    refine lookup_commitNba2_of_not_mem _ _ fun u hu => ?_
    rw [cntE_queue hr he hq] at hu
    split at hu
    · simp at hu; rw [hu]; exact fun h => hn h.symm
    · split at hu
      · simp at hu; rw [hu]; exact fun h => hn h.symm
      · simp at hu

theorem lit_zero : (⟨#[.l0]⟩ : LVec) = LVec.ofBitVec (0#1) := by
  first
  | decide
  | rfl

theorem condTrue_zero : (LVec.ofBitVec (0#1)).condTrue = false := by
  rw [← lit_zero]; first | decide | simp [LVec.condTrue] | simp [LVec.condTrue, Array.any_eq_true]

theorem condTrue_one : (LVec.ofBitVec (1#1)).condTrue = true := by
  rw [← lit_one]; first | decide | simp [LVec.condTrue] | simp [LVec.condTrue, Array.any_eq_true]

/-- **The counter's cycle-machine step, derived from E.** Through P's `Rel` (`q` holds the spec
state, known): with the reset high the closed `q` is `cntTask.init`; with it low and the enable
`b`, it is `cntTask.step` of the spec state. -/
theorem cnt_rise_step (N : Nat) (ch : Choice) {s : Store} (hT : (cntE N).base.Typed s) (k : Nat)
    {r e : LVec} {x : BitVec N} (hr : SvState.lookup ((cntE N).base.view s) "rst" = some r)
    (he : SvState.lookup ((cntE N).base.view s) "en" = some e)
    (hq : SvState.lookup ((cntE N).base.view s) "q" = some (LVec.ofBitVec x)) :
    ∃ c', SlotCloses1 (cntE N) ch { store := s, active := [0], nba := [], k := k } c' ∧
      (r.condTrue = true →
        SvState.lookup ((cntE N).base.view c'.store) "q" = some (LVec.ofBitVec (cntTask.init N))) ∧
      ∀ b : BitVec 1, r.condTrue = false → e = LVec.ofBitVec b →
        SvState.lookup ((cntE N).base.view c'.store) "q" =
          some (LVec.ofBitVec (cntTask.step N x (b, ()))) := by
  have hqw : (LVec.ofBitVec x).width = N := by simp [LVec.ofBitVec, LVec.ofNat, LVec.width]
  obtain ⟨c', hcl, hqc, -⟩ := cnt_rise N ch hT k hr he hq hqw
  refine ⟨c', hcl, fun hrc => ?_, fun b hrc heb => ?_⟩
  · rw [hqc, cntNext_reset N e _ hrc hqw]
    rfl
  · rw [hqc]
    rcases bv1_cases b with rfl | rfl
    · rw [cntNext_hold N _ hrc (by rw [heb]; exact condTrue_zero)]
      simp [cntTask]
    · rw [cntNext_inc N x hrc (by rw [heb]; exact condTrue_one)]
      simp [cntTask]

#print axioms cntE_profile
#print axioms cnt_low
#print axioms cnt_rise
#print axioms cnt_rise_step
#print axioms cnt_rise_open

end SvGolf.Arch.CntE
