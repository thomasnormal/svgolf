import SvGolf.TaskReact
import SvGolf.SeqV2
import LeanModels.Sv.Seq2Cycle

/-!
# Proof helpers for reactive tasks (untrusted, kernel-checked)

Nothing here is part of the trusted base. It goes with the trusted text `SvGolf/TaskReact.lean`
(`ReactTask`): the reduction a reactive reference proof targets, from facts about ONE cycle.

## API

* **`ReactTask.responds_of_rank`** (the window argument): a rank `≤ K` that drops at every step
  whose input triggers an obligation and whose output does not answer it gives bounded response.
* `ReactTask.ghostAt_succ`: the safety monitor's ghost state one cycle on.
* **`ReactTask.RankModel`** and **`ReactTask.satisfiedAt_of_rank`**, the reactive reduction (the
  route of `tasks/arbiter/README.md` (e)): the statement at one parameter value from the interface,
  the discipline, termination from every power-up (`TerminatesPU`, e.g. by
  `TerminatesPU.of_invariant`), rule 3 (`XSafe`, decided by `xsafeB`), and a rank model whose shape
  every power-up state has, i.e. the clock step (`CycleModel`), an invariant of the snapshots from a
  reset on (indexed by the ghost state), the outputs it shows, a RESET obligation (from any state of
  the shape), a STEP obligation (safety, the next invariant, and per obligation: answered, or the
  rank drops) and the rank bound. Release, the segment, the ghost state and the window are
  discharged once, here (`ReactTask.claim_of_rank`, one run from one start state of the shape).
* **`ReactTask.snapshots_known`**: every snapshot of every run of the statement (every power-up,
  every known stimulus) of a design that satisfies it is known, by txtask-v2's x-free lemma
  (`xfree_runsAt`): what v1's known-state clause asked, implied by rule 3.
* **`mooreOut_of_combTargets`**: a design whose comb processes write no output (and whose outputs
  are not inputs) is Moore (`MooreOut`, `S` = the inputs and every comb target).
-/

namespace SvGolf

open LeanModels.Sv

namespace ReactTask

variable {P : Type} (t : ReactTask P)

/-- **Bounded response from a ranking.** If a rank `≤ K` (indexed by the position in the segment)
drops at every step whose input triggers `o` and whose output does not respond to `o`, then every
window of `K + 1` triggers contains a response. -/
theorem responds_of_rank {p : P} {K : Nat} {xs : List (t.In p)} {ys : List (t.Out p)}
    (hl : ys.length = xs.length) (rank : t.Obl p → Nat → Nat)
    (hK : ∀ o j, j ≤ xs.length → rank o j ≤ K)
    (hdec : ∀ o j x y, xs[j]? = some x → ys[j]? = some y → t.trig p o x →
      t.resp p o y ∨ rank o (j + 1) < rank o j) :
    t.Responds p K xs ys := by
  intro o j hj htr
  refine Classical.byContradiction fun hno => ?_
  have key : ∀ i, i ≤ K + 1 → rank o (j + i) + i ≤ rank o j := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have ih' := ih (by omega)
        have hxi : j + i < xs.length := by omega
        have hyi : j + i < ys.length := by omega
        rcases hdec o (j + i) xs[j + i] ys[j + i] (List.getElem?_eq_getElem hxi)
            (List.getElem?_eq_getElem hyi)
            (htr i xs[j + i] (by omega) (List.getElem?_eq_getElem hxi)) with hr | hr
        · exact (hno ⟨i, ys[j + i], by omega, List.getElem?_eq_getElem hyi, hr⟩).elim
        · rw [show j + (i + 1) = j + i + 1 by omega]
          omega
  have h1 := key (K + 1) (Nat.le_refl _)
  have h2 := hK o j (by omega)
  omega

/-- The ghost state one cycle on. -/
theorem ghostAt_succ (p : P) (xs : List (t.In p)) (ys : List (t.Out p)) (n : Nat)
    (hx : n < xs.length) (hy : n < ys.length) :
    t.ghostAt p xs ys (n + 1) = t.gnext p (t.ghostAt p xs ys n) xs[n] ys[n] := by
  have hz : n < (xs.zip ys).length := by simp only [List.length_zip]; omega
  simp only [ghostAt, List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some,
    List.foldl_append, List.foldl_cons, List.foldl_nil, List.getElem_zip]

/-- **A rank model of `d` for `t` at `p` and the response bound `K`**: the clock step, an
invariant `Inv g st` of the snapshots from a reset on (`g` the safety monitor's ghost state before
the next cycle), the outputs `out st` an invariant state shows, and a rank per obligation; the
obligations are about ONE `Step` (no trace, segment or fuel). (The `CycleModel`'s `init`, the
shape of `initState2 d`, is not used by the v2 reduction, which asks the shape of every power-up
state instead.)
* a cycle whose entry asserts reset and drives known inputs yields `Inv (ginit)`, with `atReset`
  of its outputs, from ANY state of the shape;
* a cycle whose entry deasserts reset and drives the known inputs `x`, from `Inv g`, yields
  `Inv (gnext g x y)` for its outputs `y`, `safe g x y`, and for every obligation `o` triggered
  by `x`: `y` answers `o`, or `o`'s rank drops. -/
structure RankModel (p : P) (K : Nat) (d : Design2) extends CycleModel d where
  /-- The invariant of the snapshots from a reset on, with the ghost state before the next cycle. -/
  Inv : t.Ghost p → SvState → Prop
  /-- The output values a snapshot shows. -/
  out : SvState → t.Out p
  /-- An invariant state shows its outputs, known. -/
  shows : ∀ g st, Inv g st → HoldAll st (t.outputs p) (out st)
  /-- The rank of an obligation in a state (for a round-robin: the cyclic distance from the
  priority pointer). -/
  rank : t.Obl p → SvState → Nat
  /-- The rank is at most `K` in every invariant state. -/
  rank_le : ∀ o g st, Inv g st → rank o st ≤ K
  /-- A reset cycle with known inputs yields the invariant at the initial ghost state, from any
  state of the shape, and its outputs meet `atReset`. -/
  reset : ∀ e prev st x, Shape prev → Step e prev st → BitIs e t.rst true →
    HoldAll e (t.inputs p) x → Inv (t.ginit p) st ∧ t.atReset p (out st)
  /-- A cycle with reset deasserted and the known inputs `x`, from `Inv g`: the next invariant,
  safety, and per obligation triggered by `x`, an answer or a smaller rank. -/
  step : ∀ e prev st g x, Shape prev → Step e prev st → Inv g prev → BitIs e t.rst false →
    HoldAll e (t.inputs p) x →
    Inv (t.gnext p g x (out st)) st ∧ t.safe p g x (out st) ∧
      ∀ o, t.trig p o x → t.resp p o (out st) ∨ rank o st < rank o prev

/-- **The reactive claim from a rank model**, for one completed run from a start state `st0` of the
model's shape: at every reset release, for every list of inputs the segment drives, the snapshots
show outputs meeting the guarantee. -/
theorem claim_of_rank {p : P} {K : Nat} {d : Design2} (M : t.RankModel p K d) {σ : ScheduleOracle}
    {st0 : SvState} {stim tr : List SvState} (h0 : M.Shape st0) (hr : RunFrom d σ st0 stim tr) :
    ∀ (c1 : Nat) (x0 : t.In p) (xs : List (t.In p)), Released t.rst stim c1 (c1 + xs.length) →
      t.InsAt p stim (c1 - 1) (x0 :: xs) →
      ∃ (y0 : t.Out p) (ys : List (t.Out p)), ys.length = xs.length ∧
        t.ShowsAt p tr (c1 - 1) (y0 :: ys) ∧ t.Guar p K xs y0 ys := by
  intro c1 x0 xs hrel hins
  obtain ⟨hc1, hrs0, hoff⟩ := hrel
  obtain ⟨c0, rfl⟩ : ∃ c0, c1 = c0 + 1 := ⟨c1 - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hrs0 hins ⊢
  -- the snapshot at segment position `j`, and the outputs the segment shows
  obtain ⟨S, hS⟩ : ∃ S : Nat → SvState, ∀ j, S j = (tr[c0 + j]?).getD [] := ⟨_, fun _ => rfl⟩
  obtain ⟨ys, hyl, hyn⟩ : ∃ ys : List (t.Out p), ys.length = xs.length ∧
      ∀ j (h : j < ys.length), ys[j] = M.out (S (j + 1)) :=
    ⟨(List.range xs.length).map fun j => M.out (S (j + 1)), by simp, fun j h => by simp⟩
  have hin : ∀ j x, (x0 :: xs)[j]? = some x → ∃ e, stim[c0 + j]? = some e ∧
      HoldAll e (t.inputs p) x := hins
  have honE : ∀ {c : Nat} {e : SvState} {b : Bool}, stim[c]? = some e →
      StimBit stim c t.rst b → BitIs e t.rst b := by
    rintro c e b he ⟨e', he', hb⟩
    rw [he, Option.some.injEq] at he'
    subst he'
    exact hb
  have hsnap : ∀ {c : Nat} {e : SvState}, stim[c]? = some e → ∃ st, tr[c]? = some st :=
    fun he => RunFrom.exists_snapshot hr (List.getElem?_eq_some_iff.mp he).1
  -- the reset cycle
  have base : tr[c0 + 0]? = some (S 0) ∧ M.Inv (t.ginit p) (S 0) ∧ t.atReset p (M.out (S 0)) := by
    obtain ⟨e, he, hx⟩ := hin 0 x0 (by simp)
    obtain ⟨st, hst⟩ := hsnap he
    obtain ⟨e', prev, he', -, hsh, hs⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
    have hee : e' = e := by rw [he] at he'; exact (Option.some.inj he').symm
    rw [hee] at hs
    have hS0 : S 0 = st := by rw [hS, hst, Option.getD_some]
    rw [hS0]
    exact ⟨hst, M.reset e prev st x0 hsh hs (honE he hrs0) hx⟩
  -- one cycle of the segment
  have one : ∀ n (hn : n < xs.length), tr[c0 + n]? = some (S n) →
      tr[c0 + (n + 1)]? = some (S (n + 1)) ∧
      ∀ g, M.Inv g (S n) → M.Inv (t.gnext p g xs[n] (M.out (S (n + 1)))) (S (n + 1)) ∧
        t.safe p g xs[n] (M.out (S (n + 1))) ∧
        ∀ o, t.trig p o xs[n] → t.resp p o (M.out (S (n + 1))) ∨
          M.rank o (S (n + 1)) < M.rank o (S n) := by
    intro n hn hprev
    obtain ⟨e, he, hx⟩ := hin (n + 1) xs[n] (by simp [hn])
    have hb : BitIs e t.rst false := honE he (hoff (c0 + (n + 1)) (by omega) (by omega))
    obtain ⟨st, hst⟩ := hsnap he
    obtain ⟨e', prev, he', hp, hsh, hs⟩ := CycleModel.snapshotFrom M.toCycleModel h0 hr hst
    have hee : e' = e := by rw [he] at he'; exact (Option.some.inj he').symm
    rw [hee] at hs
    have hpp : prev = S n := by
      rw [show c0 + (n + 1) = (c0 + n) + 1 by omega, List.getElem?_cons_succ, hprev] at hp
      exact (Option.some.inj hp).symm
    rw [hpp] at hs hsh
    have hSn : S (n + 1) = st := by rw [hS, hst, Option.getD_some]
    rw [hSn]
    exact ⟨hst, fun g hg => M.step e (S n) st g xs[n] hsh hs hg hb hx⟩
  -- the invariant along the segment
  have G : ∀ n, n ≤ xs.length → tr[c0 + n]? = some (S n) ∧
      M.Inv (t.ghostAt p xs ys n) (S n) := by
    intro n
    induction n with
    | zero =>
      intro _
      have hg0 : t.ghostAt p xs ys 0 = t.ginit p := by simp [ReactTask.ghostAt]
      rw [hg0]
      exact ⟨base.1, base.2.1⟩
    | succ n ih =>
      intro hn
      have hxn : n < xs.length := by omega
      obtain ⟨hprev, hinv⟩ := ih (by omega)
      obtain ⟨h1, h2⟩ := one n hxn hprev
      refine ⟨h1, ?_⟩
      rw [ghostAt_succ t p xs ys n hxn (by omega), hyn n (by omega)]
      exact (h2 _ hinv).1
  have hxs : ∀ {j x}, xs[j]? = some x → ∃ hj : j < xs.length, x = xs[j] := by
    intro j x hx
    have hj : j < xs.length := (List.getElem?_eq_some_iff.mp hx).1
    exact ⟨hj, (Option.some.inj ((List.getElem?_eq_getElem hj).symm.trans hx)).symm⟩
  have hys : ∀ {j y}, ys[j]? = some y → j < xs.length ∧ y = M.out (S (j + 1)) := by
    intro j y hy
    have hj : j < ys.length := (List.getElem?_eq_some_iff.mp hy).1
    refine ⟨by omega, ?_⟩
    rw [List.getElem?_eq_getElem hj, hyn j hj] at hy
    exact (Option.some.inj hy).symm
  refine ⟨M.out (S 0), ys, hyl, fun j y hy => ?_, base.2.2, fun j x y hx hy => ?_, ?_⟩
  · -- the outputs shown
    have hj : j ≤ xs.length := by
      have := (List.getElem?_eq_some_iff.mp hy).1
      simp only [List.length_cons] at this
      omega
    obtain ⟨h1, hinv⟩ := G j hj
    refine ⟨S j, h1, ?_⟩
    have hyS : y = M.out (S j) := by
      cases j with
      | zero =>
        rw [List.getElem?_cons_zero] at hy
        exact (Option.some.inj hy).symm
      | succ j =>
        rw [List.getElem?_cons_succ] at hy
        exact (hys hy).2
    rw [hyS]
    exact M.shows _ _ hinv
  · -- safety
    obtain ⟨hj, rfl⟩ := hxs hx
    obtain ⟨-, rfl⟩ := hys hy
    obtain ⟨hprev, hinv⟩ := G j (by omega)
    exact ((one j hj hprev).2 _ hinv).2.1
  · -- bounded response
    refine responds_of_rank t hyl (fun o j => M.rank o (S j))
      (fun o j hj => M.rank_le o _ _ (G j hj).2) ?_
    intro o j x y hx hy htr
    obtain ⟨hj, rfl⟩ := hxs hx
    obtain ⟨-, rfl⟩ := hys hy
    obtain ⟨hprev, hinv⟩ := G j (by omega)
    exact ((one j hj hprev).2 _ hinv).2.2 o htr

/-- **The reactive reduction**: a design satisfies the `ReactTask` statement at `p` and `K` as soon
as, besides the interface, the clock discipline, termination from every power-up and rule 3, it has
a rank model whose shape every power-up state has (`hpu`). -/
theorem satisfiedAt_of_rank {p : P} {K : Nat} {d : Design2} (hI : t.Interface p d)
    (hD : t.Disciplined d) (hT : TerminatesPU d) (M : t.RankModel p K d)
    (hpu : ∀ st, PowerUp d st → M.Shape st) (hx : XSafe d) : t.SatisfiedAt p K d :=
  ⟨hI, ⟨hD, hT⟩, fun st0 h0 _ _ _ _ hr => t.claim_of_rank M (hpu st0 h0) hr.runFrom, hx⟩

/-- **Every snapshot of the statement's runs is known** (what v1's known-state clause `KnownAt`
asked, here a theorem): for a design that satisfies the statement, every snapshot of every run
from every power-up state on every known stimulus binds only known values of their declared widths
(`KnownState`), by rule 3 and txtask-v2's x-free lemma `xfree_runsAt`. -/
theorem snapshots_known {p : P} {K : Nat} {d : Design2} (h : t.SatisfiedAt p K d) :
    ∀ st0, PowerUp d st0 → ∀ (σ : ScheduleOracle) (stim tr : List SvState), KnownStim d stim →
      RunsAt d σ st0 stim tr → ∀ s ∈ tr, KnownState d s :=
  fun _ h0 _ _ _ hs hr => xfree_runsAt h.2.2.2 h0 hs hr

end ReactTask

/-- **A design whose comb processes write no output is Moore**: `S` = the input ports and every
target of a comb-phase process (closed under the comb processes by construction). -/
theorem mooreOut_of_combTargets {d : Design2}
    (hio : ∀ o ∈ d.outputNames.toList, o ∉ d.inputNames.toList)
    (hc : ∀ p ∈ d.processes.toList, p.isCombPhase = true →
      ∀ m ∈ processTargets p, m ∉ d.outputNames.toList) :
    MooreOut d :=
  ⟨fun n => n ∈ d.inputNames.toList ∨
      ∃ p ∈ d.processes.toList, p.isCombPhase = true ∧ n ∈ processTargets p,
    fun n hn => .inl hn,
    fun p hp hcp _ m hm => .inr ⟨p, hp, hcp, hm⟩,
    fun o ho hS => by
      rcases hS with h | ⟨p, hp, hcp, hm⟩
      · exact hio o ho h
      · exact hc p hp hcp o hm ho⟩

#print axioms ReactTask.claim_of_rank
#print axioms ReactTask.satisfiedAt_of_rank
#print axioms ReactTask.snapshots_known
#print axioms mooreOut_of_combTargets

end SvGolf
