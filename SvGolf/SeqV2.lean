import SvGolf.TaskSeq
import SvGolf.Seq
import SvGolf.XFree

/-!
# Proof helpers for the txtask-v2 statements (untrusted, kernel-checked)

Nothing here is part of the trusted base. It goes with the txtask-v2 section of
`SvGolf/TaskSeq.lean` (`ModelsPU`, `TerminatesPU`, `MooreOutDep`, `XSafe`, the `StatementV2`s). It
imports the v1 helpers (`SvGolf.Seq`) and the x-free lemma (`SvGolf.XFree`), so a reference proof of
a v2 statement imports this module alone.

* Rule 2, every power-up:
  * `RunsAt.runFrom`: a run from a power-up state is a `RunFrom`, which the v1 reductions now take
    (`SeqTask.claim_of_cycle`, `TxTask.guar_of_phases`, `StreamTask.guar_of_phases`), so one proof
    of the claim serves the x start and every power-up;
  * `TerminatesPU.of_invariant`: termination from every power-up from a cycle invariant that every
    power-up state has (v1's `Terminates2.of_invariant`, with the start quantified);
  * `powerUp_cons`, `powerUp_nil`: a power-up state of a declaration list, one declaration at a
    time (how a reference shows that every power-up state has its shape);
  * `knownVecs`, `powerUps`, `mem_powerUps`: the power-up states of a design, enumerated (finite
    widths), for bounded checks of a concrete design;
  * **`SeqTask.satisfiedAtV2_of_cycle`**, **`TxTask.satisfiedAtV2_of_phases`**,
    **`StreamTask.satisfiedAtV2_of_phases`**: the v2 statement at one parameter value from the v1
    reduction's data, with the shape (the invariant) holding at every power-up state in place of
    `initState2`, and the two structural rules.
* Rule 1: `MooreOutDep.of_noComb` (a design without combinational dependencies, the FF-only
  profile of every clocked reference today), the checker `mooreOutDepB` with its soundness
  `MooreOutDep.of_check`, and `combDeps_of_ffOnly`.
* Rule 3: `XSafe` is decided (`xsafeB`); the x-free lemma is `SvGolf.XFree`.
-/

namespace SvGolf

open LeanModels.Sv

/-! ## Rule 1: designs without combinational assignments, and a checker -/

/-- `MooreOutDep` of a design with no combinational dependency (the FF-only profile of every
clocked reference today): nothing but distinct input and output names, which `Interface` gives. -/
theorem MooreOutDep.of_noComb {d : Design2} {ex : List String} (hc : combDeps d = [])
    (hio : ∀ o ∈ d.outputNames.toList, o ∉ d.inputNames.toList) : MooreOutDep d ex :=
  ⟨fun n => n ∈ d.inputNames.toList, fun _ hn _ => hn,
    fun e he => by simp [hc] at he,
    fun o ho h => hio o ho h⟩

/-- One closure step: add every signal an edge writes whose dependencies meet `S`. -/
def depStep (edges : List DepEdge) (S : List String) : List String :=
  S ++ (edges.filter fun e => e.2.any fun r => S.contains r).map Prod.fst

/-- `n` closure steps. -/
def depClosure (edges : List DepEdge) (S : List String) : Nat → List String
  | 0 => S
  | n + 1 => depClosure edges (depStep edges S) n

/-- The signals a non-exempt input reaches through the combinational dependencies (enough steps:
every step that adds a signal adds an edge's target, and there are `(combDeps d).length` edges). -/
def mooreSet (d : Design2) (ex : List String) : List String :=
  depClosure (combDeps d) (d.inputNames.toList.filter fun n => !ex.contains n)
    ((combDeps d).length + 1)

/-- **A checker for rule 1**: `mooreSet` is closed along every dependency and holds no output. -/
def mooreOutDepB (d : Design2) (ex : List String) : Bool :=
  (combDeps d).all (fun e => !(e.2.any fun r => (mooreSet d ex).contains r) ||
      (mooreSet d ex).contains e.1) &&
    d.outputNames.toList.all fun o => !(mooreSet d ex).contains o

theorem mem_depClosure (edges : List DepEdge) : ∀ (n : Nat) {S : List String} {x : String},
    x ∈ S → x ∈ depClosure edges S n
  | 0, _, _, h => h
  | n + 1, _, _, h => by
      simp only [depClosure]
      exact mem_depClosure edges n (List.mem_append_left _ h)

/-- The checker is sound. -/
theorem MooreOutDep.of_check {d : Design2} {ex : List String} (h : mooreOutDepB d ex = true) :
    MooreOutDep d ex := by
  simp only [mooreOutDepB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hcl, hout⟩ := h
  refine ⟨fun n => n ∈ mooreSet d ex, fun n hn hex => ?_, fun e he hr => ?_,
    fun o ho hS => ?_⟩
  · exact mem_depClosure _ _ (List.mem_filter.mpr ⟨hn, by simpa using hex⟩)
  · obtain ⟨r, hr1, hr2⟩ := hr
    have h1 := hcl e he
    have h2 : (e.2.any fun r => (mooreSet d ex).contains r) = true :=
      List.any_eq_true.mpr ⟨r, hr1, List.contains_iff_mem.mpr hr2⟩
    rw [h2] at h1
    have h3 : (mooreSet d ex).contains e.1 = true := by simpa using h1
    exact List.contains_iff_mem.mp h3
  · have h1 := hout o ho
    rw [List.contains_iff_mem.mpr hS] at h1
    simp at h1

/-- **An FF-only design has no combinational dependency**: every process is an edge process, and
`processDeps` of an edge process is empty. -/
theorem combDeps_of_ffOnly {d : Design2} (h : FFOnly d) : combDeps d = [] := by
  unfold combDeps
  refine List.flatMap_eq_nil_iff.mpr fun p hp => ?_
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
  obtain ⟨c, b, hpb, -⟩ := h.procs i p (by simpa using hi)
  rcases hpb with rfl | rfl <;> rfl

/-- A stimulus entry `c` that binds `n` to `b` is the entry the run reads at `c`. -/
theorem StimBit.bitIs {stim : List SvState} {c : Nat} {n : String} {b : Bool} {e : SvState}
    (h : StimBit stim c n b) (he : stim[c]? = some e) : BitIs e n b := by
  obtain ⟨e', he', hb⟩ := h
  rw [he, Option.some.injEq] at he'
  subst he'
  exact hb

/-! ## Rule 2: runs from every power-up -/

/-- A run from a start state (`RunsAt`) is a `RunFrom`. -/
theorem RunsAt.runFrom {d : Design2} {σ : ScheduleOracle} {st0 : SvState}
    {stim tr : List SvState} (h : RunsAt d σ st0 stim tr) : RunFrom d σ st0 stim tr :=
  let ⟨fuel, hr⟩ := h; ⟨fuel, runFrom2_of_run2At hr⟩

/-- **`TerminatesPU` from a cycle invariant** that every power-up state has: if, for each schedule,
some fuel makes every `cycleStep2` from an `I`-state succeed into `I`, every run from every power-up
completes (v1's `Terminates2.of_invariant`, with the start quantified). -/
theorem TerminatesPU.of_invariant {d : Design2} (I : SvState → Prop)
    (hpu : ∀ st, PowerUp d st → I st)
    (hstep : ∀ σ : ScheduleOracle, ∃ F, ∀ (inputs st : SvState) (k : Nat), I st →
      ∃ st' k', cycleStep2 d σ F inputs st k = .ok (st', k') ∧ I st')
    (hnoq : d.processes.toList.any Process2.hasQualifiedCase = false) : TerminatesPU d := by
  intro st0 hst0 σ stim _
  obtain ⟨F, hF⟩ := hstep σ
  obtain ⟨tr, hraw, -⟩ := runFrom2_ok_of_invariant I hF stim st0 0 (hpu st0 hst0)
  exact ⟨tr, F, by simp [run2At, hraw, hnoq]⟩

/-- A power-up state of a declaration list `dc :: ds`, its first binding taken off. -/
theorem powerUp_cons {st : SvState} {dc : Decl} {ds : List Decl} :
    (st.map Prod.fst = (dc :: ds).map Decl.name ∧
      ∀ b ∈ st.zip (dc :: ds), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true) ↔
    ∃ v rest, st = (dc.name, v) :: rest ∧ v.width = dc.width ∧ v.allKnown = true ∧
      (rest.map Prod.fst = ds.map Decl.name ∧
        ∀ b ∈ rest.zip ds, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true) := by
  constructor
  · rintro ⟨hm, hz⟩
    cases st with
    | nil => simp at hm
    | cons b rest =>
        obtain ⟨n, v⟩ := b
        simp only [List.map_cons, List.cons.injEq] at hm
        obtain ⟨rfl, hm⟩ := hm
        have hb := hz ((dc.name, v), dc) (by simp)
        exact ⟨v, rest, rfl, hb.1, hb.2, hm, fun b hb' => hz b (by simp [hb'])⟩
  · rintro ⟨v, rest, rfl, hw, hk, hm, hz⟩
    refine ⟨by simp [hm], fun b hb => ?_⟩
    simp only [List.zip_cons_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨hw, hk⟩
    · exact hz b hb

/-- A power-up state of the empty declaration list is the empty state. -/
theorem powerUp_nil {st : SvState} :
    (st.map Prod.fst = ([] : List Decl).map Decl.name ∧
      ∀ b ∈ st.zip ([] : List Decl), b.1.2.width = b.2.width ∧ b.1.2.allKnown = true) ↔
    st = [] := by
  constructor
  · rintro ⟨hm, -⟩; simpa using hm
  · rintro rfl; simp

/-! ### The power-up states of a concrete design, enumerated -/

/-- Every known vector of width `w`. -/
def knownVecs (w : Nat) : List LVec := (List.range (2 ^ w)).map (LVec.ofNat w)

theorem mem_knownVecs {v : LVec} (hk : v.allKnown = true) : v ∈ knownVecs v.width := by
  have e := LVec.eq_ofBoolFn_of_allKnown hk
  rw [LVec.ofBoolFn_eq_ofNat] at e
  exact List.mem_map.mpr ⟨_, List.mem_range.mpr (XF.val_lt _ _), e.symm⟩

/-- Every power-up state of a declaration list. -/
def powerUpsOf : List Decl → List SvState
  | [] => [[]]
  | dc :: ds => (knownVecs dc.width).flatMap fun v => (powerUpsOf ds).map fun rest => (dc.name, v) :: rest

/-- Every power-up state of `d` (finitely many: `2 ^ (sum of the declared widths)`). -/
def powerUps (d : Design2) : List SvState := powerUpsOf d.decls.toList

theorem mem_powerUpsOf : ∀ (ds : List Decl) (st : SvState),
    (st.map Prod.fst = ds.map Decl.name ∧
      ∀ b ∈ st.zip ds, b.1.2.width = b.2.width ∧ b.1.2.allKnown = true) → st ∈ powerUpsOf ds
  | [], st, h => by rw [powerUp_nil.mp h]; simp [powerUpsOf]
  | dc :: ds, st, h => by
      obtain ⟨v, rest, rfl, hw, hk, h'⟩ := powerUp_cons.mp h
      simp only [powerUpsOf, List.mem_flatMap, List.mem_map]
      exact ⟨v, hw ▸ mem_knownVecs hk, rest, mem_powerUpsOf ds rest h', rfl⟩

/-- **Every power-up state is enumerated** by `powerUps`. -/
theorem mem_powerUps {d : Design2} {st : SvState} (h : PowerUp d st) : st ∈ powerUps d :=
  mem_powerUpsOf d.decls.toList st h

/-! ## The v2 statements from the v1 reductions -/

/-- **The v2 statement of a `SeqTask` with a reset port** from the data of v1's
`SeqTask.satisfiedAt_of_cycle`, with the invariant holding at every power-up state (`hpu`) in place
of `initState2`, termination from every power-up, and the two structural rules. -/
theorem SeqTask.satisfiedAtV2_of_cycle (t : SeqTask) (N : Nat) (d : Design2)
    (hrst : ∃ r, t.rst = some r)
    (hI : t.Interface N d) (hD : t.Disciplined d) (hT : TerminatesPU d)
    (Inv : SvState → Prop) (R : SvState → t.State N → Prop)
    (hpu : ∀ st, PowerUp d st → Inv st)
    (hinv : ∀ σ F inputs prev k st k', Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → Inv st)
    (hreset : ∀ σ F inputs prev k st k' (v : t.Ins N), Inv prev →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (true, v) →
        R st (t.init N) ∧ t.ObsOK N st (t.init N, v))
    (hstep : ∀ σ F inputs prev k st k' (s : t.State N) (v : t.Ins N), Inv prev → R prev s →
        cycleStep2 d σ F inputs prev k = .ok (st, k') → t.Drives N inputs (false, v) →
        R st (t.step N s v) ∧ t.ObsOK N st (t.step N s v, v))
    (hm : MooreOutDep d []) (hx : XSafe d) :
    t.SatisfiedAtV2 N d :=
  ⟨hI, ⟨hD, hT⟩, fun st0 h0 _ _ _ _ hr =>
    t.claim_of_cycle N d hrst Inv R hinv hreset hstep (hpu st0 h0) hr.runFrom, hm, hx⟩

/-- **The v2 statement of a `TxTask`** from v1's phase model, its shape holding at every power-up
state (`hpu`), termination from every power-up, and the two structural rules. -/
theorem TxTask.satisfiedAtV2_of_phases {P : Type} (t : TxTask P) {p : P} {lat : Nat} {d : Design2}
    (hI : t.Interface p d) (hD : t.Disciplined d) (hT : TerminatesPU d) (hlat : 1 ≤ lat)
    (M : t.PhaseModel p lat d) (hpu : ∀ st, PowerUp d st → M.Shape st)
    (hm : MooreOutDep d []) (hx : XSafe d) : t.SatisfiedAtV2 p lat d :=
  ⟨hI, ⟨hD, hT⟩, hlat, fun st0 h0 _ _ _ _ hr => t.guar_of_phases M (hpu st0 h0) hr.runFrom, hm, hx⟩

/-- **The v2 statement of a `StreamTask`** from v1's phase model, its shape holding at every
power-up state (`hpu`), termination from every power-up, and the two structural rules. -/
theorem StreamTask.satisfiedAtV2_of_phases {P : Type} (t : StreamTask P) {p : P} {lat : Nat}
    {d : Design2} (hI : t.Interface p d) (hD : t.Disciplined d) (hT : TerminatesPU d)
    (hcount : 1 ≤ t.count p) (hle : t.count p ≤ lat)
    (hlen : ∀ xs, xs.length = t.count p → (t.spec p xs).length = t.count p)
    (M : t.PhaseModel p lat d) (hpu : ∀ st, PowerUp d st → M.Shape st)
    (hm : MooreOutDep d []) (hx : XSafe d) : t.SatisfiedAtV2 p lat d :=
  ⟨hI, ⟨hD, hT⟩, by omega, fun st0 h0 _ _ _ _ hr =>
    t.guar_of_phases hcount hle hlen M (hpu st0 h0) hr.runFrom, hm, hx⟩

#print axioms MooreOutDep.of_noComb
#print axioms MooreOutDep.of_check
#print axioms combDeps_of_ffOnly
#print axioms TerminatesPU.of_invariant
#print axioms mem_powerUps
#print axioms SeqTask.satisfiedAtV2_of_cycle
#print axioms TxTask.satisfiedAtV2_of_phases
#print axioms StreamTask.satisfiedAtV2_of_phases

end SvGolf
