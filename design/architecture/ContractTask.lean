import TaskV2
import LeanModels.Sv.ContractFA
import LeanModels.Sv.ObserveRedrive

/-!
# Contracts refine the Task v2 statement (D11 → `SatAt`)

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status.** §1 and §2 are a **transport theorem**: generic over the backend (`M : ObservationModel`),
nothing about `run2`. §3, the full adder, is **provisional over `run2`**. It goes through `Obs_run2`,
not `Obs_E0`.

## §1 `Contract.Refines` and `Contract.satAt_of_sat`

A contract (`Contract.lean`) is a proof device, a D view; the trusted statement is Task v2's
`SatAt`/`Sat` (`TaskV2.lean`). `C.Refines S p` is the link between them, and it is **design-free**:
same ports, clocking and free inputs, the free inputs distinct, and, on ANY observation sequence,
`C.Holds` implies the task's guarantee on every prefix where the task's rely holds. It is proved
once per (contract, task) pair, never per design or per backend. `satAt_of_sat` then turns
`C.Sat M d` into `SatAt M Adm S p d` for every backend `M`, given the backend's admission `Adm d`.
The two receptiveness forms (the contract's `Valuation`, the task's `Vals`) are bridged by
`valOfVals`.

## §2 The canonical contract of a `CombTask`

`t.contract N`: no clock, every input free, no ghost state, no rely; the guarantee is the task's own
per-cycle claim (inputs on pre, outputs on post); arcs from every input port to every output port
(whole-port windows, the conservative default); direction `overApprox`. `contract_refines` proves it
refines `t.toSpec ty` at `N` for every `CombTask`, so `Sat` of that contract over any backend gives
`SatisfiedAt_obs` there.

## §3 The full adder through it

`faTask` is a combinational task for `Comb2Smoke.faDesign` (ports `a b ci` → `s co y`, with
`y = {co, s}`). `fa_contract_sat` proves its canonical contract over `Obs_run2`, and `fa_statement_obs`
gives `faTask.Statement_obs` through `satAt_of_sat`. The `run2` facts it uses are library pieces:
progress (`Obs_run2.progress_of_terminates`, from `fa_terminates`) and receptiveness
(`Contract.receptive_of_writesInput`); for the claim, `Obs_run2.read_sample`,
`Obs_run2.comb_samples` (`ContractFA.lean`) and `Obs_run2.comb_post_input` below (a comb-profile
design's post sample has the pre sample's inputs), with the design's own `fa_comb` and
`fa_settled`.
-/

namespace LeanModels.Sv.Observe.Contract

open SvGolf SvGolf.Arch

/-! ## §1 Refinement into the Task v2 statement -/

/-- The valuation giving each port of `free` its value in `v` (the first occurrence wins), and `0`
elsewhere. -/
def valOfVals : (free : List Sig) → Vals (free.map Prod.snd) → Valuation
  | [], _ => fun _ => 0
  | (n, w) :: rest, v => fun p =>
      if h : p.1 = n ∧ p.2 = w then cast (congrArg BitVec h.2.symm) v.1 else valOfVals rest v.2 p

theorem holdAllS_of_holdsOn {s : PortSample} :
    ∀ {free : List Sig} (v : Vals (free.map Prod.snd)), free.Nodup →
      HoldsOn s free (valOfVals free v) → HoldAllS s free v
  | [], _, _, _ => trivial
  | (n, w) :: rest, v, hnd, h => by
      rw [List.nodup_cons] at hnd
      refine ⟨?_, holdAllS_of_holdsOn v.2 hnd.2 fun p hp => ?_⟩
      · simpa [valOfVals] using h (n, w) (by simp)
      · have hne : ¬(p.1 = n ∧ p.2 = w) := fun he =>
          hnd.1 (by rw [show p = (n, w) from Prod.ext he.1 he.2] at hp; exact hp)
        simpa [valOfVals, hne] using h p (List.mem_cons_of_mem _ hp)

/-- **`C` refines the task `S` at `p`** (design-free): the same ports, clocking and free inputs, the
free inputs distinct, and on every observation sequence, the contract holding gives the task's
guarantee on every prefix where the task's rely holds. -/
structure Refines {P : Type} (C : Contract) (S : Spec P) (p : P) : Prop where
  iface : C.iface = S.iface p
  clocking : C.clocking = S.clocking
  free : C.free = S.free p
  nodup : (S.free p).Nodup
  holds : ∀ b, C.Holds b → ∀ n, S.rely p (b.take n) → S.guar p (b.take n)

/-- **A satisfied contract that refines a task gives the task's statement**, over any backend `M`
whose admission check `Adm` the design passes. -/
theorem satAt_of_sat {P : Type} {C : Contract} {S : Spec P} {p : P} {M : ObservationModel}
    {Adm : M.Design → Prop} {d : M.Design} (hr : C.Refines S p) (hadm : Adm d) (h : C.Sat M d) :
    SatAt M Adm S p d := by
  have hk := hr.clocking
  refine ⟨h.iface.trans hr.iface, ⟨hadm, by rw [← hk]; exact h.realizable, ?_⟩, ?_⟩
  · intro ch s
    obtain ⟨env, b, hd, hb, hlen, hh⟩ := h.receptive ch (s.map (valOfVals (S.free p)))
    refine ⟨env, b, hk ▸ hd, hb, by simpa using hlen, fun c o v hc hv => ?_⟩
    have := hh c o (valOfVals (S.free p) v) hc (by simp [hv])
    rw [hr.free] at this
    exact holdAllS_of_holdsOn v hr.nodup this
  · intro ch env b hd hb
    exact hr.holds b (h.safe ch env b (hk ▸ hd) hb)

/-- **The family form**: contracts `C p` that refine `S` at every covered `p` and are satisfied there
give `Sat`. -/
theorem sat_of_sat {P : Type} {C : P → Contract} {S : Spec P} {M : ObservationModel}
    {Adm : M.Design → Prop} {sem : P → M.Design}
    (hr : ∀ p, S.inRange p → S.inType p → (C p).Refines S p)
    (hadm : ∀ p, S.inRange p → S.inType p → Adm (sem p))
    (h : ∀ p, S.inRange p → S.inType p → (C p).Sat M (sem p)) : SvGolf.Arch.Sat M Adm S sem :=
  fun p hi ht => satAt_of_sat (hr p hi ht) (hadm p hi ht) (h p hi ht)

theorem ghosts_length (C : Contract) :
    ∀ (g : C.Ghost) (b : List (CycleObs PortSample)), (C.ghosts g b).length = b.length
  | _, [] => rfl
  | g, _ :: os => by simp [ghosts, ghosts_length C _ os]

end LeanModels.Sv.Observe.Contract

/-! ## §2 The canonical contract of a combinational task -/

namespace SvGolf.CombTask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf.Arch

variable (t : CombTask)

/-- **The canonical contract of a combinational task** at `N`: the task's own per-cycle claim as
the guarantee, nothing assumed. -/
def contract (N : Nat) : Contract where
  iface := ⟨t.inputs N, t.outputs N⟩
  clocking := {}
  free := t.inputs N
  Ghost := Unit
  ginit := ()
  gnext _ _ := ()
  rely _ _ := True
  guar _ o := ∀ v, HoldAllS o.pre (t.inputs N) v → HoldAllS o.post (t.outputs N) (t.fn N v)
  arcs := (t.inputs N).flatMap fun i => (t.outputs N).map fun o => ⟨(i.1, 0, i.2), (o.1, 0, o.2)⟩
  dir := .overApprox

/-- **The canonical contract refines the task**, for every `CombTask` with distinct input ports. -/
theorem contract_refines (ty : Nat → Prop) (N : Nat) (hnd : (t.inputs N).Nodup) :
    (t.contract N).Refines (t.toSpec ty) N where
  iface := rfl
  clocking := rfl
  free := rfl
  nodup := hnd
  holds b h n _ := by
    intro c o hc v hv
    have hb := getElem?_of_take hc
    obtain ⟨g, hg⟩ : ∃ g, ((t.contract N).ghosts (t.contract N).ginit b)[c]? = some g :=
      ⟨_, List.getElem?_eq_getElem
        (by rw [Contract.ghosts_length]; exact (List.getElem?_eq_some_iff.mp hb).1)⟩
    exact h c (fun _ _ _ _ _ _ => trivial) g o hg hb v hv

end SvGolf.CombTask

/-! ## §3 The full adder (provisional over `run2`) -/

namespace LeanModels.Sv.Observe

/-- **A comb design's post sample has the pre sample's inputs** (`run2`): the edge part of a comb
design is one more settle, which writes no input. -/
theorem Obs_run2.comb_post_input {d : Design2} (hd : CombDesign d) {σ : ScheduleOracle}
    {stim : List SvState} {r : List (CycleObs SvState)} (hr : Obs_run2.Runs d σ stim r) {c : Nat}
    {o : CycleObs SvState} (ho : r[c]? = some o) {n : String} (hn : n ∈ d.inputNames.toList) :
    SvState.lookup o.post n = SvState.lookup o.pre n := by
  obtain ⟨fuel, hrun⟩ := hr
  obtain ⟨inputs, prev, kc, kc', -, -, hcyc⟩ := runFromObs2_cycle hrun ho
  obtain ⟨_, _, _, _, _, _, _, hpost⟩ := pre_sample_spec hcyc
  unfold cyclePost2 at hpost
  rw [hd.edgeIndices_eq, σ.choose_nil] at hpost
  simp only [edgePass2, Res.ok_bind] at hpost
  have hc : commitNba2 o.pre [] = o.pre := rfl
  rw [hc] at hpost
  exact combSettle2_lookup (fun p hp => Design2.writesName_of_writesInput
    (CombDesign.writesInput_eq_false hd) hp hn) _ _ _ _ _ hpost

end LeanModels.Sv.Observe

namespace SvGolf.Arch.ContractFATask

open LeanModels.Sv LeanModels.Sv.Observe SvGolf SvGolf.Arch Comb2Smoke Comb2Example

/-- The full adder as a combinational task (no parameter: the range is `N = 1`). -/
def faTask : CombTask where
  inRange N := N = 1
  inputs _ := [("a", 1), ("b", 1), ("ci", 1)]
  outputs _ := [("s", 1), ("co", 1), ("y", 2)]
  fn _ := fun (x, y, z, ()) =>
    (x ^^^ y ^^^ z, x &&& y ||| x &&& z ||| y &&& z,
      (x &&& y ||| x &&& z ||| y &&& z) ++ (x ^^^ y ^^^ z), ())

/-- **The full adder satisfies the task's canonical contract over `Obs_run2`.** -/
theorem fa_contract_sat : (faTask.contract 1).Sat Obs_run2 faDesign where
  iface := by decide
  realizable := Obs_run2.progress_of_terminates _ _ fa_terminates
  receptive := (faTask.contract 1).receptive_of_writesInput (by decide) fa_terminates (by decide)
    (by decide)
  safe := by
    rintro σ stim b - ⟨r, hr, rfl⟩ c - g o - ho
    rw [List.getElem?_map] at ho
    cases hrc : r[c]? with
    | none => rw [hrc] at ho; cases ho
    | some o' =>
        rw [hrc] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        rintro ⟨x, y, z, ⟨⟩⟩ ⟨ha, hb, hc, -⟩
        have hrd : ∀ st, ∀ n ∈ ["a", "b", "ci", "s", "co", "y"],
            (Obs_run2.sample faDesign st).read n = SvState.lookup st n :=
          fun _ n hn => Obs_run2.read_sample (by revert n; decide)
        have hin : ∀ n ∈ ["a", "b", "ci"], SvState.lookup o'.post n = SvState.lookup o'.pre n :=
          fun n hn => Obs_run2.comb_post_input fa_comb hr hrc (by revert n; decide)
        simp only [CycleObs.map_pre, CycleObs.map_post] at ha hb hc ⊢
        rw [hrd _ "a" (by simp), ← hin "a" (by simp)] at ha
        rw [hrd _ "b" (by simp), ← hin "b" (by simp)] at hb
        rw [hrd _ "ci" (by simp), ← hin "ci" (by simp)] at hc
        obtain ⟨-, ⟨he2, hs2⟩⟩ := Obs_run2.comb_samples fa_comb hr hrc
        obtain ⟨hS, hCO, hY⟩ := fa_settled he2 hs2 ha hb hc
        exact ⟨(hrd _ "s" (by simp)).trans hS, (hrd _ "co" (by simp)).trans hCO,
          (hrd _ "y" (by simp)).trans hY, trivial⟩

/-- **The full adder's Task v2 statement**, through the contract: `satAt_of_sat` with the generic
`contract_refines`. Provisional over `run2`. -/
theorem fa_statement_obs (ty : Nat → Prop) :
    faTask.Statement_obs ty Obs_run2 Unclocked (fun _ => faDesign) := by
  rintro N rfl -
  exact faTask.satisfiedAt_obs_iff_satAt.mpr
    (Contract.satAt_of_sat (faTask.contract_refines ty 1 (by decide)) (by decide) fa_contract_sat)

end SvGolf.Arch.ContractFATask

#print axioms LeanModels.Sv.Observe.Contract.holdAllS_of_holdsOn
#print axioms LeanModels.Sv.Observe.Contract.satAt_of_sat
#print axioms LeanModels.Sv.Observe.Contract.sat_of_sat
#print axioms SvGolf.CombTask.contract_refines
#print axioms LeanModels.Sv.Observe.Obs_run2.comb_post_input
#print axioms SvGolf.Arch.ContractFATask.fa_contract_sat
#print axioms SvGolf.Arch.ContractFATask.fa_statement_obs
