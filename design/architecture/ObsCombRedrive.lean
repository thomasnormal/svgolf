import ObsComb
import LeanModels.Sv.ObserveRedrive
import LeanModels.Sv.Comb2Proc

/-!
# v1 ⇒ inputs read from the pre sample, over `run2`, for assign-only designs

Not in any lake library and imported by nothing trusted. Compile with `compile-obs.sh`.

**Status: provisional over `run2`.** This closes the direction `ObsComb.lean` recorded as missing,
the one the records need: v1's `Computes` (inputs bound by the stimulus entry) implies
`Computes_obs` (inputs read from the PRE sample, the trusted convention of `TaskV2.lean`). It holds
for comb-profile (assign-only) designs (`CombDesign`), over `run2`, with no typed-stimulus
restriction.

**The argument** (agent A's re-driving, `LeanModels/Sv/ObserveRedrive.lean`). Take a run, and a
cycle whose pre sample holds known inputs `v`, possibly held from earlier entries. Re-drive every
entry to its pre sample's inputs. That stimulus has the SAME run (`runObs2_redrive`), and its entry
for the cycle binds exactly `v`, so v1 applies there and gives `fn v` on the post sample.

## What is here

* `computes_obs_of_computes`: v1 ⇒ trusted convention (comb-profile designs, under `Interface`).
* `computes_iff_computes_obs`: with `computes_of_computes_obs'` (the other direction, from
  `writesInput = false`), the two conventions agree on comb-profile designs.
* `satisfiedAt_obs_of_satisfiedAt` and `statement_obs_of_statement`: a v1 record whose design is in
  the comb profile and writes no input moves to the full trusted statement (`TaskV2.lean`'s
  `CombTask.SatisfiedAt_obs`, receptiveness included) by these theorems, without being re-proved.
  The side conditions per parameter value are `CombDesign` (which the comb tactic route already
  proves), `writesInput = false` (by `rfl` or `decide`), and distinct input names (by `decide`).
-/

namespace SvGolf.Arch

open LeanModels.Sv LeanModels.Sv.Observe SvGolf

/-- Under `Interface`, every task input is an input of the design. -/
theorem inputs_mem_of_interface {t : CombTask} {N : Nat} {d : Design2} (hI : t.Interface N d) :
    ∀ p ∈ t.inputs N, p.1 ∈ d.inputNames.toList := by
  intro p hp
  rw [← inputPorts_map_fst, hI.1]
  exact List.mem_map_of_mem hp

/-- **v1 ⇒ inputs read from the pre sample** (comb-profile designs, over `run2`). -/
theorem computes_obs_of_computes {t : CombTask} {N : Nat} {d : Design2} (hd : CombDesign d)
    (hI : t.Interface N d) (h : t.Computes N d) : t.Computes_obs Obs_run2 N d := by
  intro σ stim b _ hb c o hc v hv
  obtain ⟨r, ⟨F, hrun⟩, rfl⟩ := hb
  obtain ⟨o', hrc, rfl⟩ := obs_run2_cycle hc
  have hruns : Runs2 d σ (r.map fun o => redriveEntry d o.pre) (r.map CycleObs.post) :=
    ⟨F, (run2_ok_iff (CombDesign.noQualified hd)).mpr ⟨r, runObs2_redrive hd hrun, rfl⟩⟩
  have he : (r.map fun o => redriveEntry d o.pre)[c]? = some (redriveEntry d o'.pre) := by
    simp [hrc]
  have htr : (r.map CycleObs.post)[c]? = some o'.post := by simp [hrc]
  have hinp := inputs_mem_of_interface hI
  have hpre : HoldAll o'.pre (t.inputs N) v :=
    (holdAllS_sample _ _ fun p hp => mem_names_of_inputName (hinp p hp)).mp hv
  have hent : HoldAll (redriveEntry d o'.pre) (t.inputs N) v :=
    hpre.transfer fun n hn val hval => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
      rw [lookup_redriveEntry, if_pos (hinp p hp)]
      exact hval
  exact (holdAllS_sample _ _ (outputs_mem_of_interface hI)).mpr
    (h σ _ _ hruns c _ _ he htr v hent)

/-- **The two input conventions agree on comb-profile designs** that write no input. -/
theorem computes_iff_computes_obs {t : CombTask} {N : Nat} {d : Design2} (hd : CombDesign d)
    (hw : d.writesInput = false) (hI : t.Interface N d) :
    t.Computes N d ↔ t.Computes_obs Obs_run2 N d :=
  ⟨computes_obs_of_computes hd hI, computes_of_computes_obs' hw hI⟩

/-- **A v1 record moves to the trusted statement** (comb-profile designs, over `run2`): v1's
`SatisfiedAt` gives `CombTask.SatisfiedAt_obs`, receptiveness included. -/
theorem satisfiedAt_obs_of_satisfiedAt {t : CombTask} {N : Nat} {d : Design2} (hd : CombDesign d)
    (hw : d.writesInput = false) (hnd : ((t.inputs N).map Prod.fst).Nodup)
    (h : t.SatisfiedAt N d) : t.SatisfiedAt_obs Obs_run2 Unclocked N d := by
  obtain ⟨hI, ⟨hU, hT⟩, hC⟩ := h
  exact ⟨hI, ⟨hU, Obs_run2.progress_of_terminates _ _ hT,
    receptive_of_writesInput hw hT (inputs_mem_of_interface hI) hnd⟩,
    computes_obs_of_computes hd hI hC⟩

/-- **Every v1 record whose designs are in the comb profile holds in the trusted statement**, for any
declared-type range. -/
theorem statement_obs_of_statement {t : CombTask} {sem : Nat → Design2} (ty : Nat → Prop)
    (hd : ∀ N, t.inRange N → CombDesign (sem N))
    (hw : ∀ N, t.inRange N → (sem N).writesInput = false)
    (hnd : ∀ N, t.inRange N → ((t.inputs N).map Prod.fst).Nodup)
    (h : t.Statement sem) : t.Statement_obs ty Obs_run2 Unclocked sem :=
  fun N hr _ => satisfiedAt_obs_of_satisfiedAt (hd N hr) (hw N hr) (hnd N hr) (h N hr)

/-- **The record form**: every v1 record whose designs are in the comb profile holds in the trusted
statement. Its only side conditions are the record's own `CombDesign` lemma and distinct input names
(the task's literal port list). `writesInput = false` follows from `CombDesign`. -/
theorem statement_obs_of_comb {t : CombTask} {sem : Nat → Design2} (ty : Nat → Prop)
    (hd : ∀ N, t.inRange N → CombDesign (sem N))
    (hnd : ∀ N, t.inRange N → ((t.inputs N).map Prod.fst).Nodup)
    (h : t.Statement sem) : t.Statement_obs ty Obs_run2 Unclocked sem :=
  statement_obs_of_statement ty hd (fun N hr => CombDesign.writesInput_eq_false (hd N hr)) hnd h

#print axioms inputs_mem_of_interface
#print axioms computes_obs_of_computes
#print axioms computes_iff_computes_obs
#print axioms satisfiedAt_obs_of_satisfiedAt
#print axioms statement_obs_of_statement
#print axioms statement_obs_of_comb

end SvGolf.Arch
