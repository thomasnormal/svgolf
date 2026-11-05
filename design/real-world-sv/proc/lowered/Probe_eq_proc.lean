import Submission.Design
import SvGolf.Comb
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.CombLib

namespace Submission

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq SvGolf

theorem lowerComb_decls {d d' : Design2} (h : d.lowerComb = some d') : d'.decls = d.decls := by
  unfold Design2.lowerComb at h
  rcases hp : d.lowerProcs d.processes.toList with _ | ps
  · simp [hp] at h
  · simp only [hp, Option.map_some, Option.some.injEq] at h
    rw [← h]

theorem satisfiedAt_of_lowered {t : CombTask} {N : Nat} {d d' : Design2}
    (hI : t.Interface N d) (hl : d.lowerComb = some d') (hd : CombDesign d') (ha : Acyclic d')
    (hset : ∀ st, CombEqs d' st → StateShape d' st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  obtain ⟨hph, -, -⟩ := Design2.lowerComb_phases hl
  refine ⟨hI, ⟨unclocked_of_edgeIndices hph, Terminates2.of_lowerComb_acyclic hl hd ha⟩, ?_⟩
  apply Models2.of_combProc_inputs hl hd
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  have hdec : d'.inputNames = d.inputNames := by simp [Design2.inputNames, lowerComb_decls hl]
  rw [hdec, ← inputPorts_map_fst, hI.1]
  exact hn

theorem struct_sorry (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (design.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by sorry
theorem iface_sorry (N : Nat) (hN : 1 ≤ N) {d'} (hl : (design.sem N).lowerComb = some d') :
    SvGolf.Tasks.Mul.task.Interface N (design.sem N) := by sorry

example : Goal := by
  intro N hN
  have hN' : 1 ≤ N := hN
  obtain ⟨d', hl, hc, ha⟩ := struct_sorry N hN'
  refine satisfiedAt_of_lowered (iface_sorry N hN' hl) hl hc ha ?_
  intro st heqs hs v hv
  obtain ⟨x, y, ⟨⟩⟩ := v
  simp only [SvGolf.Tasks.Mul.task, HoldAll_cons, HoldAll_nil, and_true] at hv ⊢
  obtain ⟨hA, hB⟩ := hv
  sv_equations?

end Submission
