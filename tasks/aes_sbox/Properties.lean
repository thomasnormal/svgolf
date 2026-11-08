import tasks.aes_sbox.Spec

/-!
# Task `aes_sbox`: the statement as named properties (proved, not trusted)

`Spec.lean`'s `Statement` is one formula. This file gives each part of it a name, one definition
per thing a design must satisfy, and proves `statement_iff_properties`: the statement holds
exactly when every property holds. The task has no parameter, so there is no range. The theorem
is checked by Lean's kernel, so the properties cover the whole statement and nothing else; this
file adds nothing to the trusted base. `properties.json` explains each property in plain words.
-/

namespace SvGolf.Tasks.AesSbox.Properties

open SvGolf LeanModels.Sv

/-- Exactly these ports, in this order, with these widths. -/
def Interface (d : Design2) : Prop :=
  inputPorts d = [("x", 8)] ∧ outputPorts d = [("y", 8)]

/-- No process runs at a clock edge (no `always_ff`, no `always @(posedge …)`). -/
def Unclocked (d : Design2) : Prop :=
  ∀ p ∈ d.processes.toList, p.isEdgePhase = false

/-- No combinational loop: the design lowers to continuous assigns (`Design2.lowerComb`) that are
ranked (`Acyclic`): each reads only what lower-ranked ones write. -/
def LoopFree (d : Design2) : Prop :=
  ∃ d', d.lowerComb = some d' ∧ Acyclic d'

/-- Under every schedule and every stimulus, the run completes. -/
def Terminates (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-- In every completed run, every cycle whose stimulus drives `x` with a known value ends with
`y` holding the AES S-box of `x`. -/
def ComputesSbox (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ (x : BitVec 8),
        HoldAll inputs [("x", 8)] (x, ()) →
        HoldAll st [("y", 8)] (sbox x, ())

/-- **The statement is exactly the properties.** -/
theorem statement_iff_properties (d : Design2) :
    Statement d ↔ Interface d ∧ Unclocked d ∧ LoopFree d ∧ Terminates d ∧ ComputesSbox d := by
  constructor
  · intro h
    obtain ⟨hi, ⟨hu, hl, ht⟩, hc⟩ := h
    refine ⟨hi, hu, hl, ht, ?_⟩
    intro σ stim tr hr c inputs st hs hst x hv
    exact hc σ stim tr hr c inputs st hs hst (x, ()) hv
  · intro h
    obtain ⟨hi, hu, hl, ht, hc⟩ := h
    refine ⟨hi, ⟨hu, hl, ht⟩, ?_⟩
    intro σ stim tr hr c inputs st hs hst v hv
    obtain ⟨x, ⟨⟩⟩ := v
    exact hc σ stim tr hr c inputs st hs hst x hv

end SvGolf.Tasks.AesSbox.Properties
