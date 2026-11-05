import tasks.fdivp.Spec

/-!
# Task `fdivp`: the statement as named properties (proved, not trusted)

`Spec.lean`'s `Statement` is one formula. This file gives each part of it a name, one definition
per thing a design must satisfy, and proves `statement_iff_properties`: the statement holds
exactly when, at every format `(W, P)` in range, every property holds. The theorem is checked by
Lean's kernel, so the properties cover the whole statement and nothing else; this file adds
nothing to the trusted base. `properties.json` explains each property in plain words.
-/

namespace SvGolf.Tasks.FdivP.Properties

open SvGolf LeanModels.Sv

/-- The formats the statement covers: every exponent width `W ≥ 2` and precision `P ≥ 2`. -/
def ParamsInRange (W P : Nat) : Prop :=
  2 ≤ W ∧ 2 ≤ P

/-- Exactly these ports, in this order, with these widths. -/
def Interface (W P : Nat) (d : Design2) : Prop :=
  inputPorts d = [("a", W + P), ("b", W + P)] ∧ outputPorts d = [("q", W + P)]

/-- No process runs at a clock edge (no `always_ff`, no `always @(posedge …)`). -/
def Unclocked (d : Design2) : Prop :=
  ∀ p ∈ d.processes.toList, p.isEdgePhase = false

/-- Under every schedule and every stimulus, the run completes. -/
def Terminates (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-- In every completed run, every cycle whose stimulus drives `a` and `b` with known values ends
with `q` holding the IEEE 754 quotient `a / b` in the format `(W, P)`, rounded to nearest, ties
to even (`fdivBits`). -/
def ComputesQuotient (W P : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ (a b : BitVec (W + P)),
        HoldAll inputs [("a", W + P), ("b", W + P)] (a, b, ()) →
        HoldAll st [("q", W + P)] (fdivBits W P a b, ())

/-- **The statement is exactly the properties.** -/
theorem statement_iff_properties (sem : Nat → Nat → Design2) :
    Statement sem ↔ ∀ W P, ParamsInRange W P →
      Interface W P (sem W P) ∧ Unclocked (sem W P) ∧ Terminates (sem W P) ∧
        ComputesQuotient W P (sem W P) := by
  constructor
  · intro h W P hWP
    obtain ⟨hi, ⟨hu, ht⟩, hc⟩ := h W P hWP
    refine ⟨hi, hu, ht, ?_⟩
    intro σ stim tr hr c inputs st hs hst a b hv
    exact hc σ stim tr hr c inputs st hs hst (a, b, ()) hv
  · intro h W P hWP
    obtain ⟨hi, hu, ht, hc⟩ := h W P hWP
    refine ⟨hi, ⟨hu, ht⟩, ?_⟩
    intro σ stim tr hr c inputs st hs hst v hv
    obtain ⟨a, b, ⟨⟩⟩ := v
    exact hc σ stim tr hr c inputs st hs hst a b hv

end SvGolf.Tasks.FdivP.Properties
