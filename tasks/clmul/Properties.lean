import tasks.clmul.Spec

/-!
# Task `clmul`: the statement as named properties (proved, not trusted)

`Spec.lean`'s `Statement` is one formula. This file gives each part of it a name, one definition
per thing a design must satisfy, and proves `statement_iff_properties`: the statement holds
exactly when, at every `N` in range, every property holds. The theorem is checked by Lean's
kernel, so the properties cover the whole statement and nothing else; this file adds nothing to
the trusted base. `properties.json` explains each property in plain words.
-/

namespace SvGolf.Tasks.Clmul.Properties

open SvGolf LeanModels.Sv

/-- The widths the statement covers: every `N ≥ 1`. -/
def ParamsInRange (N : Nat) : Prop :=
  1 ≤ N

/-- Exactly these ports, in this order, with these widths. -/
def Interface (N : Nat) (d : Design2) : Prop :=
  inputPorts d = [("a", N), ("b", N)] ∧ outputPorts d = [("p", 2 * N - 1)]

/-- No process runs at a clock edge (no `always_ff`, no `always @(posedge …)`). -/
def Unclocked (d : Design2) : Prop :=
  ∀ p ∈ d.processes.toList, p.isEdgePhase = false

/-- Under every schedule and every stimulus, the run completes. -/
def Terminates (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-- In every completed run, every cycle whose stimulus drives `a` and `b` with known values ends
with `p` holding the coefficients of their product as polynomials over GF(2). -/
def ComputesCarrylessProduct (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ (a b : BitVec N),
        HoldAll inputs [("a", N), ("b", N)] (a, b, ()) →
        HoldAll st [("p", 2 * N - 1)] (ofBits (2 * N - 1) (coeff N a b), ())

/-- **The statement is exactly the properties.** -/
theorem statement_iff_properties (sem : Nat → Design2) :
    Statement sem ↔ ∀ N, ParamsInRange N →
      Interface N (sem N) ∧ Unclocked (sem N) ∧ Terminates (sem N) ∧
        ComputesCarrylessProduct N (sem N) := by
  constructor
  · intro h N hN
    obtain ⟨hi, ⟨hu, ht⟩, hc⟩ := h N hN
    refine ⟨hi, hu, ht, ?_⟩
    intro σ stim tr hr c inputs st hs hst a b hv
    exact hc σ stim tr hr c inputs st hs hst (a, b, ()) hv
  · intro h N hN
    obtain ⟨hi, hu, ht, hc⟩ := h N hN
    refine ⟨hi, ⟨hu, ht⟩, ?_⟩
    intro σ stim tr hr c inputs st hs hst v hv
    obtain ⟨a, b, ⟨⟩⟩ := v
    exact hc σ stim tr hr c inputs st hs hst a b hv

end SvGolf.Tasks.Clmul.Properties
