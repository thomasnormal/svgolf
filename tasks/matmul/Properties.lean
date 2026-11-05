import tasks.matmul.Spec

/-!
# Task `matmul`: the statement as named properties (proved, not trusted)

`Spec.lean`'s `Statement` is one formula. This file gives each part of it a name, one definition
per thing a design must satisfy, and proves `statement_iff_properties`: the statement holds
exactly when, at every `(N, W, AccW)` in range, every property holds. The theorem is checked by
Lean's kernel, so the properties cover the whole statement and nothing else; this file adds
nothing to the trusted base. `properties.json` explains each property in plain words.

The statement's guarantee (`TxTask.Guar`) is one conjunction under the protocol; here it is four
properties, each under the same protocol (`UnderProtocol`): `DoneKnown`, `DoneWithinLatency`,
`DoneHeld` and `ResultIsProduct`. Hypotheses of the guarantee that follow from the rest are
dropped: that the start's operands are known values (the protocol drives them in every cycle;
`ResultIsProduct` keeps the hypothesis, since it names them), `s < h` and `s ≤ c` (implied by the
other bounds).
-/

namespace SvGolf.Tasks.Matmul.Properties

open SvGolf LeanModels.Sv

/-- The parameters the statement covers: `N, W, AccW ≥ 1`, and both port widths below `2^31`. -/
def ParamsInRange (N W AccW : Nat) : Prop :=
  1 ≤ N ∧ 1 ≤ W ∧ 1 ≤ AccW ∧ N * N * W < 2 ^ 31 ∧ N * N * AccW < 2 ^ 31

/-- Exactly these ports, in this order, with these widths. -/
def Interface (N W AccW : Nat) (d : Design2) : Prop :=
  inputPorts d = [("clk", 1), ("rst", 1), ("start", 1), ("A", N * N * W), ("B", N * N * W)] ∧
    outputPorts d = [("done", 1), ("C", N * N * AccW)]

/-- `clk` is an input; every process that runs at a clock edge is clocked by `clk`; an
asynchronous reset can only be `rst`; no process reads `clk` as data. -/
def ClockDiscipline (d : Design2) : Prop :=
  "clk" ∈ d.inputNames.toList ∧
    ∀ p ∈ d.processes.toList,
      (p.isEdgePhase = true → edgeClock p = some "clk") ∧
      (∀ r, asyncReset p = some r → r = "rst") ∧
      "clk" ∉ processDataNames p

/-- Under every schedule and every stimulus, the run completes. -/
def Terminates (d : Design2) : Prop :=
  ∀ (σ : ScheduleOracle) (stim : List SvState), ∃ tr, Runs2 d σ stim tr

/-- The declared latency is at least one cycle. -/
def LatencyAtLeastOne (lat : Nat) : Prop :=
  1 ≤ lat

/-- `G` holds in every completed run, from every release `c1` of the reset, up to every horizon
`h` before which the environment kept the protocol (`TxTask.Rely`). -/
def UnderProtocol (N W AccW : Nat) (d : Design2)
    (G : List SvState → List SvState → Nat → Nat → Prop) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ c1 h, Released "rst" stim c1 h → task.Rely (N, W, AccW) stim tr c1 h → G stim tr c1 h

/-- `done` is a known bit at every cycle from the release. -/
def DoneKnown (N W AccW : Nat) (d : Design2) : Prop :=
  UnderProtocol N W AccW d fun _ tr c1 h =>
    ∀ c, c1 ≤ c → c < h → ∃ b, TraceBit tr c "done" b

/-- After every start `s`, `done` is 1 at some cycle at most `lat` cycles later. -/
def DoneWithinLatency (N W AccW lat : Nat) (d : Design2) : Prop :=
  UnderProtocol N W AccW d fun stim tr c1 h =>
    ∀ s, c1 ≤ s → StimBit stim s "start" true → s + lat < h →
      ∃ c, s ≤ c ∧ c ≤ s + lat ∧ TraceBit tr c "done" true

/-- `Finished stim tr c1 s c`: `s` is a start after the release `c1`, `done` has been 1 at some
cycle from `s` to `c`, and there is no later start up to `c`. -/
def Finished (stim tr : List SvState) (c1 s c : Nat) : Prop :=
  c1 ≤ s ∧ StimBit stim s "start" true ∧
    (∃ c', s ≤ c' ∧ c' ≤ c ∧ TraceBit tr c' "done" true) ∧
    ∀ s', s < s' → s' ≤ c → ¬ StimBit stim s' "start" true

/-- Once `done` is 1 after a start, it stays 1 until the next start. -/
def DoneHeld (N W AccW : Nat) (d : Design2) : Prop :=
  UnderProtocol N W AccW d fun stim tr c1 h =>
    ∀ s c, c < h → Finished stim tr c1 s c → TraceBit tr c "done" true

/-- Once `done` is 1 after a start with operands `A` and `B`, `C` holds the product `A·B` until
the next start. -/
def ResultIsProduct (N W AccW : Nat) (d : Design2) : Prop :=
  UnderProtocol N W AccW d fun stim tr c1 h =>
    ∀ s c (A B : BitVec (N * N * W)), c < h → Finished stim tr c1 s c →
      (∃ e, stim[s]? = some e ∧ HoldAll e [("A", N * N * W), ("B", N * N * W)] (A, B, ())) →
      ∃ st, tr[c]? = some st ∧ HoldAll st [("C", N * N * AccW)] (product N W AccW A B, ())

theorem clockDiscipline_iff (d : Design2) : ClockDiscipline d ↔ task.Disciplined d := by
  constructor
  · rintro ⟨hk, hp⟩
    refine ⟨hk, fun p hmem => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp p hmem
    exact ⟨h1, fun r hr => by rw [h2 r hr]; rfl, h3⟩
  · rintro ⟨hk, hp⟩
    refine ⟨hk, fun p hmem => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hp p hmem
    exact ⟨h1, fun r hr => (Option.some.inj (h2 r hr)).symm, h3⟩

/-- The guarantee is the four properties. -/
theorem follows_iff (N W AccW lat : Nat) (d : Design2) :
    task.Follows (N, W, AccW) lat d ↔
      DoneKnown N W AccW d ∧ DoneWithinLatency N W AccW lat d ∧ DoneHeld N W AccW d ∧
        ResultIsProduct N W AccW d := by
  constructor
  · intro hF
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro σ stim tr hr c1 h hrel hrely
      exact (hF σ stim tr hr c1 h hrel hrely).1
    · intro σ stim tr hr c1 h hrel hrely s hs hst hlat
      obtain ⟨x, hx⟩ := (hrely s hs (by omega)).2.1
      exact ((hF σ stim tr hr c1 h hrel hrely).2 s x hs (by omega) hst hx).1 hlat
    · intro σ stim tr hr c1 h hrel hrely s c hch hfin
      obtain ⟨hs, hst, ⟨c', hsc', hc'c, hd⟩, hno⟩ := hfin
      obtain ⟨x, hx⟩ := (hrely s hs (by omega)).2.1
      obtain ⟨st, hst', hdone, _⟩ := ((hF σ stim tr hr c1 h hrel hrely).2 s x hs (by omega) hst
        hx).2 c (by omega) hch ⟨c', hsc', hc'c, hd⟩ hno
      exact ⟨st, hst', hdone⟩
    · intro σ stim tr hr c1 h hrel hrely s c A B hch hfin hx
      obtain ⟨hs, hst, ⟨c', hsc', hc'c, hd⟩, hno⟩ := hfin
      obtain ⟨st, hst', _, hC⟩ := ((hF σ stim tr hr c1 h hrel hrely).2 s (A, B, ()) hs
        (by omega) hst hx).2 c (by omega) hch ⟨c', hsc', hc'c, hd⟩ hno
      exact ⟨st, hst', hC⟩
  · rintro ⟨hK, hL, hH, hR⟩ σ stim tr hr c1 h hrel hrely
    refine ⟨hK σ stim tr hr c1 h hrel hrely, fun s x hs _ hst hx => ⟨fun hlat =>
      hL σ stim tr hr c1 h hrel hrely s hs hst hlat, fun c _ hch hdone hno => ?_⟩⟩
    obtain ⟨st₁, h₁, hb⟩ := hH σ stim tr hr c1 h hrel hrely s c hch ⟨hs, hst, hdone, hno⟩
    obtain ⟨A, B, ⟨⟩⟩ := x
    obtain ⟨st₂, h₂, hC⟩ := hR σ stim tr hr c1 h hrel hrely s c A B hch ⟨hs, hst, hdone, hno⟩ hx
    rw [h₁] at h₂
    cases h₂
    exact ⟨st₁, h₁, hb, hC⟩

/-- **The statement is exactly the properties.** -/
theorem statement_iff_properties (sem : Nat → Nat → Nat → Design2)
    (lat : Nat → Nat → Nat → Nat) :
    Statement sem lat ↔ ∀ N W AccW, ParamsInRange N W AccW →
      Interface N W AccW (sem N W AccW) ∧ ClockDiscipline (sem N W AccW) ∧
        Terminates (sem N W AccW) ∧ LatencyAtLeastOne (lat N W AccW) ∧
        DoneKnown N W AccW (sem N W AccW) ∧
        DoneWithinLatency N W AccW (lat N W AccW) (sem N W AccW) ∧
        DoneHeld N W AccW (sem N W AccW) ∧ ResultIsProduct N W AccW (sem N W AccW) := by
  constructor
  · intro h N W AccW hp
    obtain ⟨hi, ⟨hd, ht⟩, hl, hf⟩ := h (N, W, AccW) hp
    exact ⟨hi, (clockDiscipline_iff _).2 hd, ht, hl, (follows_iff N W AccW _ _).1 hf⟩
  · rintro h ⟨N, W, AccW⟩ hp
    obtain ⟨hi, hd, ht, hl, hf⟩ := h N W AccW hp
    exact ⟨hi, ⟨(clockDiscipline_iff _).1 hd, ht⟩, hl, (follows_iff N W AccW _ _).2 hf⟩

end SvGolf.Tasks.Matmul.Properties
