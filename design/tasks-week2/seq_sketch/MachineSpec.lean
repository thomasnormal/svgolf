import SvGolf.Task

/-!
# SKETCH: the statement shape of a state-machine refinement from reset (task class `MachineTask`)

**NOT A DRAFT OF A TRUSTED FILE** (see `PipeSpec.lean`). A task gives a Lean machine and a reset
protocol; the statement says every observable trace of the design is the machine's.

The reset protocol of the sketch (the simplest one, synchronous active-high `rst`): from the first
cycle `r` whose entry drives `rst = 1`, with every input driven (known) from `r` on, the machine is
in `init` after cycle `r`'s edge, and cycle `c + 1` applies `step` to cycle `c + 1`'s inputs. The
outputs of cycle `c >= r` are `out` of the machine state after cycle `c`.
-/

namespace SvGolf.Sketch

open SvGolf LeanModels.Sv

/-- A Moore machine over decoded input values `I`, output values `O`, states `S`. -/
structure Machine (I O S : Type) where
  init : S
  step : S → I → S
  out : S → O

/-- The state after consuming the inputs `is` from `s`. -/
def Machine.run {I O S : Type} (m : Machine I O S) (s : S) : List I → S
  | [] => s
  | i :: is => m.run (m.step s i) is

/-- A decoder from a snapshot-or-stimulus entry to the machine's input value, and from the machine's
output value to the expected port values: how a task ties `Machine` to its ports. -/
structure Wiring (I O : Type) where
  rstName : String
  inOf : SvState → Option I      -- `none` unless every input port is driven with a known value
  outHolds : SvState → O → Prop  -- the output ports of a snapshot hold `o`

/-- Refinement from reset: for every cycle `r` that drives `rst = 1` and every later cycle `c`, if all
entries `r .. c` are fully driven, the snapshot at `c` shows `out` of the machine after the inputs
`r+1 .. c`. -/
def RefinesFromReset {I O S : Type} (m : Machine I O S) (w : Wiring I O) (stim tr : List SvState) : Prop :=
  ∀ (r c : Nat) (e st : SvState) (is : List I), r ≤ c →
    stim[r]? = some e → SvState.lookup e w.rstName = some (LVec.ofBitVec (1#1)) →
    tr[c]? = some st →
    (∀ k, k < c - r → ∃ x, stim[r + 1 + k]?.bind w.inOf = some x ∧ is[k]? = some x) →
    is.length = c - r →
    w.outHolds st (m.out (m.run m.init is))

end SvGolf.Sketch
