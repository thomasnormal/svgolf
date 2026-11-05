import SvGolf.Task

/-!
# SKETCH: the statement shape of a pipelined combinational function (task class `PipeTask`)

**NOT A DRAFT OF A TRUSTED FILE.** It only checks that the trace-property shape type-checks against
`LeanModels.Sv.Spec2` and `SvGolf.Task`. The clock-hygiene conjunct (`SingleClock`) and the checker
side belong to WP-S0's design note; here it is a docstring.

A pipelined task reuses a combinational task `t` (so `mul`, `clmul`, `keccak_round` all become
sequential tasks for free) and a latency `L >= 1`:

* the interface is `t`'s, plus ONE extra input port `clk` (1 bit), and nothing else (no reset);
* every edge-phase process of the design is `@(posedge clk)` on that port and `clk` is read nowhere
  else (`SingleClock "clk"`, replaces `Unclocked`); every run terminates;
* **Pipelined**: in every completed run, for every cycle `c` and every `s` with `s + L = c + 1` whose
  stimulus entry drives all of `t`'s inputs with known values `v`, the snapshot of cycle `c` holds
  `t.fn N v` on the outputs. In ls-sv's cycle model a stimulus entry is one clock period and the
  snapshot of cycle `c` is the state after cycle `c`'s edge, so `L = 1` is "one register stage".
  The first `L - 1` snapshots are unconstrained (the registers start at `x`): no reset is needed.
-/

namespace SvGolf.Sketch

open SvGolf LeanModels.Sv

/-- The trace property of a pipeline with latency `L` for the function of `t` at parameter `N`. -/
def Pipelined (t : CombTask) (L N : Nat) (stim tr : List SvState) : Prop :=
  ∀ (c s : Nat) (inp st : SvState), s + L = c + 1 → stim[s]? = some inp → tr[c]? = some st →
    ∀ v, HoldAll inp (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)

/-- The sequential statement at one parameter value: `Pipelined` in every completed run of every
schedule, plus termination (the clock-hygiene conjunct is not modelled in this sketch). -/
def PipeSatisfiedAt (t : CombTask) (L N : Nat) (d : Design2) : Prop :=
  Terminates2 d ∧ d ⊨₂ spec2 (Pipelined t L N)

/-- `L = 0` is the combinational task's `Computes` in this shape (one cycle, no delay): the class
contains `CombTask.Computes` as a special case, which is a sanity check of the shape. -/
example (t : CombTask) (N : Nat) : Pipelined t 1 N = fun stim tr => ∀ (c : Nat) (inp st : SvState),
    stim[c]? = some inp → tr[c]? = some st →
    ∀ v, HoldAll inp (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v) := by
  funext stim tr
  apply propext
  constructor
  · intro h c inp st h1 h2 v hv
    exact h c c inp st (by omega) h1 h2 v hv
  · intro h c s inp st hs h1 h2 v hv
    have : s = c := by omega
    subst this
    exact h s inp st h1 h2 v hv

end SvGolf.Sketch
