import LeanModels.Sv.Spec2

/-!
# svGolf task statements (TRUSTED)

This file is part of the **trusted base** of svGolf. Every challenge statement
is built from the definitions below, so a reader who wants to know what a
proved submission guarantees has to read this file, the task's own
`tasks/<name>/Spec.lean`, and the ls-sv semantics it rests on
(`LeanModels/Sv/Spec2.lean` for `Runs2`/`⊨₂`/`Terminates2`, `Sem2.lean` for
`run2`). Nothing else is trusted: proof helpers live in `SvGolf/Comb.lean`
and are kernel-checked like any submission.

## What a combinational task says

A task fixes, for every value `N` of the design's one parameter in the
task's range (`CombTask.inRange`):

* an **interface**: the input ports (name, width) and the output ports
  (name, width), each list in port order (`CombTask.inputs`,
  `CombTask.outputs`; widths are functions of `N`);
* a **function** from the input values to the output values, on `BitVec`s
  of exactly those widths (`CombTask.fn`).

`CombTask.Statement t sem` says that the design family `sem : Nat → Design2`
(the `name.sem` constant that `load_design_sv2` defines from the player's
envelope) satisfies, at every `N` with `t.inRange N`, the three conjuncts of
`CombTask.SatisfiedAt`:

1. **`Interface`**: the design's input ports, in declaration order with their
   declared widths, are EXACTLY `t.inputs N`, and its output ports are EXACTLY
   `t.outputs N`.
2. **`Unclocked` and `Terminates2`**: no process of the design is clocked
   (no `always_ff`, no `always @(posedge …)`, no async-reset block: ls-sv's
   edge phase is empty), and under every schedule and every stimulus, the run
   completes (`Spec2.lean`). The two are one conjunct, a pair, so that
   conjuncts 1 and 3 keep their positions (`h.1`, `h.2.2`).
3. **`Computes`**: in every completed run, under every schedule and every
   stimulus, every cycle whose stimulus entry drives every input port with a
   known value (a `BitVec` at the port's width) ends in a snapshot whose output
   ports hold exactly the known values `t.fn N` assigns.

## Why it cannot be satisfied vacuously

The statement was written against the following ways a design could make a
weaker statement true without computing the function. Each is ruled out by
one of the conjuncts; the task's `tests/<name>/negative/` directory holds designs that try
them, with kernel-checked refutations.

* **Never settling, or having no run.** `⊨₂` (`Models2`) quantifies over
  *completed* runs only, so a design that never settles satisfies every `⊨₂`
  property. `Terminates2` requires a completed run for every schedule and
  every stimulus, so with conjunct 2 the property in conjunct 3 is about runs
  that exist. A design the loader refused (`errorDesign`: every run is
  `.unsupported`) has no completed run, so it fails conjunct 2.
* **Hypotheses that never hold.** Conjunct 3's hypothesis is about the
  STIMULUS, which the statement quantifies over, not about the design's
  state. For every input valuation `v` there is a stimulus entry binding
  exactly `v` (when the port names are distinct; `SvGolf/Comb.lean` proves
  this non-vacuity fact, `CombTask.SatisfiedAt.exists_run`), and by
  conjunct 2 it has a completed run whose snapshot must carry `t.fn N v`.
  A snapshot-form hypothesis ("whenever the input ports hold known values in
  the snapshot") would be weaker: a design that drives its own input ports
  could keep that hypothesis false forever. The stimulus form is immune.
* **Stimulus conventions.** `applyInputs2` stores a stimulus value verbatim
  at its own width and silently ignores names that are not input ports
  (`Spec2.lean`, "Stimulus conventions"). The hypothesis therefore uses the
  task's port names and `BitVec`s at the task's widths, and conjunct 1 pins
  that those names ARE the design's input ports with exactly those widths. A
  design that declared `a` with another width, under another name, or as an
  internal signal would either fail conjunct 1 or see different values than
  the hypothesis describes.
* **Extra or missing ports.** Conjunct 1 is list equality, not inclusion: an
  extra input (which the stimulus would never drive, so it reads `x`, or
  which a design could use as a hidden "mode" pin), an extra output, a
  missing port, a port with another direction, and an `inout` port (it would
  appear in both lists) are all rejected.
* **Unknown values.** Outputs must hold `LVec.ofBitVec x`, a fully known
  4-state vector of exactly the output's width. A design that reads an
  undriven signal (`x`), leaves an output undriven, or drives the output from
  some other variable and leaves the port itself at `x`, fails conjunct 3.
* **History.** Conjunct 3 must hold at EVERY cycle of EVERY run, whatever the
  earlier stimulus entries were, so a design whose outputs depend on earlier
  cycles (a register, a toggling mode) fails it.
* **A clock that never ticks.** ls-sv runs every edge-phase process once per
  cycle WHATEVER its clock signal holds (`cycleStep2`: `Design2.edgeIndices`
  filters on the process kind only; the charter's single-clock gap), then
  commits the nonblocking assignments and settles. So
  `logic clk; always_ff @(posedge clk) y <= f;` with `clk` undriven (or tied
  to `1'b0`) holds the right `y` in every ls-sv snapshot, while every
  simulator and Yosys see a clock that never rises and leave `y` at `x` (Yosys
  then scores the design at 0 GE). The `Unclocked` half of conjunct 2 rejects
  every clocked process, which a combinational task never needs. It goes
  when ls-sv's sequential layer models clock edges.
* **Held inputs.** Conjunct 3 constrains only cycles whose stimulus entry
  re-drives every input. A cycle that holds an input instead starts from the
  same state: `applyInputs2` writes with `SvState.set`, which replaces a
  binding in place, so re-driving the value an input already holds leaves the
  state unchanged. So no design can tell the two cases apart.

What the statement does NOT pin, on purpose: signedness and the two-state/four-state choice
of the port declarations (they do not change the bits a port carries),
internal signals, and the parameter's name and declared type. The checker
(`check.py`) separately pins the top module name and the parameter's name,
since the scoring script overrides the parameter by name.

## Conventions

* `Sig = String × Nat` is a port signature: name and width in bits.
* `Vals [w₁, …, wₖ]` is `BitVec w₁ × (… × (BitVec wₖ × Unit))`: one known
  value per port, in port order. A task's function is written with tuple
  patterns, e.g. `fn := fun _ (a, b, ()) => (a &&& b, ())`.
* `HoldAll st sigs v`: in state `st`, each port of `sigs` is bound to the
  known value `v` gives it (`SvState.lookup`, first binding wins, as
  everywhere in ls-sv).
-/

namespace SvGolf

open LeanModels.Sv

/-! ## Ports -/

/-- A port signature: the port's name and its width in bits. -/
abbrev Sig := String × Nat

/-- The input ports of `d` with their declared widths, in declaration order.
`instantiate2` lists the ports first, in port-list order. A declaration is
an input port iff its `isInput` flag is set. -/
def inputPorts (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none

/-- The output ports of `d` with their declared widths, in declaration order.
A declaration is an output port iff its `isOutput` flag is set. -/
def outputPorts (d : Design2) : List Sig :=
  d.decls.toList.filterMap fun dc => if dc.isOutput then some (dc.name, dc.width) else none

/-! ## Known values -/

/-- One known value per port: `Vals [w₁, …, wₖ] = BitVec w₁ × (… × (BitVec wₖ × Unit))`.
Reducible, so that tuple patterns `(a, b, ())` elaborate against it. -/
@[reducible] def Vals : List Nat → Type
  | [] => Unit
  | w :: ws => BitVec w × Vals ws

/-- `HoldAll st sigs v`: in state `st`, every port `(n, w)` of `sigs` is bound
to the fully known `w`-bit vector that `v` assigns it. -/
def HoldAll (st : SvState) : (sigs : List Sig) → Vals (sigs.map Prod.snd) → Prop
  | [], _ => True
  | (n, _) :: sigs, v => SvState.lookup st n = some (LVec.ofBitVec v.1) ∧ HoldAll st sigs v.2

/-! ## No clocked process -/

/-- No process of `d` is clocked: none is an `always_ff`, a plain
`always @(posedge …)` or an async-reset block, the processes ls-sv runs in
its edge phase (`Process2.isEdgePhase`). What remains are continuous assigns
and `always_comb` blocks (and loud `unsupported` nodes, which never complete
a run). -/
def Unclocked (d : Design2) : Prop :=
  ∀ p ∈ d.processes.toList, p.isEdgePhase = false

/-! ## Combinational tasks -/

/-- A combinational svGolf task for a one-parameter design family: the
parameter range, the interface at each parameter value, and the function the
outputs must compute. -/
structure CombTask where
  /-- The parameter values the statement covers ("for every `N` in range"). -/
  inRange : Nat → Prop
  /-- The input ports at parameter `N`: (name, width), in port order. -/
  inputs : Nat → List Sig
  /-- The output ports at parameter `N`: (name, width), in port order. -/
  outputs : Nat → List Sig
  /-- The function: known input values ↦ known output values. -/
  fn : (N : Nat) → Vals ((inputs N).map Prod.snd) → Vals ((outputs N).map Prod.snd)

namespace CombTask

variable (t : CombTask)

/-- Conjunct 1: the design's input and output ports are exactly the task's,
names, order and widths included. -/
def Interface (N : Nat) (d : Design2) : Prop :=
  inputPorts d = t.inputs N ∧ outputPorts d = t.outputs N

/-- Conjunct 3: in every completed run (every schedule, every stimulus),
every cycle `c` whose stimulus entry drives each input port with a known
value of the port's width ends in a snapshot whose output ports hold exactly
`t.fn N` of those values. -/
def Computes (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ v, HoldAll inputs (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)

/-- The statement at one parameter value: interface; no clocked process and
termination; function. Conjunct 2 is the pair `Unclocked d ∧ Terminates2 d`. -/
def SatisfiedAt (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (Unclocked d ∧ Terminates2 d) ∧ t.Computes N d

/-- **The challenge statement** for a one-parameter design family
`sem : Nat → Design2` (a `load_design_sv2` constant `name.sem`): the design
satisfies the task at every parameter value in range. -/
def Statement (sem : Nat → Design2) : Prop :=
  ∀ N, t.inRange N → t.SatisfiedAt N (sem N)

/-- The challenge statement for a parameterless design (`name.sem : Design2`,
a fixed-size task): the task at parameter value `0`, whose interface and
function a fixed-size task writes without using `N`. -/
def StatementFixed (d : Design2) : Prop :=
  t.SatisfiedAt 0 d

end CombTask

end SvGolf
