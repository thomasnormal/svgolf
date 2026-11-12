# About svGolf

svGolf is a public proof-golf board for hardware: a SystemVerilog design and a Lean proof that it meets the
task's statement for every size the task allows, ranked by area × time. It is maintained by the authors of its
repository; questions go to {{issues}}, and How to submit on each task says how a record is made.

svGolf asks two things of every design: a **proof** that it meets the task's statement (it computes the
task's function, or, on a clocked task, keeps the task's property on every cycle), and a **score** from a
pinned synthesis flow. The proof is checked by the Lean kernel against a statement the
maintainers wrote and reviewed; the score is a function of the submitted file. This page says why the
statements are written the way they are, and how svGolf differs from the competition it is modelled on.

The proofs are written with {{library}}, a Lean 4 library for proving real programs correct: a program's
syntax tree becomes a Lean value, and a definitional interpreter gives it meaning. From it come ls-sv, the
SystemVerilog semantics every svGolf statement is written over, the loader that turns a design into Lean, and
the tactics that prove designs. It also covers Python and C++.

## A statement must not be satisfiable without computing anything

A machine-checked proof is worth exactly what its statement says. In a competition the cheapest way to
"win" is a statement that some trivial design satisfies: a design that never settles, that reads an
undefined value, that has a hidden extra input, or that is only right at the width it is scored at. Each
would synthesize to almost nothing and still be "proved". So the trusted statements are written against
those escapes. For every parameter value in the task's range, a design for a combinational task must

1. have exactly the task's ports: names, order and widths, with no extra input and no missing output;
2. have no clocked process, and complete every run under every schedule and every stimulus. A design that
   never settles has no completed run to be wrong in, so termination is part of the claim;
3. end every cycle whose inputs are driven with known values holding exactly the function's value on its
   outputs: fully known (no `x`), whatever the earlier cycles were.

A clocked task (the first is the arbiter) keeps the first point and replaces the other two. The design has
one clock and a synchronous reset, no combinational path from an input to an output (every output is
registered), and completes every run from every power-up state. And from every power-up value of every
register, after every reset, on every input trace driven with known values, its outputs are known and keep
the task's property on every cycle, with every response the task bounds given in time. A register that is
never reset may therefore only hold a value that does not matter, and no construct may create an unknown
value.

The hypotheses are about the stimulus (and, on a clocked task, the power-up state), which the statement
quantifies over, not about the design's own behaviour, so no design can keep them false. Most statements quantify over every width `N`, so a
proof at the scoring point alone does not type-check. Every task lists such designs (wrong ports, a dead
clock, a hidden mode pin, a circuit that is right only at `N = 16`) under "What does not count", a tab of the
trusted statement, each with the checker stage that refuses it.

A statement says what is computed; it cannot say what is scored. The proof is about the design as ls-sv
reads it, the score about the netlist Yosys builds from the same text, and two tools can read one text
differently. So the checker makes both read one canonical text (no preprocessor tricks, attributes or
synthesis pragmas), refuses every way an unknown `x` or `z` value could arise (the tools resolve unknowns
differently), and before it accepts, simulates the scored netlist against the proved design on a sample
of inputs: a guard against the two tools disagreeing, not a proof. The [refusals](site:refusals.html) page
lists every such rule and the principle behind it.

## How svGolf differs from zk.golf

[zk.golf](https://zk.golf) is the model: small, crisp specifications with a large design space, published
comparison points, an `assisted_by` field naming the tools that helped, and a frontier of records. Its
challenges are zero-knowledge circuits, and the cost of a circuit is itself proved in Lean.

svGolf is about hardware, and scores differently:

- **The cost is measured, not proved.** Area and time come from a pinned Yosys and ABC flow, weighed on
  the sky130 standard cells with a pinned liberty. Every record carries the hashes of the flow that scored
  it, and scores are compared only under the same flow; [reproduce a score](site:reproduce.html) gives
  every number again.
- **Checking narrows the gap between proof and score.** In zk.golf the cost is a property of the very
  object the proof is about. In svGolf the proof is about ls-sv's reading of the design and the score about
  Yosys's netlist; the source gate and the 4-state rules refuse every known way the two can differ, and the
  post-synthesis check compares them on a sample of inputs as a backstop.
- **One ranked number, and tools to explore.** The ranked number is area × time: the sky130 area in µm²
  times the critical-path delay (on a clocked task, the register-to-register clock period, flip-flops
  included in the area), in µm²·ns (decided 2026-11-05). Par, Record and Under par use it, and a task
  page lists the records by it (equal products by area in GE, then depth, then the earlier date). The
  Pareto front of area and time, the GE and depth columns and the other flows are for exploring: each task
  page plots any two of them, `leaderboard.py board` lists the records by area × time as the task page does,
  with each one's Pareto layer beside it, and `leaderboard.py pareto` lists the frontier (a small, slow
  circuit and a larger, fast one can both be on it).
- **Proofs for every size.** Most tasks are families. The proof covers every width in range while the
  score is taken at one point, so a design tuned to the scoring point but wrong elsewhere does not count.

## Status

svGolf is in preview. The tasks, the checker and the leaderboard tooling run from the repository, on your own
machine; there is no submission server, and the board is the repository's own record directory.
{{handoff}} The [roadmap](site:roadmap.html) says what comes next.
