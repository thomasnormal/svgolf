# Prove a circuit correct, then golf its gates.

Each task fixes what a circuit must do in a trusted Lean statement: a function, or on a clocked task a
property of every cycle. You write the circuit in SystemVerilog, prove in Lean that it meets the statement
for every width the task allows, and the checker scores the circuit by area × time. Lower is better.

## How it works, on the adder

1. **Write** `solution.sv`, with the task's module header. The adder bans the arithmetic operators, so
   the sum is built from gates. The adder's ripple-carry reference,
   [`tasks/add/reference/add_n.sv`](site:tasks/add/reference/add_n.sv):

   ```systemverilog
   {{add/add_n.sv}}
   ```

2. **Prove** `Solution.lean`: one theorem. The checker turns your `.sv` into the Lean constant `design`,
   the circuit as [ls-sv](site:index.html#how-a-design-becomes-lean), the formal semantics of SystemVerilog
   in Lean, runs it. `Goal` is the task's [trusted statement](site:tasks/add/index.html#spec) about it:
   for every `N` with `1 ≤ N < 2^31`, whenever the inputs are known, `{cout, s} = a + b + cin`.

   ```lean
   import Submission.Design   -- written by the checker: `design`, `Goal`
   namespace Submission
   theorem solution : Goal := by
     -- your proof (add_n.lean: a complete one)
   end Submission
   ```

3. **Check** both files with one command. It accepts the pair or names the stage that refused it. Its
   last line is the score: the pinned Yosys and ABC synthesize your circuit, each gate becomes a sky130
   cell, and the area in µm² times the critical-path delay in ns is the one ranked number. Par is the
   best proved reference; beat it.

   ```
   $ python3.12 check.py tasks/add solution.sv Solution.lean
   ...
     "accepted": true,
   ...
   {{add/add_n.headline}}
   ```

**You submit two files**, `solution.sv` and `Solution.lean` (any names). Golf without Lean:
`python3.12 score/ppa.py solution.sv --task tasks/add --no-mapped` prints the same area and delay in a
second or two, and the same file always scores the same ([reproduce a score](site:reproduce.html)).
Install once: [Step 0](site:tasks/_example/index.html#first-submission).

## How a design becomes Lean

You never write the Lean model of your circuit. The checker reads your `.sv` through a source gate that
makes one canonical text for every tool, and the pinned extractor of proglib (formerly lean-surfaces), built on the slang
SystemVerilog frontend, turns that text into an envelope: the elaborated design, cross-checked at several
parameter values. The checker then writes the trusted module `Submission.Design`, whose
`load_design_sv2 design from "<envelope>"` makes the Lean constant `design`: `design.sem N` is your circuit
at parameter `N` as ls-sv runs it, and `Goal` is the task's statement of `design.sem`. Your
`Solution.lean` imports that module and proves `theorem solution : Goal` in `namespace Submission`. The
[proving guide](site:proving.html#0-the-loop) shows the loop: stage the design, print its equations, prove.
Each task page's "Start a new design" says which tactics prove a new circuit of that task, how to lay the
circuit out so that they take it, and which library lemmas exist.

## The proof and the score

The proof is about the design as ls-sv reads it, the score about the netlist Yosys builds from the same
text. Before it accepts, the checker simulates the scored netlist against the proved design on a sample
of input vectors and rejects any disagreement: fixed patterns and the task's corner values, inputs built
from the constants the design compares against, and seeded random vectors, salted in competition runs so
that nobody can predict them (every input where the input space is small, as for the AES S-box's 256). On
a clocked task both run long seeded input traces from several power-up states, and the checker also holds
the netlist's outputs to the task's property on every cycle. That is sampling, not a proof: a guard against the two tools disagreeing, behind the static rules that
refuse every known disagreement before any proof is tried. Read the [rules](site:rules.html) and the
[proving guide](site:proving.html), or start with the [tutorial task](site:tasks/_example/index.html).
