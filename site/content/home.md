# Prove a circuit correct, then golf its gates.

svGolf is a competition for hardware written in
SystemVerilog, in the spirit of [zk.golf](https://zk.golf). Each task fixes a function (an adder, a
multiplier, the AES S-box, IEEE 754 division) and a trusted Lean statement of what a circuit computing it
must satisfy. You submit a circuit and a proof; the checker accepts the pair or says why not.

## The loop

1. **Write** a combinational circuit in SystemVerilog, with the task's exact module header.
2. **Prove** in Lean 4 that it meets the task's trusted statement, for every parameter value in the
   task's range. The statements are written against [ls-sv](site:tasks/_example/index.html#closure), the
   lean-surfaces project's formal semantics of SystemVerilog in Lean, which defines what a design
   computes. The kernel checks the proof, which may use only the task's allowed axioms (normally
   `propext`, `Classical.choice` and `Quot.sound`).
3. **Get scored** by the pinned synthesis flow (Yosys and ABC), on the open SkyWater sky130 standard
   cells (`sky130_fd_sc_hd`). The score is *area × time*: the cell area in µm² times the critical-path
   delay (a clocked task: the cycles times the clock period), in µm²·ns. Lower is better, and the
   leaderboard ranks the area and the time. Area in NAND2 gate equivalents (GE), depth in gates and the
   other numbers are shown beside it, and each task page plots any two of them against each other.
   [Reproduce a score](site:reproduce.html) gives every number again with the pinned tools.

## The proof and the score

The proof is about the design as ls-sv reads it, the score about the netlist Yosys builds from the same
text. Before it accepts, the checker simulates the scored netlist against the proved design on a sample
of input vectors and rejects any disagreement: fixed patterns and the task's corner values, inputs built
from the constants the design compares against, and seeded random vectors, salted in competition runs so
that nobody can predict them (every input where the input space is small, as for the AES S-box's 256).
That is sampling, not a proof: a guard against the two tools disagreeing, behind the static rules that
refuse every known disagreement before any proof is tried. Read the [rules](site:rules.html) and the
[proving guide](site:proving.html), or start with the [tutorial task](site:tasks/_example/index.html).