# Catalogue B: sequential and asynchronous candidates (the ladder towards a CPU)

Same conventions as `catalogue-comb.md`. Everything here is a *design study*: the WP-S0 note (`svgolf/design/sequential/README.md`, `SeqTask.lean`) appeared while this was being written and is the
reference for the statement class (`SeqTask`, `ClockedBy`, reset-anchored `Follows`, the reduction theorem, the cost
model of its section 5, its own ladder in section 6). This catalogue adds task-level content on top of that ladder
(what to ask for, oracles, golf headroom) and flags where a rung needs a variant of `SeqTask`. The two compiled sketches (`seq_sketch/PipeSpec.lean`, `seq_sketch/MachineSpec.lean`) only prove the shapes typecheck.

## B0. What the current model gives, and what each rung must add

* **Cycle model.** One stimulus entry is one clock period; `cycleStep2` = apply inputs, settle, reset pass (async-reset
  blocks), edge pass (every `always_ff`/`@(posedge)` process ONCE, whatever its clock holds), NBA commit, settle. The
  snapshot of cycle `c` is the state after the edge with the cycle's inputs still applied. Consequences used below:
  (i) a design with one register stage is indistinguishable from combinational logic in the snapshot, so
  pipelines are counted by delay `D = stages - 1 >= 1`; (ii) outputs that depend combinationally on inputs are
  confusing, so v1 tasks use registered (Moore) outputs; (iii) sync and async reset are indistinguishable
  (no time inside the cycle), so truly asynchronous behaviour needs a new scheduler layer (R1, the "ruling 6.4"
  scheduler), not just parsing `negedge`.
* **Statement classes** (all are: `Interface` + `ClockedBy` hygiene instead of `Unclocked` + `Terminates2` + a trace
  property; `ClockedBy` = every edge process is `@(posedge clk)` on the task's `clk` port, `clk` read nowhere else,
  no `initial`, no initializer on a register, no latch):
  `PipeTask t D` (compiled sketch), `MachineTask` (Moore machine from reset; compiled sketch),
  `LatencyTask` (start/done handshake with a latency bound), `HistoryTask` (output at cycle `c` is a Lean function of the
  entire input history: for protocol blocks, with no hidden spec state), `RelTask` (relation with don't-cares),
  `ClosedLoopTask` (an environment predicate, e.g. "the instruction input equals ROM[pc of the previous
  cycle]"), `MultiClockTask` (free relative clock schedule, metastability as nondeterminism).
* **Cost model.** `area = gates + flops x GE_ff` (price `$_DFF_P_`, run `dfflegalize` so that enables and resets
  are gates), `period = depth` (`ltp -noff`, already in the pinned script, which stops at flops). The pinned flow was
  tried on a 2-stage pipeline: it maps it to `$_DFF_P_` and `score.py` stops with "cells the GE table does not price". Latency is
  fixed by the statement or bounded by a stated budget; it is not a score axis (so slower, smaller designs are
  allowed only where the budget allows).
* **Post-synthesis check for clocked designs.** ls-sv `run2` on stimulus *sequences* vs Verilator on the scored netlist with
  a toggled clock, sampled after each rising edge before inputs change; protocol-aware vector generator (reset first,
  start only when idle); compare only where ls-sv's bits are known; netlist run from two initial register contents.
* **Common defences.** No declaration initializers or `initial` blocks; no latches; one clock; no derived clocks; registered outputs.

Ranking key as in catalogue A. Products: B1 64, B3 50, B2 49, B4 36, B7 31, B8 31, B6 24, B9 16, B5 14, B10 9, B11 5, B12 4.

---

## B1. `pipe_*`: a combinational function with delay D: see `04-pipe-fn.md`
*Class `PipeTask`. First concrete task `pipe_mul`. No reset. New golf axis: where to cut. Groundwork: `SvGolf/Seq.lean`, `ClockedBy`, flop price, sequence `postsynth`, `Pipelined.of_stages`.*

## B2. `crc32_step`: a state machine from reset: see `05-crc-step.md`
*Class `MachineTask`. Reset protocol, one-step simulation theorem, linear library. Oracle `zlib`.*

## B3. `ctr_en`, `lfsr`, `shift_reg`: the spike (not tasks, but WP-S0's first proofs)
- **Pitch.** N-bit counter with enable and synchronous reset (the spike named in PLAN2 T6), a Galois LFSR, a shift register.
- **Header.** `module ctr_en #(parameter int N = 16) (input logic clk, rst, en, output logic [N-1:0] q);`
- **Statement.** `MachineTask` with `init = 0`, `step s (rst, en) = if rst then 0 else if en then s + 1 else s`, `out s = s`.
- **Spec sketch.** `def ctr (N) : Machine (Bool × Bool) (BitVec N) (BitVec N)`, as in `05-crc-step.md` with `step` above.
- **Oracle.** Python integer model; independent check: the same counter in Verilator.
- **Banned / cost.** Ban `+ - * / % **` (the incrementer is a half-adder chain from gates). Area = N flops + 2N gates + reset/enable logic.
- **Needs.** `always_ff @(posedge clk)` with `<=` (exists in `Sem2`); for the tactic: an edge-process view; the incrementer proof reuses `ripple_row` with `cin = 1`.
- **Proof.** Invariant `q = machine state` for all cycles and all N; step lemma = the `add_n` ripple row with `b = 0`, `cin = en`.
- **Reference.** Half-adder chain: `q' = q ^ carry-chain`, `carry[i+1] = carry[i] & q[i]`, `carry[0] = en`; reset by AND with `~rst`.
- **Effort: S to M** (this is the spike; the first sequential theorem for every N).
- **Risks.** None beyond the shared groundwork; as a *task* it has no golf (the incrementer is forced).
- **Appeal: 2/5** as a game; 5/5 as the unit test of the sequential layer. `Examples/system-verilog/counter` already proves a concrete 8-bit counter in the older M0 tier (`⊑@clk[from rst]`), so the statement shape has a precedent.

## B4. `serial_mul`: shift-and-add multiplier, N cycles
- **Pitch.** The area/time trade of the multiplier family: 5 times smaller than the array multiplier and N times slower; golf is the register count (2N flops is possible: the multiplier shares the accumulator's low half).
- **Header.** `module serial_mul #(parameter int N = 16) (input logic clk, rst, start, input logic [N-1:0] a, b, output logic done, output logic [2*N-1:0] p);`
- **Statement (class `LatencyTask`).** Single clock; terminates; for every cycle `s` whose entry drives `start = 1`, `a`, `b` known, with no `start` in cycles `s-N .. s-1` (environment obeys the protocol) and a reset before: `done` is 1 at cycle `s + N` with `p = a * b`, and `done` is 0 at every cycle that is not `s + N` for such an `s`; `p` is unconstrained when `done = 0`.
- **Spec sketch.** `def latency (t : CombTask) (L N) (stim tr) : Prop := ∀ c s inp st, s + L = c → stim[s]? = some inp → tr[c]? = some st → startsHigh inp → idleBefore stim s L → HoldAll inp (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)` plus the exact-`done` clause; the combinational task is the existing `mul`.
- **Oracle.** The `mul` oracle with a delay line; independent: Python big-int product.
- **Banned / cost.** Ban `+ - * / % **`; area incl. flops, period = one adder; latency pinned to `N` (a budget `<= 2N` would allow radix-4 designs: a decision).
- **Needs.** Everything of B1/B2, plus `if`/enable in edge processes, the protocol-aware vector generator, `done` as an exact-pulse output.
- **Proof.** Loop invariant over the cycle counter `i <= N`: `acc_i = a * (b mod 2^i)` in the accumulator/multiplier register pair; per-cycle step is the `add_n` row; for all N by induction on `i` inside the cycle induction.
- **Reference.** Classic: `{acc, mplier}` shift register of 2N bits, one N-bit adder, a counter (or a one-hot marker in the multiplier register).
- **Effort: M to L** (4 days after B1/B2). **Risks.** The idle-protocol assumption weakens the statement (a design may misbehave on a `start` while busy): state it, it is the standard assume/guarantee; latency exactness invites a "multi-cycle path" design that is only correct if the checker's period is honest. **Appeal: 4/5**: the area-time curve is every hardware designer's first trade-off.

## B5. `div_iter` and `fdiv16_iter`: iterative dividers
- **Pitch.** The RISC-V `DIV` unit (restoring/non-restoring, N cycles) and its binary16 sibling against the SAME trusted `fdiv16` spec as the combinational task (2089 GE, depth 298): the board then shows the area/latency trade of one function in two classes.
- **Header.** `module div_iter #(parameter int N = 16) (input clk, rst, start, input [N-1:0] a, b, output done, output [N-1:0] q, r);`
- **Statement.** `LatencyTask` over `intdiv`'s `fn` (A10), `b = 0 -> (all ones, a)`; for `fdiv16_iter`, `fn = fdiv16` with latency budget (about 14 cycles).
- **Oracle.** Python `divmod`; for fp, `spec/validate/oracle.py` (already Verilator-validated on all 2^32 pairs).
- **Cost.** flops (2N to 3N) + one subtractor + control; for fp, ~500 GE of datapath plus ~60 flops against 2089 GE.
- **Proof.** Restoring recurrence invariant (the arithmetic WP-H1 builds for fdiv) inside the cycle induction. **Needs** B4's groundwork + A10's arithmetic.
- **Effort: L (int), XL (fp).** **Risks:** the fp proof inherits fdiv16's difficulty (certificate bridge). **Appeal: 3.5/5 (int), 4/5 (fp: the HardFloat `divSqrtRecFN_small` style the lead named).**

## B6. `fifo_sync`: synchronous FIFO
- **Header.** `module fifo_sync #(parameter int W = 8, parameter int K = 3) (input clk, rst, push, pop, input [W-1:0] din, output [W-1:0] dout, output full, empty);` (two parameters: `CombTask2`-style statement, approved).
- **Statement (class `MachineTask` with output validity).** Machine state `List (BitVec W)` of length `<= 2^K`; `step`: if `pop` and not empty drop the head; if `push` and not full (after the pop) append `din`; `full`/`empty` exact; `dout` is the head when not empty (first-word-fall-through), unconstrained when empty. Overflow/underflow pushes/pops are ignored by the spec (stated: the design must also ignore them or the statement fails).
- **Oracle.** Python `collections.deque` with the same ignore rules; independent: SystemVerilog `$fatal`-free reference from the literature (Cummings, "Simulation and Synthesis Techniques for Asynchronous FIFO Design" for the pointer scheme) is a design, not an oracle: the deque is the oracle.
- **Needs.** Run-time-indexed array write and read (`dc-unpacked`, `st-assign-target`, `sel-dyn-*`, "later" in the register), a power-of-two array so the read index cannot leave range (the `fourstate` rule), edge processes with `if`.
- **Proof.** Abstraction function `contents = take count (rotate mem rptr)`; invariant `count = wptr - rptr (mod 2^(K+1))` and `count <= 2^K`; for all W, K by induction on cycles with the list model.
- **Cost.** Dominated by `2^K * W` flops; golf = pointer scheme (binary / Gray / one-hot), flag logic, write-enable structure.
- **Effort: L.** **Risks:** dynamic array semantics in ls-sv are not there yet (T2). **Appeal: 4/5.** The synchronous FIFO is the prerequisite of the asynchronous one (B12).

## B7. `arbiter_rr`: round-robin arbiter
- **Header.** `module arbiter_rr #(parameter int K = 8) (input clk, rst, input [K-1:0] req, output [K-1:0] grant);`
- **Statement (`MachineTask`, Mealy output made Moore by registering grants, or explicit combinational grant in the post-edge model).** State: the last-granted index `last`; `grant` = one-hot of the first requester after `last` (cyclically) among `req`, or 0; `last` updates to the granted index. Lean: `nextGrant (last) (req) : Option (Fin K)`.
- **Oracle.** Python loop; the fairness theorem (every requester is granted within `K` grants) is proved in Lean about the spec, a spec cross-check.
- **Banned / cost.** Arithmetic banned; area = K flops (thermometer mask) + prefix-OR logic. Known designs: masked priority encoder (two priority encoders and a mask register).
- **Needs.** `generate for` with prefix chains (in fragment), edge process; parametric K.
- **Proof.** Invariant: mask is a thermometer code; priority encoder lemma by induction on bit index.
- **Effort: M to L.** **Risks:** the spec's tie rules; liveness is a theorem about the spec, not part of the design statement. **Appeal: 3.5/5.**

## B8. `uart_tx` (then `uart_rx`)
- **Header.** `module uart_tx #(parameter int D = 4) (input clk, rst, valid, input [7:0] data, output tx, ready);` (`D` cycles per bit.)
- **Statement (class `HistoryTask`).** For a compliant `valid` pulse at cycle `s` (while `ready`): `tx` is 0 for cycles `s+1 .. s+D` (start bit), then the 8 data bits LSB first each held `D` cycles, then 1 (stop) for `D` cycles, idle 1 otherwise; `ready` is 1 exactly when idle. The spec is a function `txAt D events c` of the *whole* input history, so there is no hidden spec state to get wrong.
- **Oracle.** Python waveform generator; independent: a standard serial decoder (a Python UART receiver model) must recover the bytes from the waveform.
- **Needs.** B2's groundwork; parametric `D` counter; protocol vector generator. **rx** additionally: sampling at mid-bit, a precondition that the waveform is well-formed (a `ClosedLoopTask`-style environment predicate), and a 2-flop synchroniser modelled as plain flops (the cycle model has no metastability).
- **Proof.** Counters invariants for all `D`.
- **Effort: L (tx), L+ (rx).** **Risks:** a lot of protocol detail for little golf. **Appeal: 3.5/5** (practical, recognisable, a good demo of `HistoryTask`).

## B9. `keccak_core`: iterative Keccak-f
- **Pitch.** One round per cycle for `12 + 2 l` cycles, round constant from the LFSR of FIPS 202 Algorithm 5 (or a table): the SAME `Spec` as the combinational `keccak_round` (A4) composed. The state register is `25 W` flops: at W = 16, 400 flops are about 2200 GE next to 2965 for the round logic, so the trade between unrolling, lane-serial datapaths (the Keccak team's compact coprocessors) and round-constant generation is real.
- **Header.** `module keccak_core (input clk, rst, start, input [399:0] s_in, output done, output [399:0] s_out);` (fixed W = 16; 20 rounds.)
- **Statement.** `LatencyTask` over `fn = keccakF400` (composition of `A4`'s `round` with the specified RC) and latency 20.
- **Oracle.** `keccak_round/oracle.py` `permutation`; independent: XKCP final states (`State after permutation:`) and `hashlib` at W = 64.
- **Needs.** B4's groundwork + A4's WP-F2. **Proof:** round-by-round invariant `state_i = round^i s_in`; the A4 round proof as the step lemma.
- **Effort: L to XL.** **Risks:** statement size; lane-serial variants change the schedule (a latency budget, not an exact cycle count). **Appeal: 4/5**; zk-relevant, and the first "same spec, new cost model" pair like zk.golf's.

## B10. `acc_cpu`: an accumulator machine with a program ROM
- **Pitch.** The first CPU: 8-bit accumulator, 16-bit instructions (LDI, ADD, XOR, JNZ, OUT, HALT...), instruction fetched from an external ROM.
- **Statement (class `ClosedLoopTask`).** For every ROM `M : BitVec 8 → BitVec 16` and every stimulus in which the `instr` input of cycle `c` equals `M (pc of cycle c-1)` (the environment is a ROM; the predicate is a relation between stimulus and trace, satisfiable by construction because `pc` is registered), the trace of `(pc, acc, out)` equals the Lean ISA machine `isaStep` run on `M`. Non-vacuity theorem: for every ROM and every input sequence such a stimulus exists.
- **Oracle.** Python ISA simulator; independent: a second Python implementation written from the Lean `isaStep`'s docstring by another agent/model (the spec is the place a bug hides here).
- **Needs.** `ClosedLoopTask`, B2/B4 groundwork, register file as an array (B6's dynamic indices) if more than one register.
- **Proof.** Refinement by the abstraction `(pc, acc, flags)`; one-step simulation per instruction.
- **Effort: XL** (2 weeks). **Risks:** the environment predicate is the novelty and the danger (an unsatisfiable predicate proves everything); the non-vacuity theorem is mandatory. **Appeal: 4.5/5**; golf is real: decode logic, ALU sharing.

## B11. `rv_core`: an RV32I-subset core with a retirement interface
- **Pitch.** The destination. Statement in the style of RVFI (the riscv-formal retirement interface): the core outputs a record per retired instruction, the trusted spec is the Lean RV32I `step`, the relation says the retirement stream is the ISA execution of the program in memory, for every memory contents. Pipelining enters as freedom in the cycle at which each retirement appears. The same record format is what a zkVM proves.
- **Needs.** B10's classes, instances (register file, ALU), memory interfaces, hazards (the statement does not mention them; the proof does), a decode oracle: for instructions, the independent oracle is riscv-tests / `riscv-formal`'s own checks and a second ISA simulator (Spike, QEMU) on random programs.
- **Effort: XXL** (months). **Risks:** everything. **Appeal: 5/5.** Not this month.

## B12. `async_fifo`: Gray-pointer FIFO across two clocks
- **Statement (class `MultiClockTask`).** For every relative schedule of the write and read clocks and every resolution of the synchronisers' metastable captures (each captured bit takes either its old or new value), the sequence of values read is a prefix of the sequence written, no loss, no duplication, no reordering, and `full`/`empty` are conservative.
- **Needs.** A scheduler model with two clocks (R1), nondeterministic capture, a `negedge`/multi-process semantics, a proof about Gray-code one-bit-change invariants. **Effort: XXL.** **Appeal: 4/5.** The point where "asynchronous" stops being a name.
