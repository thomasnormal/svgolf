# 05. Sequential rung 2: `crc32_step`, a state machine from reset (task class `MachineTask`)

**Pitch.** A 32-bit CRC register that absorbs 32 data bits per clock, reset to all ones: the smallest *stateful*
design with a published oracle (`zlib`, the RevEng catalogue check value) and a real golf problem inside (the
update is a GF(2)-linear map; its XOR network is a shortest-linear-program problem: 1394 GE written naively as
XOR-of-subsets, 494 GE after greedy common-subexpression sharing, measured). It forces exactly the pieces every
later sequential task needs: reset protocol, state-machine statement, one-step-simulation proof principle.

**Header** (fixed size; the data width is part of the task, `crc32_d32`; siblings `d8`, `d64` are separate tasks,
because an optimised XOR network exists per width and a "for every D" statement would exclude it):

```systemverilog
module crc32_step (input logic clk, rst, input logic [31:0] d, output logic [31:0] crc);
```

**Relation to WP-S0.** This is `SeqTask` exactly as `design/sequential/SeqTask.lean` defines it (reset port, `init`, `step`, Moore
`obs`, claim from every reset); the task is WP-S0's ladder rung 2 (LFSR, fixed polynomial) with `D = 32` steps per
clock, which is what makes it golfable. The counter spike (rung 1) is the unit test; this is the first task with a
board.

**Trusted statement (class `MachineTask` = `SeqTask`).** Ports as above (inputs `clk, rst, d`, output `crc`); single clock
(`ClockedBy`, as in rung 1); every run terminates; and for every completed run, every cycle `r` whose entry
drives `rst = 1`, and every later cycle `c` such that entries `r+1 .. c` drive `rst` and `d` with known values,
the snapshot at `c` shows `crc` = the machine state after `c - r` steps from `init`, where
`init = 0xFFFFFFFF`, `step s (rst, d) = if rst then init else update s d`, and `update` is 32 bit-serial steps
of the reflected CRC-32 (polynomial `0xEDB88320`, LSB first). The register is the output (Moore). Nothing is
promised before the first reset.

**Sketch** (`seq_sketch/MachineSpec.lean`, the generic part, compiles; the CRC-specific part below is the new
file):

```lean
structure Machine (I O S : Type) where  (init : S) (step : S → I → S) (out : S → O)      -- compiles
def stepBit (c : BitVec 32) (b : Bool) : BitVec 32 :=
  (c >>> 1) ^^^ (if c.getLsbD 0 ^^ b then 0xEDB88320#32 else 0#32)
def update (c d : BitVec 32) : BitVec 32 := (List.range 32).foldl (fun c i => stepBit c (d.getLsbD i)) c
def crcMachine : Machine (Bool × BitVec 32) (BitVec 32) (BitVec 32) where
  init := 0xFFFFFFFF#32
  step s i := if i.1 then 0xFFFFFFFF#32 else update s i.2
  out s := s
```

**Oracle and independent checks** (all done in the study, `experiments/crc_gen.py`): `update` equals
`zlib.crc32` continued from an arbitrary running value (`zlib.crc32(data_le, prev) = update(prev ^ ~0, data) ^ ~0`,
200 random cases), and the 9-byte check string `"123456789"` gives `0xCBF43926` (the CRC-32/ISO-HDLC check of the
RevEng catalogue). The oracle for the task is a cycle-accurate model with the reset protocol.

**Cost model.** Area including flops (32 x `GE_ff`), period = reg-to-reg depth. Estimates from the measured
combinational pieces (flop price 5.5): naive XOR-of-subsets 1394 + 176 + reset gates 43 = about 1610 GE;
shared XOR network 494 + 176 + 43 = about 710 GE; period 6 to 7 gates. The reset costs one OR per bit if
the reset value is all ones (`next | rst`), which is a small golf point of its own (an all-zero reset
costs an AND per bit).

**Post-synthesis check.** As rung 1 plus the reset: vectors begin with a reset cycle (the generator knows the
protocol from `task.json`), then random `rst`/`d` sequences, compare every cycle from the first reset on; two
initial register contents for the netlist.

**Proof principle (the point of the rung).** A generic theorem `MachineTask.refines_of_step` in `SvGolf/Seq.lean`:
if the design's per-cycle step relation implies `regs' = step regs inputs` and `out = out regs`, with `regs` mapped
to the machine state by an abstraction function, then every trace refines the machine. The player proves only the
**one-step lemma**, which for this design is the combinational proof of the XOR network against `update`. For that
lemma the clean route is a **linearity transfer**: `update (c1 ^ c2) (d1 ^ d2) = update c1 d1 ^ update c2 d2` (induction on
the 32 steps) and "an XOR-only netlist is linear in its inputs" (a meta-theorem over the `sv_equations`
conjunction), so only 64 basis vectors need evaluating (`decide +kernel`). That linear library also serves
`aes_mixcol`, SECDED encoders and MDS layers (`catalogue-comb.md` A5).

**What it forces beyond rung 1.** The reset protocol (the `RefinesFromReset` shape, which is a Design2 port of
the older M0 `⊑@clk[from rst]` judgment that `Examples/system-verilog/counter` already proves for a concrete
8-bit counter), and an `if rst` in the register update (write it as `assign nxt = f | {rst}` per bit + a bare
`always_ff c <= nxt` for the first reference; `always_ff` with `if` needs the WP-G-style equation view).

**Effort: M** (3 days after rung 1's groundwork; the linear library is the only new proof infrastructure).

**Risks.** (1) The reset protocol is the standard trap: a design with a declaration initializer (`logic [31:0] crc
= '1;`) works from cycle 0 in ls-sv and not in silicon; banned. (2) Reset polarity/sync/async: sync active-high
only for rung 2, since the cycle model cannot distinguish async reset anyway. (3) Mealy outputs are confusing in
the post-edge snapshot model, so v1 allows registered (Moore) outputs only. (4) Spec bug place: the reflection
and polynomial; the zlib and RevEng checks cover both.

**Cheating and checker coverage.** `ClockedBy`, initializer ban, `fourstate`/source gate as usual; a "CRC" that
ignores `d` fails the zlib-derived oracle immediately; nothing here is data-dependent on rare inputs because the
state update is linear (a design that differs from `update` differs on a basis vector, which the `postsynth` corners
include: all-zero, walking ones).

**Appeal: 3.5/5 as a game, 5/5 as a foundation.** Ethernet/PCIe/zlib: everybody has used one; the XOR-network
golf has an academic literature (shortest linear programs, Paar and Boyar-Peralta heuristics); and the same
pattern (reset, absorb, expose) is the skeleton of the hash cores that follow (`keccak_core`, `sha256_core`).
