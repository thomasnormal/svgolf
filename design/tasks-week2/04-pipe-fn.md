# 04. Sequential rung 1: `pipe_*`, a combinational function behind registers (task class `PipeTask`)

**Pitch.** Take any combinational task `t` (`mul`, `clmul`, `chacha_qr`, `keccak_round`) and ask for the same
function with `D >= 1` extra cycles of delay. The statement is the combinational statement shifted in time, so
it needs no reset, no protocol and no new specification work; the new golf dimension is *where to cut*: flops
cost about five NAND2 each, the clock period is the longest register-to-register path, and the best cut is a
min-cut problem with arithmetic structure (carry-save rows are 2 vectors wide, partial products N^2).

**First concrete task: `pipe_mul`** (pipelined `mul`, `D = 1`, two register stages):

```systemverilog
module pipe_mul #(parameter int N = 16) (
  input  logic clk, input logic [N-1:0] a, b, output logic [2*N-1:0] p);
```

**The observation that fixes the latency convention (checked on the sketch).** ls-sv's trace has one snapshot per
stimulus entry, taken after that cycle's clock edge and settle (`cycleStep2`), with the cycle's inputs still
applied. A design with ONE register stage therefore shows `y_c = f(x_c)` in snapshot `c`: *indistinguishable from
combinational logic*. Observable latency is `D = (register stages) - 1`, so the first task that forces a register
is `D = 1`. The sketch `seq_sketch/PipeSpec.lean` proves this as a sanity theorem (`Pipelined t 1 N` equals
`Computes`'s trace property) and compiles.

**Relation to WP-S0.** `design/sequential/README.md` (written the same day) proposes `SeqTask` = a Lean state machine
`(State, init, step, obs)` plus a protocol, with `ClockedBy` replacing `Unclocked` and a claim "from every reset".
`PipeTask` is the instance whose spec state is the window of the last `D` input vectors; it needs exactly two
generalisations of `SeqTask.Follows`: **no reset port** (`rst = none` and the claim starts at *any* entry) and a **partial
observation** (`obs = none`, i.e. no claim, until the window is full, because the registers start at `x` and a pipeline
has no reset to flush them). With those two, `Pipelined` below is `Follows` unfolded, and the reduction theorem
`SeqTask.satisfiedAt_of_cycle` applies.

**Trusted statement (class `PipeTask t D`).** Ports: `t`'s inputs and outputs plus exactly one more input
`clk` (1 bit); a *single-clock* design (every edge-phase process is `@(posedge clk)` on that port, `clk` is read
nowhere else, no `initial`, no declaration initializer on a register, no latch, no `negedge`; this conjunct
replaces `Unclocked` and is a static check of the checker, `ClockedBy`); every run terminates; and in every
completed run, for every cycle `c` and every `s` with `s + D = c` whose stimulus entry drives all of `t`'s inputs
with known values `v`, the snapshot of cycle `c` carries `t.fn N v` on the outputs. The first `D` snapshots are
unconstrained (registers start at `x`). Outputs must not depend combinationally on inputs (Moore rule), which
the `D >= 1` statement already enforces semantically.

**Sketch** (`seq_sketch/PipeSpec.lean`, compiles against `SvGolf.Task`; here with `L = D + 1` in the file):

```lean
def Pipelined (t : CombTask) (L N : Nat) (stim tr : List SvState) : Prop :=
  ∀ (c s : Nat) (inp st : SvState), s + L = c + 1 → stim[s]? = some inp → tr[c]? = some st →
    ∀ v, HoldAll inp (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)
def PipeSatisfiedAt (t : CombTask) (L N : Nat) (d : Design2) : Prop :=
  Terminates2 d ∧ d ⊨₂ spec2 (Pipelined t L N)          -- + ClockedBy "clk" d, + the interface
```

**Oracle.** The combinational task's oracle with a delay line: `y_c = oracle(x_{c-D})`, `x` for `c < D`; the
`postsynth` stage already feeds ls-sv a vector sequence, so the change is to feed *sequences* and compare after
warm-up.

**Cost model.** `area = gates + flops x GE_ff`, depth = longest register-to-register or port-to-register path
(`ltp -noff`, already in the pinned script). I checked what the flow does with a 2-stage pipeline: `synth` and
`abc -g` map it to plain `$_DFF_P_` cells and `score.py` stops with "the netlist has cells the GE table does not
price: {'$_DFF_P_': 16}". The change is WP-S0's section 5.1 (price `$_DFF_P_`; add the pinned `dfflegalize` line so
that enables and resets become gates and two equivalent designs score the same); nothing new from this task.
Leaderboard: the Pareto front in (area, period), two objectives as today; `D` is fixed by the task, so there is no
third axis.

**Post-synthesis check.** ls-sv `run2` on random stimulus sequences against Verilator on the scored netlist with a
toggled clock, sampled after each rising edge before the inputs change; compare from cycle `D` on, only where
ls-sv's outputs are known; run the netlist from two different initial register contents (all 0, all 1) to catch
a design that works only from a power-up value.

**What it forces (the minimal groundwork).**
1. Trusted file `SvGolf/Seq.lean`: WP-S0's `SeqTask`/`ClockedBy`, plus the two generalisations above (or `Pipelined` as a separate
   class whose theorem links it to `SeqTask`, as `CombTask.toSeq` does).
2. Checker: `ClockedBy` check, flop pricing + `dfflegalize`, sequence-based `postsynth`, initializer ban.
3. Proof library: `Pipelined.of_stages`, a generic theorem by induction on the cycle (`Runs2.forall_of_step`,
   `Terminates2.of_invariant` are there): if the design satisfies register-transfer equations
   `R_k' = G_k(R_{k-1})` (`R_0` = the inputs) and `output = G_last(R_last)`, and `G_last ∘ ... ∘ G_1 = t.fn`, then
   `Pipelined`. The player proves only the stage equations (a `sv_seq_equations` view, or by hand first) and the
   combinational arithmetic, which for `pipe_mul` is `mul_n`'s existing proof cut in two.
4. ls-sv: nothing new for the semantics (`always_ff`, `<=`, one edge per cycle exist in `Sem2`); the tactics need an
   edge-process view where reads of registers are not ordered by rank.

**Effort: M to L** (3 to 4 days with the shared groundwork, which Rung 2 reuses).

**Risks.** (1) The convention above: a reader sees "latency 2" for one extra register; name the task by `D`.
(2) Clock hygiene is the whole defence: ls-sv runs every edge process once per cycle whatever the clock holds
(`SvGolf/Task.lean`, "A clock that never ticks"), so a design with `always_ff @(posedge clk)` and `clk`
undriven or gated looks right in ls-sv and is `x`/dead in silicon; `ClockedBy` plus the Verilator comparison
with a real clock are the two layers. (3) Declaration initializers: ls-sv honours them, synthesis drops them;
banned for sequential tasks. (4) Retiming by tools: Yosys does not retime in this flow, so the cut is the
player's choice, which is the point.

**Cheating and spec-bug coverage.** Comb designs are caught by `D >= 1`; a longer or shorter pipeline fails the
exact-delay statement for some stimulus; a latch or a gated clock is refused (`pr-always-latch` later,
`ClockedBy`, and unpriced `$dlatch` cells fail the scorer closed). The spec is the combinational spec, so the
cross-check is whatever validated it (for `mul`: the Lean `fn_eq_mul` bridge).

**Appeal: 4/5.** The first task with a retiming game; it reuses every combinational task; and it is the cheapest
way to put flops, clocks and the period metric on the board without any protocol.
