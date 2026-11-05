# Experiments behind the sequential design note (WP-S0, 10/30)

Everything below was run for real on 10/30 on this tree (branch `svgolf-prep`, ls-sv at the working
tree of that morning, Yosys 0.53, Verilator, Xcelium 24.03-s004). Scratch designs and the
scripts are in the work directory of the study, not in the repo; each experiment says what to rerun.
Lean was run through the one-job slot wrapper from the repository's root with `lake env lean <file>`; no
library file was edited.

## E1. A plain synchronous design through the real pipeline

Designs (all parametric in `N`, written in the obvious way):

```systemverilog
module cnt #(parameter int N = 8) (input logic clk, rst, en, output logic [N-1:0] q);
  always_ff @(posedge clk) if (rst) q <= '0; else if (en) q <= q + 1'b1;
endmodule
module shreg #(parameter int N = 8) (input logic clk, rst, d, output logic [N-1:0] q);
  always_ff @(posedge clk) if (rst) q <= '0; else q <= {q[N-2:0], d};
endmodule
module pipe2 #(parameter int N = 8) (input logic clk, rst, input logic [N-1:0] a, b, output logic [N-1:0] y);
  logic [N-1:0] s1;
  always_ff @(posedge clk) if (rst) begin s1 <= '0; y <= '0; end else begin s1 <= a ^ b; y <= s1; end
endmodule
```

`svgolf/check/envelope.py` (the source gate, then the pinned extractor, probe points `N=1;N=4;N=8`)
accepted every one (exit 0). `load_design_sv2` accepted them and `name.sem N` is a `Design2` with
one `alwaysFF "clk" body` (`cnt`: `ifStmt rst (nbaAssign q 0) (some (ifStmt en (nbaAssign q (q + resize N 1'b1)) none))`).
`run2` (fuel 256) results, `N = 4`, snapshot of `q` per cycle:

| design, stimulus | σ_src | σ_rev |
|---|---|---|
| `cnt`: rst=1 / en=1 / en=1 / en=0 / en=1 | `0000 0001 0010 0010 0011` | the same |
| `cnt`, the same with `clk` never bound in the stimulus | `0000 0001 0010` (3 entries) | |
| `cnt`, the same with `clk := 0` in every entry | `0000 0001 0010` | |
| `cnt`, no reset (rst=0, en=1 twice) | `xxxx xxxx` (x + 1 = x) | |
| `cnt`, rst=1 then rst=`x` with en=1 | `0000 0001 0010` (`if (x)` takes the else branch) | |
| `shreg`, rst; d=1; d=0; d=1 | `0000 0001 0010 0101` | |
| `pipe2` `(s1, y)`, rst; a=0101,b=0011; a=1111,b=0001; a=b=0 | `(0000,0000) (0110,0000) (1110,0110) (0000,1110)` | the same |

So the NBA discipline (sample, then commit) is right; the clock value is not used at all.

`fsm1` (enum typedef + `case` FSM + `assign busy = (st == RUN)`) loads and runs correctly
(`IDLE -> RUN -> DONE -> IDLE`, one `busy` pulse). `memarr` (`logic [7:0] mem [0:3]`, `if (we) mem[wa] <= wd`,
`assign rd = mem[ra]`) loads: the array is flattened to four 8-bit declarations `mem[0..3]` and the
dynamic NBA index is the usual select write (an x or out-of-range index writes nothing).

## E2. What is accepted, refused, or wrong

| scratch design | extractor / envelope.py | `load_design_sv2 ... .sem` | `run2` |
|---|---|---|---|
| `dead_clk`: `logic clk; always_ff @(posedge clk) y <= a & b;` (clk never driven) | accepted | loads, `[alwaysFF(clk)]` | `y` = `a & b` in every cycle (`[1]`, `[0]`): THE EXPLOIT. `decide (Unclocked dead_clk.sem) = false`: `Unclocked` is what blocks it today |
| `two_clk`: `@(posedge clk1) a <= d; @(posedge clk2) b <= a;`, `clk2` never driven | accepted | loads | `b` follows `a` in the SAME cycle: both processes run every cycle |
| `gated`: `assign g = clk & en; always_ff @(posedge g) q <= d;` with `en = 0` | accepted | loads | `q = 1` after the cycle (a real simulator: `q` stays x). Charter "single-clock gap" |
| `async1`: `@(posedge clk or negedge rst_n)` | accepted | `alwaysFFR(clk, rst_n)` | pin3 semantics; `clk = 0` cycles still capture `d` (`0000 0101 0111 0000 0011`) |
| `negedge1`: `always_ff @(negedge clk)` | accepted | process is `UNSUPPORTED(SignalEventControl:NegEdge)` | loud: `unsupported process 'SignalEventControl:NegEdge'` |
| `nest_clk`: `always_ff @(posedge cnt[1])` | accepted | `UNSUPPORTED(SignalEventControl:clock)` | loud |
| `init1`: `logic [N-1:0] r = '0; always_ff ... r <= r + 1` | accepted | `UNSUPPORTED(ProceduralBlockSymbol:initialized-variable: always_ff writes 'r', which has a declaration initializer ...)` | loud |
| `init2`: `initial q = '0;` | accepted | REFUSED at load: `unknown process kind "Initial"` | n/a |
| `latch1`: `always_latch if (en) q = d;` | accepted | `UNSUPPORTED(ProceduralBlockSymbol:AlwaysLatch)` | loud |
| `latch2`: `always @* if (en) q = d;` | accepted | `UNSUPPORTED(TimedStatement:ImplicitEventControl)` | loud |
| `latch3`: `always_comb if (en) q = d;` | accepted | `[alwaysComb]` | latch behavior, `[1] [1]` after `en` falls (Yosys `proc` refuses it: "Latch inferred", `fourstate` rule (e)) |
| `blk_ff`: two `always_ff`, blocking `q1 = d`, `q2 = q1` | accepted | loads | σ_src `[[1,1],[0,0]]` vs σ_rev `[[1,x],[0,1]]`: the race is visible to the `∀ σ` quantification |
| `two_writers`: two `always_ff` writing `q` | accepted | REFUSED at load: `PortConn:driver` ("written on one bit by an always_comb/always_ff procedure and by another process") | n/a |
| `delay1`: `q <= #1 d` | accepted | body `Unsupported IntraAssignment:publication-or-context` | loud when reached |
| `sync_in_comb_nba`: `always_comb q <= a` | accepted | `[alwaysComb]` | `unsupported: nonblocking assignment to 'q' inside always_comb is outside the cycle semantics` |
| `mealy`: `r <= x; assign y = r + x;` | accepted | loads | snapshot `y_c = r_{c+1} + x_c` (`0000 0110 1000`): the post-edge comb value uses the NEW register and the HELD input |

Nothing out of the one-clock `always_ff` tier is silently dropped; the single silent wrongness is the
CLOCK ITSELF (rows 1 to 3 and the gated clock): ls-sv ignores its value. The refusal register says
the same: `sg-unclocked` (svGolf), the charter "single-clock gap", `le-instance-clock`, `pr-clock-wide`,
`pr-edge-other`, `pr-edge-iff`, `pr-event-list`, `pr-nested-wait`.

## E3. What the checker does with clocked designs today (`check.py ... --unproved`, task `add`)

* `add_n` whose outputs go through registers on an undriven internal `clk`: rejected at stage
  `fourstate` ("Wire add_n.\clk is used but has no driver", Yosys `check -assert`). The undriven clock
  is therefore ALSO caught by the 4-state stage today, not only by `Unclocked`.
* The same with `clk` as an extra input port: passes `fourstate` and `design`, rejected at `score`:
  "the netlist has cells the GE table does not price: {'$_DFF_P_': 17}".
* A clock tied to a constant (`assign clk = 1'b0;` or `1'b1;`, `always_ff @(posedge clk) y <= a & b`):
  Yosys removes the flip-flop and writes `assign y = 1'hx;` (0 GE, depth 0). `fourstate` does not see it
  (no undriven wire); only `Unclocked` (proof side) and the post-synthesis "unknown constant in the
  netlist" rejection catch it.
* `postsynth` runs ONE fresh one-cycle `run2` per vector (`svgolf-eval`) and a 2-state Verilator model of
  the netlist (`--x-initial 0`); it has no clock, no reset sequence and no multi-cycle trace.

## E4. Yosys with flip-flops (scoring flow `canon.ys` + `svgolf.ys` as pinned, then variants)

`cnt` at `N = 16`:

| flow | cells | `ltp -noff` |
|---|---|---|
| as pinned (`synth -flatten`, `abc -g ...`) | `$_SDFFE_PP0P_` x16 (enable and synchronous reset ABSORBED into the flip-flop), AND 13, NAND 1, NOT 1, XNOR 1, XOR 14 | 15 |
| plus `dfflegalize -cell $_DFF_P_ 01` before `abc` | `$_DFF_P_` x16, ANDNOT 14, AND 15, NAND 1, NOR 31, XOR 1 | 17 |
| async-reset version, as pinned | `$_DFFE_PN0P_` x16, AND 13, NAND 1, NOT 1, XNOR 1, XOR 14 | 15 |
| async-reset version with `dfflegalize -cell $_DFF_P_ 01 -cell $_DFF_PN0_ 01 -cell $_DFF_PN1_ 01` | `$_DFF_PN0_` x16, AND 24, NAND 4, NOR 4, XNOR 4, XOR 10 | 9 |

The path printed by `ltp -noff` starts at a flip-flop output (`0: \q [0]`) and ends at a flip-flop input
(`ff: \q [14]`): it is the longest register-bounded combinational path, which is the clock-period
proxy. Yosys also optimizes across registers (a 3-stage 8-bit pipeline with a constant mask came out
with 20 flip-flops, not 24: constant bits are removed). ABC's result varies a lot with the flip-flop
cell set (the async case dropped from 15 to 9 levels), so the flip-flop legalization MUST be part of
the pinned script. Verilator simulates the written flip-flop netlist: the `cnt` netlist of the pinned flow
(`$_SDFFE_PP0P_` x16) plus Yosys's `simcells.v`, built with `verilator --cc --exe --build --x-initial unique`
and a 12-line C++ harness (reset in cycle 0, `en` pattern 1,1,0,...; `Verilated::randReset(2)`,
`+verilator+rand+reset+2`) gives `q = 0 1 1 2 3 3 4 5`: the clocked postsynth harness of section 5 of
`README.md` needs nothing the toolchain does not already do. An initialized flip-flop (`logic r = 1'b1;
always @(posedge clk) r <= d;`) loses its init value in the netlist the pinned flow writes (the `$_DFF_P_`
instance has no init), while `dfflegalize -cell $_DFF_P_ x` stops with `ERROR: FF ... cannot be legalized:
initialized D flip-flops are not supported`.

## E5. Xcelium 24.03-s004 (4 sessions, files kept with the study)

* A declaration initializer on a variable that an `always_ff` writes, or an `initial` assigning such a
  variable, is an elaboration ERROR (`xmelab: *E,MULAXX Multiple drivers to always_ff output variable`).
  Consistent with ls-sv's loud `initialized-variable` process and the register's `pr-init-var` (never).
* Derived and multiple clocks (`t_derived2`: a launch flop `l` toggling on `clk`, capture flops on
  other clocks, 10 ns clock, sampled at each negedge):

  | capture flop clocked by | value captured | reading |
  |---|---|---|
  | `clk_n`, a clock derived by an NBA (`clk_n <= ~clk_n` on `posedge clk`) | the NEW `l` every time (`cap_n = 1` on every line) | a clock produced in the NBA region ticks a delta cycle late and sees committed data |
  | `clk_a`, `assign clk_a = clk` | the OLD `l` (`0 1 0 1`) | a continuous-assign copy ticks in the Active region: zero skew |
  | `clk2`, an independent clock with the same phase | the OLD `l` (`0 1 0 1`) | independent zero-skew clocks sample old values |
  | `g = clk & en` (gated), `en` raised in the low phase | counter `0 0 1 2 3 4` | a gated clock counts only enabled edges; ls-sv's single-clock model would count every cycle |

  So the cycle model is exact for ONE clock (and for several clocks that are input ports with
  coincident or interleaved edges and ideal sampling); a clock produced by NBA logic needs the
  delta-cycle scheduler (R1), and a gated clock needs clock edges as events.
* Time zero (`t_start`): a clock `x -> 1` and an async reset `x -> 0` at the start; the reset register is
  `0000` (pin3), the unreset register stays `xxxx`.
