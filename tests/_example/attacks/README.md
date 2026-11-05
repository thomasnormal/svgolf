# Attacks on task `_example`: where ls-sv and Yosys read one text differently

Each design here computes `a & b` in ls-sv's reading (and in every IEEE
simulator's) while Yosys's reading of the same text is something else.
`tests/run.py` runs each through `check.py --unproved` (none has a proof) and
expects the stage `tests/expected.json` gives (`attacks`); where it says
`postsynth_alone`, it also runs the post-synthesis check
(`check/postsynth.py`) with the source gate and the `fourstate` stage
bypassed, to show what that sampling check would do on its own. That run is in
the LIGHT mode (`check.py`'s default) unless the entry says `postsynth_mode:
full`, for an attack that only the full check rejects; every other `rejects` row
is also rejected by the light mode (measured 2026-10-30), and the `numbers`
below are the full mode's.

Every known disagreement is refused STATICALLY and exactly, before any proof
is tried: the source gate refuses `unique`/`unique0`/`priority` and every
x/z literal digit outside a casez/casex item wildcard; the `fourstate` stage
(`score/fourstate.py`) refuses every other source of an x at the scoring
point (a parameter or constant with unknown bits, an out-of-range select, an
undriven net). The post-synthesis check is the backstop for the
disagreements nobody has found yet; `oob_rare.sv` shows why it cannot be the
only line: a difference on one input pair in 2^32 passes it.

| design | the construct | Yosys reads | stage | postsynth alone (measured) |
|---|---|---|---|---|
| `casex_item.sv` | `s = 1'b0; case (s) 1'bx: y = '0; default: y = a & b;` | the `x` item as matching: `y` is `x`, 0 GE | `source` (an x literal digit; before that rule it was LIVE: every stage up to postsynth passed it) | rejects every vector (4130 of 4130) |
| `zpair_or.sv` | complementary items `2'b0z`, `2'b1z` on `{a[0], b[0]}` | the z bits dropped: the two items match every input, `y = a \| b` | `source` | rejects 4132 of 4134 |
| `z_rare.sv` | `case ({a, b}) 32'hDEAD_BEEz: y = '0;` | the item matches 2^-28 of the inputs: 0 there | `source` | rejects 3 of 4133, all built from the harvested constant (its 0/1 bits, x/z bits free) |
| `zconst_param.sv` | the x/z bits inside localparams `{1'b0, 1'bz}`, `{1'b1, 1'bx}` used as case items | `y = a \| b` | `source` | rejects, failing closed: ls-sv loads the design with an unsupported node (no ports at the point), "ls-sv does not support this design" |
| `zeq_pair_if.sv` | `if ((a[1:0] == 2'b0z) \|\| (a[1:0] == 2'b1z))` | always true: `y = a \| b` | `source` | rejects 4132 of 4134 |
| `param_divzero.sv` | `localparam logic [1:0] K = 2'd1 / 2'd0;` as a case item (constant `/` is not banned) | `K` a don't-care: the item matches every input, `y = a \| b` | `fourstate` (a parameter with unknown bits; slang's `DivisionByZero`) | rejects, failing closed as `zconst_param.sv` (ls-sv does not support the constant division) |
| `undriven_mux.sv` | `logic u; t = u ? 0 : 1; if (t) y = a \| b; else y = a & b;` | `u` a don't-care resolved to `t = 1`: `y = a \| b` | `fourstate` (Yosys `check`: `u` used but undriven) | rejects 4128 of 4130 |
| `oob_select.sv` | `t = k[{1'b1, a[1:0]}] ? 0 : 1` on a 4-bit `k` (always out of range: x) | `t = 1`: `y = a \| b` | `fourstate` (a 3-bit run-time index into `[3:0]`) | rejects 4130 of 4130 |
| `oob_rare.sv` | `t = k[{rare, 2'b00}]` with `rare` true on ONE input pair (a reduction-AND detector) | `k[0]` there: `y[0]` flipped on that pair | `fourstate` | PASSES (4130 vectors): the difference is 2^-32 of the inputs and no comparison constant leads to it |
| `fn_uninit.sv` | a function-local `logic r;` that only `s = 1` assigns, returned by `f(s)`, in `if (f(a[0]))` | the unassigned `r` resolved to 1: `y = a \| b` | `design` (LATENT: no static rule sees it; ls-sv has no user function calls yet, so the design loads with an Unsupported node and the `design` stage rejects it, WP-C3, naming `CallExpression: f(a[0])`; before WP-C3 the postsynth stage failed closed with "ls-sv does not support this design". A function-call PR must add a 4-state rule for unassigned locals first) | rejects (fails closed) |
| `latch_never.sv` | an `always_latch` whose enable `a[0] & ~a[0]` is never true, read as `if (!r) y = a \| b; else y = a & b;` | the never-loaded latch resolved to `r = 0`: `y = a \| b` (21.328 GE); IEEE keeps `r` at x (`a & b`) | `fourstate` (rule (e): `proc` infers a latch for `r`, `select -assert-none t:$dlatch ...`, WP-PROC follow-up 3, 2026-11-01. LATENT before it: no other static rule sees it, the latch is a driver; ls-sv does not run `always_latch`, so the design loaded with an Unsupported process and the `design` stage rejected it, naming `ProceduralBlockSymbol:AlwaysLatch`, and still would) | rejects (fails closed) |
| `latch_star.sv` | the same latch written with `always @*` (no `proc` error, unlike `always_comb`) | the same: `y = a \| b` | `fourstate` (rule (e), as `latch_never.sv`: `proc` inferred a latch for `r`. Behind it, `design`: ls-sv runs `always @*` only under the rules R1 to R6 of docs/sv-proc-lowering.md (WP-PROC E1, 2026-11-01), and R5 refuses a block that assigns a variable on some paths only, so this one is a `TimedStatement:ImplicitEventControl` Unsupported process whose text names R5) | rejects (fails closed) |
| `func_call.sv` | a CORRECT `a & b` computed by a user function called from `always_comb` (WP-C3) | `a & b`: nothing differs | `design` (the design loads, ls-sv has no function calls, so `design.sem` carries an Unsupported node: no proof can hold; the stage names `CallExpression: both(a, b)` and the point) | rejects (fails closed: every run UNSUPPORTED) |
| `assign_func.sv` | the same function call in a continuous assignment, `assign y = both(a, b)` | `a & b` | `design` (the loud node sits in an `assign`) | rejects (fails closed) |
| `rare_mid.sv` | the `oob_rare.sv` out-of-range read, confined to about 2^-9 of the inputs (the low 9 bits of `a` equal a pattern, a reduction-AND detector) | `k[0]` there: `y[0]` flipped | `fourstate` | the FULL mode rejects 7 of 4130 vectors (all random); the LIGHT mode PASSES (256 vectors): the one attack that separates the modes, `postsynth_mode: full` in `tests/expected.json` |
| `unique_nomatch.sv` | `y = a & b; unique case (1'b1) (a[0] & ~a[0]): y = '0; endcase` | full_case + parallel_case: `y` is `x`, 0 GE | `source` (the gate refuses `unique`) | rejects every vector |
| `priority_nomatch.sv` | the same with `priority` | the same | `source` | rejects every vector |
| `unique_overlap.sv` | `unique case (1'b1) a[1]: y = a & b; a[0]: y = a | b;` | parallel_case ORs both arms where both items match | `source` | rejects 1062 of 4130 |
| `unique_rare.sv` | the overlap confined to `a[7:0] == 8'hEF && b == 16'h1234` (2^-24 of the inputs) | as above, on that region | `source` | rejects ONLY the vectors built from the harvested comparison constants (4 of 4141) |
| `unique_first_const.sv` | `unique case (1'b1) 1'b1: y = a & b; a[0]: y = a | b;` | `a & b`: benign | `source` | passes (nothing to reject) |
| `unique0_nomatch.sv` | `unique0 case` that never matches (parallel_case only) | `a & b`: benign | `source` | passes |
| `for_counter_write.sv` | `for (int k = 0; k < 2; k++) begin k = int'(a[0]); ... end` | ignores the counter write: `a & b`; simulation loops forever when `a[0] = 0` | `banlist` (the `k++` of a counter the body writes is run-time) | rejects (fails closed: ls-sv refuses the loop) |
| `for_counter_skip.sv` | `y = a & b; for (...) begin if (k == 1) y = '0; k = k + 1; end` | ignores the write, runs `k == 1`: `y = 0`, 0 GE | `banlist` (the `+` on a counter the body writes) | rejects (fails closed) |
| `array_sum.sv` | `assign y = arr.sum();` | cannot read it (Yosys 0.53) | `banlist` (the front check flags `.sum()` under a `+` ban) | not run |

So, for the decision on `unique`/`unique0`/`priority`: the post-synthesis
check alone catches a qualifier that changes the function on a reachable
input when its vectors reach that input: always for a gross violation, and
for a violation confined to a rare region only when the region is selected by
constant comparisons (the harvested vectors). It is sampling; the gate's
refusal is exact. The same holds for every x source above: `oob_rare.sv`
passes the sampling check and is refused exactly by the `fourstate` stage.
