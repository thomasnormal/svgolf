# Attacks on task `add`: where ls-sv and Yosys read one text differently

Each design here is a correct ripple adder (`a + b + cin`) wrapped in a
construct that ls-sv (and every IEEE simulator) reads one way and Yosys
another, so that the PROVED circuit computes the sum while the SCORED netlist
is something else. `tests/run.py` runs each through `check.py --unproved`
(none has a proof) and expects the stage `tests/expected.json` gives
(`attacks`), and, for `postsynth_alone`, the post-synthesis check
(`check/postsynth.py`) with the source gate and the `fourstate` stage
bypassed.

| design | the construct | ls-sv / 4-state simulators (Icarus 12, measured 10/28) | Yosys | stage | postsynth alone (measured) |
|---|---|---|---|---|---|
| `z_case_item.sv` | `case (cin) 1'bz: zero; default: sum` | case items compare by `===`: `cin` is never `z`, so the sum | the `z` item matches as a don't-care: outputs `x`, 0 GE | `source` (a z literal digit). Before that rule it was LIVE: the gate, the banlist and the design stage passed it, and ls-sv computes the sum on every vector checked, so only a proof (not written) stood between it and a 0 GE entry | rejects every vector (4132 of 4132) |
| `zpair_add_rare.sv` | complementary items `2'b0z`, `2'b1z` on `{a[0], cin}`, their arms the sum with `s[0]` flipped on ONE input pair (`a = 16'hAAAA`, `b = 16'hB6DB`, a reduction-AND detector); default: the sum | no item matches: the sum everywhere (provable) | the two items match every input: the netlist is wrong on that pair (found by the round-2 review) | `source` | PASSES (4136 vectors): 2^-32 of the inputs, no comparison constant leads to it. The gate's exact refusal is what stops it |
| `eqx_x.sv` | `(cin === 1'bx) ? '0 : sum` | Icarus 12: never `x`, so the sum; ls-sv: no `===` yet, every run UNSUPPORTED | folds to the constant 0 (0 GE) | `source` (an x literal digit) | rejects: "ls-sv does not support this design" (fails closed; a `===` feature PR would make it provable) |
| `eqx_undriven.sv` | `(u === cin)` with `u` undriven | Icarus 12: `x === 0/1` is false, so the sum; ls-sv: UNSUPPORTED | the undriven net is a don't-care: 0 GE | `fourstate` (Yosys `check`: `u` used but undriven) | rejects, as `eqx_x.sv` |

Every one of them is a bug report, not an exploit: see README.md, "Rules".

## Not Yosys splits: designs the slang DRIVER rejects

The five `slang_*.sv` designs are the reference ripple adder (`tasks/add/reference/add_n.sv`) with one construct that
slang's ANALYSIS pass reports as an error and that `Compilation.getAllDiagnostics()` (what the banlist and `fourstate`
stages read before 2026-11-01) does not contain. Decided 2026-11-01: "slang reports a program illegal" means the full
slang driver, parse, elaboration AND analysis errors. The banlist front check (`score/slangdriver.py`) now reads them;
`check.py --unproved` rejects each at the stage `banlist`, with slang's own message (`tests/expected.json`
`message_contains`). They are not Yosys/ls-sv splits: the reading is the same everywhere that matters, the program is
just illegal.

| design | slang's report | before the rule |
|---|---|---|
| `slang_two_always.sv` | `multiple-always-assigns`: two `always_comb` writers of `cout` (IEEE 1800-2023 9.2.2.2, 9.2.2.4) | both blocks drive the same value, so Yosys `check` and `fourstate` passed it; refused only at `design`, by the Lean `driversOk` guard |
| `slang_mixed_assign.sv` | `mixed-var-assigns`: `assign cout` plus `always_comb cout` (6.5) | the same: passed `fourstate`, refused at `design` by the Lean guard |
| `slang_input_assign.sv` | `cannot assign to input port 'cin'` (23.3.3.2) | refused at `fourstate`, only because Yosys `check` found two drivers |
| `slang_initial_comb.sv` | `multiple-always-assigns`: `initial cout = 0` plus an `always_comb` writer (9.2.2.2; Xcelium `*E,MULAXX`) | Yosys accepts the netlist; refused only at `design`, because the loader has no `Initial` process kind, so a day `initial` is admitted it would have passed every stage |
| `slang_always_notime.sv` | `'always' procedure does not advance time` (9.2.2.1) | Yosys reads a wire; refused only at `design` (the extractor's `ProceduralBlockSymbol:NoEventControl`) |

`score/tests/fourstate/analysis_*.sv` are the same shapes for the `fourstate` stage and for `banlist.py --selftest`
(`analysis_point.sv`: the verdict is per parameter point, clean at N = 4, `multiple-always-assigns` at N = 2).

## Not attacks: the checker's advisory checks

Five more designs live here because `tests/run.py` runs them the same way (`check.py
--unproved`, stage `unproved`, `tests/expected.json` `attacks`), but they exercise the
checker's ADVISORY output, which never changes a stage (README.md, "Checking"):

| design | what it is | what the advisory check says |
|---|---|---|
| `wrong_carry.sv` | a ripple adder whose carry cell drops the propagate term, `(a & b) \| (c & a)` | ls-sv and the netlist agree, so every stage before the proof passes it. The functional smoke check (`tasks/add/oracle.py`) finds 3245 of 4132 vectors wrong: `stages.postsynth.functional` and ONE `warnings` line |
| `mux_carry.sv` | a CORRECT adder with a `?:` carry | `--tactics`: `in_fragment: true` since WP-G S2 (it was `false`, "site `g_bit#1`: conditional expression `?:` (outside the v1 fragment)"); the oracle agrees on every vector |
| `localparam_carry.sv` | a CORRECT adder that reads a `localparam int M = N - 1;` in an index | `--tactics`: `in_fragment: true`. It was the refusal example ("local parameters are outside the v1 fragment") until the localparam extension of the tactics (PROVING.md section 4: a `localparam int`/`integer` of constant arithmetic over the parameters, `+ - *` and `/ %` by a literal, is one more named constant); kept as its regression. The oracle agrees on every vector |
| `localparam_clog2.sv` | a CORRECT adder with a `localparam int L = $clog2(N + 1);` (the prefix baselines' level count) | `--tactics`: `in_fragment: true` since ls-sv admits a `$clog2` `int` localparam (it was `false`, "localparam `L`: `$clog2` is outside the v1 fragment ..."); kept as its regression. The oracle agrees on every vector |
| `localparam_intdiv.sv` | a CORRECT adder with a 2-state `localparam int H = (N + 1) / 2;` | `--tactics`: `in_fragment: false`, "localparam `H`: a 2-state `int` localparam initialised by `/` or `%` is squashed ... declare it `localparam integer`" (the 4-state form is accepted); the oracle agrees on every vector |

The `tactics_reference` entries of `tests/expected.json` (for `add`, and for `mul`, which has no
`attacks/` directory) have no design file of their own: they point at the proved references and
are the other side, `in_fragment: true`, message `ok`.

`hier_fa.sv` is not an attack: a correct ripple adder written with one `full_adder` module instance per bit. The design and score stages accept it (measured: 112.0 GE, depth 33, exactly `add_n`), and the `--tactics` advisory (`hier_fa` in `tests/expected.json`) answers that the `sv_comb` tactics do not summarize module instances (WP-I step I0).
