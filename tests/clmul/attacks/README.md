# Attacks and styles for task `clmul`

Everything here but `div_zero_x.sv` (an attack, below) is an ADVISORY entry of `tests/expected.json` (`attacks`, `advisory: true`), run by `tests/run.py`
through `check.py --unproved` and rejected (or reaching `unproved`) at the recorded stage. The sources of the
styles are real implementations found on GitHub (`tasks/clmul/README.md`, "How people write clmul"); the files here
are WRITTEN FOR THIS TASK in each style, correct for every `N` (Verilator, `tests/clmul/validate/sim.py`), not
copies of anyone's code. They document what a contestant who writes the circuit the natural way meets today.

| design | style | stage | what stops it |
|---|---|---|---|
| `proc_nested_for.sv` | nested procedural loops, `p[i+j] ^= a[i] & b[j]` (cv32e40x, CORE-V-WALLY) | `fourstate` | the loop counter is a run-time index (`st-for`: ls-sv does not load procedural loops) |
| `proc_shift_xor.sv` | `if (b[i]) p = p ^ (a << i)` in an `always_comb` (fontamsoc, effanem, akerlund) | `fourstate` | the same |
| `func_oldstyle_xor.sv` | the same as a Verilog-2001 function | `source` | its loop counter `integer i` is declared outside the loop header (source gate item 7, the procedural-loop stopgap; before it, `fourstate` stopped it at the same counter), and the call is `ex-user-call` |
| `func_shift_xor.sv` | the same as an `automatic` function with `return` | `banlist` | the scorer's own Yosys frontend refuses `return` |
| `wally_chain.sv` | CORE-V-WALLY's chain through `S[WIDTH*i+j]` | `fourstate` | the same, and a non-affine index |
| `gen_always_step.sv` | one `always_comb` per shift-and-add step in a generate-for, `z[i] ^= h[i-1]` (Marian) | `design` | compound assignment (`st-compound`) |
| `gen_local_column.sv` | a column temporary declared in a generate block | `design` | generate-local declaration |
| `inst_karatsuba_1level.sv` | one Karatsuba level on three instances of a procedural base (effanem) | `fourstate` | the base's loop counter |
| `inst_karatsuba_rec.sv` | recursive parameterized Karatsuba (JC-S) | `extract` | a self-instantiating top (`le-recursion`) |
| `gen_word_pp_chain.sv` | generate-for word partial products `b[i] ? a << i : '0`, XOR chain (ibex, rv32imafb-core) | `unproved` | accepted up to the proof; the tactics refuse the `'0` fill as an arm of `?:` (the replication is read since WP-B2 gate 4c, the genvar shift amount since 4b, the run-time shift since 3a) |
| `gen_pp_zerofill.sv` | the same with the zero-fill loop starting at `N` | `unproved` | the tactics' generate-for header needs a literal start |
| `reduce_xor_column.sv` | `p[k] = ^(a & window)` per column | `unproved` | the tactics refuse the indexed part select `+:` |
| `gen_size_cast.sv` | the explicit size cast `(2*N-1)'(a) << i` on packed 2-D arrays | `design` | `ConversionExpression:Explicit` (`cv-explicit`) |
| `gen_unpacked_pp.sv` | parameter-sized unpacked `pp [N]` / `acc [N+1]` arrays (ibex) | `design` | `decl 'pp': unpacked array storage outside E (UnpackedDecl:memory)` |
| `gen_mask_replication.sv` | `(aw << i) & {(2*N-1){b[i]}}` (VeeR, scarv) | `unproved` | accepted up to the proof; since WP-B2 gate 4c the tactics read it (`sv_structure`, `sv_equations`) |
| `verilog2001_wire.sv` | `input wire` / `output wire` / `wire [N-1:0][N-1:0] r` | `design` | `decl 'a': unrecoverable packed dimensions` (`dc-net-z`) |
| `always_star_rows.sv` | an `always @*` per row in a generate-for | `design` | `TimedStatement:ImplicitEventControl` |
| `inst_karatsuba_1level_gen.sv` | one Karatsuba level on instances of a generate-array base | `unproved` | accepted up to the proof; the tactics refuse module instances (WP-I) |
| `div_zero_x.sv` | NOT a style and NOT advisory: an ATTACK (the universal-correctness audit, 2026-11-06), the reference array plus `q = 1'b1 / ~rare`, a zero divisor on one input pair in 2^32 | `banlist` | every task bans run-time `/ % **` since 2026-11-06; before, every stage passed it, the full post-synthesis check included (`postsynth_alone: passes`), while ls-sv's `if (q)` took the else branch at the x and the netlist flipped `p[0]` there |

and three older entries: `tactics_reference` (the reference is inside the `sv_comb` tactic fragment and the oracle agrees on
every post-synthesis vector), `functional_or_accumulate` and `functional_reversed_p` (the negative designs pass every
stage that needs no proof and the oracle reports the mismatch in one `warnings` line).

The shared defences (the source gate, `fourstate`, the banlist, post-synthesis) are attacked by `_example`, `add`
and `aes_sbox`; `clmul` inherits them unchanged. Scores of the styles that reach the scorer (not pinned): the
schoolbook forms 770.9 to 775.6 GE at `N = 16`, `inst_karatsuba_1level` 650.6, `inst_karatsuba_rec` 625.0.
