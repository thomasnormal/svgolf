# What a design may contain today, and what is planned (read off the repo on 2026-10-30)

Sources: `svgolf/PROVING.md` section 4 (the v1 fragment), `PLAN2.md` (tracks T1 tactics, T2 ls-sv coverage,
T6 sequential), `docs/sv-refusals.json` (register ids and `value_rank`), `SvGolf/Task.lean`
(`CombTask`: `Interface`, `Unclocked`, `Terminates2`, `Computes`), `LeanModels/Sv/Sem2.lean`
(`cycleStep2`: apply inputs, settle, reset pass, edge pass, NBA commit, settle).

"Proof fragment" means what the `sv_structure` / `sv_equations` / `sv_cover` tactics read, so that a
reference proof is a page and not a thousand lines. Everything the checker accepts but the tactics refuse
still has a by-hand route (`CombTask.satisfiedAt_of_comb`, CombLib), which is how `fdiv16` is meant to go.

| construct | proof fragment today | planned (owner, when) | register id / note |
|---|---|---|---|
| continuous `assign`, `& \| ^` trees over accesses and known-bit literals | yes | | |
| `~`, `!` | no ("unary operator") | WP-G, week 2 | with `?:` |
| `~^` (xnor) | no | T2 day 2 | `ex-xnor`, rank 4 |
| `?:` | no | WP-G | |
| `always_comb` bodies: blocking assigns, `if/else`, constant `case`, no latch, no self-read | no | WP-G (first fragment), then T2 | `pr-*`; designs fail at `sv_structure` today |
| block-local temporaries in `always_comb` | no | T2 day 3 | `ld-localdecl`, rank 3 |
| procedural `for` with accumulators | no | T2 day 3 to 4 | `st-for`, rank 1 |
| constant / helper functions | no | T2 day 4 | `ex-user-call`, rank 2 |
| `$countones` and friends | no (and banned with `+`) | T2 day 4 | `ex-builtins`, rank 5 |
| `casez` wildcards | no | T2 day 5 | `st-casez`, rank 6 |
| `unique` / `priority` | refused by the source gate | T2 day 6, with an obligation encoding | `st-cond-qual`, rank 7 |
| size casts `N'(x)`, 2-state `bit`/`int` ports, signed | no | T2 day 6 to 7 | `cv-explicit` 9, `dc-2state` 10, `dc-signed` 11 |
| word-level `+ - == < <= >> <<` | no (the ban on `+ - *` makes gate-level adders the norm) | WP-B2, days 5 to 7, "highest risk" | fallback: gate-level |
| generate `for`, step `g++` / `g = g + 1` (two deep, mixed bodies) | yes | genvar `i = i + 1` accepted 10/30 (L1; strides and parameter amounts stay loud) | `le-generate-genvar-step` |
| generate-`if` / `case` inside or around loops | no ("conditional generate inside a generate loop") | not scheduled | `ge-unconditional`; prefix adders and column-wise Dadda need it |
| scalar, 1-D, 2-D packed `logic` declarations, bounds affine in parameters | yes | 3-D packed no | |
| unpacked arrays, run-time indexed writes | no | later | `dc-unpacked`, `st-assign-target`; a register file or FIFO memory needs them |
| bit / part / row selects with affine constant indices; part-select and row targets | yes | | `W*i` (two variables) is not affine: a 2-D packed array is how lane arithmetic is expressed |
| dynamic (run-time) index | refused | later (power-of-two arrays are x-safe) | `sel-dyn-*` |
| concatenation, `'0`/`'1` fills | yes (replication `{N{x}}` not listed: use a loop) | | |
| `localparam int/integer` from literals, parameters, `+ - *` by a literal, `/ %` by a positive literal | yes (WP-F) | `% W` by a parameter, `$clog2`: not scheduled; **WP-F2 proposed here** (the Keccak round needs `c % W`) | PROVING section 4 |
| module instances / hierarchy | refused (`sv_structure` cannot read the family) | WP-I, design only | `Hier2` exists in ls-sv; recursion is `le-recursion`, rank 14 (Karatsuba, bitonic sort) |
| `always_ff`, `<=`, `posedge clk` | **refused by the task statement** (`Unclocked`); ls-sv models one cycle per stimulus entry (`cycleStep2`), the clock port itself is not modelled | WP-S0 note, then T6 spike | `pr-event-list`, `pr-edge-*`, `pr-nested-wait` ("the sequential layer") |
| async reset, `negedge`, latches, several clocks | no | after the sequential layer | `pr-always-latch`, `le-instance-clock`; the cycle model cannot even see sync vs async reset |
| declaration initializers on regs | ls-sv honours them (`initState2`) | a sequential task must refuse or quantify over initial states | else a design uses power-on values synthesis drops |

Checker side that every task inherits (README "Rules"): the source gate (no directives, attributes,
pragmas, `unique`/`priority`, x/z digits outside casez items), the `fourstate` stage (no constant or run-time
select out of range, no undriven/multi-driven/looping net), per-task operator banlist (pyslang front check plus
Yosys backstop), the proof (comparator with the three standard axioms, `leanchecker` replay), the pinned Yosys
flow (area in NAND2 equivalents: NOT 0.667, NAND/NOR 1, AND/OR/ANDNOT/ORNOT 1.333, XOR/XNOR 2, MUX 2.333;
depth `ltp -noff`), and the `postsynth` simulation comparison of ls-sv against the scored netlist. Any
flip-flop or latch in the netlist makes scoring fail today: a sequential task needs the table extended.

Three observations that drive the task choices below:

1. **The fragment is a bitwise-gate fragment.** Word-level arithmetic is reached through gate-level adders
   (`ripple_row`, `fullAdder_arith` in CombLib), which the `add` and `mul` references already do. A task whose
   spec contains `+` but whose banlist forces gates (ChaCha, SHA-256, Speck) is in reach NOW; a task that wants
   `+` allowed waits for WP-B2.
2. **Fixed-size tasks have no "for all N" requirement** (`fdiv16` is the precedent), so they can finish with
   kernel `decide`; they are cheap to prove and expensive to golf, which is the right way round.
3. **Anything indexed by `W*i`, `i % 5`, `2^k` or `c % W` is outside the fragment as written.** Tasks
   are therefore designed around the workarounds the references found: flat 2-D packed arrays, heap or tape
   indexing, doubled vectors for rotations, `localparam` atoms (PROVING sections 8 to 10).
