# CFRAG: how much real RTL the E fragment covers

**Status label:** measurement. Agent M, WS4, 2026-11-03, branch `arch-measure`.
- Instrument: [`CombFragCensus.lean`](CombFragCensus.lean), run with `lean --run` against a copy-on-write clone of arch-loop `d7af3dac`'s build.
- Driver: [`combfrag_census.py`](combfrag_census.py).
- Data: [`combfrag.json`](combfrag.json).

**Question (the lead's item).** L's `CombFragE` (arch-loop `d7af3dac`) gives every `always_comb` body that passes
`Stmt2.combOk d` a meaning over E-core-0 (`Stmt2.sem_run`). `Stmt2.claims` is a hypothesis of that meaning for qualified
cases. How many of the `always_comb` processes in the RB0 census blocks and the X8 cores (ibex, cv32e40p, cva6) does it
reach, at the default point?

## Method

**Corpus.**
- RB0: the 82 census blocks, taken as is. The envelopes are those of the Day 6 re-run. arch-loop `d7af3dac`'s extractor is
  that same file.
- X8: every distinct module of the three cores' lrm4 points, `ibex_core@default`, `cv32e40p_core@default` and
  `cva6@cv32a6_imac_sv32+WT` (from `x8.json`).
  - Each module is extracted as its own top from its core's file list, so it is measured at its OWN default parameters.
  - Defines go in a first source file of `` `define `` lines, because the extractor has no `-D`.
  - 103 of 104 modules extract. `cva6` itself fails inside the extractor with `ValueError: Exceeds the limit (4300 digits)
    for integer string conversion`. That is an extractor finding: CPython's integer-to-string limit, hit by a huge constant.
- Overlap: 25 top modules are in both RB0 and X8. Their load verdicts agree in all 25 cases. The overall row drops the X8
  copy.
- A secondary RB0 row uses Day 6's best variant per block: `@wa3` > `@wa2` > `@wa`, whichever loads first, else as is.

**Sources (MEASURED).**
- 375 pinned files match their sha256 in `rb0/files.tsv` and `x8_files.tsv`, with 0 mismatches.
- The envelopes' own 11,583 `source_files` sha256 entries also match the files on disk, with 0 mismatches.
- The sources are read by pyslang only, under `python3.12 -I`.

**Loading.** As `runner2.lean` loads, at the default point:
1. `loadHierString`;
2. the defaults cross-check;
3. `PDesign.atPoint`, all `none`;
4. the `int32` agreement;
5. `instantiateG2`.

Instances are removed from the generate items, so each module counts its own processes once, in its own row. This is
per-module coverage, not whole-core elaboration. X8 has the whole-core picture.

**Per `always_comb` process (MEASURED in one `lean --run`):**
- `combOk`: L's own `Stmt2.combOk d`.
- `qual`: the body holds a `unique`/`unique0`/`priority` case.
  - `Stmt2.claims` is a state-dependent `Prop`. What can be decided per process is whether it is trivially `True`, and that
    is what `qual` reports.
- `why`: the first construct that fails, by a walk that mirrors `combOk`.
  - Checked against `combOk` on every process: `why_agrees_with_combOk` is true everywhere.

**Per design (MEASURED):**
- `single`: the design is exactly one `always_comb` process, the shape of `activate_single`.
- `all_four`: `AllFour (Elab.ofDesign2 d)`, a hypothesis of `sem_run` and `activate_single`. `Elab.ofDesign2` keeps
  `d.decls`.
- `design_has_unsupported`: `Design2.hasUnsupported`, the test of svGolf's `design` stage.

**Cost (MEASURED).** One slot acquisition per pass. 185 designs take 44 to 47 s, and the 93 variants take 39 to 42 s.
Every pass is one short acquisition, under a minute of Lean time.

## Results (MEASURED)

### Processes

"In text" counts the `always_comb` processes in the top module's envelope, in processes and generate bodies, each written
once, whether the design loads or not.

| group | designs | load | `always_comb` in text | of which in designs that do not load | loaded | **in the fragment** | in fragment, qualified | out |
|---|---|---|---|---|---|---|---|---|
| RB0, as is | 82 | 41 | 298 | 107 | 191 | **183** | 3 | 8 |
| X8 ibex | 16 | 4 | 68 | 66 | 2 | **2** | 0 | 0 |
| X8 cv32e40p | 23 | 11 | 74 | 54 | 20 | **12** | 1 | 8 |
| X8 cva6 | 64 | 4 | 134 | 134 | 0 | **0** | 0 | 0 |
| X8, three cores | 103 | 19 | 276 | 254 | 22 | **14** | 1 | 8 |
| **overall, deduplicated** | **160** | **52** | **499** | **290** | **209** | **195** | **4** | **14** |
| RB0, best Day 6 variant | 82 | 42 | 300 | 107 | 192 | 185 | 3 | 7 |

- No process in any row holds a `case inside`.
- The qualified processes in the fragment are `ibex_branch_predict` (1), `ibex_multdiv_slow` (2) and
  `cv32e40p_load_store_unit` (1).

**Written `always_comb` against lowered `always @*`.** The extractor lowers `always @*` and complete sensitivity lists to
`AlwaysComb` (`always_star_lowered`). In this corpus every loaded design is all one or all the other, which the driver checks.

| overall, deduplicated | loaded | in the fragment |
|---|---|---|
| written `always_comb` | 30 | 21 (70 %) |
| lowered from `always @*` (biriscv, picorv32, serv, vexriscv) | 179 | 174 |
| of which `vexriscv_min_core`, one generated file | 159 | 159 |

### Out of the fragment, by first failing construct (overall, deduplicated, 14 processes)

| first failing construct | processes | where |
|---|---|---|
| `ParamRef:package`: a package parameter inside the body (assigned value 3, `if` condition 2, case pattern 2) | 7 | cv32e40p `controller` 3, `if_stage` 2, `compressed_decoder` 1, `int_controller` 1 |
| undeclared name | 3 | biriscv `issue` (`issue_ra_value_w`, `pipe_load_e2_w`), `regfile` (target `ra0_value_r`) |
| `CallExpression` | 1 | biriscv `exec` |
| `ConversionExpression:Explicit` | 1 | el2 `dec_gpr_ctl` |
| `ForLoopStatement` | 1 | picorv32 `pcpi_mul` |
| **target: dynamic element select** | 1 | cv32e40p `fifo` |

- **13 of the 14 carry a node the loader already marks loud.** Every one of the 13 is in a design with
  `hasUnsupported` true, so svGolf's `design` stage rejects that design before any proof. MEASURED.
  - The 3 undeclared names are declared in the envelope as `{"kind": "Unsupported", "sv_kind": "NetSymbol:net-z"}`. READ.
    So this is an envelope gap, not the fragment.
- **One process is the fragment's own boundary: a dynamic element select as a target** (`Lhs2.staticWin` is `none`). It is
  in `cv32e40p_fifo`, a design with no loud node.
  - In the best-variant row there is a second one, `biriscv_issue@wa3`. Once Day 6's modernization makes its net-z wires
    `logic`, its next failing construct is a dynamic element select target.

### Designs (overall, deduplicated, 52 that load)

| | designs |
|---|---|
| hold at least one `always_comb` | 29 |
| every `always_comb` in the fragment | 19 |
| and `hasUnsupported` false (pass the `design` stage at the default point) | 13 |
| and `AllFour` | 13 (`AllFour` holds for all 52 loaded designs) |
| only `assign` and `always_comb` processes, with every hypothesis above | 5: `biriscv_alu` and the four `ot_prim_secded` encoders and decoders |
| exactly one `always_comb` (`activate_single`'s shape), with every hypothesis above | 4: `ot_prim_secded_39_32_enc`, `_inv_39_32_dec`, `_inv_39_32_enc`, `_inv_72_64_dec` |

The 13 are:
- `biriscv_alu`, `_divider`, `_multiplier`;
- `cv32e40p_alu_div`;
- the four `ot_prim_secded` blocks;
- `serv_compdec`, `serv_decode`;
- `vexriscv_min_streamfifo`;
- cv32e40p `aligner` and `load_store_unit`.

The best variant adds `hazard3_onehot_priority@wa2`, which is single-process.

### Load refusals, weighted by the `always_comb` processes they hide (overall, deduplicated, 290 of 499)

| refusal (first one the loader reports) | designs | `always_comb` in text |
|---|---|---|
| a package-scoped parameter (CVA6Cfg struct default, a package width) | 35 | 98 |
| an `initial` process (also inside a generate) | 26 | 68 |
| a package enum type or member in a parameter default (ibex `RV32M`, `BaseIsa`, ...) | 11 | 55 |
| a block-local declaration in a procedural block (`LocalDecl`) | 15 | 45 |
| a constant construct the loader does not fold (replication, concatenation, call, ...) | 10 | 10 |
| an untyped parameter or localparam (expression-width rule) | 5 | 7 |
| an enum with unrecoverable packed dimensions | 2 | 5 |
| a system task call | 1 | 2 |
| `always_latch` | 3 | 0 |

For the X8 cores alone, 254 of their 276 `always_comb` (92 %) are in modules that do not load. For cva6 that is all 134.

Note on `ibex_alu`: it refuses at its own top, with its `RV32B` enum default, both in RB0 and in X8. L's two ibex_alu blocks
(`d7af3dac`) are local slices against local specs (READ: the commit message), not the module at its default point.

### `writtenBeforeRead`

**Pending.** L's check has not landed: arch-loop's head is `d7af3dac`, and `git log --all -S writtenBeforeRead` is empty
(MEASURED). The instrument emits one JSON object per process, so the check becomes one more field (`b.writtenBeforeRead d`)
and one more report column, plus one acquisition of about 45 s.

## Reading (JUDGED)

- **On real RTL the E fragment is not what binds.**
  - Of the `always_comb` processes that load, 93 % are in it (195 of 209). For the written `always_comb` alone it is 70 %
    (21 of 30).
  - Of the 14 that are not, 13 already fail the `design` stage through a loud loader node.
  - The fragment's own boundary costs one process here: a dynamic element select target, two in the best-variant view.
    That is the construct to add first if the fragment grows.
- **Loading binds.**
  - 58 % of the `always_comb` processes in the text (290 of 499) are in designs that do not load. In the three X8 cores it is
    92 %.
  - The largest single lever is package parameters, on both sides of the line. They are the first load refusal by hidden
    `always_comb` (98), and inside loaded bodies `ParamRef:package` is 7 of the 14 that fall out. Unlocking them is a loader
    and envelope item, not an E item.
  - Next come `initial` (68), package enums in parameter defaults (55), and block-local declarations (45). The last is an
    `always_comb` body construct, so the fragment would have to admit it too.
  - The text counts are upper bounds: a design that loads after a fix still has to pass `combOk`.
- **Design-level reach is small.** 13 designs pass the body, `design`-stage and `AllFour` tests on every `always_comb`.
  - Only 4 have the single-process shape that `activate_single` covers today.
  - The other 9 hold `always_ff` or several `always_comb` processes. They need the E route's multi-process composition,
    which this census does not price.
  - For comparison, Day 6's today's route on RB0 as is: 20 blocks pass the `design` stage, 8 are recognized by
    `sv_structure?`, 6 are accepted by `sv_equations?`. Day 6 loads through `load_design_sv2` with instances in place, so
    the two funnels are close but not identical.
- **The corpus is skewed.** 159 of the 195 in-fragment processes are one SpinalHDL-generated file (`vexriscv_min_core`),
  lowered from `always @*`, in a design that is loud (3 net-z nets). Read the per-design rows before the per-process
  percentage.

## Reproduction

`SP` is the scratchpad and `OUT` = `$SP/arch/m-cfe`. The scripts are the ones in this directory.

```
python3.12 -I combfrag_census.py verify --rb0-src $SP/wprb0/src/files --rb0-tsv svgolf/design/real-world-sv/rb0/files.tsv \
    --x8-src $SP/arch/m-src --x8-tsv x8_files.tsv
python3.12 -I combfrag_census.py extract-x8 --repo <arch-loop worktree> --x8-src $SP/arch/m-src --out OUT -j 3
python3.12 -I combfrag_census.py batch --rb-out $SP/arch/m-rb/out --out OUT --json OUT/batch_all.json
(the 93 `@wa*` variants of $SP/arch/m-rb/out as OUT/batch_rbwa.json, group rb0-wa)
slot: lean --run CombFragCensus.lean OUT/batch_all.json > OUT/cfe_all.txt     (LEAN_PATH: the d7af3dac build clone)
slot: lean --run CombFragCensus.lean OUT/batch_rbwa.json > OUT/cfe_rbwa.txt
python3.12 -I combfrag_census.py report --txt OUT/cfe_all.txt --batch OUT/batch_all.json \
    --wa-txt OUT/cfe_rbwa.txt --wa-batch OUT/batch_rbwa.json --x8-extract OUT/x8_extract.json --json combfrag.json
```
