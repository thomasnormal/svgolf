# WP-RB0 / G2: the three first targets

> **Correction (WP-RB1, 2026-11-01).** This note was written while `bv_decide` was allowed in svGolf submissions. It no longer is:
> `svgolf/check.py` has `BV_DECIDE_SUPPORTED = False` (changelog 0.1.379, the maintainers: "let's not support external solvers for now").
> Every "`bv_decide`" step below is therefore a HAND BitVec proof today (`BitVec.toNat` bridges with `omega`, per-bit `simp`/`decide` at the
> concrete width, the core `BitVec` lemmas, `bv_omega`-style normalization): the 32-bit three-vector facts are the expensive ones, and the
> day estimates below (marked "guess") should be read as lower bounds for those steps. Nothing else in the note depends on the solver.

Chosen from the census (`CENSUS.md`, `census.json`) by DEPTH REACHED in the pipeline, among combinational blocks with a trusted spec that
already exists in `LeanModels.Rv` (the ISA model: `aluSem`, `branchSem`, `decode`, `expandC`, `immI..immJ`). The statements are in
`g2/G2Specs.lean` (typechecked, with sanity `decide` examples; nothing is proved). All "measured" claims are from the census run
(`out/final4`, Lean batch G); costs marked (guess) are not measured.

Every target below goes through a WORKED-AROUND variant of the real file today (a deterministic transformation of the fetched text,
`census_extract.py: modernize/type_implicit_ports` plus, for the branch comparator, one hand edit); the first column of the second table says
which register rows that transformation stands for. None of the three loads as written.

## What the census says about the candidates

| candidate (spec) | as written | best variant | deepest stage reached (measured) | what stops it |
|---|---|---|---|---|
| `hazard3_branchcmp` (`Rv.branchSem`) | extracts, 3 Unsupported (`dc-net-z`); loader refuses first (`le-const-context`: config parameter default) | `@wa3` | **`sv_equations?` accepted** | `dc-net-z` / `ld-init-expr` (nets), `le-const-context` (hazard3_config.vh) |
| `biriscv_decoder` (`Rv.decode` + families) | 9 Unsupported (`dc-net-z`); loader refuses (`ld-init-expr`) | `@wa3` | **`sv_equations?` accepted** | same two rows (`wire`, typeless ports) |
| `biriscv_alu` (`Rv.aluSem`) | 1 Unsupported (`pr-event-list`); loader refuses (`ld-init-expr`) | `@wa3` | loads clean; `sv_structure?` REFUSED: "always_comb block with several statements" | S1b gate d (multi-statement `always_comb`) |
| `cv32e40p_compressed_decoder` (`Rv.expandC`) | extracts CLEAN, loads, lowered design loud (`le-param-package`: `cv32e40p_pkg::OPCODE_*`) | none needed | tactics REFUSED (same several-statement rule) | `le-param-package` + gate d |
| `cv32e40p_popcnt`, `cv32e40x_popcnt`, `cv32e40x_alu_b_cpop` (core `BitVec.cpop`) | extract and load CLEAN | none needed | `sv_structure?` recognized; `sv_equations?` REFUSED | multi-dimensional packed arrays (`logic [15:0][1:0]`) in `sv_equations` (`tl-sv-structure-fragment`) |
| `ot_prim_secded_inv_39_32_dec`, `_72_64_dec` | typeless ports refused by the loader | `@wa3` | loads clean; `sv_structure?` (lowered) recognized, `sv_equations?` REFUSED | multi-window `always_comb`; constant part-select write |
| `cv32e40p_ff_one`, `cv32e40x_ff_one` | extract and load CLEAN | none | `sv_structure?` REFUSED | `$clog2` in a localparam |
| `rocket_alu`, `rocket_rvc_expander` | top instantiated elsewhere (`--top` fails); then `wire`/typeless | `@wa3` (sliced) | load clean; tactics REFUSED | cast/width conversion in an expression; legacy part select |

## Target 1: `hazard3_branchcmp` (Hazard3, Apache-2.0), spec `Rv.branchSem`

Block: `hdl/arith/hazard3_branchcmp.v` at `Wren6991/Hazard3@8af992930f71`, 41 lines of logic. Ports `cir[31:0]`, `op_a`, `op_b` (`W_DATA` bits), `cmp`.
`cmp = cir[14] ? lt : op_a != op_b`, `lt` = signed or unsigned less-than from the sign bits and `op_a - op_b` (bit 13 selects unsigned);
BEQ/BNE polarity (bit 12) is applied outside the block.

Spec (`g2/G2Specs.lean`, namespace `Hazard3Branchcmp`): `cmp = bool(if cir[14] then (if cir[13] then branchSem .ltu a b else branchSem .lt a b) else branchSem .ne a b)`,
as a `CombTask` with `inputs := [cir 32, op_a 32, op_b 32]`, `outputs := [cmp 1]`, read as `task.StatementFixed (branchcmp.sem <defaults>)`
(or `Statement` over `W_DATA`, with the spec stated at 32 because `Rv.branchSem` is 32-bit). The exact Rv definitions: `LeanModels.Rv.branchSem`
(Exec.lean:111), `BranchCond.{ne,lt,ltu}`.

Measured on `hazard3_branchcmp@wa3`: slang 0 errors; extractor 0 Unsupported; `load_design_sv2` accepts; lowered design clean;
`sv_structure?` RECOGNIZED (parameters `[W_DATA]`, plain sites `diff`, `cmp_is_unsigned`, `lt`, `cmp`, no families, a three-line rank relation: `diff` and `cmp_is_unsigned` below `lt` below `cmp`);
`sv_equations?` RECOGNIZED: four Boolean equations (`eq_diff` through `XF.subBits`, `eq_lt`, `eq_cmp` through `XF.eqv`) and the obligations
`auto`, `cover` and `inputsKnown_1..3`. This is the only block of the census that reaches the equations stage.

Missing in ls-sv (what the variant stands for):
1. `wire` / `output wire` and net declaration assignments `wire x = e;` (rows `dc-net-z` and `ld-init-expr`): the variant spells them `logic x; assign x = e;`.
   Gates 25 of 79 blocks (census section 5). Cost (guess): M. The cheap sound fragment is "every bit of the net has exactly one continuous driver", a driver-coverage check.
2. `hazard3_config.vh` brings ~60 parameters into the module header and one default (`PMP_HARDWIRED`, a replication) is refused by the loader (`le-const-context`):
   the variant hand-replaces the two includes by `parameter W_DATA = 32` (the one hand edit of the census). Cost (guess): M for replication/concatenation in
   parameter defaults (8 blocks), or S if the block is verified through a wrapper that fixes the configuration.
3. Through the svGolf checker only: the `include`s are refused by the source gate. With ls-sv alone (`extract.py --top ... -I hdl`) nothing is needed.

Plan: (a) `sv_structure (rank := ...)` for `CombDesign` and `Acyclic` (four sites, rank `diff`, `cmp_is_unsigned` < `lt` < `cmp`); (b) `sv_equations` in the settled-state lemma
of `CombTask.satisfiedAt_of_comb`; (c) the arithmetic: bridge `XF.subBits`/`XF.eqv` at width 32 to `BitVec` subtraction and equality (a three-vector 32-bit goal after the bridge, to be proved by hand since `bv_decide` is not supported, see the correction above) giving `cmpOf`. Estimate (guess): 1-2 days once 1 and 2 are in or the source is pre-flattened.

## Target 2: `biriscv_decoder` (ultraembedded/riscv, BSD-3-Clause), spec `Rv.decode`

Block: `core/riscv/riscv_decoder.v` at `ultraembedded/riscv@7ae6f803e3`, 236 lines: `invalid_o`, `exec_o`, `lsu_o`, `branch_o`, `mul_o`, `div_o`, `csr_o`, `rd_valid_o`
as OR-trees of `(opcode_i & MASK) == PATTERN` over ~60 instructions (macros of `riscv_defs.v`, pulled in by `-I core/riscv`).

Spec (namespace `BiriscvDecoder`): a `RelTask` (the relational twin of `CombTask`, 20 lines, not in SvGolf today) stating COMPLETENESS against the ISA model:
for every word `w` and every `i` with `Rv.decode w = some i`: `invalid_o = (valid && isMulDiv i && !enable_muldiv)`, `exec_o = isExec i` (the `.alu` family: OP, OP-IMM, LUI, AUIPC),
`lsu_o = isLsu i` (`.mem`), `branch_o = isBranch i` (`.branch` or `.jump`), `mul_o`/`div_o` by `MulDivOp` under `enable_muldiv_i`, `csr_o = isSystem i || invalid || fault`,
`rd_valid_o = rdValid i`. Definitions used: `LeanModels.Rv.decode`, `decodeTable` rows, `Instr.{alu,mem,branch,jump,mulDiv,system}`, `MulDivOp`, `SysOp.csr`.
The converse is NOT claimed: the block accepts `lwu` (mask 0x707f), `sfence.vma` (0xfe007fff) and `sret`/`uret` (ERET mask 0xcfffffff) that `Rv.decode` rejects; a second
theorem would enumerate exactly those words, and the first attempt at the proof may find more differences (that is the point of the target).

Measured on `biriscv_decoder@wa3`: loads clean; `sv_structure?` and `sv_equations?` RECOGNIZED (plain sites `invalid_w`, then one per output; the equation of `invalid_w` is an OR of ~60
masked equalities, `XF.eqv` over 32-bit `opcode_i & const`).

Missing: the same two rows as Target 1 (typeless Verilog-2001 ports and `wire x = e;`), nothing else. Plan: each `mask/value` pair of the RTL against the `decodeTable` row it corresponds to
(about 60 `decide`-sized constant facts on 32-bit masks), then a case split over `Rv.decode` by the row found first; no solver needed unless the first-match order matters. Estimate (guess): 3-5 days,
most of it the table correspondence.

## Target 3: `biriscv_alu` (same repository), spec `Rv.aluSem`

Block: `core/riscv/riscv_alu.v`, 207 lines, ports `alu_op_i[3:0]`, `alu_a_i`, `alu_b_i`, `alu_p_o` (all 32-bit), a 5-stage barrel shifter written as muxes, add/sub, logic, two comparators.

Spec (namespace `BiriscvAlu`): `alu_p_o = match opOf? op with | some o => aluSem o a b | none => a` where `opOf?` maps the block's op codes (1 `sll`, 2 `srl`, 3 `sra`, 4 `add`, 6 `sub`,
7 `and`, 8 `or`, 9 `xor`, 10 `sltu`, 11 `slt`; everything else is the RTL's `default:` arm, the result is operand a). A total function, so a plain `CombTask`, read as `StatementFixed riscv_alu.sem`.
Definitions used: `LeanModels.Rv.aluSem` (Exec.lean:47) with its `<<< (b.extractLsb' 0 5)` shift convention, which is what the RTL's five muxes on `alu_b_i[4:0]` compute.

Measured on `biriscv_alu@wa3`: loads clean (lowered design has no Unsupported node); `sv_structure?` and `sv_equations?` REFUSED: "site `plain#1`: always_comb block with several statements
(outside the first fragment: write one if/else tree that assigns the target on every path)". The body assigns nine shift temporaries before the `case`.

Missing: (1) the two Verilog-2001 rows (variant: `always @(a or b or ...)` -> `always_comb`, typeless ports typed, `wire x = e;`); (2) the tactics' multi-statement `always_comb`
(the survey's "S1b gate d", in flight; also blocks `cv32e40p_compressed_decoder` and the `prim_secded` decoders). Cost (guess): (2) is M and shared; (1) is the Target 1/2 cost.
The workaround for (2) at source level is to rewrite the body as one `case` with the shifts as functions of `alu_b_i` (no temporaries), which changes the text under proof.

Plan: after gate d, `sv_structure`/`sv_equations`, then per-op lemmas (one per op over two 32-bit vectors, ten small goals; the shifter against `aluSem .sll/.srl/.sra` is the heavy one:
a 5-stage mux network equals `<<<`/`>>>`, an induction over the five stages by hand now that `bv_decide` is out). Estimate (guess): 3 days after gate d.

## Why not the others first, and the next in line

* `cv32e40p_compressed_decoder` (`Rv.expandC` is documented as the spec of this very RTL at `FPU = 0`; relational statement `Cv32e40pRvc` in `G2Specs.lean`) is the best FOURTH target: it
  needs `le-param-package` (`cv32e40p_pkg::OPCODE_*`, which also frees 5 other SystemVerilog blocks) and gate d. The `illegal_instr_o`/`instr_o` don't-care is why the statement is relational.
* `cv32e40p_popcnt` (+ the two cv32e40x popcounts) is the zero-blocker smoke test of the whole chain (spec `BitVec.cpop`; the 32-bit equality is a hand proof or `BitVec.cpop`'s own bitblast lemmas now), blocked only by multi-dimensional packed arrays in `sv_equations`.
  It validates the pipeline but does not exercise `LeanModels.Rv`.
* `ibex_alu`/`cv32e40p_alu`/`hazard3_alu` (the popular ALUs) need loops, explicit casts and width conversions on top of the above: not first.

## Statements (copied from `g2/G2Specs.lean`; the file is the normative text)

```lean
def cmpOf (cir a b : BitVec 32) : Bool :=
  if cir.getLsbD 14 then (if cir.getLsbD 13 then branchSem .ltu a b else branchSem .lt a b) else branchSem .ne a b
def Hazard3Branchcmp.task : CombTask where
  inRange _ := True
  inputs _ := [("cir", 32), ("op_a", 32), ("op_b", 32)]
  outputs _ := [("cmp", 1)]
  fn _ := fun (cir, a, b, ()) => (BitVec.ofBool (cmpOf cir a b), ())

def BiriscvAlu.task : CombTask where
  inRange _ := True
  inputs _ := [("alu_op_i", 4), ("alu_a_i", 32), ("alu_b_i", 32)]
  outputs _ := [("alu_p_o", 32)]
  fn _ := fun (op, a, b, ()) => (match opOf? op with | some o => aluSem o a b | none => a, ())

def BiriscvDecoder.rel (valid fault mdE : BitVec 1) (w : BitVec 32) (inv ex ls br mu dv cs rdv : BitVec 1) : Prop :=
  ∀ i, decode w = some i →
    inv = b (valid == 1#1 && isMulDiv i && mdE == 0#1) ∧ ex = b (isExec i) ∧ ls = b (isLsu i) ∧ br = b (isBranch i) ∧
    mu = b (mdE == 1#1 && isMul i) ∧ dv = b (mdE == 1#1 && isDiv i) ∧
    cs = b (isSystem i || inv == 1#1 || fault == 1#1) ∧ rdv = b (rdValid i)
```

What the statements do not say (honest list): they say nothing about 4-state inputs (the `CombTask` shape quantifies over fully known inputs, as the existing tasks do);
Target 1's spec is at `W_DATA = 32`; Target 2's is one direction; Target 3 treats op codes outside the ten as the RTL does (a documented RTL behavior, not an ISA fact).
`LeanModels.Rv` is a hand-written model validated by its own `#guard` battery and `tools/rv-oracle`, not by these RTL blocks: a mismatch found by a proof is a finding about one of the two.
