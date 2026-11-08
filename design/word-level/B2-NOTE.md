# WP-B2: word-level operators in the `sv_comb` tactics (design note)

Status: DESIGN, 2026-10-31, branch `svgolf-prep` (844b1344). Documents only: nothing in `LeanModels/`,
`extractors/`, `harness/`, the checker, the tests or the tasks was edited; no Lean, `lake` or Xcelium process was
started. Labels as in `design/always-comb/README.md`: READ (a source file, `file:line` given), MEASURED (I ran it;
listed in the appendix), PLANNED (a proposal). Names marked NEW do not exist in the tree.

## 0. Summary

1. **The bottom half of B2 is built; the top half is the work.** `Expr2.xfWidth`/`xfBits`
   (`CombKnownBits.lean:668`, `:734`) already cover unsigned `+ - * == != < <= > >= << >>`, `&& ||`, `?:`,
   reductions, concatenation, slices and `resize`. Their Boolean bit functions are proved equal to the four-state
   `LVec` operations (`add_ofBoolFn :492`, `lt_ofBoolFn :524`, `eqLogical_ofBoolFn :550`, `shl_ofBoolFn :562`,
   `shr_ofBoolFn :581`), `Expr2.evalPure2_ofBoolFn :1154` turns known reads into a known value, and
   `CombKnown.settled` (`CombKnownThm.lean:294`) needs no change. Missing is the layer between a SystemVerilog
   expression and that machinery: the recognizer (`rdsOf?`, `CombView.lean:632`), the skeleton `Sk`
   (`CombEqBase.lean:69-218`), the shape theorems (`CombEqShape.lean`) and the glue from bit equations to `BitVec`.
2. **Recommended v1:** unsigned `+ -`, `== != < <= > >=`, `<<`/`>>` (literal amount, and any amount at no extra cost),
   concatenation as an operand, implicit zero-extension (`PExpr.resize`). Not in v1: signed forms, `*`, parameter-valued
   constants, reductions (WP-G S2 already plans them), `/ % **` (never).
3. **Equations stay Boolean bit functions** over `st.boolAt n (lo + k)` (the faithful form the tactics already hand
   out); the `BitVec` form comes from a NEW plain-Lean module `CombWord`, not from a new tactic.
4. **B2 alone does not make `tasks/fdiv16/reference/fdiv16.sv` loadable, nor does WP-G S2 alone.** Of its 52 `assign`s: 12 need neither, 17 only
   B2, 5 only S2, 18 both; the `always_comb` table needs S2 (section 6).
5. **Size:** `+` end to end 3.5 to 5 agent-days (2 to 4 on the Lean slot); v1 8 to 10 (5 to 7 on the slot).
   Highest risks: the context width threaded through `Sk.bit` (six files) and `Resize` markers being metadata of the
   default parameter point (section 5.3).
6. **Pins:** eight SV snippets (section 4); the width rules were witnessed on Verilator (all 256 pairs of 4-bit
   operands, 18 outputs, 0 mismatches), but run-time shifts have no Xcelium pin at all.
   Decisions for the maintainers: section 7.

## 1. What the tactics accept today (a)

| layer | accepted | refused, with the message the contestant sees | where |
|---|---|---|---|
| declarations | scalar, 1-D, 2-D packed `logic`, affine bounds | initializer; "signed or 2-state (outside the v1 fragment ...)"; 3-D | `CombView.lean:500-520` |
| processes | continuous `assign`, target whole / bit / 1-D cell / row / 2-D cell / part / row part (`Acc :355`); `generate for` two deep; `always_comb` (second chain) | "concatenation target" (`:662`); other processes (`:677`) | `siteOf? :664`, `tgtOf? :653` |
| right-hand side | sized literal; `& \| ^` (`gateOf :450`) over accesses and literals; a concatenation of literals and ONE access per part; a whole-RHS fill | "operator `+` is not a bitwise gate" (`:636`); unary (`:601`); `?:` (`:602`); replication (`:604`); reduction (`:605`); anything else "(constant, cast, width conversion or system call)" (`:607`): `PExpr.int`, `paramRef`, `genvarRef`, `.resize`, `.cast` | `leafRd? :590`, `rdsOf? :632` |
| `always_comb` (WP-G) | ONE window; `if/else` tree; leaves = the right-hand sides above; conditions = gate trees of 1-bit accesses | `case`, latch, second window, richer condition (`CombProc.lean:440`) | `CombProc.lean:430-458` |

So `assign t = a + b + cin;` fails at the first `+`, and the `Resize` markers slang puts around its operands
(section 5.1) would be refused next.

**The equation pipeline** (READ); each row is a place a new operator must be added:

| stage | object | where |
|---|---|---|
| reads, skeleton | `PDesign.summary` (`CombView.lean:994`) builds the `Summary` (`:978`) of `TSite`s, each with `rds` (accesses in leaf order); `Sk := lit \| rd \| gate \| cat (List Part) \| fill`, `Part := lit \| rd`; `skT`/`skRhs` consume `rds` with leaf counts `cnt`; `fragG`/`fragOk` allow concat and fill at the root only | `CombView.lean:437`, `CombEqBase.lean:69-132` |
| equation | `Sk.bit σ dw rd : Nat → Bool`; `EqSite`: `st.boolAt n (lo+k) = (skRhs ..).bit σ' dw st.boolAt k` for `k <` window width | `CombEqBase.lean:157`, `CombEqThm.lean:173` |
| instantiation shape | `Sk.low σ tw : Expr2` must EQUAL what `fitExpr2` builds: `gate_shape :164`, `parts_shape :228`, `rhs_shape :276`, `proc_shape :367` | `CombEqShape.lean` |
| width contract | `Sk.WidthOk` (every operand EXACTLY as wide as the target), `WidthObl`, a decidable instance for flat netlists | `CombEqBase.lean:192`, `CombEqThm.lean:148`, `CombEqPlain.lean:29` |
| x-free | `low_xfWidth :432`, `low_xfBits :460`: the lowering is in the XF fragment and `xfBits = Sk.bit` | `CombEqShape.lean` |
| reads promised | `RdOK :303`, `inst_rd :582`, `rhs_ok :626` | `CombViewThm.lean` |
| producer, names | `eq_of_summary :334`, `KnownSite :180`; `eq_<sig>_<block>_<pos>`, aliases `eq_<sig>_<k>` (`stableAliases :247`); equations printed by `simp only` with `Sk.bit`, `accBit`, `catBit` in the set | `CombEqThm.lean`, `CombEqTactic.lean:148, :219, :247` |
| `always_comb` | `PSk := leaf (sk : Sk) \| ite (c : Sk) .. \| blk`; leaves REUSE `rhs_shape`, `low_xf*`; conditions use `cond_shape :337`, `skT_selfWidth :276`, a COPY of `gate_shape` (`G22-NOTE.md` section 3) | `CombProcEq.lean:51-440` |

A new `Sk` constructor therefore costs five definitions (`bit`, `low`, `WidthOk`, `leaves`, `knownB`), the instance
`Sk.decWidthOk`, two x-free theorems and four PExpr-indexed theorems (`rdsOf?_len`, `skT_leaves`, `gate_shape`,
`inst_rd`). Because `PSk.leaf` wraps an `Sk`, an operator in an `always_comb` right-hand side then comes almost free (the leaf counts `rcnt` follow `cnt`); in an
`if` condition it needs the `cond_shape` copy extended (S2 work as well).

Building blocks that exist (READ): `instExpr2_add`/`_sub` (`Gen2.lean:947`, `:953`; hypothesis `(ctxOpWidth2 ..).getD w
≤ w`), `fitExpr2_of_rigid_ne` (`:1017`), `fitExpr2_binary` (`:1029`). No equation lemma exists yet for the
comparison, shift, `.resize` (`Param2.lean:923`) or reduction arms of `instExpr2`.

## 2. Notation and width classes

For an access `x` with window `(n, lo, w)`: `bits x := fun j => st.boolAt n (lo + j)`, `X := XF.bv w (bits x)`, the
value read from the state (`SvState.boolAt_ofBitVec :1443`, `SvState.lookup_eq_ofBitVec_bv :1470`). For the target
window `(m, lo', tw)`: `O := XF.bv tw (fun k => st.boolAt m (lo' + k))`. `XF.val` is `CombLib.bfVal` (same recursion,
`CombKnownBits.lean:393`, `CombLib.lean:22`; the bridge is NEW, one induction).

The width classes are `PExpr.ctxPropagates` (`Param.lean:818`). **Context-determined** (operands are extended to
the context first): `+ - * / % ** & | ^ << >> <<< >>>`, unary `- ~ +`, `?:`. **Self-determined** (a wider context
zero-extends the result through a `Resize` marker): `== != < <= > >= === !==`, `&& ||`, `!`, reductions;
concatenation parts too (`instParts2 :1026`). Signedness lives in the envelope (`s<`, `signedResize`), not in the
skeleton, and three independent guards keep every signed form out today: the extractor refuses signed ports and
sign-extending conversions in symbolic mode (MEASURED on P8: 8 `Unsupported` nodes, `PortSymbol:signed`,
`ConversionExpression:width`; register row `dc-signed`), the recognizer refuses signed declarations
(`CombView.lean:505`) and casts (`:607`), and the x-free fragment returns `none` for `resizeSigned`, `scmp`
(`CombKnownBits.lean:709-711`).

## 3. Operator by operator (b)

`tw` is the target window's width; "bit equation" holds for `k < tw`.

### 3.1 The rules

| op | width rule in ls-sv | four-state rule in ls-sv | bit equation (known regime) | `BitVec` form (glue) |
|---|---|---|---|---|
| unsigned `+` | operands zero-extended to `tw` (`Param2.lean:866-879`); an operand WIDER than `tw` is not narrowed first (an x above `tw` would collapse the sum): sum at the operand width, then `.resize tw` | any x/z bit of either operand makes the WHOLE result x (`LVec.add`, `Basic.lean:302`; section header `:291`) | `XF.addBits wl (bits l) wr (bits r) k = (val bl wl + val br wr).testBit k` (`CombKnownBits.lean:441`; natural widths suffice, zero-extension does not change `val`) | `X.setWidth tw + Y.setWidth tw` |
| unsigned `-` | as `+` | as `+` (`Basic.lean:308`) | `XF.subBits` (`CombKnownBits.lean:445`) uses `2^max wa wb`: call it with the CONTEXT width, not the natural widths (`a - b` from 4-bit operands into 5 bits is `(a-b) mod 32`, bit 4 is 1 iff `a < b`; MEASURED) | `X.setWidth tw - Y.setWidth tw` |
| `==` `!=` | self-determined, 1 bit; operands extended to the larger self-determined width `wo` (`Param2.lean:880-884`, `selfWidth2 :521`); into a wider target slang wraps the result in `Resize` (MEASURED) | `LVec.eqLogical` (`Basic.lean:459`): 0 on a known mismatch EVEN with x elsewhere, else x if any x/z, else 1; `!=` negates (`:469`) | bit 0: `XF.eqv wo bl br` (`CombKnownBits.lean:435`; negated for `!=`), bits `k>0`: `false` | `(BitVec.ofBool (decide (X.setWidth wo = Y.setWidth wo))).setWidth tw`; `LVec.eqv_iff_bv` (`:540`) EXISTS |
| `<` `<=` `>` `>=` | as `==` | `relOp` (`Basic.lean:435-450`): any x/z bit gives x | bit 0: `decide (val bl wo < val br wo)` (`CombKnownBits.lean:756-767`; no same-width condition in `xfWidth :685`) | `(BitVec.ofBool (X.setWidth wo < Y.setWidth wo)).setWidth tw` |
| `<<` `>>` | left operand extended to `max(tw, own)` BEFORE the shift, result truncated to `tw`; amount self-determined (`Param2.lean:839-853`, `ctxTrunc2 :666`) | `Basic.lean:369`, `:377`: unknown amount gives all x; amount `>=` width gives 0; x/z bits of the left operand MOVE, they do not collapse | `shlBits` (`CombKnownBits.lean:456`) `= decide (val g wr ≤ k) && f (k - val g wr)`; `shrBits w ..` (`:460`), `w = max tw wl`; literal amount `c`: `decide (c ≤ k) && f (k - c)` (NEW `XF.val_lit`) | `(X.setWidth w <<< c).setWidth tw`, `(X.setWidth w >>> c).setWidth tw` |
| concat operand | parts self-determined (`Param2.lean:922`), width = sum | bits move, no collapse (`Basic.lean:606`) | `catBit` (`CombEqBase.lean:149`), `Expr2.catBits` (`CombKnownBits.lean:800`) | `X ++ Y` |
| reductions | operand self-determined, 1 bit (`Param2.lean:1005`) | partial: `\|` is 1 given a known 1 even with x elsewhere (`Basic.lean:282-289`) | `XF.red` (`CombKnownBits.lean:268`) | `Known2.lean:568-600` |

Verilator witness for every width claim above except reductions: all 256 pairs of 4-bit `a`, `b`, an 8-bit `c`, a
4-bit variable amount; 18 outputs, among them `a << 1` into 5 bits keeping the carried-out bit, `a << 4` into 5 bits,
`a & (a == b)` with only bit 0 surviving, `a - b` into 5 bits wrapping at 32, `a + b` into 3 bits truncating, mixed
8/4-bit `==`, `<`, `+`, variable shifts: 0 mismatches. Verilator is 2-state, so this witnesses the known regime
only; the four-state column rests on `Basic.lean` and the pins of section 4.

### 3.2 Knownness consequence

Nothing new is proved. The operators are already in the fragment `xfWidth` accepts, so `XFree` holds, and the only
inputs-known fact needed is the one `CombKnown.reads_known` (`CombKnownThm.lean:280`) already supplies: every read
window of the lowered right-hand side is known. Output known: all `tw` bits for `+ - << >>`, concat, ternary; bit 0
(the rest is literal zero) for comparisons. Read windows needed: both operand windows, ALL bits, for `+ - == <`
(one unknown bit poisons a sum); the left and the amount window for shifts (an unknown amount makes everything x).
So operand reads must stay EXACT windows (`slice (ident n) lo w`, `accExpr`, `CombEqBase.lean:169`), which they are;
`CoverObl` (`CombEqThm.lean:161`) then already says what is needed. No new `cover_k`, `inRange_k`, `bitRead_k` or rank
obligation arises: operands are accesses.

### 3.3 Obligation added: the width contract

Only `Sk.WidthOk` changes (the existing `width_k` goal: `intros; omega`, or decided for a flat netlist):

| node | contract per instance (`Acc.win` widths) |
|---|---|
| bare leaf under `+ -` (as under `& \| ^` today) | `= tw`: otherwise `fitExpr2` inserts a `.resize` the skeleton does not model, and `width_k` is false |
| leaf under a `Resize` marker (`Sk.ext`), under `+ -` | `≤ tw`, the hypothesis of `instExpr2_add`; wider takes the `.resize tw (sum at ow)` arm (`Param2.lean:870-875`), refused in v1 with a message |
| operands of `== < ..` | none: each is fitted to `wo` (the narrower gets `.resize wo`) |
| marker around a width-1 result | none: lowering is `.resize tw`, `xfBits` is `decide (k < 1) && ..` (`CombKnownBits.lean:790`) |

A false contract is a loud false goal, never a silently different circuit.

### 3.4 What the contestant's proof uses (the glue)

NEW module `LeanModels/Sv/CombWord.lean` (plain Lean; imports `CombKnownBits`, `CombLib`):

| NEW lemma | statement |
|---|---|
| `XF.zext n f`, `XF.val_zext`, `XF.bv_zext` | `fun j => decide (j < n) && f j` (what `xfBits (.resize ..)` computes); `val (zext n f) m = val f n` for `n ≤ m`; `XF.bv m (zext n f) = (XF.bv n f).setWidth m` |
| `XF.bv_addBits`, `_subBits`, `_shlBits`, `_shrBits` | `(∀ k<w, g k = XF.addBits w f w f' k) → XF.bv w g = XF.bv w f + XF.bv w f'`, and the same for `-`, `<<`, `>>` |
| `XF.ult_iff`, `XF.bv_cat` | `decide (val f w < val g w) = true ↔ XF.bv w f < XF.bv w g`; concatenation of bit functions is `++` |

Promoted, not rewritten: `cadd_toNat`, `cadd_low`, `cadd_carry`, `cadd_arith` (`Comb2ConcatExample.lean:225-286`,
proved at every `N` for the hand-built `{cout, s} = a + b + cin`) are the arithmetic of the `+` glue with carry.

### 3.5 Constants, and the tactic surface

`PExpr.int` (unsized, materialized at the context width: `intLit2`, `Param2.lean:684`; `LVec.ofInt` wraps mod `2^w`,
`Param.lean:174`), `paramRef`, `genvarRef`, `sysCall` are refused today (`:607`); a sized literal is accepted. v1:
`.int v` with `0 ≤ v` as `Sk.const v` (bit `(v mod 2^tw).testBit k`, needs `tw`); parameter-valued constants
(`W-1`, `1 << (W-1)`, `$clog2`) wait for the localparam work (section 6.2).

No new tactic in v1: `sv_equations` hands out `eq_<sig>_<k>`, the glue is a lemma call. `sv_bitvec` stays reserved
(`docs/sv-comb-design.md` principle 3); option for later, after three references show the same three-line pattern:
`sv_bitvec eq_t_1 as ht` restating a named bit equation by the matching glue lemma (about 1 agent-day).

## 4. Differential pins still needed (c)

Why: the proofs are about ls-sv's reading of the design. A wrong width rule (say, not extending a shift's left
operand) would certify a proof about a circuit the netlist does not implement; only post-synthesis sampling would
notice. Already pinned in `harness/sv/xcelium_golden.json` (whether each is `XREF-MATCH` is what `diff_test2.py
--golden` reports; it needs the Lean slot, so I did not run it): `ctx_width*` (9 rows: `a + 4'd1`, `-a`,
`b - v[0+:N]`, `v[1+:N] + 4'd9` with an x above the context, `a == 4'd3`, `v < 5'd17`, `{a + 1'b1, 1'b0}`, with x/z
stimulus), `concat_add*` (3), `addsub_comb*` (3), `alu_div_w8/w32`, a few reductions. **Not covered**: no
run-time shift of a signal vector appears in `Examples/system-verilog/sem2/*/*.sv` outside parameter lines, and
`harness/sv/cases.json` has no shift row (the M0 self-check `harness/sv/shifts/shifts.sv` asserts the rules, but its
oracle is its own `PASS` line, not a trace); for the rest I read the rows above and found none, a check I did not
make exhaustive: a comparison inside a wider bitwise context, the `fdiv16` chain and concatenation-operand shapes,
operands of per-instance width (`tests/add/baselines/cmp_carry.sv`), unsized constants as operands of `+ - == <`
(`ctx_width` has one for `*`), every signed combination.

Each snippet is a module for `harness/sv/cases2.json` (source `Examples/system-verilog/sem2/<name>/`); all eight
pass `verilator --lint-only` and the pinned extractor (P8 with 8 `Unsupported` nodes, section 2).

| id | snippet | stimulus (besides small exhaustive) | pins | gate |
|---|---|---|---|---|
| P1 | `module wl_shift #(parameter int N = 4) (input logic [N-1:0] a, input logic [3:0] sh, output logic [N-1:0] y_same, y_over, v_same, output logic [N:0] y_wide, z_wide, v_wide); assign y_same = a << 1; assign y_wide = a << 1; assign y_over = a << N; assign z_wide = a >> 1; assign v_same = a << sh; assign v_wide = a >> sh; endmodule` | `a = 1x01, x101`; `sh = 4'b00x1, 4'bz000`, `sh >= N` | left operand extended BEFORE the shift; x moved, not collapsed; unknown amount all x; overshift | M3 |
| P2 | `module wl_cmp_ctx (input logic [3:0] a, b, input logic [7:0] c, output logic [3:0] y_zext, y_and, output logic y_lt48, y_eq48, output logic [4:0] y_cat); assign y_zext = (a < b); assign y_and = a & (a == b); assign y_lt48 = (b < c); assign y_eq48 = (a == c); assign y_cat = {a < b, a}; endmodule` | `a = 1x00, b = 0000` (`<` is x); `a = 0x11, c = 8'b1000_0011` (`==` is 0 despite the x) | `Resize` of a 1-bit result; zero-extension of the narrower comparison operand; partial `==` | M2 |
| P3 | `module wl_addsub_ctx (input logic [3:0] a, b, input logic [7:0] c, output logic [4:0] s5, output logic [3:0] s4, output logic [2:0] s3, output logic [4:0] d5, output logic [8:0] m9, output logic [4:0] chain5); assign s5 = a + b; assign s4 = a + b; assign s3 = a + b; assign d5 = a - b; assign m9 = c + b; assign chain5 = a + b + 1'b1 - a; endmodule` | `a = 1x01`, `b = z000` | zero-extension (not sign) of a subtraction into a wider target; truncation into a narrower; mixed widths; left-associated chain at the context width | M1 |
| P4 | `module wl_cat_operand (input logic [4:0] xa, input logic [3:0] lzb, input logic adj, input logic [4:0] ef, input logic [9:0] q, input logic inc, output logic [6:0] eoff, output logic [14:0] mag); assign eoff = {2'b0, xa} + {3'b0, lzb} + 7'd47 - {6'b0, adj}; assign mag = {ef, q} + {14'd0, inc}; endmodule` (shapes of `fdiv16.sv:111,132`) | `inc = x`; `xa` with one x bit | concatenation operands, sized padding, mixed add/sub chain | M1/M2 |
| P5 | `module wl_unsized (input logic [3:0] a, output logic [3:0] y_inc, output logic [4:0] y_inc5, output logic y_eq, y_lt); assign y_inc = a + 1; assign y_inc5 = a + 1; assign y_eq = (a == 3); assign y_lt = (a < 1); endmodule` | `a = 4'b1111`, `4'bx000` | 32-bit unsized constants as operands (`a < 1` compares at 32 bits) | M2 |
| P6 | `module wl_cmp_prefix #(parameter int N = 4) (input logic [N-1:0] a, b, input logic cin, output logic [N:0] c); assign c[0] = cin; for (genvar i = 1; i < N + 1; i++) begin : g assign c[i] = (a[i-1:0] > ~b[i-1:0]) \| ((a[i-1:0] == ~b[i-1:0]) & cin); end endmodule` at `N = 1, 2, 4, 8` | exhaustive `N <= 4`; one `x` in `b` | operands of per-instance width `i`; `~` inside a comparison operand | M2 (+S2) |
| P7 | `module wl_red (input logic [3:0] a, output logic r_or, r_and, r_xor, r_nor); assign r_or = \|a; assign r_and = &a; assign r_xor = ^a; assign r_nor = ~\|a; endmodule` | `1x00, 0x11, xxxx, 1111, 0000` | partial reductions | S2 |
| P8 | `module wl_signed (input logic signed [3:0] sa, sb, input logic [3:0] ua, output logic lt_ss, lt_su, output logic signed [4:0] s5, output logic [4:0] u5, output logic signed [3:0] sh_r); assign lt_ss = sa < sb; assign lt_su = sa < ua; assign s5 = sa + sb; assign u5 = sa + sb; assign sh_r = sa >>> 1; endmodule` | all sign pairs; one x | signed compare; mixed is unsigned (§11.8.1); sign extension even into an unsigned target; `>>>`. The extractor refuses it today: waits for `dc-signed` | signed step |

Procedure (not run; `docs/sv-xcelium-reference.md` section 3): add rows and sources; per row
`python3 harness/sv/xcelium_batch.py prepare --workdir $W --case NAME` (runs the model: Lean slot, about 2 s per row),
`... run --workdir $W --case NAME` (on the Xcelium host, one run at a time, about 2.3 s), then
`python3 harness/sv/diff_test2.py --golden --case NAME`. Any `XREF-DIFF` is a model bug, never a whitelist.

## 5. One operator end to end on paper: unsigned `+` (d)

### 5.1 From the SystemVerilog line

A hypothetical `add` with the banlist lifted. (`tests/add/negative/plus.sv` is the same circuit written with a
concatenated target: 117.994 GE / depth 33, MEASURED; a concatenated target is outside the summary,
`CombView.lean:662`, so the carry goes through a wider signal.)

```systemverilog
module addw #(parameter int N = 8) (input logic [N-1:0] a, b, input logic cin,
                                    output logic [N-1:0] s, output logic cout);
  logic [N:0] t;
  assign t = a + b + cin;      // context N+1: every operand zero-extended, the carry lands in t[N]
  assign s = t[N-1:0];
  assign cout = t[N];
endmodule
```

MEASURED envelope (default point `N = 8`): `Binary + (Binary + (Resize 9 (Ident a 8)) (Resize 9 (Ident b 8))) (Resize 9
(Ident cin 1))`, then `ArraySel t [N-1:0]` and `ArraySel t [N]`. The `9` is metadata of the default point; ls-sv
recomputes it (`Param2.lean:923-943`). Lowered at every `N` it is `.binary .add (.binary .add (.resize (N+1) a)
(.resize (N+1) b)) (.resize (N+1) cin)`, exactly `caddRhs N` (`Comb2ConcatExample.lean:95`), whose settled-state proof
exists for a hand-built design.

### 5.2 Skeleton, equations, obligations, theorem

NEW constructors (proposal): `Sk.ext e` (zero-extension from a marker: `bit k = decide (k < e.width) && e.bit k`,
`low = .resize tw e.low`), `Sk.add l r`, `Sk.sub l r`; `Sk.width σ dw` (self-determined width); `tw` threaded into
`Sk.bit`. `rdsOf?` accepts `.binary (.m0 .add) l r` and `.resize _ e` with `e` a leaf; `skT` builds the nodes; `fragG`
accepts them. Equations `sv_equations` would produce (alias rule `CombEqTactic.lean:247`):

```
eq_t_1    : ∀ k, k < N + 1 → st.boolAt "t" k =
              XF.addBits (N+1) (XF.addBits (N+1) (XF.zext N (st.boolAt "a")) (N+1) (XF.zext N (st.boolAt "b")))
                         (N+1) (XF.zext 1 (st.boolAt "cin")) k
eq_s_1    : ∀ k, k < N → st.boolAt "s" k = st.boolAt "t" k
eq_cout_1 : st.boolAt "cout" 0 = st.boolAt "t" N
known_t_1 : ∀ k, k < N + 1 → (∃ v, st.lookup "t" = some v ∧ v.width = N + 1) ∧ KnownBit st "t" k   -- shape unchanged
```

The printed `eq_t_1` keeps the source's structure (left-associated `+`, one `zext` per marker): principle 10 of
`docs/sv-comb-design.md`. Obligations: `width_1` is `N ≤ N+1 ∧ N ≤ N+1 ∧ 1 ≤ N+1` (`intros; omega`); `inRange`,
`bitRead`, `cover` as usual; rank `rippleRank (fun p => if p = 0 then 1 else 2) (fun _ _ _ => 0)`.

The final theorem is what `check.py` demands, `theorem Submission.solution : Submission.Goal` with
`Goal := SvGolf.Tasks.Add.Statement design.sem`; the scaffold is `add_n.lean` unchanged (`sv_structure (rank := ..)`,
`sv_interface`, `satisfiedAt_of_comb`, `sv_equations`, the `first | (intros; omega) | sv_cover | inKnown_ofBitVec`
closer). Only `add_final` changes:

```lean
theorem addw_final {N : Nat} {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : st.lookup "a" = some (LVec.ofBitVec x)) (hB : st.lookup "b" = some (LVec.ofBitVec y))
    (hCi : st.lookup "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (et : ∀ k, k < N + 1 → st.boolAt "t" k = XF.addBits (N+1) (XF.addBits ..) (N+1) (..) k)   -- eq_t_1
    (es : ∀ k, k < N → st.boolAt "s" k = st.boolAt "t" k) (eo : st.boolAt "cout" 0 = st.boolAt "t" N)
    (known facts for s and cout, as in add_final) :
    st.lookup "s" = some (LVec.ofBitVec (BitVec.ofNat N (x.toNat + y.toNat + c0.toNat))) ∧
    st.lookup "cout" = some (LVec.ofBitVec (BitVec.ofNat 1 ((x.toNat + y.toNat + c0.toNat) / 2 ^ N)))
```

Proof, no carry induction: (1) `XF.bv (N+1) (st.boolAt "t") = x.setWidth (N+1) + y.setWidth (N+1) +
(BitVec.ofBool c0).setWidth (N+1)` by NEW `XF.bv_addBits` twice, `XF.bv_zext` and `SvState.boolAt_ofBitVec` for the
ports; (2) `cadd_low` and `cadd_carry` (EXISTS, `Comb2ConcatExample.lean:239`, `:248`) read `s` and `cout` off it
through `es`, `eo`; (3) `SvState.lookup_eq_ofBitVec_bv` and `bitvec_eq_ofNat_of_val`/`sum_split` (EXIST,
`CombLib.lean:148`, `:156`) give the statement. Estimate: `addw_final` 25 to 35 lines against `add_final`'s 45 (which
carries `AddView` and the ripple row); whole file about 55 lines against `add_n.lean`'s 84. The saving is the carry
induction, not the scaffold.

### 5.3 Size, risk, fallback

| piece | content | estimate |
|---|---|---|
| spike (like G2.0) | the `+`/`ext` case of `gate_shape` and the side condition `ctxOpWidth2 ≤ tw` from `WidthOk` (NEW `ctxOpWidth2_le`, an induction like `rdsOf?_len`); GO if about 150 lines without whnf storms | 0.5 day |
| recognizer, `Sk` | `rdsOf?`, `leafRd?` (`.resize`), `cnt`, `skT`, `fragG`; `Sk.ext/add/sub/width`; `tw` through `Sk.bit` (users: `CombEqBase`, `CombEqShape`, `CombEqThm`, `CombEqTactic`, `CombProcEq`, `CombProcTactic`) | 1 day |
| shape theorems | `gate_shape` arms; `rdsOf?_len`, `skT_leaves`; `low_xfWidth`/`low_xfBits`; `inst_rd` | 1 to 1.5 days |
| tactic, glue, example | simp sets (`CombEqTactic.lean:148, :219`), `CombWord`, an `Examples/system-verilog` proof, row P3 | 0.5 to 1 day |
| byte-identity regression | goal dumps of `add_n`, `mul_*`, `add_proc`, `sbox_bp` before/after; the 386-check suite (3154 s, PLAN2.md:105); `gen_sv_refusals --check`; docs | 0.5 to 1 slot-day |
| **`+` total** | | **3.5 to 5 agent-days** |

Calibration: the Gate 1 note sized WP-G Gate 2 at 5 to 7 slot-days, PLAN2 re-estimated 4 to 5, it took about 1.5
(PLAN2.md:106). B2 has no lowering-mirror lemma at a symbolic index (what made G2 risky) but has width bookkeeping.
Later operators: `-` +0.5, constants +0.5, `== !=`/`<`-family +1, shifts +1, concatenation operands +0.5, a
regression rerun (0.5) per milestone: v1 8 to 10 agent-days.

Risks, by weight:

* **D2, `Resize` markers are metadata of the default point.** `instExpr2 (.resize ..)` wraps even when the operand
  already has the context width (`Param2.lean:941-942`); `fitExpr2` of a bare leaf does not (`:1124`). The shape
  theorem is an EXACT equality of `Expr2` terms, so `Sk.low` must reproduce the marker: keep `Sk.ext` tied to it, with
  the contracts of 3.3. A design whose widths coincide only at the default point fails loudly (false `width_k`), as
  gates do today. Looking through markers and recomputing breaks exact equality and was rejected.
* **D3, `tw` in `Sk.bit`.** `-`, `>>`, constants need it; `+` and comparisons do not. Threading it is mechanical, touches
  the six files above and must keep every goal dump byte-identical (the WP-F/WP-G discipline); do it with the first
  operator.
* **Duplicated chains:** the `always_comb` layer copies the gate-tree proofs for conditions (`CombProcEq.lean:269-440`);
  `if (a < b)` doubles the work unless S2 consolidates them first.
* **Nested `Sk`:** concatenation of sub-skeletons wants `cat (List Sk)`; keep walkers list-recursive so kernel `decide`
  on closed `Sk` data reduces (the `partKnown`/`partLeaves` lesson; `Sk.decWidthOk`, `CombEqPlain.lean:29`).
* **Speed:** new nodes lengthen normalized equations; tactic proofs already take 30 to 90 s (PLAN2.md section 0).

**Fallback if B2 does not land.** (1) Gate-level design, as PLAN2.md:372 says. Dearer than written: CombLib has
`ripple_row` but no subtractor or comparator lemma, and a restoring divider needs `~` and `?:` anyway (S2); a
comparison is the carry out of `x + ~y + 1`, one NEW lemma away. (2) Per-site hand proofs in the `Known2` style
(`sv2_known`, `Known2.lean:868`; `Comb2ConcatExample` is 628 lines for two small designs; `tasks/fdiv16/PROOF_PLAN.md` D4 says
"about 77 small lemmas" for `fdiv16`). Neither is attractive for the 35 sites of `fdiv16.sv` that use a B2 operator;
the spike decides before anything else is spent.

## 6. Interaction with fdiv H2 and the references (e)

### 6.1 `fdiv16.sv` against the fragments

MEASURED by a regex pass over the comment-stripped `tasks/fdiv16/reference/fdiv16.sv` (indices masked; 52 `assign`s
and one `always_comb`):

| needs | assigns | examples (line) |
|---|---|---|
| nothing beyond today | 12 | field selects, `{za8, za4, za2, za1}`, `rem[0] = {1'b0, na4}` |
| B2 only | 17 | `ma = {ea != 5'd0, fa}` (57), `qq[12-i] = (rem[i] >= {1'b0, nb4})` (97), `eoff = {2'b0, xa} + .. - ..` (111), `qs = qm >> sh` (127, VARIABLE shift), `st1 = st0 \| ((qs << sh) != qm)` (128), `mag = {ef, qs[10:1]} + {14'd0, inc}` (132) |
| S2 only (`~`, `?:`) | 5 | `za1 = ~na3[10]`, `qm = qq[12] ? .. : ..` (106), `ef = nrm ? .. : 5'd0` (131) |
| B2 and S2 | 18 | `xa = (ea == 5'd0) ? 5'd1 : ea` (61), `na1 = za8 ? (ma << 8) : ma` (68), `rem[i+1] = qq[12-i] ? ((rem[i] - ..) << 1) : (rem[i] << 1)` (98), `a_nan = (ea == 5'd31) && (fa != 10'd0)` (48) |
| `always_comb` (135-148) | 1 | five arms, three conditions with `\|\|`/`&&`: S2 |

So 35 of 52 assigns use a B2 operator, 23 need S2, 18 need both: neither package loads the file alone. Also
**variable-amount shifts** (127, 128): free in the skeleton, but not "literal shifts" as PLAN2 words WP-B2.

### 6.2 What H2 gets, and the parametric fdiv

`tasks/fdiv16/PROOF_PLAN.md` D4 is by hand "about 77 small lemmas"; with B2+S2 the equations come from `sv_equations` and each
word-level site costs one glue application (5 to 10 lines once the lemma exists): about 35 plus the table. The digit
loop (M3b) becomes arithmetic on `XF.val` of the state; `restore_spec` (`tasks/fdiv16/SpecFacts.lean`) is already on `Nat`.

For `design/fdiv-param` B2 is necessary, not sufficient: the format-dependent constants (bias `2^(w-1) - 1`, field
boundaries `W+P-1`, the `7'd33` of `fdiv16.sv:119`) become expressions of `W`, `P` with `<<`/`**` (`**` is banned),
while `localparam` accepts only `+ - *` by a literal and `/ %` by a literal (PROVING.md section 4): a
`localparam`-with-shift item (WP-F2) or size casts must come with it.

### 6.3 What gets shorter in the references

Nothing in `add`, `mul`, `aes_sbox`: `add` and `mul` ban `+ - *` (`task.json`), and the S-box reference is an
XOR/AND netlist. What changes for existing material: `tests/add/baselines/cmp_carry.sv` (195.975 GE, depth 17,
MEASURED; a policy probe whose depth beats every reference) uses `>`, `==` on operands of width `i`, and `~`. It
passed the banlist then (banned since 2026-11-05: a task that bans `+` or `-` rejects the `$alu` that Yosys
builds for a run-time ordering comparison) and has no proof, because the tactics read none of it. With B2 plus S2's `~` it is
tactic-readable; the remaining mathematics (the carry-of-a-prefix identity `c_i = (2^i ≤ A_i + B_i + cin)` and the sum
assembly) I estimate at 60 to 120 lines, unmeasured. It would have been a second Pareto point on the `add` board (195.975
GE / 17, against the reference's 112.000 / 33); under the 2026-11-05 ban it cannot be a record. The hand-built word-level proofs in `LeanModels/Sv`
(`Comb2ConcatExample`, `Comb2ProcExample`) remain examples; their arithmetic moves into `CombWord`.

## 7. Open questions for the maintainers

1. **Printed form.** Faithful nested `XF.addBits (N+1) (XF.addBits ..) .. (XF.zext ..)` (this note, principle 10) or a
   normalized `XF.val a N + XF.val b N + ..`? The latter reshapes `(a + b) + c` and needs an associativity lemma per
   chain. Recommendation: faithful.
2. **Scope of v1.** Variable-amount shifts (needed by `fdiv16`, free in the skeleton): yes. `*` (same shape as `+`,
   `XF.mulBits :449`, banned by `add`/`mul`): no.
3. **One family, not two.** B2 and WP-G S2 edit the same functions (`leafRd?`, `Sk`, `low_xf*`) and both list
   reductions (`always-comb/README.md` section 2.2, PLAN2 WP-B2). Recommendation: one "skeleton v2" family, S2
   first (smaller; 23 of `fdiv16`'s 52 assigns and its table need it), B2 second, reductions with S2, H2 not started
   on B2 alone.
4. **Which tasks allow `+`.** `add` and `mul` ban it; the `fdivp` draft bans `/ % **` only. B2's board payoff is
   `cmp_carry`-style comparison adders (banned in `add` since 2026-11-05) and any new `+`-allowed task (a `+`-allowed adder starts from Yosys's own
   117.994 GE). Banlists are per task and their call.
5. **Constants.** Parameter-valued constant arithmetic (WP-F2, size casts): inside B2 or a separate gate? The
   parametric fdiv cannot proceed without it.
6. **Signed.** Defer entirely (recommended): the extractor refuses it first (`dc-signed`).
7. **Pins.** Approve eight new Xcelium rows (a few minutes of Lean slot, 20 s of Xcelium) before M2? Shifts have
   no pinned four-state trace today.
8. **The copied chain** (`G22-NOTE.md` section 3): consolidate before B2? Recommendation: no; extend `cond_shape`'s
   copy only when S2 conditions need it.

## Appendix: what was run

| what | result |
|---|---|
| `python3.12 check/envelope.py` on the 5.1 module and on `a & (a == b)` / `a << 1` | `Resize` around each `+` operand, the comparison, the shift's left operand; no Lean |
| the same on P1 to P8 (+ `verilator --lint-only`) | P1 to P7: 0 `Unsupported`; P8: 8; all lint clean |
| Verilator 5.042 `--binary`, 256 pairs, 18 outputs of the P1 to P3 shapes | 0 mismatches against 3.1 (scratch: `$SCRATCH/wpd2/probe/vl/`) |
| `python3.12 score/score.py .. --task tasks/add` on `tasks/add/reference/add_n.sv`, `tests/add/negative/plus.sv`, `tests/add/baselines/cmp_carry.sv` | 112.000 / 33; 117.994 / 33; 195.975 / 17 |
| regex inventory of `fdiv16.sv` | 52 assigns: 12 / 17 / 5 / 18 |
| search of `sem2/*/*.sv` for run-time shifts | none (section 4) |
