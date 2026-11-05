# WP-B2, gates 1, 2a and 2b: `+`, `-`, comparisons, truncation and unsized constants in the `sv_comb` chains (as built)

Status (2026-11-01, branch `wpb2g2`): gate 1 (`+`, `-` and the `Resize` marker in the GENERIC chain, `assign` sites)
is on master; **gate 2a** (the `always_comb` chain reads the same fragment, ONE reading of the skeleton) is
implemented, section 8; **gate 2b** (comparisons, truncation markers over operations, unsized constants) in section 9. Companion of `B2-NOTE.md` (the design) and `spike/` (the gate-0 evidence).

## 1. The fragment

In an `assign` right-hand side, at the CONTEXT-determined positions (the root, the operands of `& | ^ ~ + -`, the
arms of `?:`):

* `l + r` and `l - r`, left-associated as written, with an operand either a bare access/literal exactly as wide as
  the target, or narrower, in which case slang wraps it in a `Resize` marker and the tactics model the zero
  extension (`XF.zext n f`), or a nested context-determined expression;
* the marker itself, around ONE signal access or ONE sized literal (also at the root: `assign y5 = a;`).

Refused, each with its own message: `*`, ordering comparisons, shifts, unary minus; a width conversion around an
OPERATION (a truncated sum `y3 = a4 + b4`, `!s` into a vector); an unsized constant operand (`a + 1` is
`Resize4[(Resize32[a] + 1)]`: a truncation marker over a 32-bit sum); `+`/`-` or a marker in a SELF-determined
position (the operand of `!`, a reduction, `&&`, `||`, `==`, `!=`, the condition of `?:`: those keep the v1 fragment);
`+`/`-` in an `always_comb` leaf was refused in gate 1 and is accepted since gate 2a (section 8). A contract that fails is a loud false `width_k`
goal: a marker wider than the context, a bare access narrower than it.

## 2. The compatibility layer (why the proc chain did not move)

`Sk.bit` must read the CONTEXT width for `+` and `-` (the carry survives up to it; `-` wraps modulo `2^tw`; a
marker's natural width is below it, so it cannot be recovered from the operands: spike, section 2). Threading it into
`Sk.bit` changes the arity the `always_comb` chain is built on (`PSk.bit`, nine statements in `CombProcEq`), and that
chain is being rewritten (S3b, consolidation, S1b). So gate 1 adds a word-level reading BESIDE the v1 one:

| v1 (frozen, the `always_comb` chain uses it) | word-level (the generic chain uses it) |
|---|---|
| `binOk`, `rdsOf?`, `rhsRds?` | `ctxOpW`, `selfOpW`, `rdsOfW?`, `rhsRdsW?` (the self-determined operands are read by `rdsOf?`) |
| `Sk.WidthOk`, `Sk.bit`, `Sk.width` | `Sk.WidthOkC`, `Sk.bitC`, `Sk.nwidth` (the natural width, a max over operands) |
| `skT_shape`, `rhs_shape`, `low_xfWidth/Bits` | `skT_shapeC`, `rhs_shapeC`, `proc_shapeC`, `low_xfWidthC/BitsC` |

Shared and extended in place: `Sk` (three constructors `ext (p : Part)`, `add`, `sub`, with the v1 definitions saying
`False`/`false` for them), `cnt` and `skT` (new arms), `Sk.low` (no new argument: a marker lowers to `.resize tw`,
the part under it at no width), `siteOf?` (assign arms through `rhsRdsW?`). The v1 theorems that quantify over all
skeletons got vacuous arms (`low_xf_gen`, `Sk.low_irrel`, `Sk.selfOk_widthOk`, the decidable instances). The
statements `proc_shape` and `site_sk` are kept (the `always_comb` chain calls them) and are now corollaries of the
word-level ones (`Sk.WidthOk.toC`). **Gate 2** merges the two readings (`Sk.bit := Sk.bitC` with the context width
threaded through `PSk`, deletes `rdsOf?`/`Sk.WidthOk` and the frozen statements). Self-determined operands are v1
skeletons, so the word-level theorems call the v1 ones for them (`Sk.bitC_of_selfOk` is the bridge): the S2 theory is
not copied.

## 3. The shape theorem

`skT_shapeC` keeps the five facts of `skT_shape` with the NATURAL width `W = Sk.nwidth` for the self-determined
reading: `selfWidth2 = rigidMax2 = W`; `instExpr2 none = low W` (not for a root marker, whose `instExpr2 none` keeps
the envelope's default-point width); `instExpr2 (some tw)` and `fitExpr2 (some tw)` are `low tw`. The new arms are
`+`, `-` (the side condition `ctxOpWidth2 ≤ tw` of `instExpr2_add` follows from the width contract:
`Sk.nwidth_le`) and the marker, whose instance fact (`ie_resize_leaf`, 12 lines) is uniform: for a leaf under
`.resize m`, `instExpr2 (some cw)` is `.resize cw (accExpr σ a)` whatever the relation between the leaf width and `cw`
(the leaf is not context-propagating and not a constant leaf). The envelope's `m` is default-point metadata and is
never read at a context. Spike numbers (miniature, gate 0): shape theorem 181 lines, x-free 94, compile 6 s CPU at a
fifth of the default heartbeats; the real arms compiled at the first attempt.

## 4. What changed (file, declaration)

| file | change |
|---|---|
| `CombWord.lean` (new) | `XF.zext`, `val_congr_lt`, `val_zext`, `val_testBit`, `toNat_bv`, `bv_congr_lt`, `bv_zext`, `bv_addBits`, `bv_subBits`, `addBits_congr`, `subBits_congr`: the plain-Lean glue from a bit equation to `BitVec` arithmetic at a symbolic width |
| `CombView.lean` | `ctxOpW`, `selfOpW`, `rdsOfW?`, `rhsRdsW?`; `siteOf?` reads assign right-hand sides through `rhsRdsW?` |
| `CombViewThm.lean` | inversions of `rdsOfW?`; `leaf_flags`, `ie_addsub_cases`, `ie_resize_cases`; `inst_rdW`, `rhs_okW` (the reads promised); `siteOf?_cases`, `site_desc` over the word-level recognizer |
| `CombEqBase.lean` | `Sk.ext/add/sub`; `mkOpW`; `Sk.nwidth`, `Sk.isExt`, `Sk.WidthOkC`, `Sk.bitC`, `Sk.bitC_of_selfOk`, `Sk.nwidth_le`, `Sk.WidthOkC.mono`, `Sk.WidthOk.toC`; `rdsOfW?_len`, `skT_leavesW` |
| `CombEqShape.lean` | `ie_resize_leaf/lit`, `ie_bin_none`, `ie_ternary_none'`, `skT_shapeC`, `gate_shapeC`, `rhs_shapeC`, `proc_shapeC` (`proc_shape` a corollary), `part_xf`, `low_xf_genC`, `low_xfWidthC`, `low_xfBitsC`; axiom pins |
| `CombEqThm.lean` | `skRhs_leavesW`; `WidthObl` is `Sk.WidthOkC`, `EqSite` is `Sk.bitC` with the target width; `eq_of_summary` uses the word-level theorems |
| `CombEqPlain.lean` | `Sk.decSelfOk`/`decWidthOk` arms (`False`), `Sk.decWidthOkC`; the flat-netlist decision uses `WidthOkC` |
| `CombEqTactic.lean` | the two normalization simp sets SWAP `Sk.bit` for `Sk.bitC` and `Sk.WidthOk` for `Sk.WidthOkC` (see section 6) |

Examples: `Examples/system-verilog/comb_word` (four designs, structure, equations pinned verbatim, proofs, negatives);
`comb_ops/comb_errors` re-pinned. Rows: `harness/sv/cases2.json` +11 (P1..P8), `sem2/wl_*`.

## 5. Results

* **The `always_comb` chain moved by zero lines**: `CombProc.lean`, `CombProcStmt.lean`, `CombProcLower.lean`,
  `CombProcSummary.lean`, `CombProcEq.lean`, `CombProcTactic.lean` are byte-identical to the base; `lake build
  LeanModels.Sv.CombProcTactic` (46 jobs) is green. `PT.low` / `PTree.low` and `PSk.low` are unchanged (`Sk.low`
  gained no argument); `PSk.bit` / `PSk.WidthOk` are unchanged too, they get the context width in gate 2.
* **Dumps**: the 24 goal dumps (`sv_structure` / `sv_equations` of the 18 Example probes and the six proved
  references `add_n`, `add_proc`, `mul_n`, `mul_tree`, `mul_tree_h`, `mul_wallace`) are byte-identical to the base
  modulo worktree paths. No intentional change.
* **Examples**: all 51 Example modules that import the `sv_comb` chain build. Intentional changes: `comb_ops/comb_errors`
  (`neg_add`, `neg_resize` are accepted, `neg_cmp` and `neg_lnot_wide` carry the new message). New:
  `comb_word` (`gen`, `comb_view`, `comb_hint`, `comb_proof`, `comb_errors`): the real tactic output for `add_same`,
  `add_wide`, `sub_wide`, `addw` pinned verbatim, four theorems for every `N ≥ 1`, seven negatives.
* **Heartbeats**: `comb_ops/comb_proof.lean`'s `add_mux_correct` needs 185k to 200k heartbeats both before and after
  (bisection at 170k, 185k, 200k, 215k); it passes at the default 200k. No `set_option maxHeartbeats` anywhere.
* **Pins**: `CombWordPins.lean` checks 71 lemmas with `#pin_axioms` (imported by `comb_word/comb_proof.lean`);
  `#print axioms` guards in `CombWord`, `CombEqShape` and the four theorems.
* **Xcelium 24.03-s004** (one run at a time): rows `wl_shift` (150 cycles), `wl_cmp_ctx` (202),
  `wl_addsub_ctx` (152), `wl_cat_operand` (68), `wl_unsized` (20), `wl_cmp_prefix_n1/n2/n4/n8` (11, 35, 515, 126),
  `wl_red` (9): 10 of 10 `XREF-MATCH`, 0 `XREF-DIFF` (1288 cycles; run-time shifts included: this is the first
  four-state trace of one); `wl_signed` is a loud refusal row (`PortSymbol:signed`).
* **Merge with WP-G**: `wpb2` contains S3b (`d83c9360`; the docs conflicts are resolved by union: changelog, register
  entry `tl-sv-structure-fragment`, PROVING sections 16 and 17). The generic and proc chains build together (137 jobs of
  the Example set, `comb_ovr` included, default heartbeats) and the 24 dumps are still byte-identical. Branch
  `wpb2-cons` is `wpb2` plus the consolidation commit `dc03f1c6` of `wpgs2` (the generic recognizer `so`): textually
  clean, same 137 jobs green.
* Size: +1389 / -27 lines in seven existing `LeanModels/Sv` files, two new modules (111 + 30 lines).

## 6. A finding: the heartbeat budget of the existing proofs

`comb_ops/comb_proof.lean`'s `add_mux_correct` needs between 185 000 and 200 000 heartbeats at the default limit of
200 000 BEFORE this step (bisection at 150k, 170k, 185k, 200k). Adding the new names to the `sv_equations` simp
sets (`Sk.bitC`, `Sk.WidthOkC`, `Sk.nwidth`, `Sk.Payload`) cost a constant 0.2 M raw heartbeats per `simp` call
(about ten calls: +1.7 %), enough to time out. The fix is structural: the sets SWAP the v1 names for the word-level
ones (no growth), the marker holds a `Part` (no `Sk.Payload`), `Sk.nwidth` is not in the sets, and the
self-determined operands of `Sk.bitC` are read by `Sk.bitC` itself (so `Sk.bit` leaves the set). Any later growth of
these lists is paid by every proof: measure `add_mux_correct` first.

## 7. Follow-ups

* Gate 2: the `always_comb` chain (`PSk`, conditions, leaves) and the merge of the two readings.
* Truncation markers over arithmetic and unsized constants (`a + 1`): `Sk.trunc`, `Sk.const`, `dw` in `Sk.low`; the
  natural width of a constant is 32 but its `rigidMax2` is none, so the single `nwidth` splits.
* Comparisons, shifts, concatenation operands (`Sk.cat` as an operand).
* A marker wider than the context at the root or under a gate is harmless for the instance fact; the contract
  `n ≤ tw` could be relaxed there (it is needed under `+ -` only).

## 8. Gate 2a: one reading, and the leaves of an `always_comb` tree

Gate 1 added the word-level reading BESIDE the v1 one so that the `always_comb` chain (`CombProc*.lean`) stayed
frozen. Gate 2a merges them on the skeleton side, through the proc chain:

* **`Sk.low σ dw tw`** takes the declared widths. `dw` is read by nothing yet; it is the argument a lowering that
  depends on the widths of the operands (`==` of unequal widths, a truncation marker, the natural width of an
  operation) needs, so the interface is frozen here, once.
* **`PSk.bit σ dw tw rd`**, **`PSk.low σ dw tw`**, **`PSk.WidthOk σ dw tw`**: a leaf is read by `Sk.bitC` /
  `Sk.WidthOkC` at the target width `tw`; a condition and the `case` subject keep their v1 shape (a one-bit
  condition: `Sk.WidthOkC σ dw 1`; a subject: `Sk.SelfOk`). `Summary.EqSiteL` states the bits at the target window's
  width. `PT.low` / `PTree.low` and the instantiation side are unchanged (they never saw the skeleton).
* **One recognizer for right-hand sides**: `rhsRds?` IS the word-level one now (`rdsOfW?`; the name is kept, so
  `CombProc.lean` and `CombProcLower.lean` need no edit for it). `rdsOf?` is what it always was for the positions
  it covers: the reader of the SELF-determined operands (`!`, reductions, `&&`, `||`, `==`, `!=`, the `?:` condition,
  the `case` subject, the `if` condition). It cannot be deleted without making the context a parameter of the
  recognizer.
* **Deleted** (no consumer left): the v1 `rhs_shape`, `proc_shape`, `gate_shape`, `skT_selfWidth`, `skRhs_leaves`,
  `rhs_ok`, `rhsRdsW?`, `rhs_okW`, `skRhs_leavesW`. **New**: `inst_idxFreeW` (the index-freeness of a word-level
  expression, CombProc.lean; `rhs_idxFree` is re-proved with it), `Sk.v1` / `Sk.WidthOkC.toV1` / `skT_v1` (a condition
  skeleton has no word-level node, so its contract is the v1 one: `cond_shape` keeps its statement).
* **Kept**: `Sk.bit`, `Sk.WidthOk`, `skT_shape`, `low_xf_gen`, `low_xfWidth/Bits` (the v1 theory of the
  self-determined operands, called by `skT_shapeC` and `low_xf_genC` for them; replacing the calls by recursion into
  the word-level theorems needs `nwidth = width` on self-determined skeletons and is the cleanup of gate 2b).
* **The tactics**: `CombProcTactic` swaps `Sk.bit` / `Sk.WidthOk` for `Sk.bitC` / `Sk.WidthOkC` in its two simp sets
  (a swap, not a growth: section 6).
* **Example**: `comb_word/addp.sv`, `if (c) y = a + b; else y = a - b;` into an `(N+1)`-bit `y`: structure,
  `sv_equations?` output pinned verbatim, `addp_settles` for every `N`. The seventh negative of gate 1 (`neg_proc`)
  became this positive design.

## 9. Gate 2b: comparisons, truncation, unsized constants

* **The S/R split** (the gate-1 finding): `selfWidth2 (.int _) = 32` but `rigidMax2 (.int _) = none` (a constant carries
  no x bit), so the natural width and the rigid width of an expression differ. The skeleton now has both:
  `Sk.width` is the natural width (`selfWidth2`: the former `Sk.nwidth` is merged into it; for a self-determined
  skeleton it is the v1 width, `Sk.SelfOk` keeps saying the operands agree) and `Sk.rmax : Option Nat` is `rigidMax2`
  (`none` at a constant). The shape bundle of `skT_shapeC` is `selfWidth2 = some width`, `rigidMax2 = rmax`, the
  lowering at no context only when the context holds the natural width (`width ≤ tw`), the lowering at `tw`, the fit.
* **The `+ -` contract**: `instExpr2`'s `+`/`-` arm compares `(ctxOpWidth2 l r).getD tw` with the context; with a
  constant or a marker around an operation under it, that number is no longer implied by the width contract of the
  operands. `Sk.rok σ dw tw` carries it (only a marker around an operation, `rsz`, can violate it; `Sk.rok_of_width`
  discharges it whenever the node's natural width fits). It enters `WidthOkC` of `+`, `-` and `~` (the `bnot` arm of
  `instExpr2` compares `rigidMax2`).
* **Comparisons**: `Sk.cmp (op : CmpOp) l r`, one bit; the operands are lowered at `max (width l) (width r)`, the
  operand contract is `WidthOkC` at that width, so the contract context changes under the node (`Sk.decWidthOkC`
  takes `tw` as an argument of the recursion). The v1 reading (`Sk.bit`, `Sk.SelfOk`) keeps `==`/`!=` of operands of
  one width (the `Sk.WidthOk` contract of the old chain is unchanged); the six operators share one proof per arm via
  `CmpOp.ex`.
* **Unsized constants**: `Sk.const v`, lowered to `LVec.ofInt tw v`, bit `XF.constBit v tw k`, natural width 32.
* **Truncation**: `Sk.rsz (pr : Bool) p` is a marker around an operation, `pr` = the operation follows a wider context
  (`ctxPropagates`, decided by `skT` from the head of the operand: no new name in the tactic simp sets). `rsz true`
  lowers to `if w < tw then p at tw else .resize tw (p at w)`, `rsz false` to `.resize tw (p at w)`; the contract and
  the bits follow the same `if`, so a comparison into a vector prints without it.
* **Not in this gate**: concatenation as an operand (`{a, b} + c`, `{a < b, a}`): `Sk.cat` has no word-level reading yet
  (parts are read by `partsRd?` as accesses and literals); shifts (gate 3, they go through `instDivOperand2`); signed
  forms; `+`/`-`/comparisons in self-determined positions.
* **Proc chain**: `CombProc.lean` (`inst_idxFreeW`: the `CmpOp`, `int` and marker arms) and the two simp sets of
  `CombProcTactic` (`Nat.max_self`, `Sk.rok`). `CombProcEq.lean`, `CombProcLower.lean`, `CombProcSummary.lean`,
  `CombProcStmt.lean` are untouched: the leaf theory is stated over `Sk`, not over its constructors.
* **Heartbeats**: after merging `svgolf-prep` (S1b gate b, c1, tier B) `add_mux_correct` crossed the default limit (it fails at 200 000, passes at 215 000; `wpgs2` alone and gate 2b alone both sat at 185 000 to 200 000). Removing the two names this gate added (`Nat.max_self`, `Sk.rok`) from the simp sets did NOT recover it (measured), so the proof was split into three declarations (`add_mux_comb`, `add_mux_acyclic`, `add_mux_settled`, each its own budget; the statement is unchanged): the largest passes at 140 000 and fails at 100 000. No `set_option maxHeartbeats`.

## 10. Gate 3 (design delta, before the Lean work): run-time shifts and concatenation operands

Status: DESIGN (2026-11-01, branch `wpb2g3` on svgolf-prep `c1c2e44b`). Every claim about `instExpr2` below is READ from
`Param2.lean` (line numbers in the report), every claim about the x-free layer from `CombKnownBits.lean`; none is measured yet.

**10.1 What the model does with `l << r` (READ).** `instExpr2` lowers `.m0 (.shl s)`, `.m0 (.shr s)` (and `<<<`, `>>>`) as
`ctxTrunc2 ctx lc (.binary op L R)` with `lc = maxW2 ctx (divOperandWidth2 l)`, `L = instDivOperand2 s lc l`,
`R = instDivOperand2 false (divOperandWidth2 r) r`. So: the left operand is context-determined (extended to
`lc = max tw (width of l)` BEFORE the shift, `fitDivOperand2`: `l` itself when its width is `lc`, else `.resize lc l`),
the amount is self-determined and unsigned and **never widens the result** (its own width is only the width of `R`);
the result is then truncated to the context (`.resize tw` when `lc > tw`). `selfWidth2` of the shift is
`divOperandWidth2 l` (the width of the left operand, a `Resize` marker is seen through) and so is its `rigidMax2`;
`ctxPropagates` is `true` (a marker around a shift is the gate-2b `rsz true`). The shift is NOT in `rigidExpr`: it goes
through `instExpr2`, not `fitExpr2`'s rigid arm, so a shift under `+ - ~ ?:` needs no new case beyond the node itself.

**10.2 x-free layer and bit function (READ).** `Expr2.xfWidth (.binary (.shl _) L R) = xfWidth L` (both must be defined),
`xfBits = XF.shlBits (L bits) wr (R bits)`, `XF.shlBits f wr g k = decide (val g wr <= k) && f (k - val g wr)`,
`XF.shrBits w f wr g k = decide (k + val g wr < w) && f (k + val g wr)`; `LVec.shl/shr` equal these (`shl_ofBoolFn`,
`shr_ofBoolFn`, already proved); an x/z amount is excluded by the knownness reads exactly like any operand. Because the
extension of `L` is by zeros, **the bit function does not depend on the context**: for `k < tw`
`bitC (sh l r) tw k = XF.shlBits (XF.zext wl (l bits)) wr (r bits) k` (and `XF.shrBits wl (l bits) wr (r bits) k`), with
`wl = l.width`, `wr = r.width`; the three lowering shapes (`wl < tw`: `shl (.resize tw l) R`, `wl = tw`: `shl l R`,
`wl > tw`: `.resize tw (shl l R)`) only differ in `Sk.low`, not in the equation the player sees.

**10.3 BitVec glue (`CombWord`, plain Lean, one lemma per operator, no induction).**
`XF.bv_shlBits : bv w (XF.shlBits (XF.zext wl f) wr g) = ((bv wl f).setWidth w) <<< (bv wr g).toNat` for every
`w`, `wl` (covers extension and truncation) and `XF.bv_shrBits : bv w (XF.shrBits wl f wr g) = ((bv wl f) >>> (bv wr g).toNat).setWidth w`.
An amount at least the width gives `0` as in the LRM: this is `BitVec.shiftLeft`/`ushiftRight`'s own behaviour (the
`Nat` amount is not reduced modulo the width), so no case split. Proofs by `getLsbD` ext (`BitVec.getLsbD_shiftLeft`,
`getLsbD_ushiftRight`), about 12 lines each. Concatenation: `XF.bv_cat : bv (w1 + w2) (catBit [p1, p2]) = bv w1 f1 ++ bv w2 f2`
(and the cons step for more parts), the glue the `cadd_*` lemmas of `Comb2ConcatExample` already do by hand.

**10.4 Skeleton nodes.** `Sk.sh (dir : Bool) (l r : Sk)` (`dir = true`: `<<`). Recognizer `rdsOfW?`: a new `shOpW`
(`.m0 (.shl false)`, `.m0 (.shr false)`), the shift arm reads the left operand through `shLeftRd?` and the amount
through `shAmtRd?`. **Restriction, stated up front:** `L` and `R` are lowered by `instDivOperand2`, a different
instantiation function from `instExpr2` (its own `common`-width and `fitDivOperand2` rules), so the closed cases are
the operands whose `instDivOperand2` is the default arm or the concatenation arm:
* left: a signal access, a sized literal, an unsized constant, or a concatenation of accesses and literals, bare or under
  the `Resize` marker (the marker is transparent: `instDivOperand2 (.resize _ e)` is `instDivOperand2 e`);
* amount: a signal access, a sized literal or an unsized constant (`a << 1`, `a << s`, `a << s[1:0]`, `1 << s`).
A left operand that is itself an operation (`(a + b) << 1`, `~a << 1`) or an amount that is an expression (`s + 1`) is
REFUSED with a message ("write it into a signal first"). The amount-expression case is the one place the brief says
"or an expression": `instDivOperand2` of an `add` and `instExpr2` of an `add` agree (both fit the operands to the own width
`max`), but proving it is a second shape theorem; I propose it as stage 3c if the first two stages fit the budget.
`Sk.low (.sh d l r) tw = if wl <= tw then (shl (fit lc l_own) R) else .resize tw (shl l_own R)` with `l_own = l.low σ dw wl`,
`R = r.low σ dw wr`, `fit lc x = if wl = lc then x else .resize lc x`; `Sk.width (sh) = l.width`, `Sk.rmax (sh) = some l.width`
(`l.rmax` for an unsized constant is `none` but the SHIFT's `rigidMax2` is `selfWidth2`: 32 for `1 << s`);
`WidthOkC (sh) tw = l.WidthOkC l.width tw' ...` is just `l.WidthOkC σ dw l.width ∧ r.WidthOkC σ dw r.width` (both trivially
`x = x` for leaves, so **no new `width_k` goal appears for a shift**; the context only decides the lowering shape);
`rok`, `leaves`, `knownB` are the unions. `skT_resize_op`'s inline match gets `.m0 (.shl _) | .m0 (.shr _) => rsz true`.

**10.5 Concatenation operands.** The gate-1 recognizer already READS a nested `.concat` (`partsRd?`) but `cnt`/`skT`/`fragG`
treat it as a leaf: it is accepted by `sv_structure` and fails loud in `sv_equations` (`fragOk`). Stage 3b: `cnt (.concat ps) = pcnt ps`
(`pcnt` moves to `CombEqBase`), `skT (.concat ps) = .cat (partsT ps as)` (the SAME node as the top-level concat: no new
vocabulary in the output, `catBit` is already in the simp sets), `fragG (.concat _) = true` for parts that are leaves or literals,
`isOpW (.concat _) = true` (a marker around a concatenation is `rsz false`), and a concat arm in `skT_shape` and `skT_shapeC`
reusing `parts_shape` (`instExpr2 ctx (.concat ps) = .concat (instParts2 ps)` for EVERY context, so the arm is the
`rhs_shape` concat branch). The context contract of `.cat` stays `sum = tw` (a concatenation of the wrong width carries a marker
and is `rsz false`). The v1 theorems that case on `fragG` get the same arm. **`{a < b, a}` (a comparison as a PART)** needs
`Part.cmp (op) (l r : Part)` (parts are self-determined: `instParts2` lowers a part at its own `selfWidth2`, a comparison of two
accesses is `binary op (fit w l) (fit w r)`, one bit): that touches `Part.wid/bit/expr`, `partLeaves`, `partKnown`, `partsRd?`,
`partsT`, `pcnt` (a part now consumes 0, 1 or 2 reads) and the parts lemmas; I propose it as stage 3c with the amount-expression case, and
will report its measured size before starting it.

**10.6 Obligations, proofs, pins.** No new obligation kind: a shift prints `eq_y_1 : forall k, k < tw -> st.boolAt "y" k = XF.shlBits
(fun x => XF.zext W (fun k => st.boolAt "a" k) x) W' (fun k => st.boolAt "s" k) k` and only the usual `inputsKnown`/`cover`/`bitRead`
reads (the amount window is read in full). New theorems: `ie_shift` (the instance fact `instExpr2 (some tw) (sh)`), the shift arm of
`skT_shapeC` (3 lowering shapes by `wl ? tw`), arms of `low_xf_genC` (reusing `xf_shl`, `xfb_shl` over `Expr2.xfWidth/xfBits`),
`inst_rdW`, `inst_idxFreeW` (the only proc-chain edit: `CombProc.lean`, the leaf side; `CombProcEq/Lower/Summary` untouched),
`Sk.rmax_le_width`, `rok_of_width`, `mono` arms; pins in `CombWordPins`. Examples (`comb_word`, `#py`-style three files as before):
`shl_n` (`y = a << s`, every `N`, `S`), `shr_n`, `onehot` (`y = 1 << s` into `N` bits: truncation of a 32-bit shift, `1#N <<< s.toNat`
for every `N`), `shl_wide` (into `N + K` bits: the extension), `cat_add` (the `wl_cat_operand` shapes). Rows `wl_shl_n`, `wl_shr_n`,
`wl_onehot`, `wl_shl_wide`, `wl_cat_add` on Xcelium (exhaustive small widths + x/z amounts and an amount at least the width; the
gate-1 row `wl_shift` already pins the model for the shapes, except `a << N` with a parameter amount, which stays refused: a
`paramRef` is a constant of the localparam work).

**10.7 Heartbeat expectation and slot use.** Gate 2b added seven constructors, two simp names and cost +0.3 % on every Example proof.
Gate 3 adds ONE constructor with arms in the same eight functions and no new simp name (`XF.shlBits`, `XF.zext`, `catBit`,
`Sk.cat` already print/unfold as they do): expectation +0.1 % to +0.2 % per proof, +0.3 % at most. `lp_correct` is at 199,433 without
its own `set_option maxHeartbeats 1000000` and will cross 200,000: I propose to split it into `lp_comb`, `lp_acyclic`, `lp_settled`
as `add_mux_correct` was (statement unchanged; each part about a half of the old total) and to drop the option and the docstring that
says the default is not enough; every other number in the 2b table has more than 3 % of margin or carries its own option. I measure
with wpgs2's harness against the 2b table at the end of each stage, in acquisitions of at most 15 minutes (the instrumented
`measure.sh` split in three: tasks, Examples, 24 dumps in two halves). Stages: 3a shifts (accesses, constants, concatenation as the left
operand), 3b nested concatenation, 3c (only with the lead's go) amount expressions and `Part.cmp`.

**10.8 Rulings of the review (2026-11-01).** The fragment of 10.4 is the gate-3 fragment. Not in this pass, and the FIRST candidate for a
gate 3d: a shift by a PARAMETER (`a << N`) and amounts of the `x << (N-1)` kind: the two things a golfer hits next (parameter-valued
constants wait for the localparam work, and an expression amount needs the second shape theorem of 10.4). Stage 3c (`Part.cmp`,
expression amounts) only after its measured size is reported. The `lp_correct` split into `lp_comb` / `lp_acyclic` / `lp_settled` is
accepted on the condition that every part keeps at least 15 % of margin under 200,000 heartbeats with the option and the docstring
dropped; a part that does not keeps a `set_option` of its own (and says why). The same check applies to every other Example proof within
5 % of 200,000 after 3a.

## 11. Gate 3a results: run-time shifts (2026-11-01, branch `wpb2g3`)

* **What it is.** `a << s` and `a >> s` at the context-determined positions of a right-hand side, in the fragment of 10.4:
  a signal access, a sized literal or an unsized constant as the left operand (bare, or under the marker that keeps its
  signedness) and as the amount. One skeleton constructor, `Sk.sh (dir) (sg) l r`; no new `width_k` goal; no new simp-set name.
  The equations print as `XF.shlBits` / `XF.shrBits` (`XF.zext W …` for an extended left operand), the glue is `XF.bv_shlBits`,
  `XF.bv_shrBits` (about 14 lines each, `getLsbD` extensionality).
* **A finding that changed the design delta.** 10.4 assumed an UNSIGNED shift. The real envelope of `y = 1 << s` is
  `s<<` with the left operand `SignedResize 32 (Int 1)`: an unsized constant is a signed 32-bit integer, so the shift is
  signed, `instDivOperand2` lowers its left operand SIGNED, and for a context wider than 32 bits the lowering contains
  `resizeSigned`, which the x-free layer did not cover (`Expr2.xfWidth (.resizeSigned _ _) = none`). Gate 3a therefore adds
  `Expr2.resizeSigned` to the x-free fragment (`XF.sext`, `LVec.resizeSigned_ofBoolFn`, `evals_resizeSigned`: +58 lines in
  `CombKnownBits.lean`, five executable rows against the interpreter) and the glue `XF.bv_shlBits_s`. The marker handling is
  flag-dependent (`instDivOperand2` ignores the flag it is given at a `Resize` (unsigned inside) and a `SignedResize`
  (signed inside)), so `shLeftRd?` takes the operator's flag and strips only the marker that keeps it. A signed `>>`
  would make the bit function depend on the context width and is refused (it is the only unreachable `Sk.sh` corner; its
  `bitC` is defined so the ∀-skeleton theorems stay true).
* **Dumps**: the 24 goal dumps are byte-identical to `afterB0` (23) except `comb_proc/comb_errors`, the intended
  removal of the `neg_multi` block (identical to the `wpgs2` dump).
* **Examples**: all 55 Example modules that import the chain build (143 jobs, default heartbeats, `lake exit 0`).
  `comb_word`: `shl_n`, `shr_n`, `shl_wide`, `onehot`, `shl_const` (structure, equations pinned verbatim in `comb_hint`, five
  theorems for every `N ≥ 1`), three negatives (`neg_shift_op`, `neg_shift_amt`, `neg_shift_par`: one message, "write the
  operand into a signal first"); `neg_shift` (`a << 1`) is now accepted. `lp_correct` is split into `lp_comb`,
  `lp_acyclic`, `lp_settled` (no `set_option` any more).
* **Heartbeats** (instrumented harness, against the gate 2b table `hbm/m1`; limit 200 000 unless the declaration carries
  its own option): `lp_comb` 32 693, `lp_acyclic` 50 990, `lp_settled` 103 873 (187 700 with the 144 of the wrapper, 5.9 %
  below the 199 433 of the old declaration; the largest part has 48 % margin); `ripple_correct` 163 305 (+0.4 %, margin 18 %);
  `mul_correct` 207 667 (+0.3 %, own option); `add_mux_settled` 101 666 (+0.3 %); `sbox_table` `solution` 189 898 (+0.1 %,
  margin 5.1 % at the default limit: a reference file, not touched here); `sbox_bp` `solution` 347 899 (+1.6 %, the
  largest growth, own option); `mul_tree` `tree_struct` 797 104 (+0.0 %); the five new theorems 73 529 to 82 143.
  Nothing grew by 3 % or more.
* **Pins**: `CombWordPins.lean` checks 43 more lemmas; `#print axioms` guards on the new Example theorems.
* **Xcelium 24.03-s004**: eleven rows, 1119 cycles, 11 of 11 `XREF-MATCH`, 0 `XREF-DIFF`:
  `wl_shl_n_n1/n2/n4/n8`, `wl_shr_n_n1/n2/n4/n8` (all amounts 0 to 7 against every operand up to 4 bits, random 8-bit
  operands, x/z bits in the operand and in the amount), `wl_shl_wide` (into 5 and 8 bits, `<<` and `>>`), `wl_onehot`
  (`1 << s` into 4 and 40 bits, amounts 0 to 63 and x/z), `wl_shl_const`.
* Size: +795 / -18 lines in nine existing `LeanModels/Sv` files, no new module.

### 11b. Gate 3b results: concatenations as operands (2026-11-01, branch `wpb2g3b` on svgolf-prep `e862b83c`)

* **What it is.** `{hi, lo}` (literals and signal accesses) at every position `rdsOfW?` reads as a context-determined operand,
  bare or under a `Resize` marker. `skT (.concat ps) = .cat (partsT ps rs)` (the top-level node), `cnt (.concat ps) = pcnt ps`,
  `PExpr.isOpW (.concat _) = true` (a marker around it is `rsz false`, the existing `skT_resize_op` and the marker arm of
  `skT_shapeC` carry it over), and ONE new shape arm (`parts_shape` + `fitExpr2_concat` + `instExpr2_concat`, as `rhs_shapeC`
  does for the whole right-hand side). No new constructor, no new `Sk` function arm: every ∀-skeleton theorem already had
  the `.cat` case.
* **`fragW`.** The delta proposed `fragG (.concat _) = true`; that would have forced a concatenation arm into every v1
  theorem (`rdsOf?_len`, `skT_leaves`, `skT_shape`, …), where a concatenation sits at a SELF-determined position the
  v1 fragment never accepted (`rdsOf?` reads it, `fragG` refuses it). The word-level theorems take instead
  `fragW`: `fragG` with concatenations accepted, recursing with `fragW` at the context-determined children and with `fragG`
  at the self-determined ones (`&&`, `||`, `!`, reductions, `?:` conditions). The v1 theorems did not move; the word-level
  ones changed their hypothesis type and the head of the binary and unary arms (`fragW_bin_ctx`, `fragW_bin_self`).
* **A tactic-vocabulary cost, measured.** A concatenation operand needs `pcnt` in the sv_equations normal form (the lists of
  `CombEqTactic`) and its marker obligation needs the rigid width: unfolding `Sk.rmax` and `Sk.maxO` (25 equations) cost
  +1.0 % to +1.3 % on EVERY proof that calls `sv_equations` (a fixed ~900 heartbeats per call, structure proofs unchanged);
  a single rewrite rule `Sk.rmax_cat` costs +0.2 % to +0.6 % and gives the same output. A third change, `width_mk_toArray` in the
  plain tactic, was reverted because it renumbered the `width_k` goals of the `mul_tree` reference dump.
* **Dumps**: the 24 goal dumps are identical to those of gate 3a (so 23 identical to `afterB0` plus the intended
  `comb_proc/comb_errors` change).
* **Examples**: 55 Example modules build, default heartbeats. `comb_word/cat_add`: `s = {1'b0, a} + {1'b0, b} + cin`
  (bare concatenations), `t = {2'b0, a} + {b, 1'b0}` (a marker around a concatenation), `w = cin ? {a, 1'b0} : {1'b1, a}`,
  `e = {a, b} == {b, a}`; `cat_add_correct` for every `N ≥ 1` in 121 627 heartbeats.
* **Heartbeats** (against the 3a table `hbm/m2`): every theorem between -0.2 % and +0.6 %; `sbox_table` `solution` 190 068
  (+0.1 %, margin 5.0 %); `add_n` `solution` +0.5 %, `add_mux` +0.4 %, `add_proc` +0.2 % (re-measured with the final tactic
  lists; the multiplier references were measured with the heavier intermediate lists and are at most +0.5 %: an upper bound).
* **Xcelium 24.03-s004** (label `wpb2`): `wl_cat_add_n1/n2/n4/n8`, 905 cycles (exhaustive for N ≤ 4, random 8-bit,
  x/z in the operands and in the carry), 4 of 4 `XREF-MATCH`.
* **Not done, recorded.** A concatenation as the LEFT operand of a shift (accepted in the review ruling's fragment, but
  `instDivOperand2` lowers its parts through `instDivParts2`, a third instantiation function, and the six-kind operand
  analysis of the shift lemmas gains a seventh kind): refused with the shift-operand message. The part of a concatenation
  stays a literal or ONE access (`{a < b, a}` and the like are `Part.cmp`, stage 3c, size to be reported first).

## 12. Gate 4 (design delta, before the Lean work): selects, replication, constant references

Status: DESIGN (2026-11-01, branch `wpb2g4` on svgolf-prep `fdfa7419`). Scope given by the lead: (a) constant part selects
over literally-bounded declarations (`x[hi:lo]`, "legacy part select"), (b) replication `{N{x}}`, (c) the loop-indexed
whole-row access of a 2-D packed array, (d) a genvar- or parameter-valued shift amount (`a << i`, `a << N`, `x << (N-1)`);
value order for real code (survey, census, fdiv spike): (a), (b), (d), (c). Everything about the recognizer below is READ from
`CombView.lean` / `Param2.lean` / `extract.py`; the diagnosis of (c) is MEASURED (probe designs `g1`..`g6`, `m1`, `m2`, `v1`,
`v3`, `v4` through `sv_structure` and a `#eval` of the summary's accesses, 2026-11-01).

**12.1 Diagnosis of (c): a loop-indexed row is read as a one-bit select of a two-dimensional declaration.** Mechanism, three
steps, each measured:

1. *The extractor's encoding.* For a select over a declared packed signal whose range is canonical `[hi:0]`, a label that is not
   static (a genvar, any expression of one) keeps the LEGACY encoding (`_sym_array_select_depth1`, `extract.py:12959`: `ArraySel`
   only for static labels over a parameter-dependent range, or for a non-canonical range). For a two-dimensional base the
   legacy node is `BitSel{value: Ident r (12 bits), index: i + 1}` with the node's own `width` field `3`: it denotes a ROW, and
   says so only through that annotation and through the model (`PExpr.bitSel`: "over a multi-dim packed base this reads one
   `elemW`-bit chunk"; `instExpr2`'s `.bitSel` arm is `.slice base (i * ew) ew` with `ew = elemOf elems base`). A constant or
   parameter row index (`r[0]`, `r[N]`) over a parameter- or localparam-dependent range is static and comes out as
   `ArraySel` with one index; two indices (`r[i][k]`) are always `ArraySel`.
2. *The recognizer.* `leafRd?` and `tgtOf?` read every `.bitSel (.ident n) i` as `Acc.bit n (affine i)`; `elemAcc?` is the only
   producer of `Acc.row`, and it sees `ArraySel` only. The summary of `g1` (`assign r[i + 1] = ~r[i]`) is
   `(Acc.bit "r" (i + 1), [Acc.bit "r" i])` (MEASURED); the constant rows of `m2` are `Acc.row "r" C 0`.
3. *The structural check.* `Summary.accOk (.bit n _)` accepts a declaration of zero or one packed dimensions only, so `r[i + 1]`
   "does not match the declaration of `r`" in every dimension form (`g1` localparam, `g3` parameter, `g2` literal) and in every
   statement form. MEASURED, `sv_structure`: `g1`, `g3`, `g6` fail on exactly the loop-indexed row accesses and on nothing else;
   `g5` (constant rows, loop-indexed cells) and `v3` (constant rows, parameter dimensions) pass; `m2` passes; `g2` and `m1`
   (literal dimensions) fail even on `r[0]`, `r[3]`, because with literal bounds a constant label is legacy as well.

*The five shapes of WP-PROC's note* (assign or `always_comb`, N or 2N wide, `s1`, `v6`, `t1`, `t2`, `t3`) are all this one
mechanism: the row select `p__1[i + 1]` is a genvar-indexed select over canonical `[N:0][W-1:0]`, hence a legacy `BitSel` whether
it sits in a continuous assign (measured on `g1`, `g6`) or as the target of an `always_comb` leaf (measured on `v4`, the
PROC-NOTE shape: `BitSel{width: 8}` on `p1`; `p1[0]` and `p1[N]` are `ArraySel`). `tgtOf?` is the one function that reads the
target of an `assign` and of an `always_comb` leaf, so the leaf shape does not matter; the width (N or 2N) does not matter
either, only the rank of the declaration; the note's remark that "a continuous assign gets `ArraySel`" holds for its static
labels only. The one-bit chain `s2` passes because its declaration has one dimension. "`sv_structure` reads them" in the
note is the advisory `sv_structure?` (it describes the summary and never calls `accOk`); the tactic itself, and so
`sv_equations`, stops in `structProblems`.

*Fix (recognizer side, no extractor or envelope change):* in `leafRd?` / `tgtOf?`, a `.bitSel (.ident n) i` over a two-dimensional
zero-based declaration `[hi:0][hi:0]` is `Acc.row n (m2 + 1) (affine i)`; over a 0- or 1-dimensional one it stays `Acc.bit`. All the
row machinery (`Acc.win`/`lhs`/`accExpr`, `accOk`, the `AccGeom` row case, the `inRange` obligations, `arrayElemRead`-side lemmas
of the `arrayElem` row case) exists and is used by `m2`/`v3` today. New proof work: (i) the instance lemmas for the `.bitSel` leaf
gain the row case (`instExpr2 (.bitSel (.ident n) i)` is `.slice (.ident n) (i * ew) ew`, and `Acc.lhs (.row n w r)` is
`.slice n (r * w) w`, so the two sides agree when `ew = w`); (ii) `Ctx.elems` knows only element width one
(`EW n = some 1 → elems.lookup n = some 1`) and becomes `EW n = some ew → elems.lookup n = some ew`, its three constructors
following `buildElems`. An extractor-side alternative (`_sym_array_select_depth1` answers true for a base of two or more
dimensions) is three lines but changes the envelope of every design with such a select and lives in the lane WP-PROC is
editing; the recognizer side is mine and independent of it. Size: 1.5 days. Risk: low to medium (the `.bitSel` branch of five leaf
lemmas splits on the declaration's rank, a decidable fact the summary already carries).

**12.2 (a) Literal-bound constant part selects.** The same legacy mechanism: `x[hi:lo]` over a literal-bounded vector is
`PartSel{value: Ident x, msb: Int, lsb: Int}` (measured: `m4`), refused by `leafRd?` / `tgtOf?` as "legacy part select". Model:
`instExpr2`'s `.partSel` arm is `.slice (ident n) (l * ew) ((m - l + 1) * ew)` under `0 ≤ l ≤ m`, `msb.isInt env`; for a
declaration of one zero-based dimension (`ew = 1`) this is `accExpr σ (.part1 n hi lo)`, an access the recognizer already has
(`partAcc?` for the `ArraySel` form). So: an arm `.partSel (.ident n) (.int hi) (.int lo)` → `Acc.part1 n (const hi) (const lo)` in
`leafRd?`, the same in `tgtOf?` for `PLhs.partSel`, the instance lemma next to the row case of 12.1 (`msb.isInt` is `rfl` for
literal bounds, `0 ≤ lo ≤ hi ≤ m` is the existing `part1` geometry), nothing in the skeletons, the shape theorems or the x-free
layer. Not covered, refused with a message that says why: a part select of a two-dimensional base (rows), bounds that are not
literals over a literal declaration (those are `ArraySel`, already read), a packed-struct member select (the same node, read
as a part select of the whole struct: works when the struct is one vector). Size: 1 day; examples: `rotl` by concatenated part
selects of a literal-width port (the ARX idiom), field unpacking of a 16-bit float; rows `wl_partsel_*`.

**12.3 Prerequisite R for (b) and (d): constant references and their scope.** A replication count `{N{x}}` and a shift amount
`i` are constants of the instance (`evalInt` of a parameter or genvar reference); the shape theorems need the environment to
bind the names they mention (`Ctx.agree` for `n ∈ ns`, `ns` = the parameters and the loop variables of the site). For accesses
this comes from `AccOK`'s `∀ x ∈ a.affs, ∀ n ∈ x.names, n ∈ ns`, which the summary's structural obligation `affNames ⊆ params ∪
loop variables` discharges. A constant reference is not an access, so the same obligation has no source today. Proposal: a
derived `TSite.cnames` (the genvar and parameter names mentioned by constants in the right-hand side, from `PProcess` and the
`PTR` leaves; no new field, no change to the many `⟨pos, tgt, rds, proc, more⟩` constructors), one more conjunct in
`comb_view`'s structural obligation (decidable, in `structProblems` with a message of its own), and one more hypothesis `hcn` in the
word-level shape theorems, discharged next to `hacc`. Size: 2 days, mechanical; (b) and (d) cannot start before it.

**12.4 (b) Replication.** `PExpr.repl count arg`; the model: `.repl n (instExpr2 (selfWidth arg) arg)`, self-determined, rigid in
`fitExpr2` (as `.concat`); the x-free layer already has `Expr2.repl` (`xfWidth = n * w`, bit `k % w`, soundness `evals_repl`).
Skeleton: `Sk.rep (cnt : Aff) (p : Part)` (the argument a literal or ONE access, as a concatenation part) with width
`cnt * p.wid`, `low = .repl n (Part.expr p)`, bit `p.bit (k % p.wid)`, contract `cnt * w = tw` (a replication of the wrong width
carries a marker, `rsz false`, like a concatenation); recognizer arm in `rdsOfW?` (count: `affOf?`, parameters only, `0 ≤ cnt` is
an obligation), `isOpW`, `cnt`/`skT`/`fragW`, and `Part.rep` so that `{ {K{1'b0}}, x }` (zero padding, the commonest use) is a
concatenation part. Glue: `BitVec.replicate` (`bv (w * n) (fun k => f (k % w)) = (bv w f).replicate n`, one `getLsbD`
extensionality). Idioms it opens (survey: 104 files, 31%): the AND mask `a & {N{b[i]}}` (clmul, array multiplier partial
products), zero and sign padding. Cost estimate: one constructor with arms in the same eight functions as `Sk.sh` (+0.1 % to
+0.3 % heartbeats expected, no new simp name beyond `XF.repl`'s unfolding if the equation prints through it), the shape arm
(`instExpr2` of `.repl` + `fitExpr2_rigid`), the `Part.rep` arms (`partsT`, `Part.wid/bit/expr`, `partLeaves`, `partKnown`,
`partsRd?`, `parts_shape`): 2.5 days after 12.3.

**12.5 (d) Shift amounts that are genvars or parameters.** `shOpdRd?` reads literal, `.int` and accesses. The lowering of
`a << i`: `instDivOperand2 false 32 (.genvarRef i)` is `.lit (LVec.ofInt 32 (σ i))`, width 32, the same node as an unsized
constant with value `σ i`; for `a << N` with `parameter int N` the same (the width is the parameter's declared width: 32 for
`int`, other types need the `pwidths` fact; the first step takes genvars and `int` parameters, with the width a decidable
side condition). Skeleton: `Sk.cref (a : Aff)` (an affine constant of the instance: `low = .lit (LVec.ofInt 32 (a.eval σ))`,
bit `XF.constBit (a.eval σ) 32`), reads nothing, names recorded through 12.3. `x << (N - 1)` and `a << (i + 1)` need the operator
node the model builds for a binary constant (`instDivOperand2`'s binary arm: `.binary .sub (lit N) (lit 1)`), i.e. a second node
`Sk.cbin` over two constant leaves; its bit function is `XF.subBits 32 …` and the glue is `XF.bv_subBits` +
`XF.bv_constBit`; I would do `cref` first (1 day after 12.3) and `cbin` (`+`, `-` of a reference and a literal) as a second step
(1 day). The equation reads `XF.shlBits (XF.zext W a) 32 (fun x => XF.constBit ↑i 32 x) k` under the loop quantifier, and
the glue goes through `XF.bv_shlBits` with `(bv 32 (constBit i 32)).toNat = i` (`i < 2^32`). The clmul customer
(`p ^= a << i` in a lifted loop) also needs (c) (the carried row `p__1[i + 1]`), so (c) and (d) land together for it.

**12.6 Plan, sizes, acceptance.** Stages: **4a** = (c) + (a) (no new infrastructure, 2.5 days, the recognizer only: every
existing theorem and dump unchanged, the five PROC-NOTE row shapes and the literal part selects of the ARX/FP designs become
provable); **4b** = R (12.3) + (d1) (`Sk.cref`); **4c** = (b); **4d** = (d2) (`Sk.cbin`). I propose to report after 4a and after
4c; `(c)` goes before (b) and (d) although the value order is (a), (b), (d), (c) because it is the cheapest and unblocks the
lifted row chains of WP-PROC, and (b)/(d) wait for R in any case. Per stage the bar of 3a/3b: 24 dumps identical (the new arms do not
fire on them), no theorem more than +1 % except new ones (one new `Sk` constructor costs +0.3 % to +0.8 % per proof; the
rewrite-rule discipline of 11b applies to the tactic lists: a single rule per new shape, measured before and after), Xcelium
rows for every new shape (row designs: `wl_rowloop` (loop-indexed rows read and written, literal, localparam and parameter
dimensions, N and 2N wide), `wl_partsel` (literal-bound part selects read and written, x/z in the selected window),
`wl_repl`, `wl_shl_gen`), examples with theorems for every `N` (a row chain `r[i + 1] = ~r[i]` with the closed form of
`r[N]`, a rotate by part selects, the AND-mask multiplier row, the genvar-shift clmul), register, PROVING and changelog entries.
Not in gate 4: a concatenation as the left operand of a shift (deferred, lowest priority), `Part.cmp` (3c: size report first),
indexed part selects `x[i +: w]`, 3-D packed arrays.


## 13. Gate 4a results: whole rows of a two-dimensional array and constant part selects (2026-11-01, branch `wpb2g4a` on svgolf-prep `898f76d1`)

Stage 4a of section 12.6, (c) + (a): recognizer only, 326 inserted and 70 deleted library lines in seven files; the skeletons, the
shape theorems, the x-free layer, `AccGeom`, `accGeom_of` and every tactic list are unchanged.

* **(c) the diagnosis of 12.1 held; the fix is `bitAcc?`.** `leafRd?` and `tgtOf?` read a `.bitSel (.ident n) i` through
  `bitAcc? ds n a : Except String Acc`: over a zero-based two-dimensional declaration it is `Acc.row n (m2 + 1) a` (the access
  `elemAcc?` makes of the `ArraySel` form of the same row, so `accOk`, `AccGeom`, `Acc.win/lhs/rd` and `accExpr` are the existing
  row machinery), over anything else `Acc.bit n a` (a declaration whose ranges are not zero-based stays `Acc.bit` and is refused by
  `accOk`: the message is the old "does not match the declaration"). The five shapes of WP-PROC's note are this one case (assign or
  `always_comb`, N or 2N wide): `v4` of the diagnosis is `wl_rowloop`'s third part. MEASURED (probe `pg4a`): the summaries of all five
  designs have `Acc.row`/`Acc.part1` accesses with `accOk = true`; `sv_structure` and `sv_equations` print the row equation over
  `rmN W (↑i + 1) 0 + k` (stride `↑N`, `2 * ↑N`, `3`).
* **A trap, recorded: the result of a recognizer must be an `Except`.** The first version was `bitAcc : … → Acc` inside `.ok (bitAcc …)`;
  the tactic reads the summary by `whnf`, which stops at the `.ok` constructor, so the payload printed as
  `match bitAcc [declarations…] "r" … with | Acc.whole n => …` inside every equation. `bitAcc?` returns the `.ok (Acc.row …)` itself (as
  `elemAcc?`/`partAcc?` do), so the whnf of `leafRd?` exposes the constructor.
* **(a) constant part selects, and a free generalization.** `.partSel (.ident n) msb lsb` is `partAcc? ds n [] .range msb lsb`: the
  `Acc.part1` the `ArraySel` form of the same select had (a zero-based one-dimensional declaration; a part select of a row is not read). The
  design delta said "literal bounds" because the model's `.partSel` arm needs `msb.isInt env ∨ m < 2^31`; with `affOf?_sound` giving
  `isInt` for every affine bound the arm is proved for bounds affine in the genvars and parameters at no extra cost, which reads
  `y[4*i+3:4*i]` inside a generate loop (`ps_gen`; the extractor emits it as a legacy `PartSel` over the parameter-dependent range). It
  reaches every leaf position of the word-level fragment (`resizeRd?`, the `Resize` arm of `rdsOfW?`, `shOpdRd?`, the marker arm of
  `skT`; the six leaf kinds of a shift operand are now seven) and the target of an assign.
* **Proof work (the pre-registered "`Ctx.elems` generalized" became a new field).** `Ctx.elemsG : DG n = some ds → elems.lookup n =
  some (elemWOfDims ds)` (`DeclT.elemW_vals` is its source; `ctx_of_env` proves it from the declaration), with `ctxElemsRow`
  (a row is `(m2 + 1).toNat` wide) and `ctxElemsOne`; the v1 field `Ctx.elems` and its five consumers are unchanged, the three `Ctx`
  constructors gained the field (declared BEFORE `elems`: in a structure a later field sees an earlier field of the same name, not the
  parameter). Three facts for a part select (`inst_partSel`, `selfWidth_partSel`, `instLhs_partSel`, from `instExpr2_partSel_ident`,
  `selfWidth2_partSel_of`, `instLhs2_partSel`); new arms in `inst_leaf`, `instLhs_acc`, `leaf_eq`, `instLhs_acc_w`, the five
  `∀ v`-recognizer theorems and the shape theorems (`skT_shape`, `skT_shapeC`: one copy of the bit-select arm); `tgtOf?_cases` and
  `divW_eq_selfW` changed their statements (the second takes the context: for an undeclared base `selfWidth2` of a part select has a
  constant-parameter arm that `divOperandWidth2` has not, so the equality is a fact about declared bases). Pins:
  `bitAcc?_cases`, `DeclT.elemW_vals`, `ctxElemsRow`, `ctxElemsOne`, `inst_partSel`, `selfWidth_partSel`, `instLhs_partSel`, and the
  changed theorems, in `CombWordPins` (axioms: `propext`, `Classical.choice`, `Quot.sound`).
* **Dumps**: the 24 goal dumps are identical to those of gate 3b (`cmp3.sh`: identical 24, differing 0; the new arms do not fire).
* **Examples** (`comb_word`): `row_chain`, `row_chain_lp` (rows `2N` bits wide over localparams), `row_chain_lit` and the negatives
  `neg_part_nz`, `neg_row_nz`, `neg_row_3d` (messages pinned); `ps_rot`, `ps_gen`. Theorems: `row_chain_correct`,
  `row_chain_lp_correct`, `row_chain_lit_correct` (`y = if R % 2 = 0 then x else ~~~x`, every `N ≥ 1`, from ONE induction over the rows,
  `row_chain_gen`; the structure goals close with `sv_rowmajor; omega`, the two coverage goals of the chain by naming the writer),
  `ps_rot_correct` (`x.rotateLeft 7`, `x.rotateLeft 8`, `x.extractLsb' 10 5`), `ps_gen_correct` (`~~~x`, every `N ≥ 1`); heartbeats 126 511,
  133 439, 120 369, 35 246 and 89 137 (limit 200 000, defaults). Hints for the five designs pinned verbatim.
* **Heartbeats** (against the 3b table `hbm/m4`): every measured theorem between -0.3 % and +0.5 % (largest: `sbox_bp`
  `bp_interface`, 263 heartbeats; `add_mux_comb` +0.3 %); `sbox_table` `solution` 190 075 (+0.0 %, margin 5.0 % under the default limit).
* **Xcelium 24.03-s004** (label `wpb2`): `wl_rowloop_n1/n2/n3/n4/n8` (chains over parameter, localparam and literal
  dimensions, an `always_comb` per iteration over rows, x/z travelling along the chain) and `wl_partsel_n1/n2/n4` (rotation, byte-swap
  targets, field, genvar-affine windows, an x or z at every position of `x` and of `g`), 1 212 cycles, 8 of 8 XREF-MATCH, and the multi-point cross-check agrees.
  A finding about the second oracle: the first draft of `wl_rowloop` wrote `assign s[0] = '0` and `always_comb s[i + 1] = …` into one
  variable; slang and Xcelium accept it, Icarus does not ("reg s cannot be driven by primitives or continuous assignment"); the row now writes every row
  procedurally.
* **Not done, recorded.** A part select of a ROW of a two-dimensional array (`r[i][3:0]`) is read only in its `ArraySel` form; an
  indexed part select `x[i +: w]`; a row select over a first range that is not zero-based (3-D arrays are refused at the declaration). Next: 4b
  (R, the constant references, and `Sk.cref`).

## 14. Gate 4b results: a genvar as the amount of a shift, and the scope of a constant (2026-11-01, branch `wpb2g4b`)

Stage 4b of section 12.6, R + (d1), on the tip merged with svgolf-prep `68e270e4` and github/master `8a5e622c` (one merge fix: the
off-prem lane's new `PStmt.forLoop` needed refusal arms in the always_comb recognizer, six arms; no conflict touched
`CombView`/`CombEq*`).

* **What is read.** `a << i` and `a >> i` with a BARE genvar as the amount, in an `assign` (and in the family of a generate loop).
  `shAmtRd? ds e = .ok []` for `.genvarRef _`, else `shOpdRd?`; used by the shift arm of `rdsOfW?` for the amount only. The model: `divOperandWidth2 (.genvarRef _)`
  is 32 and the default arm of `instDivOperand2` gives `fitDivOperand2 s c (some 32) (.lit (LVec.ofInt 32 v))`, the node an unsized constant gives;
  the genvar under a `Resize` marker has its own arm (`negGenvarWidened`) and is not read.
* **`Sk.cref (a : Aff)`**, the one new constructor: a twin of `Sk.const` (width 32, no leaves, not an extension, value `a.eval σ` at its context width); every arm
  (twenty-five, in `CombEqBase` and `CombEqPlain`) that has a `.const _` case has the twin (copied by a script; the three arms that read the value are written out),
  `skT (.genvarRef g) = .cref (Aff.var g)`, `cnt (.genvarRef _) = 0`. The x-free layer needed only `xf_lit_ofInt` again.
* **R as built, against the plan of 12.3.** No new `TSite` field, no new conjunct of `StructOk`: `PExpr.cnames` (the genvars named as shift
  amounts), `TSite.cnames` (from `proc`), and `TSite.affNames` now ends with `st.cnames`, so the fourth conjunct (every index name is a parameter or an
  enclosing loop variable) and its message cover the constants. `site_cn` (from `StructOk`) and `SiteCtx.cn` deliver the fact per located site. The shape
  theorems take `hcn : ∀ n ∈ v.cnames, n ∈ ns` (seven theorems, recursion included: a binary operator's, a unary's, a ternary's, a marker's `cnames`
  are `cnames_binary_l/r`, `cnames_unary`, `cnames_resize`, `cnames_ternary_c/t/e`; a shift amount's name is `cnames_amount`). R took about one day of edits (the plan said two); the v1
  theorems did not change; the two proofs that unfold `TSite.affNames` (`siteCtx_of_reach`, `site_ok`) gained one `Or.inl`.
* **The proc chain does not carry the scope.** A constant in an `always_comb` leaf would need `hcn` through the tree theorems (`PTR`, `PLfR`: a dozen call sites).
  Instead `fragOkL v = fragOk v && v.cnames.isEmpty` replaces `fragOk` in `leafL?`, `leafW?`, `armLeaf?` and in `PTR.Ok`/`PLfR.Ok`, so the leaf is refused with the
  ordinary message, and the proc theorems get `hcn` from `fragOkL_cn` (an empty list). A genvar amount in a leaf (`if (b[i]) p ^= a << i`) is the next gate, with the lifted
  procedural loops of WP-PROC.
* **Parameters were not read.** `a << N` lowers the amount at the parameter's declared width (`(E.pwidths.lookup n).getD (paramNWidth E n)`), a fact about
  `paramEnv2`'s typed-parameter table that the summary does not carry; it would be one more `Ctx` field plus a decidable structural check that
  the parameter is `int`/`integer` (width 32), and a proof about `filterMapM` over the parameter list. Genvars are always 32 bits.
* **A semantic finding.** The amount is 32 bits wide, so a genvar of `2^32` or more wraps: the printed equation `XF.constBit ↑i 32` is exact, but a theorem that says
  "row `i` is `x <<< i`" needs `N ≤ 2^32` (`shl_gen_correct`).
* **Dumps** identical to 3b (24 of 24). **Heartbeats** (against the 4a table `hbm/m5`): -0.2 % to +0.7 % everywhere except `sbox_table` `tbl_struct` +1.4 % (+614 of 45 297: its 256 sites
  each pay the `TSite.cnames` unfolding of `affNames`); `solution` 190 807 (+0.4 %, margin 4.6 %). A new constructor with its arms cost nothing measurable
  (`mul_tree` solution +0.0 %).
* **Examples/rows**: `comb_word/shl_gen` (`shl_gen_correct`, 84 388 heartbeats), `neg_shift_gv`; rows `wl_shl_gen_n1/n2/n3/n4/n8`, 680 cycles, 5 of 5 XREF-MATCH on Xcelium 24.03-s004.
* **The customers** (`svgolf/tests/clmul/attacks`, first wall of each, MEASURED): `gen_word_pp_chain`, `gen_mask_replication`, `gen_always_step`: replication; `gen_size_cast`: a size cast
  `(2*N-1)'(a)` as the LEFT operand of a shift (the operand analysis has no cast kind); `gen_pp_zerofill`: the generate-for header `for (i = N; …)` (start not a literal). So (d1) alone
  moves none of them; the path is 4c (replication), a size-cast operand, a fill as an arm of `?:`, and the generate-for start.

## 14b. Gate 4c results: replication `{N{x}}` (2026-11-02, branch `wpb2g4c` on `wpb2g4b`)

Stage 4c of section 12.6, (b), on the tip of gate 4b (`87f0e2b4`). Plan 12.4 against what was built:

* **What is read.** A replication of a SIZED LITERAL or of ONE access that is not a whole signal, with an AFFINE count, as a part of a
  word-level concatenation (`{ {K{1'b0}}, x }`, the zero padding) or as a whole right-hand side or an operand of a word-level operator
  (`a & {N{b[i]}}`, `{4{x[1:0]}}`), in the `assign` chain. The extractor writes the braces of `{K{1'b0}}` as a ONE-PART `Concat`
  (`Repl{count, operand: Concat[Literal]}`): the recognizer reads `.repl c (.concat [e])`, `repArgRd?`; a concatenation of several parts
  is refused (the message says to write it into a signal first). A whole signal is refused by `notWhole` (its width is the declared
  one, which `Acc.wid` does not read: `Acc.wid (.whole _) = 0`).
* **Skeleton: two `Part`s and one `Sk`, not `Sk.rep (cnt) (p)` of the plan.** `Part.replit (c : Aff) (v : LVec)` (width `c * v.width`,
  bit `v.boolAt (k % v.width)`, expression `.repl c (.concat #[.lit v])`) and `Part.reprd (c : Aff) (a : Acc)` (width `c * Acc.wid σ a`,
  bit `accBit σ rd a (k % Acc.wid σ a)`), and `Sk.rep (p : Part)` for the replication that is a whole operand; `partsT`/`skT`
  build them from `.repl c (.concat [.lit v])` / `.repl c _` (`repAff c`, the count's `Aff`). The arms are the `.cat` arms
  (twenty-five, copied by a script). `pcnt`/`cnt` of a replicated literal is 0, of a replicated access 1.
  A replicated access is never whole: `partKnown` checks `!a.isWhole` (the x-free layer reads the access's own window width).
* **A separate word-level part recognizer.** `partRdW?`/`partsRdW?` (literal | replication | `rdsLeaf?`) are used by `rdsOfW?` for a
  concatenation and for the replication itself; the v1 `partRd?`/`partsRd?` and their theorems are untouched, so v1 positions
  (`&&`, a reduction operand, ...) keep refusing a replication (`neg_repl_selfdet`), and `partsT_of_ne` gained one hypothesis.
* **The count is a constant of the instance (R again).** `PExpr.cnames` names the parameters/genvars of a count, `TSite.affNames`
  lists them (fourth `StructOk` conjunct, unchanged), and its NON-NEGATIVITY is one new conjunct of `InRangeObl` guarded like
  `more`: `(if ∀ b ∈ s.lsites, b.site.rcounts = [] then True else ∀ ls, Loops.all ls.hdrs σ fun σ' => ∀ c ∈ ls.site.rcounts, 0 ≤ c.eval σ')`,
  with two new `TSite` fields `cnames`/`rcounts` (stored by the recognizer, read by projection like `more`). `ConstOK σ ns v` (names in scope and counts non-negative)
  replaces `hcn` in the word-level theorems; `site_co`/`SiteCtx.cn` deliver it per located site; `InRangeObl.rc_all` extracts it. A parameter
  count is non-negative by `Int.natCast_nonneg` in the normalization, so for `K : Nat` no `[inRange]` line is left (`[width]` is `K + … = …`, for `omega`).
* **The proc chain refuses it.** `fragOkL v = fragOk v && noConst v` (`noConst`: one cheap traversal, `noConst_spec` gives `cnames = []` and `rcounts = []`; a constant of the instance in an
  `always_comb` leaf is the next gate, with WP-PROC's lifted loops); the idx-freedom readers of the chain gained the replication arms
  (`inst_repRd_idxFree`, `inst_parts_idxFreeW`).
* **Plain netlists.** `inRangeObl_of_plain`'s premise `hp` (one traversal of the sites, as before) also says `a.site.rcounts = []`, so
  the third conjunct is vacuous; a flat netlist WITH a replication fails it and takes the normalization route (small designs).
* **Glue.** `BitVec.getLsbD_replicate` and `getLsbD_setWidth` (core): no new library lemma. The equations print as
  `if k < N then st.boolAt "x" k else false` (padding), `st.boolAt "a" k && st.boolAt "b" (i + k % 1)` (mask), `st.boolAt "x" (k % Int.toNat 2)`
  (`{4{x[1:0]}}`). The replication vocabulary (`PExpr.rcounts`, `repCount`, `repAff`,
  `affOf?`, `affBin`, `affMul`, `List.isEmpty_nil/cons`) is NOT in the tactics' six simp lists: it is passed to `simp` only for a design
  that contains a replication (`Summary.hasRepl`, decided by the tactic on the compiled summary; `replSimpLemmas`, `withRepl`: the first
  `simp only [pd, …]` pass, `sv_simp […]` in the equation loops, `first | (simp only […] at key; …) | …` for the netlist view).
  `LVec.width_mk_toArray` was not added to the equation lists either (it changes the pinned `cat_add` hint), so a replicated multi-bit
  literal prints its width unevaluated, as a concatenated one does.
* **Examples/rows**: `comb_word/repl_pad` (`repl_pad_correct`: `y = x.setWidth (N + K)`, every `N ≥ 1`, every `K`), `repl_mask`
  (`repl_mask_correct`: row `i` is `if b.getLsbD i then a else 0#N`), `repl_bits` (`repl_bits_correct`: `y = BitVec.replicate 4 (x.extractLsb' 0 2)`);
  negatives `neg_repl_whole`, `neg_repl_nonaffine`, `neg_repl_op`, `neg_repl_selfdet`, `neg_repl_leaf`; rows `wl_repl_n1k0/n1k2/n2k1/n3k3/n4k3/n8k5`.
* **Heartbeats (the budget of `sbox_table`), and what it cost to keep it.** Against the gate 4b table (`hbm/m6`): every measured theorem
  between -0.1 % and +0.5 %, except `sbox_bp` `bp_struct` +1.5 % (+1 899 of 128 066), `ps_rot_correct` +1.3 % (+460 of 35 257) and
  `sbox_bp` `bp_interface` +0.8 %. `sbox_table`: `tbl_struct` 45 880 (-0.1 % against 4b, +1.3 % over the gate 3b base 45 297), `solution`
  190 866 (+0.0 %, margin 4.6 % under 200 000), `tbl_interface` 13 399; `mul_tree` `tree_struct` +0.1 %, `solution` +0.2 %. New theorems:
  `repl_pad_correct` 95 840, `repl_mask_correct` 124 736, `repl_bits_correct` 58 662 (`shl_gen_correct` 84 977, +0.7 %). The FIRST build was not
  this cheap: +2.0 % to +3.5 % on almost every proof (`tbl_struct` 47 183, `solution` 192 963, margin 3.5 %: both over the limits set for this
  gate), from three things, found by measuring and fixed one by one. (1) The replication vocabulary was named in the tactics' six simp lists: a
  probe (`hb_in` around one `simp only`) says eight extra lemma names cost 21 thousand heartbeats per call (20 for the call without them),
  and a proof makes about a hundred calls; the vocabulary is now passed to `simp` only for a design that has a replication
  (`Summary.hasRepl`, decided by the tactic on the compiled summary). (2) `fragOkL` traversed every leaf of the always_comb tree twice
  (`cnames.isEmpty && rcounts.isEmpty`), 2.5 thousand heartbeats per leaf of a function of the nested `PExpr`, which is 650 on the 256-leaf case
  table of `sbox_table`: one function `noConst` now (`noConst_spec` gives both lists empty). (3) The constants of a site were thunks that
  every obligation had to unfold with `simp`: `forceSite` forces them at recognition time (`noConst` first, `PExpr.consts` for both lists in
  ONE traversal otherwise), so a site that names no constant carries `[]` literally. Measured NOT to matter: forcing `cnames` or only
  `rcounts`, the premise of the plain closure as `List.isEmpty` instead of a list equality (kept: it is cheaper in principle, identical
  to the unit in `sbox_table`). Axiom pins that moved with the proofs (standard axioms only): `siteOf?_proc'`, `siteOfP?_proc`,
  `siteOfP?_proc'` gained `Quot.sound` (through `noConst_spec`), `coverObl_of_plain` gained `propext`.
* **Dumps.** The 24 goal dumps (18 example probes, 6 task references) are byte-identical to those of gates 3b, 4a and 4b.
* **Xcelium** (24.03-s004, label `wpb2`): rows `wl_repl_n1k0/n1k2/n2k1/n3k3/n4k3/n8k5`, 736 cycles, 6 of 6 XREF-MATCH
  (K = 0, the empty replication beside another operand, included; x/z in every position of every operand).
* **The customers** (`svgolf/tests/clmul/attacks`, first wall of each design after this gate, MEASURED by `sv_structure` on the envelope
  extracted with `--top clmul_n`; the checker stage that stops most of them earlier is in the README table there):
  `gen_mask_replication`: NONE, `sv_structure` and `sv_equations` accept it (every obligation linear; only the proof of the clmul theorem is
  missing); `gen_word_pp_chain`: `'0` as an arm of `?:` (`site g_pp#0: unbased unsized literal inside an expression`); `gen_pp_zerofill`: the
  generate-for START `N`; `gen_always_step`: the `<=` bound of `for (i = 1; i <= N; i++)` (behind it: compound `^=` and a genvar in an
  `always_comb` leaf); `gen_size_cast`: the size cast as the left operand of a shift; `reduce_xor_column`: the indexed part select `+:`;
  `wally_chain`: `declaration s: packed bounds are not affine`; `gen_local_column`: the generate-local declaration (`GenerateDecl:Var`);
  `gen_unpacked_pp`, `func_oldstyle_xor`, `func_shift_xor`: out-of-tier module members (unpacked arrays, functions);
  `inst_karatsuba_1level`, `inst_karatsuba_1level_gen`: module instances; `proc_nested_for`, `proc_shift_xor`: `procedural process (always)`
  (their `for` loops); `always_star_rows`: the generate nesting of its `always @*` rows; `verilog2001_wire`: refused by the loader
  (`unrecoverable packed dimensions`); `inst_karatsuba_rec`: does not extract with `--top clmul_n` (self-instantiating top). One design of
  seventeen is through the tactics; the next candidates are in section 15.
* **Not run here**: `tests/run.py`. The checker refuses the clmul task in this tree at its `infrastructure` stage (`task.json` sets
  `allow_bv_decide: true`, which the checker of this tree does not support), so the advisory entries I changed in `tests/expected.json`
  (`gen_mask_replication` now `in_fragment: true`; `gen_word_pp_chain` now stops at `unbased unsized literal`) were checked by the tactic
  messages above, not by the harness.

## 15. After gate 4c: the next gate-4 candidates, with size estimates (for the coordinator's choice)

The first wall of every clmul attack design is in section 14b (measured through `sv_structure`, then `sv_equations`). What stands
behind them, one row per feature; sizes are by the cost of the closest built gate (4a: 2.5 days planned; 4b: R in one day, the constant
in half a day; 4c: see 14b), `S` = about one day, `M` = two, `L` = three to five. "Unlocks" names the attack design whose current first
wall it is.

| # | Feature (what is not read) | Where it stops today | Size | Unlocks (alone) | What it needs |
|---|---|---|---|---|---|
| 1 | the fill `'0`/`'1` as an arm of `?:` (`b[i] ? (aw << i) : '0`) | `site g_pp#0: unbased unsized literal inside an expression (allowed as a whole right-hand side)` | M (the plan said S: the arm has NO self-determined width, so `selfWidth2` of the conditional and `Sk.width`/`rmax` of `.tern` gain an `Option` case; `skT .fill`, `Sk.low`, `bitC`, the x-free `.fill` arm already exist) | `gen_word_pp_chain` (its only wall) | a `fragW` arm for a fill under `?:` only, the arm's recognizer case (`[]` reads), the `skT_shapeC` fill arm for a CONDITIONAL context, `Sk.WidthOkC` of the other arm alone, one `rhs_shapeC` tweak |
| 2 | a size cast `(2*N-1)'(a)` as the LEFT operand of a shift | `site g#0: operand of a shift that is not a signal access, a sized literal or an unsized constant` | M | `gen_size_cast` | `shLeftRd?` gets a cast case (`instDivOperand2` of `.cast w a`: the operand is converted to `w` bits BEFORE the shift: a `Sk.ext`-like marker with an explicit width), the width contract `w`, one shape arm; the extractor's `Cast` kind is already structured |
| 3 | a generate-for header with a `<=` bound (`for (i = 1; i <= N; i++)`) | `generate-for header outside for (g = <int>; g < <affine>; g++)` | M | `gen_always_step` (first wall; behind it: `^=` and a genvar in an `always_comb` leaf) | `hdrOf?` reads `.binary .sle` as bound `bnd + 1`; `Hdr.bndE` (the PExpr of the bound, kept for `hdrOf?_spec`'s inversion) and the model's unrolling of the loop condition must agree: a second spec shape |
| 4 | a generate-for START that is not a literal (`for (i = N; i < 2*N-1; i++)`) | same message | L | `gen_pp_zerofill` (then its `'0` arm: row 1) | `Hdr.c0 : Int` becomes an `Aff`: `Hdr.Rng`, `Loops.all`/`Reach`, the enumerations of `LoopsN/LoopsE`, `hdrOf?_spec`, the `Summary.hdrPaths`/`sound` lemmas (52 mentions of `c0` in eleven `Comb*.lean` files, counted) |
| 5 | a PARAMETER or localparam as a shift amount (`a << N`) | `operand of a shift that is not …` | M | none of the five (a spelling of the same constants) | one `Ctx` field for the typed-parameter widths (`paramNWidth`), a decidable structural check that the parameter is `int`/`integer` (32 bits), a `filterMapM` lemma over the parameter list; the shape arm is `Sk.cref` with a parameter (`Aff.var`) |
| 6 | a replication of a CONCATENATION or of several parts (`{2{a[0], b[1]}}`) | `replication of a concatenation of several parts` | S | none | `Part.repcat (c) (ps : List Part)` (one more constructor, the `Part.wid/bit/expr` arms are `catBit`/`Part.expr` mapped); the recognizer reads `.concat ps` through `partsRdW?` |
| 7 | a CONSTANT OF THE INSTANCE in an `always_comb` leaf (a genvar shift amount, a replication count) | `right-hand side outside the v1 fragment (a gate tree, a concatenation or a fill)` | M | none today (`gen_always_step` needs 3 first) | `ConstOK` through the `PTR`/`PLfR` theorems (`proc_shapeC` already takes it; a dozen call sites in `CombProcEq`, `CombProcLower`), `fragOkL` back to `fragOk`, the proc-chain `InRangeObl` consumer |
| 8 | `Sk.cbin`: expression shift amounts (`a << (i + 1)`, `a << (N - 1)`), stage 4d of section 12.6 | `operand of a shift that is not …` | M | none (the clmul styles use a bare genvar) | as planned in 12.5: an `Aff`-valued amount lowered at its own width |
| 9 | an indexed part select `x[i +: w]` | `indexed part select … (outside the v1 fragment)` | L | `reduce_xor_column` | a new `Acc` kind with a symbolic base and a width obligation; the write window of a target of this kind |

Not on the list because they are outside the tactics by KIND, not by distance: generate-local declarations (`gen_local_column`:
`GenerateDecl:Var`), unpacked arrays (`gen_unpacked_pp`), module instances (`inst_karatsuba_*`), functions (`func_*`), procedural
`for` loops in `always_comb` (`proc_*`: WP-PROC's lane), `always @*` (`always_star_rows`) and Verilog-2001 nets (`verilog2001_wire`:
rejected by the loader).

Reading of the table: the shortest path to a SECOND clmul design through the tactics is row 1 (`gen_word_pp_chain`, size M); the
design that is already read since 4c (`gen_mask_replication`) needs no further gate, only a proof. Rows 3 and 4 are the cost of
`gen_always_step` and `gen_pp_zerofill` and are large for one design each.
