# WP-G, S3a: a plain `case` with constant items (as built)

Status (2026-10-31, branch `wpgs2`): **S3a implemented** in the existing skeleton chain, with the proved
reference `tasks/aes_sbox/reference/sbox_table.{sv,lean}` (the 256-entry S-box table) and the Example
`Examples/system-verilog/comb_case`. Companion of `G23-NOTE.md` (S2).

## 1. The fragment

In an `always_comb` (alone, in a `begin … end`, or as a branch of an `if` tree): a PLAIN `case (subject)` with a
`default`, whose items are lists of KNOWN SIZED LITERALS as wide as the subject and whose arms are SINGLE
ASSIGNMENTS of the one target (`y = v;`, `v` a right-hand side of the fragment of S2). The subject is an
expression of the fragment, read once. Refused, each with its own message: no `default` (a latch), `inside`,
`unique`/`priority` (the extractor's `check`), an arm that is not one assignment (`begin … end`, `if`, `case`),
arms writing different windows, an item that is not a `.lit` (an unsized item arrives as a subject `Resize`: the
width-conversion message), an item wider than the subject (same). An item with an `x`/`z` bit passes the
recognizer and is refused by `sv_equations` (the equation fragment needs known literals).

**Deviation from the gate-0 design**: the arms are single assignments, not trees. The gate-0 plan had
`PTree.cases` with tree arms (a nested inductive over `List (List Expr2 × PTree)`); a single-assignment arm keeps
`PTree`, `PT`, `PTR` and `PSk` ordinary inductives (the arms carry Expr2 / PExpr / Sk values, not subtrees), so
every lemma about the new node is an induction over a LIST inside one arm of the existing `induction`. Trees as
arms (and with them default-then-override) are the follow-up and need a mutual or fuel-based induction.

## 2. What changed (file, declaration)

| file | change |
|---|---|
| `CombProcStmt.lean` | `caseItems`, `caseLow` (the lowering: `joinIte` of `anyGuard` per item, first match wins, ending in the default); `PTree.cases s its d` with `toStmt` (the flat `Stmt2.caseStmt`), `low`, `wf`, `noRead`, `noRdW`, `idxFree`, `bit`, `xfOk`; the list lemmas `symExec_caseItems`/`symExec_cases`, `reads_caseLow`, `drvWins_cases`, `mayW_cases`, `combViol_cases`, `anyGuard_xfWidth/xfBits`, `caseLow_xfWidth/xfBits`; one new arm in each of `symExec_tree`, `low_reads`, `drvWins_tree`, `mayW_tree`, `combViol_tree`, `noRdW_of_noRead`, `low_xfWidth`, `low_xfBits` |
| `CombProc.lean` | `PLf` (an arm: `t = v;` / `n = v;`), `PT.cases`, `PLfR`, `PTR.cases`; `instStmt2_tree` arm (`instItems2_arms`); the recognizer `armLeaf?`, `casePats?`, `caseArms?`, `caseTree?`, `caseStmt?` and their specs; arms in `low_idxFree`, `low_wf`, `low_noRead`, `tree_tgt` |
| `CombProcLower.lean` | `anyGuard_rdOK`, `caseLow_rdOK`, the arm of `low_rdOK` |
| `CombProcEq.lean` | `XF.caseSel` (the printed fold), `PSk.cases`, `pskArmsBit/Low`, `armRcnt/itemsRcnt/armSk/caseSkItems`, arms of `stmtRcnt`, `stmtSk`, `ptrSk`, `ptr_rds_len`, `ptr_sk_eq`, `ptr_sk_leaves`, `ptr_low_shape`, `psk_xfOk`, `psk_bit`; the bridge `XF.caseSel_table`, `caseSel_bv`, `caseSel_out` (section "A `case` over a table of literals"); `#pin_axioms` for all of it |
| `CombProcTactic.lean` | the three normalization simp sets gain `pskArmsBit`, `PskArmsOk`, `armRcnt`, `itemsRcnt`, `armSk`, `caseSkItems`, `patLit`, `PLfR.armRds`, `PLfR.rds`, `XF.caseSel_nil`, `LVec.width_mk_toArray` (`maxRecDepth` 4000 on the three macros) |

Existing pins that changed (all `[propext]`-only theorems that now also use `Quot.sound`): `CombProc.treeStmt?_spec`,
`CombProc.treeStmts?_spec`. No signature of an existing definition changed except the constructors added to
`PTree`, `PT`, `PTR` and `PSk` (and `PT.low`/`PTR.pt`/… on them).

## 3. Why a fold (`XF.caseSel`), and the arithmetic

Kernel evaluation, all 256 inputs of the S-box table, measured on the shared machine:

| form of the final `decide +kernel` | time | memory |
|---|---|---|
| the printed nested `if` / per-bit `XF.eqv` on `LVec` literals | 128 s | 6.2 GB |
| per-bit `XF.val` comparison | 12.2 s | 3.8 GB |
| lookup in the table of numbers, once per input (`XF.caseSel_table`) | 3.1 to 4.9 s | 1.4 GB |

So `sv_equations` prints one list (`XF.caseSel w subj [([pat bits], arm bits), …] default k`) and the bridge turns it
into `XF.lookupNat (XF.tblNat tbl) d.nat (XF.val xf w)`. `XF.caseSel_out` goes all the way from the equation of the
target to `lookup st y = some (LVec.ofBitVec (f x))`; the one fact it asks for is the closed `decide`.

## 4. Scale (the gate-1 measurement, repeated with the real rule)

`case` of 16, 64, 256 items on an 8-bit subject, default heartbeats, one Lean process (CPU seconds, whole file:
`load_design_sv2`, `sv_structure`, `sv_equations`): proxy (a 256-deep `else if` chain of `==`) 4.0 / 5.4 / 12.8,
real `case` 3.6 / 4.7 / 12.4; maximum resident set about 1.3 GB. `sv_equations` at 256 items needs between 160 M
and 200 M heartbeats in both (the default limit is 200 M). The proxy did not measure: the recognizer arm
(`caseArms?` over 256 items), the `Sk` width obligations of 256 patterns, the `PskArmsOk` simp normalization,
the 256 literal widths (`width_k`), the equation statement in its folded form. The real rule shows the first two
cost nothing visible and the widths are folded into the simp set (`LVec.width_mk_toArray`).

The reference `sbox_table` through `check.py`: ACCEPTED, `solution` stage 31.6 s (shared machine, default
heartbeats, no `set_option maxHeartbeats`), `comparator` 17 s, `leanchecker` 34 s, score 786.894 GE, depth 11.

## 5. Follow-ups

* Arms that are trees (`if`/`case` inside an arm) and default-then-override: the S3b node.
* Several written windows per body (S1b), unsized items (B2), `inside`.
* `sv_equations` heartbeats at several hundred items are close to the default limit; the obvious saving is to
  normalize the folded list once instead of per obligation.
