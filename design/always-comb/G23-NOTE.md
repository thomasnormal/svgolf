# WP-G, S2: operators in expressions (as built)

Status (2026-10-31, branch `wpgs2`): **S2 core + S2d implemented** in the existing skeleton chain; the staged
differential rows are installed and pinned (`87388d6a`, `harness/sv/xcelium_golden.json`). The design is
`G20-SPIKE.md`'s companion for S2: the spike that decided the shape of the shape theorem is `spike/S2Spike.lean`.

## 1. The fragment

`~e`, `!e`, the six reductions, `l && r`, `l || r`, `l == r`, `l != r` (operands of ONE width) and `c ? a : b`,
over accesses and known literals, in an `assign` right-hand side, an `always_comb` leaf and an `if` condition;
every operand exactly as wide as its context (the width contract of section 1.3 of the contract note, now the
`width_k` goal). `Resize` markers (an operand narrower than its context), `'0` and concatenations inside an
operator, `+ - * < > << >>`, unary minus and unsized constants stay refused, each with a message of its own.

## 2. What changed (file, declaration)

| file | change |
|---|---|
| `CombView.lean` | `binOk`; `rdsOf?` gains `.unary (~ !)`, `.reduce`, `.ternary` (reads in textual order c, a, b) and the binary operators `&& \|\| == !=`; the refusal texts |
| `CombViewThm.lean` | inversions `binOk_cases`, `rdsOf?_binary/_unary/_ternary/_reduce`; `RdOK.unary/reduce/logical/ternary` (`ternary` moved up from `CombProcLower`); the `instExpr2` / `selfWidth2` / `rigidMax2` equations of the new constructors (`ie_*`, `sw_*`, `rm_*`, the spike's section A); `inst_rd` |
| `CombEqBase.lean` | `Sk` gains `bnot lnot red land lor tern eqv nev`; `cnt`, `skT`, `fragG`; `Sk.width`, `Sk.SelfOk`, `Sk.WidthOk`, `Sk.bit`, `Sk.low`, `Sk.leaves`, `Sk.knownB`; `Sk.low_irrel`, `Sk.selfOk_widthOk`; `rdsOf?_len`, `skT_leaves` |
| `CombEqShape.lean` | `skT_shape` (five facts per expression); `gate_shape` is its corollary; `low_xf_gen` (the x-free width and bits in one induction) with `low_xfWidth`, `low_xfBits` as wrappers; the `XF.any_congr/red_congr/eqv_congr/any_one/eqv_one` helpers and the `Expr2` x-free facts |
| `CombProc.lean` | `inst_idxFree`, `fit_idxFree`; the condition message; new `#guard`s |
| `CombProcEq.lean` | `skT_selfWidth` and `cond_shape` become corollaries of `skT_shape` (statements unchanged; the pin of `skT_selfWidth` now lists `Classical.choice`) |
| `CombEqPlain.lean` | `Sk.decSelfOk`, `Sk.decWidthOk` for the new constructors: the flat-netlist fast path takes them |
| `CombEqTactic.lean`, `CombProcTactic.lean` | the four equation-normalization simp sets gain `Sk.SelfOk`, `Sk.width`, `XF.red`, `XF.any_one`, `XF.eqv_one` |

Unchanged: `CombKnown*`, `CombProcStmt`, `CombProcSummary`, `CombProcLower` (beyond the moved lemma), `CombEqThm`.
No signature of an existing definition changed: `Sk.low` and `Sk.bit` keep their arguments; the self-determined
operands are lowered at the dummy width `0` (`Sk.low` reads its width only at a `.fill`, and `Sk.SelfOk`
excludes it: `Sk.low_irrel`). The dw/tw threading B2 needs is B2's.

## 3. The shape theorem

`skT_shape` proves, for an accepted expression `v` whose skeleton fits width `w`: `selfWidth2 v = some w`,
`rigidMax2 v = some w`, and `instExpr2` at no context, at `w` and `fitExpr2 … w` all equal `Sk.low … w`. The
five facts are needed together: `~a` at context `w` requires `rigidMax2 a ≤ w` (fact R); `a && b`, `!a`,
reductions and `==` instantiate their operands at their SELF-determined width (`instExpr2 none`, `instExpr2
(selfWidth2 a)`); `c ? a : b` instantiates the condition at no context and the arms at `w`. The x-free side
(`low_xf_gen`) is one induction for the width and the bits because the operands of the self-determined
operators are lowered at their own width, which makes the width an argument of the recursion.

## 4. Pins and proofs

See the report of gate 1 (numbers, timings, the dumps). The example `Examples/system-verilog/comb_ops`
(`add_mux`, `ops_gen`, `ops_flat`, `ops_proc`, the negatives) is the acceptance battery; `add_mux_correct` is
a complete `∀ N ≥ 1` proof of the adder written with `~` and `?:`.
