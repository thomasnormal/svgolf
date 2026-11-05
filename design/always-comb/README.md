# WP-G, Gate 1: `always_comb` bodies in the `sv_comb` tactics

Status: DESIGN (Gate 1), written 2026-10-30. Nothing in `LeanModels/`, `Examples/`, the checker or the tests was
edited and no Lean, `lake`, `check.py` or `tests/run.py` was run. Every claim below is labelled MEASURED (Xcelium
24.03-s004, the extractor, a Python reference of the ls-sv rules) or READ (from the Lean sources) or
PLANNED. The evidence is in `probe/` (generators, the reference model, the raw `xrun` outputs) and `rows/`
(the staged differential rows) next to this file.

Contents: 1 the four-state contract; 2 the fragment; 3 the equations, knownness and names; 4 architecture and
soundness; 5 stage register; 6 differential rows; 7 plan and go/no-go; 8 risks and the lead's decisions; 9 recorded for
others (the M0 timed tier). The G2.0 spike plan is `G20-SPIKE.md`; the staged rows are runnable with `rows/run.sh`.

---------------------------------------------------------------------------------------------------------

## 0. What Gate 1 fixes

1. **Three different semantic contracts are not conflated.** A procedural `if (c)`, a conditional expression
   `c ? a : b` and a `case` treat an `x`/`z` selector three different ways (section 1). The tactics' netlist view
   states plain Boolean `if c then e1 else e2` equations; they are justified **only for known conditions**, and the
   knownness theorem (`CombKnown.reads_known`, WP-P) is what establishes that a condition is known (section 3.3).
2. **First fragment (S1):** `always_comb` (module level or generate-for body), blocking assignments, `if / else if /
   else`, ONE written window per process, every path assigns it (no latch), the body reads no window it writes (no
   self-read), conditions are 1-bit gate trees (`& | ^`) of accesses and literals. Equation per process:
   `x = if c1 then e1 else (if c2 then e2 else e3)`. No new operator, no `case`, no temporaries.
3. **Then, in this order, each only after its rows are green:** S1b multi-window bodies; S2 `~ ! ?:`, reductions and
   logical `&& ||` in conditions and right-hand sides; S3 `case` with constant items and SSA temporaries.
   Procedural `for` is a separate later gate (recurrence extraction) and is not part of this package.
4. **The knownness theorem needs NO change for any of these operators:** `Expr2.xfWidth/xfBits`
   (`CombKnownBits.lean`) already cover `~ ! ?: reductions === && ||` and `CombKnown.settled` is stated for
   concat targets. What changes is the recognizer, the skeleton type and the lowering lemmas (section 4).
5. **Soundness path:** the settle theory is stated for assign-only designs; `always_comb` enters through the
   EXISTING lowering `Design2.lowerComb` (`Comb2Proc.lean`, unchanged). The new tactics prove
   `(X.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'` from the same kind of summary obligations, and
   `sv_equations` reads the equations of the lowered design `d'`. No axiom is added; nothing is trusted that is not
   kernel-checked; the existing outputs for designs without `always_comb` stay byte-identical (section 4.5).

The honest size of Gate 2 is **5 to 7 slot-days for S1 plus the Gate 3 payoff** (PLAN2 assumed about one), and the
single biggest unknown is the lowering-mirror lemma at a symbolic index; section 7 puts a spike and a go/no-go in
front of it.

---------------------------------------------------------------------------------------------------------

## 1. The four-state contract

Sources. MEASURED on Xcelium 24.03-s004 on a licensed host (one run at a time, scratch
`/tmp/wpg/r1..r5`): r1 23 DUTs / 386 cycles, r2 5 DUTs / 79 cycles, r3 a 3-bit carry chain of `always_comb`
blocks over bits of one vector (130 cycles, exhaustive plus x/z), r4 the two Gate 2/3 fixtures at N = 4
(exhaustive) and N = 16 (3000 random vectors and corners), r5 the 9 staged differential rows (204 cycles).
`probe/model.py` is a Python transcription of the ls-sv rules AS READ from `Basic.lean` (`LVec.condTrue`,
`isKnownZero`, `ternary` = merge, `lnot`, the zero-extension of operands); it reproduces **all 465 cycles of r1 and
r2 and all 204 of r5 with 0 mismatches**, and an independent adder model matches r3 and r4. So the rules below are
Xcelium-true; that the LEAN model implements them is READ (`Basic.lean` has `#guard`s for the merge and the `1x`
rows; `Sem2.execStmt2` uses `condTrue`) and is verified in Gate 2 by the staged differential rows.

Notation: `c` is a 1-bit condition unless stated; `v` is 2 bits; values are `0 1 x z`.

### 1.1 Procedural `if (c) A else B` (the `if` rule: x/z means ELSE)

The then-branch runs iff the condition has **at least one definite `1` bit** (`LVec.condTrue`); everything else,
including all-`x`, all-`z` and `0x`, runs the else branch (or nothing, if there is no else).

| case | Xcelium (measured) | model |
|---|---|---|
| `if (c) y=a; else y=b;`, c = 0 / 1 | b / a | same |
| same, c = x, c = z | **b** (the else branch) for all (a,b) | same |
| `if (v)`, v = 01 10 11 | then | same |
| `if (v)`, v = 1x x1 1z | then (a definite 1 bit) | same |
| `if (v)`, v = 00 0x x0 xx zz 0z xz | else | same |
| `if (!c)`, c = x or z | **else** (`!x = x`, so the condition is not 1) | same |
| `if (c) y=b; else y=a;` (the "swapped twin"), c = x | a | same |
| so `if (!c) a else b` and `if (c) b else a` DIFFER at c = x (b versus a); equal for c in {0,1} | measured | same |
| `if (~c)`, c = x | else (as `!c`) | same |
| `if (!v)` with a 2-bit v | true ONLY at v = 00; every other v (01 10 11 1x x1 1z 0x x0 xx zz 0z xz) takes the else branch | same |
| `if (\|v)` (reduction) equals `if (v)` | measured equal on all 13 values | same |
| else-if chain, c1 = x/z | falls through to the second test (c1=x, c2=1 gives b) | same |
| nested `if` with x inner condition | the inner else | same |
| `y = 1'b0; if (c) y = a;`, c = x/z | y = 0 (the default survives) | same |
| value of the TAKEN arm only: `if (c) y=a; else y=b;` with c=1, a=x/z | y = x / z (copied unchanged, z stays z) | same |
| same with c=1 and b=x, or c=0 and a=x | y = the known arm (an x/z in the untaken arm does not leak) | same |
| two targets under one `if`, c = x/z | BOTH take the else arm | same |

Pinned rows: existing (Xcelium golden, already `XREF-MATCH`): `acg_cond_ok` (cycles 4, 5 are a = x, z),
`fa_comb_proc` (cycles 8 and 9: the temporary `t = a ^ b` is x and `if (t)` takes the else branch), `acg_nested_ok`, `latch_comb`;
staged: `wpg_if_x`, `wpg_if_chain` (section 6).

### 1.2 Conditional expression `c ? a : b` (the `?:` rule: x/z means MERGE)

If the condition has a definite 1 bit: the first arm. If every bit is a definite 0: the second arm. Otherwise
(no 1 bit and some `x`/`z`): the **bitwise merge** of the arms, a bit survives only if both arms agree on a known
bit, every other bit is `x`.

| case | Xcelium (measured) | model |
|---|---|---|
| scalar, c = x/z, arms (a,b) = (1,1) / (0,0) | 1 / 0 (equal arms survive) | same |
| scalar, c = x/z, arms (1,0) (0,1) or either arm x/z | **x** | same |
| vector arms 1100 / 1010, c = x/z | `1xx0` | same |
| arms 10x0 / 1010, c = x | `10x0` | same |
| arms 1z10 / 1x10, c = x | `1x10` (a z merges with x to x) | same |
| arms 1111 / 1111, 0000 / 0000, c = x | unchanged | same |
| 2-bit condition v = 1x x1 1z | the FIRST arm (a definite 1 bit) | same |
| v = 0x x0 xx zz 0z xz | merge `1xx0` | same |
| v = 00 | the second arm | same |
| the same `?:` as the RHS of a procedural assignment | identical to the continuous one (merge), unlike the `if` | same |
| nested `c ? a : (d ? b : e)`, c = x | merge of a with the inner value | same |
| `!c ? a : b`, c = x | merge(a, b) (the condition is x) | same |

So with an x/z condition: the `if` statement takes the else arm and the `?:` expression merges. **These are
different rules and the fragment must not be allowed to mix them silently.** (The lowering `Comb2Proc` turns an `if`
into `G ? A : B` with the KNOWN guard `G = (|c) === 1'b1` (`Expr2.ifGuard`), which is what keeps the `if` rule: G is
never x, so the lowered `?:` picks an arm.)

Pinned rows: staged `wpg_tern_x`, `wpg_tern_ctx`.

### 1.3 `!` versus `~`, scalar versus vector, widths

| case | Xcelium (measured) | model |
|---|---|---|
| 1-bit `a`: `!a` and `~a` for a = 0, 1, x, z | 1,0,x,x and 1,0,x,x | same |
| `!` is self-determined, 1 bit, then zero-extended: `n4 = !a`, a = x | `000x`; a = 0: `0001` | same |
| `~` is context-determined: the operand is extended FIRST: `b4 = ~a`, a = 0 / 1 / x | `1111` / `1110` / `111x` | same |
| 2-bit `!v`: v = 00 / 01 10 11 / 1x x1 1z / 0x x0 xx zz 0z xz | 1 / 0 / 0 / x | same |
| 2-bit `~v`: v = 0x / 1x / xx | `1x` / `0x` / `xx` (bitwise, x stays x) | same |
| `!!v`: v = 1x, 0x | 1, x (NOT the identity on x) | same |
| `c ? ~a : 4'b0000`, a = 1, c = 1 / x | `1110` / `xxx0` | same |
| a narrower RHS is zero-extended to the target (`y = a` into 4 bits), `y=4'b1111` else | `000x` for a = x | same |

Consequences for the fragment: `~` and `?:` arms must be exactly as wide as the target (the existing `width_k`
obligation), otherwise the context extension changes the value (`~a` into a wider target is not `~` of the
zero-extension of the result). `!` and reductions have a 1-bit result whatever the operand width.

### 1.4 Structure rules

| rule | semantics (measured / pinned) | what the library does |
|---|---|---|
| blocking order | the last write to a window wins (`y = a; y = b` gives b); a module-level temporary written then read in the same body carries the value just written (`z = (a^b)&c`) | S1: a second write to the window replaces the first (the first's reads are dead and dropped from the site's reads); a READ of a written window is refused in S1, admitted in S3 by SSA substitution |
| block-local temporary `begin logic t; ... end` | same value semantics as a module-level temporary (r2 `p_local`, 27 cycles) | refused today by the loader (`LocalDecl` is not ingested, `docs/sv-refusals.md` line 92); staged as refusal row `wpg_local`; later step |
| no latch | a window not written on some path HOLDS its previous value (x before the first write): r2 `p_partial` shows history dependence; pinned by `latch_comb` | the settle semantics admits it (CombGuard2 admits latches); `lowerComb` refuses it (`selfReadFree`); S1 refuses it at the recognizer: "not assigned on every path (a latch)" |
| self-read | `y = t; t = a;` and `if (c) t = a; y = t; t = b;`: Icarus/Xcelium keep the previous run's value, Verilator/Yosys the settled one (existing rows `rbw_*`) | refused by CombGuard2 at instantiation (`AlwaysComb:self-read`, unchanged) AND by the S1 obligation `noSelfRead` (a read window that overlaps the written window) |
| alias-read | `assign w = t; always_comb y = w; t = a;` (`AlwaysComb:alias-read`, existing) | unchanged loader guard; the Gate 3 fixtures do not trip it (their reads are inputs and bits written by other bodies, none downstream of the body's own writes) |
| cross-process bit chain | body i reads `c[i]` written by body i-1 and writes `c[i+1]`: r3 (both one-body-per-target and multi-target forms) is a correct adder on all 128 known cycles, and wakes through the chain; IEEE 1800-2023 9.2.2.2.1 (longest static prefix: the block is woken by `c[i]`, not by its own `c[i+1]`) | the settle semantics agrees. **Disagreement to report (READ from the source, not run):** the M0 timed tier (`Load.lean`, 7145c5f6) excludes by signal NAME (`readNames \ writeNames`), so there such a body would apparently not be woken by `c[i]`; the symbolic tier (CombGuard2) is bit-granular and equals Xcelium. The timed tier is not on the svGolf path |
| `case` with x/z selector | compared with `===`: never matches a known item, falls to `default` (`mux4_case`, `acg_case_ok`) | S3 |

### 1.5 What the library claims, and what it never does

* The equations of section 3 are Boolean `if c then e1 else e2` and they are **justified only for a known
  condition**: in a settled state with known inputs, `c` is a read of the process like any other read, and
  `CombKnown.reads_known` (`CombKnownThm.lean`, hypotheses `CombDesign`, `Acyclic`, `XFree`, `Covered`, `CombEqs`,
  `StateShape`, `InputsKnown`) says every read bit is `0` or `1`. The lowered right-hand side contains the guard
  `(|c) === 1'b1`, so `Expr2.reads` of the process include the condition's reads; the same theorem therefore covers
  them. In that regime the three rules of 1.1, 1.2 and the `case` rule coincide with the Boolean `if`.
* If the condition may be x: a read of an undriven or out-of-range bit has no source (`cover_k` cannot be
  discharged), an input that is not known is not discharged by `inputsKnown_k`, a latch or a combinational loop has
  no rank. Then `sv_equations` leaves the obligation open and states **no** equation: the "x takes the else branch"
  behaviour is never encoded in the netlist view and never silently relied on. The static `fourstate` stage of the
  checker (undriven nets, latches, x literals, out-of-range reads) is the second line.
* Differential rows (section 6) tie the MODEL (Sem2/Comb2Proc) to Xcelium on the x/z regimes, so the claim "the
  lowered design is the real design" is not just the statement of `Runs2.lowerComb_iff`.

---------------------------------------------------------------------------------------------------------

## 2. The fragment

### 2.1 S1 (Gate 2): exact definition

```
process   ::= always_comb stmt                  module level, or inside a generate-for body (two levels as today)
stmt      ::= begin stmt* end
            | target = rhs ;                    blocking
            | if ( cond ) stmt [ else stmt ]    else-if is an else holding an if
target    ::= any `Acc` the summary already writes: whole signal, x[i], x[i] of a 1-D array, x[i][j], x[i] (row),
              x[hi:lo], x[i][hi:lo]; every index and bound affine in the parameters, localparams and genvars
rhs       ::= the existing right-hand-side fragment (gate tree over & | ^, concatenation of accesses and literals,
              fill '0/'1), every operand exactly as wide as the target
cond      ::= a gate tree (& | ^) of 1-bit accesses and 1-bit literals (width 1)
```
and the five side conditions, each checked and each with a message (the message is the first line of
`sv_structure?`, so the checker's `--tactics` advisory reports it as `in_fragment false`):

| id | condition | how | refusal text (planned) |
|---|---|---|---|
| C1 | all assignments of the body write the SAME window: syntactically equal `Acc` | recognizer | ``site `g_bit#1`: always_comb writes more than one window (`c[i + 1]` and `s[i]`): outside the first fragment; split it into one always_comb per target`` |
| C2 | no latch: the template execution returns a tree on EVERY path | recognizer | ``site `g_bit#1`: always_comb does not assign `c[i + 1]` on every path (a latch)`` |
| C3 | no self-read: no read access of the body overlaps the written window | recognizer (syntactic equality of the window: early error) + obligation `noSelfRead_k` (same signal, other index: `omega`) | ``site `g_bit#1`: always_comb reads the window it writes (`c[i + 1]`)`` / a failing `noSelfRead_k` with the sampled violation |
| C4 | known conditions | `cover_k`, `inputsKnown_k` (the existing obligations; the condition's reads are in the site's reads) | the existing uncovered-read diagnostics |
| C5 | statement kinds | recognizer | ``site `g_bit#1`: always_comb statement `case` (outside the v1 fragment)`` for `case` (WP-G S3a: a plain `case` with a `default` and single-assignment arms is now INSIDE; WP-G S3b: a block of several statements of ONE window, a first tree then `if (c) tree;` overrides without `else`, is INSIDE too; the others name the reason: no `default`, `inside`, an arm that is not one assignment), `unsupported` kinds named; a `for`/`while`/function call does not reach the tactics (the design stage rejects `Unsupported` first, WP-C3); a block-local declaration does not load (LocalDecl) |

Equal-window rule: C1 compares `Acc` values structurally (same constructor, same signal, equal `Aff`s); two
spellings of one window (`y[0]` as a bit and as `y[0:0]`) count as two windows and are refused (conservative).

Allowed shapes (all accepted by S1): `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];`; the same with `else if`;
nested `if` inside either arm; `y = a; if (c) y = b;` (default then override: a one-armed `if` is fine when the
window is already assigned on the path); `y = a; y = b;` (last wins); whole-vector targets (the former 16-bit divider's special-case
table is exactly this shape: one 16-bit target `q`, an `if / else if` chain whose conditions are `||`/`&&` of
1-bit wires (S2) and whose arms are `16'h7E00`, `{s, 15'h7C00}`, `{s, mag}`).

### 2.2 Later steps (each separately logged; none is part of Gate 2 acceptance)

* **S1b, multi-window bodies** (`if (p) c[i+1] = c[i]; else c[i+1] = a[i]; s[i] = p[i]^c[i];` in ONE body): the
  lowering already handles k windows (`SymState.toAssign` is a concatenation target); what changes is the summary
  (a site with extra written windows: `StructOk`, `InRangeObl`, `DisjObl` including within-site disjointness,
  `RankObl'` writers, `Realized` descriptors). Layer L1 below is stated for window lists from the start so S1b adds
  only L2/L3 work. Estimated +2 slot-days. Not needed by the Gate 3 payoff (the carry cell is single-window) nor by
  the former 16-bit divider's table.
* **S2, operators** (DONE 2026-10-31 on branch `wpgs2`, `G23-NOTE.md`; the rows `wpg_not`, `wpg_tern_x`, `wpg_tern_ctx`, `wpg_red`, `wpg_logic` are pinned and XREF-MATCH; the text below is the plan as written at Gate 1): `~` and `!`
  and `?:` and reductions in right-hand sides, and `~ ! | & ^ && || == !=` over 1-bit values and reductions in
  conditions (so `if (a_nan || b_nan || (a_inf && b_inf))` reads). Recognizer plus `Sk` constructors plus lemma cases
  (`rdsOf?_len`, `skT_leaves`, `low_xfWidth`, `low_xfBits`); the knownness theorem is untouched. Width rules of
  1.3 become `WidthObl` cases. `tests/add/attacks/mux_carry.sv` flips to `in_fragment true` here (not at S1).
  Estimated +1.5 slot-days.
* **S3, `case` and SSA temporaries:** `case (x) k: ...; default: ...` with constant items (hit guards
  `===`, already x-free in `xfWidth`), and a read of a window the body wrote earlier on the path, replaced by the
  earlier value (what `Expr2.symSubst` already does at the Expr2 level; at the skeleton level it substitutes a tree
  into a gate tree, which is why S2's `Sk` extension comes first). Block-local `begin logic t; end` additionally needs
  `LocalDecl` ingestion (`Json.lean`/`Ingest2.lean`): out of scope here, listed.
* **Separate gate:** procedural `for` accumulators (recurrence extraction).

### 2.3 Decisions asked for in the brief

* (iii) read-after-write of a bit the same process assigns earlier on the path: **refuse in S1** with a clear
  message; admit in S3 by substitution. The sequential semantics does collapse to a plain equation (that is exactly
  what `symExec`/`symSubst` prove), so this is a staging decision, not a semantic obstacle.
* `~`, `!`, `?:`: **a second step**, as the amendment says. They come cheaply on the knownness side (0 lines) and
  moderately on the recognizer side; their truth tables are pinned (section 1) and their rows are staged.

---------------------------------------------------------------------------------------------------------

## 3. The equations, knownness and names

### 3.1 Shape

For a process whose body writes window `W = (n, lo, w)`, the netlist view gives, for every bit `k < w`,
ONE path-merged equation (`T` is the tree of the body):

```
st.boolAt n (lo + k) = T k
T k = (skRhs e).bit k                                   at a leaf
T k = if (c).bit 0 then T_then k else T_else k          at an if (Bool condition, printed `if b then x else y`)
```
Example (`add_proc`, the carry cell, `eq_c_2`):
`∀ i, i < N → st.boolAt "c" (i + 1) = if st.boolAt "p" i then st.boolAt "c" i else st.boolAt "a" i`
with `known_c_2 : ∀ i, i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)`.
The gate structure of every leaf is kept (principle 10: no reshaping, `^^` left-associated).

Why this is the real semantics of the LOWERED design: `Process2.lowerComb` produces, for the body, the window
`W` with the expression `Expr2.joinIte (ifGuard c) A B` (a ternary under the known guard, or `A` when the two arms
are syntactically equal), the leaves being `resize w` of the fitted right-hand sides (exactly the `eY N` of
`Comb2ProcExample`). Its Boolean bit is `if any(c) then A.bit k else B.bit k` in both cases of `joinIte`
(`Expr2.eq_of_same`), and `XF.any 1 f = f 0`, so the displayed equation is the lowered process's, not a
reconstruction.

### 3.2 Obligations (tags)

Existing tags unchanged: `auto_k`, `inRange_k`, `driverDisjoint_k`, `rankDecreases_k`, `width_k`, `bitRead_k`,
`cover_k`, `inputsKnown_k`. New: `noSelfRead_k` (one per read occurrence of a proc site: its window does not overlap
the written window; `intros; omega`). The width obligation also covers the conditions (width 1). The rank is the
player's, a function of the site identity (`rippleRank`, `lexRank` unchanged): ONE rank per process, shared by all
its windows, which is exactly what `Acyclic` on the lowered design asks (it ranks processes, not windows). For the
Gate 3 design: `rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ pos i => if pos = 0 then 0 else i.toNat + 1)`
(`p[i]` has rank 0, the carry body and the sum cell rank `i + 1`, `cout` rank `N + 1`).

### 3.3 How knownness of `c` is established, and what happens otherwise

See 1.5. In the implementation the condition is not special: its reads are among the site's reads, the cover and
`inputsKnown` obligations quantify over them, and `CombKnown.settled` is applied to the lowered process exactly as
to an assign. The hypothesis `XFree` for the lowered right-hand side needs only static widths: the guard is
`caseEq (reduce or c) (lit 1)` (width 1 on both sides) and both arms are `resize w`, so
`xfWidth (ternary guard A B) = some w` whenever the leaves are width-correct (`WidthObl`).

### 3.4 Names and the ordinal rule

* Generated names for a single-window process: as for assigns, `eq_<signal>_<block>_<position>` and
  `known_<signal>_<block>_<position>`, the position being the process's index in its block (an `always_comb` counts
  as one position, like an `assign`). S1b adds `_<w>` (window index in the body, from 0) only when the body has two
  or more windows.
* Stable alias `eq_<signal>_<k>`, `known_<signal>_<k>`: **k is the ordinal (from 1) of the EQUATION among the
  equations that write that signal, in site order and, inside one body, in order of first assignment.** One
  equation per written window of a body, however many branches assign it. Consequences: an `if / else` that
  assigns `c[i+1]` in both arms is ONE equation (one alias), `y = a; if (c) y = b;` is ONE equation, adding an
  `else if` arm does not renumber anything; two windows of one signal written by one body (S1b) count twice, in
  textual order of first assignment. `stableAliases` (CombEqTactic.lean) needs no change for S1 (it counts
  `lsites` by target name); S1b iterates the windows.
* `add_proc`: `eq_c_1` (`c[0] = cin`, plain#0), `eq_c_2` (the carry body), `eq_p_1`, `eq_s_1`, `eq_cout_1` , i.e.
  the same alias names as `add_n`.

---------------------------------------------------------------------------------------------------------

## 4. Architecture and soundness

### 4.1 Why a lowered view

The settle theory (`CombDesign`, `Acyclic`, `CombEqs`, `CombKnown.settled`, `Models2.of_comb`) is stated for designs
whose processes are all `assign`s (`CombDesign.assign`). `Comb2Proc.lean` (2985 lines, READ) extends it to
`always_comb` by `Design2.lowerComb`: `Runs2.lowerComb_iff`, `Models2.of_combProc_inputs`,
`Terminates2.of_lowerComb_acyclic`, `procFixpoint_iff_combEqs` transfer everything from the lowered design `d'`
(one concat-target assign per body) to `d`, and are unchanged. A tactic for `always_comb` therefore has to prove
facts about `d'`, for a symbolic `N`, from the template. That is the whole new content.

### 4.2 Layers (new files, plain structural Lean)

* **L1, `CombProcStmt.lean` (generic over `Stmt2`, no templates).** For a body of the shape
  `IteTree Ws` (blocks, `if/else`, blocking assignments to constant slices, every path assigning every window of `Ws`,
  windows pairwise equal-or-disjoint as HYPOTHESES) and a design `d` that declares the signals:
  (a) `Stmt2.symExec d [] body = some S` with `S` the windows of `Ws` and `evalPure2`/`xfBits`-semantics of each entry
  equal to the tree's Boolean semantics (shape-agnostic: the `joinIte` collapse on syntactically equal arms is
  covered by `Expr2.eq_of_same`); (b) `S.selfReadFree = true` from "no read overlaps a window"; (c)
  `Stmt2.combAdmits` holds under the same hypothesis (a generic lemma about the path-sensitive `combViol` walk of
  `CombGuard2`, so `combGuardProc` is the identity on the body); (d) `Stmt2.drvWins` of the body lists exactly the
  windows (needed for the one-driver `driversOk` guard that `name.sem` applies). Windows are abstract `(n, lo, w)`
  values, so no symbolic arithmetic enters L1; the equality/disjointness facts are supplied by L3.
* **L2, template side (`CombProc.lean`).** `procSiteOf? ds pos body : Except String TSite`: the template execution
  (`PStmt` to a tree of leaves and 1-bit conditions, with C1 to C5), the skeleton type `PSk` (leaf `Sk` or
  `ite (c : Sk) (t e : PSk)`; a SEPARATE type so `Sk` and its dozen lemmas are not touched in S1), `PSk.bit`,
  `PSk.low`, `PSk.WidthOk`, leaves; and the instantiation lemma: `instStmt2 E elems body` IS an `IteTree` with the
  leaves `fitExpr2 ... v` and conditions `instExpr2 ... none c`, using the existing `instLhs_acc` and `inst_leaf`
  facts.
* **L3, summary integration.** One arm in `siteOf?` (`.alwaysComb body` calls `procSiteOf?`, today it errors with the
  "procedural process" message), a dispatch `rhsBit` in `EqSite` (assign sites unchanged), `site_desc` for the lowered
  process (`Desc names si q'` with `q'` the lowered process, target `.concat [lhs]`), `Realized` for the lowered pair
  list so that `realized_comb` and `realized_acyclic` (both stated against `Realized`, not against `instProcess2`,
  READ) are REUSED on `d'`; a version of `CombEqThm.sound_pairs` that stops before `pairs_desc` (the process-list
  equality `m.processes.toList = (s.pairs ..).map snd`), then `Summary.sound_lowered : ∃ m d', instantiate2 = .ok m ∧
  m.lowerComb = some d' ∧ Realized s σ d'`; the driver-guard removal for the unlowered design (`driversOk` from the
  summary's `DisjObl`, via L1(d)); `eq_of_summary` for `d'`. Two implementation choices, decided at G2.1: hook `siteOf?`
  (a new case in the four consumers `siteOf?_cases`, `site_desc`, `site_sk`, `rhsOf`) with a five-line check in the
  existing front end that turns a proc summary at an old-shaped goal (`CombDesign (X.sem N)`) into the message "this
  design has always_comb processes: state the goal as `∃ d', CombLowered ...`"; or a parallel `summaryP` that copies the
  six short recognizers (`sitesOf?`, `itemOf?`, `itemsOf?`, `famOf?`, `famsOf?`, `summary`) and their spec lemmas and
  leaves every existing definition untouched. The hook is smaller; the parallel route has a smaller blast radius.
* **Tactic front end (`CombProcTactic.lean`).** New goal shape and context shape, registered as additional
  `elab_rules` for the existing `sv_structure` / `sv_interface` / `sv_equations` syntax that call
  `throwUnsupportedSyntax` unless the goal is the lowered one, so the existing elaborators and their outputs are
  untouched. Proposed statements (final shapes decided with the lead at G2.3):
  `theorem add_struct (N) (hN : 1 ≤ N) : ∃ d', CombLowered (design.sem N) d'` where
  `structure CombLowered (m d') : Prop := (lower : m.lowerComb = some d') (comb : CombDesign d') (acyc : Acyclic d')`;
  `sv_interface` takes `hl : CombLowered ..`; `sv_equations` finds `heqs : CombEqs d' st`, `hs : StateShape d' st`
  and the lowering hypothesis in the context.

### 4.3 Theorem inventory

| theorem | status |
|---|---|
| `Comb2Proc.*` (`lowerComb_iff`, `of_combProc*`, `procFixpoint_iff_combEqs`, `symExec_sound`), `CombGuard2*`, `Hier2.driversOk`, `CombKnown.*`, `CombEqs`, `Models2.*`, `CombTask.satisfiedAt_of_comb` | UNCHANGED |
| `CombView.Summary`, `TSite`, `Acc`, `Realized`, `realized_comb`, `acyclic_of_*`, `insts_disj` | UNCHANGED (reused on `d'`), one weakening: `inst_facts` states `a.tgt ≠ .concat ps`; the lowered target is `.concat [leaf]`, so that conjunct becomes "a concat target has exactly one leaf window" (`wins` = `[a.win]`, still pairwise-trivial). Used in `realized_comb`'s `selfDisjoint` |
| `siteOf?`, `siteOf?_cases`, `site_desc`, `siteOf?_proc`, `rhsOf`, `fragOk`, `EqFrag`, `WidthObl`, `EqSite`, `eq_of_summary`'s `hshape` | EXTENDED by a proc case (additive; the assign cases are untouched) |
| NEW: `symExec` IteTree lemma, `selfReadFree` and `combAdmits` from disjointness, `drvWins` lemma, `site_lower`, `lowerComb` of the instantiated list, `driversOk` from `DisjObl`, `eq_of_lowered`, `PSk.low_xfWidth/low_xfBits`, `Sk`-leaf bridge, `CombLowered` | NEW |
| the task reduction `CombTask.satisfiedAt_of_combProc` (the lowered analogue of `satisfiedAt_of_comb`) | NEW; where it lives is open question Q1 |

Axioms: none added. Every new theorem is kernel-checked plain Lean; no `native_decide`/`bv_decide`; the `#print axioms`
pins of the existing library are kept and the new ones are pinned the same way
(`[propext, Classical.choice, Quot.sound]`).

### 4.4 The consumed facts, checked by reading

* `Design2.lowerComb` returns a `.concat [window]` target even for one window (`SymState.target`), so `CombDesign d'`
  works with `Lhs2.windows?` of a one-leaf concat; `CombKnown.settled` takes `Win.placed` windows with offsets.
* `PDesign.instantiateGD2` = `instantiate2` then the driver guard. `driversOk` has an exclusivity clause for
  `always_comb`/`always_ff` (`procExclusiveOk`) and a continuous-vs-procedural clause (`vs.all (!w.overlaps v)`),
  window-level; `assign c[0]` next to `always_comb c[i+1]` is legal and accepted by Xcelium (r3, r4).
* `combGuardProc` is the identity on an admitted body (`combGuardProc_of_admits`); admission of a body that reads
  `c[i]` and writes `c[i+1]` needs the bit arithmetic `i ≠ i + 1` (CombGuard2's own note: "needs the bit arithmetic of
  `BWin.subAll` at the symbolic width"): this is why L1(c) is a generic lemma from the `noSelfRead` fact rather than a
  `simp` evaluation.
* `WP-C3`: `Design2.hasUnsupported` looks inside `always_comb` bodies, so a body with an `Unsupported` statement is
  rejected at the `design` stage; a LOADED but out-of-fragment body (a `case`, a second window) is a tactic error
  (`sv_structure?` message, `in_fragment false`), not an elaboration error.
* `7145c5f6` (timed always_comb sensitivity): see the cross-process row of 1.4.

### 4.5 Byte-identity discipline (the WP-F method)

Gate 2 acceptance (a) is checked as WP-F did: goal dumps (the `sv_structure` and `sv_equations` obligations with
full contexts) of `add_n`, `mul_n`, `mul_tree`, `mul_tree_h`, `mul_wallace` before and after, compared byte for byte;
the `Examples/system-verilog` comb proofs rebuilt; `tools/gen_sv_refusals.py --check`. For S1 the outputs of designs
without `always_comb` are expected byte-identical (new code is reached only through an `alwaysComb` site or the new
goal shape). At S2 the TEXT of the refusal rows for `?:` and unary operators changes by design (`mux_carry`,
PROVING.md section 4 rows), and nothing else.

---------------------------------------------------------------------------------------------------------

## 5. Stage register (parser, semantics, lowering, differential, proof, register)

| construct | extractor | symbolic semantics | proof representation | differential vs Xcelium | Examples proof | register |
|---|---|---|---|---|---|---|
| `always_comb`, blocking, `if/else` | yes (28 probe modules, 0 Unsupported) | yes (`lowerComb`; `fa_comb_proc`, `acg_cond_ok`, `acg_nested_ok` pinned) | **no (S1)** | existing rows XREF-MATCH; staged `wpg_if_x`, `wpg_if_chain`, `wpg_carry` | no | `tl-sv-structure-fragment` trigger text to change |
| multi-window body | yes | yes (`fa_comb_proc`, `addsub_comb`) | no (S1b) | staged `wpg_carry`, `wpg_if_chain` | no | |
| `case`, constant items | yes | yes (`mux4_case`, `acg_case_ok`) | no (S3) | existing rows | no | |
| `?:` | yes | yes | **yes (S2, `G23-NOTE.md`)**; knownness: **yes** | pinned `wpg_tern_x`, `wpg_tern_ctx` (Xcelium, XREF-MATCH) | `comb_ops` | `mux_carry` advisory flipped |
| `!`, `~` | yes | yes | **yes (S2)**; knownness: **yes** | pinned `wpg_not` | `comb_ops` | |
| reductions, `&& \|\|`, `== !=` (equal widths) | yes | yes | **yes (S2, S2d)**; knownness: **yes** | pinned `wpg_red`, `wpg_logic` | `comb_ops` | |
| temporaries read after write | yes | yes (SSA in `symSubst`) | no (S3) | staged `wpg_order` | no | |
| block-local declaration | yes (`LocalDecl`) | **no** (ingestion refuses) | no | `wpg_local` (refusal row, Xcelium trace quoted) | no | line 92 of sv-refusals.md |
| procedural `for` | **no** (Unsupported) | no | no | | | `LOOPS` |

A construct counts as SUPPORTED only when every column is filled; this package targets the first row at Gate 2, the
`?:`/`!`/`~` rows at S2.

---------------------------------------------------------------------------------------------------------

## 6. Differential rows (staged in `rows/`, Xcelium-validated against the rules, Lean side at Gate 2)

`rows/cases_wpg.json` (9 rows, 204 cycles), one directory per row with the `.sv` and its envelope. Gate 2 copies the
directories to `Examples/system-verilog/sem2/`, appends the cases to `harness/sv/cases2.json`, and pins them with
`xcelium_batch.py prepare/run --case ...` (the prepare phase runs the Lean model: slot). Expected status: all
`XREF-MATCH`; any `XREF-DIFF` is a model bug to report, never a whitelist.

| row | what it pins | cycles |
|---|---|---|
| `wpg_if_x` | `if` with 1-bit and 2-bit conditions at 0/1/x/z, `if (!c)` versus the swapped twin, `if (~c)` | 21 |
| `wpg_if_chain` | else-if chain, nested if, default-then-override, taken/untaken x/z, two targets | 21 |
| `wpg_tern_x` | `?:` scalar, vector, 2-bit condition, nested, as a procedural RHS | 49 |
| `wpg_not` | `!` versus `~` at 1 and 2 bits, in 4-bit contexts, `!!v`, `!(~v)` | 17 |
| `wpg_tern_ctx` | `c ? ~a : 4'b0000` (context-determined `~`) | 12 |
| `wpg_order` | last write wins, temporary written then read | 27 |
| `wpg_carry` | the carry-select cell, multi-target and single-target twin (z passes through the taken arm) | 32 |
| `wpg_partial` | the per-bit latch (history), `lowerComb` refuses it | 7 |
| `wpg_local` | REFUSAL row: block-local declaration (Xcelium trace in `measured`) | 18 |

Already pinned and used as the contract's anchors: `fa_comb_proc`, `acg_cond_ok`, `acg_nested_ok`, `acg_case_ok`,
`mux4_case`, `latch_comb`, `addsub_comb`, `acg_xproc_bits`, the `rbw_*` refusal rows, the `acg_alias_*` rows.

Gate 2/3 fixtures (staged in `fixtures/`, functionally verified on Xcelium: N = 4 exhaustive, N = 16 3000 random +
corners, bad = 0): `add_proc.sv` (the carry cell is an `always_comb` if/else, single window, S1), `add_proc_m.sv` (the
whole cell, carry and sum, in one body: S1b), and negatives `neg_latch`, `neg_selfread`, `neg_condx`, `neg_case`,
`neg_multi`, `neg_dyn` (all extract with zero Unsupported nodes; expected tactic messages in section 2.1).

---------------------------------------------------------------------------------------------------------

## 7. Plan, estimates, go/no-go

| step | content | est. slot-days |
|---|---|---|
| G2.0 spike | plain-Lean scratch file against the BUILT library (no shared-tree edit): prove L1 for the one-window `if/else` IteTree at a symbolic window, and `lowerComb` of the instantiated carry body by the generic lemma. GO if it closes in about 150 lines without whnf storms; NO-GO falls back to a per-design `simp` mirror (the `as_symExec` recipe) plus a smaller generic lemma | 0.5 |
| G2.1 | L1 + L2 (`CombProcStmt.lean`, `CombProc.lean`), unit `#guard`s on the carry body | 1 to 1.5 |
| G2.2 | L3: `site_desc`/`Realized` for the lowered list, driver guard, `eq_of_lowered`, `CombLowered`, the reduction lemma | 1.5 to 2 |
| G2.3 | tactic front end, messages, `Examples/system-verilog/comb_proc` (view, hint, errors, known, proof, neg), pins | 1 |
| G2.4 | byte-identity regression (goal dumps), library chain and Examples rebuild, `gen_sv_refusals --check`, rows pinned, advisory test updates | 0.5 to 1 (+ the 75-minute suite runs) |
| G3 | `add_proc.{sv,lean}` (the arithmetic is `add_final` plus an 8-case Bool identity `(if p then c else a) = (a&b)|(c&(a^b))` with `p = a^b`), `task.json`, `expected.json` scores, VALIDATION entry, README/PROVING paragraph | 0.5 to 1 |
| S2 (after G3) | `~ ! ?:`, reductions, logical ops; rows; `mux_carry` flips | 1.5 |
| S1b / S3 | multi-window; `case`, temporaries | 2 / 3 |

The proof file of `add_proc` is estimated at about `add_n`'s 84 lines plus 10; the elaboration time at 1.0 to 1.5 times
`add_n`'s (one more site per bit, one more condition read); the `Solution.olean` size similar. Time limits unchanged
unless it is slower than the slowest existing `add` reference by a lot (README rule).

The lead's decision points: after G2.0 (go/no-go on the architecture), after G2.2 (is the soundness chain closed), and
the S1b-before-S2 or S2-before-S1b ordering after G3.

---------------------------------------------------------------------------------------------------------

## 8. Risks and open questions

Risks, in order of weight:

1. **Size.** Gate 2 is a multi-day package, not one day; the schedule slips unless something else is dropped.
2. **The mirror at a symbolic index** (L1/L2) is the one place the elaborator could fight back (window comparisons
   `("c", (i+1).toNat, 1)` against `("c", i.toNat, 1)`; `simp` on `Win.overlaps`). Mitigation: L1 never compares symbolic
   windows (they are hypotheses), and G2.0 measures this before anything else.
3. **`name.sem` is the guarded family:** removing the driver guard for a design with `always_comb` needs `driversOk`
   from the summary (`Stmt2.drvWins` lemma), a piece the assign-only chain gets from `CombDesign` for free.
4. **`inst_facts`/`Desc` target form** (`.concat [leaf]` for proc sites): a small weakening of an existing theorem used
   by `realized_comb`. Done additively (a second lemma) if the weakening causes churn.
5. **Goal-shape change for the player:** `∃ d', CombLowered ...` instead of `CombDesign ∧ Acyclic`; documented in
   PROVING.md section 4; existing proofs unaffected (new `elab_rules`, existing ones untouched).
6. **Regression cost.** Any edit to `CombView*/CombEq*` rebuilds the chain and the 191-test suite takes about 75
   minutes (WP-F): plan two full runs (after G2.2, final).
7. **Differential pins need the Lean `prepare` phase** (the model's port list and trace), so they cannot be finished
   before the slot is free; staged data and the Xcelium side are ready.

Decisions of the lead on the four questions (2026-10-30, after the note was committed as ab13a278):

* **Q1, the lowered task reduction (`CombTask.satisfiedAt_of_combProc`):** a ten-line LOCAL lemma inside the `add_proc`
  reference file. Not in CombLib (and not in `SvGolf/Comb.lean`) until the reference proof works; promotion comes after.
* **Q2, the M0 timed-tier sensitivity list:** recorded in section 9; I do not touch that tier. The lead passes it to
  The maintainers and the off-prem agent.
* **Q3, scope:** S1 is single-window only. S1b (multi-window), S2 (`~ ! ?:`, reductions, logical operators) and S3 (`case`,
  temporaries) are STRETCH, not part of the Gate 2/3 acceptance. (Sections 2.2 and 7 list them with estimates; read
  "S2 (after G3)" as "stretch".)
* **Q4, doc edits:** allowed: the `tl-sv-structure-fragment` `trigger` text in `docs/sv-refusals.json`, the `mux_carry`
  expectation in `svgolf/tests/expected.json` (only when S2 lands), and the PROVING.md section 4 rows. Every edit is listed
  in the report; docs are regenerated with `python3 tools/gen_sv_refusals.py --write` and verified with `--check`;
  the register's attack names are not touched.

Order of work: no Lean until the lead releases the slot (after the Q0 agent's `~^` report); meanwhile the staged rows
are runnable (`rows/run.sh`, `rows/install_gate2.py`) and the spike plan is `G20-SPIKE.md`.

---------------------------------------------------------------------------------------------------------

## 9. Recorded for others: the M0 timed tier's sensitivity list is name-granular

Not part of this package and not touched by it; recorded here so that the maintainers and the off-prem agent have the facts.

* **Where.** `LeanModels/Sv/Load.lean`, `timedProcOf`, the `.alwaysComb body` case added by `7145c5f6` ("admit always_comb
  sensitivity"): `writes := SStmt.writeNames body` and `reads := (SStmt.readNames body).eraseDups.filter (fun name =>
  !writes.contains name)`; the process is woken (`combReads`) only by a change of a signal in `reads`. Both lists are
  SIGNAL NAMES (`List String`).
* **What the LRM says.** IEEE 1800-2023 9.2.2.2.1 puts into the implicit sensitivity list every longest static prefix the
  block reads, except an expression that is also written within the block. So `always_comb begin if (p) c[1] = c[0];
  else c[1] = a; end` IS woken by `c[0]` (the written prefix is `c[1]`, the read prefix `c[0]`), even though both are
  bits of the signal `c`.
* **The disagreement (READ from the source, NOT run).** Because the timed tier excludes by name, `c` is dropped from
  `combReads` and, as read, the block would not be woken when another process changes `c[0]`: the output `c[1]` would
  stay stale. The symbolic tier (`CombGuard2`, bit-granular `BWin`) and Xcelium 24.03 wake it (measured in this package:
  `probe/probe3.sv`, a 3-bit carry chain of `always_comb` blocks over bits of one vector `c`, 128 known cycles correct,
  `probe/xrun3.out`; the same chain is the shape of the Gate 3 `add_proc`). The known Icarus departure
  (`iverilog-comb-bit-split-sensitivity`, whole-vector reads only) is a different bug on the same theme.
* **Scope.** Only designs run through the M0 timed tier (`elabTimedDesign`, single module, initial-only legacy path). It is
  not on the svGolf path (the checker's tier is the symbolic one), so no svGolf result depends on it.
* **A fix, for whoever owns the tier (not applied).** Either make the exclusion window-granular (compare read and write
  windows instead of names), or drop the exclusion and wake on ANY change of a read signal: an `always_comb` body admitted
  by the self-read guard is idempotent on its own output (`runCombProcess2_alwaysComb_idem_of_admits`), so an extra
  self-wake re-runs the block once and changes nothing. The first is exact, the second is simpler and sound for admitted
  bodies.
