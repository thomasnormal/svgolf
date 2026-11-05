# WP-I: module instances in the `sv_comb` tactics (design note)

Status: DESIGN, 2026-10-31, branch `wpi` (from `svgolf-prep` ac484007). Documents only: nothing in `LeanModels/`, `extractors/`,
`harness/`, the checker, the tests or the tasks was edited, and no Lean, `lake` or Xcelium process was started. What did run, all
outside Lean: the pinned ls-sv extractor (`python3.12`, pyslang 11.0.0), the svGolf scorer (`score/score.py`, Yosys 0.53) and one
Yosys SAT equivalence; `probe/run.sh` reproduces them (appendix A). Labels as in `design/word-level/B2-NOTE.md`: READ (a source,
`file:line`; paths are under `LeanModels/Sv/` unless they start with `svgolf/`, `docs/` or `Examples/`; lines are those of
ac484007), MEASURED (I ran it), PLANNED (a proposal), UNVERIFIED (cannot be settled without Lean; each is an item of the spike,
step I1, and is listed in appendix B). Names marked NEW do not exist in the tree. Estimates are mine, not measurements.

## 0. Summary

1. **Hierarchy works everywhere except in the tactics.** The extractor emits instances; `load_design_sv2` defines `X.plib` and, for a
   hierarchical top, `X.sem := PDesign.instantiateHD2 X.pdesign X.plib args` (`Ingest2.lean:1098-1105`); `Hier2` flattens at any
   parameter point with a one-driver rule per level; the scorer flattens in its first stage; and the flattened process list of a
   ripple adder of `full_adder` cells is proved by hand for every `N` (`Examples/system-verilog/ripple_fa/gen.lean`, 477 lines).
   The tactics refuse on their first line: three copies of `findGD2` (six call sites) look for the head `PDesign.instantiateGD2`, and
   the family of a hierarchical top has the head `instantiateHD2` (section 1). The message does not mention instances (`svgolf/PROVING.md:545`).
2. **The gap is one recognizer and one soundness theorem, not a new semantics.** `CombDesign`, `Acyclic`, `CombEqs`, the knownness
   theorem `CombKnown.settled` and `CombTask.satisfiedAt_of_comb` are statements about a `Design2`, and `X.sem N` of a hierarchical
   envelope already IS a flat `Design2`. Missing: a summary of the template with instances, a twin of `Summary.sound`
   (`CombViewSound.lean:801`) against `instantiateH`, and the facts about the flattening's hoisted names (K1 to K7, section 2.1).
   No theorem mentions `Expr2.rename` or `Process2.rename`, and nothing uses them outside `Hier2.lean` (MEASURED by grep).
3. **Recommendation: route C, a mixed route.** The parent's summary sees an instance as a black-box site (reads its input actuals,
   writes its output targets); the child is summarized by the same recognizer, separately, at the override point; ONE generic
   hierarchy theorem, proved once in the library, composes them into `CombDesign`/`Acyclic`/knownness of `X.sem N`; equations come
   out in the parent's own signal names when every actual is a window. Option A (one flat summary with hoisted-name templates)
   costs more for the same unavoidable core and cannot do recursion; option B (player-composed contracts) leaves the composition to
   the contestant (section 2).
4. **Honest value.** Hierarchy is not a score lever: the scorer flattens, and the hierarchical `ripple_fa` scores exactly like
   `add_n` at `N = 16` (112 GE, depth 33), while a hierarchical array multiplier moves the score by under one GE either way
   (section 1.4, MEASURED). What hierarchy buys is readability, proof modularity (prove a stage once, use it `N` times) and the only
   route to recursion. It should be started by a task that needs it, not before.
5. **Cost.** Step I0 (a truthful message) is 0.5 agent-day. The cheapest tactic milestone is the ripple adder written with a
   `full_adder` module and proved for all `N`: 14 to 20 agent-days (11 to 14 slot-days) when the tactic returns hoisted-name
   equations, 16 to 23 (13 to 15) when it returns the parent-name equations of `add_n` so that the `add_n` proof script runs
   unchanged. It sits behind a 1 to 1.5 day spike that can say no; its by-hand half (the library facts, no tactic) is 7.5 to 10.5.
6. **Not covered by that milestone:** parametric children, expression actuals in the inlined equations, recursion (F3b),
   `always_comb` or clocked children, instance arrays, generate-local declarations, unconnected inputs (section 4).
7. **Decisions for the maintainers:** section 6. The one that matters first: whether to start before WP-B2 and S1b land, because all three
   edit `TSite`/`Summary`.

## 1. What the tactics see today (a)

### 1.1 The chain, stage by stage

| stage | where | what an instance does there |
|---|---|---|
| 1 extractor | `extractors/sv/extract.py` (`convert_instance_sym`, `_sym_port_conn`); `docs/sv-envelope-schema.md:1773-1790` | ONE `Instance` node (definition, generate path, parameter overrides) and ONE `PortConn` per child port; the definitions of all transitive children follow the top in `design.modules`. Positional, `.name`, `.*` and named connections arrive in the same canonical form (MEASURED, `probe/conn_forms.sv`: `u1` to `u3` give identical five-entry `ports`). An instance array stays `InstanceArraySymbol:InstanceArray` (MEASURED; register `hi-instance-array`). |
| 2 ingestion | `Ingest2.lean:935-947` (every library module is cross-checked like a top), `:1080-1123` | defines `X.plib`; `X.sem` is `instantiateHD2 X.pdesign X.plib` unless `flatTop := lib.isEmpty \|\| GenItem.listInstFree pd.generates` (`:1098-1105`). An instance-free top keeps `instantiateGD2` even if the file holds other modules. A generate-local `Var`/`Net` item is turned into a loud `GenerateDecl:<kind>` (`:511-515`). |
| 3 semantic flattening | `Hier2.lean` (section 1.2) | flattens; refuses by loud `Process2.unsupported` nodes in `X.sem N`. |
| **4 tactic front end (the refusal)** | `CombViewTactic.lean:67-77` `findGD2`, called at `:270` (`sv_structure`, `sv_structure?`) and `:524` (`sv_interface`); copies `CombProcTactic.lean:285-293` (called at `:351`, `:529`, `:651`) and `CombEqTactic.lean:81-90` (called at `:299`) | `findGD2` unfolds `X.sem N` for at most 8 steps looking for `PDesign.instantiateGD2` with two arguments; `instantiateHD2` has three, a different head, so the lookup returns `none` and every site throws `cannot read a load_design_sv2 family (X.sem N) off the design in the goal` (`CombViewTactic.lean:271`, `CombEqTactic.lean:300`). `svgolf/PROVING.md:545` records this as how an instance is refused ("the message does not say so"); `svgolf/PLAN.md:512` asks for a better message. READ for the cause; I did not run the tactic. |
| 5 recognizer | `CombView.lean:861-872` `famOf?` (module-level instance: `module instance (outside the v1 fragment)`, `:870`), `itemOf?` (`:848`, instance in a loop body), `procsOf?` and `itemOf?` (`:778-799`, `:842`, instance in an inner loop); the `always_comb` twin `CombProcSummary.lean:95, 117` | would refuse in the right words, but is unreachable from a hierarchical top because of stage 4. It is reached only through a hand-written goal over `instantiateGD2 X.pdesign`, and there the flat expansion already turns the instance into a loud `Instance` process (`Param2.lean:1296-1297`). |
| 6 checker | `svgolf/check.py:1074-1135` (`--tactics`) | advisory `in_fragment: false` with the stage-4 text; nothing else in `check.py` or the scorer minds a hierarchy (`score/canon.ys:28` `flatten -noscopeinfo`; `svgolf/README.md:1112`). No test in `svgolf/` has a hierarchical submission: only two multi-module `.sv` files exist there, an Xcelium testbench probe (`design/always-comb/probe/probe3.sv`) and a source-gate fixture (`score/tests/gate/host_dead_code.sv`), neither a submission (MEASURED by grep). UNVERIFIED: the checker's `design` and `solution` stages on one. |

### 1.2 What the semantic tier does with an instance (`Hier2.lean`)

* Names: the child's declarations are hoisted as `<path><inst>.<signal>` with port flags cleared (`Decl.hoist :303`,
  `PInst.pathPrefix :310`, e.g. `g_bit[3].fa.s`); every child process is renamed the same way (`Process2.rename :288`).
* Connections are continuous assigns (`connProcs :424`): an input becomes `pfx.port = fitExpr2 actual` when `portInOk` (`:391`),
  else the loud `PortConn:context-width` (`:447-454`); a bare net actual narrower than a net port is `PortConn:net-width`
  (`:442-443`); an unconnected input NET reads `z` (`:456`), an unconnected input variable nothing; an output becomes
  `target = portOut` or the loud `PortConn:target` (`:457-466`); `PortConn:missing`, `:direction` and `:port` (`strayConn :483`)
  complete the list. Overrides: `PInst.given :343` evaluates an INT-class expression in the parent's scope; an untyped child
  parameter with a non-INT override is refused (`:352-353`).
* Guards: `childInstOf :930` returns `(c'.driverGuard cd).clockGuard clocks i`, the top gets `topGuard :974`; a violated one-driver
  rule appends a loud `PortConn:driver`; a clocked child must be clocked through bare input-port connections (`:544-557`).
* Depth: `instantiateRec :950` recurses structurally on a depth that `instantiateHFrom :979-982` fixes to `lib.length + 1`; depth 0
  returns `instance hierarchy deeper than its module library` (`:952-953`).
* Every loud node ends up as a non-`assign` process of `X.sem N`, which the field `CombDesign.assign` (`Comb2Base.lean:807`)
  cannot hold. So the semantic refusals are inherited by any tactic for free, and never silently chosen (principle
  `P-NO-SILENT-PICK`).

### 1.3 What a contestant can do today

Flatten the design in the source (the score is the same), or prove by hand. `ripple_fa/gen.lean` shows the price of the second:
477 lines only for the flattened process list, the declarations and the one-driver rule at symbolic `N`
(`ripple_fa_processes :421`, `ripple_fa_driversOk :387`, `ripple_fa_instantiateH :400`); `CombDesign`, `Acyclic` and the equations
are not in it, and `add_n_byhand.lean` (509 code lines for the flat adder, `PROVING.md` section 5) is the size of those.

### 1.4 What hierarchy costs and buys at the score (MEASURED)

| design | area (milli-GE) | depth | gates |
|---|---|---|---|
| `Examples/system-verilog/ripple_fa/ripple_fa.sv`, N = 16 | 112000 | 33 | 80 |
| `tasks/add/reference/add_n.sv`, N = 16 | 112000 | 33 | 80 |
| `probe/mul_h.sv` (row adders `rca #(.W(N))` of `full_adder`), N = 4 / 8 | 90993 / 448642 | 16 / 40 | 64 / 320 |
| `tasks/mul/reference/mul_n.sv`, N = 4 / 8 | 91326 / 447976 | 16 / 40 | 64 / 320 |

`mul_h` equals `mul_n` at N = 6 (Yosys `miter` and `sat -verify`, silent). So module boundaries vanish in stage 1, but a
restructured source is a different statement order, which moves ABC's choices by under 1 GE (the ruling 1 of 10/31 already
accepts such movement, `PLAN2.md:124`). Hierarchy is a source-level and a proof-level device, never a score one.

## 2. The options (b)

### 2.1 The core every option needs: hoisted-name facts about `flattenInst`

The flat design is `parent decls ++ hoisted` and `parent static processes ++ gens ++ others`, where each instance contributes
`strayConn ++ ports.flatMap connProcs ++ child.processes.map instBodyProc` (`flattenInst :569-576`, `instantiateRec :960-969`).
Whatever route is taken, a proof of `CombDesign`, `Acyclic` and knownness of that list needs these facts, none of which is a
theorem today:

| id | fact | status |
|---|---|---|
| K1 | shape: every flat process is an `assign` with static windows; a renamed child target is the child's window under the hoisted name; `declWidth (pfx ++ n)` is the child's width | NEW (lookup by name in `parent ++ hoisted`) |
| K2 | names: hoisted names are pairwise distinct and differ from the parent's (`CombDesign.nodup`, `Comb2Base.lean:803`); two prefixes `label[v].inst.` with different `v` are not prefixes of each other, which needs `toString` injective on `Int` and `]` not a digit | NEW; UNVERIFIED which core lemmas exist (grep: none in `LeanModels/Sv`). `ripple_fa/gen.lean:327` dodges it by length because the driver rule only compares the parent's names. |
| K3 | one driver: `disjoint`, `selfDisjoint`, `notInput` across parent windows, connection windows and renamed child windows (the child's `notInput` makes the input connection the only writer of a port) | NEW; the converse (`CombDesign` gives `driversOk`) is built: `driversOk_of_combDesign`, `Hier2Gen.lean:632` |
| K4 | rank: the lexicographic key (parent-site rank, phase in / child / out, child rank) as a `Nat` by `countRank` | NEW but small; the mechanism exists (`CombViewArith.lean:231-240`, used by `acyclic_of_lex`, `CombViewMain.lean:648`) |
| K5 | state view: a `childView st pfx : SvState` with `CombEqs flat st` giving `CombEqs child (childView st pfx)`, and the `StateShape` transfer; needs `evalPure2 st (e.rename f) = evalPure2 st' e` for the renamed state `st'` (`evalPure2` is fuel-free and structural, `Pure2.lean:136-199`, one case per constructor) | NEW |
| K6 | knownness: `XFree`, `Covered`, `InputsKnown` of the flat design from the parent's and the child's. An unconnected input is a `z` literal assign (`Hier2.lean:456`), and x/z literals are outside the XF fragment (register `tl-xfree`), so the recognizer must refuse it | NEW |
| K7 | guards: the child's `driversOk` from its `CombDesign` (K3 converse), `clockGuard` is the identity on a clockless child (`clockGuardProc :544-548`, `clock? = none`), `topGuard` from `instantiateH_of_rec` (`Hier2Gen.lean:360`) | built, to be assembled; `ripple_fa_instantiateH` (`gen.lean:400`) is the worked instance |

Already built and reused: `instantiateRec_of_ok :207`, `expandListH_cons_ok :87`, `instExpandH_of :166`, `instantiateRec_flat :227`
(a flat child's recursive instantiation IS `instantiate2From`), `GenItem.expandH_genFor_ascending_flatMap :145`,
`instantiateHD2_of_ok :378` (all `Hier2Gen.lean`).

### 2.2 Option A: one flat summary (the brief's option 1)

*Idea.* `PDesign.summary` learns `.inst`: one site per input connection (target: the hoisted port, reads: the actual), one per
output connection (target: the parent's window, read: the hoisted port), and the child's sites renamed under the prefix, with the
child's affine forms composed with the override (`Aff.subst`). Ports become hoisted signals (or aliases of the actual, variant A':
the summary reads `a[i]` where the real process reads `g_bit[i].fa.a`; the real design still has the hoisted signal, so `Desc`
(`CombViewThm.lean:921`) would need a "reads through the connection" form and K1 to K3 are needed all the same).

*Why it costs most.* A hoisted signal inside a loop is a FAMILY of one-bit declarations named `"g_bit[" ++ toString i ++ "].fa.a"`.
`Acc.name : String` (`CombView.lean:365`), `DeclT.name` and `Win` are keyed by static strings, so A needs name templates (base plus
genvar-dependent index) in every one of them, then through all of `CombViewThm/Sound/Main` and `CombEq*`. Its
obligations would contain string-valued windows that `sv_norm_core` cannot decide (its simp set has `String.reduceEq` for literals
only, `CombViewTactic.lean:134, 141`). The two-level loop cap (`CombView.lean:842`) is hit as soon as a looped instance has a looped
child. K1 to K7 are needed in full.

*Recursion.* Impossible: a finite template cannot summarize a recursive family.

### 2.3 Option B: modular contracts, composed by the player (the brief's option 2)

*Idea.* The player proves, per module, a contract about the child's own `Design2` with the existing tactics (the child as a top),
and a library hierarchy theorem turns the children's contracts plus the connection facts into the parent's settled-state lemma.

*What is wrong with it alone.* The goal `CombDesign (X.sem N)` is about the flat design, so the structure still needs K1 to K7;
contracts only help the equations. The contestant then writes the per-instance reasoning (a family quantifier over instances, the
view transfer, the connection rewriting) by hand, hundreds of lines. Reusable only as a layer under C. Knownness cannot be
avoided either: a child's inputs are known only because the parent's actuals are, which is `CombKnown.reads_known` on the FLAT design
(`CombKnownThm.lean:280`).

### 2.4 Option C: black-box instance sites and one generic hierarchy theorem (recommended)

*Recognizer (NEW `PDesign.summaryH d lib`).* The parent as today, plus an instance item: `{name, module, path, overrides, child :=
the same recognizer on the library module at the override point, conns}`. A connection is `in (port, reads | literal)` or
`out (port, target window)`. The instance is ONE site that writes one window per connected output and reads the windows of its
input actuals. The width contract per connection is the existing one (operand exactly as wide as its target,
`Sk.WidthOk`, `CombEqBase.lean:284`; a violated one is the `width_k` goal). Overrides are carried as evaluated argument lists for the
child's family, so `Aff.subst` is never needed; the language of overrides is the localparam one (`CE`, `CombView.lean:900-975`:
`+ - *` by a literal, `/ %` by a positive literal), because then the parent's width obligations stay `omega`-linear. A site with
several written windows is exactly what S1b needs (`design/always-comb/README.md:200-203`: `StructOk`, `InRangeObl`, `DisjObl`
within the site, `RankObl'` writers, `Realized`): build it once.

*Theorems (NEW, twins of the flat ones; the existing ones are not edited).* `Summary.soundH` (`instantiateH` succeeds and the result
realizes the extended summary), `comb_view_H`, `acyclic_view_H`, `comb_acyclic_view_H` concluding about `d.instantiateHD2 lib args`
via `instantiateHD2_of_ok :378`, `instantiateH_of_rec :360` and `driversOk_of_combDesign :632` (the recipe documented at
`Hier2Gen.lean:37-60`), `decls_view_H` (for `sv_interface`: hoisted declarations carry no port flag, `Hier2.lean:303-304`), and
`eq_view_H`. The child's profile enters as premises: `CombDesign` and `Acyclic` of the child's `Design2` at the override point.
For a closed child (no free variable) the existing `tryClosePlain` path (`CombViewTactic.lean:239-252`) decides them natively;
for a parametric child they are found in the local context by type, as `sv_equations` finds `CombDesign` and `Acyclic`
(`CombEqTactic.lean:278-291`).

*Rank.* The instance is a single rank step: `kappa(instance)` from the player's rank over site ids, expanded by K4 to
(`kappa`, phase, child rank). Conservative: two instances coupled through each other's ports are refused even if neither child has an
input-to-output path.

*Equations.* Step M-lite: the tactic returns the child's equations in the child's frame (`eq_<inst>_<signal>_<k>` over hoisted
names, via K5 and the child's own `eq_view`) and the connection equations, e.g. `st.boolAt "s" i = st.boolAt (pfx i ++ "s") 0`.
Step M-inline: when every actual of the instance is a window of a declared signal or a literal, the child's skeleton (`Sk`,
`CombEqBase.lean:69`) is composed with the connection windows and the tactic returns the equations in the PARENT's names, the same
statements the flat design gives. A non-window actual (an expression) falls back to M-lite for that instance.

*Naming.* Stable aliases keep their rule (`stableAliases`, `CombEqTactic.lean:251`: target signal plus the ordinal among the writers
in site order); an instance counts as one writer of each parent signal its outputs target, in position and child-port order. For
`add_fa` that gives `eq_c_1` (`c[0] = cin`), `eq_c_2` (the instance's carry), `eq_s_1`, `eq_cout_1`, the four names of
`add_n.lean`. The generated long names keep the scheme `eq_<signal>_<block>_<pos>` for the connection (`eq_s_g_bit_0`); a child-internal signal gets
`eq_<block>_<inst>_<signal>_<pos>` (PLANNED, e.g. `eq_g_bit_fa_s_0`); the `known_...` twins follow.

*What the contestant writes (milestone).*
```systemverilog
module full_adder (input logic a, b, cin, output logic s, cout);
  assign s = a ^ b ^ cin;  assign cout = (a & b) | (cin & (a ^ b));
endmodule
module add_fa #(parameter int N = 16) (input logic [N-1:0] a, b, input logic cin, output logic [N-1:0] s, output logic cout);
  logic [N:0] c;  assign c[0] = cin;
  for (genvar i = 0; i < N; i++) begin : g_bit
    full_adder fa (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
  end
  assign cout = c[N];
endmodule
```
and the proof file of `add_n.lean` (`add_struct` with `rippleRank`, `add_interface`, `add_final`, `solution`) unchanged: the rank is
over the parent's site ids (plain 0, the instance family, plain cout), the equations are the four above.

*Soundness story.* (i) The trusted object does not change: `X.sem N = instantiateHD2` is the semantic tier, pinned by the
differential rows (`hier_*`, `ripple_fa*`, `docs/sv-envelope-schema.md:2041-2047`). (ii) The new theorems are about that object;
there is no second semantics and no fourth design representation (principle 6 of `docs/sv-comb-design.md`: a derived summary with a
soundness theorem against the real instantiation). (iii) The child's facts are theorems about the child's own `Design2`, obtained
by the unchanged tactics; the hierarchy theorem (K1 to K7) transports them, so nothing about a child is trusted. (iv) The recognizer
may be wrong in the safe direction only: the admission of each connection is a closed decidable `connOk` taken as a hypothesis of
`soundH`, so a recognizer that admitted what `connProcs` rejects fails a `decide`, it does not prove a false statement. (v) Inlining
is logic: rewriting hoisted equations by connection equations. (vi) The additive discipline of G2.2 applies: the hierarchical
elaborators `throwUnsupportedSyntax` on every existing goal shape (`CombProcTactic.lean:10`), so the goal dumps of all existing
references stay byte-identical.

*Variant C' (not costed): wire elimination.* A refinement theorem that deletes single-driver port wires by expression substitution
(the `Expr2.symSubst` of the `always_comb` lowering, `Comb2Proc.lean`) would make `X.sem N` equivalent to a hoisting-free design; it
re-pays the width side conditions of substitution and still needs K5 to transfer `Goal`.

### 2.5 Comparison

| | A: flat summary | B: player-composed contracts | C: black-box sites + hierarchy theorem |
|---|---|---|---|
| contestant writes | the `add_n` proof | child contract, composition by hand | the `add_n` proof (parametric child: plus a child lemma) |
| tactics print | hoisted names `eq_g_bit_fa_s_1`, connection assigns in the ordinals | none for the parent | parent-name aliases (M-inline), hoisted names only for M-lite and for non-window actuals |
| new trust | none | none | none (section 2.4, soundness story) |
| where K1 to K7 live | inside the summary pipeline | in the library | in the library, once |
| retarget surface | edits `Acc`/`DeclT`/`Win` and every theorem over them; 87 uses of `instantiateGD2` in 8 files (MEASURED by grep) | none | none: twins, as G2.2 |
| parametric child | `Aff.subst`, affine overrides only | contract at the override point | evaluated override list; child family applied to it |
| recursion | impossible | by induction, by hand | by induction with the IH as child profile (section 2.7) |
| cost to the ripple milestone | highest | cheapest but not a tactic | middle |

### 2.6 Port-connection forms, overrides and child forms

| form | extractor | `Hier2` | route C |
|---|---|---|---|
| named, ordered, `.name`, `.*` | canonical, one `PortConn` per port (MEASURED) | n/a | nothing to do |
| actual = window (`x`, `x[i]`, `x[i+1]`, `x[h:l]`, row `x[i]`), literal | ok | `fitExpr2` assign | structure by `Acc`; M-inline; literal has no reads |
| actual = fragment expression (`p & q`, `~x`, `s ? x : y`), concatenation | ok | ok at equal width; `portSafe` when narrower (`:378-387`) | structure by `rdsOf?` (`CombView.lean:642`), so WP-B2 operators arrive for free; equations by M-lite |
| narrower non-`portSafe` expression (`n2 + n2` into 4 bits) | ok (`Binary`, MEASURED `u5`) | `PortConn:context-width`, register `le-portconn-context-width`, `never`, `P-SAME-PROGRAM` | refused; widen explicitly |
| bare net narrower than a net port | `net: true` (MEASURED `u6`) | `PortConn:net-width`, `refused-now` (Xcelium split) | refused |
| unconnected output `.co()` | `target` absent | no process | no target, fine |
| unconnected input | `expr` absent | `z` literal (net) or nothing (var) | refused (K6) |
| output into a concatenation `{t8a, t8b}` | ok (MEASURED `u8`) | `instLhs2` (`PortConn:target` for a nested concat) | refused until multi-window targets (the plain assign refuses concat targets too, `CombView.lean:687`) |
| output width not equal to its target | not probed | `portOut` resize (`:400`) | `width_k` goal, as for gates |
| instance array `fa u [N-1:0] (...)` | `InstanceArraySymbol`, loud (MEASURED); `hi-instance-array`, `later` | n/a | use a generate-for; an extractor lowering to one is possible (open question 6) |
| parameter override by literal, affine or `N/2` | symbolic expression (MEASURED: `.W(N)`, `.N(N/2)`) | `PInst.given :343-357`, INT class | carried as a `CE`; `$clog2` refused as for localparams (`CombView.lean:970`) |
| typed child parameter, override needing narrowing | not probed (`ConversionExpression:width`, `Hier2.lean:166-170`) | `hi-override-context`, `never` | use `parameter int` children |
| child parameter without default | `ModuleDefinition:elaboration`, loud (register `hi-module-elab`, `later`; not probed) | n/a | give every child parameter a default |
| generate-local declaration beside an instance (`logic [3:0] w;` in the loop block) | emits a `Var` item (MEASURED) | `GenerateDecl:Var` (`Ingest2.lean:511-515`; register `le-generate-decl`) | refused; hoist the signal to module level as a vector |
| non-ANSI ports, child `wire [..]` | not probed | refused at the load gate (`Hier2.lean:178-184`) | refused; use ANSI ports and `logic` |
| `inout`/`ref`/interface ports, signed or 2-state ports, hierarchical references `u.y` | loud | loud | refused (`hi-port-direction`, `ex-hier-ref`) |

Fuel: the parent's `F = surfaceFuel args` (quadratic in the top's parameter magnitude, `Param.lean:2257`) is passed to every child
(`Hier2.lean:962`), so a child loop above it ends in the loud timeout design. Not a restriction for the designs here.

### 2.7 Recursion (F3b)

* MEASURED (`probe/rec_xor.sv`, `rec_xor_base.sv`): slang itself rejects a self-instantiating TOP (`--top xr`: `no such module
  among top instances`); a recursive child under a non-recursive top extracts when its DEFAULT lies on the recursive branch
  (N = 8: both child instances arrive); with the base case as default (N = 1) both instances arrive as
  `UninstantiatedDefSymbol:UninstantiatedDef` (register `hi-uninstantiated`, `never`, `P-SAME-PROGRAM`), so today a recursive module needs
  a default on the recursive branch.
* READ: the Lean depth is `lib.length + 1` (`Hier2.lean:950-953, 979-982`), so with one library module the first recursive step
  (`top -> xr(8) -> xr(4)`) is already refused, and even `xr(2) -> xr(1)` reaches depth 0, which refuses before it looks at the
  module; the register row is `le-recursion` (`F3B`: "flattening by induction ... with a symbolic recursion
  depth"). Decided 10/29: "F3b moved to Day 6 (no current task needs it)".
* PLANNED recipe, only for route C: (1) replace the constant depth by a fuel computed from the arguments, with a monotonicity lemma
  (`instantiateRec k = .ok m` gives the same at every `k' >= k`; an induction on depth, about 150 lines, UNVERIFIED); (2) the
  player proves the family by strong induction on `N`, the induction hypothesis being the child's profile at the halved parameter,
  passed to `sv_structure` as the child hypothesis; (3) optionally the extractor elaborates a definition per instance (the
  prerequisite of `hi-module-elab`) so the base case may be the default. The tactic never inducts. Estimate 5 to 7 agent-days after
  I4; not scheduled.

## 3. Interactions (c)

### 3.1 The register

| rows | effect |
|---|---|
| `hi-*` (extractor, Python) | unchanged by route C. The ones a contestant meets: `hi-instance-array`, `hi-module-elab`, `hi-uninstantiated`, `hi-override-context` (never), `hi-port-default`. `hi-override-untyped-width` (Icarus-only split, proposed `later`; `design/nondeterminism/NOTE.md:252`) is first on the nondeterminism list and independent of this work. |
| `le-portconn-*` | inherited: any of them leaves a non-`assign` process, so no tactic can prove `CombDesign`; the recognizer's own admission (`connOk`) must be the same Boolean as `connProcs`' branches and is a premise of `soundH` (soundness story iv). The messages should quote the row id. `context-width` and `hi-override-context` are `never` ("Yosys is non-conformant", `NOTE.md:258`). |
| `le-driver-*` | clause 1 (`later`) to 4 (`never`) are subsumed by `CombDesign.disjoint`/`selfDisjoint`/`notInput` (`Hier2Gen.lean:625-632`); for a hierarchical top `topGuard` runs `driverGuard` on the flat result (`Hier2.lean:974`), which the tactic route discharges from `CombDesign` exactly as `instantiateGD2_of_combDesign :735` does for flat tops. Instance outputs on disjoint bits of one signal stay admitted (`Hier2.lean:159-160`). |
| `le-recursion` / `F3B`, `le-library-missing`, `le-genvar-path`, `le-generate-decl` | unchanged; `le-generate-decl` ("hoist generate-local declarations as `<path>.<name>` like instance signals") is a second customer of K1 to K3. |
| `tl-sv-structure-fragment` | its trigger text names "instances" as a stage-2 lane; after I3 it becomes the exact list of section 4's "not covered". New `later` rows for the new messages (parametric child, expression actual, unconnected input, instance cycle) via `tools/gen_sv_refusals.py --write`, then `--check`. |

### 3.2 The proof chain

| file | role | under route C |
|---|---|---|
| `Comb2Base/Sound/Term`, `Comb2` (`CombDesign`, `Acyclic`, `CombEqs`, `Runs2`, `Terminates2`) | settle theory, per `Design2` | unchanged |
| `CombKnownBits`, `CombKnownThm` (`XFree`, `Covered`, `settled`) | knownness, per `Design2` | unchanged; K6 supplies its hypotheses |
| `svgolf/SvGolf/Comb.lean:113` `satisfiedAt_of_comb` | task reduction, any `Design2` | unchanged |
| `Hier2`, `Hier2Gen` | flattening and handles | `Hier2`: only the depth fuel (F3b); `Hier2Gen`: additive lemmas |
| `CombView.lean` (`TSite`, `Summary`, recognizer) | structure | extended: instance item, multi-window site, child summaries |
| `CombViewThm/Sound/Main` (`Desc`, `Realized`, `Summary.sound`, `comb_of_summary`, ...) | structure soundness | NEW twins `CombViewH*`; existing theorems untouched |
| `CombEqBase/Shape/Thm/Plain/Tactic` | equations | NEW `eq_view_H`; `Sk` gains `subst` only in I4 |
| `CombProc*`, `CombAlias2` | `always_comb` lowering | untouched; a child with `always_comb` needs the lowered variant of the kit (+3 to 5 days) |
| tactic front ends | three `findGD2` copies | I0: say "hierarchical"; I3: read `instantiateHD2` |

### 3.3 Sequencing against WP-B2, S1b, S3b and the slot

* **S1b** (multi-window `always_comb`, `design/always-comb/README.md:200-203`) and the instance site need the same generalization of
  `TSite` (one site, several written windows). Do it once; if I3 runs first it pays about +2 agent-days and S1b gets it free.
* **WP-B2** (`design/word-level/B2-NOTE.md`) edits `rdsOf?` and threads the context width `tw` through `Sk.bit` in six files. Connection
  actuals and child bodies use the same recognizer, so B2's operators arrive in hierarchical designs for free. I4's `Sk.subst` needs one
  arm per `Sk` constructor (each new constructor already costs five definitions, `B2-NOTE.md:57-59`), so M-inline waits for B2's `Sk`
  shape; M-lite does not.
* **S3b** (`case`, temporaries): a child's temporaries become hoisted internal signals; K1 to K3 already cover internal child signals.
* **The slot.** I1 and I2 are NEW additive files (plain Lean and `LeanModels.Sv` builds, no edit of a shared file), so they can queue
  at any time. I3 and I4 edit `CombView*`/`CombEq*` and wait for B2 and S1b. Each landing needs the regression of 386 checks
  (3154 s, `PLAN2.md:105`) twice.

## 4. Plan, estimates and the cheapest useful milestone (d)

| step | content | agent-days | slot-days | stopping value |
|---|---|---|---|---|
| I0 | the three `findGD2` copies (six call sites) detect `instantiateHD2` and say "module instances are outside the `sv_comb` tactics: flatten the design in the source, or prove by hand"; `PROVING.md:545`; `check.py --tactics` text; one hierarchical positive pair in `tests/` (design and score stages only); register wording | 0.5 | 0.25 | the player is told the truth now |
| I1 | SPIKE, plain Lean against the built library, no shared-tree edit: `CombDesign (ripple_fa.sem N)` for all `N` from `CombDesign` of the closed `full_adder` design, via K1 to K3 and K7. GO if about 400 lines, no whnf storm, and K2 is settled (a `toString` injectivity lemma, or a different argument for distinct prefixes) | 1 to 1.5 | 1 | go / no-go on C; also answers the symbolic `PInst.given` / `atPoint` reduction question (appendix B) |
| I2 | the kit K1 to K7 as NEW files `LeanModels/Sv/Hier2Comb*.lean`; acceptance: `CombDesign` and `Acyclic` of `ripple_fa.sem N` and the transfer of its equations, by hand, in `Examples/system-verilog/ripple_fa/comb.lean` | 5 to 7 | 4 to 5 | a by-hand route for hierarchical designs, no tactic |
| I3 | `summaryH`, `soundH`, `comb_acyclic_view_H`, `decls_view_H`, `findHD2`; `sv_structure` and `sv_interface` on a hierarchical goal; the multi-window site (or reuse S1b's) | 4 to 6 | 3 to 4 | `add_struct`, `add_interface` of `add_fa` close with the `add_n` script |
| I4 | `sv_equations`: M-lite, then M-inline (window and literal actuals) | 2 to 3, then 2 to 3 | 2, then 1.5 | `solution` of `add_fa` |
| I5 | reference `add_fa.{sv,lean}`, three negatives (unconnected input, narrower actual, instance cycle), register and docs, regression | 1.5 to 2 | 1 to 1.5 | in the suite |
| total I0 to I5 | with M-lite only | 14 to 20 (expect 17) | 11 to 14 | |
| | with M-inline | 16 to 23 | 13 to 15 | |

The by-hand half alone (I0, I1, I2 and a hand proof of `ripple_fa` on the kit) is 7.5 to 10.5 agent-days. Calibration: WP-G Gate 2 was
sized 5 to 7 slot-days and took about 1.5 (`PLAN2.md:106`); B2 v1 is sized 8 to 10 agent-days (`B2-NOTE.md:266-269`). Route C is close
to WP-G's soundness chain but adds K2 and K5, which G2 did not have. If the WP-G ratio repeats, the whole ladder is 5 to 8 agent-days;
I do not plan on it.

**Add-ons, each costed apart:** parametric child `rca #(W)` (a child lemma quantified over `W`, `using`-style child hypotheses, the
symbolic reduction of `PInst.given`/`atPoint`): +3 to 5; recursion (section 2.7): +5 to 7; `always_comb` children: +3 to 5; instance
arrays by extractor lowering (Python, pins on Xcelium for the LRM 23.3.3.5 slicing rule): +1 to 2.

**What the milestone does NOT cover:** a parametric child; an expression as an actual in the inlined equations (M-lite names appear);
recursion and induction over instances; children with `always_comb`, flops or clocks; instance arrays; generate-local declarations;
unconnected inputs; output into a concatenation; two instances coupled through each other's ports; more than two loop levels in
total; `inout`, `ref`, interface and signed ports; hierarchical references; any child not in the fragment of the current recognizer
(but a child with its own generate loops is in, and so is every operator B2 or S2 adds).

**Main risks, by weight.** (1) K2, the prefix-distinctness lemma over `toString`, the one piece with no precedent in the tree. (2) K5,
`evalPure2` under renaming: mechanical, but it touches the 16-constructor evaluator and the `Res` plumbing. (3) The black-box rank
refusing a legal design; the message must say "instance cycle". (4) Elaboration cost: the existing tactic proofs take 30 to 90 s;
the hierarchy lemmas add a layer of `rfl` on the flattening at a symbolic parameter, where whnf storms have happened before
(`Hier2.lean`'s own `fa_child` needed a hand `rw`). (5) Merge conflicts with B2 and S1b (section 3.3).

## 5. Reference designs that get shorter or newly possible (e)

| design | with hierarchy | verdict |
|---|---|---|
| `add_n` | `add_fa` above: the same proof script, the four same equations | not shorter; the demonstration and the regression design |
| `mul_n` (133 lines) | row adder as `rca #(N)` (`probe/mul_h.sv` extracts, scores within 0.7 GE, equals `mul_n` at N = 6): the six nested 2-D coverage goals and the `(row, column, phase)` key `mulKey` become a row-level key | plausibly shorter; needs the parametric child (add-on); UNVERIFIED |
| `mul_tree`, `mul_tree_h`, `mul_wallace` (370 to 433 lines) | compressor cells as modules | a redesign; the two-level loop cap is where hierarchy would help; needs the add-on |
| `sbox_bp` (113 plain sites) | three modules | not needed: P3b already made the flat netlist 12 s (`PLAN2.md:105`) |
| `fdiv16` | the 13-stage restoring divider as a `div_stage` module: the H2 "digit loop (induction over stages)" (`PLAN2.md:237`) is a stage contract plus an induction over instances | the one design where hierarchy is the natural proof structure; needs B2's operators in the stage |
| bitonic sort, Karatsuba (register `le-recursion`) | recursion | newly possible only after F3b; no task asks |

## 6. Open questions for the maintainers (f)

1. **Start now or behind B2 and S1b?** My recommendation: I0 now (0.5 day, no risk); the spike I1 when a task or reference wants a
   hierarchy, `fdiv16`'s stage being the first real customer; I3 and I4 behind B2 and S1b.
2. **Black-box rank.** Accept that an instance is one rank step (two instances coupled through each other's ports are refused even when
   no combinational path exists)? Recommended: yes, with a message that says so.
3. **Equation shape.** Parent-name equations (M-inline) as the target, hoisted-name equations (M-lite) as the first release, and the
   ordinal rule "each connected output is one writer of its target"?
4. **Unconnected inputs.** Refuse (an x/z literal, matching `tl-xfree`), or admit when the child never reads the port?
5. **Generate-local declarations** (`le-generate-decl`) block the natural way to chain instances (a local `wire` per iteration).
   Worth the hoisting prerequisite, which shares K1 to K3 with this work?
6. **Instance arrays** (`fa u [N-1:0] (...)`): an extractor lowering to a generate-for (register: "equivalent to generate-for of
   instances"), needing an Xcelium pin of the LRM 23.3.3.5 slicing and broadcast rule. Wanted?
7. **F3b.** Defer until a task wants recursion? And for the extractor: keep "a recursive module needs its default on the recursive
   branch" (MEASURED), or implement per-instance definition extraction (`hi-module-elab`) first?
8. **Where do child obligations live?** Inside the tactic for closed children (decided natively), visible `have hfa := ...` in the
   player's file for parametric ones. Recommended.
9. **Regression policy.** The hierarchical elaborators fall through on every existing goal shape and the goal dumps of all existing
   references stay byte-identical, as G2.2 did?

## Appendix A. What I ran

`sh svgolf/design/hierarchy/probe/run.sh` from the repository root (no Lean; a few seconds). Sources under `probe/`: `mul_h.sv` (two
levels of hierarchy, `rca #(.W(N))` of `full_adder`), `rec_xor.sv` and `rec_xor_base.sv` (recursive child, default on the recursive
branch and on the base case), `conn_forms.sv` (positional, `.*`, `.name`, constants, a concatenation, an unconnected output, a
narrower expression, a narrower bare net, an output into a concatenation, an instance array), `equiv.ys`, `summarize.py`. Results: all four extract with no
`Unsupported` node except the instance array and the two `UninstantiatedDef` of the base-case variant; the scores of section 1.4;
the SAT proof silent. A `logic [N-1:0] sm;` inside the instance's generate block was also extracted (the block then lists `Var`
items next to the `Instance`, MEASURED) and is what `Ingest2.lean:511-515` turns into `GenerateDecl:Var`.

## Appendix B. What I could not verify

* That `findGD2` fails on `instantiateHD2` exactly as read: the symptom is documented (`PROVING.md:545`) but I ran no tactic.
* Any claim about elaboration time or `maxHeartbeats` of the new lemmas; every estimate in section 4.
* Whether core has a `toString`/`Int.repr` injectivity lemma usable for K2 (no hit in `LeanModels/Sv`); whether the `String`
  `find?`/append API makes K1 pleasant.
* That `PInst.given` / `PDesign.atPoint` reduce by `rfl` at a SYMBOLIC override (`ripple_fa/gen.lean` covers only the 0-parameter
  child, `fa_child :226`; the `hier_params*`, `hier_width*` rows are concrete). Decides the parametric add-on.
* The depth exhaustion at `top -> xr(8) -> xr(4)`: read from `Hier2.lean:950-953`, not run.
* How the checker's `design` and `solution` stages behave on a hierarchical submission (no such test exists).
* No simulator pin was added or needed: route C does not change the semantics. The instance-array slicing rule would need one.
