# WP-G, S1b: bodies that write several windows — scoping note (NOT implemented)

Status (2026-10-31, branch `wpgs2`): **investigated, not started on the proof side.** The semantic fact the
feature rests on holds today and was checked on the real tree; the summary/realization layer is a much larger
edit than the gate-0 estimate suggested once it is counted declaration by declaration. This note records the
measurements, the options, and a recommended order, so the decision can be made before the slot time is spent.

## 1. What already holds (checked)

`Design2.lowerComb` already lowers a body that writes k windows to ONE assign `{W₀,…,Wₖ₋₁} = {E₀,…,Eₖ₋₁}`
(`SymState.toAssign`), and the settle theory takes it (`CombDesign.assign`: a target with static windows, a
concatenation of leaves; `selfDisjoint`; `Acyclic` quantifies over `tj.wins d`). Probe on the fixture
`fixtures/add_proc_m.sv` ("the whole cell in one body": `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i]; s[i] = p[i] ^ c[i];`),
`add_proc_m.sem 2` lowered:

    ["assign windows=1", "assign windows=1", "assign windows=1", "assign windows=2", "assign windows=1", "assign windows=2"]

and `sv_structure` on it today answers (the C1 message): ``site `g_bit#1`: always_comb block with several statements
(outside the first fragment: …)``. So nothing in the semantics or the settle theory is missing; the gap is the
SUMMARY (`TSite` has one target) and everything proved from it.

## 2. What a faithful S1b touches (counted on the tree at `5a014f92`)

Occurrences of the single-window assumption (`.tgt`, `.win`, `SiteInst`, `TSite`) per file: `CombView` 4/8/4/10,
`CombViewThm` 17/2/3/4, `CombViewMain` 15/31/10/3, `CombViewSound` 2/0/2/6, `CombProcSummary` 5/0/0/8,
`CombProcLower` 16/18/10/6, `CombProcEq` 44/31/0/6, `CombEqThm` 34/28/0/6, `CombProcTactic` 6/5/0/0, `CombEqTactic` 4/2/0/1.

The realization chain that must change (P layer, all stated with ONE window per process): `Desc`/`DescL`
(`p = .assign (.concat [si.win.lhs]) e`), `pairs_descL` (110 lines), `Summary.soundL` (95), `descL_facts`,
`realizedL_comb` (105: `hwr : m.Writes i wn → wn = q.1.win`, `hpw`, `selfDisjoint`), `realizedL_acyclic` (50:
`rank_insts`), `driversOk_of_lowered` (170), `comb_of_summaryL`/`struct_of_*L`; on the equation side `site_lowL`,
`eq_of_summaryL`, `EqSiteL`/`EqsL`, the knownness facts per window and the stable aliases; in the tactic the
obligation generation (`inRange`, `driverDisjoint` incl. WITHIN a site, `rankDecreases` by any window name,
`noSelfRead` against every window of the body, `width`/`bitRead`/`cover` per window). About 2000 lines of
statement and proof edits across eleven files, none of them mechanical copies: each is a window-list
generalization of an existing argument (`∃ q, wn = q.1.win` becomes `∃ q, wn ∈ q.1.wins`, pairwise disjointness
becomes disjointness of window LISTS, the rank certificate must be constant on a body).

The semantic core is smaller but not free: `symExec` of a block of independent statements from a NON-empty state
needs `symSubst` against a state whose windows the reads avoid (`symSubst_nil` generalized; a read of a
zero-width slice can be "covered" by an entry, so the lemma needs positive widths, which the template layer has
from `LeafOk`), `SymState.write` appending, and `SymState.join` over a common prefix
(`Expr2.joinIte G A A = A` for every prefix entry); then `selfReadFree` and the self-read guard over several
windows (`readsViol_none` with a LIST of windows). Estimated 400 lines, new, additive.

## 3. A design that keeps the obligations per window

One encoding keeps `InRangeObl`, `DisjObl`, `RankObl'`, `SrcS`, `EqSiteL`, `Knowns` and the stable aliases exactly
as they are: a body of k windows is k consecutive `TSite`s (one per statement, `proc := alwaysComb (statement j)`
for the skeleton, own reads), the first marked as the head and carrying the whole body for `pairs`. The cost moves
to the realization: `pairs` keeps only heads, `DescL` talks about the group's window list, and the rank
certificate has to be CONSTANT on a group (a process has one rank; the sub-sites of a body would otherwise get the
player's per-cell ranks). That is an extra tactic obligation (`rank_group`, closed by `omega` for a rank that
depends on the loop index only) and a visible change of `sv_structure?` for every design (the sites are listed per
window). It still needs the whole realization chain above and the group-rank argument; it saves the obligation
side, about a third of the list.

## 4. Recommendation

1. **Do S3b before S1b.** The idioms that need S3b (default-then-override on ONE window, `case` arms that are
   `if` trees) are more common than a body writing several independent windows, they use only the single-window
   `PTree` machinery (a `seq` node with substitution of the earlier path value, `symExec` of statements against a
   non-empty state on ONE window) and no summary change, and they unlock temporaries' first half.
2. **Consolidate the copies (G22-NOTE section 3) before S1b**, or accept that S1b edits the P chain only and the
   old chain keeps `more = []` (the lead's instruction): the edit then forks every shared lemma that mentions a
   window (`StructOk`, the three obligations, `SiteInst`) or adds `more = []` cases to the old proofs.
3. If S1b goes ahead as specified: four gates, each green on its own. (a) the semantic core above, with a theorem
   on the fixture at a concrete `N` (the lowering of the body IS the 2-window assign); (b) the template layer
   (`PT`/`PTR` bodies of several trees, `instProcess2_body`, the recognizer, `PSk` list, the C1 text); (c) `TSite.more`
   and the realization chain; (d) equations, aliases, the tactic, the Example, the dumps.

Acceptance as asked: (1) the whole-cell design proved for every `N` with the tactics; it scores the same as
`add_n` (the canonical flow maps the body to the same netlist: 112.0 GE, depth 33 at `N = 16`), so it is an
expressiveness result, not a leaderboard candidate; (2) the 24-file dump set byte-identical except where a goal
intentionally changes (the C1 refusal text in `comb_proc`'s `neg_multi`); (3) pins, `#pin_axioms`, default
heartbeats; (4) docs.

## 5. S3b outcome (2026-10-31): what was built, what was not

Built (single-window `PTree` machinery only, no summary change): `PTree.ovr c a b` / `PT.ovr` / `PTR.ovr` /
`PSk.ovr` — default-then-override, `b; if (c) a;`, the last write wins; a block of several statements of ONE window
(a first tree, then `if (c) tree;` overrides without `else`; `begin … end` branches may hold their own default and
overrides). The lowering of `ovr c a b` IS that of `ite c a b` (so every lemma about the lowered expression, its
reads, widths and Boolean reading is the old `ite` arm, shared by an alternative pattern); only the STATEMENT
differs (`toStmt` flattens the base's block and appends the `if`). The reads of an `ovr` site are in SOURCE order
(`b.rds ++ rc ++ a.rds`), which is why `PSk.ovr` lists its leaves in that order and `stmtSk` folds a statement list
base-first (`stmtSkL`, `ovrSk`, `stepSk`; the snoc lemma `listSk_snoc`).

The two points the notes of section 1 and 2 flagged both landed as predicted: (1) the earlier statements' window is
a NON-EMPTY symbolic state for the later ones — `symSubst_apart` (a read that overlaps nothing of the window is
unchanged by it) needs the read to be non-EMPTY too (`ReadWin.apart`: a zero-width slice at the edge of a window
is "covered" by it), so `PTree.noRead` is now `ReadWin.apart`, supplied by the summary's geometry (`acc_rd_pos`);
(2) `SymState.write`/`join` over one window give the window back (`write_single`, `join_single`), the self-read
guard walks the statement list (`listCombViol_append`).

NOT built, with the reason:

* **SSA reads of the written window.** `y = a; if (e) y = y ^ b;` is refused (the `noSelfRead` message of
  PROVING 13). The `symSubst` lemma generalizes (the independence lemma becomes a substitution lemma), but
  the SUMMARY cannot carry it: `NoSelfRead` and the rank obligation treat any read of the body's own window as a
  cycle, and the recognizer lists every read of every leaf. Reading the PATH value needs the reads of the body to
  be split into "reads of the signal" (rank-ordered across sites) and "reads of the earlier write" (internal) — a
  summary change, which this step was told not to make. Pinned negative: `comb_ovr/neg/neg_rbw.sv`.
* **`case` arms that are trees.** `PTree.cases` has leaf arms (`List (List Expr2 × Expr2)`); tree arms need the
  arms to be trees, i.e. a NESTED inductive (`List (List Expr2 × PTree)`), for which `induction` does not exist.
  The honest route (measured on paper, not built): one generic induction principle per tree type proved from
  `PTree.rec` (`∀ it ∈ arms, P it.2`), mutual structural definitions for the arm lists (`low`, `toStmt`, `wf`,
  `noRead`, `rds`, `Ok`, ...), and list lemmas in the style of `caseLow`/`reads_caseLow` for every family
  (about 25 statements, roughly the size of S3a again, ~1000 lines). A linear "spine" encoding (one node per arm)
  was rejected: the statement is ONE case, so its items would have to be reassembled from the spine by every
  statement-side lemma (`symExec`, `mayW`, `drvWins`, `combViol`), the subject's reads would be duplicated per
  node in `rds`, and the skeleton would need the head's reads at every node. `Examples/…/comb_ovr/case_tree.sv`
  documents the boundary (its refusal is pinned).
* **`else if` chains without a final `else` after a default** (`y = d; if (a) y = 1; else if (b) y = 2;`): the
  second `if` is partial inside the `else`; it needs a hole in the tree. Add the final `else`, or write two
  overrides in the opposite order.

## 6. S1b gate a (2026-11-01): the semantic core — built

New content only in `CombProcStmt.lean` (section "S1b gate a"), plus `Examples/system-verilog/comb_multi`. No summary,
template, recognizer, skeleton or tactic change: the tactics still refuse a multi-window body with the C1 message.

* **A body is a list of segments** `Seg := ⟨tgt, W, t⟩` (a tree over its own target and window); `bodyStmts` is the
  flattened statement list (`Seg.stmts` = `baseL` of the tree, so an override tree contributes its block), `bodyStmt`
  the `.block`, `bodyWins`, `bodyEntries`.
* **The tree executor over a prefix** (`symExec_treeF`): the incoming state is the windows written so far `P`, possibly
  followed by the entry of the window being written (`FrameS`, `PrefixOk`: positive widths, pairwise disjoint). Reads apart
  from EVERY window of the body make `symSubst` the identity on a list state (`symSubst_apartL`, the `S = [(W,E0)]`
  lemma generalized; the old `symSubst_apart` is its corollary), `write_frame` appends (or replaces the entry of the
  window), `join_frame` joins two branches that both extend the same prefix (`Expr2.same_self`: the prefix entries agree,
  so `joinIte` keeps them). The three single-window theorems `symExec_caseItems/cases/tree` are unchanged (they need no
  positivity); the new ones are the same arguments over a prefix, including the `ovr` and `cases` nodes.
* **The result**: `symExec_body` (the body's state is `bodyEntries`), `selfReadFree_body`, `combAdmits_body` (the
  self-read guard over several windows: `readsViol_none_ws`, `combViol_treeF` take a window SET `Ws`; `combViol_tree` is
  the instance `Ws = [W]` and the four lemmas it used are replaced by the `_ws` ones), `drvWins_bodyStmts`, and
  `lower_body_plain` / `lower_body`: `Process2.lowerComb d (alwaysComb (bodyStmt segs)) = some (assign {W₀,…,Wₖ} =
  {E₀,…,Eₖ})`, with `BodyOk` (positive widths, `allDisjoint`, per-segment `SegOk`: `symWin`, `wf`, `idxFree`, `noRead` against
  every window of the body, target `mayW`/`rdW`).
* **Why this is the right shape for gates b-d**: a segment is exactly what a `PT`/`PTR` tree (with its `ovr` nodes) is,
  `BodyOk.seg` is what `low_wf`/`low_idxFree`/`low_noRead` (with the reads of the OTHER windows added) will supply, and
  `BodyOk.pos`/`disj` are the summary's in-range and within-site disjointness obligations.
* **Fixture** (`Examples/system-verilog/comb_multi/comb_semantic.lean`): `cell_lowers` — for EVERY bit `i` and any
  design declaring `c`, `s` wide enough and the names `a`, `p`, `c`, the lowering of `add_proc_m.sv`'s cell body
  (`cellSegs i`: the carry `if/else` over `c[i+1]` and the sum over `s[i]`) is `cellAssign i = {c[i+1], s[i]} =
  {p ? c : a, p ^ c}`; `cell_admitted` (the guard is the identity). The link to the REAL extracted design at `N = 2` is
  two `#guard`s on `add_proc_m.sem 2` (its two `always_comb` processes are `bodyStmt (cellSegs 0/1)`; its
  `Design2.lowerComb` yields exactly `cellAssign 0/1`) — `X.sem N` is compiled code that the kernel cannot reduce
  (`decide`/`rfl` get stuck), which is why every concrete-width fact about the real design is a `#guard`.
* **Known limits carried to the next gates**: a read of ANOTHER window of the body that a LATER statement of the same body
  writes is refused by `noRead` against all windows (a pre-state read of a window the body overwrites is the self-read the
  lowering refuses); a read of a window written EARLIER in the body is the SSA case (gate c moves it into the summary).
  Segments are consecutive statements of one window: the recognizer (gate b) must group statements by window and refuse
  interleavings (`y = a; z = b; if (c) y = d;` writes `y` in two non-adjacent groups).

## 7. S1b gate b (2026-11-01): the recognizer and the instantiation of a multi-window body — built

New file `LeanModels/Sv/CombProcBody.lean` (imports `CombProcEq`, imported by nothing yet). No summary, template (`PT`/`PTR`
/`PTree` unchanged), skeleton or tactic change: `siteOfP?` still reads the first statement with `treeStmt?`, so a body of
several windows is still refused with the C1 text; the dumps and the references are byte-identical by construction.

* **Segments are `List (Acc × PTR)`**, not a new template type. A segment is exactly what `treeStmt?` returns (the
  target accessor and the annotated tree, with its `ovr` nodes); `bodyP2 segs := .block (segs.flatMap fun s =>
  s.2.pt.stmtsP)` is the body statement, so the existing single-tree lemmas (`inst_low`, `low_wf`, `low_idxFree`,
  `low_noRead`) are used per segment unchanged and no `PT`-level wrapper was needed. Several trees = a list.
* **The recognizer** `multiSegs?` (spec `multiSegs?_spec`: `b = .block ss`, `bodyP2 segs = .block ss`, every segment
  `Ok ds acc`, the targets `Nodup`): the first statement by `treeStmt?`, then `segFold?` over the rest. A following
  statement either continues the current window (`ovrStmt?`: an `if (c) …;` without `else` whose branch writes the
  current target; spec `ovrStmt?_shape`, `segFold?_of_ovrFold` shows it IS `ovrFold?`'s step) or starts a new segment
  by `treeStmt?`. Refused with a message: a window written in two separate groups of statements ("an always_comb body
  writes a window in two separate groups of statements (outside the second fragment: put the statements of one window
  together)", both for `y = a; z = b; y = c;` and for an override of the first window after the second); a second
  unconditional assignment of the window being built (the existing text); a latch on another window (the existing
  "writes more than one window" text, since the `if` without `else` is neither an override nor a tree); a nested
  `begin … end` with several statements (the existing text). A block of ONE window is ONE segment equal to
  `treeStmt?`'s tree (`multiSegs?_of_treeStmt`), so `more = []` behaviour for single-window sites is a corollary.
* **Instantiation**: `segsOf σ dw E elems segs` is the list of `Seg`s of gate a (`lhs σ`, `win σ dw`, `pt.low E elems w`).
  `instStmt2_body : instStmt2 E elems (bodyP2 segs) = bodyStmt (segsOf …)` (via `instStmts2_flatMap`, `instStmts2_stmtsP`),
  `body_ok` (BodyOk of gate a: positive widths, `allDisjoint`, per segment `SegOk` from `Ok` + the target and read
  accessors in range; every read of every segment is apart from EVERY window of the body: `hself`), `proc_body_eq`,
  and `lower_body_site`: `lowerComb d (instProcess2 E elems (.alwaysComb (bodyP2 segs))) = some (assign {W₀,…,Wₖ} =
  {low₀,…,lowₖ})` — the several-window `lower_site`. `drvWins_body` is the within-site part of `driversOk`.
* **Non-vacuity**: `add_proc_m.sv`'s cell as a `PStmt` (`cellBody`) is two segments (`c[i+1]`, `s[i]`, reads 3 and 2),
  `treeStmt?` still refuses it with the C1 text, and the cell instantiated at `N = 4`, `i = 1` lowers to ONE assign of
  `{c[2], s[1]}` with two elements (a ground `#guard` through `Process2.lowerComb (apDesign 4) (instProcess2 …)`);
  accepted/refused rows for a default-then-override on the second window, both interleavings, the second assignment,
  the latch, the nested block.
* **Left to gate c**: the symbolic-`N` lowering of the real cell through `lower_body_site` (it needs the summary's
  `StructOk` / in-range / disjointness obligations as its hypotheses), the sub-site vs `TSite.more` encoding (a segment
  carries the same data as a sub-site: accessor, annotated tree, reads; `more = []` for one window stays), the
  SSA reads (a read of an EARLIER window of the body), and Tier B.

## 8. Consolidation Tier B (2026-11-01): the shared cores of the proof halves — built

Library only, no statement changed, no tactic or dump change. The old chain (`CombViewSound`/`CombViewMain`) now owns
one core for each argument the lowered chain (`CombProcLower`) used to copy; both chains are thin instances.

* **B1/B2, `CombViewMain`**: `PairFacts s d' a p` (the process `p` of the design `d'` is an assign to a target whose
  windows are `[a.win]`, with the positivity / not-an-input / loud-free / reads / idents facts of one footprint),
  `mem_insts_of_map_fst`, `desc_facts` (an instantiated old site satisfies `PairFacts`), `realized_comb_core` and
  `realized_acyclic_core` (the bodies of the former `realizedL_comb` / `realizedL_acyclic`, over `PairFacts`).
  `realized_comb`, `realized_acyclic`, `realizedL_comb`, `realizedL_acyclic` are one `exact` each (the old chain
  supplies `desc_facts`, the lowered chain `descL_facts`, whose proof now delegates its old-site case to
  `desc_facts`). A multi-window `PairFacts` (a window LIST per footprint) is the one statement gate c edits.
* **B3, `CombViewSound`**: `SiteCtx` (what the per-site proofs read at a located site reached at `σ'`, `E'`: context,
  declared names, parameters, reach, `InWin`, `AccOK` of the footprint accessors), `pairs_ctx` (every pair of
  `Summary.pairs` is a located site's footprint and instantiated process, with its `SiteCtx` — the 55-line preamble
  of `pairs_desc` and `pairs_descL`), `pairs_desc_site` (an old site satisfies `Desc`). `pairs_desc` is four lines,
  `pairs_descL` keeps its procedural branch only.
* **B4, `CombViewSound`**: `sound_prefix` (the parameter / declaration / generate stages of `Summary.sound` and
  `Summary.soundL`: the reached context and the instantiation `M` with the summary's declarations and process list
  `(s.pairs σ E elems).map Prod.snd`); both soundness theorems start with it.
* **B5, `CombViewSound`**: `fams_expand2W` (the finite family expansion from `∀ f ∈ s.fams, f.Wf` alone — the only
  part of the spec it reads); `fams_expand2` and `fams_expand2P` are the corollaries over `SpecOk` / `SpecOkP`.
* **Kept names and statements**: `realized_comb`, `realized_acyclic`, `realizedL_comb`, `realizedL_acyclic`,
  `descL_facts`, `pairs_desc`, `pairs_descL`, `fams_expand2`, `fams_expand2P`, `Summary.sound`, `Summary.soundL`.
  New: `PairFacts`, `mem_insts_of_map_fst`, `desc_facts`, `realized_comb_core`, `realized_acyclic_core`, `SiteCtx`,
  `pairs_ctx`, `pairs_desc_site`, `sound_prefix`, `fams_expand2W`; all `#pin_axioms`-checked in `CombProcEq`.

## 9. S1b gate c1 (2026-11-01): `TSite.more` and the obligations — built (single-window output unchanged)

Decision (lead, 2026-11-01): a body of several windows is ONE site with further target accessors, `TSite.more : List Acc`
(the head window is `tgt`, the others follow in source order; `rds` are the reads of all of them), NOT k sub-sites.
Why: (1) the expansion chain is untouched (`d.generates = s.fams.map TFam.toGen` needs one process item per body; sub-sites
would have to be dropped from `toGen`, `itemProcs`, `Summary.enum`, `pairs` and the `enum` lemmas re-proved, with a head
flag); (2) the site identity (`SiteId`) is per process, so the rank certificate is constant on a body by construction (no
`rank_group` obligation); (3) `Acyclic`, `selfDisjoint`, `LowRel`, `driversOk_of_lowered` already speak window lists per
process: the lowered design really has one assign per body.

c1 changes only the data and the obligations; the recognizers still return `more = []` (the switch is c3), so every
design reads exactly as before:

* `TSite.more`; `TSite.names` / `TSite.affNames` read `tgt :: (more ++ rds)`; `StructOk` (no window of a site is an
  input; `accOk` of every access) and `AutoObl` (`DimNum`) read `tgt :: (more ++ rds)` IN PLACE.
* `InRangeObl`, `DisjObl`, `RankObl'` gain ONE conjunct each, guarded by the decidable test "no site has a further
  window": `InWinAcc` (the further windows in range), `DisjMore` (a further window of any site against every window of
  every other instance, and the windows of one instance pairwise disjoint), `RankMore` (a read overlapping a FURTHER
  window of the writer: the rank is the writer SITE's). The tactics' `simp` sets decide the guard first (`↓reduceIte`:
  `∀ b ∈ [sites], more = []` normalizes to `True` on a constructor-term summary) and drop the conjunct: NO tactic
  simp list was edited and the 24 goal dumps are byte-identical. The extractors `InRangeObl.more_all`,
  `DisjObl.more_all`, `RankObl'.more_all` give the plain conjunct in both cases (vacuous when no site has a further window).
* The flat-netlist closed forms (`CombViewPlain`): `disjObl_of_plain`, `rankObl'_of_plain`, `autoObl_of_plain`,
  `inRangeObl_of_plain` take ONE premise `hp : ∀ a ∈ s.lsites, a.hdrs = [] ∧ a.site.more = []`. MEASURED TRAP: a separate
  `hm` premise cost one more `closeByDecide` per lemma (each `evalExpr`s a term that embeds the whole 113-site summary,
  about 3.8 M heartbeats a decision): `bp_struct` +11.9%, `sbox_bp` `solution` +2.4%. Folding it into `hp` brought them
  to +0.7% / +0.3%.
* Heartbeats of the reference files before / after (per theorem, k heartbeats, instrumented `count` of every top-level
  theorem): see the c1 report (every theorem within +0.7%, `add_mux_correct` 185 842 -> 186 550 against the 200 000
  limit, `bp_struct` 126 308 -> 127 169, `tbl_struct` 45 087 -> 45 237, `tree_struct` 793 903 -> 796 581).

## 10. S1b gates c2 and c3 (2026-11-01): the realization chain and the recognizer switch — built

**c2, the realization chain over window lists** (no behaviour change). `SiteInst` gains `more : List (Win × Lhs2)` and
`SiteInst.wins` (the head window, then the further ones); `PairFacts` talks about `windows? = some a.wins` (every window
positive, none an input); `DescL`/`LowKind` take the assign of ALL the windows (`.concat (si.wins.map Win.lhs)`);
`Desc` carries `si.more = []` (an old site has no further window). The instance lemmas: `insts_disj_wins` (every window
of one instance against every window of another), `insts_within` (the windows of ONE instance pairwise disjoint),
`inrange_insts_wins`, `inst_notInput`, `rank_insts_all` (a read overlapping ANY window of the writer: the rank is the
writer SITE's), `SiteCtx.win_facts` (the geometry of every target window at a reached valuation). `realized_comb_core`
and `realized_acyclic_core` read them, so `realized_comb`/`realizedL_comb`/`*_acyclic` are unchanged one-liners.

**c3, the recognizer switch.** `siteOfP?` keeps the first fragment exactly (`treeStmt?` first, `more = []`) and, when
that refuses a body, reads it with `CombProc.multiSegs?` (gate b): at least two segments make ONE site, head window the
first segment's target, `more` the others in source order, `rds` the reads of all segments (`segsRds`, `multiSite`).
Refusal text: `treeStmt?`'s message as before, EXCEPT the new interleaving message (a window written in two separate
groups of statements); `comb_ovr/neg_otherwindow`, `neg_second`, `neg_elsechain`, `neg_nested`, `neg_latch` keep their
old texts (a body `multiSegs?` also refuses falls back to the old message). `siteOfP?_cases` is now a three-way inversion
(old site / one tree / several windows); `multiSite_shape` gives `tgt :: more = segs.map fst`, `rds = segsRds segs`,
`more ≠ []`.

* **The several-window branch of `pairs_descL`** (`pairs_descL_multi`, ~60 lines): `lower_body_site` + `proc_body_eq`
  (gate b) give the lowering and the instantiated process; the lowered assign reads only the site's reads
  (`rdOK_segs`: the per-segment `low_rdOK` concatenated), the windows the body drives each match a window of the
  footprint (`drvWins_body`). Its hypotheses are the summary's: `SiteCtx` facts, the in-range of EVERY window
  (`InRangeObl` + its guarded conjunct), `NoSelfRead` against EVERY window of the body (the head conjunct plus the guarded
  further-window conjunct; `NoSelfRead.all` gives every window), and the within-site disjointness `DisjWithin` (the second conjunct of `DisjMore`). `Summary.soundL` and
  `pairs_descL` therefore take `hwithin : s.DisjWithin σ` (the structural theorems pass `hdisj.within_all`; the equation
  theorem `eq_of_summaryL` gets it from `EqFragL`).
* **The equations stay single-window**: `EqFragL` gains `ls.site.more = []`, so `sv_equations` refuses a site of several
  windows through the existing fragment check (the equations of a body of several windows are gate d), and
  `site_lowL` has the third `siteOfP?_cases` branch closed by that conjunct.
* **The tactics**: `sv_structure` accepts a body of several windows, with NO change to any `sv_norm` simp list. The
  else-branches of the guarded conjuncts of `InRangeObl`, `DisjObl`, `RankObl'` and `NoSelfRead` are written INLINE
  with the vocabulary the lists already unfold (`Summary.InR`, `Acc.win`, `LSite.id`, `Win.overlaps`, …) and the
  site's `rds` for a several-window body is a plain `List.flatMap` (`multiSite`), so the same lists normalize them.
  MEASURED TRAP #2: the first version named the new definitions (`InWinAcc`, `DisjMore`, `DisjWithin`, `RankMore`,
  `NoSelfMore`, `segsRds`) in the three proc lists and made `NoSelfRead` read `tgt :: more` in place: +1.2% to +4.6% on
  every theorem of the proc tactic (`lut_struct` +1.0 M, `lut_settles` +1.7 M, `tbl_struct` +1.2 M heartbeats) — a
  new name costs its equation lemma per theorem, and the in-place `tgt :: more` costs a simp round per read. Inlining
  and guarding brought every theorem back to +0.0% to +0.2% over c1. The early checks (`selfReadSyntactic`, the sampled
  counterexamples of `CombViewDiag`/`CombProcTactic`) range over every window; `sv_structure?` prints
  `drives c[i + 1] and s[i]`.
* **Examples**: `comb_multi/comb_view.lean` — `add_proc_m_struct` (the whole carry/sum cell in ONE body, every
  `N ≥ 1`: `CombDesign ∧ Acyclic` by `sv_structure` and the same rank as `add_proc`) and `multi_flat_struct` (a body
  with a default, an override and a second window, no generate loop), plus the `sv_structure?` pin. The two refusal pins
  that stopped being refusals moved: `comb_proc/neg_multi` (the add_proc cell with a second statement) and
  `comb_ovr/neg_multi` (`y = a; z = b;`) are the accepted instances above; `comb_ovr/neg_interleave` is the new pin of
  the interleaving refusal.
* **Not in c**: the equations (gate d), the SSA reads (a read of an EARLIER window of the body is refused through
  `NoSelfRead`/`selfReadSyntactic` against every window of the body), and the flat-netlist closed forms for a
  design with a further window (`*_of_plain` apply when every `more` is `[]`; otherwise the tactic normalizes).

## 11. S1b gate c4 (2026-11-01): the symbolic-`N` theorem for the real cell, and the equations refusal — built

* **`cell_lowers_site`** (`Examples/system-verilog/comb_multi/cell_site.lean`): for every `N`, every bit `k < N` and every
  instantiation environment `E` of the adder `apDesign N` that binds `i` to `k`, knows the declared widths and that
  `a`, `c`, `p`, `s` are one-bit elements, `Process2.lowerComb (apDesign N) (instProcess2 E elems (.alwaysComb
  cellBody))` is ONE assign `{c[k+1], s[k]} = {low₀, low₁}` (the segments' own `PT.low` at width 1) — the several-window
  counterpart of `carry_lowers`. It goes through `lower_body_site` with the `Ctx`, the in-range / positivity /
  no-self-read / disjointness hypotheses all discharged from `apDesign`'s declarations; `multiSegs? apDecls cellBody =
  .ok cellSegs` is closed by `rfl` (the kernel runs the recognizer).
* **`sv_equations` on a body of several windows** refuses up front, with the reason and the way out, not with a failed
  decision of the fragment check: ``sv_equations: outside the supported fragment — site `g_bit#1[i]`: an always_comb
  body that writes several windows (c[i + 1], s[i]): `sv_structure` accepts it, but `sv_equations` has no equations for
  such a body yet (outside the supported fragment: write one always_comb per written window)`` (`Summary.multiWindowForEquations`
  in `CombProcTactic`, checked right after the structural check, so `sv_equations?` refuses it too; pinned in
  `comb_multi/comb_errors.lean` for the adder and the flat `multi_flat`). Without it the failure was
  `closeDecide hfrag`'s generic message plus a `decide` report.
* **Register**: `tl-sv-structure-fragment` says the open part is the EQUATIONS of a body that writes several windows
  (`prerequisite`: "the equations of multi-window bodies (S1b gate d)"); `sv_structure` is no longer refused for them.

## 12. S1b gate d: the equations of a body that writes several windows — BUILT (d0 design, d1 library, d2 tactics, d3 reference; 2026-11-01)

Gate c made `sv_structure` accept a body that writes several windows (one site, `TSite.more`); `sv_equations` refuses it
(`Summary.multiWindowForEquations`). Gate d lifts that refusal: one equation and one knownness fact PER WINDOW, and a full
`add_proc_m` solution. SSA reads (a read of an EARLIER window of the same body) stay out: `NoSelfRead` still refuses any
read of any window of the body.

### 12.1 What the golfer sees (the shape, derived from `add_proc`'s `comb_hint` and the c3 summary; printed for real at d2)

`sv_equations?` on `add_proc_m` (`hl`, `hc`, `ha`, `st`, `heqs`, `hsh` in context), the equation lines:

```
  eq_c_plain_0     : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1  : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_p_g_bit_0     : ∀ i < N, st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i)
  eq_c_g_bit_1     : ∀ i < N, st.boolAt "c" (i + 1) = if st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i
  eq_s_g_bit_1_w1  : ∀ i < N, st.boolAt "s" i = (st.boolAt "p" i ^^ st.boolAt "c" i)
  known_… (the same five, in the same order)
  stable aliases: eq_c_1 := eq_c_plain_0   eq_cout_1 := eq_cout_plain_1   eq_p_1 := eq_p_g_bit_0
                  eq_c_2 := eq_c_g_bit_1   eq_s_1 := eq_s_g_bit_1_w1       (and the known_ twins)
```

The head window of a body keeps the name the single-window tactic gives (`eq_<signal>_<block>_<position>`); window `j ≥ 1`
of the same body is `eq_<signal>_<block>_<position>_w<j>` (`known_…` likewise). **The aliases are the contract**: they are
`eq_<signal>_<ordinal>`, the ordinal counting the WINDOWS that write that signal in source order (site by site, window by
window). `add_proc_m` therefore has the SAME aliases and statements as `add_proc` (`eq_c_2` the carry equation, `eq_s_1` the
sum equation): a proof written against the aliases of `add_proc` (`tasks/add/reference/add_proc.lean`) holds for
`add_proc_m` unchanged. Stable under statement order across signals (swapping `c[i+1]`'s group and `s[i]`'s keeps
`eq_c_2` and `eq_s_1`; the generated names change, as they do under any edit); two windows of ONE signal in one body
(`y[0] = …; y[1] = …`) get their ordinals from source order. The obligation goals keep their tags; `width_k` has one goal
per window of the body, after the goals of the sites that write one.

### 12.2 The skeleton of a window (the one design decision with a ripple)

`rhsSk proc rds` is the skeleton of ONE window: the first statement, then the overrides (`ovrSk`). Today `ovrSk` SKIPS a
non-override statement (`stepSk _ => base`) but keeps applying later overrides, which for a body of several windows would
lay window 2's overrides over window 1. Proposal: **`ovrSk` stops at the first statement that is not `if (c) …;` without
`else`**. For every body the first fragment accepts nothing changes (all statements after the first are overrides: that is
exactly `ovrFold?`'s acceptance), and for a body of several windows `rhsSk` becomes the skeleton of the HEAD window with no
new data on the site. Further windows: `windowSks as ss` splits the block into its segments (a segment starts at each
statement that is not an override; the recognizer accepts exactly that segmentation, gate b `segFold?`) and gives
`listSk` of each, taking the reads chunk by chunk (`stmtRcntL`); `procSks proc rds = windowSks …` for a block body,
`[rhsSk …]` otherwise. `ptr_sk_both` (S3b: `listSk (ptr.rds ++ extra) ptr.pt.stmtsP = ptrSk ptr` for every `extra`) is
already the per-segment lemma; the new one is `windowSks (segsRds segs) (bodyP2 segs) = segs.map (ptrSk ∘ snd)` for a
recognized body. Cost: `ovrSk_append`/`listSk_snoc` (S3b) gain the hypothesis "the statements are overrides" (their uses
are on override lists). No `TSite` field is added (an explicit `cuts` list was rejected: the segmentation is syntactic).

### 12.3 The statements: SIBLINGS, no guards on the single-window route (decision B, 2026-11-01)

d0 proposed guarded conjuncts inside `EqsL`/`Knowns`/`WidthOblL`/`SrcS`/`CoverObl` (`if no site has a further window then
True else …`). d1 built them and measured: the 24 dumps were byte-identical but sbox_bp `solution` moved **+4.8%**
(342 565k → 358 991k heartbeats; 113 sites, and simp expands the guard `∀ b ∈ lsites, b.site.more = []` over every site at
every occurrence) while every other theorem moved at most +0.4%. Decision B removed the guards: the single-window
statements are back to their exact pre-d1 text, and a body of several windows has SIBLINGS that the tactic selects only
when some site has a further window (a syntactic check of the summary, the one `multiWindowForEquations` already makes).

* Unchanged (the single-window route, the one every existing design and dump uses): `EqFragL` (with `more = []`),
  `WidthOblL`, `EqSiteL`, `EqsL`, `Knowns`, `SrcS`, `CoverObl`, `eq_of_summaryL`, `eq_viewL`, `site_lowL`'s statement. No
  `hwithin` argument and no new `decide` on this route.
* Siblings (`CombProcEq.lean`): `EqFragM` (`fragOkP ∧ (rhsSk …).knownB ∧ ∀ sk ∈ (procSks …).tail, sk.knownB`, decided
  natively), `WidthOblM` (the head conjunct, then `sk.WidthOk σ' dw w` per further window), `EqsM` (the head equations of
  every site, then one fact per further window `∀ k < w, st.boolAt n (lo + k) = sk.bit σ' dw w st.boolAt k`), `KnownsM`
  likewise, `SrcSM` (the extra disjunct "a bit inside a window of `more`"), `CoverOblM`, and the producers
  `site_lowLM`, `eq_of_summaryM` (extra hypothesis `hwithin : s.DisjWithin σ`), `eq_viewLM`. The facts of the multi route
  come out as `EqsM ∧ KnownsM`, each a conjunction of the heads in site order and then the further windows in (site,
  window) order. `BitReadObl`, `AutoObl`, `InKnown` are shared (the reads of a body are all in `rds`).
* `site_lowL_single` is the old per-site lemma over generic head hypotheses (`hfrag`, `hwid`, `hmore`); `site_lowL` (single
  route) and `site_lowLM` (unified, over window lists) are its two users.
* The inline-body rule of c3: the multi route's obligations are written with the vocabulary the lists already unfold,
  EXCEPT the skeleton functions (`procSks`, `windowSks`, `listSk`, `ovrSk` …), which are new names. They go in a COPY of
  the equation normalizer, `svL_eq_norm_multi`, selected by the tactic when `s.lsites.any (more ≠ [])`; the existing
  literal copies are not touched (the c3 trap: a name in a list costs its equation lemma per theorem, +1.2% to +4.6%).
  The literal simp lists are NOT a registered attribute set, so a union (`simp only [svL_eq_norm, …]`) is not available:
  every copy carries a COPY NOTE pointing at its siblings.

### 12.4 The proof (d1) and what carries over from c2/c3

* `CombKnown.settled` is ALREADY per window with an offset: `((n, lo, w), off) ∈ Win.placed (t.wins d)` gives
  `KnownBit st n (lo + k) ∧ boolAt st n (lo + k) = e.xfBitsZ d boolAt (off + k)`, and `Win.placed` puts the first window at
  the offset of the total width of the rest (MSB first, as `SymState.toAssign` writes `{W₀, …, Wₖ} = {E₀, …, Eₖ}`). So
  `eq_of_summaryL`'s `hmain` for window j is the same three lines with `off_j`, plus one lemma on the bits of a
  concatenation: `xfBits (.concat (x :: l)) env k` is `x`'s bit `k − Σ widths(l)` above that sum and `l`'s below
  (`catBits`), with `xfWidth` the sum (`xfWidth_concat_one`/`xfBits_concat_one` of S3b are its one-part case).
* `site_lowL` gets the several-window branch: `lower_body_site` (gate b) and `proc_body_eq` give the lowered assign; its
  parts are `(ptrSk p_j).low … ` per segment, whose width and bits are `psk_low_xfWidth`/`psk_low_xfBits` (S3b) per
  segment, so the per-window statement is `e.xfBits d' env (off_j + k) = (sk_j).bit σ' dw w_j env k`. The conclusion
  quantifies over the window list (`t.wins d' = wins`), the single-window form being the one-element instance.
* Carry over unchanged from gate c: `pairs_descL_multi`, `Summary.soundL`, `SiteInst.wins`/`PairFacts`, `insts_disj_wins`,
  `insts_within`, `SiteCtx.win_facts`, `cell_lowers_site`, `NoSelfRead.all`, `multiSite_shape`. `hsrc` (SrcS ⇒
  `Sourced`) gets the further-window disjunct (the window is a member of the process's `t.wins`); `hcv`, `hxf`, `hik`
  are the same.

### 12.5 Acceptance and plan

d1 (statements, `site_lowL`/`eq_of_summaryL` over window lists, the ovrSk change with its S3b lemma repairs) builds
with the tactics untouched; d2 (the normalizer copy, naming, aliases, `sv_equations?` pins for `add_proc_m` and
`multi_flat`, the refusal removed and the old pin replaced) ; d3 (`tasks/add/reference/add_proc_m.{sv,lean}`, same
score as `add_proc`: 112.0 GE depth 33 at N = 16, `check.py` accepted, `--postsynth full`). 24 dumps byte-identical
(except the intended `comb_errors` pins), four references unchanged, heartbeat table against the merged-tree baseline
at d2 and d3 (the baseline is re-taken on the tree that contains B2 gate 2b; `lp_correct` and the three `add_mux`
declarations are the standing numbers). Every slot acquisition at most about 15 minutes: builds, dumps and the
measurement run in separate acquisitions.

### 12.6 d1 as built (2026-11-01)

Built in `LeanModels/Sv/CombProcEq.lean` (+ `multi_lowers` in `CombProcLower.lean`, `siteCtx_of_reach` extracted from
`pairs_ctx` in `CombViewSound.lean`): the `ovrSk` stopping rule with the repaired S3b lemmas (`ovrSk_append`, `listSk_snoc`
gain the override hypothesis; `ovrSk_stop`, `ovrSk_append_stop`), `windowSksF`/`windowSks`/`procSks` (fuel-structural, so
kernel `rfl` reduces them), `windowSksF_segs`/`procSks_multi`/`rhsSk_multi` (the skeletons of a recognized body), the
placed-window layer (`placedSegs`, `catBits_cons_head/tail`, `parts_bits`), `SiteLow`, `site_lowL_multi`, and the sibling
statements and producers of §12.3. The tactics are untouched except comments. All new theorems carry `#pin_axioms`
(standard axioms only); the three old `#print axioms` pins are unchanged.

Measured against the merged-tree baseline (`wpgs2/c1/m0`, thousands of heartbeats): 24 dumps byte-identical; sbox_bp
`solution` 342 565 → 342 565, `bp_struct` 127 390 → 127 390; sbox_table `solution` 189 656 → 189 749; mul_n 184 230 →
184 230; mul_tree 436 904 → 436 904; mul_tree_h 398 452 → 398 452; mul_wallace 311 026 → 311 026; add_proc `solution`
101 877 → 101 897; add_mux `solution` 90 041 → 90 041; add_mux_settled 101 389 → 101 389; lp_correct 199 433 → 199 433
(informational: not this gate's). Every `*_struct`/`solution` within +0.06% of the baseline.

### 12.7 d2 as built (2026-11-01): the tactic route

`sv_equations` (`LeanModels/Sv/CombProcTactic.lean`, `runSvEquationsL`) takes the multi-window route exactly when some site
has a further window (`s.lsites.any (more ≠ [])`, a syntactic check of the summary; the early refusal
`multiWindowForEquations` is gone). On that route it produces `eq_viewLM` (hypothesis `hwithin`, closed by the normalizer,
reported as the obligation `within` only if something is left), closes `EqFragM` natively, and normalizes the
obligations with `svL_eq_norm_multi` and the view with `svL_eq_norm_multi_at`, two COPIES of `svL_eq_norm` and
`svL_eq_norm_at` with the skeleton vocabulary added (`EqsM`, `KnownsM`, `WidthOblM`, `CoverOblM`, `SrcSM`, `DisjWithin`,
`procSks`, `windowSks`, `windowSksF`, `spanOvr`, `listSk`, `List.tail_cons`, `List.tail_nil`, `List.zip_nil_left`). All
eight literal lists carry a COPY NOTE naming their siblings (a union `simp only [svL_eq_norm, …]` is impossible: they are
macros over literal lists).

Naming is by STRUCTURE, not by counting the conjunction spine. d0 proposed flattening the view with `and_assoc`; that is
wrong because a knownness fact can itself be a conjunction (`(∃ v, …) ∧ KnownBit …` for a one-bit window), and
flattening ate the fact boundaries (seen in the first hint output). The view is split into `EqsM`'s two halves and
`KnownsM`'s two halves; the heads (one fact per site) are peeled by name as on the single-window route, and the further
windows as GROUPS (one right-nested group per site that has any), each group peeled by name. The head window keeps
`eq_<signal>_<block>_<position>`; window `j ≥ 1` is `eq_<ITS signal>_<block>_<position>_w<j>` (`eq_s_g_bit_1_w1`, named after
the window's own signal, as §12.1 says; the first implementation named it after the head's). The aliases count WINDOWS (`stableAliasesM`):
`eq_<signal>_<k>`, `k` from 1 in source order over sites and, within a site, windows.

Examples (`Examples/system-verilog/comb_multi`): `comb_hint.lean` REPLACES `comb_errors.lean` (the gate-c refusal pins,
deleted): `sv_equations?` pinned verbatim for `add_proc_m` (the five aliases `eq_c_1 eq_cout_1 eq_p_1 eq_c_2 eq_s_1`, the
same statements as `add_proc`'s) and for `multi_flat`; `comb_proof.lean` (`multi_flat_settles`: both windows proved, axioms
standard); `alias_reuse.lean` (`add_proc_m_aliases`: the five equations and two knownness facts that `add_proc`'s
`add_final` consumes, from the aliases, with the same closers); `multi_same.sv` (two windows of ONE signal, ordinals by
source order).

Measured (merged tree, baseline `wpgs2/c1/m0`): the 24 goal dumps are byte-identical, sbox_bp `solution` 342 565k →
342 565k, `bp_struct` identical, every `solution`/`*_struct` within +0.06%, `add_mux_settled` 101 389k → 101 389k,
`lp_correct` 199 433k → 199 433k. The single-window route is untouched by construction: the new code is selected only by
a summary with a further window.

### 12.8 d3 as built (2026-11-01): `add_proc_m` is a reference

`tasks/add/reference/add_proc_m.{sv,lean}` (registered in `task.json`, `tests/expected.json`, `tests/add/validate`, the
tactic-reference list of `tests/run.py`): the ripple adder with the carry cell AND the sum bit in ONE body. `check.py` accepts it
(`--postsynth full`: 4132 vectors, 0 mismatches), 112.0 GE, depth 33 at N = 16 (56.0/17 at N = 8, 224.0/65 at N = 32: the
same netlists as `add_proc`: NAND 48, XOR 32 at N = 16). **The golfer-facing claim is a pinned check**: the proof in
`add_proc_m.lean` is `add_proc.lean`'s character for character (everything after the doc comment, the imports included),
`tests/add/same_proof.py` (in the `unit` step, with a `--selftest` that shows a changed alias or import is caught), and that
it CHECKS for `add_proc_m` is the `references` step (check.py accepted). Heartbeats of the new reference (default limit 200 000k):
`add_struct` 92 575k (the two-window structure obligations; `add_proc`'s is 61 089k), `solution` 159 014k (`add_proc`'s is
101 897k); the Example proofs `multi_flat_settles` 100 306k and `add_proc_m_aliases` 176 942k.

Decisions for review: (a) the `ovrSk` stopping rule (statements unchanged, S3b lemma repairs); (b) generated names
`…_w<j>`, aliases by (signal, ordinal over windows); (c) heads first, further windows after, in the one chain; (d)
`EqFragM`'s form (a sibling of `EqFragL`, decided natively); (e) the copied normalizer `svL_eq_norm_multi` (selected by the tactic, so single-window designs pay
nothing).

## 13. WP-COV (2026-11-01): coverage goals left in the site-witness form

**Symptom.** On the one-level Karatsuba multiplier (`design/tasks-week2/clmul/karatsuba/clmul_k1u.sv`, 19 sites, 26 operand reads,
two operand vectors written by two generate families each) `sv_equations` prints its 17 coverage goals as
`∃ b : LSite, (b = site₀ ∨ … ∨ b = site₁₈) ∧ Q b` (60 to 90 KB of pretty-printed goal each) instead of the explicit disjunction of
writers that the 2-D rule of `sv_cover` reads, and `all_goals first | (intros; omega) | sv_cover` leaves 15 of them with the
message `failed to synthesize OfNat LSite 0`. Smaller variants (13 or 16 sites, 20 reads) came out explicit.

**What decides the form.** Three facts, each measured on the staged design (probes in `wpgs2/cov/probes`):

1. The coverage obligation (`CoverObl`: every site, every read, every bit) is normalized as ONE conjunction by
   `repeat (sv_eq_norm; try sv_simp)`, and only then split into goals (`repeat' refine And.intro ?_ ?_`). `sv_eq_norm`'s own
   list has `List.mem_cons` but not `exists_eq_or_imp`, so the first `sv_eq_norm` turns `∃ b ∈ sites, …` into
   `∃ b, (b = site₀ ∨ …) ∧ Q b`; turning that into the explicit disjunction of `Q site₀ ∨ …` is the job of the full simp set in the
   `try sv_simp` after it.
2. That one `sv_simp` call on the whole obligation (every read of every site) runs out of steps on the larger design, `try`
   swallows the failure, and the loop ends because the next `sv_eq_norm` finds nothing to do: the goals keep the form `sv_eq_norm`
   leaves. Measured (`wpgs2/cov/probes/P9a.lean`: the old chain's `eq_view` with the cover goal left open, then the first
   `sv_eq_norm`): the goal is in the site-witness form, and `sv_simp` on it fails with `simp failed: maximum number of steps
   exceeded` (default `maxSteps` 100000); the same `simp` with `maxSteps := 6000000` finishes (about 5 s) and the form is explicit
   (`P9b.lean`). So the form depends on reads times sites of the WHOLE obligation, not on any one goal, which is why 20 reads came
   out explicit and 26 did not. After the split into one goal per read the default budget is enough: `case cover_3 => sv_simp`
   finishes at once and the goal is explicit, and after `all_goals (try sv_simp)` and the loop, `all_goals sv_cover` closes ALL 17
   goals (`P4b.lean`, 42 s of CPU).
3. Two messages hide the real failures. `omega` on a goal that contains `∃ b : LSite` does not fail: it LOGS the elaboration error
   `failed to synthesize OfNat LSite 0` and succeeds, so `first | (intros; omega) | sv_cover` never reaches `sv_cover`; and
   `svCover`'s second alternative is `omega` too, so when the site route (`siteWitness`) fails (a bit with several writer families, a
   localparam inside `Q`) the same logged error is what the player reads.

**The fix (small).** After the split, a coverage goal that still contains an existential over `LSite` is renormalized on its own:
`sv_simp` first, then the loop (`sv_cover_renorm`, `svL_cover_renorm`, `svL_cover_renorm_multi`; `hasSiteWitness`, in
`CombEqTactic.lean`/`CombProcTactic.lean`). A goal without a site witness is not touched, so every design whose obligation
normalized as a whole keeps its normal form and its cost, and no simp list gained a name. It runs only for a design with a generate
loop: a FLAT design with a parameter (`flat_net_p`, `Examples/system-verilog/flat_net/sv_cover_site.lean`) keeps the
site form, which `sv_cover`'s site route closes (its documented purpose). The site route itself is unchanged (a bit with several
writer families still needs the explicit form, which it now does not meet on a loop design).

Not done: a site route that splits per writer family and evaluates localparams. The explicit form needs neither: the 2-D rule
already case-splits on each writer's condition (`Classical.em`), and the localparam `H` is `(↑N + 1) / 2` in the explicit goals
(`P4c.lean`), which `omega` reads.

**Measured** (staged `clmul_k1u.sv` at N symbolic; baseline = the tip before the change, `wpgs2/c1/cov0`, thousands of
heartbeats):

* The Karatsuba proof `G3h.lean` compiles WHOLE (structure, interface, the 15 `sv_bridge` fields, the combination layer and
  all 17 coverage goals closed by the standard `all_goals first | (intros; omega) | sv_cover`): 62 to 72 s of CPU, standard axioms.
  Before the change the same file left 15 goals with `failed to synthesize OfNat LSite 0`.
* New regression pin `Examples/system-verilog/comb_karatsuba/cover.lean` (`k1u_covers`: the design's 17 coverage goals and the
  two input premises, closed by the same closer; the design is the scratch one, `clmul_k1u.sv`).
* The 24 goal dumps (18 example views, 6 references) are byte-identical to the dumps of the WP-COV acceptance (`ripple_add/neg` included; the first
  version, with the flat rank list, differed there). Measured with up-to-date oleans: see "A retraction" below for the three that first looked different.
* Heartbeats (thousands), tip baseline → this change. Flat and single-site designs do not take the grouped route and are unchanged:
  `sbox_bp` `solution` 348 253 → 348 254, `bp_struct` 127 700 → 127 700, `bp_interface` 53 430 → 53 431, `bp_correct` unchanged;
  `sbox_table` `solution` 190 303 → 190 305, `tbl_struct` 45 325 → 45 326, `tbl_interface` and `tbl_correct` unchanged (the standing bar:
  nothing added to `sbox_table`'s structure). The designs of four or more sites get cheaper: `add_n` struct 43 146 → 36 903, `solution` 81 090 → 72 046
  (-11%); `add_mux` 58 368 → 46 321, 90 996 → 80 075; `add_proc` 61 134 → 49 743, 102 525 → 91 634; `mul_n` struct 279 072 → 162 028, `solution`
  185 425 → 148 563 (-20%); `mul_wallace` struct 310 906 → 214 554, `solution` 312 682 → 278 293; `mul_tree_h` struct 636 430 → 279 907, `solution`
  400 674 → 285 534 (-29%); `mul_tree` struct 797 221 → 310 506, `solution` 439 991 → 288 055 (-35%). The interface and the other theorems of
  these files are unchanged (`tree_interface` 5 327 → 5 328). The examples that take the route: `ripple_add` `ripple_correct` 164 103 → 146 653, `lp_add`
  `lp_settled` 104 595 → 92 991, `mul_array` `mul_correct` 208 461 → 171 666, `comb_ops` `add_mux_settled` 102 412 → 91 574; the one-site and word-level
  examples (`prio_struct` 24 267 → 24 268, `comb_word` `add_same_correct` 76 630 → 76 663) are unchanged.
* The Examples that exercise the route build with the new tactics: `comb_karatsuba/cover` (the 17 coverage goals of the 19-site Karatsuba design, closed
  by the same `all_goals first | (intros; omega) | sv_cover`: the WP-COV pin), `comb_multi/*` (bodies of several windows), `comb_bridge/*`, `comb_ops`, `comb_ovr`, `flat_net`,
  `lp_add` (+ `neg`), `mul_array`, `ripple_add` (+ `neg`, `proof`, `spec`), `ripple_fa`, `ripple_step`, and (after the retraction below) `comb_case`,
  `comb_word`, `comb_proc`: every module of `tools/check_sv_chain.sh --list`, 0 failures.
* `check.py` of `aes_sbox/sbox_bp` hits its 215 s limit when the machine is loaded (both trees); the heartbeats are measured on the staged solution regardless.
* Axioms: the new lemmas depend on at most `propext`, `Classical.choice`, `Quot.sound` (`#pin_axioms` in both files).

**A retraction (2026-11-02).** The first version of this acceptance said that at the tip the examples `comb_case`, `comb_word` and `comb_proc` and the `add_proc`
reference's dumps fail ("Unknown identifier `row_chain.sem`", "nonblocking assignment in always_comb", the `PStmt.forLoop` refusal), and that the tip tactics
print the same. That was wrong: the build tree the measurements ran in held STALE oleans of the `gen` modules (those examples were not among the modules the
chain builds had rebuilt since an older tip), and the probes and instrumented copies compile with `lake env lean`, which does not rebuild imports. After
`git merge svgolf-prep` (9d3c578c; `LeanModels/Sv` is the same as at e033732c, only `LeanModels/Cpp` tests and svgolf tasks changed) and a `lake build` of the
`comb_case`, `comb_word` and `comb_proc` modules, all of them build (0 failures), and the dumps taken afterwards are identical to the WP-COV ones: 23 of the 24 from
the rebuilt oleans, `ref_add_proc` from the staged build of a fresh `check.py` run (the old stage directory was the stale one). The `PStmt.forLoop` arm is
the intended one and has nothing to do with these designs. The lesson for any measurement here: `lake build` the examples before a `lake env lean` run over them.

**Follow-up (2026-11-02): the cover of a body of several windows, and a regression example.**
* `CoverOblM` is grouped like `CoverObl` (above). On a synthetic 13-site design of multi-target `always_comb` bodies (`x_i = x_{i-1} ^ y_{i-1}; y_i = x_{i-1} & a;`),
  `sv_equations` costs 398 335 thousand heartbeats on the tip tactics, with the cover goals in the site-witness form (66 558 lines of output), and 254 647 with
  the grouped cover (49 lines; the cover alone 79 995). The tip's `sv_structure` on the same design costs 328 912, ours 284 714: the structure of a multi-window
  design only gains the pair listing, because the GUARDED conjuncts (the further windows of `DisjObl`: every site against every further window; of `RankObl'`: every
  further window against every read) are still stated over all sites and stay quadratic (13 sites: `driverDisjoint` 75 540, `rankDecreases` 133 372 with no related pair
  at all). Grouping them by the name of the further window is the same lemma shape (`more` names instead of `tgt` names); not done.
* `set_option sv_comb.group_report true` makes `sv_structure` / `sv_equations` say, per obligation, how large the list was that the obligation was restricted to
  (`sv_comb group: DisjObl, 4 same-signal pairs of 9 sites`, `RankObl', 17 reads with 14 writers of 9 sites`, `CoverObl, ...`, `CoverOblM, ...`); a design that took
  the original route says nothing. The messages are deterministic.
* The regression example is `Examples/system-verilog/comb_lin/` (`lin_chain.sv`: nine plain sites at symbolic widths, two windows per vector; `chain.lean`).
  `lin_struct` (structure and rank, `CombDesign ∧ Acyclic`), `lin_settled` (`sv_equations` with every obligation closed) and `pm_settled` (`add_proc_m`, the multi-window
  cover) run with `group_report` and PIN its messages with `#guard_msgs`, at the default heartbeats (the whole file builds in about 15 s). The tactic falls back to the original
  route on any failure of the listing, and the proofs then still go through; the pinned messages are what fail when a grouping lemma, or the way the tactic applies it,
  drifts (a lemma whose statement the tactic's hand-built application no longer matches gives a kernel error or an unprovable goal as well).
