# WP-G, G2.2: the proc-aware layer (additive), the contestant's statement shape, and the list of copies

Status: DONE for the first fragment (worktree branch `wpg-g22`, from 415c27ce): R2 (`Summary.soundL`), R3
(`driversOk_of_lowered`, the structure theorem), R4 (`eq_of_summaryL`), R5 (`CombProcTactic.lean`), the
`Examples/system-verilog/comb_proc` fixture and `tasks/add/reference/add_proc.{sv,lean}`, accepted by `check.py`. This
note was written BEFORE the tactic layer, as the lead asked; sections 1 and 2 are the contract (one change, below),
section 3 lists the copies, section 4 the as-built facts.

## 0. Why the layer is parallel (additive) and not an edit of the summary

Adding the `alwaysComb` arm to the existing `CombView.siteOf?` makes `pairs_desc`, `Summary.sound`,
`comb_of_summary`, `acyclic_of_summary`, `acyclic_of_lex`, `sound_pairs`, `eq_of_summary` and `eq_view` FALSE for a
summary with a proc site (their conclusion says every process of the instantiated design is an `assign`). Giving them
a hypothesis `hnp : no proc site` would change statements that Examples proofs (`ripple_add`, `mul_array`, `lp_add`)
and the migrated references call with their current signatures. So the old chain is untouched and a parallel chain
handles proc summaries; for assign-only designs nothing changes, by construction.

## 1. What the contestant types

`name.sem N` of a design with an `always_comb` contains the (guarded) procedural process, so
`CombDesign (design.sem N)` is FALSE for it (`CombDesign.assign`: every process is an `assign`). What is true, and
what the settle theory transfers to the design along `Runs2.lowerComb_iff` (`Comb2Proc.lean`), is a statement about
the LOWERED design `d'` (`Design2.lowerComb`: each `always_comb` body replaced by the one continuous assign
`assign {w₀,…} = {E₀,…}` it computes; assign processes kept).

**The only change in the contestant's text is the statement of the structure theorem and one extra hypothesis name
in the next two steps.** For an assign-only design (`add_n`, today):

```lean
theorem add_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (design.sem N) ∧ Acyclic (design.sem N) := by
  sv_structure (rank := …)
  all_goals (intros; omega)
theorem add_interface (N) (hN) (hc : CombDesign (design.sem N)) : Task.Interface N (design.sem N) := by sv_interface
theorem solution : Goal := by
  intro N hN
  obtain ⟨hc, ha⟩ := add_struct N hN
  refine CombTask.satisfiedAt_of_comb (add_interface N hN hc) hc ha ?_
  intro st heqs hs v hv  …
  sv_equations
```

For a design with `always_comb` (`add_proc`):

```lean
theorem add_struct (N : Nat) (hN : 1 ≤ N) :
    ∃ d', (design.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := …)            -- same tactic name, same rank syntax, same closers
  all_goals (intros; omega)           -- the same obligations, plus noSelfRead_k (omega)
theorem add_interface (N) (hN) {d'} (hl : (design.sem N).lowerComb = some d') :
    Task.Interface N (design.sem N) := by sv_interface   -- hc is not needed (see section 4)
theorem solution : Goal := by
  intro N hN
  obtain ⟨d', hl, hc, ha⟩ := add_struct N hN
  refine satisfiedAt_of_lowered (add_interface N hN hl) hl hc ha ?_    -- one local lemma, below
  intro st heqs hs v hv             -- heqs : CombEqs d' st, hs : StateShape d' st
  …
  sv_equations                       -- finds hl, hc, ha, heqs, hs by type
```

* **The bundle is about `d'`, the lowered design**, obtained by the existential; `sv_structure` supplies the
  witness itself (the new soundness theorem `Summary.soundL` returns it) — the contestant never names `d'`
  except in the `obtain`.
* **`Submission.Goal` / `CombTask.Statement` is untouched** and is about `design.sem N`. The bridge from the
  lowered design to it is the local lemma (ten lines, `Comb2Proc.lean`'s theorems, modelled on
  `SvGolf.CombTask.satisfiedAt_of_comb`):
  `satisfiedAt_of_lowered (hI : t.Interface N d) (hl : d.lowerComb = some d') (hd' : CombDesign d')
  (ha' : Acyclic d') (hset : ∀ st, CombEqs d' st → StateShape d' st → ∀ v, HoldAll st (t.inputs N) v → HoldAll st
  (t.outputs N) (t.fn N v)) : t.SatisfiedAt N d` — `Unclocked` from `Design2.lowerComb_phases`, `Terminates2` from
  `Terminates2.of_lowerComb_acyclic`, `Computes` from `Models2.of_combProc_inputs`. It is stated and proved in the
  `add_proc` reference first (lead's ruling); promotion to `CombLib`/`SvGolf` only after the reference works.
* **The tactic entry points are the same names**: `sv_structure`, `sv_interface`, `sv_equations`, `sv_cover`,
  `sv_structure?`, `sv_equations?`. They dispatch on the goal: `CombDesign X ∧ Acyclic X` (or either alone) keeps
  today's elaborators and output; `∃ d', X.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'` runs the proc-aware
  layer. A contestant needs one extra import line, `import LeanModels.Sv.CombProcTactic` (the tactic module is
  new; the allowlist already admits `LeanModels.Sv.*`).
* **Equation names** keep the Gate-1 rule: `eq_<signal>_<k>` with `k` the ordinal of the EQUATION among those writing
  the signal (one per written window of a body), generated names `eq_<signal>_<block>_<pos>`; `add_proc` has the
  same aliases as `add_n`. The new obligation tag is `noSelfRead_k` (closed by `intros; omega`).
* **What a refused body looks like**: a tactic error whose first line is the planned message, e.g.
  ``sv_structure: outside the supported fragment — site `g_bit#1`: always_comb writes more than one window (…)``,
  never an elaboration error of the kernel (the checker's `--tactics` advisory reports it as `in_fragment false`).

## 2. What the contestant does NOT get yet

Multi-statement bodies (default-then-override, temporaries), `case`, and `?:`/`!`/`~` in bodies (S1b, S2, S3 of the
Gate-1 note). They are refused with a tactic message; by-hand proofs remain possible with the same bridge lemma.

## 3. The pieces, and which are COPIES of the old chain (for a later mechanical consolidation)

The consolidation the lead described (one `siteOf?` with the proc arm, `hnp` removed from the old theorems) becomes a
refactor: delete the copies, add the arm, and replace each copy by the old theorem plus one case. `[C]` = generated
copy (the old text with `siteOf?`→`siteOfP?` and friends; same proofs), `[M]` = copy with a proc case added by hand,
`[N]` = new.

| new declaration (file) | old original | kind |
|---|---|---|
| `siteOfP?`, `siteOfP?_proc`, `siteOfP?_cases` (`CombProcSummary.lean`) | `siteOf?`, `siteOf?_proc`, `siteOf?_cases` (CombView/CombViewThm) | [M]: the old arm text + the proc arm |
| `sitesOfP?`, `itemOfP?`, `itemsOfP?`, `famOfP?`, `famsOfP?`, `PDesign.summaryP` | same names without `P` (CombView) | [C] |
| `sitesOfP?_spec` … `famsOfP?_spec`, `Summary.SpecOkP`, `summaryP_spec`, `lsitesP_spec` | `sitesOf?_spec` … `summary_spec`, `lsites_spec` (CombViewSound) | [C] |
| `fams_expand2P` (`CombProcLower.lean`) | `fams_expand2` (CombViewSound) | [C]: `SpecOk` -> `SpecOkP` (only the `Wf` half is read) |
| `pairs_descL` (`CombProcLower.lean`) | `pairs_desc` (CombViewSound) | [M]: old-site branch verbatim, proc branch = `lower_site` + `proc_site_eq` |
| `Summary.soundL` | `Summary.sound` (CombViewSound) | [M]: first half verbatim, then the lowering step (`lowerProcs_map`) |
| `DescL`, `RealizedL`, `descL_facts`, `realizedL_comb`, `realizedL_acyclic` | `Desc`, `Realized`, (the `hdesc` uses of) `realized_comb`, `realized_acyclic` (CombViewMain) | [M]: the proofs are the old ones with `descL_facts` for `hdesc` |
| `LowKind`, `LowRel`, `proc_site_eq`, `windows_concat_win`, `RdOK.ifGuard/ternary/mono`, `low_rdOK`, `lowP`, `lowerProcs_map` | none | [N] |
| `driversOk_of_lowered`, `PDesign.instantiateGD2_of_lowered` | `driversOk_of_combDesign`, `instantiateGD2_of_combDesign` (Hier2Gen) | [N]: same clauses, procedural windows read off `drvWins_tree` |
| `comb_of_summaryL`, `struct_of_summaryL`, `struct_of_rankL`, `struct_of_lexL` | `comb_of_summary`, `acyclic_of_summary`, `acyclic_of_lex` (CombViewMain) | [M]: one theorem gives `CombDesign d' ∧ Acyclic d'` for the SAME `d'` |
| `eq_of_summaryL`, `eq_viewL`, `EqSiteL`, `PSk` | `eq_of_summary`, `eq_view`, `EqSite`, `Sk` (CombEqThm, CombEqBase) | [M]: new skeleton constructor `ite` |
| `CombProcTactic.lean` | `CombViewTactic.lean`, `CombEqTactic.lean` | [M]: new `elab_rules` that fall through |

(The table is filled in as the files land; the remaining rows are the plan.)

## 4. As built (2026-10-31)

* **Contract change**: `add_interface` takes `hl` only. The ports of `design.sem N` are the summary's declarations; that
  needs "the instantiation succeeded and lowers" (`declsL_of_lowerable`), not the comb profile of `d'`.
* **Files** (lines incl. pins): `CombProcSummary.lean` 335+, `CombProcLower.lean` ~890, `CombProcEq.lean` ~1000,
  `CombProcTactic.lean` ~810; every theorem has an axiom pin (propext, Classical.choice, Quot.sound at most).
  No existing file is edited; the tests and docs touched are `svgolf/tasks/add/{task.json,README.md,reference/add_proc.*}`,
  `svgolf/tests/{expected.json,run.py,add/validate/validate.py,add/negative/add_proc_case.*}`, `svgolf/PROVING.md`,
  `svgolf/README.md`, `docs/sv-refusals.{json,md}`, `svgolf/REFUSALS.md`.
* **The tactic layer is a second elaborator per syntax node** (`@[tactic svStructure]` etc., tried first; it throws
  `unsupportedSyntax` before deciding anything unless the goal or context has the lowered shape, so every existing proof
  elaborates as before: the goal dumps of `add_n`, `mul_n`, `mul_tree`, `mul_tree_h`, `mul_wallace` are byte-identical with
  and without `import LeanModels.Sv.CombProcTactic`, modulo file path and the shifted line of one warning).
* **Framework fact worth keeping**: when the NEWEST elaborator of a syntax node fails with an error (or an abort), the
  framework restores the state and tries the next one, and reports the failure of the LAST one tried, i.e. the OLD
  elaborator's generic message. So a new elaborator that has recognized its goal must not throw: `guardL` logs the error
  and admits the goal (`sorryAx`; the file does not compile). `tests/add/negative/add_proc_case` pins that check.py rejects
  such a proof at the `solution` stage, and `Examples/system-verilog/comb_proc/comb_errors.lean` pins the `sorryAx`.
* **Not done / known gaps**: `check.py --tactics` probes the assign-only shape, so it reports `in_fragment: false` for
  `add_proc.sv` (check.py was not touched; the probe should try the lowered shape when the old one refuses); S1b/S2/S3
  (multi-window bodies, `?:` `!` `~` in bodies, default-then-override and temporaries) are not implemented, so
  `mux_carry` keeps its expectation; the consolidation of the copies (section 3) is deliberately not done.

