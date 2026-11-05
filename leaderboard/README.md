# svGolf leaderboard

One JSON **record** per accepted submission, the **Pareto frontier** over the
ranked score (the sky130 A0' area in um^2 and time in ps, decided 11/03; area in
GE and depth are extra columns), ranked **boards**, and a **verification** that
re-derives what a record claims. Everything is `leaderboard.py` (Python 3, standard library
only; it runs `check.py` and `score/score.py` as subprocesses). The short
version, with the rules of the game, is in [../README.md](../README.md),
"Leaderboard".

```
leaderboard/
  leaderboard.py                  the CLI and the library (pure functions + thin commands)
  README.md                       this file
  data/<task>/<record_hash>.json  the record
  data/<task>/<record_hash>.sv    the submitted design, byte for byte
  data/<task>/<record_hash>.lean  the submitted proof, byte for byte
tests/leaderboard/                unit tests (synthetic check results; no Lean, no Yosys)
```

## Commands

```bash
# record a submission: runs check.py on it and REFUSES unless it is accepted
python3 leaderboard/leaderboard.py add --task add --player alice \
    --assisted-by "Claude (Anthropic)" --assisted-by "a proof assistant" \
    --sv my_adder.sv --lean MyAdder.lean --notes "Sklansky prefix tree"

python3 leaderboard/leaderboard.py add ... --from-check RESULT.json   # use a stored check.py result instead
python3 leaderboard/leaderboard.py add ... --postsynth light          # a LIGHT record (local; marked), see below
python3 leaderboard/leaderboard.py verify [--task T] [--offline | --full]
python3 leaderboard/leaderboard.py pareto --task T [--format text|json] [--unassisted]
python3 leaderboard/leaderboard.py pareto --task T --axes area_mge,depth   # opt-in: n-D frontier over chosen columns (here GE)
python3 leaderboard/leaderboard.py pareto --task T --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1   # ... of flow A1' (mapped)
python3 leaderboard/leaderboard.py board  --task T [--format md|json] [--unassisted] [--all-flows]
python3 leaderboard/leaderboard.py export --out LEADERBOARD.md        # every task
python3 leaderboard/leaderboard.py seed-references [--task T [--ref STEM ...]]   # the proved references
```

`add` takes `--date YYYY-MM-DD` (default: today, UTC; this is the only place
the clock is read), `--require-clean` (refuse if the svgolf or lean-surfaces
revision is unknown or `+dirty`), `--lean-wrap CMD` (else `$SVGOLF_LEAN_WRAP`,
which `check.py` reads itself), `--data-dir DIR`. Exit status: 0 success, 1
refused or verification failed, 2 usage or infrastructure error (an
infrastructure error of `check.py` is never a verdict and never a record).
As for `check.py`, set `SVGOLF_PYTHON` to choose the `python3.12` that runs
it; the leaderboard itself runs on any Python 3.9+.

**Official records are full.** `add` runs `check.py` with `--ppa require --postsynth full` (its
post-synthesis check on the task's whole vector budget; `check.py`'s own default is
the lighter `light` mode, a deterministic subset for local feedback), `verify --full`
re-runs it the same way, and `seed-references` records in full mode. `--ppa require` (WP-X3)
is the sky130 columns of `score/ppa.py` (see "The sky130 PPA columns" below): the pinned liberty
must be present (and readable), else `check.py` answers with an infrastructure error (exit status 2) and a
live `add` writes nothing; a light record (`add --postsynth light`) asks for the columns too. `add --from-check RESULT.json`
records a STORED result and so cannot ask: a result made by `--ppa require` is recorded as it is (with the columns, or
with `{"available": false, "reason"}` for a design the pinned flow could not weigh); a result made by `--ppa auto` that
found no liberty is REFUSED (its `ppa` says `available: false` and the run was not `require`: an official record is never
the record of a missing file); and a result with NO `ppa` key (`--ppa off`, or a checker from before the columns) is
recorded WITHOUT the columns, which `add` says in a NOTE (such a record is "not shown" by `pareto --axes`). A check result
whose `stages.postsynth.mode` is `light` (a `--from-check` file made with the
default) is REFUSED unless `add --postsynth light` asks for a light record; a result
without a `mode` was made by a checker that had only the full check and reads as full.
A light record is a legitimate local record: it is marked (`postsynth.mode:
"light"`), `add` prints a NOTE saying so, `board` and `pareto` show it (`light` after
the record hash, `[light post-synthesis check]` in the text listing, a footnote under
the table, `postsynth` in the JSON rows), and `verify` notes it (`verify --full`
rechecks it in full mode). Whether a public board takes light records is the
hand-off policy, not decided here: the leaderboard only carries the field.

`add` reads the two files once, hands `check.py` a snapshot of exactly those
bytes, hashes the same bytes into the record and stores them: the files in
`data/` are the files that were checked. It refuses a submission that
`check.py` did not accept (any stage), a result about another task, scored
anywhere but at the task's scoring point, ungated, without a passing
`postsynth` record, with an axiom outside the task's allowed set, over the
task's `scoring.depth_budget`, a duplicate (same player, same two files), and
a run during which the checker's own files changed (their sha256 are read
before and after). With `--from-check`, the result must additionally be about
this very `.sv` (`stages.source.sha256` equals the sha256 of the file); it
cannot be bound to the `.lean` (check.py's result does not carry its hash), so
a competition host runs `add` without `--from-check`.

Real output (the proved references re-seeded on 2026-11-04 under `sky130_a0_v3` with its per-edge pin loads, the same
design and proof files as the records of 10-29, which had no sky130 columns, and `clmul_n`; the five `check.py` runs took
90 s for the two `_example` ones together, then 44 s, 1 min 52 s and 1 min 9 s, in one Lean slot acquisition):

```
$ python3 leaderboard/leaderboard.py seed-references --task add --ref add_n_byhand
seeded add: reference/add_n_byhand.sv -> leaderboard/data/add/ec8d54a21973397139413b0d328cb5bc1891c59ec09e793857a67f4e20a3385a.json
$ python3 leaderboard/leaderboard.py pareto --task mul
mul: Pareto frontier of (sky130 area, time) at N=16 (1 of 1 ranked records)
  area um^2 time ps  area GE depth  player               record        assisted by
  8290.4512   10907 1962.576    88  svgolf-reference     1b6a6bf23908  Claude (Anthropic)
$ python3 leaderboard/leaderboard.py verify
[ok] _example/35d6541e6ab1: svgolf-reference 100.0960 um^2, 280 ps (21.328 GE, depth 1): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] _example/732b207a5f97: svgolf-reference 100.0960 um^2, 280 ps (21.328 GE, depth 1): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] add/ec8d54a21973: svgolf-reference 460.4416 um^2, 2611 ps (112.000 GE, depth 33): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] clmul/e60572825e9d: svgolf-reference 3429.5392 um^2, 1114 ps (772.267 GE, depth 6): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] mul/1b6a6bf23908: svgolf-reference 8290.4512 um^2, 10907 ps (1962.576 GE, depth 88): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
verify (hashes + rescore): 5 records, 0 failed, 0 stale
$ python3 leaderboard/leaderboard.py board --task add
```

| # | layer | player | assisted by | area (um^2) | time (ps) | area (GE) | depth | proof lines | date | record |
|--:|--:|---|---|--:|--:|--:|--:|--:|---|---|
| 1 | 1 | svgolf-reference | Claude (Anthropic) | 460.4416 | 2611 | 112.000 | 33 | 509 | 2026-11-05 | `ec8d54a21973` |

## The record (schema `svgolf-leaderboard-record/1`)

`record_hash` is the sha256 of the record's **canonical JSON** (sorted keys,
no whitespace, ASCII-only, no NaN) with `record_hash` itself removed. The
record's file name is its hash. Unknown or missing top-level keys are
errors, except the one OPTIONAL key `ppa` (below). A different schema is a different `schema` string, never a
silent change; the optional keys are the exception that proves it, additive and
READER-FORWARD ONLY: a record that carries `ppa` (or `postsynth.mode`) is
invalid to a `leaderboard.py` from before that key, which skips it with one stderr line per record
(`not an intact record`), so update every reader before the first such record is shared.
(Floats, `area_ge`, `build_seconds` and, when the record has `ppa`, `ppa.area_um2_sky130`, are hashed as Python's
shortest round-trip text, which another implementation has to reproduce.)

| key | meaning |
|---|---|
| `schema` | `"svgolf-leaderboard-record/1"` |
| `task` | the task name (the directory under `tasks/`) |
| `player` | handle, `[A-Za-z0-9][A-Za-z0-9._-]{0,31}` |
| `assisted_by` | list of strings, free text, may be empty: the tools and AI systems that helped write the design or the proof (see "assisted_by") |
| `submitted_at` | ISO date `YYYY-MM-DD` (or `YYYY-MM-DDTHH:MM:SSZ`); passed in, never read by a pure function |
| `files` | `{sv: {name, sha256}, lean: {name, sha256}}`: base names as submitted, sha256 of the exact bytes (also the content of the stored copies) |
| `canonical_sha256` | sha256 of the source gate's canonical text (`stages.source.canonical_sha256`): what the extractor, the banlist and Yosys all read |
| `score` | the extra GE columns: `area_mge` (integer milli-GE, the exact value), `area_ge` (= `area_mge / 1000`), `depth`, `num_gates`, `gates` (count per gate type), `top`, `scoring_point` (the parameter values, e.g. `{"N": 16}`), `rtlil_sha256` (the canonical RTLIL: equal RTLIL, equal score); for a CLOCKED result also check.py's clocked ranked score `area_um2`, `period_ps`, `cycles`, `time_ps` (= `cycles` x `period_ps`, the time the boards rank) and `ffs`, checked against the `ppa` block (`period_ps` its `delay_ps_sky130`, `area_um2` its `area_um2_sky130`) |
| `checker` | who judged: `svgolf_revision` (git HEAD of the svgolf checkout, `+dirty` if the trusted base has uncommitted changes: `check.py`, `check/`, `score/`, `SvGolf/`, the lake files, the tasks' `Spec.lean`, `IEEE754.lean` and `task.json`; read before the check ran), `lean_surfaces_revision` (as `check.py` records it, `+dirty` if `LeanModels/Sv` or `extractors/sv` has uncommitted changes), `lean_toolchain` (the `lean-toolchain` file), `yosys` (version line), `verilator` (version line), `extractor_sha256` (the extractor program: `extract.py` alone for a checkout from before `lower_proc.py`, else the digest of both files, `check/envelope.py` `extractor_sha256`), `canon_script_sha256`, `script_sha256`, `ge_table_sha256` (the pinned flow), `files` (sha256 of the checker's own files: `check.py`, `check/*`, `score/*`, `lean-toolchain`, `lakefile.toml`) |
| `proof` | `axioms` (sorted; from the comparator, walked through kernel values), `build_seconds` (compiling `Solution.lean` only), `lines` (code lines: blank lines and comments, including doc comments and nested block comments, stripped; `import` lines count), `imports`, `tactics` (the watched tactics found in the code: `sv_*` tactics, `omega`, `grind`, `decide`, `induction`, `simp`, `bv_decide`, `native_decide`; lexical, not a claim about the proof term), `uses_comb_view` / `uses_comb_eq` (the proof imports `LeanModels.Sv.CombView*` / `CombEq*`) |
| `ppa` | OPTIONAL (absent in every record made before the sky130 columns, which stay valid; hashed when present; the schema string is unchanged: additive, like `postsynth.mode`). check.py's `ppa` object of the run: `available: true`, `ppa_version`, `area_um2_sky130` (= `area_e4um2_sky130` / 10^4), `area_e4um2_sky130` (integer, 1e-4 um^2), `delay_ps_sky130` (integer ps), `unit_depth` (= `score.depth`, checked), `cells_sky130` (= `score.num_gates`, plus 1 if `constants`: the priced tie cell; checked, and equal to the sum of `cell_hist_sky130`), `cell_hist_sky130`, `constants`, `critical`, `setup`, `liberty_file`, and the hashes `liberty_sha256`, `ppa_pins_sha256`, `ppa_script_sha256`, `netlist_sha256`, and (WP-X4) the optional sub-object `mapped` (flow A1': `{"available": true, ...}` with `ppa_mapped_version`, `area_um2_sky130_mapped_v1` (= `area_e4um2_sky130_mapped_v1` / 10^4), `area_e4um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1` (= the sum of `mapped_cell_hist_sky130_v1`), `mapped_levels_sky130_v1`, `mapped_buffers_sky130_v1`, `mapped_inverters_sky130_v1`, `equivalence`, the hashes and the Yosys/ABC builds; its `rtlil_sha256` must be the record's `score.rtlil_sha256`; or `{"available": false, "reason": "..."}` for a design the mapping could not weigh; an old reader accepts the key, extra keys of `ppa` are allowed); or `{"available": false, "reason": "..."}` for a design the pinned flow could not weigh (recorded only from a `--ppa require` run: under `auto` a missing liberty would look the same). THE RANKED SCORE: the boards rank `area_e4um2_sky130` and the time (`delay_ps_sky130`; a clocked record's `score.time_ps`); a record without the key, or with an unavailable one, is not ranked |
| `postsynth` | the post-synthesis check that passed: `point`, `vectors` (those the run used), `mismatches` (0), `salted` (whether `$SVGOLF_POSTSYNTH_SALT` was set), `seed`, `mode` (`"full"` or `"light"`; absent in records made before the modes existed, which read as full) and `full_vectors` (what the full mode would have used; equal to `vectors` for a full record; absent in those same records). Additive: the schema is unchanged |
| `notes` | free text (at most 2000 characters) |
| `record_hash` | as above |

A real record is `data/_example/*.json` (every key above except the optional `ppa`, which that file predates, and nothing else).

## The sky130 PPA columns (WP-X3, WP-X4): the ranked score

The boards rank flow A0' (decided 11/03): a record made since the wiring carries the columns `score/ppa.py` computes on
the scored netlist (flow A0': area in um^2, delay in ps; units and what is NOT claimed in
[../score/PPA.md](../score/PPA.md) and the README's "Scoring"), and `pareto`, `board` and `export` rank their area and time
(`RANKED_AXES`: `area_um2_sky130`, `time_ps`), with the GE area and depth as extra columns; since WP-X4 the record also
carries the sub-object `ppa.mapped` (flow A1': the same design's canonical RTLIL mapped by a real `abc -liberty` run,
weighed by the same STA), an unranked research column. A record is ranked only when its columns are comparable with the
ones weighed now (`unranked_reason`: the task's scoring point, the current flow, the current `ppa_version`, liberty and
pins file, and the task's input drive); a record without them is not ranked until it is backfilled (checked again under
`--ppa require`). "Reproduce a score" in [../score/PPA.md](../score/PPA.md) re-derives every ranked number bit for bit.
Since 11/04 (`ppa_version` `sky130_a0_v2`) A0' is weighed on the netlist REPAIRED by buffering only (balanced buffer trees
on every net over its driver's limits, replicated tie cells, nothing resized; the record's `ppa.repair` counts them, and
`cells_sky130` = `cells_before` + `buffers` + `tie_cells`), and `check.py` rejects a design the repair cannot make
electrically legal, so such a design never reaches a record (score/PPA.md, "The repair and the legality check"); since
`sky130_a0_v3` every primary input is driven by the task's input drive (default `sky130_fd_sc_hd__buf_8`), which the
record's `ppa.setup.input_drive` names and the record hash covers (score/PPA.md, "The input drive"; "Reproduce a score"
re-derives a record's numbers bit for bit). `pareto` has an opt-in view over any of the columns:

```bash
python3 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130,time_ps     # the board's frontier
python3 leaderboard/leaderboard.py pareto --task add --axes area_mge,depth              # the GE frontier, an extra view
python3 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1
python3 leaderboard/leaderboard.py pareto --task aes_sbox --axes area_um2_sky130,delay_ps_sky130,depth --format json
```

The axes are `area_mge`, `depth` (the GE columns), `area_um2_sky130`, `time_ps` (the board's: the delay, or a clocked
record's cycles x period), `delay_ps_sky130`, `unit_depth`, `cells_sky130` (flow A0'), and `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1`,
`mapped_levels_sky130_v1` (flow A1', mapped cell levels; axes of both flows may be mixed, each is read from its own flow); all "lower is better", all compared as exact integers (areas in 1e-4 um^2). In the JSON view each
row's `values` are keyed by the RECORD FIELD the number was read from, so the unit is in the name
(`"values": {"area_e4um2_sky130": 4604416, "delay_ps_sky130": 2611}` for the axes `area_um2_sky130,delay_ps_sky130`:
the area is the integer in 1e-4 um^2, 460.4416 um^2), and `axis_fields` maps each axis to its field; the text view prints um^2. The
frontier is the n-dimensional one, by the same rule as the default (no other record is at least as good on every
axis and strictly better on one; ties are kept) and in the same deterministic order. A record is listed under
"not shown" with the reason when it lacks a column (made before them, or its design could not be weighed), was
checked under another flow or scored at another point (as for the board; `--all-flows` shows them), or its columns
were computed under another `ppa_version`, liberty or pins file than the current `score/ppa_pins.json`, or (A0' axes) under another
input drive than the task's now (`ppa.setup.input_drive` against `task.json` `input_drive`, else the pins' default: a task
field, outside the pins file, so a task that changes it never has its old and new records ranked together) (for the mapped axes:
another `ppa_mapped_version`, liberty, `score/ppa_mapped_pins.json` or `score/ppa_mapped.ys`; the Yosys and ABC builds are part
of the flow check; a record whose design the mapping could not weigh, or that was made before WP-X4, has no mapped columns). The output
carries no noise band: differences under about 10% in area and 20% in delay are mapper noise (README, "Scoring"),
and what a board does with that is a policy decision. Without `--axes`, `pareto` prints the board's frontier.

## Policy

**Ranking is the Pareto frontier of the sky130 A0' area and time** (decided
11/03). Both axes are "lower is better" and both are exact integers: the area
`ppa.area_e4um2_sky130` in 1e-4 um^2, the time in ps (`ppa.delay_ps_sky130`
for a combinational record, `score.time_ps` = cycles x period for a clocked
one). A record is on the frontier iff no other record is at least as good on
both axes and strictly better on one: **equal scores do not dominate each
other, ties are kept**. Every listing uses one total order, so it is the same
on every machine: area, then time, then the earlier `submitted_at` first (on
a tie in both, the earlier record stands), then player, then record hash. The
GE area and depth are shown beside them and rank nothing. The board shows the frontier first (layer 1), then the dominated
records by layer (layer 2 is the frontier of what is left, and so on). A
player's old, dominated submissions stay on the board as dominated entries;
records are append-only and never edited.

**There is no depth budget by default.** A task author may add one of two:

* `leaderboard.depth_budget` in `task.json` (positive integer, absent or
  `null` = none): a **ranking-only** budget on the unit depth. The board then
  also ranks "best area under the depth budget" (records within the budget,
  ordered by sky130 area then time, ties sharing a rank: 1, 1, 3), and lists the records over it
  after those, flagged `over budget`. The frontier is not changed by it; its
  rows carry an `over`/`ok` flag. Nothing is rejected.
* `scoring.depth_budget` (already in `task.json`): the checker's **hard**
  budget, a depth over it rejects the submission at the `score` stage, so a
  fresh record is always within it. The board uses it for the same ranking,
  so records made before the budget was set or lowered are flagged.

With both, the smaller one ranks. The value for `mul` is an open question
(PLAN.md); no task has a budget today.

**Scores are comparable exactly when the flow, the point, the sky130 pins and
the input drive agree.** The board ranks only records whose `canon_script_sha256`,
`script_sha256`, `ge_table_sha256` and `yosys` equal the current pinned flow,
whose `scoring_point` is the task's current one, and whose `ppa` block is
numeric, of the current `ppa_version`, liberty and pins file
(`ppa_identity`), and weighed under the task's input drive now
(`ppa_setup_now`); the others are listed under "Not ranked" with the reason
(a record without sky130 columns: until it is backfilled), until the same files are submitted again (`add
--sv data/<task>/<hash>.sv --lean data/<task>/<hash>.lean ...` makes a new
record under the new flow; the stale one stays as history). `--all-flows`
ranks every record that carries sky130 columns (nothing is compared: flow,
pins or drive). A bump of the flow or of lean-surfaces therefore re-checks
the leaderboard: the stale list is the to-do list.

**`assisted_by`** names the tools and AI systems that helped write the design
or the proof: a model and version, a prover service, a search script ("Claude
Opus 4.1 (design)", "a prover service (proof)", "ABC scripts"). Free text,
stripped, duplicates dropped, order kept; an empty list is an unassisted
claim. It is **not verified** (nothing can verify it) and it does not split
the board: it is printed next to every entry, and `--unassisted` ranks only
the entries with an empty list. A host that wants separate tracks filters on
it; the format already carries what they need.

## Verification

`verify` re-checks stored records at three levels. It exits 1 if any record
fails; a record checked under another flow is `stale`, not a failure.

| level | what | cost |
|---|---|---|
| `--offline` | the record is well-formed; `record_hash` is the hash of its canonical JSON and its file name; both stored files exist with the recorded sha256; the area equals the sum of the gate weights of `score/ge.json` (when that is the recorded table); the axioms are within the task's allowed set; a `ppa` object agrees with the record's own score (unit depth, cell count, histogram, area arithmetic); a `ppa` object of the current `ppa_version`, liberty and pins names the timing setup the task's configuration gives now: its `setup.input_drive` another than the task's (`task.json` `input_drive`, else the pins' default) makes the record `stale`, not comparable and not ranked (the task changed its drive: the record is not wrong), and a `pi_slew_ps` or `po_load_ff` other than the pins file's is a failure. Also notes which checker files have changed since the record | milliseconds; no tools |
| default | `--offline`, plus a rescore: `score/score.py` on the stored design at the task's scoring point (source gate, then the two-stage Yosys flow): area, depth, gate mix, canonical text hash and canonical RTLIL hash must equal the record's. For a record with a `ppa` object the same single flow runs through `score/ppa.py` (its `score` is `score.py`'s result unchanged) and the columns must reproduce exactly (`area_e4um2_sky130`, `delay_ps_sky130`, `unit_depth`, `cells_sky130`, the histogram, `netlist_sha256`, the whole `setup`, and, when the record has `ppa.mapped`, the mapped area, delay, cells, histogram, levels and mapped netlist hash: the same flow also maps once, +0.3 to 1.4 s); without the pinned liberty on the verifying machine, or when the record was weighed under another `ppa_version`/liberty/pins, that comparison is a NOTE, never a failure; weighed under another input drive than the fresh weighing's (the task's now), the record is `stale` and its A0' columns are not compared (a record that claims a drive its numbers were not weighed under is therefore never "reproduced": stale under the task's drive, a failure once the task's drive is the claimed one) | one Yosys run per record (7 s for the five seeded records, the `mul` one and the sky130 columns and the A1' mapping of each included, 11/04); no Lean, no Verilator |
| `--full` | `check.py --ppa require` again on the stored `.sv` and `.lean`, every stage: it must accept, with the same canonical text and axioms, and (same flow) the same score and (same flow, `ppa_version`, liberty, pins) the same `ppa` columns; the pinned liberty must be present. Under another flow (Yosys or script hashes differ) the record is `stale` and neither the score nor the columns are compared: the netlist, its area and its hash legitimately differ. A record made before the columns has nothing to reproduce: it is rechecked with `--ppa off` and never needs the liberty | the cost of the original check (10 to 90 s per record on a free Lean slot, plus waiting for it; hours for a large board) |

`check.py` has no "cheap stages only" flag (`--unproved` still builds the
generated design module with Lean), which is why the default level calls
`score.py` itself. The postsynth check is part of `--full` only.

What a record is worth: it is **tamper-evident, not tamper-proof**. Editing a
record, or a stored file, breaks `verify --offline`. Someone who also
recomputes `record_hash` and renames the file passes `--offline`; the default
level catches a changed score and `--full` an invalid proof or a changed
axiom set; the git history is the ledger. The boards skip a record that is
not intact (hash, name, shape) and say so. `submitted_at`, `player`,
`assisted_by` and `notes` are the submitter's word.

## Records in the tree

`data/` holds five proved references (`_example` `band` and `band_lp`,
`add_n_byhand`, `mul_n_byhand`, `clmul_n`) as player `svgolf-reference`,
`assisted_by` `["Claude (Anthropic)"]`, notes `reference solution`, each from
a real `check.py --ppa require` run (their stored files are byte-identical to
`tasks/*/reference/` at the time). They were re-seeded on 11/04 under
`sky130_a0_v3`, so they carry the ranked sky130 columns: the first four
replace the records of 10-29 (the same design and proof files; made before the
columns, they would have been "not ranked"; the git history keeps them), and
`clmul_n` is new. `seed-references` does it for every `ready` task (`--task T
--ref STEM` for one reference): it runs `check.py` on each reference that is
not already recorded (same player, same two files), so after a reference
changes it adds a new record for the new files and leaves the old one; with
nothing changed it is instant. Baselines
are **not** records: a baseline is
scored but never accepted by `check.py` (no proof), so `add` refuses it. The
unscored reference points live in `tests/expected.json` (`baselines`) and in
the README's task table (Yosys's own `+` and `*`; the Sklansky, Kogge-Stone
and Dadda designs).

## Tests

`python3 tests/leaderboard/test_leaderboard.py` (also the `leaderboard` step
of `tests/run.py`, with `leaderboard.py verify --offline` on `data/`): the
ranked board (the sky130 area and time rank where GE says otherwise; records
without sky130 columns, of another PPA identity or under another input drive
are not ranked, with the reason; a clocked record's time is cycles x period,
held to its `ppa` block); record
round trip; `record_hash` canonicality and a pinned hash; tamper detection
(record, `.sv`, `.lean`, a hash recomputed without renaming, a forgery that is
fully consistent and is caught by the rescore); refusal of every kind of
rejected or mismatched check result; Pareto dominance, ties, determinism under
permutation, agreement with `score.py --pareto`; layers; the budget ranking;
stale flows and off-point records; `assisted_by`; the Markdown golden file
(`tests/leaderboard/golden_board.md`, rewritten with `UPDATE_GOLDEN=1`); the
`add` path against a fake `check.py`; the committed records' integrity; the `ppa` key (optional,
additive, validated against the record's own score, hashed; `add` and `verify --full` run `check.py --ppa
require`; an unavailable block only from a `require` run; a stored result without the key is recorded with a NOTE;
rescore and recheck compare the columns exactly under the same flow and degrade to a note without the liberty or
under another flow; the input drive: a record under another drive than the task's is stale and not shown, never failed,
and the review's two attack records, rebuilt from `tests/leaderboard/drive_records.json`, never pass as reproduced; the sub-object `ppa.mapped` of flow A1' likewise, under its own identity: version, script, pins, liberty,
Yosys and ABC builds) and the `pareto --axes` view (n-D dominance, ties, permutation
determinism, records without columns or under another version listed as not shown, `--axes area_um2_sky130,time_ps` is the default board's frontier, the mapped axes). The
tests inject the check and rescore results; none runs Lean or Yosys.
