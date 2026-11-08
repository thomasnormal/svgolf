# svGolf leaderboard

One JSON **record** per accepted submission, its **ranked number** (area x time:
the sky130 A0' area in um^2 times the time, in um2*ns, decided 2026-11-05;
`combined.py`), **boards** that list the records by it, lowest first, with the
Pareto layer of the area and the time beside it (an exploration column, like the
GE area and depth; `pareto` prints the frontier), and a
**verification** that re-derives what a record claims. Everything is `leaderboard.py` (Python 3, standard library
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
# record a submission: runs check.py on it and REFUSES unless it is accepted. It writes into
# leaderboard/data/<task>/, the directory a pull request adds; --data-dir DIR is for a private trial
python3.12 leaderboard/leaderboard.py add --task add --player YOUR_HANDLE \
    --assisted-by "TOOL OR MODEL" --sv solution.sv --lean Solution.lean --notes "Sklansky prefix tree"

python3.12 leaderboard/leaderboard.py add ... --from-check RESULT.json   # use a stored check.py result instead
python3.12 leaderboard/leaderboard.py add ... --postsynth light          # a LIGHT record (local; marked), see below
python3.12 leaderboard/leaderboard.py verify [--task T] [--offline | --full]
python3.12 leaderboard/leaderboard.py board  --task T [--format md|json] [--unassisted] [--all-flows]   # by area x time
python3.12 leaderboard/leaderboard.py export --out LEADERBOARD.md        # every task's board
python3.12 leaderboard/leaderboard.py pareto --task T [--format text|json] [--unassisted]   # exploration: the frontier
python3.12 leaderboard/leaderboard.py pareto --task T --axes area_mge,depth   # opt-in: n-D frontier over chosen columns (here GE)
python3.12 leaderboard/leaderboard.py pareto --task T --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1   # ... of flow A1' (mapped)
python3.12 leaderboard/leaderboard.py seed-references [--task T [--ref STEM ...]]   # the proved references
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
rechecks it in full mode). A light record NEVER RANKS (decided 2026-11-06: a light check is an incomplete
check, and an incomplete check establishes nothing): the boards list it under "Not ranked" with that reason,
whatever its score.

**The board's own data directory** (`leaderboard/data`, the default `--data-dir`) takes only a record whose
kernel check `add` ran itself, in the OS sandbox (decided 2026-11-06, the universal-correctness audit): there
`add` refuses `--from-check` and `--sandbox off`, and a live check whose result says the sandbox was not
active (`--sandbox auto` on a machine without a working mechanism). Both options stay available for a trial in
another `--data-dir`. Whatever the directory, `add` refuses a result `check.py` marks INCOMPLETE (`complete:
false`, the reasons in `incomplete`: `--no-score`, a light post-synthesis check unless `--postsynth light`
asks for a light record, `--no-trusted-build`, a `--time-limit` other than the task's), a result without
`stages.trusted` with exit 0, and a solution stage that did not run under the task's own CPU limit
(`stages.solution.time_limit_s`) or was stopped at a limit (`stopped_by`).

`add` reads the two files once, hands `check.py` a snapshot of exactly those
bytes, hashes the same bytes into the record and stores them: the files in
`data/` are the files that were checked. It refuses a submission that
`check.py` did not accept (any stage), a result about another task, scored
anywhere but at the task's scoring point, ungated, without a passing
`postsynth` record, with an axiom outside the task's allowed set, over the
task's `scoring.depth_budget`, a duplicate (same player, same two files), and
a run during which the checker's own files changed (their sha256 are read
before and after).

**A clocked task's record** (decided 2026-11-07, the clocked record format). For a task whose `kind` is one of
`CLOCKED_KINDS` (`seq-family`, `tx-family`, `stream-family`, `react-family`), acceptance requires the clocked flow's
result: `stages.score.flow` is `"seq"` (score/svgolf_seq.ys and ge_seq.json), the score is check.py's clocked one
(`area_um2`, `period_ps`, `cycles`, `time_ps`), and `stages.postsynth.points` holds EVERY point of the task (its
task.json `postsynth.points`, plus the scoring point if they do not list it), each once, of the task's kind, in full
mode (light only for `add --postsynth light`), with every seed the task asks for (task.json `postsynth.seeds`, else
check/postsynth.py's default 8, F5: seeds 0 to S-1), each seed with its cycles and its segments or transactions, 0
mismatches, its netlist's sha256 and the declared latency; `stages.postsynth.netlist_sha256` is the scoring point's
netlist, the one the `ppa` block weighed. A combinational task refuses a result of the clocked flow, and a clocked task
one of the combinational flow. With `--from-check`, the result must additionally be about
this very `.sv` (`stages.source.sha256` equals the sha256 of the file); it
cannot be bound to the `.lean` (check.py's result does not carry its hash), so
a competition host runs `add` without `--from-check`, and the board's own data
directory refuses it.

Real output (2026-11-05: ten proved references re-seeded from the same design and proof files after `check.py` and
`check/envelope.py` changed, one `check.py` run per Lean slot acquisition, from 66 s (`add_n_byhand`) to 5 min 18 s
(`fdivp_newton`); then `pareto` and `board` as they order since that day):

```
$ python3.12 leaderboard/leaderboard.py seed-references --task add --ref add_n_byhand
seeded add: reference/add_n_byhand.sv -> leaderboard/data/add/c3c7511d17e94c48df8fb16fb0385673b72bf0cdbe5cb2d803ccd099dfdce3e5.json
$ python3.12 leaderboard/leaderboard.py verify
[ok] _example/452e4ad868fd: svgolf-reference 100.0960 um^2, 280 ps (21.328 GE, depth 1): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] _example/a6b94132454f: svgolf-reference 100.0960 um^2, 280 ps (21.328 GE, depth 1): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] add/c3c7511d17e9: svgolf-reference 460.4416 um^2, 2611 ps (112.000 GE, depth 33): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] aes_sbox/b863f1c282ce: svgolf-reference 892.1056 um^2, 4297 ps (200.986 GE, depth 21): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] aes_sbox/c671f15e21c3: svgolf-reference 3445.8048 um^2, 2288 ps (786.894 GE, depth 11): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] clmul/6ce61496f878: svgolf-reference 3429.5392 um^2, 1114 ps (772.267 GE, depth 6): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] fdivp/9993e24c70ea: svgolf-reference 12356.8512 um^2, 27592 ps (2787.652 GE, depth 189): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] fdivp/a01cc92d4599: svgolf-reference 33824.9408 um^2, 40031 ps (7892.452 GE, depth 252): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] fdivp/d3c6b29f88e5: svgolf-reference 9675.5296 um^2, 37984 ps (2166.076 GE, depth 289): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] mul/4f925aec8e6e: svgolf-reference 8563.2128 um^2, 5992 ps (2025.905 GE, depth 62): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
[ok] mul/8cd856ed5b94: svgolf-reference 8290.4512 um^2, 10907 ps (1962.576 GE, depth 88): rescored: same score; ppa columns reproduced; ppa.mapped columns reproduced
verify (hashes + rescore): 11 records, 0 failed, 0 stale
$ python3.12 leaderboard/leaderboard.py pareto --task mul
mul: Pareto frontier of (sky130 area, time) at N=16 (2 of 2 ranked records), exploration: the board ranks area x time; # is the entry's rank there
  Par, the best proved reference by area x time (the ranked number; lower is better): `mul_tree_h`: 8563.2128 um^2 x 5992 ps = 51310.77 um2*ns (record `4f925aec8e6e`).
  # area x time um2*ns area um^2 time ps  area GE depth  player               record        assisted by
  2           90423.95 8290.4512   10907 1962.576    88  svgolf-reference     8cd856ed5b94  Claude (Anthropic)
  1           51310.77 8563.2128    5992 2025.905    62  svgolf-reference     4f925aec8e6e  Claude (Anthropic)
$ python3.12 leaderboard/leaderboard.py board --task mul
```

Both `mul` records are on the frontier (`mul_n_byhand` has the smaller area, `mul_tree_h` the shorter time); the board
ranks them by area x time:

| # | player | assisted by | area x time (um2*ns) | area (um^2) | time (ps) | layer | area (GE) | depth | proof lines | date | record |
|--:|---|---|--:|--:|--:|--:|--:|--:|--:|---|---|
| 1 | svgolf-reference | Claude (Anthropic) | 51310.77 | 8563.2128 | 5992 | 1 | 2025.905 | 62 | 307 | 2026-11-05 | `4f925aec8e6e` |
| 2 | svgolf-reference | Claude (Anthropic) | 90423.95 | 8290.4512 | 10907 | 1 | 1962.576 | 88 | 1385 | 2026-11-05 | `8cd856ed5b94` |

## The record (schema `svgolf-leaderboard-record/1`)

`record_hash` is the sha256 of the record's **canonical JSON** (sorted keys,
no whitespace, ASCII-only, no NaN) with `record_hash` itself removed. The
record's file name is its hash. Unknown or missing top-level keys are
errors, except the one OPTIONAL key `ppa` (below). A different schema is a different `schema` string, never a
silent change; the optional keys are the exception that proves it, additive and
READER-FORWARD ONLY: a record that carries `ppa` (or `postsynth.mode`) is
invalid to a `leaderboard.py` from before that key, and a clocked record (`checker.flow`, `postsynth.points`) to one
from before the clocked format (2026-11-07), which skips it with one stderr line per record
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
| `checker` | who judged: `svgolf_revision` (git HEAD of the svgolf checkout, `+dirty` if the trusted base has uncommitted changes: `check.py`, `check/`, `score/`, `SvGolf/`, the lake files, the tasks' `Spec.lean`, `IEEE754.lean` and `task.json`; read before the check ran), `lean_surfaces_revision` (as `check.py` records it, `+dirty` if `LeanModels/Sv` or `extractors/sv` has uncommitted changes), `lean_toolchain` (the `lean-toolchain` file), `yosys` (version line), `verilator` (version line; of a clocked record, the scoring point's check), `extractor_sha256` (the extractor program: `extract.py` alone for a checkout from before `lower_proc.py`, else the digest of both files, `check/envelope.py` `extractor_sha256`), `canon_script_sha256`, `script_sha256`, `ge_table_sha256` (the pinned flow of the record's kind: `score/svgolf.ys` and `score/ge.json` for a combinational record, `score/svgolf_seq.ys` and `score/ge_seq.json` for a clocked one), `flow` (OPTIONAL, decided 2026-11-07: `"seq"` in a record of a clocked task, the clocked flow; absent in a combinational record, whose flow is `"comb"`, and in every record made before the clocked format), `files` (sha256 of the checker's own files: `check.py`, `check/*`, `score/*`, `lean-toolchain`, `lakefile.toml`), `statement` (OPTIONAL, decided 2026-11-07: the trusted statement the record was checked under, the sha256 of each file of it, read before the check ran: the task's statement module, task.json `statement.module`, and every svgolf/ module it imports transitively, e.g. `tasks/add/Spec.lean` and `SvGolf/Task.lean`, plus `SvGolf/TaskSeq.lean` and `SvGolf/TaskReact.lean` for a clocked kind that rests on them and `tasks/fdivp/IEEE754.lean` for fdivp; `leaderboard.py` `statement_files`; absent in a record made before 2026-11-07). The board, par, `pareto --axes`, the site and `verify` compare it with the task's statement as it is now (`current_statement`): a record checked under another statement, or one that names none, is stale and not ranked, whatever its score |
| `proof` | `axioms` (sorted; from the comparator, walked through kernel values), `build_seconds` (compiling `Solution.lean` only), `lines` (code lines: blank lines and comments, including doc comments and nested block comments, stripped; `import` lines count), `imports`, `tactics` (the watched tactics found in the code: `sv_*` tactics, `omega`, `grind`, `decide`, `induction`, `simp`, `bv_decide`, `native_decide`; lexical, not a claim about the proof term), `uses_comb_view` / `uses_comb_eq` (the proof imports `LeanModels.Sv.CombView*` / `CombEq*`) |
| `ppa` | OPTIONAL (absent in every record made before the sky130 columns, which stay valid; hashed when present; the schema string is unchanged: additive, like `postsynth.mode`). check.py's `ppa` object of the run: `available: true`, `ppa_version`, `area_um2_sky130` (= `area_e4um2_sky130` / 10^4), `area_e4um2_sky130` (integer, 1e-4 um^2), `delay_ps_sky130` (integer ps), `unit_depth` (= `score.depth`, checked), `cells_sky130` (= `score.num_gates`, plus 1 if `constants`: the priced tie cell; checked, and equal to the sum of `cell_hist_sky130`), `cell_hist_sky130`, `constants`, `critical`, `setup`, `liberty_file`, and the hashes `liberty_sha256`, `ppa_pins_sha256`, `ppa_script_sha256`, `netlist_sha256`, and (WP-X4) the optional sub-object `mapped` (flow A1': `{"available": true, ...}` with `ppa_mapped_version`, `area_um2_sky130_mapped_v1` (= `area_e4um2_sky130_mapped_v1` / 10^4), `area_e4um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1` (= the sum of `mapped_cell_hist_sky130_v1`), `mapped_levels_sky130_v1`, `mapped_buffers_sky130_v1`, `mapped_inverters_sky130_v1`, `equivalence`, the hashes and the Yosys/ABC builds; its `rtlil_sha256` must be the record's `score.rtlil_sha256`; or `{"available": false, "reason": "..."}` for a design the mapping could not weigh; an old reader accepts the key, extra keys of `ppa` are allowed); or `{"available": false, "reason": "..."}` for a design the pinned flow could not weigh (recorded only from a `--ppa require` run: under `auto` a missing liberty would look the same). THE RANKED SCORE: the boards rank `area_e4um2_sky130` and the time (`delay_ps_sky130`; a clocked record's `score.time_ps`); a record without the key, or with an unavailable one, is not ranked |
| `postsynth` | the post-synthesis check that passed. A combinational record: `point`, `vectors` (those the run used), `mismatches` (0), `salted` (whether `$SVGOLF_POSTSYNTH_SALT` was set), `seed`, `mode` (`"full"` or `"light"`; absent in records made before the modes existed, which read as full) and `full_vectors` (what the full mode would have used; equal to `vectors` for a full record; absent in those same records). Additive: the schema is unchanged. A CLOCKED record (`checker.flow` `"seq"`, decided 2026-11-07) has exactly `mode` (`"light"` when one point ran light, else `"full"`), `mismatches` (0), `netlist_sha256` (the scored netlist: the scoring point's, and `ppa.netlist_sha256`) and `points`, one per point of the task in check.py's order, each exactly `point` (check.py's name, `N=8`, `default` for a parameterless top), `params` (`{"N": 8}`), `mode`, `mismatches` (0), `netlist_sha256` (that point's netlist), `latency` (the declared latency, `null` when the kind declares none; `score.cycles` is it, or 1) and `seeds`, the seeds 0 to n-1 in order, each with `seed`, `cycles` (stimulus entries), `segments` (react-family) or `transactions` (tx-family, stream-family) as a count (a seq-family seed counts only its cycles), and, where the check recorded them, `reset_cycles`, `salted`, `seed_sha256` and (F5, decided 2026-11-07: everything random in a seed's run derives from `$SVGOLF_POSTSYNTH_SALT` and is recorded) the power-ups' draws `netlist_randseed` (Verilator's `randSeed`, 1 to 2^31 - 1) and `lssv_start` (`zeros` or ls-sv's `seed:<k>`); the run's timings are not kept. `validate_record` holds the points to the record's own score and `ppa` block; acceptance holds them to the task |
| `notes` | free text (at most 2000 characters) |
| `record_hash` | as above |

A real record is `data/_example/*.json` (every key above except the optional `ppa`, which that file predates, and nothing else).

## The sky130 PPA columns (WP-X3, WP-X4): the ranked score

The ranked number is flow A0''s area x time (A0' decided 11/03, the product 11/05): a record made since the wiring
carries the columns `score/ppa.py` computes on the scored netlist (flow A0': area in um^2, delay in ps; units and what
is NOT claimed in [../score/PPA.md](../score/PPA.md) and the README's "Scoring"), `combined.py` multiplies them,
`board` and `export` rank the records by the product, and `pareto` lists the Pareto frontier of the two factors
(`RANKED_AXES`: `area_um2_sky130`, `time_ps`), an exploration view, with the GE area and depth as extra columns; since WP-X4 the record also
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
python3.12 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130,time_ps     # pareto's default frontier
python3.12 leaderboard/leaderboard.py pareto --task add --axes area_mge,depth              # the GE frontier, an extra view
python3.12 leaderboard/leaderboard.py pareto --task add --axes area_um2_sky130_mapped_v1,mapped_delay_sky130_v1
python3.12 leaderboard/leaderboard.py pareto --task aes_sbox --axes area_um2_sky130,delay_ps_sky130,depth --format json
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
carries no noise band: the pinned flow is deterministic (the same design text gives the same integers on every run,
README "Scoring"), so the board compares the exact integers and a difference of any size is a difference between the
scored netlists. Without `--axes`, `pareto` prints the frontier of the ranked number's two factors, each row with its
board rank (`#`) and its area x time.

## Policy

**The ranked number is area x time** (decided 2026-11-05): the sky130 A0' area
times the time, exact in 1e-4 um^2 x ps (`combined.py`), lower is better; par,
the record and "under par" on the site use it, and so do `board` and `export`.
Both factors are exact integers: the area `ppa.area_e4um2_sky130` in 1e-4 um^2,
the time in ps (`ppa.delay_ps_sky130` for a combinational record,
`score.time_ps` = cycles x period for a clocked one). **The board lists the
records by area x time, lowest first** (`score_key`, the site's order): the `#`
column is the rank, equal products share one (1, 1, 3), and they are listed by
the smaller GE area, then the smaller depth, then the earlier `submitted_at`,
then the record hash, so the order is the same on every machine and on the
site. In the JSON (`board --format json`) the board is `ranking`, each row with
its `rank`, `exact` (area x time in 1e-4 um^2 x ps) and `um2ns` (the same in
um^2 x ns). **The Pareto frontier of the two factors is for exploring** (decided
2026-11-03 as the ranking, an exploration view since 2026-11-05): every row of
the board names its `layer`, the Pareto layer it is on, and `pareto` prints
layer 1. A record is on the frontier iff no other record is at least as good on
both factors and strictly better on one: equal scores do not dominate each other,
ties are kept; layer 2 is the frontier of what is left, and so on (the JSON
keeps them as `frontier` and `dominated`, layer by layer, each layer in area,
time, date, player, hash order). The GE area and depth are shown beside them and rank nothing. A
player's old submissions stay on the board as entries of their own;
records are append-only and never edited.

**There is no depth budget by default.** A task author may add one of two:

* `leaderboard.depth_budget` in `task.json` (positive integer, absent or
  `null` = none): a **ranking-only** budget on the unit depth. The board then
  also ranks "best area x time under the depth budget" (records within the budget,
  ordered by area x time as the board is, ties sharing a rank: 1, 1, 3), and lists the records over it
  after those, flagged `over budget`. The board's own ranking and the frontier are not changed by it; their
  rows carry an `over`/`ok` flag. Nothing is rejected.
* `scoring.depth_budget` (already in `task.json`): the checker's **hard**
  budget, a depth over it rejects the submission at the `score` stage, so a
  fresh record is always within it. The board uses it for the same ranking,
  so records made before the budget was set or lowered are flagged.

With both, the smaller one ranks. The value for `mul` is an open question
(PLAN.md); no task has a budget today.

**Scores are comparable exactly when the flow, the point, the sky130 pins and
the input drive agree.** The board ranks only records whose `canon_script_sha256`,
`script_sha256`, `ge_table_sha256` and `yosys` equal the current pinned flow
OF THE TASK'S KIND (decided 2026-11-07: `current_flow(svgolf, task_flow(task))`, the
hashes of `score/svgolf.ys` and `score/ge.json` for a combinational task, of
`score/svgolf_seq.ys` and `score/ge_seq.json` for a clocked one, and the flow's
name, so a record of the other kind's flow is never ranked; the site compares
with the pins `flow` and `flow_seq` of `tests/expected.json` the same way),
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
Opus 4.1 (design)", "PROVER-SERVICE (proof)", "ABC scripts"). Free text,
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
| `--offline` | the record is well-formed (a clocked record's points, seeds, netlist and latency held to its own score and `ppa` block); `record_hash` is the hash of its canonical JSON and its file name; both stored files exist with the recorded sha256; the area equals the sum of the gate weights of the GE table of the record's flow, `score/ge.json` or, for a clocked record, `score/ge_seq.json` (when that is the recorded table); a record whose flow is not its task's kind's is `stale`; so is one checked under another trusted statement than the task's now, or made before records named theirs (`checker.statement`); the axioms are within the task's allowed set; a `ppa` object agrees with the record's own score (unit depth, cell count, histogram, area arithmetic); a `ppa` object of the current `ppa_version`, liberty and pins names the timing setup the task's configuration gives now: its `setup.input_drive` another than the task's (`task.json` `input_drive`, else the pins' default) makes the record `stale`, not comparable and not ranked (the task changed its drive: the record is not wrong), and a `pi_slew_ps` or `po_load_ff` other than the pins file's is a failure. Also notes which checker files have changed since the record | milliseconds; no tools |
| default | `--offline`, plus a rescore: `score/score.py` on the stored design at the task's scoring point (source gate, then the two-stage Yosys flow; `score.py --seq`, the clocked flow, for a clocked record, and `ppa.py --seq` for its columns): area, depth, gate mix, canonical text hash and canonical RTLIL hash must equal the record's. For a record with a `ppa` object the same single flow runs through `score/ppa.py` (its `score` is `score.py`'s result unchanged) and the columns must reproduce exactly (`area_e4um2_sky130`, `delay_ps_sky130`, `unit_depth`, `cells_sky130`, the histogram, `netlist_sha256`, the whole `setup`, and, when the record has `ppa.mapped`, the mapped area, delay, cells, histogram, levels and mapped netlist hash: the same flow also maps once, +0.3 to 1.4 s); without the pinned liberty on the verifying machine, or when the record was weighed under another `ppa_version`/liberty/pins, that comparison is a NOTE, never a failure; weighed under another input drive than the fresh weighing's (the task's now), the record is `stale` and its A0' columns are not compared (a record that claims a drive its numbers were not weighed under is therefore never "reproduced": stale under the task's drive, a failure once the task's drive is the claimed one) | one Yosys run per record (7 s for the five seeded records, the `mul` one and the sky130 columns and the A1' mapping of each included, 11/04); no Lean, no Verilator |
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

`data/` holds eleven proved references (`_example` `band` and `band_lp`,
`add_n_byhand`, `aes_sbox` `sbox_bp` and `sbox_table`, `clmul_n`, `fdivp`
`fdivp`, `fdivp_newton` and `fdivp_srt`, `mul_n_byhand` and `mul_tree_h`) as
player `svgolf-reference`, `assisted_by` `["Claude (Anthropic)"]`, notes
`reference solution`, each from a real `check.py --ppa require` run (their
stored files are byte-identical to `tasks/*/reference/` at the time). The first
five were re-seeded on 2026-11-04 under `sky130_a0_v3`, so they carry the ranked
sky130 columns (four replace the records of 10-29, the same design and proof
files made before the columns; the git history keeps them). The record
fingerprint is strict (a score is tied to an exact checker), so after a change
to a checker file the references are re-seeded as a routine step: on 2026-11-05,
after `check.py` and `check/envelope.py` changed, the ten records made before it
were re-seeded from the same files, with the same score, `ppa` columns and
post-synthesis vectors (only the checker hashes and revisions, the build time
and the record hash differ). On 2026-11-06, after the statement gained the
parameter range and `LoopFree` and `check.py`, `score/banlist.py`,
`score/fourstate.py` and `score/srcgate.py` changed, all eleven were re-seeded
the same way, with the same score, `ppa` columns, post-synthesis vectors and
stored `.sv`: nine from their proofs as updated for the range, the two `aes_sbox`
ones from the same files (new: the proof files of the nine, the checker hashes
and revisions, the build time, the date and the record hash). The four player
records were made under the statement before that change; three of their
proofs (`select-six`, `late-carry`, `plus-minus-two`) read the range as `1 ≤ N`
and were rejected at `solution` by the checker of 2026-11-06. On 2026-11-07 a
record started naming the statement it was checked under (`checker.statement`,
decided 2026-11-07), so a record that names none, or another, is stale and not
ranked: all eleven reference records were re-seeded again from the same files
(`seed-references --require-clean`, the sandbox, `--ppa require`, full post-synthesis; MEASURED: every score, `ppa` block, post-synthesis record, canonical hash and stored `.sv` and `.lean` equal to the record it replaces; new: `checker.statement`, the checker hashes and revisions, the build time, the date and the record hash), and the three study records were re-recorded with their proofs
ported by the maintainers, one line each (`have hN' : 1 ≤ N := hN` to `hN.1`,
nothing else), the design, player, assistance, date and credit kept and the
notes saying so (`add --require-clean`; MEASURED: score, `ppa`, post-synthesis record, canonical hash, stored `.sv`, player, assistance and date equal to the old record's). The fourth player record, `tower-shuffle`
(aes_sbox), made on 2026-11-05 and accepted by `verify --full` under the current
statement on 2026-11-06, names no statement: it is stale and unranked until it
is re-recorded, a step for the maintainers to decide. `seed-references` does it for every `ready` task (`--task T
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

`python3.12 tests/leaderboard/test_leaderboard.py` (also the `leaderboard` step
of `tests/run.py`, with `leaderboard.py verify --offline` on `data/`): the
ranked board (area x time ranks, above the Pareto layer: a dominated record
with the smaller product ranks above a frontier one; equal products share a rank
and are listed as on the site, which `tests/site/test_units.py` cross-checks
against site/build.py; the sky130 area and time rank where GE says otherwise; records
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
determinism, records without columns or under another version listed as not shown, `--axes area_um2_sky130,time_ps` is the default board's frontier, the mapped axes); and
the clocked record format (decided 2026-11-07) on the arbiter's real accepted check result
(`tests/leaderboard/clocked_arbiter/`: the reference `rr_mask`, react-family, `check.py --postsynth full --ppa require`,
its task.json and design; only the run's temporary paths changed): the result is accepted and its record keeps
the three points and their seeds; it ranks, and is par, under the clocked flow and not under the combinational one;
it verifies offline and by rescore, `--seq` on the command line; every way a clocked result can fall short (a point,
a seed, a light point, a mismatch, a latency, a netlist, the flow) is refused, and every way a stored clocked record
can be inconsistent is invalid; each clocked kind keeps its own count (transactions, segments, none); and the kinds,
flow files and seed default agree with `check.py`, `check/postsynth.py`, `score/score.py` and `score/points.py`. The
tests inject the check and rescore results; none runs Lean or Yosys.
