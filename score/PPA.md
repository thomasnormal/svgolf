# PPA columns (`score/ppa.py`): flow A0' (ranked, repaired) and flow A1' (research)

The RANKED score of the scored netlist (decided 2026-11-03; the boards rank it since 2026-11-04: `leaderboard.py`'s `RANKED_AXES`,
the A0' area and time), with `(area_ge_v1, depth_v1)` as extra columns; `score.py` is unchanged; `check.py` records the
columns as the result key `ppa` ("Wiring" below). Study and measurements:
`design/ppa/sky130.md` (the study of 2026-10-30) and `design/ppa/spike/`.

**Rulings since.** Decided 2026-11-03: A0' becomes the ranked sky130 score (area um^2, delay ps; clocked
tasks: cycles x the register-to-register period), GE and unit depth stay as columns, A1' stays an unranked research column.
Decided 2026-11-04: the repair step everywhere (buffering only), and a design whose netlist stays illegal is rejected, since a
golfer can fix it: A0' is `sky130_a0_v2`, weighed on the netlist REPAIRED by buffering
only, and one the repair cannot make legal is rejected ("The repair and the legality check" below). Decided 2026-11-04, on which cell
drives the inputs: each task chooses the drive that is more realistic or more interesting for it: A0' is `sky130_a0_v3`, every primary input driven by the TASK's input drive (`task.json`
`input_drive`, default `sky130_fd_sc_hd__buf_8`; "The input drive" below). 2026-11-04, after the STA study against OpenSTA: the
per-edge pin loads go into `sky130_a0_v3` before it is released, so that the ranked numbers change once ("The per-edge
loads" below). Decided 2026-11-05: the ONE ranked number is area x time, the A0' area times the time (`leaderboard/combined.py`);
par, the record and "under par" use it, and the Pareto frontier of the two is an exploration view. Decided 2026-11-09: a reader may see
the golf scores on sky130 or on ASAP7 (a dropdown on the front page), so `ppa.py` weighs two libraries: sky130, the
default and the records' ranked score, and ASAP7 (`--pdk asap7`), whose numbers live beside the records ("ASAP7: an
alternative library" below). The text further down describes the flows as
built from 2026-10-31 to 2026-11-01; where it says the columns rank nothing or reject nothing, these rulings supersede it. To reproduce a
recorded number bit for bit: "Reproduce a score" below.

**The banlist, decided 2026-11-05** (a rule of `score/banlist.py`, not of the PPA flow; no number here moves): in a task that
bans `+` or `-`, a run-time ordering comparison (`< <= > >=`) is banned too, at the Yosys level. Yosys's `alumacc` builds it
as an `$alu`, Yosys's own adder, so the backstop runs `alumacc` after `proc; opt` and rejects every `$alu`, `$macc`,
`$macc_v2`, `$lcu` or `$fa` cell it builds, at the comparison's source location; equality and comparisons Yosys folds as
constants stay allowed. So `add`'s `cmp_carry` (`tests/add/baselines/cmp_carry.sv`, every carry a comparison: the fastest
add design below, 1,965 ps at N = 16) is a BANNED baseline since then, scored with the banlist lifted like `plus` and
`yosys_mul` (`designs.json` and `tests/expected.json` `"banned": true`); the tables measured before name it without the mark.

**Two flows, side by side** (decided 2026-11-01, superseded for A0' by the rulings above: neither is declared official,
nothing is ranked; the real mapping stands beside the simple one, as an algorithm competition would not be run without
compiler optimization):

| | **A0'** (`ppa`, since 2026-10-31) | **A1'** (`ppa.mapped`, since 2026-11-01) |
|---|---|---|
| what it is | the pinned `abc -g` netlist of the default score, each Yosys gate re-expressed as one sky130 `_1` cell, REPAIRED (buffer trees and replicated tie cells, nothing resized, `sky130_a0_v2`), then a static timing analysis with every input driven by the task's input drive (default `buf_8`, `sky130_a0_v3`); a netlist the repair cannot make legal is rejected | the canonical RTLIL of the same run mapped by a real `abc -liberty` run onto every ordinary sky130 cell (compound cells, every drive strength), then the very same timing analysis |
| closer to | the default score: a fixed function of the netlist the board already ranks, no new synthesis | a fabricated chip: what a technology mapper does with the circuit |
| sensitivity | follows the expression tree you wrote (commuting operands moves area up to 11% and delay up to 32%) | follows the mapper too: `&nf` re-derives the structure (the proved array multiplier goes from 2nd to last in area); commuting operands moves area up to 15.5% and delay up to 20% |
| fields | `area_um2_sky130`, `delay_ps_sky130`, `unit_depth`, `cells_sky130`, `cell_hist_sky130` | `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1`, `mapped_cell_hist_sky130_v1`, `mapped_levels_sky130_v1` |
| version, pins, script | `ppa_version` `sky130_a0_v3`, `ppa_pins.json` (its `timing`, `repair` and `constants` sections), `ppa.py`, the task's `input_drive` | `ppa_mapped_version` `sky130_a1_v1`, `ppa_mapped_pins.json`, `ppa_mapped.ys`, `ppa.py`, the Yosys and ABC builds |
| cost | the repair is Python in `ppa.py`: 0.01 to 0.6 s per netlist, 1.3 s for matmul (two weighings) | one more Yosys process, 0.3 to 1.4 s on the references (3.6 s on the largest idiom), about the cost of the pinned flow |

The fields of the two flows have different names, versions and hashes and are never swapped silently (PLAN2: "A1' never replaces
A0' under the same name"). Both are exact deterministic functions of the design text and the tool build: bit-exact across processes, hash
seeds, parallelism, temp and working directories, checkouts, locales and file names (measurements below; again
2026-11-05 on 52 designs). Another build of the same Yosys version can give other numbers (2026-11-05: 3 of 52 designs,
all fdivp, under the WebAssembly build; "Determinism (measured)" below). A1' is never a reason to reject a submission; A0' is, when the repair
cannot make its netlist electrically legal (2026-11-04).

## The repair and the legality check (`sky130_a0_v2`, 2026-11-04)

Why: the unbuffered A0' netlist can be electrically illegal. The 2026-11-04 fanout study found the 33 combinational designs legal
(worst load 0.57x max_capacitance) but matmul G1 not: 4 cells over max_capacitance, 361 over max_transition, 1,616 table
reads past the characterized grid, where the extrapolated tables are non-monotone and can go negative; its period read
48,079 ps against about 10,700 ps repaired, and duplicating one control flop was a 4.4x ranked-time shortcut.

**`sky130_a0_v2` is BUFFERING ONLY** (decided 2026-11-04, "add the repair step everywhere (buffering)"; `buffer_trees_v1`, pinned in
`ppa_pins.json` `repair` and `constants`, implemented in `ppa.py` itself, no external tool):

* The A0' cell netlist (flops cut out) is weighed and audited: every primary input driven by the task's input drive (fed
  by the pinned 50 ps ramp; `buf_1` in `sky130_a0_v2`, the task's since `sky130_a0_v3`, "The input drive" below), every
  output BIT a separate 10 fF load, every flop D pin a load. Every net that is the CAUSE of a violation (its load
  over its driver's `max_capacitance` or past its tables' characterized loads, or its transition over a limit while its
  driver's own inputs are legal) gets a BALANCED BUFFER TREE: internal nets, primary-input nets, flop Q nets and nets that
  drive output bits alike.
* The tree: the net's loads (cell pins, output bits, flop D pins) in a stable order (cell instance, then output port and bit,
  then flop; names in natural order) are cut into contiguous groups balanced by capacitance, level by level from the loads up.
  A level is the buffer cell (of `repair.buffers`: `buf_1, buf_2, buf_4, buf_6, buf_8, buf_12, buf_16`) and group count of
  least total area such that every group's load is within that cell's BUDGET (on an equal area, fewer cells), each group then
  driven by the smallest buffer whose budget holds it; levels are added until the driver's own load is within its budget. A
  cell's budget is the largest load, within its `max_capacitance` and its tables, at which its output transition stays within
  min(its `max_transition`, the library's `default_max_transition`, 1.5 ns) for every input transition up to 1.5 ns (the
  input drive: at the 50 ps ramp; a flop's Q: at the ideal clock's ramp), so a tree is legal by construction. Budgets
  (fF): `buf_1` 129.5, `buf_2` 313.7, `buf_4` 556.6, `buf_6` 783.6, `buf_8` 968.2, `buf_12` 1,372.4, `buf_16` 1,482.9; as
  the input drive (at the 50 ps ramp): `buf_1` 129.6, `buf_8` 973.2 (every allowed drive: "The input drive").
* The netlist is weighed again and the repair repeated until no violation is left (a net slow only because its input is waits
  for that input's repair; a tree still illegal would be rebuilt at half its budgets), at most `max_rounds` (32) rounds.
* Constants: the tie cell `conb_1` is REPLICATED, as few as hold every constant load within the `max_capacitance` of the
  output driving it (LO 2,046.8 fF, HI 1,903.8 fF), the loads split as a tree's are: one for an ordinary design, two for 255
  constant output bits, six for 1,023. The tie outputs' loads are audited (a tie cell has no timing arcs: its transition is not).
* No cell is resized and nothing is restructured: a net within its limits is weighed exactly as A0' wrote it (33 of the 37
  designs measured below need no buffer at all and weigh their `sky130_a0_v1` area to the 1e-4 um^2).
* The repaired netlist is written as structural Verilog (the trees and tie cells visible, a comment per tree naming the net,
  its driver, its loads and the tree; `--repaired-netlist OUT`), READ BACK, simulated against the A0' netlist on 2048 vectors
  (every output bit and flop D net; a difference is `RepairDefect`, a defect of the repair, never a number), and that text is
  what is weighed and hashed (`repair.netlist_sha256`). Yosys reads it against the liberty (`test_ppa.py`).

**Why not ABC's sizing** (the first `sky130_a0_v2` on this branch: `topo; buffer -p; upsize; dnsize` with `buf_1` driving and
10 fF loading every ABC input and output; dropped after the 2026-11-04 review, MEASURED): (1) a HOLE: the one tie cell was never
load-checked, so 255 constant-0 output bits (2.55 pF on `conb_1` LO, 1.25x its `max_capacitance`) scored as legal; (2)
UNFIXABLE REJECTIONS: ABC sees one 10 fF output per distinct net and no input-to-output or flop-to-output wire at all, so an
input wired to 14 or more output bits, a plain sign extension `{{16{x[15]}}, x}`, a replicated `{24{a & b}}`, a flop's Q to 17
or 64 output bits and an input into 96 flop D pins were REJECTED, and a golfer could not fix them (the pinned flow removes the
buffers they write and merges duplicates), contrary to "they can fix things themselves"; (3) UNEVEN AREA: `upsize` has no delay
target, so areas moved +2.4% to +40% unevenly (the proved ripple adder left the add frontier, the array multiplier went from
2nd to last in area, `sbox_bp` left its frontier). Buffering only repairs exactly the illegal nets: every review probe is now
legal (`test_ppa.py ReviewProbesTest`), the tie cell is audited and replicated, and a legal netlist keeps its v1 area.

The legality check (`ppa.Audit`): every driven net's load is within its driver's `max_capacitance` (cell outputs, the input
drive, the flops' Q, every tie-cell output), every net's transition within the `max_transition` of its driver and of every
pin it reaches, and every timing-table read (cells, the input driver, clock-to-Q, setup) inside its characterized grid, both
bounds. Nothing is ever extrapolated in the ranked flow; flow A1' keeps its own `sky130_a1_v1` reading (extrapolation
included) unchanged.

**What is still rejected.** A netlist the repair cannot make legal: a read BELOW a table's grid (a transition or load smaller
than the library characterizes), or a driver that cannot carry even one buffer within its limits. No netlist of the pinned
flow on `sky130_fd_sc_hd` is known to be one (the budgets of the ten gate cells, of every allowed input drive and of the
flop's Q are all at least 69.6 fF, `xnor2_1`'s); `test_ppa.py UnfixableTest` builds both on synthetic liberties. `check.py` then stops at stage `ppa` (after
`postsynth`), prints `ppa: REJECTED, the repaired sky130 netlist is electrically illegal`, and records `ppa: {"available":
false, "illegal": true, "reason": ..., "legality": {counts}}`. The message names the net in the design's words (an input by
its port bit, a register by its Q net, a cell net by its driver; what it drives as output bits `y[0] .. y[23]`, cell pins,
flop D pins):

```
the sky130 netlist is electrically illegal and the repair (buffer trees, replicated tie cells) cannot make it legal: the net
_0_ (inv_1 _1_), driving 1 cell pin: its driver may carry at most 0.0 fF, less than the buffers it would need. The ranked
sky130 score (sky130_a0_v3) is taken on a legal netlist only (no timing table is extrapolated), so the design is rejected
```

A repaired netlist that is not the scored circuit (`RepairDefect`) is not a rejection: `ppa.available` false under `auto`, an
infrastructure error under `require`.

**Inputs are not free.** `sky130_a0_v1` drove every input with an ideal 50 ps ramp at any load; `sky130_a0_v2` puts one
`sky130_fd_sc_hd__buf_1` in front of every input that is read, at the input net's real load, fed by that ramp, and that
`buf_1` is audited and, when over its limits, buffered like any other driver. Against v1 it costs a combinational design 10 to
1,276 ps (median 200; the 34 combinational designs below): most where an input carries a heavy but legal load (`sbox_table`,
whose inputs carry up to 0.88x the `buf_1` limit: +1,276 ps, +60.7%). The output load (10 fF per output bit) is unchanged.
Since `sky130_a0_v3` the cell is the TASK's input drive, by default `buf_8` ("The input drive" below).

**Determinism.** The repair is ours and has no run-dependent output. Two clean runs of `ppa.py --netlist-in X --path
--repaired-netlist Y` on the 37 netlists below (separate processes, hash seeds 17 and 34, separate `TMPDIR`s) gave 74 of 74
files byte-identical; `test_ppa.py` repeats it on the CLI (`test_two_clean_runs_are_byte_identical`, a clocked netlist and
constants too). The A1' goldens (`expected_ppa_mapped.json`) re-record byte-identically; the A0' goldens (`expected_ppa.json`,
`expected_idioms.json`) were re-recorded for the buffering repair, and again for `sky130_a0_v3`'s input drive (by
`ppa_validate.py table --expected-out`; the A1' goldens byte-identical again), and again, with the A1' goldens, for the
per-edge loads (A1' runs the same STA: its delays moved, nothing else).

## The input drive (`sky130_a0_v3`, 2026-11-04)

Decided 2026-11-04, on `buf_1` against a stronger input driver: each task chooses one or the other, whichever is more
realistic or interesting for it. `sky130_a0_v3` makes the cell in front of every primary input a field of the task:

* **`task.json` `input_drive`** (optional): the liberty cell name of one of the pins' `timing.input_drive.allowed`: the
  buffers `sky130_fd_sc_hd__buf_1`, `buf_2`, `buf_4`, `buf_6`, `buf_8`, `buf_12`, `buf_16`, the inverters `inv_1` to
  `inv_16` (the same strengths), and `sky130_fd_sc_hd__dfxtp_1` (a register: its Q). Absent, the pins'
  `timing.input_drive.default`: **`sky130_fd_sc_hd__buf_8`**. Every task uses the default today: their inputs stand for an
  on-chip bus or a register, which a strong driver models; a task whose inputs come from something weaker, or from a
  register, names its cell. A name outside the list is a TASK-CONFIGURATION error, never a number: `tests/run.py`'s
  `layout` step fails, `ppa.py` exits 1 (`TaskConfigError`), `check.py` stops with an infrastructure error (exit 2)
  before any stage, Lean or synthesis, runs (it needs the pins file, not the liberty).
* **What it means.** A buffer or an inverter is that cell, its input the pinned 50 ps ideal ramp at 0, its output the
  input net at its real load, the cell's WHOLE delay counted: a real cell in front of every input, as in v2 with `buf_1`.
  OpenSTA timing the netlist with one explicit instance of the cell per input gives the same arrivals to 1 fs; OpenSTA's
  `set_driving_cell -lib_cell <cell>` is another model, which adds only the load-dependent part, delay(load) - delay(0),
  and so is earlier by the cell's zero-load delay (`buf_1` at the 50 ps ramp: 58.7 ps on a rising input, 72.8 ps on a
  falling one; MEASURED 2026-11-04, `score/test_ppa_opensta.py`). `dfxtp_1` is the
  flop's CLK->Q `rising_edge` arc read at the ideal clock's 50 ps ramp, both Q edges from the one clock edge at 0: exactly
  how a clocked design's own Q nets start. The drive is outside the design (its area is not counted), but it is audited
  like every driver (`max_capacitance`, `max_transition`, its tables' grid), and its budget is what the repair holds an
  input net to: the load at which its output transition reaches 1.5 ns at the 50 ps ramp. In fF: `buf_1` 129.6, `buf_2`
  314.4, `buf_4` 558.9, `buf_6` 785.3, `buf_8` 973.2, `buf_12` 1,374.4, `buf_16` 1,483.9; `inv_1` 181.3, `inv_2` 331.4,
  `inv_4` 563.1, `inv_6` 782.8, `inv_8` 1,035.5, `inv_12` 1,417.2, `inv_16` 1,681.8; `dfxtp_1`'s Q 162.1. (`test_ppa.py`
  `test_the_input_budget_is_the_task_s_drive`: an input read by 407 inverters is weighed as written under `buf_8` and 408
  get a tree; under `buf_1`, 54 and 55; an inverter input counts at its larger edge, 2.39 fF.)
* **Recorded.** The block's `setup.input_drive` names the cell (it replaces v2's `setup.pi_driving_cell: "buf_1"`), so the
  drive is in every record and in its hash; `ppa_pins.json`, whose sha256 every block carries, holds the allowlist and
  the default; each task's README states its drive under "Rules for this task". `ppa.py --input-drive CELL` weighs under
  another allowed cell (research; it may not contradict a task that declares one).
* **Why `buf_8` by default** (MEASURED 2026-11-04 on the development tree of that day: the 36 rows of the v2 rankings below, each weighed
  under `buf_1`, `buf_2`, `buf_4`, `buf_8`, `dfxtp_1`'s Q and an ideal input, on a copy of v2 with only the driver made a
  flag). No drive changes an area order, a delay or time order or a Pareto frontier of any task, every row is legal under
  every drive, and the repair inserts the same 8 buffers under all of them. What the drive changes is how much the inputs
  add to the delay, and how unevenly across designs (the 27 combinational designs, against an ideal input):

  | drive | added delay, ps | spread across designs |
  |---|---|--:|
  | `buf_1` | 70 to 1,276 | 1,206 ps |
  | `buf_2` | 98 to 569 | 471 ps |
  | `buf_4` | 92 to 335 | 243 ps |
  | `buf_8` | 73 to 192 | 119 ps |
  | `dfxtp_1` Q | 273 to 1,262 | 989 ps |

  Most of `buf_1`'s spread is one design: `sbox_table` paid +61% (2,102 to 3,378 ps) for one 114.7 fF input, a LEGAL load
  the golfer cannot buffer away (the repair buffers illegal nets only, and the pinned flow removes the buffers a source
  writes); that erased 74% of its real speed lead over `sbox_bp_d16`, and under `buf_8` it keeps 94%. `buf_8`'s cost is
  small and nearly the same for every design, so the delay column measures the design's own logic, while input loading
  still costs something (192 ps at 115 fF; a tree past 973 fF: matmul's two `start` nets, 1,199.5 and 1,019.5 fF, get one
  under every drive). A register's Q adds its clock-to-Q (+167 to +211 ps over `buf_1`) to every combinational score. At a
  light load the big buffer is the slower one (its own intrinsic delay: `band` 255 ps under `buf_1`, 280 under `buf_8`).
  Open sky130 flows assume a strong input driver too (OpenLane drives inputs with `inv_8`; ORFS buffers every input port).

## The per-edge loads (`sky130_a0_v3`, 2026-11-04, before its release)

The 2026-11-04 STA study timed the same netlists under the same setup with OpenSTA (openroad/orfs 26Q4) and found one defect:
`ppa.py` loaded every net with the pins' `capacitance`, while OpenSTA reads a load pin's `rise_capacitance` for a rising
transition and its `fall_capacitance` for a falling one (in `sky130_fd_sc_hd` `capacitance` is about their mean: rise about
4.7% above it, fall 4.7% below, at most 9%). That put the STA 0.5% to 2.8% off OpenSTA on the references. Now every timing
read takes the edge's own load: cell outputs, the input drive's output, a flop's Q (clock-to-Q) and its D pin; a net's load
is checked against `max_capacitance` on its larger edge (OpenSTA checks each edge), the tie cells' too; and the repair counts
a pin at its larger edge, so a group within a budget is within it on both edges. The energy model's C (`energy.py`,
1/2 C V^2) stays the pins' `capacitance`. `sky130_a0_v3` was not released yet and takes the change: no `sky130_a0_v4`; a
number weighed before it and one weighed after differ in `ppa_script_sha256` (and `ppa_pins_sha256`, whose comments now
describe it).

MEASURED with the change (`score/test_ppa_opensta.py`, OpenSTA's numbers recorded in it): every timing arc of 46 cells (the
families a golfer may hand-instantiate, `_0` to `_16`) equals OpenSTA to the printed 1 fs; so do six hand-built netlists
on ideal ramps and behind one explicit `buf_1` per input, every output bit on both edges, and a register-to-register period;
the larger-edge `max_capacitance` violation OpenSTA reports is reported. 7 of its 8 tests fail on the code before the change.
The study found the same on all 330 cells with a function, the references and `bin_to_thermo`: per arc to 1 fs, full paths
to a few fs (OpenSTA computes in single precision).

What moves (MEASURED 2026-11-04: every reference and every baseline `tests/expected.json` scores at its task's scoring point, 36
rows, 32 distinct netlists, each weighed before and after through `ppa.score_and_weigh` under its task's drive, the default
`buf_8`, clocked tasks through the clocked flow; `ppa_validate.py table` agrees on its 18 designs): **every area is the
same, delays move -0.30% to +1.32%, and no task changes a delay order, an area x time order or a Pareto frontier.** One
tree changes, area unchanged: matmul G1's control net `_04378_` (`nor2b_1`, 443 cell pins, 980.5 fF at the larger edge)
gets 2 x `buf_4` instead of 1 x `buf_8`, so its repair is 6 buffers on 5 nets, and its worst load is 0.875x
`max_capacitance` (0.711 before). Every other tree is the same; the repaired netlists of `fdivp_newton` and of the idiom
`sbox_logexp` change only in their tree's comment, which names the load at the larger edge (`repaired_sha256`). Delays in
ps, before -> after:

| task | A0' delay, ps |
|---|---|
| `_example` | `band` (and `band_lp`) 280 -> 280 |
| `add` | ripple (`add_n`, `add_proc`, `add_proc_m`, `add_mux`, `add_n_byhand`) 2,590 -> 2,611, Sklansky 2,431 -> 2,451, Kogge-Stone 2,051 -> 2,064, `cmp_carry` 1,971 -> 1,965, the banned `plus` 3,127 -> 3,143 |
| `mul` | `mul_n` (and `mul_n_byhand`) 10,765 -> 10,907, `mul_tree` 6,054 -> 6,129, `mul_wallace` 5,910 -> 5,982, `mul_tree_h` 5,918 -> 5,992, `dadda_rc_16` 5,404 -> 5,461, `dadda_ks_16` 5,151 -> 5,148, the banned `yosys_mul` 6,202 -> 6,261 |
| `aes_sbox` | `sbox_bp` 4,264 -> 4,297, `sbox_bp_d16` 3,638 -> 3,670, `sbox_table` 2,294 -> 2,288 |
| `clmul` | `clmul_n` 1,112 -> 1,114, `school_tree_16` 969 -> 969, `kara_b4_16` 1,801 -> 1,807, `kara_b8_16` 1,361 -> 1,372, `kara_b2_16` 2,050 -> 2,055, `kara_full_16` 2,075 -> 2,089 |
| `fdivp` | `fdivp` 37,872 -> 37,984, `fdivp_newton` 39,692 -> 40,031, `fdivp_d1` 34,813 -> 34,994, `fdivp_d2` 38,196 -> 38,294, `flat_binary16` 35,675 -> 35,735 |
| `matmul` (time = 4 x period) | G1 period 10,705 -> 10,696, time 42,820 -> 42,784 ps, 87,173.6064 um^2 |
| `sorter` (time = 16 x period) | `sorter_ins` period 2,510 -> 2,523, time 40,160 -> 40,368 ps, 5,512.7872 um^2 |

The idioms move -0.73% to +0.55% and keep their order. Flow A1' runs the same STA, so its delays move too (`mul_tree` 7,539
-> 7,558, `sbox_logexp` 5,845 -> 5,944: OpenSTA's 7,558 and 5,944); its areas, cells, levels and mapped netlists do not, and
it keeps `sky130_a1_v1`. The energy columns move -0.06% to +0.13% (the STA's transitions feed the internal-power tables),
leakage not at all.

## Rankings under `sky130_a0_v3` (2026-11-04, the input drive)

Measured before the per-edge loads joined v3 (the numbers since: "The per-edge loads" above, which moves no ranking
either). The 36 rows of the v2 table below (every reference, every baseline `tests/expected.json` scores at the task's
scoring point, the matmul duplication probe; 31 distinct designs), each weighed by v3's own `ppa.py SV --task tasks/<t>
--no-mapped` (`--seq` for matmul, `--netlist-in` for the probe), every task on the default `buf_8`, against v2's numbers
(MEASURED 2026-11-04 on this branch): **0 flipped pairs in area, 0 in delay or time and every Pareto frontier v2's, on every task: no ranking
moves.** Every area is v2's to the 1e-4 um^2 (the repair inserts the same buffers: `fdivp_newton` 1, matmul G1 5, the
probe 2). Over the 30 distinct combinational netlists the delay moves -1,084 ps (`sbox_table`, -32.1%) to +25 ps (`band`,
+9.8%), median -66 ps (-1.7%); matmul's period is 10,705 ps in both (its critical path is internal). The v3 numbers equal,
row for row, the `buf_8` column of the drive measurement above.

| task | v3 against v2 | the A0' columns under v3 at the scoring point, um^2 / ps |
|---|---|---|
| `_example` | same orders and frontier | `band` 100.096 / 280 (v2 255) |
| `add` | same | ripple 460.4416 / 2,590, Sklansky 541.7696 / 2,431, Kogge-Stone 641.8656 / 2,051, `cmp_carry` 857.072 / 1,971, the banned `plus` 497.9776 / 3,127 |
| `mul` | same | `mul_n` 8,290.4512 / 10,765, `mul_tree` 8,603.2512 / 6,054, `mul_wallace` 8,966.0992 / 5,910, `mul_tree_h` 8,563.2128 / 5,918, `dadda_rc_16` 8,230.3936 / 5,404, `dadda_ks_16` 8,937.3216 / 5,151, the banned `yosys_mul` 8,825.9648 / 6,202 |
| `aes_sbox` | same | `sbox_bp` 892.1056 / 4,264, `sbox_bp_d16` 952.1632 / 3,638, `sbox_table` 3,445.8048 / 2,294 (v2 3,378) |
| `clmul` | same | `clmul_n` 3,429.5392 / 1,112, `school_tree_16` 3,419.5296 / 969, `kara_b4_16` 2,756.3936 / 1,801, `kara_b8_16` 2,853.9872 / 1,361, `kara_b2_16` 2,960.3392 / 2,050, `kara_full_16` 2,979.1072 / 2,075 |
| `fdivp` | same | `fdivp` 9,675.5296 / 37,872 (as in v2), `fdivp_newton` 33,824.9408 / 39,692, `fdivp_d1` 8,575.7248 / 34,813, `fdivp_d2` 10,344.9216 / 38,196, `flat_binary16` 8,734.6272 / 35,675 |
| `matmul` (time = 4 x period) | same | G1 87,173.6064 um^2, 4 x 10,705 = 42,820 ps; the probe 88,807.6736 um^2, 43,560 ps |

The netlist-reader idioms (`idioms.json`: no task, so the default drive) are not ranked; one pair returns to its v1 order,
`lut_case` and `packed2d_idx` (v1 616 and 496 ps, v2 713 and 731, v3 717 and 609).

## Rankings under `sky130_a0_v2` (2026-11-04, buffering only)

The fanout study's 35 scored netlists (references, baselines, idioms, matmul, the counter fixture), the Newton reference
`fdivp_newton` and the matmul duplication probe, weighed by v1 (`sky130_a0_v1`: unrepaired, ideal inputs, extrapolated
tables), by the dropped ABC-sizing v2 and by the buffering v2 (the scored netlists are the same, only the weighing differs).
MEASURED: all 37 legal (worst load 0.91x `max_capacitance`, the probe; worst transition 0.98x, matmul), none rejected; four
needed a buffer (matmul G1: 5 nets, one buffer each; the probe: 1 net, 2 x `buf_4`; `sbox_logexp`: 1 x `buf_2`;
`fdivp_newton`: 1 x `buf_1`), so areas equal v1's to +0.1%; delays move +0.0% to +60.7% against v1 (median +5.7%, the driven
inputs), matmul's period 48,079 to 10,705 ps. Against the ABC-sizing v2: areas -27.4% to 0.0% (median -7.6%), delays +2.1%
to +58.5% (median +6.7%; ABC's `upsize` bought speed with area).

| task | delay order | area order | Pareto frontier (area, delay) |
|---|---|---|---|
| `_example` | — (one circuit) | — | `band`: 100.096 um^2 (v1's), 255 ps (v1 185, the driven inputs) |
| `add` | unchanged from v1 | unchanged from v1 (the proved ripple adder 1st again) | v1's: ripple, Sklansky, Kogge-Stone, `cmp_carry` |
| `mul` | unchanged from v1 | unchanged from v1 (the array multiplier 2nd again) | v1's: `dadda_rc_16`, `dadda_ks_16` |
| `aes_sbox` | unchanged | unchanged from v1 (`sbox_bp` 1st again) | v1's: `sbox_bp`, `sbox_bp_d16`, `sbox_table` |
| `clmul` | unchanged from v1 | unchanged from v1 | v1's: `kara_b4_16`, `kara_b8_16`, `school_tree_16` |
| `fdivp` | unchanged (`fdivp_newton` last) | unchanged (`fdivp_newton` last) | `fdivp_d1` |
| idioms | `lut_case` and `packed2d_idx` swap (616 and 496 ps in v1, 713 and 731 now: the driven inputs) | unchanged from v1 | v1's |
| `matmul` (time = 4 x period) | the duplication probe was 4.4x faster in v1 (43,552 against 192,316 ps); it is now slower (43,560 against 42,820) | unchanged | the probe LEAVES it; the reference alone |

Per task, every pair (MEASURED 2026-11-04 at 3d7fadb8: every reference, `fdivp_newton` included, every baseline that
`tests/expected.json` scores at the task's scoring point, and the matmul probe, 36 rows, 31 distinct designs; each weighed by
its version's own `ppa.py SV --task tasks/<t> --no-mapped`, `--seq` for matmul, v1 being the development tree's `score/` before the change):
`_example`, add, mul, aes_sbox, clmul and fdivp have 0 flipped pairs in area, 0 in delay and v1's frontier; matmul has one
flipped pair, the probe against the reference in time, and the probe leaves the frontier. The ABC-sizing v2's flips on the
same designs (area: add 2, mul 5, aes_sbox 1, clmul 2; delay: mul 1, clmul 1; frontiers: add's proved references out and the
banned `plus` in, `sbox_bp` out, `clmul_n` in) are all undone; its matmul flip is the one kept. The A0' columns at the scoring
point, buffering only (um^2 / ps; v1's area everywhere but `fdivp_newton` and matmul): add ripple 460.4416 / 2,602,
Sklansky 541.7696 / 2,443, Kogge-Stone 641.8656 / 2,060, `cmp_carry` 857.072 / 1,963; mul `mul_n` 8,290.4512 / 10,924,
`dadda_rc_16` 8,230.3936 / 5,573, `dadda_ks_16` 8,937.3216 / 5,329; aes_sbox `sbox_bp` 892.1056 / 4,345, `sbox_bp_d16`
952.1632 / 3,747, `sbox_table` 3,445.8048 / 3,378; clmul `clmul_n` 3,429.5392 / 1,283; fdivp 9,675.5296 / 37,872,
`fdivp_newton` 33,824.9408 / 39,689; matmul G1 87,173.6064 um^2, 4 x 10,705 = 42,820 ps.

JUDGED: buffering only restores v1's orders and frontiers on every task; what moves is delay, by the input driver (the same
for every design of a task, so orders barely move) and, where a net is over its limits, by a tree loaded up to its budget
(about 1.5 ns transitions: slower than ABC's sized trees, e.g. matmul's period 10,705 against 10,218 ps). A legal net near
its limit is weighed as written and can be slower than a buffered one (an input to 13 output bits, legal, 1,088 ps; to 14,
buffered, 615 ps); that is the price of a repair that is not timing-driven, and a golfer who wants the speed restructures.

## Columns

| column | unit | exact? | meaning |
|---|---|---|---|
| `area_um2_sky130` | um^2 | yes (`area_e4um2_sky130` is the integer in 1e-4 um^2) | sum of the `sky130_fd_sc_hd` areas of the REPAIRED netlist (each Yosys gate of the pinned `abc -g` netlist one `_1` cell, then the buffer trees of the repair), flops and the tie cells included |
| `delay_ps_sky130` | ps, integer | rounded from the STA's float | latest primary-output arrival of a graph-based NLDM static timing analysis of the repaired netlist (clocked: the register-to-register period) |
| `unit_depth` | gates | yes | gates on the longest input-to-output path of the scored netlist (before the repair); equal to `ltp -noff` (the run fails if it is not) |
| `cells_sky130`, `cell_hist_sky130` | | yes | cell count and histogram of the repaired netlist (`nand2_1`, `xor2_4`, `buf_2`, ...) |
| `repair` | | yes | `method` (`buffer_trees_v1`), `cells_before` (the scored netlist's gates and flops: equals `score.py`'s `num_gates`, checked), `buffers`, `nets_buffered`, `tie_cells`, `rounds` (weighings), the repaired netlist's `netlist_sha256` (the structural Verilog `--repaired-netlist` writes) |
| `legality` | | ratios to 3 decimals | `worst_load_ratio` (load / max_capacitance), `worst_transition_ratio`, and the violation counts, all 0 in a weighed block |
| `ppa_version` | | | `sky130_a0_v3`: bumped whenever a number could change (pins file, STA, cell table, the repair, the input drive's meaning) once the version is released; the per-edge loads joined `sky130_a0_v3` before its release |
| `setup` | | | the timing setup the number was weighed under: `pi_slew_ps` 50, `input_drive` (the task's, default `sky130_fd_sc_hd__buf_8`), `po_load_ff` 10, no wires, no extrapolation |
| `liberty_sha256`, `ppa_pins_sha256`, `ppa_script_sha256`, `netlist_sha256` | | | the inputs of the number: the liberty, `ppa_pins.json`, `ppa.py`, the weighed netlist file |

Flow **A0'**: the pinned flow of `score.py` is run as it is; its scored netlist is read and each gate is re-expressed as one
sky130 cell (`NOT inv_1, NAND nand2_1, NOR nor2_1, AND and2_1, OR or2_1, XOR xor2_1, XNOR xnor2_1, MUX mux2_1,
ANDNOT nor2b_1, ORNOT nand2b_1`; the table is `ppa_pins.json`, each entry is checked against the liberty's own boolean
function on every run), then REPAIRED (below). No new synthesis, no mapping, no wires.
Timing setup (pinned, `sky130_a0_v3`): every primary input that is read is the output of the task's input drive (default
`buf_8`; `buf_1` in v2) at the input net's real load, whose own input is an ideal 50 ps ramp arriving at 0, its whole delay
counted (a real cell per input, not OpenSTA's `set_driving_cell`: "The input drive"; inputs are not free); every
primary-output **bit** 10 fF; a load pin presents its `rise_capacitance` to a rising edge and its `fall_capacitance` to a
falling one ("The per-edge loads"); no wire load; `T` = latest arrival over both edges; arcs: every arc of every related pin, bilinear interpolation
INSIDE the table only (a read outside it rejects the netlist; `sky130_a0_v1` extrapolated linearly), unateness picks the input
edge, worst arrival wins, largest transition carried. Constants (a literal on a cell pin or
an output bit) cost exactly one `conb_1` per module and no delay (the proposal of sky130.md section 4.2; open decision, below).

### Flow A1': the `mapped` sub-object

| field | unit | exact? | meaning |
|---|---|---|---|
| `area_um2_sky130_mapped_v1` | um^2 | yes (`area_e4um2_sky130_mapped_v1` is the integer in 1e-4 um^2) | sum of the `sky130_fd_sc_hd` areas of the cells of the mapped netlist (+ one `conb_1` if a constant is used, as in A0') |
| `mapped_delay_sky130_v1` | ps, integer | rounded from the STA's float | latest primary-output arrival of the SAME graph-based NLDM static timing analysis, same setup (50 ps input ramps, 10 fF per output bit, no wires), on the mapped netlist |
| `mapped_cells_sky130_v1`, `mapped_cell_hist_sky130_v1` | | yes | cell count and histogram (`maj3_1`, `xnor2_1`, `a21oi_1`, `buf_2`, ...) |
| `mapped_levels_sky130_v1` | cells | yes | cells on the longest input-to-output path (cell levels, not the gate depth of `unit_depth`: 16 for the ripple adder's 33) |
| `mapped_buffers_sky130_v1`, `mapped_inverters_sky130_v1` | | yes | `buf_*`/`bufbuf_*`/`bufinv_*` and `inv_*` cells of the histogram |
| `constants`, `critical`, `setup`, `liberty_file` | | | as in A0' (`critical.cells` counts cells on the critical path) |
| `equivalence` | | | `{vectors, seed}`: the mapped netlist agrees with the scored netlist on that many input vectors (below) |
| `ppa_mapped_version`, `liberty_sha256`, `ppa_pins_sha256`, `ppa_mapped_pins_sha256`, `ppa_mapped_script_sha256`, `ppa_script_sha256`, `yosys_version`, `abc_version`, `rtlil_sha256`, `netlist_sha256` | | | the inputs of the number: the liberty, both pins files, the Yosys script, `ppa.py`, the tool builds, the canonical RTLIL that was mapped (equal to `stages.score.rtlil_sha256`), the mapped netlist file |
| `available` | | | `true`; or the object is exactly `{"available": false, "reason": ...}` for a design the mapping cannot weigh |

Flow **A1'** is `score/ppa_mapped.ys` run in a FRESH Yosys process on the canonical RTLIL that stage 1 of the pinned flow
(`canon.ys`) wrote, so layout and names cannot change it, as in the default score:

```
read_rtlil canon.il
synth -flatten -top TOP
abc -liberty sky130_fd_sc_hd__tt_025C_1v80.lib -dont_use <24 globs> -script +strash;&get -n;&fraig -x;&put;scorr;dc2;dretime;strash;&get -n;&dch -f;&nf;&put
opt_clean -purge
write_verilog -noattr -noexpr mapped.v
```

* **The ABC script** is Yosys 0.53's own default for `abc -liberty` without `-constr`, written out (`sky130.md` section 5.1, variant
  `u`) so that a later Yosys cannot change it silently; omitting `-script` gives a byte-identical netlist (checked on all 24
  designs of `score/tests/ppa/designs.json` and `idioms.json`, and again by `test_ppa.py`). The delay-first mapper `&nf` chooses among
  all allowed cells and drive strengths; there is no `-constr`, no delay target `-D` and no `buffer; upsize; dnsize` sizing pass (the
  sized variant `s` of the study, which adds a constraint file and a delay target, costs about +5% area for -9% delay and was not
  chosen: sizing and buffering are decisions of a physical-design flow, and the plain script is Yosys's own default; the other is a
  change of `ppa_mapped.ys` and a new `ppa_mapped_version`).
* **The cell policy** is the one of A0' (`ppa.POLICY`): `-dont_use` globs exclude every cell that is not of class `logic`
  (sequential, scan, latch, clock-tree, low-power-flow, physical-only, tri-state, delay and multi-output cells and the tie cell), leaving
  the 268 ordinary combinational cells of every drive strength (`_0` to `_16`, buffers and inverters, `mux4`, `xor3`, `maj3`, the
  AOI/OAI families). `test_ppa.py` checks that the globs and `cell_class` agree on all 428 cells; `ppa.py` enforces the policy again on the
  mapped netlist (an instance that is not a cell of the pinned liberty, or not of class `logic`, refuses the weighing).
* **Constants** are the A0' policy: no `hilomap`, literals stay in the netlist, ONE `conb_1` is priced per module if any constant
  is used (tested on a design with constant output bits: both flows price the same single tie cell).
* **Unmapped count**: zero or a refusal.
* **Tool builds**: the live Yosys and ABC versions are recorded in every block, compared by the tests with the ones the goldens were
  recorded under (`ppa_mapped_pins.json`: Yosys 0.53 `53c22ab7c0`, ABC `UC Berkeley, ABC 1.01 (compiled May  6 2025 05:45:16)`); a different build is a
  loud failure of the golden tests, not a silent change of numbers. `leaderboard.py verify` compares the mapped columns only under
  equal mapped version, script, pins, liberty and builds, and says so otherwise.
* **Time limit**: one mapping run may take `yosys_timeout_s` (900) seconds of wall clock; a design that needs longer has `mapped:
  {available: false, reason: "... timed out ..."}` and nothing else changes.

**The equivalence sample.** Before a mapped netlist is weighed it is simulated, bit-parallel through the liberty's own cell functions,
against the scored netlist (the one `postsynth` verified against ls-sv) on 2048 input vectors (vector 0 all zeros, vector 1 all ones,
the rest `SHA-256("svgolf-ppa-mapped/1" / input bit / block)` bits) and must agree on every output bit: it catches a mapper or reader
defect that changes the function broadly. It is a SAMPLE, not a proof (a difference on one input pattern of 33 bits is invisible to
it); it costs 0.001 to 0.04 s. A disagreement is a `MappedDefect`: nothing is reported (`auto`) or the run is an infrastructure error
(`require`), because the circuit under test is not at fault.

## Run

```
python3.12 score/ppa.py --fetch-liberty                          # once: the pinned liberty into score/lib/ (git-ignored)
python3.12 score/ppa.py SOLUTION.sv --top add_n --param N=16     # pinned flow, then the columns of its netlist (A0') and of its mapping (A1')
python3.12 score/ppa.py SOLUTION.sv --task tasks/add             # top and scoring point from task.json
python3.12 score/ppa.py SOLUTION.sv --task tasks/add --no-mapped # A0' only (no second Yosys run)
python3.12 score/ppa.py SOLUTION.sv --task tasks/add --mapped-netlist OUT.v   # also write the mapped netlist
python3.12 score/ppa.py --netlist-in SCORED.v --task tasks/add    # the netlist file postsynth simulates (A0' only: A1' maps the RTLIL); --task: its input drive
python3.12 score/ppa.py SOLUTION.sv --task tasks/matmul --seq      # a clocked task: the clocked flow and its register-to-register period
python3.12 score/ppa.py ... --input-drive sky130_fd_sc_hd__buf_1   # research: another allowed input drive (not against a task that names one)
python3.12 score/test_ppa.py                                     # tests (SVGOLF_PPA_REQUIRE_LIB=1: a missing liberty fails)
python3.12 score/ppa_validate.py table                           # the (GE, depth) vs (um^2, ps) table of the references
python3.12 score/ppa_validate.py table --mapped                  # ... and A1' against A0' (um^2, ps, cells, levels, ranks, tau)
python3.12 score/ppa_validate.py table --designs designs.json,idioms.json --mapped-expected-out score/tests/ppa/expected_ppa_mapped.json   # re-record the A1' goldens
python3.12 score/ppa_validate.py table --designs idioms.json     # the 8 netlist-reader idiom designs (5 s); --expected-out re-records their goldens
python3.12 score/ppa_validate.py stime                           # the STA against ABC's own stime (112 mapped netlists)
```

Output: `{"ppa": {..., "mapped": {...}}, "score": {score.py's result, unchanged}}` (`--netlist-in`: `ppa` only; `--no-mapped`: no `mapped`). Exit 0 weighed (a design the mapping cannot weigh is still exit 0, with `mapped.available` false and the reason), 1 refused (JSON
`{"error": ...}`), 2 usage. A missing, unreadable or wrong liberty, a gate outside the table (flip-flop, latch, tri-state, a mapped cell),
an undriven or doubly driven net, a loop, an x/z constant that a gate or an output reads, a liberty whose cell does not compute the
gate it is mapped to, or whose table variables or units differ from the pinned ones, are errors, never a number. `--path` adds the
critical path: `critical_path` (net, edge) and, node by node, `critical_path_timing` (the net, its edge, the instance and cell
driving it, the arrival and the transition in ps to 0.1 ps, as the STA computed them; display only, never ranked: the site's
critical-path table).

**The netlist reader** takes what `write_verilog -noattr -noexpr` prints for the pinned flow: one flat module, `TYPE name (.PIN(net), ...);`
instances, port vectors, `assign`. It also reads what Yosys leaves of the cells it techmapped (`$shiftx`, `$shr`, `$pmux`, `$div`, ...): wires with
PUBLIC dotted names, which are printed as escaped identifiers (`wire [7:0] \_1_.A ;`, ended by a space, possibly with brackets inside the
name), `assign \_1_.A  = a;`, a part select after the space (`assign \_10_.B [23:8] = { a, b };`), and constants with x bits in those
assigns. They are real nets: a gate may drive one (`.Y(\_2_.Y )`, then `assign y = { 7'h00, \_2_.Y  }`), and then the signal goes
through it; when no gate reads them they change nothing. An x/z bit is an error only if a gate pin or an output bit reads it. A run-time bit select, a variable
shift or rotate, a `case` mux, a constant-table `case`, a one-hot decode, an index into a packed array and `/` or `%` by a variable
all weigh, and so does an S-box through log/antilog tables (a 2048-bit constant indexed by a computed value) (`tests/ppa/idioms.json`, 8 designs
with goldens; the first version of the reader refused every one of them with `assign width mismatch`, found by the review of the wiring). Two of the eight
(`packed2d_idx`, `sbox_logexp`) leave an x literal in a dead buffer: `ppa.py` and the leaderboard's rescore read them, but `check.py` never gets
that far (see "Known gap" below).

## Measured at several points (2026-11-05; measured, not ranked)

Decided 2026-11-04: "Maybe it would be interesting to score tasks at multiple points (not just N=16) and make the alternative
parameters available in the 'Compare the designs' plot". Every proof holds at every point of its task's range, so this is
measurement only: the ranked board stays at task.json's `scoring.params` and nothing here ranks anything.

* **The points**: `score/points.json` (untrusted, not hashed by the checker; task.json is not touched). add N = 8, 16, 32, 64;
  mul and clmul N = 4, 8, 16, 32; aes_sbox its one size; fdivp bfloat16 (W = 8, P = 8), binary16 (5, 11, the scored point) and
  binary32 (8, 24); matmul (N, W, AccW) = (2, 8, 32) and (4, 8, 32); the sorter N = 4, 8, 16 at W = 8. The scored point must be
  one of them (`score/test_points.py`).
* **The designs**: every reference of task.json and baseline of tests/expected.json (a baseline with `banlist_points` is a
  fixed size and is measured there only), which covers every design of `tests/ppa/designs.json`; `--records` adds the players'
  leaderboard records (shown as measured, never ranked; a nightly is meant to run it).
* **The flow**: `score/points.py measure` runs `score/ppa.py SV --task tasks/<t> --param ... --no-mapped` (`--seq` for a clocked
  task) once per (design file, point), one process at a time, under `nice -n 19`: the pinned flow, liberty, input drive and repair
  of the ranked score. A clocked design's time is cycles x period, the cycles from its proof's own `def lat` (checked against its
  `-- svgolf-latency:` header at the scored point; read for binders, literals, `+ - * /`, parentheses and the library's
  `clog2`, as LeanModels/Sv/Param.lean defines it, and for nothing else). A point other than the scored one whose flow fails or takes longer than the
  task's `time_limit_s` (120 s) is dropped for that design, with the reason in the data; `points.json` `skip` pins such a drop
  with its measurement (today: `fdivp_newton` at binary32, stopped at 120 s, more than 30 min in an earlier run; `dadda_ks_32`,
  stopped at 120 s, more than 1800 s earlier). 93 runs took 454 s in all (2026-11-05, load average 7 to 8); the binary32 runs that
  finish take 9 to 30 s.
* **The data**: `score/measured/<task>.json`, deterministic and sorted (no wall time in it). At the scored point it EQUALS the
  goldens bit for bit, and `measure` refuses to write it otherwise: `tests/ppa/expected_ppa.json` for every design of
  designs.json, tests/expected.json's GE columns at every point it scores (75 of the 99 rows) and its clocked columns (matmul, the sorter)
  at the scored point. `score/points.py check` (and `score/test_points.py`) also holds it to the current design files, sky130
  identity and pinned flow.
* **The site**: the explorer of "Compare the designs" gets a point selector (the scored point labelled ranked, every other
  "measured, not ranked") and a scaling view (any number against the task's parameter, one line per design, log axes, and the
  score over par's at each point, where a crossing shows a design starting to pay off: on add, the banned `cmp_carry` beats
  the ripple adder at N = 64). The headline chart, the leaderboard and the tables of the scored point are unchanged.

```
python3.12 score/points.py plan [--records]                          # what would be measured, no tool runs
nice -n 19 python3.12 score/points.py measure [--task T] [--records] [--timings OUT.json]
python3.12 score/points.py check                                     # the data against the plan and the goldens
python3.12 score/test_points.py
```

**The records at other sizes** (2026-11-13; measured, not ranked; leaderboard/README.md, "Other sizes"): every
record's design file, players' and par's, by the same command at the sizes of `leaderboard/sizes.json`, written to
`leaderboard/sizes/<task>.json` by `leaderboard.py sizes --write`, with the ASAP7 view's cells-only columns on the same
scored netlist (`ppa.py --netlist-in NET --pdk asap7`). The board still ranks the scoring point alone; at that point
every column equals the record's own (checked by `--write` and by `leaderboard.py sizes`), the evidence that the other
sizes come from the scoring flow. Each run has 900 s and 6 GiB for its process tree (`sizes.json` `limits`); a run that
reaches either is recorded as not measured, never retried under the same pins. The routed course has no data at other
sizes. aes_sbox has no size parameter and is left out.

## Reproduce a score

A ranked number is a pure function of: the design's text; the pinned flow (`score/srcgate.py`, `score/canon.ys`,
`score/svgolf.ys`, `score/ge.json`; for a clocked task `score/svgolf_seq.ys` and `score/ge_seq.json`), run by the pinned
Yosys BUILD and its ABC (the build, not only the version: "Determinism (measured)", and the reference build below);
`score/ppa.py` and `score/ppa_pins.json`; the pinned liberty; and the task's scoring point and input
drive. A check result (and so a record) carries the hash of each: `score.yosys_version`, `score.canon_script_sha256`,
`score.script_sha256`, `score.ge_table_sha256`, `score.rtlil_sha256`, and `ppa.liberty_sha256`, `ppa.ppa_pins_sha256`,
`ppa.ppa_script_sha256`, `ppa.netlist_sha256`, `ppa.repair.netlist_sha256`, `ppa.setup`.

**Tools and pinned files** (the versions the goldens and `tests/expected.json` were recorded with; `tests/run.py` fails when
the Yosys version or a script hash differs from `tests/expected.json`'s `flow`):

| what | version or sha256 | role |
|---|---|---|
| Python | 3.12 (3.12.8 on the rating machine), with `pyslang` (11.0.0 on the rating machine) | `score/*.py`; `pyslang` parses the source for the source gate |
| Yosys | `Yosys 0.53 (git sha1 53c22ab7c0ced80861c7536c5dae682c30fb5834, clang++ 17.0.0 -fPIC -O3)`; the binary of the rating build (Homebrew's `yosys` 0.53, macOS arm64) has sha256 `011e094340da48932dd0af17da0846519af24cee7de9ae84c11cc78753ab7732` | the pinned flow: two processes, below |
| ABC | the `yosys-abc` beside that Yosys: `UC Berkeley, ABC 1.01 (compiled May  6 2025 05:45:16)`; the binary here (Homebrew's `yosys` 0.53, macOS arm64) has sha256 `769348bb154a26d5d97cd877d086893b3c6a1c8242343a505025bad62c7fa653` (another build has another hash and can give other numbers on some designs, measured 2026-11-05; the version line a record carries names the compiler) | run only by Yosys's `synth` and `abc -g` passes; the ranked weighing and its repair are Python (`ppa.py`), no ABC |
| liberty | `sky130_fd_sc_hd__tt_025C_1v80.lib`, 12,800,135 bytes, `ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5` (OpenROAD-flow-scripts `6c6fc7e2`, URL in `ppa_pins.json`) | fetched, never vendored: `python3.12 score/ppa.py --fetch-liberty` (size and sha256 checked) or `SVGOLF_SKY130_LIB=/path/to/copy` |
| `score/canon.ys` | `bbd11227d45dc1365f27597fd45c565fe721ba2648450588fc4fd983d00b367b` | Yosys process 1 |
| `score/svgolf.ys` | `ea58219d8ef14c3bad265218ee266ccdb709ac9d4dc5258edc34d51ee83a0445` | Yosys process 2 (combinational) |
| `score/svgolf_seq.ys` | `c3874dbfc85921a87df6eacdfc6b2c9a0e2b34edd5738951e0d8bdb51f4558b2` | Yosys process 2 (clocked) |
| `score/ge.json` | `6a29196a3f4b58241f4c9af650c9141e4632b737214d563a11ba142a725c4bea` | the GE prices (the extra GE column) |
| `score/ge_seq.json` | `0a1aa1147b6916efa4a41e03aa3c8c70e68c1e3fd7a0e9c9a3cbc177edefd1f6` | the GE prices of a clocked task (`ge.json`'s plus the flop's; its `_derivation` names the pins file it was derived under, so it changed with `sky130_a0_v3`'s pins) |
| `score/ppa_pins.json` | `d66a6086a37a97f5985266057051979fb6a8a3c557d3ef9c42acc1b5e41502d8` (`sky130_a0_v3`), recorded in every block as `ppa_pins_sha256` | the gate-to-cell table, the timing setup and input drives, the repair, the tie cells |

**The reference build** (the build ratings use, decided 2026-11-05; README.md, "Scoring", and `score/reference_build.json`): Homebrew's Yosys 0.53 for macOS arm64, compiled by clang++ 17 with -O3, with its `yosys-abc` (both sha256 above); every published number was made with it, the flow is deterministic on it, and another build can give other numbers on some designs ("Determinism (measured)"). It is not pinned to a slower portable build.

**The pinned flow, step by step** (what `score.py` does):

1. The source gate, `srcgate.py`, refuses preprocessor directives, attributes, synthesis pragmas and `unique`/`priority`,
   and writes the CANONICAL text (comments stripped). Yosys reads that text, never the submitted file.
2. Yosys process 1, `yosys -q -l canon.log -s canon.ys`: `score/canon.ys` without its comment lines, its placeholders
   filled (`@SOURCES@`: one `read_verilog -sv "<canonical file>"` per source; `@TOP@`: the task's top; `@CHPARAM@`:
   ` -chparam NAME VALUE` per scoring parameter; `@RTLIL@`: the output). For the `add` reference at `N = 16`:

   ```
   read_verilog -sv "add_n.sv"
   hierarchy -check -top add_n -chparam N 16
   proc
   flatten -noscopeinfo
   hierarchy -top add_n
   setattr -unset src
   setattr -mod -unset src
   setattr -unset hdlname
   setattr -mod -unset hdlname
   rename -hide
   rename -enumerate
   write_rtlil "canon.il"
   ```

3. Yosys process 2 (a fresh process: Yosys's results depend on names a process has interned), `score/svgolf.ys`:

   ```
   read_rtlil "canon.il"
   synth -flatten -top add_n
   abc -g AND,NAND,OR,NOR,XOR,XNOR,ANDNOT,ORNOT,MUX
   opt_clean
   tee -q -o "stat.json" stat -json
   tee -q -o "ltp.txt" ltp -noff
   write_verilog -noattr -noexpr "netlist.v"
   ```

   ABC runs twice, each time with Yosys 0.53's own default script (the log, `grep "ABC: + " synth.log`, prints both):
   inside `synth`, `abc -fast`, `strash; dretime; map`; then the `abc -g` pass, onto a generated gate library of the listed
   gates, `strash; &get -n; &fraig -x; &put; scorr; dc2; dretime; strash; &get -n; &dch -f; &nf; &put`. `netlist.v` is the
   SCORED netlist (the one `postsynth` simulates and `check.py` weighs); GE is the `stat` count priced by `ge.json`, the
   depth `ltp -noff`. A clocked task runs `score/svgolf_seq.ys` instead: the same with `synth -nofsm` (no FSM re-encoding,
   decided 2026-11-06), `dfflegalize -cell $_DFF_P_ x` after it and `opt_clean -purge` as the last clean-up (decided
   2026-11-07: "Known gap" below), priced by `ge_seq.json`.
4. The ranked weighing, `ppa.py` on `netlist.v` (Python only): each gate becomes ONE `_1` cell (`ppa_pins.json` `gates`:
   NOT `inv_1`, NAND `nand2_1`, NOR `nor2_1`, AND `and2_1`, OR `or2_1`, XOR `xor2_1`, XNOR `xnor2_1`, MUX `mux2_1`, ANDNOT
   `nor2b_1`, ORNOT `nand2b_1`; each checked against the liberty's own function), a flop `dfxtp_1`, cut out of the timing
   graph; the netlist is REPAIRED by buffering only ("The repair and the legality check"); then the STA: every primary input
   that is read is the output of the task's input drive (`ppa.setup.input_drive`, default `sky130_fd_sc_hd__buf_8`) whose
   own input is an ideal 50 ps ramp at 0, every output bit a 10 fF load, no wires, every table read by bilinear
   interpolation inside its characterized grid only (a read outside it rejects the netlist), both edges, the worst arrival
   and the largest transition carried; `delay_ps_sky130` is the latest output arrival, rounded to the ps (clocked: the
   latest output or flop D arrival plus the flop's setup, the clock ideal with a 50 ps transition); `area_um2_sky130` the sum
   of the cell areas (exact: `area_e4um2_sky130`); the legality audit last.

**Reproduce a recorded number.** From `svgolf/` of a checkout at the record's commit, with the tools above on `PATH`
(checked 2026-11-04 by running the two blocks below as written, in a scratch copy of `svgolf/`: both references and the hand
run matched the goldens bit for bit; again after the per-edge loads):

```
python3.12 score/ppa.py --fetch-liberty
python3.12 score/ppa.py tasks/add/reference/add_n.sv --task tasks/add --no-mapped --json add_n.json --netlist add_n.scored.v --repaired-netlist add_n.repaired.v
python3.12 score/ppa.py tasks/aes_sbox/reference/sbox_bp.sv --task tasks/aes_sbox --no-mapped --json sbox_bp.json --netlist sbox_bp.scored.v --repaired-netlist sbox_bp.repaired.v
```

`add_n.json` then has `"area_e4um2_sky130": 4604416`, `"delay_ps_sky130": 2611`, `"netlist_sha256": "3b7da549a07e…"`,
`"repair": {..., "netlist_sha256": "ac214a9f04d7…"}` and `"setup": {..., "input_drive": "sky130_fd_sc_hd__buf_8", ...}`, and
its `score` block `"rtlil_sha256": "0699af350c19…"`: the golden `add_ripple` of `score/tests/ppa/expected_ppa.json`.
`sbox_bp.json` has 8921056, 4297, `22493fba30d8…`, `b27773491834…`: the golden `sbox_bp`. A clocked task needs `--seq`
(`python3.12 score/ppa.py tasks/matmul/reference/matmul_g1.sv --task tasks/matmul --seq`: 87173.6064 um^2, period 10696 ps,
6 buffers on 5 nets, `tests/expected.json`). A record's own numbers come from `check.py ... --ppa require`, which weighs the very netlist its
`postsynth` stage verified, by the same function; `leaderboard.py verify` weighs it again.

The same `add_n` numbers by hand, each step one tool and none of `score.py`:

```
mkdir hand && cd hand
python3.12 ../score/srcgate.py ../tasks/add/reference/add_n.sv --write add_n.sv
grep -v '^[[:space:]]*#' ../score/canon.ys | sed -e 's|@SOURCES@|read_verilog -sv "add_n.sv"|' -e 's|@TOP@|add_n|g' -e 's|@CHPARAM@| -chparam N 16|' -e 's|@RTLIL@|"canon.il"|' > canon.ys
grep -v '^[[:space:]]*#' ../score/svgolf.ys | sed -e 's|@RTLIL@|"canon.il"|' -e 's|@TOP@|add_n|g' -e 's|@STAT@|"stat.json"|' -e 's|@LTP@|"ltp.txt"|' -e 's|@NETLIST@|"netlist.v"|' > synth.ys
yosys -q -l canon.log -s canon.ys
yosys -q -l synth.log -s synth.ys
python3.12 ../score/ppa.py --netlist-in netlist.v --task ../tasks/add --repaired-netlist repaired.v --json hand.json
shasum -a 256 canon.il netlist.v repaired.v
```

The three hashes are the record's `score.rtlil_sha256`, `ppa.netlist_sha256` and `ppa.repair.netlist_sha256` (`0699af35…`,
`3b7da549…`, `ac214a9f…`), and `hand.json`'s columns are `add_n.json`'s. For another design: its canonical file(s), its
top and its scoring parameters in the two `sed` lines, and its task in `--task`.

**With OpenSTA.** Time the REPAIRED netlist (`--repaired-netlist`) with one explicit instance of the task's input drive in
front of every input (a buffer per input, whose own input gets `set_input_transition 0.05`), `set_load 0.010` on every
output and `set_load 0` on every net (no wires), the clock ideal with a 0.05 ns transition: OpenSTA (openroad/orfs 26Q4)
then gives `ppa.py`'s arrivals to 1 fs per arc; `set_driving_cell` instead would make every input path earlier by the
drive's zero-load delay ("The input drive"). `score/test_ppa_opensta.py` holds the script (`OPENSTA_TCL`) and OpenSTA's
recorded numbers.

**The ASAP7 view's numbers** (decided 2026-11-09: a reader may see the golf scores on ASAP7; sky130 stays the default).
The same command with `--pdk asap7` weighs the same scored netlist on the five pinned ASAP7 liberty files (flow A0',
`asap7_a0_v1`, "ASAP7: an alternative library" below); `leaderboard/asap7/<task>.json` keeps each design's numbers, and
`leaderboard.py asap7 --rescore` weighs them all again and compares, bit for bit:

```
python3.12 score/ppa.py --pdk asap7 --fetch-liberty         # once: the five files into score/lib/asap7/ (git-ignored)
python3.12 score/ppa.py tasks/add/reference/add_n.sv --task tasks/add --pdk asap7 --no-mapped --json add_n_asap7.json
python3.12 leaderboard/leaderboard.py asap7 --rescore --task add
```

`add_n_asap7.json` has `ppa.netlist_sha256` `3b7da549…` (the sky130 run's: the scored netlist does not depend on the
library), `area_e5um2_asap7` 699840 (6.99840 um^2) and `delay_ps_asap7` 563, so area x time is 3.940 um2*ns.

## The liberty

`sky130_fd_sc_hd__tt_025C_1v80.lib`, 12 800 135 bytes, sha256 `ef34f999d582044cad9c1f4d5422504ae99702ad42baa432d75215476e5d23d5`,
OpenROAD-flow-scripts commit `6c6fc7e2`, `flow/platforms/sky130hd/lib/` (URL and git blob in `ppa_pins.json`). It is **not
vendored**: the file has no header, the upstream SkyWater PDK repositories are Apache-2.0 (GitHub licence API, 2026-10-31) but ORFS
carries no licence file for the platform directory and the provenance of its generated copy is not recorded, and it is 12.8 MB.
`--fetch-liberty` downloads it and moves it into place only after size and sha256 match; `$SVGOLF_SKY130_LIB` or `--liberty`
point at any copy (the hash is checked on every load). Without it the real-library tests are skipped.

## Validation (every number: the command beside it)

`python3.12 score/ppa_validate.py table` (the 18 designs of `designs.json`, `fdivp_newton` included; 147 s with `--mapped`, 121 s
of it scoring `fdivp_newton`; `sky130_a0_v3`, every design on its task's default `buf_8` input drive, re-measured 2026-11-04 with
the per-edge loads): (GE,
depth) of `score.py` against (um^2, ps) of `ppa.py`.

| task | designs | GE vs um^2, Kendall tau-b | depth vs ps, tau-b | um^2 / GE | ps / level |
|---|--:|--:|--:|--:|--:|
| add | 5 | +1.00 | +0.95 | 4.11 to 4.37 | 79 to 116 |
| mul | 7 | +0.90 | +0.59 | 4.21 to 4.30 | 90 to 124 |
| aes_sbox | 3 | +1.00 | +1.00 | 4.38 to 4.44 | 204 to 208 |
| fdivp | 3 | +1.00 | -1.00 | 4.29 to 4.49 | 118 to 159 |

| design | GE | depth | um^2 | ps | design | GE | depth | um^2 | ps |
|---|--:|--:|--:|--:|---|--:|--:|--:|--:|
| add_ripple (ref) | 112.0 | 33 | 460.4 | 2611 | mul_dadda_rc | 1953.6 | 61 | 8230.4 | 5461 |
| add_sklansky | 127.7 | 28 | 541.8 | 2451 | mul_dadda_ks | 2076.5 | 48 | 8937.3 | 5148 |
| add_kogge | 149.7 | 24 | 641.9 | 2064 | mul_yosys (`*`) | 2081.2 | 59 | 8826.0 | 6261 |
| add_cmpcarry (`>`) | 196.0 | 17 | 857.1 | 1965 | sbox_bp (ref) | 201.0 | 21 | 892.1 | 4297 |
| add_yosys (`+`) | 118.0 | 33 | 498.0 | 3143 | sbox_bp_d16 | 216.3 | 18 | 952.2 | 3670 |
| mul_array (ref) | 1962.6 | 88 | 8290.5 | 10907 | sbox_table | 786.9 | 11 | 3445.8 | 2288 |
| mul_tree (ref) | 2034.9 | 63 | 8603.3 | 6129 | fdivp (ref) | 2166.1 | 289 | 9675.5 | 37984 |
| mul_wallace (ref) | 2113.9 | 62 | 8966.1 | 5982 | fdivp_newton (ref) | 7892.5 | 252 | 33824.9 | 40031 |
| mul_tree_h (ref) | 2025.9 | 62 | 8563.2 | 5992 | flat_binary16 | 1944.8 | 303 | 8734.6 | 35735 |

Reading: buffering only gives area ranks that follow GE as under `sky130_a0_v1` (tau-b +1.00, +0.90, +1.00; the ABC-sizing
variant had dropped them to +0.60, +0.43, +0.33, "The repair and the legality check" above): no design of the table needs a
buffer except `fdivp_newton` (one `buf_1`), so um^2 per GE is the gate mix alone, 4.11 to 4.49. Delay ranks follow unit depth
except where delay per level differs: 79 ps per level for the ripple adder against 90 to 124 for the multipliers, 204 to 208
for the S-boxes (under v2's `buf_1`, `sbox_table`'s heavily loaded inputs made it 307 ps per level; under `buf_8`, 208), and
`add_yosys` is as deep as `add_ripple` (33) but 20% slower (3143 against 2611 ps), which is why its depth rank (tied 4th) and
delay rank (5th) differ; the dividers are ordered opposite to their depth (`fdivp_newton` 252 levels, 40,031 ps; `fdivp` 289,
37,984; `flat_binary16` 303, 35,735).

The SRT reference `fdivp_srt` joined `designs.json` on 2026-11-05, after these tables were measured
(`python3.12 score/ppa_validate.py table --only fdivp_srt --mapped`): 2787.7 GE, depth 189, 12,356.9 um^2, 27,592 ps
(146 ps per level, no buffer; A1' 9,850.7 um^2, 33,290 ps, 1545 cells, 97 levels). Against the order of the other three
dividers, its delay follows its depth: the shallowest divider is also the fastest. The rank statistics above are of
the 18 designs without it.

`python3.12 score/ppa_validate.py stime`: `abc -liberty` maps each canonical RTLIL (sized script, driver `buf_1`, load 10 fF,
7 delay targets), ABC's `stime -p` times it, `ppa.py`'s STA times the same netlist under the fixed setup. Re-measured 2026-11-04
with the per-edge loads: 126 netlists (the 18 designs; 39 distinct: most delay targets are inert), |STA / stime - 1| **mean
1.90%, max 9.8%, mean signed -0.20%**; the worst designs are `mul_array` (6.2% mean) and `sbox_bp_d16` (5.6% mean, 9.8% at
D = 6000, the STA below ABC's). Before the per-edge loads it was 112 netlists, mean 2.22%, max 10.7%, mean signed -0.62%, and
on the 14 designs of the first study's spike alone (98 rows) 1.96% mean, 6.7% max, row for row the spike's numbers (same ABC delays,
same STA to 0.01 ps, same cell counts). The "1.3% mean" quoted for the STA is the **Nangate45** figure of an earlier study (72
netlists). ABC's `stime` is not OpenSTA: against OpenSTA itself the STA agrees to 1 fs per arc ("The per-edge loads").

Determinism: `ppa_validate.py table` run twice (hash seeds 0 and 7, other `TMPDIR`): all 16 rows identical, including the
sha256 of the canonical RTLIL and of the scored netlist; `test_ppa.py` runs the CLI in separate processes under three hash
seeds and compares stdout byte for byte; the STA is IEEE doubles in a fixed order (it reproduced the spike's floats bit for
bit on all 14 netlists, `==` on the float).

### Flow A1' against A0' (`python3.12 score/ppa_validate.py table --mapped`; both re-measured 2026-11-04 under `sky130_a0_v3`'s per-edge loads, A0' on the default `buf_8` input drive)

The same 18 designs through the real `abc -liberty` mapping. The A1' numbers equal the first study's variant `u` on all 14 designs it
had (area, delay, cells, levels), and the mapped netlists are byte-identical to the study's on the 12 add and mul designs (the two
S-boxes were studied from design-study copies with other module names, so only their netlist text differs). The A0' columns are the
repaired ones (`sky130_a0_v3`); the A1' goldens (`expected_ppa_mapped.json`) re-recorded byte-identically after the repair and
the input drive, and the per-edge loads moved only their delays (A1' runs the same STA):

| design | GE | depth | A0' um^2 | A0' ps | A1' um^2 | A1' ps | A1' cells | A1' levels | A1'/A0' area | A1'/A0' ps |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| add_ripple (ref) | 112.0 | 33 | 460.4 | 2611 | 440.4 | 6279 | 48 | 16 | 0.957 | 2.405 |
| add_sklansky | 127.7 | 28 | 541.8 | 2451 | 499.2 | 3359 | 69 | 12 | 0.921 | 1.370 |
| add_kogge | 149.7 | 24 | 641.9 | 2064 | 568.0 | 2661 | 92 | 10 | 0.885 | 1.289 |
| add_cmpcarry (`>`) | 196.0 | 17 | 857.1 | 1965 | 660.6 | 1846 | 105 | 9 | 0.771 | 0.939 |
| add_yosys (`+`) | 118.0 | 33 | 498.0 | 3143 | 489.2 | 3567 | 74 | 11 | 0.982 | 1.135 |
| mul_array (ref) | 1962.6 | 88 | 8290.5 | 10907 | 8644.5 | 16391 | 834 | 45 | 1.043 | 1.503 |
| mul_tree (ref) | 2034.9 | 63 | 8603.3 | 6129 | 7975.1 | 7558 | 1074 | 31 | 0.927 | 1.233 |
| mul_wallace (ref) | 2113.9 | 62 | 8966.1 | 5982 | 8398.1 | 7374 | 1217 | 32 | 0.937 | 1.233 |
| mul_tree_h (ref) | 2025.9 | 62 | 8563.2 | 5992 | 8134.1 | 6217 | 1050 | 30 | 0.950 | 1.038 |
| mul_dadda_rc | 1953.6 | 61 | 8230.4 | 5461 | 7551.0 | 6758 | 1125 | 31 | 0.917 | 1.238 |
| mul_dadda_ks | 2076.5 | 48 | 8937.3 | 5148 | 8265.4 | 5506 | 1063 | 20 | 0.925 | 1.070 |
| mul_yosys (`*`) | 2081.2 | 59 | 8826.0 | 6261 | 8454.4 | 6205 | 1145 | 26 | 0.958 | 0.991 |
| sbox_bp (ref) | 201.0 | 21 | 892.1 | 4297 | 1094.8 | 4160 | 129 | 13 | 1.227 | 0.968 |
| sbox_bp_d16 | 216.3 | 18 | 952.2 | 3670 | 1122.3 | 3822 | 120 | 12 | 1.179 | 1.041 |
| sbox_table | 786.9 | 11 | 3445.8 | 2288 | 2343.5 | 1648 | 378 | 6 | 0.680 | 0.720 |
| fdivp (ref) | 2166.1 | 289 | 9675.5 | 37984 | 8266.7 | 35611 | 1368 | 103 | 0.854 | 0.938 |
| fdivp_newton (ref) | 7892.5 | 252 | 33824.9 | 40031 | 31849.3 | 39161 | 4359 | 126 | 0.942 | 0.978 |
| flat_binary16 | 1944.8 | 303 | 8734.6 | 35735 | 7873.8 | 37868 | 1276 | 105 | 0.901 | 1.060 |

Over the 18 designs A1'/A0' is **0.93 in area (median; 0.68 to 1.23)**, **1.06 in delay (median; 0.72 to 2.40)** and 0.77 in cells
(the mapper's compound cells replace several abstract gates). A1' is area-leaning: the delay-first mapper `&nf` trades depth for area
on the carry chains (the ripple adder's 33 gates become 16 `maj3_1` cells in 6.3 ns, against 2.6 ns for A0''s two-gate-per-bit
chain). Rankings, best first, against the default score and A0':

| task | metric | order |
|---|---|---|
| add | area, GE = A0' = A1' | ripple < yosys < sklansky < kogge < cmpcarry |
| add | delay, A0' | cmpcarry < kogge < sklansky < ripple < yosys |
| add | delay, A1' | cmpcarry < kogge < sklansky < **yosys < ripple** (the maj3 chain: the proved ripple adder goes from 4th to last) |
| mul, the four proved | area, GE and A0' | array < tree_h < tree < wallace |
| mul, the four proved | area, A1' | tree < tree_h < wallace < **array** (8645 um^2 in A1', 8290 in A0'; the tree 7975 in A1', 8603 in A0') |
| mul, the four proved | delay, A0' and A1' | tree_h < wallace < tree < array in A1'; A0': wallace < tree_h (10 ps apart) < tree < array |
| mul, all seven | area, A0' | dadda_rc < array < tree_h < tree < yosys < dadda_ks < wallace |
| mul, all seven | area, A1' | dadda_rc < tree < tree_h < dadda_ks < wallace < yosys < array |
| aes_sbox | area | bp < bp_d16 < table in GE, A0' and A1' |
| aes_sbox | delay | table < bp_d16 < bp in A0' and A1'; the table design is 32% smaller under the mapper, the BP circuit 23% larger |

Kendall tau-b of the area rankings (`table --mapped`): GE against A0' / against A1' / A0' against A1': add +1.00 / +1.00 / +1.00;
**mul +0.90 / +0.33 / +0.24**; aes_sbox +1.00 / +1.00 / +1.00; fdivp +1.00 / +1.00 / +1.00. Delay: depth against A0' / against A1' /
A0' against A1': add +0.95 / +0.95 / +0.80; mul +0.59 / +0.88 / +0.43; aes_sbox +1.00 / +1.00 / +1.00; fdivp -1.00 / -0.33 / +0.33
(the area tau-b are `sky130_a0_v1`'s again; the ABC-sizing variant had add +0.60 / +1.00 / +0.60, mul +0.43 / +0.33 / +0.71, aes_sbox
+0.33 / +1.00 / +0.33). **Reading: A1''s disagreements with the default score are the mapper's, and the data are from one mapping
script.** `sky130.md` section 5.6 measured the same designs under the study's ABC scripts (A0', u, s, l, h, r): the same design's area
moves a median 12% (max 53%) and its delay a median 49% (max 154%) between them, which is larger than the rewrite sensitivity below.

**Determinism (measured).** The 16 designs, the 8 idioms and 5 more references (`add_proc`, `add_mux`, `add_n_byhand`,
`mul_n_byhand`, the aes_sbox `sbox_table` reference), 29 designs, four times: serially under a random hash seed; serially under
`PYTHONHASHSEED=1` with another `TMPDIR`; six at a time under `PYTHONHASHSEED=7` with a third `TMPDIR`; serially under
`PYTHONHASHSEED=0` with a fourth: **every column, every cell histogram and the sha256 of every scored AND mapped netlist identical in
all four runs** (serial 42 to 48 s, 6-way 13 s). `test_ppa.py` repeats it through the CLI (three hash seeds, two `TMPDIR`s, three
processes at once, byte-identical JSON), and the mapped numbers are exact integers (`area_e4um2_sky130_mapped_v1`, ps). The first study found ABC's mapper
single-threaded in this build (no thread option, child CPU time never above wall time).

Again 2026-11-05, the ranked flow alone (`ppa.py --no-mapped`) on the 52 references, baselines, records and trial designs
of the five ranked tasks, 16 runs each (14 for the three slowest; five serial runs under random, 0, 1, 7 and 4242 hash
seeds; three `TMPDIR`s, the system default included; three working directories; two checkouts; six runs of one design at
once; the file named `design.sv`, as `check.py` stages it, and `solution.sv`; `LC_ALL=C` and `de_DE.UTF-8`; the Yosys
binary through a second path): every area, delay, cell count, canonical RTLIL and scored and repaired netlist
byte-identical, and equal to every stored number (the 10 records, `score/measured`, `expected_ppa.json`, the built site).
ANOTHER BUILD: YoWASP's WebAssembly Yosys 0.53 (same git sha1, ABC linked in) gives the same numbers on 49 of the 52
designs and other ones on `fdivp`, `fdivp_newton` and `fdivp_d2` (area -0.32% to +0.15%, delay -0.79% to +2.85%; no order
on the fdivp board changes). The canonical RTLIL and the gates handed to ABC are identical in both builds, ABC's input
files are byte-identical, and the native `yosys-abc` gives the WebAssembly result on all 52 designs once the C library's
`qsort` is replaced by a stable merge sort: the difference is the tie order of `qsort` inside ABC's `map` (synth's
`abc -fast`), a property of the build's C library. Linux: not measured (no Linux run of the flow exists; CI runs no
Yosys). A Linux build is a different C library and may differ the same way.

**Structure sensitivity (deterministic; measured through the shipped code, `tests/canon/variants.py`).** Seven designs (`add_ripple`, `add_sklansky`,
`add_kogge`, `mul_array`, `mul_tree_h`, `mul_tree`, `sbox_bp`), nine rewrites each (layout, rename, hoisted declarations, reversed and four
shuffled item orders, all commutative operands swapped) and the original, 70 runs: the 21 layout and rename variants have a
byte-identical canonical RTLIL and **identical columns in both flows** (by construction); over the others the
largest movement is **A0': area 11.3%, delay 31.8%** (`mul_array`, commuted) and **A1': area 15.5%** (`sbox_bp`, commuted),
**delay 20.1%** (`mul_tree_h`, commuted); the real mapper erases most of the tree's area signature on the regular designs (at most
1.9% on all multipliers) but not the S-box's, and its delay is more sensitive than A0''s on some designs. These are the figures of the
first study (sky130.md section 6.2), reproduced here by the shipped `ppa.py`. These movements are deterministic (one text,
one number) and belong to the golfer: the board applies no tie band. Remeasured 2026-11-05 on four
designs (46 variants): renames, comments, blank lines and whitespace leave the canonical RTLIL byte-identical; reordering
independent statements moves `sbox_bp`'s delay from -0.6% to +17.7%, and moving the final adder's generate block ahead of
the leaves moves a proved carry-save multiplier's area +12.6% and delay +40.9%; all 21 changed netlists are equivalent to
their originals (ABC `cec`).

## ASAP7: an alternative library (`--pdk asap7`; `asap7_a0_v1`, `asap7_a1_v1`; 2026-11-09)

The question (2026-11-09): would ASAP7 be a better library than sky130? This section is the PORT, so that the two can be
weighed side by side on the same designs.
sky130 stays the default and the records' ranked score: with `--pdk` absent every sky130 number, record field (but
`ppa_script_sha256`) and repaired netlist is byte-identical to the scorer before the port (MEASURED on the eight designs
below and add_mux, both flows), and `score/test_ppa.py` (79 tests), `test_ppa_opensta.py` and `test_energy.py` pass unchanged.
The port is `score/ppa.py` sha256 `1ef1b1c1904853711cbed9b3b5e275f333aade8f60361f8bbc61305c98c480ab`. Records made
before it name the scorer before the port, sha256 `912031912c3e3f6790725161753e95415df34846bd8c27dde3eb707747ddbcbe`
(`checker.files` and `ppa_script_sha256`), and are not made again: rescoring each with the port reproduced every stored
sky130 field but that hash, `ppa.mapped` included (MEASURED 2026-11-11 on all 23 records of the board). Since 2026-11-12 the file
also prints one summary line on stderr after the JSON and takes `--latency` (sha256
`2be8c01e931a3b640c1d3a4104ffe06d8fd3f0e48737d5222e78ed5f58747150`); the JSON is unchanged but for that hash (rescored:
every stored sky130 field of all 23 records and every ASAP7 entry reproduced, MEASURED 2026-11-12). `leaderboard.py
verify` notes the changed file; a note never changes a record's status.
**Decided 2026-11-09: a reader may choose ASAP7** (a dropdown on the front page lets the reader see the golf scores on
sky130 or on ASAP7): the site's library selector shows every golf score on sky130 (the default) or on these
A0' columns, both views ranked by `leaderboard.py` at build time (`board --pdk asap7`). The ASAP7 columns of every record,
proved reference and baseline are kept in `leaderboard/asap7/<task>.json`, bound to each record's scored netlist and
re-derived by `leaderboard.py verify` and `asap7 --rescore` (leaderboard/README.md, "The ASAP7 view"; README.md,
"Scoring", "The ASAP7 view").

    python3.12 score/ppa.py --pdk asap7 --fetch-liberty                     # five files into score/lib/asap7/ (git-ignored)
    python3.12 score/ppa.py --pdk asap7 SOLUTION.sv --task tasks/<name>      # A0' (+ A1' for a combinational task)
    python3.12 score/ppa.py --pdk asap7 SOLUTION.sv --task tasks/<name> --seq
    python3.12 score/test_ppa_asap7.py                                       # $SVGOLF_ASAP7_LIB: a directory of the five files

**Same flows, same rules.** The scored netlist of `score.py` (unchanged), re-expressed cell by cell, repaired by the same
`buffer_trees_v1` buffering (no resizing, no restructuring), written as Verilog, read back, simulated against the unrepaired
netlist and weighed by the same STA; an illegal netlist is rejected with the nets named; nothing is extrapolated above a
table's grid; bit-exact run to run. A1' is the same `abc -liberty` script on the library's combinational cells. The columns
carry the library's name (`area_um2_asap7`, `area_e5um2_asap7`, `delay_ps_asap7`, `cells_asap7`, `cell_hist_asap7`; A1':
`area_um2_asap7_mapped_v1`, `mapped_delay_asap7_v1`, ...) plus `"pdk": "asap7"` and `liberty_files`, so a board can never
read an asap7 number as a sky130 one.

**What the library forced** (each pinned in `score/ppa_pins_asap7.json` with its reason in a `_why` entry; the measurements
with the ported `ppa.py`):

* **The library**: asap7sc7p5t rev 28, RVT, TT (0.70 V, 25 C), NLDM; five files (INVBUF, SIMPLE, AO, OA, SEQ: 202 cells),
  fetched gzipped from OpenROAD-flow-scripts `a1a6c3ff` (the four `.lib.gz` and the plain SEQ file; compressed and
  uncompressed sizes and sha256 pinned, the git blob sha1 recorded), not vendored; each file carries its BSD-3 header. TT
  because sky130's pin is its typical corner; not FF (ORFS's default), whose SIMPLE file is a 2025 re-characterization by
  another Liberate version than its siblings. A library of several files has one identity, `liberty_sha256` = SHA-256 over
  `<file> <sha256>` lines (`5ece07ac...`), each file's hash in `liberty_files`.
* **Units**: ps and fF, converted to ns and pF as the files are read (one division by 1000; sky130's numbers are read
  exactly as before). Areas have five decimals: integers in 1e-5 um^2. Cell names have a suffix (`_ASAP7_75t_R`); cell names
  are unquoted; the 37 INVBUF cells and five SEQ cells have no semicolon after `area` (the line end closes it, as Yosys and
  OpenSTA read it; sky130 has no such line). The SIMPLE file declares `default_max_transition` 4000 ps, the others 320 ps:
  a library of several files takes the smallest (every asap7 input pin declares 320 ps and every table ends at 320 ps).
* **Gates**: each Yosys gate is its least-area build of at most two cells (exhaustive search; ties: fewer cells, larger
  max_capacitance, faster FO4): NOT `INVx1`, NAND `NAND2xp5`, NOR `NOR2xp33`, AND `AND2x2`, OR `OR2x2`, XOR `XOR2xp5`, XNOR
  `XNOR2xp5`, and, the library having no MUX2 and no A&!B / A|!B cell, MUX = `INVx1` on S + `AO22x1`, ANDNOT = `INVx1` on A +
  `NOR2xp33`, ORNOT = `INVx1` on A + `NAND2xp5`. In NAND2 units: 0.75, 1, 1, 1.5, 1.5, 2.25, 2.25, 3.0, 1.75, 1.75 (sky130: 1,
  1, 1, 1.667, 1.667, 2.333, 2.333, 3.0, 1.667, 1.667). A build's helper cell is a real cell (weighed, timed, repaired) but
  not a gate of the unit depth, which stays `ltp -noff`'s.
* **The flop**: every asap7 positive-edge flop but the x4 has QN only. `$_DFF_P_` = `DFFHQNx1` + `INVx1` forming Q (0.33534
  um^2, 8% under `DFFHQx4`; clock-to-Q 63.0 / 69.5 / 99.0 ps at Q loads of 1 / 2.5 / 10 fF against 73.0 / 74.6 / 83.3).
  `ppa.py` checks from the `ff` group that QN is !D of the last rising edge; asap7 stores its setup tables with the D
  transition first, so they are read transposed (a latent assumption of the sky130 code, now checked on both).
* **Timing setup**, scaled by sky130's own stated reasons (design/ppa/sky130.md:187-188): the input ramp and the ideal
  clock's transition 20 ps (sky130's 50 ps sits at 55% of a min-size inv/nand2/buf output into two inverter pins, 27.6 to
  68.2 ps; the same measurement on asap7 is 9.7 to 25.8 ps, 55% of it 18.6 ps, and 20 ps is a grid point); the output load
  2.5 fF per bit (sky130's 10 fF is 4.18 inverter inputs; 4 `INVx1` inputs are 2.48 fF); the input drive `BUFx8` (sky130's
  `buf_8` may carry 407 `inv_1` input loads, `BUFx8` 433 `INVx1` input loads, the nearest asap7 buffer). Allowed input
  drives: every BUF and INV of INVBUF; no flop (asap7's has no Q).
* **Constants**: `TIELOx1` and `TIEHIx1` (a cell per constant, not one `conb_1`), replicated as `conb_1` is. They declare no
  max_capacitance: 46.08 fF is pinned (`INVx1`'s, the same size and area).
* **Below a grid**: asap7's grids start at max_capacitance / 64 (0.36 fF for the xp cells, 0.72 fF for `INVx1`), above most
  single input pins (`INVx1` 0.62 fF), so sky130's rule (a read below a grid rejects) would reject almost every fan-out-1
  net. asap7 reads below a grid at the grid's floor in that dimension, counts it (`legality.table_reads_floored`) and keeps
  sky130's rule above a grid. Every asap7 delay table rises from its first point along both axes (MEASURED over the 20,162
  tables the flow can read, and checked by `test_ppa_asap7.py`), so a floored delay errs slow; transitions are flat there
  (at most 0.39 ps).
* **A1'**: the four combinational files, SIMPLE first: the pinned `yosys-abc` (ABC 1.01 of 6 May 2025) dies with a
  segmentation fault when INVBUF is the first `-liberty` file (MEASURED). `-dont_use` excludes exactly the non-logic cells
  of the asap7 cell policy (clock inverters, hold buffers, FA/HA, tie cells).

**Measured** (2026-11-09; A0' at the tasks' scoring points, rating build; area um^2 / delay ps; the clocked rows' delay is the
register-to-register period):

| design | sky130 A0' | asap7 A0' | ratio area, delay | sky130 A1' | asap7 A1' |
|---|---|---|---|---|---|
| add_n (add, N=16) | 460.4416 / 2611 | 6.99840 / 563 | 65.8x, 4.6x | 440.4224 / 6279 | 7.10046 / 328 |
| mul_n (mul, N=16) | 8290.4512 / 10907 | 123.93000 / 1981 | 66.9x, 5.5x | 8644.5408 / 16391 | 110.91006 / 1784 |
| mul_wallace | 8966.0992 / 5982 | 133.91730 / 1186 | 67.0x, 5.0x | 8398.0544 / 7374 | 115.42986 / 913 |
| sbox_bp (aes_sbox) | 892.1056 / 4297 | 13.35528 / 704 | 66.8x, 6.1x | 1094.8 / 4160 | 12.21804 / 653 |
| sbox_table | 3445.8048 / 2288 | 51.81732 / 373 | 66.5x, 6.1x | 2343.4976 / 1648 | 29.69946 / 291 |
| rr_mask (arbiter, N=8, clocked) | 769.488 / 2826 | 12.15972 / 464 | 63.3x, 6.1x | | |
| matmul_g1 (matmul, clocked) | 87173.6064 / 10696 | 1334.7261 / 1539 | 65.3x, 6.9x | | |
| sorter_ins (sorter, clocked) | 5512.7872 / 2523 | 85.68666 / 512 | 64.3x, 4.9x | | |

Over the 19 designs of `score/tests/ppa/designs.json` (A0', banned baselines included), the area ratio is 65.8x to 68.3x and
the area order within every task is the same on both libraries (Kendall tau 1.0 in add, mul, aes_sbox, fdivp); the delay
ratio is 4.6x to 6.1x and the delay order moves in mul (tau 0.62) and fdivp (0.67); area x time moves in add (0.40), mul
(0.71). Repairs are few on both (matmul: 6 buffers on asap7, 6 on sky130). Records are bit-identical over two runs in
separate processes with different hash seeds (all nine designs, JSON and repaired netlists).

**Not claimed for asap7.** It is a predictive kit ("the resulting designs are not manufacturable", asap.asu.edu): its
numbers are a model of a 7 nm process, not of a fabricated one. No wires, as on sky130, but at 7 nm the resistive lower
metal is a larger share of real delay than at 130 nm, so a wireless STA claims less on asap7. The floored reads are an
upper bound on delay, not a characterization. Licence (decided 2026-11-10): only files of a public BSD-3 repository are
used: the five liberty files of OpenROAD-flow-scripts at commit `a1a6c3ff933391161089e65e0af92324e41aefa3`
(`score/ppa_pins_asap7.json`), each with its BSD 3-Clause licence in its header, fetched at pinned hashes and never
vendored. Nothing comes from the ASU download page, whose academic, non-commercial, no-redistribution terms cover other
material (the gated Calibre decks).

## ASAP7 placed and routed (the routed course; decided 2026-11-11 and 2026-11-12)

The site's second course (README.md, "How the routed course is scored"; leaderboard/README.md, "The routed course").
Every number in this section is MEASURED by the 2026-11-11, 2026-11-12 and 2026-11-13 campaigns on one host type
(x86-64 Linux, Intel Xeon Platinum 8488C, Rocky Linux 9.8, the image unpacked into a rootless user namespace and
chroot). Since 2026-11-13 every design file the tasks show (39) has a routed score; "the scored runs" below are those
39 runs.

**What is placed.** The design's ASAP7 netlist as the ASAP7 view above writes it: `ppa.py --pdk asap7`'s repaired
netlist (`--repaired-netlist`; its sha256 is the view entry's `repaired_sha256`), cells only. Nothing is synthesized
again: the placed netlist (ORFS's `1_2_yosys.v`) is that file, checked by sha256 on every run.

**The flow.** OpenROAD-flow-scripts from the image `openroad/orfs`, tag `26Q4-262-g3ff0197f0`, used by digest only
(amd64 manifest `sha256:df7ba49c0bc2bcdfc353b9fc75a17dac489200c239967564bc25d6bd40462c21`), platform `asap7`, the
minimal flow `min_v1`: core utilisation 40%, aspect ratio 1, placement density 0.60, no timing-driven placement, no
timing repair at floorplan, placement or clock-tree time, no power recovery, no flop clustering, ports not buffered,
the typical corner, the flow's equivalence check on (`LEC_CHECK=1`). Two threads, two CPUs, an 8 GB memory cap without
swap, no network, inputs read-only. `score/pnr/pins.json` pins all of it (and the sha256 of the scripts that render a
job's config.mk and SDC: `score/pnr/gen_course.py` and `gen_course2.py`, kept byte for byte; `score/pnr/job.py` renders
the same text from the tree); a result made under other pins is stale. **The SDC** sets one clock whose period is the ASAP7
view's delay of the design (its `delay_ps`); on a combinational design a virtual clock constrains input to output.
In the minimal flow nothing optimises against the period, so it is only the reference the slack is measured from
(that the layout does not depend on it is NOT MEASURED).

**The score.** Area: the routed netlist's cells (`6_final.v`) by the pinned ASAP7 liberty, summed exactly in 1e-5 um^2
(the buffers and clock tree the flow adds included; tap, fill and the die not), checked against ORFS's printed stdcell
area less its tap cells. Time: the clock period minus ORFS's worst setup slack after routing, with the parasitics
extracted from the layout, rounded half-even to whole ps (checked within 0.01 ps of ORFS's own `period_min`); on a
clocked task, times the cycles. Score = area x time (`combined.py`, `AREA_SCALE["asap7pnr"]`, 1e-5 um^2 x ps).
**Valid**: ORFS exit 0, detailed-route DRC 0, and every equivalence log printing "Circuits are IDENTICAL" (the
positive line is required; the flow itself passes a run on the absence of a "Found difference" line). Recorded, not
scored: hold violations (no hold repair: every clocked run ends with some, 13 to 288 on the 8 clocked scored runs) and
slow-signal (max-slew) warnings (4 of the 39 scored runs; the record page names the count).

**One run per design.** The seed (`GPL_RANDOM_SEED`, global placement) is the request's: the seed a submission names,
else one drawn at random once and kept with the record (decided 2026-11-11). A request is stored before the run with
`leaderboard.py asap7pnr --request` (the seed `--seed` names, source `record`; else one drawn from the operating
system's random source, source `drawn`), as the design's pending entry, and is never changed; the run itself is still
made by the maintainers on the course host. Every design so far (2026-11-11 to 2026-11-13) ran at seed 1 (source
`default`). Detailed placement's own seed is 1 in every job. On the 23 records of 2026-11-11, seeds 1, 2 and 3 differ by 0 to 2.8% of the median area x time; their median
(`v_median`) is kept as an unranked extra (on the 21 entries still shown that were measured then) and never ranks; the
later campaigns ran seed 1 only.

**Measured.** Repeatable on the same host type: 3 of 3 re-runs of a seed (2026-11-11), 4 of 4 netlists placed earlier
under other job names (2026-11-12) and 13 of 13 (2026-11-13) gave the same `6_final.def`, `6_final.v`, `6_final.odb`
and stage databases, byte for byte. Cost per scored run, two threads: 65 to 109 s and 0.7 to 0.9 GB up to 2,476 cells;
152 s and 1.2 GB at 6,045 cells; 4 to 7 min and 1.7 to 2.5 GB at 12,889 to 22,872 cells; 698 s and 4.1 GB for the
41,035-cell matmul record. The wire cost, routed area x time against the cells-only A0' of the same netlist, ranges
from -55.4% (`_example`) to +35.0% (the table S-box); neither end is analysed yet. The flow added cells (clock-tree and
repair buffers) in 14 of the 39 scored runs: at most 2.2% of a design's cells (3 on the 138-cell arbiter), 509 on the
41,035-cell matmul record.

**The pictures.** OpenROAD's own renderer, off-screen inside the pinned image, draws the scoring run's
`6_final.odb` in the flow's routing view (every layer, net and instance; power and ground nets hidden) at 1600 px; the
PNG is then encoded as WebP (Pillow 11.1.0, libwebp 1.5.0, method 6) at the largest long side of 1600 to 1000 px whose
quality 80 to 50 (in steps of 5) fits in 300,000 bytes, with a 640 px thumbnail at quality 80. Six of the 39
pictures were encoded again from the same render at the same size one quality step away (79, 74, 71, 69, 54), so that
their bytes pass the publication scan; each entry records its picture's quality. Two renders of one database gave the
same PNG bytes (2 of 2 on 2026-11-12, 2 of 2 on 2026-11-13), and two encodings of all 45 pictures of 2026-11-12 the
same files.

**The ASAP7 files** (as decided 2026-11-11 by the maintainers: only files of a public BSD-3 repository). The routed
course uses the `asap7` platform of OpenROAD-flow-scripts as the pinned image ships it (repository
The-OpenROAD-Project/OpenROAD-flow-scripts, the image's revision `3ff0197f0` per its tag; `flow/platforms/asap7`, whose
ASAP7 files come from The-OpenROAD-Project/asap7, BSD 3-Clause). Its five liberty files are byte-identical to the ones
`score/ppa_pins_asap7.json` pins (commit `a1a6c3ff`, each with its BSD 3-Clause header), so routed timing reads the
tables the ASAP7 view reads. None of the platform's files is in this repository (only the layout pictures drawn from the
routed databases are), and nothing comes from the ASU download page. The full commit hash of the image's
OpenROAD-flow-scripts is not recorded beyond its tag (an open item).

**What the equivalence check shows, and the negative control.** The flow's own check (step `6_report`, with
`LEC_CHECK=1`: kepler-formal on `1_synth_lec.v` and `6_final_lec.v`) compares the routed netlist with the flow's
rendering of the netlist the run was given (`1_synth_lec.v` is written from `1_synth.odb`, which is `1_2_yosys.v`, the
job's input, loaded): it shows
that place and route preserved the input, not that the input was the design's netlist. The runs of the two changed
netlists below both passed it. That the input is the design's ASAP7 netlist is checked by sha256: `1_2_yosys.v`'s
hash must be the entry's `netlist_sha256` and the ASAP7 view's `repaired_sha256`, and a run of a changed netlist is
refused there (`asap7pnr`: "the placed netlist (1_2_yosys.v) is not the entry's netlist_sha256"; the binding:
"unbound: its routed netlist is not this design's ASAP7 netlist"). The negative control (2026-11-13, MEASURED): one gate
changed in each of two par designs, keeping its pins and area (add_n: an XOR2 driving `s[4]` made an XNOR2; sorter_ins:
an AND2 feeding a register made an OR2), each changed netlist placed and routed under the course's pins; then the same
kepler-formal with the flow's own configuration of each case, its inputs set to the unchanged netlist and the case's
routed netlist, reported "Found difference ... Circuits are DIFFERENT" for both changed netlists against both forms
of the unchanged one (the file the course binds, and the flow's `1_synth_lec.v` of a run of it): 4 of 4; and "Circuits
are IDENTICAL" for the two unchanged runs against the same references: 4 of 4. kepler-formal exits 0 in both cases;
its verdict is read from its log, as the flow does. This comparison is not a pinned step of a run: the results carry
the flow's own verdict only. `score/pnr/lec.py` makes this job for a run (the bound netlist file as the reference) and
reads its log (IDENTICAL, DIFFERENT, or no verdict for anything else); it is a tool, not part of a run's validity.

**Not claimed.** One corner, setup only, no hold repair, no power: not sign-off, on a predictive library that was
never fabricated. Docker, other x86-64 hosts, a GitHub-hosted runner and Apple silicon are not measured (the image is
amd64 only). The run tools are in `score/pnr/` (its README: the job files, the runner by digest, the picture, the
collector and the check of collected data): the `config.mk` and SDC they write are those of every committed run, byte
for byte (97 runs), and their collector rebuilds the committed `_example` table from a stored run; no run has been made
with their container runner yet (the committed runs ran the image unpacked into a rootless chroot), so a run made
again from the repository alone is expected, not shown, to give the committed numbers. A request can name a seed
(`leaderboard.py asap7pnr --request`), but the run itself is still made by the maintainers on the course host.

## What is NOT claimed

* **(Superseded 2026-11-03 and 2026-11-04.)** A0' is the ranked sky130 score, and an electrically illegal repaired A0' netlist is a
  reason to reject a submission (check.py's `ppa` stage); `(area_ge_v1, depth_v1)` are unchanged extra columns.
* **Ranking, not picoseconds.** One library, one corner, no wires, a 130 nm process, uniform fixed loads; A0' is buffered
  where it is electrically illegal and nowhere else, nothing resized (a repair, not timing closure) and A1' has the mapper's
  cell choice but no sizing or buffering pass. The STA equals **OpenSTA** to 1 fs per arc on the same netlist and setup
  (`score/test_ppa_opensta.py`, "The per-edge loads"; an explicit input buffer, not `set_driving_cell`) and is compared with
  ABC's `stime` (above). Equal to OpenSTA is not equal to silicon: the corner, the missing wires and the fixed loads stay.
* **No noise band.** The ranked numbers are exact and deterministic: the same design text through the pinned flow and build
  gives the same integers on every run, so the board ranks them as they are (area x time) and a difference of any size is
  real. What looks like noise between similar designs is the flow's deterministic sensitivity to how the circuit is
  written (operand order, grouping, statement order: up to 11% in area and 32% in delay for commuted operands, 12.6% and
  41% for one moved generate block), and finding the better form is golf.
* **A0' versus A1' (decided 2026-11-01: neither official; superseded 2026-11-03: A0' ranks, A1' is research).** A0' prices the
  netlist the default score already ranks, repaired; A1' is a real `abc -liberty` mapping, closer to a fabricated chip and more
  sensitive to the mapper. A contestant who golfs for A1' is optimizing one ABC script on one liberty; the board never compares
  a number of one flow with the other's.
* **A1' is one mapping script, not "the" mapped result.** Other scripts (the `s`, `l`, `h`, `f`, `r` variants of the study) move
  the same design a median 12% in area and 49% in delay. The equivalence check is a sample of 2048 vectors, not a proof.
* No hold check, no clock tree, no clock skew: a clocked design (`--seq`, PLAN4 Gate 2) is weighed as its register-to-register
  period (latest D arrival plus setup, from an ideal clock with the input ramp's transition), flops included in area. Energy is
  `score/energy.py`'s unranked columns, on the same repaired netlist.
* `ppa.py` reads a liberty cell function with `&` binding tighter than `^`, while Liberty binds `^` tighter; no function
  string in the pinned sky130 or ASAP7 files contains `^` (MEASURED 2026-11-11), so nothing is misread today.

## Wiring (2026-10-31; flow A1' 2026-11-01)

Decision (2026-10-31): wire the columns in as EXTRA columns. The default board `(area_ge_v1, depth_v1)` stays the ranking, nothing
a contestant could submit before is rejected, and `check.py`'s output for every existing field is byte-identical (below).
Golfers can run ABC themselves and submit the best-scoring design; the columns record, they do not rank. (Superseded: 2026-11-03 A0'
is the ranked sky130 score; 2026-11-04 the `ppa` stage REJECTS a design whose repaired netlist is electrically illegal, the one kind of
design the stage rejects; "The repair and the legality check" above; 2026-11-04 the boards rank A0''s area and time, with GE and
depth as extra columns.)

**`check.py`.** After the `postsynth` stage (the netlist is verified before it is weighed; a design that is rejected is not
weighed) the `ppa` stage weighs THE netlist file the score stage kept and postsynth simulated: no second synthesis, and
`netlist_sha256` equals `stages.postsynth.netlist_sha256`; the stage CHECKS that (the bytes it reads must hash to what postsynth
recorded), so a file replaced between the two stages is an infrastructure error, never a number. The result gets the key `ppa` (an
object, never mixed into the score fields) and `stages.ppa = {"mode", "seconds"}`. Measured: under `auto` the stage takes
0.11 to 0.13 s (the liberty's hash and cell scan, about 0.10 s, then the STA); under `--ppa require` the liberty is opened before the first stage, so
`stages.ppa.seconds` is 0.00 to 0.02 s and the same ~0.10 s is spent up front. The weighed netlist's unit depth and cell count must equal the score
stage's `ltp -noff` depth and gate count (+1 for the priced tie cell): a disagreement means the two readings of the netlist differ,
and nothing is reported (`auto`) or the run is an infrastructure error (`require`).

| `--ppa` | liberty present | liberty absent, unreadable or not the pinned file |
|---|---|---|
| `auto` (default) | `ppa: {"available": true, ...the columns...}` | `ppa: {"available": false, "reason": "liberty not found: ..."}`, one line on stderr, nothing else changes |
| `require` | the same | an infrastructure error before any other work (exit status 2, `stage: "infrastructure"`): competitions, `leaderboard.py add`/`verify --full`, and `tests/run.py` where the liberty exists |
| `off` | no `ppa` key, no stage, no stderr line | the same (the liberty is never looked at) |

What can still be `ppa: {"available": false, "reason": ...}`, and what is an infrastructure error (exit status 2, no verdict) instead:

| situation | `auto` | `require` |
|---|---|---|
| liberty absent, unreadable (permissions) or not the pinned file | `available: false` + reason | infrastructure error, before any work |
| the pinned flow cannot weigh THIS netlist (a cell outside the A0' table, an undriven net, an x/z bit that is read, ...) | `available: false` + the loud reason | the same (never fails the check; `leaderboard.py add` records the reason) |
| the REPAIRED netlist is electrically illegal (a load over `max_capacitance`, a transition over `max_transition`, a timing-table read outside its grid; `sky130_a0_v2`) | REJECTED at stage `ppa`: `available: false, illegal: true`, the reason and the `legality` counts | the same |
| the repaired netlist is not the scored circuit on the 2048-vector sample (`RepairDefect`: the repair's or the reader's fault) | `available: false` + `the repaired netlist is not the scored circuit: ...` | infrastructure error |
| `ppa.py` raises something other than its own refusal (a defect of `ppa.py`) | `available: false` + `ppa.py failed on this netlist: ...` | infrastructure error |
| the weighed netlist's depth or gate count differs from the score stage's | `available: false` + the numbers | infrastructure error |
| the netlist file is not the one postsynth verified (sha256) | infrastructure error | infrastructure error |

So "never fails the check" is exact for what a DESIGN can do, with ONE exception since `sky130_a0_v2` (2026-11-04): a design whose
repaired netlist is electrically illegal is rejected at `ppa`. (A design can still be rejected BEFORE the `ppa` stage, by a stage
the wiring did not touch: "Known gap" below.) A comb-family task's flow refuses a flip-flop (so does its score stage); a
clocked task's `score_clocked` weighs its `--seq` netlist through this same stage under `require`, and the ranked clocked score
IS that block. The integrity tripwire fingerprints `score/ppa.py` and `score/ppa_pins.json`
by content with the other trusted scripts (the liberty is not in it: its sha256 is verified on every load).

**Flow A1' in the same stage (2026-11-01).** The `ppa` block of a weighed design also carries `mapped` (the sub-object of "Columns"; `ppa`
minus `mapped` is exactly what it was, so a reader from before 2026-11-01 still validates every record). The score stage now keeps the
canonical RTLIL of its run (`score.score(rtlil_out=...)`, asked for only when `--ppa` is not `off`; its sha256 is the `rtlil_sha256` the
score stage already records, and the stage CHECKS that the file it maps hashes to it, like the netlist), and after the A0' weighing the
stage maps that RTLIL in one more Yosys process (through the same sandbox as the pinned flow, reading only the RTLIL and the liberty),
checks the mapped netlist against the scored one and weighs it. `stages.ppa` gains `mapped_seconds` (`seconds` is the total; measured
0.3 to 1.4 s on the references, 3.6 s for the 760-cell `sbox_logexp`); `--ppa off` maps nothing; the stderr line is
`ppa: mapped (A1', real abc -liberty): ... um^2, ... ps, ... cells, ... levels (sky130_a1_v1; extra column)`.
What can still be `mapped: {"available": false, "reason": ...}`, and what is an infrastructure error instead (the A0' columns and the verdict
are never touched):

| situation | `auto` | `require` |
|---|---|---|
| the mapping run fails or times out (Yosys error, `yosys_timeout_s`), a cell outside the policy, a netlist the reader or STA cannot handle | `mapped.available: false` + the loud reason, the check goes on | the same (never fails the check; `leaderboard.py add` records the reason) |
| the mapped netlist computes another function than the scored one on the equivalence sample (`MappedDefect`) | `mapped.available: false` + `the mapped netlist is not the scored circuit: ...` | infrastructure error |
| `ppa.py` raises something other than its own refusal while mapping | `mapped.available: false` + `ppa.py failed on this design's mapping: ...` | infrastructure error |
| the canonical RTLIL (or the netlist) is not the file the score (postsynth) stage recorded (sha256) | infrastructure error | infrastructure error |
| the mapped-flow pins or script unreadable | `mapped.available: false` + reason | infrastructure error, before any other work |

The integrity tripwire also fingerprints `score/ppa_mapped.ys` and `score/ppa_mapped_pins.json` by content (and the leaderboard's
`checker.files` records their hashes).

**Known gap, not of this stage.** The `postsynth` stage lints the scored netlist with Verilator `-Wall`, every warning fatal but two, and UNDRIVEN is
fatal; and it refuses an unknown literal (`1'hx`) that a gate, a flip-flop or an output reads (since 2026-11-11 one that nothing reads
is accepted). The dead public-named wires of some techmapped cells are only partly driven, so some ordinary designs are refused at `postsynth` ("the scored netlist does not compile: verilator rejected it ... Bits of signal are not
driven") before the `ppa` stage runs, in every `--ppa` mode, with or without a liberty. Found while testing the reader (`check/postsynth.py` is
unchanged since before the wiring); this one, on the `aes_sbox` task, stops at stage `postsynth`:

```
module aes_sbox (input logic [7:0] x, output logic [7:0] y);
  logic [7:0] s;
  assign s = {x[3:0], x[7:4]};
  always_comb case (x[1:0])
    2'd0:    y = x;
    2'd1:    y = s;
    2'd2:    y = x & s;
    default: y = x | s;
  endcase
endmodule
```

The designs of `tests/checker/ppa_wiring/dead_wire_designs/` (a run-time shift, a one-hot decode, a run-time bit select) do pass `postsynth`
and reach the `ppa` stage with dead wires in their netlists. What to do about the refusal is a decision about the pinned flow and the postsynth
policy (for example writing the scored netlist without its dead public wires changes `script_sha256`). For the COMBINATIONAL flow it is not
made here.

**Closed for the clocked flow (decided 2026-11-07).** `score/svgolf_seq.ys` ends with `opt_clean -purge` instead of `opt_clean`: the last
clean-up also removes internal nets that have a public name (Yosys's `help opt_clean`), the dead techmap wires among them, so the scored netlist
no longer carries them; it removes wires, never a cell or a port. MEASURED (2026-11-07, Yosys 0.53, the reference build): the correct rotating-priority
arbiter `tests/arbiter/designs/rotate.sv`, refused at `N = 8` before (`Bits of signal are not driven: '_269_.B'[1]`; `tasks/arbiter/README.md`,
F6), is lint-clean at `N = 3, 5, 8` with the same gates, GE and depth (310.294 GE, depth 13 at `N = 8`); the reference `rr_mask`'s netlists are
byte-identical at `N = 3, 5, 8`. Over every clocked `.sv` of the tree (163 designs: tasks/arbiter, matmul, sorter and the tests of
those, `tests/seq_counter`, `tests/seq_tx`; 247 (design, point) runs at the points the checks use, 20 of them refused by the gate or Yosys under
both scripts): in the 227 that synthesize, every gate mix, GE, depth and flop count is the same, 185 netlists are byte-identical and 42 differ
in wire names; the netlist lint passes 13 it refused (12 UNDRIVEN on a dead techmap wire: `rotate.sv` and the attack `a09_rotate_pow2` at
`N = 8`, the three FSM fixtures of `tests/seq_counter/never_loaded/`, which now pass every stage but the proof, and seven fixtures of
`tests/seq_counter/xsafe/`; one UNOPTFLAT) and refuses 2 it passed, both UNOPTFLAT, a FALSE combinational loop: the netlist assigns one bit
of an output vector from another (`assign { q[7:2], q[0] } = { 6'h00, q[1] };`), and Verilator's lint, at vector granularity, calls that
circular when a lower bit reads a higher one. The two are the wrong `matmul` attack `acc_2w` at `(4, 8, 32)` (its pinned check is at
`solution`) and the `/` fixture `xsafe/d3_sdiv.sv` (banned anyway); one more fixture, `xsafe/c2_rt_div.sv`, moves from UNDRIVEN to
UNOPTFLAT. The same false loop meets a CORRECT idiom: two registers each sign-extended into one half of an output (a narrow accumulator
widened to the port, as a `matmul` golfer may write) passes the lint with plain `opt_clean` and is refused with `-purge` (MEASURED on a
probe outside the tree; a one-register sign extension passes both). Which bit Yosys keeps as the driver of an aliased group decides it, so
the UNOPTFLAT over-rejection exists under both scripts (`xsafe/d1_ashr_signed.sv` was refused by it before); it is recorded here, not
changed: the netlist lint's policy is a separate decision (changed 2026-11-13: loops are refused bit by bit and UNOPTFLAT is waived,
`check/postsynth.py` `comb_loops` and `NETLIST_WNO`). Of the pinned hashes, only the script hash of the clocked flow changed (the
table above, `tests/expected.json` `flow_seq`, `score/measured/`); `svgolf.ys` and every combinational hash are unchanged.

**Fields of `ppa`** (`available: true`): the A0' columns of the table above (`ppa.py`'s `columns`), `available`, `mapped` (flow A1', above), and four more:

| field | meaning |
|---|---|
| `constants` | boolean: a literal sits on a cell pin or an output bit, so ONE `conb_1` is priced (it is in `cells_sky130` and `cell_hist_sky130`; `cells_sky130 - 1` is the score stage's gate count then) |
| `critical` | `{"output": the output bit (the netlist's own name) the latest arrival ends at, or null with no path, "edge": "r" or "f", "cells": the number of cells on that path}` |
| `setup` | the timing setup: `{"pi_slew_ps": 50, "input_drive": "sky130_fd_sc_hd__buf_8", "po_load_ff": 10, "wires": "none", "tables": "no extrapolation"}`, `input_drive` the task's (`sky130_a0_v3`; v2 recorded `"pi_driving_cell": "buf_1"`) (A1''s `mapped.setup` stays `{"pi_slew_ps": 50, "po_load_ff": 10, "wires": "none"}`) |
| `liberty_file` | the file name of the pinned liberty |

**The liberty.** Fetched, not vendored (licence above): `python3.12 score/ppa.py --fetch-liberty`, once per checkout, into `score/lib/`
(git-ignored); or `SVGOLF_SKY130_LIB=/path/to/copy` (the hash is checked on every load); both flows use this one file. Flow A0' is
`ppa_version` `sky130_a0_v3`, flow A1' is `ppa_mapped_version` `sky130_a1_v1` (a change of `ppa_pins.json`, the STA, the cell table or the
repair changes the first; a change of `ppa_mapped.ys`, `ppa_mapped_pins.json` or the Yosys/ABC build changes the second).

**Leaderboard.** `leaderboard.py add` runs `check.py --ppa require --postsynth full` and stores the block as the optional record key
`ppa` (the schema string is unchanged; records without it stay valid and verify as before; a `leaderboard.py` from before the
key treats a record that has one as corrupt, so readers are updated first). `add --from-check RESULT.json` records a stored result as it is: a
`require` result with its block, an `auto` result that found no liberty is refused, a result without the key (`--ppa off`, an older checker)
gives a record without the columns and a NOTE. `verify` compares the columns exactly when the weighing is the same (`ppa_version`,
liberty and pins hashes equal, and the same Yosys flow: under another flow a record is `stale` and neither score nor columns are
compared), and says so with a note when it cannot (the default level re-weighs through `ppa.py` and needs no liberty to pass;
`verify --full` rechecks a record that has columns with `--ppa require`, and a record made before the columns with `--ppa off`, so
legacy records verify as before on a machine without the liberty). `pareto --axes area_um2_sky130,delay_ps_sky130` is the opt-in
n-dimensional frontier. See `leaderboard/README.md`.
Flow A1' rides in the same record key as the sub-object `ppa.mapped` (an old `leaderboard.py` accepts it: extra keys of `ppa` are
allowed): `validate_mapped` checks its shape and arithmetic, `ppa_score_problems` that it read the record's own canonical RTLIL,
`verify` compares the mapped columns exactly under equal `ppa_mapped_version`, liberty, mapped pins, script, Yosys and ABC builds and
says so with a note otherwise (`verify --full`, which runs `--ppa require`, FAILS a record whose mapped columns it can no longer
reproduce or map; a record made before 2026-11-01 or whose design the mapping could not weigh is not compared on them), and
`pareto --axes` takes `area_um2_sky130_mapped_v1`, `mapped_delay_sky130_v1`, `mapped_cells_sky130_v1`, `mapped_levels_sky130_v1`
beside the A0' axes (axes of both flows may be mixed; each is read from its own flow, and records under another mapped identity or
without the sub-object are listed "not shown" with the reason).

**Tests.** `tests/checker/test_ppa_wiring.py` (modes, absent and unreadable liberty, byte-identity, the swapped-netlist check, `aes_sbox`
designs with dead wires in their netlists through check.py's stages, tripwire),
`tests/leaderboard/test_leaderboard.py` (the record key, the axes view, and `ppa.mapped` of both), `score/test_ppa.py` (the reader on escaped identifiers and dead
wires, on a synthetic liberty; flow A1' on the synthetic liberty: weighing, equivalence sample, pins, reasons, timeouts; the idiom designs with goldens on the real one, and the
A1' goldens, the dont_use globs against the policy on all 428 cells, the script against Yosys's default, bit-exactness through three hash
seeds and two temp dirs), and in `tests/run.py` the `ppa` step plus a golden check of
the `ppa` block of each reference's real check result (`SVGOLF_PPA_REQUIRE_LIB=1` is set for the suite when the liberty file exists; without
it these checks are SKIPPED with a message and nothing unrelated fails). What the goldens pin, per design: `area_ge`, `depth`, `gates` and
`area_e4um2`, `delay_ps`, `unit_depth`, `cells`, `netlist_sha256`. The other columns are checked for every weighed block by derivation
(`tests/run.py` `ppa_block_problems`): `area_um2_sky130 = area_e4um2_sky130 / 10^4`; `cell_hist_sky130` sums to `cells_sky130` and, priced
cell by cell in the live liberty, to `area_e4um2_sky130`; `setup` and `liberty_file` equal the pins file's; `critical` has its shape; the
three provenance hashes (pins, liberty, `ppa.py`) and `ppa_version` equal the live files'. Not pinned by any golden: the values of `critical.output` and `critical.cells`.
Flow A1' (`score/tests/ppa/expected_ppa_mapped.json`, the 16 designs and the 8 idioms): per design the canonical RTLIL hash it read (equal to the A0'
golden's), `area_e4um2`, `delay_ps`, `cells`, `levels`, `buffers`, `inverters`, `constants` and the mapped netlist's `netlist_sha256`; the file is for
one `ppa_mapped_version`, liberty, script hash, Yosys and ABC build (`ppa_validate.py table --designs designs.json,idioms.json
--mapped-expected-out ...` re-records it), and every mapped block is checked by derivation (`tests/run.py` `ppa_mapped_block_problems`:
area arithmetic, the histogram priced in the live liberty, only `logic`-class cells, buffer and inverter counts, the pins, script, builds and
equivalence parameters, the RTLIL equal to the score run's). The suite's `ppa` step stays a Python-and-Yosys step: A1' adds about 25 s
for the 24 designs (and `test_ppa.py` 28 s: 24 s to 52 s).

**Byte-identity of the default result.** `tests/checker/ppa_wiring/*.baseline.json` are the results of the checker from before the wiring
(the development tree of that day) on the `add` and `aes_sbox` references, with the machine- and run-dependent leaves masked
(`tests/checker/byte_identity.py`). Two masks. `RUN_VOLATILE` (times, directories, the integrity file count) is masked everywhere.
`BUILD_VOLATILE` is deterministic in one checkout but a function of more than (design, pinned flow): the tool identities (`yosys_version`,
`verilator`, `lean_surfaces`, `extractor_sha256`, `sveval_sha256`), the `envelope_sha256` (a function of the extractor, which other work
changes) and `submission_constants_used` (a function of the proof file). It is masked against the goldens, which another commit recorded, and NOT
masked between two results of the same checkout: `--ppa off` and `--ppa auto` in one process are compared with only `RUN_VOLATILE` masked. Every
other key and value stays. `PROVENANCE.txt` there has the commands. `--ppa off` equals the goldens; `--ppa auto` equals them plus exactly the key `ppa` and
the stage `stages.ppa`.
