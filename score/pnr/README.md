# The routed course's run tools

What it takes to make a run of the routed course ("ASAP7 placed and routed") again with the pinned image, and to turn
it into the tree's data: the rules are README.md, "How the routed course is scored", and score/PPA.md, "ASAP7 placed
and routed"; the data and its checks are leaderboard/README.md, "The routed course". Python 3.12, standard library
only, but for `encode.py` (Pillow).

| file | what |
|---|---|
| `pins.json` | the course's pins: the image by digest, the flow `min_v1` and its ORFS variables, threads, CPUs, memory cap, the rules; every tool here reads them from this file |
| `job.py` | the generator: a job's `config.mk` and SDC from a design's ASAP7 netlist and a seed (no pin-placement file: ORFS places the pins) |
| `run_job.py` | the runner: `run` (ORFS's `make` in the image) and `render` (the layout picture), in a container, by digest |
| `layout.tcl`, `draw.tcl` | the picture: OpenROAD's own renderer, off-screen, the flow's routing view, power and ground hidden |
| `encode.py` | the WebP picture (at most 300,000 bytes) and the 640 px thumbnail from the render |
| `collect.py` | `row` (a finished job's numbers and hashes), `entry` (the routed entry), `sitedata` (what `leaderboard.py asap7pnr --import` reads) |
| `check_sitedata.py` | the check of collected data before it is imported; shares no code with `collect.py` |
| `lec.py` | the reference-against-routed equivalence job and its log reader: a tool, not a pinned step (below) |
| `pnr.py` | what they share: the pins, a job directory's layout, the container command |
| `gen_course.py`, `gen_course2.py` | the two campaign scripts that wrote the committed runs' `config.mk` and SDC, kept byte for byte because `pins.json` pins their sha256; they read a campaign's work list, which is not in the tree, and are not needed to make a job |

## What a run needs

- **An x86-64 Linux host** with a container runtime (docker or podman; `--runtime`, or `$SVGOLF_CONTAINER_RUNTIME`)
  that can pull the image by its digest or already holds it:
  `docker pull docker.io/openroad/orfs@sha256:df7ba49c0bc2bcdfc353b9fc75a17dac489200c239967564bc25d6bd40462c21`
  (the amd64 manifest of `openroad/orfs:26Q4-262-g3ff0197f0`; `pins.json` `image`). `run_job.py` refuses any other
  host; `--dry-run` prints the command anywhere. A job takes two CPUs, at most 8 GB of memory, no swap and no network:
  65 to 109 s for up to 2,476 cells, 698 s and 4.1 GB for the 41,035-cell matmul record (score/PPA.md).
- **The design's ASAP7 netlist**: the ASAP7 view's repaired netlist, from `score/ppa.py` with Yosys and the five pinned
  ASAP7 liberty files (`python3.12 score/ppa.py --pdk asap7 --fetch-liberty` fetches them into `score/lib/asap7/`).
- **The request's seed** (`leaderboard/asap7pnr/<task>.json`, `request.seed`): a design not routed yet gets its request
  first, `python3.12 leaderboard/leaderboard.py asap7pnr --request --task T --design DESIGN.sv [--seed N] --write`
  (the seed named, else one drawn from the operating system's random source; stored, never changed).
- For `collect.py` and `check_sitedata.py`: the five liberty files (the area); for `encode.py`: Pillow (the committed
  pictures were encoded with Pillow 11.1.0 and libwebp 1.5.0).

## The commands, for one design

```bash
# 0. the design's ASAP7 netlist (add --seq on a clocked task); its sha256 must be the ASAP7 view's repaired_sha256
python3.12 score/ppa.py DESIGN.sv --task tasks/T --pdk asap7 --no-mapped --repaired-netlist netlist.v
# 1. the job's files under ./job: designs/, sdc/, cfg/, jobs/ (prints the job's name, NICK__min_sS)
python3.12 score/pnr/job.py --task T --netlist netlist.v --seed S --out job
# 2. place and route (x86-64 Linux, docker or podman), then draw the scored layout
python3.12 score/pnr/run_job.py run job JOB
python3.12 score/pnr/run_job.py render job JOB
# 3. the numbers and hashes of the run, its picture, its entry
mkdir -p job/rows && python3.12 score/pnr/collect.py row job JOB --out job/rows/JOB.json
python3.12 -I score/pnr/encode.py job/img/JOB.png out/images T SV16 --json job/img/JOB.SV16.json
python3.12 score/pnr/collect.py entry --task T --sv SV_SHA256 job JOB --out job/entry.json
# 4. the task's site data, checked, then imported into the tree
python3.12 score/pnr/collect.py sitedata --task T --out out job/entry.json
python3.12 score/pnr/check_sitedata.py out --task T --jobs job
python3.12 leaderboard/leaderboard.py asap7pnr --import out --task T --write
python3.12 leaderboard/leaderboard.py asap7pnr --task T
```

`SV_SHA256` is the design file's sha256 and `SV16` its first 16 hex digits: the names its entry and its picture take.
Designs that share a netlist share a job and its run: each gets its own entry (step 3 once per design file). `collect.py
entry` takes the request the tree stores for the design, and refuses a job at another seed; `collect.py sitedata` keeps
every other entry of the tree's table and refuses to replace a design's scoring run by another (one run per design).

## What is and is not reproducible

Measured on the course host (one host type: x86-64 Linux, Intel Xeon Platinum 8488C, Rocky Linux 9.8, the image
unpacked into a rootless user namespace with chroot): a run is repeatable, byte for byte, on that host type: 3 of 3
re-runs of a seed (2026-11-11), 4 of 4 netlists placed again under other job names (2026-11-12) and 13 of 13
same-netlist re-runs (2026-11-13) gave the same `6_final.def`, `6_final.v`, `6_final.odb` and stage databases (and,
on 2026-11-13, the same normalized SPEF); two renders of one database gave the same PNG (2 of 2 on 2026-11-12 and on
2026-11-13).

Checked offline by `tests/pnr/test_pnr_tools.py` on stored data: `job.py` renders the `config.mk` and SDC of every
committed run (97 runs, three campaigns) to the sha256 each run records; the path render, picture, entry, site data,
import reproduces the committed `leaderboard/asap7pnr/_example.json` byte for byte from the stored job of one design
(its collected row, render and render log; the ORFS work trees themselves stayed on the course host, so `collect.py
row` is tested on the files that came back and on report files written from a stored row's texts); `encode.py` makes
the committed picture and thumbnail from the stored render (with Pillow 11.1.0 and libwebp 1.5.0); `check_sitedata.py`
passes that data and catches each planted fault.

Not measured: these tools' own runs. The committed runs were made by the course host's commands, which ran the same
image unpacked into a rootless user namespace with chroot, not under docker or podman; no run has been made with
`run_job.py` yet, so its results are expected, not shown, to equal the committed ones. No second host type has been
measured (another x86-64 machine, a cloud runner, Apple silicon under emulation). The picture's renderer scripts are
not pinned (their sha256 is not in `pins.json`). The two extra seeds of the first records (`spread`) and re-runs
(`verification`) are not made by these tools.

## The reference-against-routed equivalence job

The flow's own equivalence check (step `6_report`, `LEC_CHECK=1`) compares the routed netlist with the flow's rendering
of the netlist the run was given: it shows that place and route preserved the run's input, not that the input was the
design's netlist, which the course checks by sha256 (score/PPA.md, "What the equivalence check shows, and the negative
control"). `lec.py` makes the job the negative control of 2026-11-13 ran: the same tool, kepler-formal, in the pinned
image, with the run's own configuration changed in three lines (the reference is the netlist file the course binds,
`designs/<nick>.v`; the other side the run's routed `6_final_lec.v`; its own log), and reads its log.

```bash
python3.12 score/pnr/lec.py config  job JOB      # job/lec/JOB.yml, from job/run/objects/.../6_final_lec_test.yml
python3.12 score/pnr/lec.py run     job JOB      # kepler-formal in the image; the netlist and the run read-only
python3.12 score/pnr/lec.py verdict job/lec/JOB_lec_check.log
```

kepler-formal exits 0 whether the circuits are equal or not, so the verdict is read from the log: IDENTICAL when it
prints "Circuits are IDENTICAL" and neither "Found difference" nor "Circuits are DIFFERENT" (exit 0); DIFFERENT when
it prints "Found difference" and "Circuits are DIFFERENT" and not the first (exit 1); anything else, an empty or cut-off
log included, is NO VERDICT (exit 3). On the control's eight logs: 4 IDENTICAL (the unchanged netlists), 4 DIFFERENT
(one gate changed), `tests/pnr/test_lec.py`. This job is a tool only: it is not part of a run's validity, not pinned in
`pins.json`, and the committed results carry the flow's own verdict only; whether it becomes a pinned step is open.
