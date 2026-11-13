#!/usr/bin/env python3
"""job.py: the files of one routed-course job, from a design's ASAP7 netlist and a seed (score/pnr/README.md).

    python3.12 score/pnr/job.py --task T --netlist NETLIST.v --seed S --out JOBDIR

NETLIST.v is the design's ASAP7 netlist: the repaired netlist the ASAP7 view weighs (`score/ppa.py DESIGN.sv --task
tasks/T --pdk asap7 --no-mapped [--seq] --repaired-netlist NETLIST.v`); its sha256 must be the `repaired_sha256` of an
entry of leaderboard/asap7/T.json, whose delay (`delay_ps`, the clocked period on a clocked task) becomes the SDC's
clock period. S is the request's seed (leaderboard/asap7pnr/T.json `request.seed`; 1..2^31-1). Writes, under JOBDIR:

    designs/<nick>.v   the netlist, byte for byte            sdc/<nick>.sdc    the timing setup
    cfg/<job>.mk       the config.mk                         jobs/<job>.json   the job's record (hashes, period, ...)

No pin-placement file: ORFS places the pins itself (`io_tcl_sha256` is null on every course run).

The text is the one the committed runs were made with: the two renderers score/pnr/pins.json pins by sha256
(score/pnr/gen_course.py and gen_course2.py, the campaign scripts, kept byte for byte) wrote these same lines; this
script renders them from the tree instead of a campaign's work list, and takes every ORFS variable's VALUE from
score/pnr/pins.json (`orfs_variables`; the seed is the job's). Only the order of the lines is kept here, so that the
bytes, and so the config.mk's sha256 every run records, are the campaigns'. tests/pnr/test_pnr_tools.py renders the
job of every committed run and requires its recorded config.mk and SDC sha256."""

import argparse
import json
import os
import shutil
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pnr  # noqa: E402

# the order of the ORFS variables in a course config.mk (the campaigns' order); their values are the pins'
ORFS_ORDER = ("CORE_UTILIZATION", "PLACE_DENSITY", "CORE_ASPECT_RATIO", "GPL_RANDOM_SEED", "NUM_CORES", "LEC_CHECK",
              "CORNER", "SKIP_REPAIR_TIE_FANOUT", "SKIP_FLOORPLAN_REPAIR_TIMING", "GPL_TIMING_DRIVEN",
              "DONT_BUFFER_PORTS", "ENABLE_PLACE_REPAIR_TIMING", "SKIP_CTS_REPAIR_TIMING", "SKIP_INCREMENTAL_REPAIR",
              "SKIP_LAST_GASP", "RECOVER_POWER", "CLUSTER_FLOPS")
DRIVE = "set_driving_cell -lib_cell BUFx8_ASAP7_75t_R -pin Y -input_transition_rise 20 -input_transition_fall 20"


class JobError(Exception):
    pass


def sdc_text(top, delay_ps, clock=None):
    """The SDC of a design: one clock at the ASAP7 view's delay (a virtual clock on a combinational design, the clock
    port's on a clocked one), ideal, inputs and outputs at 0, the A0' input drive and output load."""
    per = delay_ps * 1.0
    if clock is not None:
        return (f"# A0' asap7 timing setup as SDC (clocked): ideal clock, 20 ps transition, period = A0' period x 1.0\n"
                f"current_design {top}\ncreate_clock -name clk -period {per:.1f} [get_ports {clock}]\n"
                "set_clock_transition 20 [get_clocks clk]\n"
                "set_input_delay 0 -clock clk [all_inputs -no_clocks]\nset_output_delay 0 -clock clk [all_outputs]\n"
                f"{DRIVE} [all_inputs -no_clocks]\nset_load 2.5 [all_outputs]\n")
    return (f"# A0' asap7 timing setup as SDC (combinational): virtual clock at the A0' delay x 1.0\n"
            f"current_design {top}\ncreate_clock -name vclk -period {per:.1f}\n"
            "set_input_delay 0 -clock vclk [all_inputs]\nset_output_delay 0 -clock vclk [all_outputs]\n"
            f"{DRIVE} [all_inputs]\nset_load 2.5 [all_outputs]\n")


def mk_text(nick, top, seed, pins):
    """The config.mk of the job <nick>__min_s<seed>."""
    orfs = pins["orfs_variables"]
    if set(ORFS_ORDER) != set(orfs) | {"GPL_RANDOM_SEED"} or "GPL_RANDOM_SEED" in orfs:
        raise JobError("score/pnr/pins.json's orfs_variables are not the ones this renderer orders: "
                       f"{sorted(set(ORFS_ORDER) ^ (set(orfs) | {'GPL_RANDOM_SEED'}))}")
    variant = f"min_s{seed}"
    lines = [f"# {nick}__{variant}", f"export DESIGN_NAME = {top}", f"export DESIGN_NICKNAME = {nick}",
             f"export PLATFORM = {pins['platform']}", f"export SYNTH_NETLIST_FILES = /work/designs/{nick}.v",
             f"export VERILOG_FILES = /work/designs/{nick}.v", f"export SDC_FILE = /work/sdc/{nick}.sdc",
             f"export FLOW_VARIANT = {variant}", "export WORK_HOME = /work/run"]
    for k in ORFS_ORDER:
        lines.append(f"export {k} = {seed if k == 'GPL_RANDOM_SEED' else orfs[k]}")
    return "\n".join(lines) + "\n"


def render(task, view, netlist_sha256, seed, pins):
    """(job name, config.mk text, SDC text, the job's record) of the netlist with this sha256 at `seed`: `task` is the
    task.json (its top and clock port), `view` the task's ASAP7 view (leaderboard/asap7/<task>.json). Pure."""
    if not (isinstance(seed, int) and 1 <= seed <= pnr.SEED_MAX):
        raise JobError(f"seed {seed!r} is not an integer in 1..2^31-1")
    es = [e for e in view.get("designs") or [] if e.get("repaired_sha256") == netlist_sha256]
    if not es:
        raise JobError(f"no design of {task['name']}'s ASAP7 view has the ASAP7 netlist {netlist_sha256[:16]}...: "
                       "weigh it first (`leaderboard.py asap7 --write --task T`)")
    if len({(e["delay_ps"], e["cycles"], e["cells"]) for e in es}) != 1:
        raise JobError("the view's entries of this netlist disagree on its delay, cycles or cells")
    e = es[0]
    clocked = e["cycles"] is not None
    if clocked and not task.get("clock"):
        raise JobError(f"{task['name']} is clocked but its task.json names no clock port")
    nick = f"{task['name']}_{netlist_sha256[:12]}"
    job = f"{nick}__min_s{seed}"
    mk = mk_text(nick, task["top"], seed, pins)
    sdc = sdc_text(task["top"], e["delay_ps"], task["clock"] if clocked else None)
    rec = {"job": job, "nick": nick, "task": task["name"], "flow": "min", "seed": seed, "settings": {},
           "threads": int(pins["threads"]), "clock_period_ps": e["delay_ps"] * 1.0, "seq": clocked,
           "cells": e["cells"], "netlist_sha256": netlist_sha256,
           "designs": sorted({x for y in es for x in y["of"]}),
           "config_mk_sha256": pnr.sha256_bytes(mk.encode()), "sdc_sha256": pnr.sha256_bytes(sdc.encode()),
           "io_tcl_sha256": None}
    return job, mk, sdc, rec


def write_job(out, netlist_path, task, view, seed, pins):
    """Render the job of the netlist file and write its files under `out`; returns the job's record."""
    sha = pnr.sha256_file(netlist_path)
    job, mk, sdc, rec = render(task, view, sha, seed, pins)
    for sub in ("designs", "sdc", "cfg", "jobs"):
        os.makedirs(os.path.join(out, sub), exist_ok=True)
    shutil.copyfile(netlist_path, os.path.join(out, "designs", rec["nick"] + ".v"))
    for path, text in ((os.path.join(out, "sdc", rec["nick"] + ".sdc"), sdc),
                       (os.path.join(out, "cfg", job + ".mk"), mk),
                       (os.path.join(out, "jobs", job + ".json"), json.dumps(rec, indent=1, sort_keys=True) + "\n")):
        with open(path, "w", encoding="utf-8", newline="\n") as fh:
            fh.write(text)
    if pnr.sha256_file(os.path.join(out, "designs", rec["nick"] + ".v")) != sha:
        raise JobError("the copied netlist is not the netlist")
    return rec


def load_tree(task_name, svgolf=pnr.SVGOLF):
    """(task.json with its name, the ASAP7 view) of a task of the tree."""
    with open(os.path.join(svgolf, "tasks", task_name, "task.json"), encoding="utf-8") as fh:
        task = json.load(fh)
    task.setdefault("name", task_name)
    with open(os.path.join(svgolf, "leaderboard", "asap7", task_name + ".json"), encoding="utf-8") as fh:
        view = json.load(fh)
    return task, view


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--task", required=True)
    ap.add_argument("--netlist", required=True, help="the design's ASAP7 (repaired) netlist")
    ap.add_argument("--seed", required=True, type=int, help="the request's seed, 1..2^31-1")
    ap.add_argument("--out", required=True, help="the job directory (created; other jobs in it are kept)")
    args = ap.parse_args(argv)
    try:
        task, view = load_tree(args.task)
        rec = write_job(args.out, args.netlist, task, view, args.seed, pnr.load_pins())
    except (OSError, ValueError, KeyError, JobError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    print(f"{rec['job']}: config.mk {rec['config_mk_sha256']}, SDC {rec['sdc_sha256']}, period "
          f"{rec['clock_period_ps']} ps, {rec['cells']} cells, for {', '.join(rec['designs'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
