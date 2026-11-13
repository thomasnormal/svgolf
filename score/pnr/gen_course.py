#!/usr/bin/env python3
"""gen_course.py SRCDIR EXPDIR SVGOLF : the course job set (a copy of the 2026-11-09 study's gen.py, adapted).

usage: python3.12 -I gen_course.py <pnrcourse>/designs <pnrcourse>/jobs <pnrcourse>/export/svgolf
Inputs: SRCDIR/designs.json (one entry per board record, the netlists step) and SRCDIR/<task>__<record12>.v (the record's
ASAP7 repaired netlist; its sha256 must equal the entry's repaired_sha256), and the pinned commit's ASAP7 view and
task.json under SVGOLF (cross-checks only: period, top, clock port).
Outputs under EXPDIR: designs/<nick>.v, sdc/<nick>.sdc, cfg/<nick>__min_s<seed>.mk, jobs.txt (small designs first,
matmul last), jobs.json (per job), records.json (per record: its nickname and jobs).

What changed against gen.py (everything else is gen.py's text):
  - ONE flow: "min" (gen.py's MIN dict, verbatim), default settings (gen.py's BASE, verbatim), seeds 1, 2, 3. No td flow,
    no settings grid, no ISA or thread variants.
  - course names (DESIGN.txt 2.3): DESIGN_NICKNAME = <task>_<first 12 hex of the netlist sha256>; FLOW_VARIANT = min_s<seed>;
    job = <nick>__min_s<seed>. Records with the same netlist share the nickname and therefore the runs (DESIGN.txt 1.1).
  - the period: the record's wire-free ASAP7 delay (clocked: its register-to-register period), designs.json a0_delay_ps,
    checked equal to the view entry's delay_ps; the clock port is designs.json clock_port (checked = task.json clock),
    where gen.py hard-codes "clk" (all three clocked tasks use clk, so the text is the same).
  - the design top comes from designs.json (checked = task.json top)."""
import hashlib, json, os, shutil, sys

SRC, EXP, SV = (os.path.abspath(x) for x in sys.argv[1:4])
R = json.load(open(os.path.join(SRC, "designs.json")))
CFG, SDC, DES = (os.path.join(EXP, x) for x in ("cfg", "sdc", "designs"))
for p in (CFG, SDC, DES):
    os.makedirs(p, exist_ok=True)

MIN = {"SKIP_REPAIR_TIE_FANOUT": "1", "SKIP_FLOORPLAN_REPAIR_TIMING": "1", "GPL_TIMING_DRIVEN": "0",
       "DONT_BUFFER_PORTS": "1", "ENABLE_PLACE_REPAIR_TIMING": "0", "SKIP_CTS_REPAIR_TIMING": "1",
       "SKIP_INCREMENTAL_REPAIR": "1", "SKIP_LAST_GASP": "1", "RECOVER_POWER": "0", "CLUSTER_FLOPS": "0"}
BASE = {"CORE_UTILIZATION": "40", "PLACE_DENSITY": "0.60", "CORE_ASPECT_RATIO": "1.0", "GPL_RANDOM_SEED": "1",
        "NUM_CORES": "2", "LEC_CHECK": "1", "CORNER": "TC"}
SEEDS = (1, 2, 3)


def sha(b):
    return hashlib.sha256(b).hexdigest()


# one design per distinct netlist (nickname), with the records that share it
D = {}
for rk, r in R.items():
    b = open(os.path.join(SRC, f"{r['task']}__{r['record_id']}.v"), "rb").read()
    assert sha(b) == r["repaired_sha256"], rk
    task = json.load(open(os.path.join(SV, "tasks", r["task"], "task.json")))
    view = json.load(open(os.path.join(SV, "leaderboard", "asap7", r["task"] + ".json")))
    e = [x for x in view["designs"] if f"record:{r['record_hash']}" in x["of"]]
    assert len(e) == 1 and e[0]["repaired_sha256"] == r["repaired_sha256"], rk
    e = e[0]
    assert r["a0_delay_ps"] == e["delay_ps"] and r["top"] == task["top"], rk
    assert (e["cycles"] is not None) == r["seq"], rk
    if r["seq"]:
        assert r["clock_port"] == task["clock"] and r["a0_period_ps"] == r["a0_delay_ps"], rk
    nick = f"{r['task']}_{r['repaired_sha256'][:12]}"
    d = D.setdefault(nick, {"task": r["task"], "top": r["top"], "seq": r["seq"], "clock": r["clock_port"],
                            "a0_delay_ps": r["a0_delay_ps"], "cells": r["cells"], "netlist_sha256": r["repaired_sha256"],
                            "records": []})
    for k in ("top", "seq", "a0_delay_ps", "cells"):
        assert d[k] == r[k], (rk, k)
    d["records"].append(rk)
    open(os.path.join(DES, nick + ".v"), "wb").write(b)


def sdc(name, scale=1.0):
    d = D[name]
    per = d["a0_delay_ps"] * scale
    tag = "" if scale == 1.0 else f"_x{int(round(scale * 100)):03d}"
    path = os.path.join(SDC, f"{name}{tag}.sdc")
    drv = "set_driving_cell -lib_cell BUFx8_ASAP7_75t_R -pin Y -input_transition_rise 20 -input_transition_fall 20"
    if d["seq"]:
        txt = (f"# A0' asap7 timing setup as SDC (clocked): ideal clock, 20 ps transition, period = A0' period x {scale}\n"
               f"current_design {d['top']}\ncreate_clock -name clk -period {per:.1f} [get_ports {d['clock']}]\n"
               "set_clock_transition 20 [get_clocks clk]\n"
               "set_input_delay 0 -clock clk [all_inputs -no_clocks]\nset_output_delay 0 -clock clk [all_outputs]\n"
               f"{drv} [all_inputs -no_clocks]\nset_load 2.5 [all_outputs]\n")
    else:
        txt = (f"# A0' asap7 timing setup as SDC (combinational): virtual clock at the A0' delay x {scale}\n"
               f"current_design {d['top']}\ncreate_clock -name vclk -period {per:.1f}\n"
               "set_input_delay 0 -clock vclk [all_inputs]\nset_output_delay 0 -clock vclk [all_outputs]\n"
               f"{drv} [all_inputs]\nset_load 2.5 [all_outputs]\n")
    open(path, "w").write(txt)
    return f"/work/sdc/{name}{tag}.sdc", per, sha(txt.encode())


JOBS = {}


def job(name, seed):
    d = D[name]
    k = dict(BASE)
    k.update(MIN)
    k["GPL_RANDOM_SEED"] = str(seed)
    sdc_path, per, sdc_sha = sdc(name)
    variant = f"min_s{seed}"
    j = f"{name}__{variant}"
    lines = [f"# {j}", f"export DESIGN_NAME = {d['top']}", f"export DESIGN_NICKNAME = {name}", "export PLATFORM = asap7",
             f"export SYNTH_NETLIST_FILES = /work/designs/{name}.v", f"export VERILOG_FILES = /work/designs/{name}.v",
             f"export SDC_FILE = {sdc_path}", f"export FLOW_VARIANT = {variant}", "export WORK_HOME = /work/run"]
    for key, val in k.items():
        lines.append(f"export {key} = {val}")
    mk = "\n".join(lines) + "\n"
    open(os.path.join(CFG, j + ".mk"), "w").write(mk)
    JOBS[j] = {"nick": name, "task": d["task"], "flow": "min", "seed": seed, "settings": {},
               "threads": int(k["NUM_CORES"]), "clock_period_ps": per, "seq": d["seq"], "cells": d["cells"],
               "netlist_sha256": d["netlist_sha256"], "records": d["records"], "config_mk_sha256": sha(mk.encode()),
               "sdc_sha256": sdc_sha, "io_tcl_sha256": None}
    return j


order = sorted(D, key=lambda n: (D[n]["cells"], n))
jl = [job(n, s) for n in order for s in SEEDS]
open(os.path.join(EXP, "jobs.txt"), "w").write("\n".join(jl) + "\n")
json.dump(JOBS, open(os.path.join(EXP, "jobs.json"), "w"), indent=1)
recs = {rk: {"nick": f"{r['task']}_{r['repaired_sha256'][:12]}", "task": r["task"], "record_hash": r["record_hash"],
             "jobs": [f"{r['task']}_{r['repaired_sha256'][:12]}__min_s{s}" for s in SEEDS]} for rk, r in R.items()}
json.dump(recs, open(os.path.join(EXP, "records.json"), "w"), indent=1)
print(f"records {len(R)}  distinct netlists {len(D)}  record x seed rows {len(R) * len(SEEDS)}  jobs {len(jl)}")
for n in D:
    if len(D[n]["records"]) > 1:
        print(f"  shared netlist {n}: records {D[n]['records']}")
print("renderer", sha(open(os.path.abspath(__file__), "rb").read()))
