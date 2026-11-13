#!/usr/bin/env python3
"""gen_course2.py EXTRAS_DIR EXPDIR SVGOLF RECORD_JOBS_DIR : the job set for the designs of the ASAP7 view that are NOT
records (proved references and baselines), seed 1 only, in the course's minimal flow.

usage: python3.12 -I gen_course2.py <pc>/designs/extras <course2 job dir> <tree>/svgolf <pc>/jobs
Inputs: EXTRAS_DIR/designs.json (assemble.py's extras: one entry per non-record design file of the ASAP7 view) and
EXTRAS_DIR/<name>.v (its ASAP7 repaired netlist; sha256 must equal the entry's repaired_sha256 AND the view entry's);
SVGOLF = the board tree whose leaderboard/asap7/<task>.json and tasks/<task>/task.json are cross-checked (period, top,
of); RECORD_JOBS_DIR = the 2026-11-11 campaign's jobs/ (designs/*.v): a netlist already placed there is NOT run again
(runs are keyed by netlist, DESIGN.txt 1.1), it is listed in reused.json instead.
Outputs under EXPDIR: designs/<nick>.v, sdc/<nick>.sdc, cfg/<nick>__min_s1.mk, jobs.txt (small designs first, the
largest last), jobs.json (per job, gen_course.py's shape plus `designs`: the view tags), reused.json.

The rendering is gen_course.py's, text for text (its MIN, BASE, sdc() and job() are copied below unchanged but for the
seed list and the record keys); `selftest` re-renders one 2026-11-11 job (add_3f31f3f29548__min_s1) and requires the
config.mk and SDC bytes of that campaign before anything is written."""
import hashlib, json, os, sys

SRC, EXP, SV, RJ = (os.path.abspath(x) for x in sys.argv[1:5])
R = json.load(open(os.path.join(SRC, "designs.json")))
CFG, SDC, DES = (os.path.join(EXP, x) for x in ("cfg", "sdc", "designs"))

# ---- gen_course.py's text (verbatim) ------------------------------------------------------------------------------
MIN = {"SKIP_REPAIR_TIE_FANOUT": "1", "SKIP_FLOORPLAN_REPAIR_TIMING": "1", "GPL_TIMING_DRIVEN": "0",
       "DONT_BUFFER_PORTS": "1", "ENABLE_PLACE_REPAIR_TIMING": "0", "SKIP_CTS_REPAIR_TIMING": "1",
       "SKIP_INCREMENTAL_REPAIR": "1", "SKIP_LAST_GASP": "1", "RECOVER_POWER": "0", "CLUSTER_FLOPS": "0"}
BASE = {"CORE_UTILIZATION": "40", "PLACE_DENSITY": "0.60", "CORE_ASPECT_RATIO": "1.0", "GPL_RANDOM_SEED": "1",
        "NUM_CORES": "2", "LEC_CHECK": "1", "CORNER": "TC"}
SEEDS = (1,)                       # gen_course.py: (1, 2, 3); the owner's rule: one run, seed 1 unless named


def sha(b):
    return hashlib.sha256(b).hexdigest()


def sdc_text(d, scale=1.0):
    per = d["a0_delay_ps"] * scale
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
    return per, txt


def mk_text(name, d, seed):
    k = dict(BASE)
    k.update(MIN)
    k["GPL_RANDOM_SEED"] = str(seed)
    variant = f"min_s{seed}"
    j = f"{name}__{variant}"
    lines = [f"# {j}", f"export DESIGN_NAME = {d['top']}", f"export DESIGN_NICKNAME = {name}", "export PLATFORM = asap7",
             f"export SYNTH_NETLIST_FILES = /work/designs/{name}.v", f"export VERILOG_FILES = /work/designs/{name}.v",
             f"export SDC_FILE = /work/sdc/{name}.sdc", f"export FLOW_VARIANT = {variant}", "export WORK_HOME = /work/run"]
    for key, val in k.items():
        lines.append(f"export {key} = {val}")
    return j, "\n".join(lines) + "\n", k
# -------------------------------------------------------------------------------------------------------------------


def selftest():
    """The renderer must reproduce the campaign's own files for one of its jobs (add 8c1f662e, seed 1)."""
    d = {"top": "add_n", "seq": False, "a0_delay_ps": 563}
    task = json.load(open(os.path.join(SV, "tasks", "add", "task.json")))
    d["top"] = task["top"]
    j, mk, _ = mk_text("add_3f31f3f29548", d, 1)
    _, txt = sdc_text(d)
    want_mk = open(os.path.join(RJ, "cfg", j + ".mk"), "rb").read()
    want_sdc = open(os.path.join(RJ, "sdc", "add_3f31f3f29548.sdc"), "rb").read()
    assert mk.encode() == want_mk, "config.mk rendering differs from the campaign's"
    assert txt.encode() == want_sdc, "SDC rendering differs from the campaign's"
    assert sha(want_mk) == "b05d50fc3f373aa2af28e9502c62bdfaabfe70d4b622bf64c9d824f091add07b"
    return sha(want_mk), sha(want_sdc)


st = selftest()
for p in (CFG, SDC, DES):
    os.makedirs(p, exist_ok=True)
done = {sha(open(os.path.join(RJ, "designs", f), "rb").read()): f[:-2] for f in os.listdir(os.path.join(RJ, "designs"))
        if f.endswith(".v")}
D, reused = {}, {}
for name, r in sorted(R.items()):
    b = open(os.path.join(SRC, f"{name}.v"), "rb").read()
    assert sha(b) == r["repaired_sha256"], name
    task = json.load(open(os.path.join(SV, "tasks", r["task"], "task.json")))
    view = json.load(open(os.path.join(SV, "leaderboard", "asap7", r["task"] + ".json")))
    e = [x for x in view["designs"] if x["sv_sha256"] == r["sv_sha256"]]
    assert len(e) == 1 and e[0]["repaired_sha256"] == r["repaired_sha256"] and e[0]["of"] == r["of"], name
    e = e[0]
    assert r["a0_delay_ps"] == e["delay_ps"] and r["top"] == task["top"] and not r["seq"] and e["cycles"] is None, name
    nick = f"{r['task']}_{r['repaired_sha256'][:12]}"
    if r["repaired_sha256"] in done:
        reused[name] = {"nick": done[r["repaired_sha256"]], "of": r["of"], "netlist_sha256": r["repaired_sha256"]}
        continue
    d = D.setdefault(nick, {"task": r["task"], "top": r["top"], "seq": False, "clock": None,
                            "a0_delay_ps": r["a0_delay_ps"], "cells": r["cells"], "netlist_sha256": r["repaired_sha256"],
                            "designs": []})
    assert (d["top"], d["a0_delay_ps"], d["cells"]) == (r["top"], r["a0_delay_ps"], r["cells"]), name
    d["designs"] += r["of"]
    open(os.path.join(DES, nick + ".v"), "wb").write(b)

JOBS = {}
order = sorted(D, key=lambda n: (D[n]["cells"], n))
jl = []
for n in order:
    d = D[n]
    per, txt = sdc_text(d)
    open(os.path.join(SDC, f"{n}.sdc"), "w").write(txt)
    for s in SEEDS:
        j, mk, k = mk_text(n, d, s)
        open(os.path.join(CFG, j + ".mk"), "w").write(mk)
        JOBS[j] = {"nick": n, "task": d["task"], "flow": "min", "seed": s, "settings": {},
                   "threads": int(k["NUM_CORES"]), "clock_period_ps": per, "seq": d["seq"], "cells": d["cells"],
                   "netlist_sha256": d["netlist_sha256"], "records": [], "designs": sorted(d["designs"]),
                   "config_mk_sha256": sha(mk.encode()), "sdc_sha256": sha(txt.encode()), "io_tcl_sha256": None}
        jl.append(j)
open(os.path.join(EXP, "jobs.txt"), "w").write("\n".join(jl) + "\n")
json.dump(JOBS, open(os.path.join(EXP, "jobs.json"), "w"), indent=1)
json.dump(reused, open(os.path.join(EXP, "reused.json"), "w"), indent=1)
print(f"selftest config {st[0][:16]} sdc {st[1][:16]} = the campaign's")
print(f"extra designs {len(R)}  distinct new netlists {len(D)}  reused (already placed) {len(reused)}  jobs {len(jl)}")
for k, v in reused.items():
    print(f"  reused {k} -> {v['nick']}")
print("renderer", sha(open(os.path.abspath(__file__), "rb").read()))
