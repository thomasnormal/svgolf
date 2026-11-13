#!/usr/bin/env python3
"""collect.py: a finished routed-course job, turned into the tree's data (score/pnr/README.md).

    python3.12 score/pnr/collect.py row      JOBDIR JOB [--out ROW.json]
    python3.12 score/pnr/collect.py entry    --task T --sv SV_SHA256 JOBDIR JOB [--date YYYY-MM-DD] [--out ENTRY.json]
    python3.12 score/pnr/collect.py sitedata --task T --out OUTDIR ENTRY.json ...

`row` (where the job ran; reads only JOBDIR): one JSON row of the job, the campaigns' course_collect.py for one job.
ORFS's metric values are kept as their raw JSON text (parsed with Decimal, written as strings, never as floats); the
full sha256 of 1_2_yosys.v, 6_final.def, 6_final.v, 6_final.odb, the stage databases and 6_final.spef NORMALIZED (its
*DATE, *VENDOR, *PROGRAM and *VERSION lines dropped: they name the time and the tool build, not the layout); the cell
histogram of 6_final.v; per-step peak memory, elapsed and CPU seconds; the detailed-route DRC count; the verdict of
every equivalence log (`<step>:IDENTICAL` when it prints "Circuits are IDENTICAL", `DIFFERENT` when it prints "Found
difference", else `UNKNOWN`); the status line's exit status, seconds, CPUs and date. Never the host's name.

`entry`: the routed entry (schema svgolf-asap7pnr/2) of the design file with sha256 SV_SHA256, scored by this job:
  area   the routed netlist's cells (the row's histogram of 6_final.v) by the pinned ASAP7 liberty, summed exactly in
         1e-5 um^2 (the five files of score/ppa_pins_asap7.json, each sha256-checked; --liberty DIR, else
         $SVGOLF_ASAP7_LIB, else score/lib/asap7/, where `score/ppa.py --pdk asap7 --fetch-liberty` puts them)
  delay  half-even(P - WS) in ps: P the SDC's clock period, WS ORFS's worst setup slack after routing
         (finish__timing__setup__ws); time = cycles x delay on a clocked task; exact = area x time
  valid  ORFS exit 0, detailed-route DRC 0, and every equivalence log IDENTICAL (score/pnr/pins.json validity_rule)
It requires: the job's config.mk to be a course job under the pins, its seed to be the request's (the request is the one
leaderboard/asap7pnr/T.json stores for the design), the placed netlist (1_2_yosys.v) to be the ASAP7 view's netlist of
the design, and the SDC period its delay. Reads JOBDIR/rows/JOB.json (`row`'s output), JOBDIR/cfg/JOB.mk, the SDC,
JOBDIR/logs/JOB.host.json, JOBDIR/logs/JOB.render.out (the die and core boxes) and JOBDIR/img/JOB.<sv16>.json
(encode.py's record of the picture); each can be named instead (--row, --host, --render-log, --picture).

`sitedata`: OUTDIR/sitedata/T.json for `leaderboard.py asap7pnr --import OUTDIR --write`: the tree's routed table of T
with the given entries added (an entry for a design that already has a scoring run is refused unless it is that entry,
byte for byte: one run per design), every picture under OUTDIR/images/T/ (the new ones are encode.py's output there;
the carried ones are copied from site/layouts/T/). Check it with score/pnr/check_sitedata.py before importing."""

import argparse
import collections
import copy
import glob
import json
import os
import re
import shutil
import sys
from decimal import ROUND_HALF_EVEN, Decimal

sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pnr  # noqa: E402

sys.path.insert(0, os.path.join(pnr.SVGOLF, "leaderboard"))
import leaderboard as lb  # noqa: E402

STEP = re.compile(r"Elapsed time: ([\d:.]+)\[h:\]min:sec\. CPU time: user ([\d.]+) sys ([\d.]+) \(\d+%\)\. "
                  r"Peak memory: (\d+)KB")
CELL = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s+(\\\S+|[A-Za-z_][A-Za-z0-9_$\[\]]*)\s*\(", re.M)
STATUS = re.compile(r"(\S+) rc=(\d+) seconds=([\d.]+)(?: cpus=(\S+))?(?: date=(\d{4}-\d\d-\d\d))?(?: host=\S+)?\s*$")
HASHED = ("1_2_yosys.v", "6_final.def", "6_final.v", "6_final.spef", "6_final.odb", "2_floorplan.odb", "3_place.odb",
          "3_5_place_dp.odb", "4_cts.odb", "5_1_grt.odb", "5_route.odb")
ARTIFACTS = ("1_2_yosys.v", "6_final.def", "6_final.v", "6_final.odb", "2_floorplan.odb", "3_place.odb", "4_cts.odb",
             "5_route.odb")
LAYOUT_VIEW = ("the flow's routing view (the settings of its scripts/save_images.tcl): every layer, net and instance; "
               "power and ground nets hidden")
BOX = re.compile(r"layout\.tcl: dbu_per_micron (\d+) die (-?\d+) (-?\d+) (-?\d+) (-?\d+) core (-?\d+) (-?\d+) "
                 r"(-?\d+) (-?\d+)")


class CollectError(Exception):
    pass


# ---- row: where the job ran -----------------------------------------------------------------------------------------

def spef_sha256(path):
    """sha256 of a SPEF without its *DATE, *VENDOR, *PROGRAM and *VERSION lines (the lines joined by newlines)."""
    with open(path, "rb") as fh:
        b = fh.read()
    return pnr.sha256_bytes(b"\n".join(x for x in b.split(b"\n")
                                       if not re.match(rb"^\*(DATE|VENDOR|PROGRAM|VERSION)\b", x)))


def lec_verdicts(logs_dir):
    """['<step>:IDENTICAL' | ':DIFFERENT' | ':UNKNOWN', ...] of every <step>_lec_check.log, by name."""
    out = []
    for lg in sorted(glob.glob(os.path.join(logs_dir, "*_lec_check.log"))):
        with open(lg, errors="replace") as fh:
            t = fh.read()
        verdict = "IDENTICAL" if "Circuits are IDENTICAL" in t else ("DIFFERENT" if "Found difference" in t else "UNKNOWN")
        out.append(os.path.basename(lg)[:-len("_lec_check.log")] + ":" + verdict)
    return out


def final_hist(path):
    """{cell type: count} of a gate-level Verilog netlist (comments dropped; module, ports, wires and assigns are not
    cells)."""
    with open(path) as fh:
        body = re.sub(r"/\*.*?\*/", "", fh.read(), flags=re.S)
    hist = collections.Counter(m.group(1) for m in CELL.finditer(body)
                               if m.group(1) not in ("module", "input", "output", "wire", "assign", "inout"))
    return dict(sorted(hist.items()))


def _text(path):
    with open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read()


def _dsize(p):
    return sum(e.stat(follow_symlinks=False).st_size for e in os.scandir(p) if e.is_file(follow_symlinks=False)) \
        if os.path.isdir(p) else 0


def collect_row(job_dir, job):
    """The row of one job (see the module text). A job without a status line is "pending"."""
    nick, variant, _seed = pnr.parse_job(job)
    d = pnr.work_dirs(job_dir, job)
    res, logs, rep = d["results"], d["logs"], d["reports"]
    row = {"job": job, "nick": nick, "variant": variant}
    status, n = None, 0
    sp = os.path.join(job_dir, "logs", "status.txt")
    if os.path.exists(sp):
        with open(sp, encoding="utf-8") as fh:
            for ln in fh:
                m = STATUS.match(ln.strip())
                if m and m.group(1) == job:
                    status, n = m, n + 1                 # the last status line counts
    if status is None:
        row["status"] = "pending"
        row["started"] = os.path.isdir(logs)
        return row
    row.update({"rc": int(status.group(2)), "seconds": round(float(status.group(3)), 1), "cpus": status.group(4),
                "status_lines": n})
    if status.group(5):
        row["date"] = status.group(5)
    peak, steps, elapsed, cpu = 0, {}, {}, {}
    for lg in sorted(glob.glob(os.path.join(logs, "*.log"))):
        with open(lg, errors="replace") as fh:
            t = fh.read()
        for m in STEP.finditer(t):
            k = os.path.basename(lg)[:-4]
            peak = max(peak, int(m.group(4)))
            steps[k] = int(m.group(4)) // 1024
            s = 0.0
            for x in [float(x) for x in m.group(1).split(":")]:
                s = s * 60 + x
            elapsed[k] = round(s, 2)
            cpu[k] = round(float(m.group(2)) + float(m.group(3)), 2)
    row.update({"peak_mem_mb": peak // 1024, "step_peak_mb": steps, "step_elapsed_s": elapsed, "step_cpu_s": cpu,
                "cpu_s": round(sum(cpu.values()), 1),
                "bytes": {"results": _dsize(res), "logs": _dsize(logs), "reports": _dsize(rep)}})
    if row["rc"] != 0:
        row["status"] = "failed"
        o = os.path.join(job_dir, "logs", job + ".out")
        o = _text(o) if os.path.exists(o) else ""
        errs = re.findall(r"\[ERROR [^\]]+\][^\n]*", o)
        row["error"] = errs[0][:300] if errs else None
        row["error_code"] = re.match(r"\[ERROR ([^\]]+)\]", errs[0]).group(1) if errs else None
        row["out_tail"] = o[-1500:]
        return row
    row["status"] = "ok"
    rj = os.path.join(logs, "6_report.json")
    r = json.loads(_text(rj), parse_float=Decimal) if os.path.exists(rj) else {}
    row["metrics"] = {k: str(x) for k, x in r.items() if k.startswith("finish__")}
    rpt = os.path.join(rep, "6_finish.rpt")
    if os.path.exists(rpt):
        row["period_min"] = re.findall(r"period_min = ([\d.]+)", _text(rpt))
    rl = os.path.join(logs, "5_2_route.json")
    if os.path.exists(rl):
        rr = json.loads(_text(rl), parse_float=Decimal)
        row["drc"] = rr.get("detailedroute__route__drc_errors")
        row["route_wirelength"] = str(rr.get("detailedroute__route__wirelength"))
    gl = os.path.join(logs, "5_1_grt.json")
    if os.path.exists(gl):
        gg = json.loads(_text(gl), parse_float=Decimal)
        row["grt_wirelength"] = str(gg["globalroute__route__wirelength"]) if "globalroute__route__wirelength" in gg \
            else None
    fv = os.path.join(res, "6_final.v")
    if os.path.exists(fv):
        row["final_hist"] = final_hist(fv)
    row["sha256"] = {f: (None if not os.path.exists(os.path.join(res, f)) else
                         spef_sha256(os.path.join(res, f)) if f.endswith(".spef") else pnr.sha256_file(os.path.join(res, f)))
                     for f in HASHED}
    row["lec"] = lec_verdicts(logs)
    return row


# ---- entry: the tree's data -----------------------------------------------------------------------------------------

def liberty_dir(explicit=None):
    return explicit or os.environ.get("SVGOLF_ASAP7_LIB") or os.path.join(pnr.SVGOLF, "score", "lib", "asap7")


def liberty_areas(lib_dir=None):
    """{cell: Decimal area in um^2} of the five pinned ASAP7 liberty files (score/ppa_pins_asap7.json), each checked by
    sha256. CollectError when a file is missing or another."""
    with open(os.path.join(pnr.SVGOLF, "score", "ppa_pins_asap7.json"), encoding="utf-8") as fh:
        files = json.load(fh)["liberty"]["files"]
    d, areas = liberty_dir(lib_dir), {}
    for f in files:
        p = os.path.join(d, f["file"])
        try:
            got = pnr.sha256_file(p)
        except OSError:
            raise CollectError(f"liberty {p} not found: `python3.12 score/ppa.py --pdk asap7 --fetch-liberty` fetches "
                               "the pinned files (or set $SVGOLF_ASAP7_LIB, or --liberty DIR)")
        if got != f["sha256"]:
            raise CollectError(f"liberty {p}: sha256 {got} is not the pinned {f['sha256']}")
        with open(p, encoding="ascii") as fh:
            text = fh.read()
        starts = [(m.start(), m.group(1)) for m in re.finditer(r"\bcell\s*\(\s*\"?([A-Za-z0-9_]+)\"?\s*\)\s*\{", text)]
        for i, (s, name) in enumerate(starts):
            e = starts[i + 1][0] if i + 1 < len(starts) else len(text)
            areas[name] = Decimal(re.search(r"\barea\s*:\s*([0-9.]+)", text[s:e]).group(1))
    return areas


def area_e5(hist, areas):
    """The cells of a histogram by the liberty's areas, exactly, in 1e-5 um^2."""
    missing = sorted(c for c in hist if c not in areas)
    if missing:
        raise CollectError(f"cells not in the pinned liberty: {missing}")
    t = sum((areas[c] * n for c, n in hist.items()), Decimal(0)) * 100000
    if t != t.to_integral_value():
        raise CollectError("the area is not a whole number of 1e-5 um^2")
    return int(t)


def half_even(x):
    return int(Decimal(x).quantize(Decimal(1), rounding=ROUND_HALF_EVEN))


def boxes(render_log):
    """{die_um, core_um} ([width, height] as decimal text) from layout.tcl's line in a render log."""
    m = BOX.search(render_log)
    if not m or "layout.tcl: done" not in render_log:
        raise CollectError("the render log has no finished layout.tcl run")
    dbu = Decimal(m.group(1))
    v = [int(x) for x in m.groups()[1:]]
    return {"die_um": [str((Decimal(v[2] - v[0]) / dbu).normalize()), str((Decimal(v[3] - v[1]) / dbu).normalize())],
            "core_um": [str((Decimal(v[6] - v[4]) / dbu).normalize()), str((Decimal(v[7] - v[5]) / dbu).normalize())]}


def build_entry(*, task_name, view_entry, of, request, row, mk_bytes, sdc_bytes, host, date, picture, render_log,
                areas, pins):
    """The routed entry of one design file scored by one job (see the module text). Pure; CollectError when the job
    is not this design's scoring run."""
    job = row["job"]
    nick, _variant, seed = pnr.parse_job(job)
    bad = pnr.config_problems(mk_bytes.decode(), pins, job)
    if bad:
        raise CollectError(f"{job}: config.mk is not a course job: " + "; ".join(bad))
    if seed != request["seed"]:
        raise CollectError(f"{job}: seed {seed} is not the request's seed {request['seed']}")
    if request.get("settings") != {}:
        raise CollectError("the course takes no layout settings yet")
    if nick != f"{task_name}_{view_entry['repaired_sha256'][:12]}":
        raise CollectError(f"{job} is not a job of this design's ASAP7 netlist")
    period = re.search(r"create_clock -name \S+ -period (\S+)", sdc_bytes.decode()).group(1)
    if Decimal(period) != Decimal(view_entry["delay_ps"]):
        raise CollectError(f"the SDC period {period} is not the ASAP7 view's delay {view_entry['delay_ps']}")
    cycles = view_entry["cycles"]
    run = {"seed": seed, "role": "scoring", "settings_sha256": pnr.sha256_bytes(b"{}"),
           "config_mk_sha256": pnr.sha256_bytes(mk_bytes), "sdc_sha256": pnr.sha256_bytes(sdc_bytes),
           "io_tcl_sha256": None, "host": host, "measured_at": date, "seconds": row.get("seconds"),
           "peak_mb": row.get("peak_mem_mb")}
    if run["settings_sha256"] != lb.pnr_settings_sha256({}):
        raise CollectError("the settings hash rule changed")
    lec = row.get("lec") or []
    ok = row.get("status") == "ok" and row.get("rc") == 0 and row.get("drc") == 0 and bool(lec) \
        and all(x.endswith(":IDENTICAL") for x in lec)
    run["status"] = "ok" if ok else "failed"
    if not ok:
        run["error"] = row.get("error") or (f"rc={row.get('rc')} status={row.get('status')} drc={row.get('drc')} "
                                            f"lec={lec} last step {row.get('last_step')}")
    else:
        mt, sha = row["metrics"], row["sha256"]
        if sha["1_2_yosys.v"] != view_entry["repaired_sha256"]:
            raise CollectError("the placed netlist (1_2_yosys.v) is not the design's ASAP7 netlist")
        ws = mt["finish__timing__setup__ws"]
        delay = half_even(Decimal(period) - Decimal(ws))
        area = area_e5(row["final_hist"], areas)
        time_ps = delay * (cycles if cycles is not None else 1)
        arts = {k: sha[k] for k in ARTIFACTS}
        arts["6_final.spef(normalized)"] = sha["6_final.spef"]
        run.update(orfs={"area_stdcell": mt["finish__design__instance__area__stdcell"],
                         "area_tap_cell": mt.get("finish__design__instance__area__class:tap_cell"), "setup_ws": ws,
                         "period_min": (row.get("period_min") or [None])[0], "sdc_period": period},
                   area_e5um2=area, delay_ps=delay, time_ps=time_ps, exact=area * time_ps, drc=row["drc"],
                   lec=list(lec),
                   drv={k: int(Decimal(mt.get(f"finish__timing__drv__{k}", "0")))
                        for k in ("max_slew", "max_cap", "max_fanout")},
                   hold_violations=int(Decimal(mt.get("finish__timing__drv__hold_violation_count", "0"))),
                   artifacts=dict(sorted(arts.items())), cells_in=view_entry["cells"],
                   cells_out=sum(row["final_hist"].values()), wire_um=row.get("route_wirelength"))
    recs = [x[len("record:"):] for x in of if x.startswith("record:")]
    e = {"sv_sha256": view_entry["sv_sha256"], "of": list(of), "record": recs[0] if recs else None,
         "netlist_sha256": view_entry["repaired_sha256"], "scored_netlist_sha256": view_entry["netlist_sha256"],
         "cycles": cycles, "a0_asap7": {"area_e5um2": view_entry["area_e5um2"], "delay_ps": view_entry["delay_ps"],
                                        "time_ps": view_entry["time_ps"]},
         "request": copy.deepcopy(request), "runs": [run]}
    scores, status = lb._pnr_scores(e)
    e.update(scores=scores, status=status, layout=None)
    if status == "measured":
        if picture is None or render_log is None:
            raise CollectError("a measured design needs its picture (encode.py's record) and its render log")
        need = {"png_sha256", "png_px", "px", "quality", "bytes", "sha256", "thumb_px", "thumb_bytes", "thumb_sha256"}
        if not need <= set(picture):
            raise CollectError(f"the picture record lacks {sorted(need - set(picture))}")
        b = boxes(render_log)
        sv16 = view_entry["sv_sha256"][:16]
        e["layout"] = {"image": f"images/{task_name}/{sv16}.webp", "image_sha256": picture["sha256"],
                       "image_px": picture["px"], "image_bytes": picture["bytes"], "webp_quality": picture["quality"],
                       "thumb": f"images/{task_name}/{sv16}.thumb.webp", "thumb_sha256": picture["thumb_sha256"],
                       "thumb_px": picture["thumb_px"], "thumb_bytes": picture["thumb_bytes"],
                       "render_png_sha256": picture["png_sha256"], "render_png_px": picture["png_px"],
                       "run_seed": seed, "odb_sha256": run["artifacts"]["6_final.odb"], "die_um": b["die_um"],
                       "core_um": b["core_um"], "view": LAYOUT_VIEW,
                       "caption": (f"The scored layout: placed and routed by OpenROAD-flow-scripts on ASAP7, placement "
                                   f"seed {seed}; die {Decimal(b['die_um'][0]):.1f} × {Decimal(b['die_um'][1]):.1f} µm "
                                   "(power and ground wires not drawn).")}
    return e


def tree_context(task_name):
    """(task, the ASAP7 view, the routed table or None, designs the task shows {sv_sha256: {of, ...}}) of the tree."""
    task = lb.load_task(lb.DEFAULT_TASKS, task_name)
    view, why = lb.read_asap7(task_name)
    if why or view is None:
        raise CollectError(why or f"no ASAP7 view for {task_name}")
    table, why = lb.read_asap7pnr(task_name)
    if why:
        raise CollectError(why)
    with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
        expected = json.load(fh)
    records = lb.good_records(lb.load_records(lb.DEFAULT_DATA))
    designs = lb.asap7_designs(task, records, expected)
    return task, view, table, designs


def stored_request(table, sv_sha256):
    """The request leaderboard/asap7pnr/<task>.json stores for the design file, or None."""
    e = lb.asap7pnr_entry(table, sv_sha256)
    return copy.deepcopy(e["request"]) if e is not None else None


def _read(path, binary=False):
    with open(path, "rb" if binary else "r", **({} if binary else {"encoding": "utf-8"})) as fh:
        return fh.read()


def cmd_entry(args):
    task, view, table, designs = tree_context(args.task)
    ve = lb.asap7_entry(view, args.sv)
    if ve is None or args.sv not in designs:
        raise CollectError(f"{args.sv[:16]}... is not a design file {args.task}'s pages show (or the ASAP7 view has "
                           "no entry for it)")
    request = stored_request(table, args.sv)
    if request is None:
        raise CollectError(f"leaderboard/asap7pnr/{args.task}.json stores no request for this design file: make one "
                           "first (`leaderboard.py asap7pnr --request --task T --design FILE [--seed N] --write`)")
    nick, _v, _s = pnr.parse_job(args.job)
    j = args.job_dir
    row = json.loads(_read(args.row or os.path.join(j, "rows", args.job + ".json")))
    host = json.loads(_read(args.host or os.path.join(j, "logs", args.job + ".host.json")))
    date = args.date or row.get("date")
    if not (isinstance(date, str) and re.fullmatch(r"\d{4}-\d\d-\d\d", date)):
        raise CollectError("no date for the run (the status line has none): give --date YYYY-MM-DD")
    pic_path = args.picture or os.path.join(j, "img", f"{args.job}.{args.sv[:16]}.json")
    log_path = args.render_log or os.path.join(j, "logs", args.job + ".render.out")
    e = build_entry(task_name=args.task, view_entry=ve, of=designs[args.sv]["of"], request=request, row=row,
                    mk_bytes=_read(os.path.join(j, "cfg", args.job + ".mk"), True),
                    sdc_bytes=_read(os.path.join(j, "sdc", nick + ".sdc"), True), host=host, date=date,
                    picture=json.loads(_read(pic_path)) if os.path.exists(pic_path) else None,
                    render_log=_read(log_path) if os.path.exists(log_path) else None,
                    areas=liberty_areas(args.liberty), pins=pnr.load_pins())
    return e


def sitedata(task_name, out_dir, new_entries, *, table, view, svgolf=pnr.SVGOLF, pins=None):
    """Write out_dir/sitedata/<task>.json (the tree's table with `new_entries` added) and copy the carried entries'
    pictures to out_dir/images/<task>/. Returns the data. CollectError on a conflict."""
    pins = pins or pnr.load_pins()
    if table is None:
        raise CollectError(f"the tree has no routed table for {task_name} (leaderboard/asap7pnr/{task_name}.json)")
    if {k: table["course"][k] for k in lb.PNR_PINNED} != pins:
        raise CollectError("the tree's routed table was made under other pins")
    by_sha = {e["sv_sha256"]: copy.deepcopy(e) for e in table["designs"]}
    new_shas = set()
    for ne in new_entries:
        old = by_sha.get(ne["sv_sha256"])
        if old is not None and any(r.get("role") == "scoring" for r in old["runs"]):
            back = copy.deepcopy(old)
            if isinstance(back.get("layout"), dict):
                for key in ("image", "thumb"):
                    back["layout"][key] = "images/" + back["layout"][key][len(lb.PNR_LAYOUTS) + 1:]
            if back != ne:
                raise CollectError(f"{ne['sv_sha256'][:16]}... already has a scoring run: one run per design (a new "
                                   "run replaces it only if it is that entry, byte for byte)")
        by_sha[ne["sv_sha256"]] = copy.deepcopy(ne)
        new_shas.add(ne["sv_sha256"])
    img = os.path.join(out_dir, "images", task_name)
    os.makedirs(img, exist_ok=True)
    designs = []
    for sha in sorted(by_sha):
        e = by_sha[sha]
        L = e.get("layout")
        if isinstance(L, dict) and sha not in new_shas:
            for key in ("image", "thumb"):
                src = os.path.join(svgolf, *L[key].split("/"))
                if pnr.sha256_file(src) != L[f"{key}_sha256"]:
                    raise CollectError(f"{L[key]} is not the picture its entry records")
                name = os.path.basename(L[key])
                shutil.copyfile(src, os.path.join(img, name))
                L[key] = f"images/{task_name}/{name}"
        elif isinstance(L, dict):
            for key in ("image", "thumb"):
                p = os.path.join(out_dir, *L[key].split("/"))
                if not os.path.isfile(p) or pnr.sha256_file(p) != L[f"{key}_sha256"]:
                    raise CollectError(f"{L[key]}: missing under {out_dir} or not the picture the entry records "
                                       "(encode.py writes it there)")
        designs.append(e)
    data = {"_comment": "Collected by score/pnr/collect.py for `leaderboard.py asap7pnr --import`; do not edit.",
            "schema": lb.ASAP7PNR_SCHEMA, "task": task_name, "scoring_point": view["scoring_point"],
            "asap7_view": {"identity": view["identity"], "ppa_script_sha256": view["ppa_script_sha256"]},
            "course": copy.deepcopy(table["course"]), "designs": designs}
    os.makedirs(os.path.join(out_dir, "sitedata"), exist_ok=True)
    with open(os.path.join(out_dir, "sitedata", f"{task_name}.json"), "w", encoding="utf-8") as fh:
        fh.write(json.dumps(data, indent=1, sort_keys=True) + "\n")
    return data


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("row")
    r.add_argument("job_dir")
    r.add_argument("job")
    r.add_argument("--out")
    e = sub.add_parser("entry")
    e.add_argument("--task", required=True)
    e.add_argument("--sv", required=True, help="the design file's sha256")
    e.add_argument("job_dir")
    e.add_argument("job")
    for opt in ("--row", "--host", "--render-log", "--picture", "--date", "--liberty", "--out"):
        e.add_argument(opt)
    s = sub.add_parser("sitedata")
    s.add_argument("--task", required=True)
    s.add_argument("--out", required=True)
    s.add_argument("entries", nargs="+")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "row":
            out = collect_row(args.job_dir, args.job)
        elif args.cmd == "entry":
            out = cmd_entry(args)
        else:
            _task, view, table, _designs = tree_context(args.task)
            data = sitedata(args.task, args.out, [json.loads(_read(p)) for p in args.entries], table=table, view=view)
            print(f"wrote {os.path.join(args.out, 'sitedata', args.task + '.json')}: {len(data['designs'])} entries")
            return 0
    except (OSError, ValueError, KeyError, CollectError) as ex:
        print(f"error: {ex}", file=sys.stderr)
        return 2
    text = json.dumps(out, indent=1, sort_keys=True) + "\n"
    if getattr(args, "out", None):
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
