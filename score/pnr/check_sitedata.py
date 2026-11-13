#!/usr/bin/env python3
"""check_sitedata.py: check collected routed-course data before it is imported (score/pnr/README.md).

    python3.12 score/pnr/check_sitedata.py OUTDIR [--task T ...] [--jobs JOBDIR ...] [--liberty DIR]

OUTDIR is what `collect.py sitedata` wrote (OUTDIR/sitedata/<task>.json, OUTDIR/images/<task>/); each JOBDIR a job
directory whose runs it holds (cfg/, sdc/, rows/, img/, logs/). It shares no code with collect.py: every number is
derived again from the job's own files, the area with score/ppa.py's own liberty reader. Problems:
  import     what `leaderboard.py asap7pnr --import` refuses (written form, shape and arithmetic, each picture's bytes,
             sha256 and pixel size), an entry for a design the task does not show, a design that would not be bound
             (`asap7pnr_status`: failed, stale, unbound) under the tree's ASAP7 view, scoring point and pins
  one run    an entry the tree already has with a scoring run must come back unchanged (one run per design); the
             request of a design the tree has is the tree's (a request is never changed by a collection), and a new
             entry needs a request the tree stores (leaderboard.py asap7pnr --request)
  runs       for every run that is not the tree's, from its job directory: config.mk and SDC are the recorded files
             (sha256), the config.mk holds the pinned ORFS variables and no other, its seed is the run's and the
             request's; the SDC period is the ASAP7 view's delay; the collected row says exit 0, DRC 0 and every
             equivalence log IDENTICAL for a valid run; area = the liberty's areas over the row's cell histogram (exact);
             delay = half-even(period - worst setup slack); artifacts = the row's hashes (the SPEF's normalized one)
  pictures   the render PNG is the recorded one (sha256, pixel size), the die box is the render log's, the caption
             names the seed; with the Pillow and libwebp the committed pictures were made with (11.1.0, 1.5.0), the
             picture is the render encoded again at its recorded size and quality, byte for byte, and the thumbnail
             the render at its recorded size and quality 80, or at another quality of 79 to 50 (a thumbnail encoded
             again one step away for the publication scan: the entry records no thumbnail quality; a note says which);
             otherwise a note says the bytes were not re-derived
Exit status: 0 no problem, 1 problems, 2 usage or infrastructure (no liberty, an unreadable file)."""

import argparse
import copy
import hashlib
import io
import json
import os
import re
import sys
from decimal import ROUND_HALF_EVEN, Decimal

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(SVGOLF, "leaderboard"))
sys.path.insert(0, os.path.join(SVGOLF, "score"))
import leaderboard as lb  # noqa: E402

PER_JOB = {"DESIGN_NAME", "DESIGN_NICKNAME", "PLATFORM", "SYNTH_NETLIST_FILES", "VERILOG_FILES", "SDC_FILE",
           "FLOW_VARIANT", "WORK_HOME", "GPL_RANDOM_SEED"}
ARTS = {"1_2_yosys.v": "1_2_yosys.v", "6_final.def": "6_final.def", "6_final.v": "6_final.v",
        "6_final.spef(normalized)": "6_final.spef", "6_final.odb": "6_final.odb", "2_floorplan.odb": "2_floorplan.odb",
        "3_place.odb": "3_place.odb", "4_cts.odb": "4_cts.odb", "5_route.odb": "5_route.odb"}


def H(b):
    return hashlib.sha256(b).hexdigest()


def liberty_area_reader(lib_dir=None):
    """cell -> Decimal area, by score/ppa.py's own liberty reader (the pinned ASAP7 files, sha256-checked by it)."""
    import ppa
    pins = ppa.Pins(ppa.pdk_paths("asap7")[0])
    lib, _ = ppa.open_library(lib_dir, pins)

    def area(cell):
        return Decimal(str(lib.group(cell).attrs["area"])) if lib.has(cell) else None
    return area


def _png_px(b):
    return [int.from_bytes(b[16:20], "big"), int.from_bytes(b[20:24], "big")] if b[:8] == b"\x89PNG\r\n\x1a\n" else None


def _reencode(png, L):
    """(whether the picture is the render encoded at the entry's recorded size and quality, the quality 80..50 at which
    the render at the thumbnail's size gives the thumbnail, or None), or None without the Pillow and libwebp the
    committed pictures were made with."""
    try:
        import PIL
        from PIL import Image, features
    except ImportError:
        return None
    if (PIL.__version__, features.version("webp")) != ("11.1.0", "1.5.0"):
        return None
    im = Image.open(io.BytesIO(png)).convert("RGB")

    def webp(px, q):
        x = im if list(im.size) == px else im.resize(tuple(px), Image.Resampling.LANCZOS)
        buf = io.BytesIO()
        x.save(buf, format="WEBP", quality=q, method=6, exact=False)
        return buf.getvalue()
    pic_ok = H(webp(L["image_px"], L["webp_quality"])) == L["image_sha256"]
    thumb_q = next((q for q in range(80, 49, -1) if H(webp(L["thumb_px"], q)) == L["thumb_sha256"]), None)
    return pic_ok, thumb_q


def _bytes(path):
    with open(path, "rb") as fh:
        return fh.read()


def _find(job_dirs, *rel):
    for d in job_dirs:
        p = os.path.join(d, *rel)
        if os.path.isfile(p):
            return p
    return None


def check_run(w, run, ent, task_name, job_dirs, area_of, pins, P, N):
    """Problems (via P) and notes (via N) of one run that is not the tree's."""
    nick = f"{task_name}_{ent['netlist_sha256'][:12]}"
    job = f"{nick}__min_s{run['seed']}"
    mk_p, sdc_p, row_p = (_find(job_dirs, "cfg", job + ".mk"), _find(job_dirs, "sdc", nick + ".sdc"),
                          _find(job_dirs, "rows", job + ".json"))
    if not (mk_p and sdc_p and row_p):
        P(f"{w}: the job {job} is not in the job directories (cfg/, sdc/, rows/)")
        return
    mk, sdc = _bytes(mk_p), _bytes(sdc_p)
    row = json.loads(_bytes(row_p))
    if H(mk) != run["config_mk_sha256"] or H(sdc) != run["sdc_sha256"]:
        P(f"{w}: config.mk or SDC is not the job's file (sha256)")
    var = {m.group(1): m.group(2) for m in re.finditer(r"^export (\w+) = (.*)$", mk.decode(), re.M)}
    if {k: v for k, v in var.items() if k not in PER_JOB} != pins["orfs_variables"] or not PER_JOB <= set(var):
        P(f"{w}: config.mk's ORFS variables are not the pinned ones")
    if var.get("GPL_RANDOM_SEED") != str(run["seed"]) or var.get("DESIGN_NICKNAME") != nick \
            or var.get("FLOW_VARIANT") != f"min_s{run['seed']}":
        P(f"{w}: config.mk's seed or nickname is not the run's")
    if run["seed"] != ent["request"]["seed"] and run["role"] == "scoring":
        P(f"{w}: the scoring run is not at the request's seed")
    m = re.search(rb"create_clock -name \S+ -period (\S+)", sdc)
    period = m.group(1).decode() if m else None
    if period is None or Decimal(period) != Decimal(ent["a0_asap7"]["delay_ps"]):
        P(f"{w}: the SDC period is not the ASAP7 view's delay")
        return
    if row.get("job") != job:
        P(f"{w}: the row is another job's")
        return
    valid = row.get("status") == "ok" and row.get("rc") == 0 and row.get("drc") == 0 and bool(row.get("lec")) \
        and all(x.endswith(":IDENTICAL") for x in row["lec"])
    if (run["status"] == "ok") != valid:
        P(f"{w}: status {run['status']!r}, but the row says exit {row.get('rc')}, DRC {row.get('drc')}, "
          f"equivalence {row.get('lec')}")
        return
    if (run["seconds"], run["peak_mb"]) != (row.get("seconds"), row.get("peak_mem_mb")):
        P(f"{w}: seconds or peak memory are not the row's")
    if run["status"] != "ok":
        return
    mt = row["metrics"]
    o = run["orfs"]
    if (o["setup_ws"], o["period_min"], o["sdc_period"], o["area_stdcell"], o["area_tap_cell"]) != (
            mt["finish__timing__setup__ws"], (row.get("period_min") or [None])[0], period,
            mt["finish__design__instance__area__stdcell"], mt.get("finish__design__instance__area__class:tap_cell")):
        P(f"{w}: the raw ORFS texts are not the row's")
    cells = row["final_hist"]
    areas = {c: area_of(c) for c in cells}
    if any(a is None for a in areas.values()):
        P(f"{w}: a cell outside the pinned liberty: {sorted(c for c, a in areas.items() if a is None)}")
    else:
        a = sum((areas[c] * n for c, n in cells.items()), Decimal(0)) * 100000
        if a != a.to_integral_value() or int(a) != run["area_e5um2"]:
            P(f"{w}: area_e5um2 {run['area_e5um2']} is not the liberty's sum over the routed cells ({a})")
    d = Decimal(period) - Decimal(mt["finish__timing__setup__ws"])
    if int(d.quantize(Decimal(1), rounding=ROUND_HALF_EVEN)) != run["delay_ps"]:
        P(f"{w}: delay_ps is not half-even(period - worst setup slack)")
    if {k: row["sha256"].get(v) for k, v in ARTS.items()} != run["artifacts"]:
        P(f"{w}: artifacts are not the row's hashes")
    if run["cells_out"] != sum(cells.values()) or run["cells_in"] is None:
        P(f"{w}: cells_out is not the routed netlist's cell count")
    if run["role"] != "scoring" or ent["layout"] is None:
        return
    L = ent["layout"]
    png_p = _find(job_dirs, "img", job + ".png")
    log_p = _find(job_dirs, "logs", job + ".render.out")
    if not png_p or not log_p:
        P(f"{w}: the render ({job}.png) or its log is not in the job directories")
        return
    png = _bytes(png_p)
    if H(png) != L["render_png_sha256"] or _png_px(png) != L["render_png_px"]:
        P(f"{w}: the render PNG is not the recorded one")
    m = re.search(r"layout\.tcl: dbu_per_micron (\d+) die (-?\d+) (-?\d+) (-?\d+) (-?\d+)", _bytes(log_p).decode("utf-8", "replace"))
    if not m:
        P(f"{w}: the render log has no die box")
    else:
        dbu, x0, y0, x1, y1 = (Decimal(m.group(i)) for i in range(1, 6))
        if [Decimal(v) for v in L["die_um"]] != [(x1 - x0) / dbu, (y1 - y0) / dbu]:
            P(f"{w}: the die box is not the render log's")
    if f"seed {run['seed']}" not in L["caption"] or L["run_seed"] != run["seed"] \
            or L["odb_sha256"] != run["artifacts"]["6_final.odb"]:
        P(f"{w}: the picture is not named as the scoring run's (seed, 6_final.odb)")
    again = _reencode(png, L)
    if again is None:
        N(f"{w}: picture bytes not re-derived from the render (another Pillow or libwebp than 11.1.0 / 1.5.0)")
    elif not again[0] or again[1] is None:
        P(f"{w}: the picture or thumbnail is not the render encoded at its recorded size and quality")
    elif again[1] != 80:
        N(f"{w}: the thumbnail is the render encoded at quality {again[1]}, not 80 (encoded again one step away?)")


def check(out_dir, task_name, job_dirs, *, area_of, pins=None, tree=None):
    """(problems, notes) of OUTDIR/sitedata/<task>.json against the tree and the job directories. `tree`: the tree's
    routed table of the task (default: read leaderboard/asap7pnr/<task>.json)."""
    problems, notes = [], []
    P, N = problems.append, notes.append
    pins = pins if pins is not None else lb.asap7pnr_identity()
    task = lb.load_task(lb.DEFAULT_TASKS, task_name)
    view, why = lb.read_asap7(task_name)
    if why or view is None:
        return [f"{task_name}: the tree's ASAP7 view: {why}"], notes
    if tree is None:
        tree, why = lb.read_asap7pnr(task_name)
        if why:
            return [f"{task_name}: the tree's routed table: {why}"], notes
    with open(lb.EXPECTED_JSON, encoding="utf-8") as fh:
        expected = json.load(fh)
    designs = lb.asap7_designs(task, lb.good_records(lb.load_records(lb.DEFAULT_DATA)), expected)
    try:
        data, _pictures, dropped, bad = lb.asap7pnr_import(out_dir, task_name, designs)
    except (OSError, ValueError, KeyError) as e:
        return [f"{task_name}: cannot be imported: {e}"], notes
    problems += [f"{task_name}: import: {x}" for x in bad]
    problems += [f"{task_name}: an entry for no design the task shows ({', '.join(e['of'])})" for e in dropped]
    if {k: (data.get("course") or {}).get(k) for k in lb.PNR_PINNED} != pins:
        P(f"{task_name}: the course block is not score/pnr/pins.json")
    if bad:
        return problems, notes
    for e in data["designs"]:
        w = f"{task_name}/{e['sv_sha256'][:12]}"
        status, why, _ = lb.asap7pnr_status(data, view, e["sv_sha256"], task=task, pins=pins)
        if status not in ("bound", "pending"):
            P(f"{w}: {status}: {why}")
        old = lb.asap7pnr_entry(tree, e["sv_sha256"])
        if old is not None and any(r.get("role") == "scoring" for r in old["runs"]) and e != old:
            P(f"{w}: the tree's entry has a scoring run and this one is not it (one run per design)")
        if old is not None and e["request"] != old["request"]:
            P(f"{w}: the request is not the one the tree stores")
        if old is None:
            P(f"{w}: the tree stores no request for this design (make one with leaderboard.py asap7pnr --request)")
        for i, run in enumerate(e["runs"]):
            if old is not None and run in old["runs"]:
                continue                         # the tree's own run, carried unchanged (checked when it came in)
            check_run(f"{w} run {i} ({run.get('role')}, seed {run.get('seed')})", run, e, task_name, job_dirs,
                      area_of, pins, P, N)
    return problems, notes


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("out_dir")
    ap.add_argument("--task", action="append", default=[], help="(repeatable) default: every OUTDIR/sitedata/*.json")
    ap.add_argument("--jobs", action="append", default=[], metavar="JOBDIR", help="(repeatable) a job directory")
    ap.add_argument("--liberty", help="the pinned ASAP7 liberty directory (else $SVGOLF_ASAP7_LIB, score/lib/asap7)")
    args = ap.parse_args(argv)
    tasks = args.task or sorted(f[:-5] for f in os.listdir(os.path.join(args.out_dir, "sitedata")) if f.endswith(".json"))
    try:
        area_of = liberty_area_reader(args.liberty)
    except Exception as e:                       # ppa.PpaError and anything the liberty reader raises: infrastructure
        print(f"error: the pinned ASAP7 liberty: {e}", file=sys.stderr)
        return 2
    n = 0
    for t in tasks:
        problems, notes = check(args.out_dir, t, args.jobs, area_of=area_of)
        for x in problems:
            print("PROBLEM", x)
        for x in notes:
            print("note", x)
        n += len(problems)
    print(f"check_sitedata: {len(tasks)} task(s), {n} problem(s)")
    return 1 if n else 0


if __name__ == "__main__":
    sys.exit(main())
