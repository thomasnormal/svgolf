#!/usr/bin/env python3.12
"""Measured at several points: the pinned flow at every parameter point of score/points.json, on every reference and
baseline of each task, written to score/measured/<task>.json for the site's explorer (PLAN4 section 3b, step 2b).

    python3.12 score/points.py plan    [--task T ...] [--records]     # what would be measured (no tool runs)
    nice -n 19 python3.12 score/points.py measure [--task T ...] [--records] [--retry-skipped] [--timings OUT.json]
    python3.12 score/points.py check   [--task T ...]                 # the committed data against the plan and the goldens

MEASUREMENT ONLY. Every proof holds at every point of its task's range, so a point other than the scored one is the
same proved design at other parameters; the ranked board stays at task.json's `scoring.params` and nothing here ranks
anything. The site shows these numbers as "measured, not ranked".

THE SAME PINNED FLOW. Each (design, point) is one run of `score/ppa.py SV --task tasks/<t> --param K=V ... --no-mapped`
(`--seq` for a clocked task) in its own process: score.py's two Yosys processes, the A0' weighing of the scored
netlist, the repair by buffering, the static timing analysis under the task's input drive, on the pinned liberty. At
the scored point that is exactly how the goldens were recorded, and `check` (and score/test_points.py) asserts that the
data equals them bit for bit: score/tests/ppa/expected_ppa.json for every design of designs.json, tests/expected.json's
GE columns at EVERY point where it has them, and its clocked columns (area, period, cycles, time) at the scored point.

THE DESIGNS of a task: the maintainers' proved designs, the references of task.json (one of them is par's design,
leaderboard/par.json; decided 2026-11-12, every other one is an entry, shown once a player's record holds it) and the
baselines of tests/expected.json (each names its proof, `lean`, and a baseline without one is a plan error, decided
2026-11-12: every design the site shows has a kernel-checked proof; one with a banned operator is a comparison design,
never an entry, one without is an entry like a reference that is not par; a baseline with `banlist_points` is a
fixed-size design and is measured at those points only), and with `--records` the leaderboard
records of the players (not the reference player's, which are par's; a record whose design file is a
reference's or baseline's is that design). A design file shared by two entries is measured once.

A CLOCKED task's time is cycles x the register-to-register period. The cycles at a point are the latency function the
design's own proof defines (`def lat (N _W : Nat) : Nat := 2 * N` in its .lean; `latency_of` reads that one line and
evaluates it, checking it against the `-- svgolf-latency: n` header at the scored point); a design without one (a
clocked baseline) has a period but no time.

DROPS. A point other than the scored one whose flow fails, or does not finish within the task's time limit (task.json
`time_limit_s`), is dropped for that design with the reason; the scored point has no limit beyond the pinned flow's own
and a failure there is an error (nothing is written). `skip` in points.json pins a drop without running it (the
measured reason and time recorded there); `--retry-skipped` runs those too.

Deterministic: the data has no clock reading or wall time in it (`--timings` writes those elsewhere), keys and lists
are sorted, so two measurements give the same bytes. Run it under `nice -n 19`, one process at a time: the runs are
sequential by design.

Exit status: 0 done, 1 a measurement or a check failed, 2 usage error.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
CONFIG = os.path.join(HERE, "points.json")
OUT_DIR = os.path.join(HERE, "measured")
PPA_PY = os.path.join(HERE, "ppa.py")
DESIGNS = os.path.join(HERE, "tests", "ppa", "designs.json")
EXPECTED_PPA = os.path.join(HERE, "tests", "ppa", "expected_ppa.json")
EXPECTED = os.path.join(SVGOLF, "tests", "expected.json")
TASKS = os.path.join(SVGOLF, "tasks")
RECORDS = os.path.join(SVGOLF, "leaderboard", "data")
SCHEMA = "svgolf-points/1"
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family", "react-family")
LATENCY_KINDS = ("tx-family", "stream-family")
REFERENCE_PLAYER = "svgolf-reference"        # par's player (site/config.json `reference_player`)
KIND_ORDER = {"reference": 0, "baseline": 1, "record": 2}
# the flow files a clocked and a combinational run hash (score.py's FLOWS), relative to score/
FLOW_FILES = {"comb": ("svgolf.ys", "ge.json"), "seq": ("svgolf_seq.ys", "ge_seq.json")}
GOLDEN_KEYS = ("area_ge", "depth", "gates", "cells", "area_e4um2", "delay_ps", "unit_depth", "netlist_sha256",
               "repaired_sha256", "rtlil_sha256")     # expected_ppa.json's columns, named so in the data but for:
GOLDEN_TO_DATA = {"gates": "num_gates"}


class PlanError(Exception):
    pass


def load_json(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def _load_leaderboard():
    spec = importlib.util.spec_from_file_location("svgolf_leaderboard_points",
                                                  os.path.join(SVGOLF, "leaderboard", "leaderboard.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


lb = _load_leaderboard()


# ---------------------------------------------------------------------------
# points and the latency function
# ---------------------------------------------------------------------------

def param_order(task):
    """The task's parameter names in task.json's order (the scoring point's, as tests/expected.json keys it)."""
    return list(task["scoring"]["params"])


def point_key(params, order):
    """'N=16', 'W=5,P=11', 'N=4,W=8,AccW=32', or 'default' (tests/expected.json's keys)."""
    return ",".join(f"{k}={int(params[k])}" for k in order) or "default"


def point_text(params, order):
    return ", ".join(f"{k} = {int(params[k])}" for k in order) or "the one fixed size"


LAT_DEF = re.compile(r"^def[ \t]+lat[ \t]+((?:\([^()]*\)[ \t]*)+):[ \t]*Nat[ \t]*:=[ \t]*([^\n]+?)[ \t]*$", re.M)
LAT_BINDERS = re.compile(r"\(([^():]*):[ \t]*Nat[ \t]*\)")
LATENCY_HEADER = re.compile(r"^--[ \t]*svgolf-latency:(.*)$", re.M)     # check.py's
TOKEN = re.compile(r"\s*(?:(\d+)|([A-Za-z_][A-Za-z_0-9']*)|(.))")


def eval_nat(expr, env):
    """A natural-number expression of `def lat` (binder names, literals, + - * / and parentheses; Lean's Nat: `-`
    truncates at 0, `/` rounds down, `/ 0` is 0) at `env`, or None if it is anything else."""
    toks, pos = [], 0
    while pos < len(expr):
        m = TOKEN.match(expr, pos)
        if not m or m.end() == pos:
            break
        pos = m.end()
        if m.group(1):
            toks.append(("n", int(m.group(1))))
        elif m.group(2):
            if m.group(2) not in env:
                return None
            toks.append(("n", env[m.group(2)]))
        elif m.group(3).strip():
            toks.append(("op", m.group(3)))
    k = [0]

    def peek():
        return toks[k[0]] if k[0] < len(toks) else ("end", None)

    def atom():
        t = peek()
        k[0] += 1
        if t[0] == "n":
            return t[1]
        if t == ("op", "("):
            v = add()
            if peek() != ("op", ")"):
                raise ValueError("expected )")
            k[0] += 1
            return v
        raise ValueError(f"unexpected {t}")

    def mul():
        v = atom()
        while peek() in (("op", "*"), ("op", "/")):
            op = peek()[1]
            k[0] += 1
            w = atom()
            v = v * w if op == "*" else (v // w if w else 0)
        return v

    def add():
        v = mul()
        while peek() in (("op", "+"), ("op", "-")):
            op = peek()[1]
            k[0] += 1
            w = mul()
            v = v + w if op == "+" else max(0, v - w)
        return v

    try:
        v = add()
    except ValueError:
        return None
    return v if peek()[0] == "end" else None


def latency_of(lean_text, order):
    """(the `def lat` line, {params tuple -> n} as a function) of a clocked design's proof, or (None, None): its latency
    function, evaluated by `eval_nat` over the binders in task.json's parameter order."""
    m = LAT_DEF.search(lean_text)
    if not m:
        return None, None
    names = [n for grp in LAT_BINDERS.findall(m.group(1)) for n in grp.split()]
    if len(names) != len(order):
        return None, None
    expr = m.group(2)

    def at(params):
        return eval_nat(expr, {n: int(params[p]) for n, p in zip(names, order)})
    return m.group(0).strip(), at


def declared_latency(lean_text):
    found = LATENCY_HEADER.findall(lean_text)
    if len(found) != 1 or not re.fullmatch(r"\s*[1-9][0-9]*\s*", found[0]):
        return None
    return int(found[0])


# ---------------------------------------------------------------------------
# the plan: which design at which point
# ---------------------------------------------------------------------------

def rel(path):
    return os.path.relpath(path, SVGOLF).replace(os.sep, "/")


def task_plan(name, tcfg, *, expected, records=None):
    """The measurement plan of one task (pure apart from reading the design files): {"task", "kind", "top", "order",
    "scored", "limit", "scale", "points": [{key, params, label, x, scored}], "designs": [...], "skip": {(id, key): entry}}.
    Each design: {id, kind, name, src (relative to svgolf/), sha256, banned, family, lean, points (keys)}; a baseline's
    `lean` is its proof (tests/expected.json `lean`, relative to tests/<task>/), required. `records`:
    leaderboard records (dicts) to include, or None."""
    task = lb.load_task(TASKS, name)
    order = param_order(task)
    scored_key = point_key(task["scoring"]["params"], order)
    scale = tcfg.get("scale") or (order[0] if len(order) == 1 else None)
    if order and scale not in order:
        raise PlanError(f"{name}: `scale` must name one of the parameters {order} (a multi-parameter task names it)")
    points, labels = [], set()
    for p in tcfg.get("points") or []:
        params = p.get("params")
        if not isinstance(params, dict) or set(params) != set(order) or not all(
                isinstance(v, int) and not isinstance(v, bool) and v >= 1 for v in params.values()):
            raise PlanError(f"{name}: point {p!r}: `params` must give every parameter {order} a positive integer")
        key = point_key(params, order)
        label = p.get("label")
        text = label or point_text(params, order)
        if key in [q["key"] for q in points] or text in labels:
            raise PlanError(f"{name}: point {key} twice (or its label twice)")
        labels.add(text)
        points.append({"key": key, "params": {k: int(params[k]) for k in order}, "label": label,
                       "x": int(params[scale]) if scale else None, "scored": key == scored_key})
    if scored_key not in [p["key"] for p in points]:
        raise PlanError(f"{name}: the scored point {scored_key} (task.json scoring.params) is not one of its points")
    points.sort(key=lambda p: (p["x"] if p["x"] is not None else 0, p["key"]))
    keys = [p["key"] for p in points]
    exp = expected["tasks"].get(name, {})
    designs = []
    for ref in task.get("references", []):
        stem = os.path.splitext(os.path.basename(ref["sv"]))[0]
        designs.append({"id": f"reference/{stem}", "kind": "reference", "name": stem,
                        "src": f"tasks/{name}/{ref['sv']}", "lean": f"tasks/{name}/{ref['lean']}",
                        "banned": False, "points": list(keys)})
    for stem, e in sorted((exp.get("baselines") or {}).items()):
        if not e.get("lean"):
            raise PlanError(f"{name}: the baseline {stem} names no proof (tests/expected.json `lean`): every design the "
                            "site shows is proved")
        mine = [k for k in keys if k in e["banlist_points"]] if "banlist_points" in e else list(keys)
        designs.append({"id": f"baseline/{stem}", "kind": "baseline", "name": stem,
                        "src": f"tests/{name}/" + e.get("sv", f"baselines/{stem}.sv"), "lean": f"tests/{name}/{e['lean']}",
                        "banned": bool(e.get("banned")), "points": mine})
    for d in designs:
        d["sha256"] = sha256_file(os.path.join(SVGOLF, d["src"]))
        if d["kind"] == "baseline" and not os.path.isfile(os.path.join(SVGOLF, d["lean"])):
            raise PlanError(f"{name}: the proof {d['lean']} of the baseline {d['name']} is not there")
    known = {d["sha256"] for d in designs}
    for r in sorted(records or [], key=lambda r: r["record_hash"]):
        if r["task"] != name or r["player"] == REFERENCE_PLAYER or r["files"]["sv"]["sha256"] in known:
            continue
        h = r["record_hash"]
        designs.append({"id": h, "kind": "record", "name": r["player"], "src": f"leaderboard/data/{name}/{h}.sv",
                        "lean": f"leaderboard/data/{name}/{h}.lean", "banned": False, "points": list(keys),
                        "sha256": r["files"]["sv"]["sha256"]})
        known.add(r["files"]["sv"]["sha256"])
    family = {}
    for fam, stems in sorted((tcfg.get("families") or {}).items()):
        for stem in stems:
            if f"baseline/{stem}" not in [d["id"] for d in designs] or stem in family:
                raise PlanError(f"{name}: family {fam}: {stem} is not a baseline of the task (or in two families)")
            family[stem] = fam
    for d in designs:
        d["family"] = family.get(d["name"], d["name"]) if d["kind"] == "baseline" else d["name"]
    skip = {}
    for s in tcfg.get("skip") or []:
        d = next((d for d in designs if s.get("design") in (d["id"], d["name"]) and d["kind"] != "record"), None)
        if d is None or s.get("point") not in d["points"] or not s.get("reason"):
            raise PlanError(f"{name}: skip {s!r}: names no (design, point) of the plan, or gives no reason")
        if s["point"] == scored_key:
            raise PlanError(f"{name}: skip {s!r}: the scored point is never skipped")
        skip[(d["id"], s["point"])] = s
    designs.sort(key=lambda d: (KIND_ORDER[d["kind"]], d["name"], d["id"]))
    return {"task": name, "kind": task.get("kind"), "top": task["top"], "order": order, "scored": scored_key,
            "limit": task.get("time_limit_s"), "points": points, "designs": designs, "skip": skip,
            "scale": {"param": scale, "label": tcfg.get("scale_label") or scale},
            "seq": task.get("kind") in CLOCKED_KINDS}


def full_plan(config, tasks=None, *, records=False):
    expected = load_json(EXPECTED)
    recs = lb.good_records(lb.load_records(RECORDS)) if records else None
    names = sorted(config["tasks"])
    if tasks:
        unknown = sorted(set(tasks) - set(names))
        if unknown:
            raise PlanError(f"points.json has no task {', '.join(unknown)}")
        names = [n for n in names if n in tasks]
    plans = {n: task_plan(n, config["tasks"][n], expected=expected, records=recs) for n in names}
    # every design of designs.json (the sky130 goldens) is in the plan, at its point
    for g in load_json(DESIGNS)["designs"]:
        if g["task"] not in plans:
            continue
        p = plans[g["task"]]
        key = point_key(g.get("params") or {}, p["order"])
        if not any(d["src"] == g["src"] and key in d["points"] for d in p["designs"]):
            raise PlanError(f"designs.json's {g['name']} ({g['src']} at {key}) is not in the plan of {g['task']}")
    return plans


# ---------------------------------------------------------------------------
# one measurement
# ---------------------------------------------------------------------------

def run_ppa(plan, d, point, timeout):
    """One run of score/ppa.py on design `d` at `point` in its own process group. Returns (ppa.py's JSON result or
    None, the failure reason or None, wall seconds)."""
    cmd = [sys.executable, PPA_PY, os.path.join(SVGOLF, d["src"]), "--task", os.path.join(TASKS, plan["task"]),
           "--no-mapped"] + [a for k, v in point["params"].items() for a in ("--param", f"{k}={v}")]
    if plan["seq"]:
        cmd.append("--seq")
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True,
                            env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)              # ppa.py and the Yosys it runs
        proc.communicate()
        return None, (f"the pinned flow did not finish within the task's time limit ({timeout} s)"), time.time() - t0
    secs = time.time() - t0
    try:
        res = json.loads(out)
    except ValueError:
        return None, f"ppa.py exited {proc.returncode} without a result: {(err or out).strip()[-300:]}", secs
    if proc.returncode != 0 or "error" in res:
        first = str(res.get("error", "")).strip().splitlines()
        return None, "the pinned flow failed: " + (first[0] if first else f"exit {proc.returncode}"), secs
    return res, None, secs


def row_of(res, plan, point, cycles):
    """The data columns of one measurement."""
    p, s = res["ppa"], res["score"]
    if s.get("params") != point["params"]:
        raise PlanError(f"ppa.py scored at {s.get('params')}, not at {point['params']}")
    r = {"area_e4um2": p["area_e4um2_sky130"], "area_um2": p["area_um2_sky130"], "cells": p["cells_sky130"],
         "buffers": p["repair"]["buffers"], "unit_depth": p["unit_depth"], "area_mge": s["area_mge"],
         "area_ge": s["area_ge"], "depth": s["depth"], "num_gates": s["num_gates"], "gates": s["gates"],
         "netlist_sha256": p["netlist_sha256"], "repaired_sha256": p["repair"]["netlist_sha256"],
         "rtlil_sha256": s["rtlil_sha256"]}
    if plan["seq"]:
        r.update(period_ps=p["delay_ps_sky130"], ffs=s["ffs"])
        if cycles is not None:
            r.update(cycles=cycles, time_ps=cycles * p["delay_ps_sky130"])
    else:
        r.update(delay_ps=p["delay_ps_sky130"], time_ps=p["delay_ps_sky130"])
    return r


def identity_of(res):
    p, s = res["ppa"], res["score"]
    return ({"ppa_version": p["ppa_version"], "ppa_pins_sha256": p["ppa_pins_sha256"],
             "liberty_sha256": p["liberty_sha256"], "input_drive": p["setup"]["input_drive"]},
            {"yosys_version": s["yosys_version"], "canon_script_sha256": s["canon_script_sha256"],
             "script_sha256": s["script_sha256"], "ge_table_sha256": s["ge_table_sha256"]})


def design_latency(plan, d):
    """(the `def lat` line, its value at each point key) of a clocked design, or (None, {})."""
    if not plan["seq"] or not d.get("lean"):
        return None, {}
    with open(os.path.join(SVGOLF, d["lean"]), encoding="utf-8") as fh:
        text = fh.read()
    line, at = latency_of(text, plan["order"])
    if at is None:
        return None, {}
    vals = {p["key"]: at(p["params"]) for p in plan["points"]}
    n = declared_latency(text)
    if plan["kind"] in LATENCY_KINDS and n is not None and vals.get(plan["scored"]) != n:
        raise PlanError(f"{d['src']}: `{line}` gives {vals.get(plan['scored'])} at the scored point, but its header "
                        f"declares `-- svgolf-latency: {n}`")
    return line, vals


def measure_task(plan, *, retry_skipped=False, log=print, timings=None):
    """Measure every (design, point) of `plan`; returns the task's data (`task_data`). Raises PlanError when the
    scored point fails."""
    cache, rows, ident, flow = {}, {}, None, None
    for d in plan["designs"]:
        line, cycles = design_latency(plan, d)
        d["latency"] = line
        for point in plan["points"]:
            key = point["key"]
            if key not in d["points"]:
                continue
            s = plan["skip"].get((d["id"], key))
            if s and not retry_skipped:
                rows[(d["id"], key)] = ("dropped", s["reason"])
                log(f"  {d['id']} @ {key}: skipped ({s['reason']})")
                continue
            unit = (d["sha256"], key)
            if unit not in cache:
                timeout = None if point["scored"] else plan["limit"]
                res, why, secs = run_ppa(plan, d, point, timeout)
                cache[unit] = (res, why)
                if timings is not None:
                    timings.append({"task": plan["task"], "design": d["id"], "point": key, "seconds": round(secs, 2),
                                    "result": "ok" if res else why})
                log(f"  {d['id']} @ {key}: " + (f"{res['ppa']['area_um2_sky130']} um^2, "
                                                f"{res['ppa']['delay_ps_sky130']} ps" if res else why)
                    + f" ({secs:.1f} s)")
                if res:
                    i, f = identity_of(res)
                    if ident is None:
                        ident, flow = i, f
                    elif (i, f) != (ident, flow):
                        raise PlanError(f"{d['id']} @ {key}: weighed under another identity or flow than the "
                                        f"task's other designs ({i}, {f})")
            res, why = cache[unit]
            if res is None:
                if point["scored"]:
                    raise PlanError(f"{plan['task']}: {d['id']} fails at the scored point {key}: {why}")
                rows[(d["id"], key)] = ("dropped", why)
            else:
                rows[(d["id"], key)] = ("at", row_of(res, plan, point, cycles.get(key)))
    if ident is None:
        raise PlanError(f"{plan['task']}: nothing was measured")
    return task_data(plan, rows, ident, flow)


def task_data(plan, rows, ident, flow):
    designs = []
    for d in plan["designs"]:
        e = {k: d[k] for k in ("id", "kind", "name", "src", "sha256", "banned", "family")}
        if d["kind"] == "baseline":
            e.update(lean=d["lean"], proved=True)      # its proof (checked by tests/run.py, step `baseline-proofs`)
        if d.get("latency"):
            e["latency"] = d["latency"]
        e["at"] = {k: v for (i, k), (what, v) in sorted(rows.items()) if i == d["id"] and what == "at"}
        dropped = {k: v for (i, k), (what, v) in sorted(rows.items()) if i == d["id"] and what == "dropped"}
        if dropped:
            e["dropped"] = dropped
        designs.append(e)
    return {
        "_comment": ("GENERATED by score/points.py measure; do not edit (re-measure instead). The pinned flow of "
                     "score/ppa.py at every point of score/points.json: MEASURED, NOT RANKED except at `scored`, where "
                     "the numbers equal the goldens (score/test_points.py). `at` maps a point to the A0' columns: "
                     "area_e4um2 (1e-4 um^2), delay_ps or, clocked, period_ps x cycles = time_ps, and the GE columns of "
                     "score.py; `dropped` maps a point to why it has no numbers."),
        "schema": SCHEMA, "task": plan["task"], "kind": plan["kind"], "top": plan["top"], "scored": plan["scored"],
        "scale": plan["scale"], "identity": ident, "flow": flow,
        "records": any(d["kind"] == "record" for d in plan["designs"]) or plan.get("records", False),
        "points": [{k: p[k] for k in ("key", "params", "label", "x", "scored")} for p in plan["points"]],
        "designs": designs,
    }


def data_text(data):
    return json.dumps(data, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def data_path(task, out_dir=OUT_DIR):
    return os.path.join(out_dir, f"{task}.json")


# ---------------------------------------------------------------------------
# the check: the committed data against the plan, the current flow and the goldens
# ---------------------------------------------------------------------------

def current_identity(task):
    ident = dict(lb.ppa_identity() or {})
    ident["input_drive"] = lb.ppa_setup_now(task).get("input_drive")
    return ident


def current_flow(seq):
    script, table = FLOW_FILES["seq" if seq else "comb"]
    return {"canon_script_sha256": sha256_file(os.path.join(HERE, "canon.ys")),
            "script_sha256": sha256_file(os.path.join(HERE, script)),
            "ge_table_sha256": sha256_file(os.path.join(HERE, table)),
            "yosys_version": load_json(EXPECTED)["flow"]["yosys_version"]}


def check_task(plan, data):
    """The problems (strings) of one task's data: its plan (points, designs and their files), the current sky130
    identity and flow, every (design, point) measured or dropped (the scored one never), and the goldens."""
    bad = []
    name = plan["task"]
    if data.get("schema") != SCHEMA or data.get("task") != name or data.get("scored") != plan["scored"]:
        return [f"{name}: the data is not this task's (schema, task or scored point differ)"]
    want_points = [{k: p[k] for k in ("key", "params", "label", "x", "scored")} for p in plan["points"]]
    if data["points"] != want_points:
        bad.append(f"{name}: the points differ from points.json's")
    if data.get("scale") != plan["scale"]:
        bad.append(f"{name}: the scale differs from points.json's")
    task = lb.load_task(TASKS, name)
    if data.get("identity") != current_identity(task):
        bad.append(f"{name}: weighed under another sky130 identity or input drive than now: {data.get('identity')}")
    if data.get("flow") != current_flow(plan["seq"]):
        bad.append(f"{name}: weighed under another pinned flow than now: {data.get('flow')}")
    by_id = {d["id"]: d for d in data["designs"]}
    # every reference and baseline exactly; a record only if it is one of the leaderboard's (a record
    # added since the last measurement is not missing: its extra points come with the next one)
    want_ids = [d["id"] for d in plan["designs"] if d["kind"] != "record"]
    got_ids = [d["id"] for d in data["designs"] if d["kind"] != "record"]
    if sorted(want_ids) != sorted(got_ids):
        bad.append(f"{name}: the designs differ from the plan: missing {sorted(set(want_ids) - set(got_ids))}, "
                   f"extra {sorted(set(got_ids) - set(want_ids))}")
    records = {d["id"] for d in plan["designs"] if d["kind"] == "record"}
    for e in data["designs"]:
        if e["kind"] == "record" and e["id"] not in records:
            bad.append(f"{name}: {e['id']} is not a player's record of the leaderboard (now)")
    for d in plan["designs"]:
        e = by_id.get(d["id"])
        if e is None:
            continue
        for k in ("src", "sha256", "kind", "banned", "family") + (("lean",) if d["kind"] == "baseline" else ()):
            if e.get(k) != d[k]:
                bad.append(f"{name}: {d['id']}: {k} is {e.get(k)!r}, the plan's {d[k]!r} (a changed design file: "
                           "measure again)")
        for key in d["points"]:
            here = (key in e.get("at", {})) + (key in e.get("dropped", {}))
            if here != 1:
                bad.append(f"{name}: {d['id']} @ {key}: {'neither measured nor dropped' if not here else 'both'}")
            if key == plan["scored"] and key not in e.get("at", {}):
                bad.append(f"{name}: {d['id']} has no numbers at the scored point {key}")
        if d["kind"] == "baseline" and e.get("proved") is not True:
            bad.append(f"{name}: {d['id']}: not marked proved (`proved`): measure again")
        extra = set(e.get("at", {})) | set(e.get("dropped", {}))
        if extra - set(d["points"]):
            bad.append(f"{name}: {d['id']} has numbers at points it is not measured at: {sorted(extra - set(d['points']))}")
    bad += check_goldens(plan, data)
    return bad


def check_goldens(plan, data):
    """The data against the goldens, bit for bit: expected_ppa.json at the scored point (every designs.json design of
    the task), tests/expected.json's GE columns at every point it scores, its clocked columns at the scored point."""
    bad = []
    name, scored = plan["task"], plan["scored"]
    gold = load_json(EXPECTED_PPA)
    by_src = {}
    for e in data["designs"]:
        by_src.setdefault(e["src"], e)
    for g in load_json(DESIGNS)["designs"]:
        if g["task"] != name:
            continue
        e = by_src.get(g["src"])
        row = (e or {}).get("at", {}).get(point_key(g.get("params") or {}, plan["order"]))
        if row is None:
            bad.append(f"{name}: designs.json's {g['name']} has no numbers at {scored}")
            continue
        want = gold["designs"][g["name"]]
        for k in GOLDEN_KEYS:
            if row.get(GOLDEN_TO_DATA.get(k, k)) != want[k]:
                bad.append(f"{name}: {g['name']} at {scored}: {k} {row.get(GOLDEN_TO_DATA.get(k, k))!r}, "
                           f"the golden (expected_ppa.json) {want[k]!r}")
    exp = load_json(EXPECTED)["tasks"].get(name, {})
    for e in data["designs"]:
        if e["kind"] == "record":
            continue
        scores = ((exp.get(e["kind"] + "s") or {}).get(e["name"]) or {}).get("scores") or {}
        for key, row in sorted(e["at"].items()):
            s = scores.get(key)
            if not s:
                continue
            for k in ("area_mge", "depth", "num_gates", "gates"):
                if row.get(k) != s.get(k):
                    bad.append(f"{name}: {e['id']} at {key}: {k} {row.get(k)!r}, tests/expected.json {s.get(k)!r}")
            if key == scored:
                for k in ("area_um2", "period_ps", "cycles", "time_ps", "ffs"):
                    if k in s and row.get(k) != s[k]:
                        bad.append(f"{name}: {e['id']} at {key}: {k} {row.get(k)!r}, tests/expected.json {s[k]!r}")
    return bad


def check(config, tasks=None, out_dir=OUT_DIR):
    """Every problem of the committed data (strings; [] when it is consistent)."""
    bad = []
    try:
        plans = full_plan(config, tasks)
    except PlanError as e:
        return [str(e)]
    for name, plan in plans.items():
        path = data_path(name, out_dir)
        if not os.path.isfile(path):
            bad.append(f"{name}: no data ({rel(path)}): run `score/points.py measure --task {name}`")
            continue
        data = load_json(path)
        if any(e["kind"] == "record" for e in data["designs"]):
            plan = full_plan(config, [name], records=True)[name]
        bad += check_task(plan, data)
    return bad


# ---------------------------------------------------------------------------
# the command line
# ---------------------------------------------------------------------------

def cmd_plan(args, config):
    plans = full_plan(config, args.task, records=args.records)
    for name, p in plans.items():
        print(f"{name} (scored {p['scored']}, limit {p['limit']} s, scale {p['scale']['param']}):")
        for pt in p["points"]:
            ds = [d["id"] for d in p["designs"] if pt["key"] in d["points"]]
            sk = [d for d in ds if (d, pt["key"]) in p["skip"]]
            print(f"  {pt['key']}{' (scored)' if pt['scored'] else ''}: {len(ds)} designs"
                  + (f", {len(sk)} skipped" if sk else "") + ": " + ", ".join(ds))
    return 0


def cmd_measure(args, config):
    plans = full_plan(config, args.task, records=args.records)
    os.makedirs(args.out, exist_ok=True)
    timings = [] if args.timings else None
    failed = False
    for name, plan in plans.items():
        print(f"{name}:", file=sys.stderr, flush=True)
        plan["records"] = args.records
        try:
            data = measure_task(plan, retry_skipped=args.retry_skipped,
                                log=lambda m: print(m, file=sys.stderr, flush=True), timings=timings)
        except PlanError as e:
            print(f"error: {e}", file=sys.stderr)
            failed = True
            continue
        bad = check_goldens(plan, data)
        if bad:
            print("error: the measurement disagrees with the goldens (nothing written):\n  " + "\n  ".join(bad),
                  file=sys.stderr)
            failed = True
            continue
        with open(data_path(name, args.out), "w", encoding="utf-8") as fh:
            fh.write(data_text(data))
        print(f"  wrote {rel(data_path(name, args.out))}", file=sys.stderr)
    if timings is not None:
        with open(args.timings, "w", encoding="utf-8") as fh:
            json.dump(timings, fh, indent=1)
    return 1 if failed else 0


def cmd_check(args, config):
    bad = check(config, args.task)
    for b in bad:
        print(b)
    print(f"{'FAILED' if bad else 'ok'}: {len(bad)} problem(s)", file=sys.stderr)
    return 1 if bad else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("plan", "measure", "check"):
        p = sub.add_parser(name)
        p.add_argument("--task", action="append", help="only this task (repeatable)")
        p.add_argument("--config", default=CONFIG)
        if name in ("plan", "measure"):
            p.add_argument("--records", action="store_true",
                           help="also the players' leaderboard records (measured, never ranked)")
        if name == "measure":
            p.add_argument("--out", default=OUT_DIR, help="where the data files go (default score/measured/)")
            p.add_argument("--retry-skipped", action="store_true", help="also run the pairs points.json skips")
            p.add_argument("--timings", metavar="OUT.json", help="write the wall time of every run there")
    args = ap.parse_args(argv)
    try:
        config = load_json(args.config)
        return {"plan": cmd_plan, "measure": cmd_measure, "check": cmd_check}[args.cmd](args, config)
    except PlanError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
