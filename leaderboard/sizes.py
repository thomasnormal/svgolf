#!/usr/bin/env python3.12
"""The designs of the boards at other sizes: every record's design file synthesized by the pinned flow at the sizes of
leaderboard/sizes.json, written to leaderboard/sizes/<task>.json. MEASURED, NOT RANKED.

    python3.12 leaderboard/leaderboard.py sizes [--task T ...]                 # check the files offline (no Yosys)
    nice -n 19 python3.12 leaderboard/leaderboard.py sizes --write [--task T ...] [--jobs 1|2] [--size KEY ...]
                                                                [--design PREFIX ...] [--timings OUT.jsonl]

Owner feedback, 2026-11-13: "Even though we fix N for the main rated score, we should still synthesize for more N (or
other parametrics) and make it possible to choose in the graph ... that way we can see which designs scale better."
The ranked board stays at task.json's `scoring.params`; nothing here ranks anything.

THE DESIGNS: every design FILE the task's pages show as a record (`good_records` at the task's scoring point: the
players' records and par's, the reference player's), one entry per file (its sha256), naming the records that hold it.
The references and baselines that are no record are measured at other points by score/points.py (score/measured/).

THE FLOW: each (design, size) is ONE run of `score/ppa.py SV --task tasks/<t> --param K=V ... --no-mapped --netlist
NET` (`--seq` on a clocked task): score.py's two Yosys processes, the A0' weighing, the repair by buffering and the
static timing analysis under the task's input drive, on the pinned liberty: the scoring flow itself, at other
parameters. Then the ASAP7 view's cells-only columns on THAT netlist (`ppa.py --netlist-in NET --pdk asap7`: Python,
no second synthesis; the scored netlist does not depend on the library). The routed course has no data at other
sizes: it is not run here and nothing is estimated for it.

THE CONTROL: at the scoring size every column must equal what the record itself stores (its `ppa` and `score` blocks:
area, delay or period, cycles, time, the product, cells, buffers, unit depth, GE, the netlist, repaired netlist and RTLIL
hashes) and, when the task's ASAP7 table is current, that table's entry. `--write` refuses to keep a design whose
scoring size differs, and the check fails on it: equality there is what shows that this is the scoring flow.

THE CYCLES of a clocked design at a size: its proof's latency function (`def lat` in the record's .lean, evaluated as
score/points.py does, checked against the record's own cycles at the scoring point); 1 on the reactive kind, as
check.py counts it. Time = cycles x the register-to-register period; combinational: the critical-path delay.

LIMITS: every run has `limits.timeout_s` seconds of wall clock and `limits.memory_gb` GiB of memory for its whole
process group (a watchdog: macOS enforces no memory ulimit); a run that reaches either is "not measured" (`limit`)
and is never retried under the same pins. A size the flow refuses (an error of ppa.py, e.g. a netlist the repair
cannot make legal) is "not measured" (`flow`) with the flow's own reason.

RESUMABLE: `--write` keeps every entry of an existing file made under the same pins (flow, sky130 and ASAP7
identities, input drive, limits) for a design file and size of the plan, and runs only the missing ones. Deterministic
file form (sorted keys, one-space indent); the only clock reading in it is each run's `seconds`, which a resumed run
keeps.

Exit status: 0 good (a stale file is a note), 1 a check or a measurement failed, 2 usage or infrastructure.
"""

import argparse
import ast
import concurrent.futures
import ctypes
import ctypes.util
import hashlib
import importlib.util
import json
import os
import platform
import signal
import struct
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
CONFIG = os.path.join(HERE, "sizes.json")
OUT_DIR = os.path.join(HERE, "sizes")
PPA_PY = os.path.join(SVGOLF, "score", "ppa.py")
POINTS_PY = os.path.join(SVGOLF, "score", "points.py")
SCHEMA = "svgolf-sizes/1"
MAX_JOBS = 2
POLL_S = 0.5
GIB = 1 << 30

TOP_KEYS = {"schema", "task", "kind", "top", "scoring_point", "scored", "sizes", "series", "pins", "designs"}
PIN_KEYS = {"flow", "sky130", "asap7", "limits", "ppa_script_sha256"}
STALE_PINS = ("flow", "sky130", "asap7", "limits")          # what makes data comparable (ppa_script_sha256 is recorded)
SIZE_KEYS = {"key", "params", "label", "scored"}
SERIES_KEYS = {"param", "label", "fixed", "keys"}
DESIGN_KEYS = {"sv_sha256", "sv_name", "records", "par", "latency", "at"}
RECORD_KEYS = {"record_hash", "player", "sv_name"}
MEASURED_KEYS = {"status", "area_e4um2", "area_um2", "delay_ps", "cycles", "time_ps", "area_x_time", "cells",
                 "buffers", "unit_depth", "area_mge", "depth", "num_gates", "flops", "netlist_sha256",
                 "repaired_sha256", "rtlil_sha256", "seconds", "asap7"}
ASAP7_KEYS = {"status", "area_e5um2", "area_um2", "delay_ps", "time_ps", "area_x_time", "cells", "buffers",
              "repaired_sha256"}
NOT_MEASURED_KEYS = {"status", "why", "reason", "seconds"}
WHY = ("limit", "flow")
LATENCY_KINDS = ("tx-family", "stream-family")
REACT_KINDS = ("react-family",)
# the scoring-size control: an entry's column -> where the record keeps it
CONTROL = (("area_e4um2", ("ppa", "area_e4um2_sky130")), ("delay_ps", ("ppa", "delay_ps_sky130")),
           ("cells", ("ppa", "cells_sky130")), ("buffers", ("ppa", "repair", "buffers")),
           ("unit_depth", ("ppa", "unit_depth")), ("netlist_sha256", ("ppa", "netlist_sha256")),
           ("repaired_sha256", ("ppa", "repair", "netlist_sha256")), ("area_mge", ("score", "area_mge")),
           ("depth", ("score", "depth")), ("num_gates", ("score", "num_gates")),
           ("rtlil_sha256", ("score", "rtlil_sha256")))
CONTROL_CLOCKED = (("cycles", ("score", "cycles")), ("time_ps", ("score", "time_ps")), ("flops", ("score", "ffs")),
                   ("delay_ps", ("score", "period_ps")))
CONTROL_ASAP7 = (("area_e5um2", "area_e5um2"), ("delay_ps", "delay_ps"), ("time_ps", "time_ps"),
                 ("cells", "cells"), ("buffers", "buffers"), ("repaired_sha256", "repaired_sha256"))

COMMENT = ("GENERATED by `leaderboard.py sizes --write`; do not edit (measure again instead). MEASURED, NOT RANKED: "
           "every record's design file of the task synthesized by the pinned scoring flow (score/ppa.py, sky130 flow "
           "A0') at the sizes of leaderboard/sizes.json; the board ranks the scoring size (`scored`) alone, where every "
           "column equals the record's own (checked). `at` maps a size key to the sky130 columns: area_e4um2 (1e-4 um^2), "
           "area_um2, delay_ps (the critical-path delay; on a clocked task the register-to-register period), cycles "
           "(clocked: the design's proved latency at that size; null on a combinational task), time_ps (delay, or "
           "cycles x period), area_x_time (area_e4um2 x time_ps, 1e-4 um^2 x ps), the GE columns, the cell count, the "
           "netlist hashes and the run's wall-clock seconds; `asap7` the ASAP7 view's cells-only columns on the same "
           "netlist (area_e5um2 in 1e-5 um^2). A size that was not measured says why (`limit`: the run's time or memory "
           "limit, `pins.limits`; `flow`: the flow refused it). The routed course is not measured at other sizes. See "
           "leaderboard/README.md, \"Other sizes\".")


class PlanError(Exception):
    pass


# ---------------------------------------------------------------------------------------------------------------------
# the leaderboard module and score/points.py (loaded lazily, by path)
# ---------------------------------------------------------------------------------------------------------------------

LB = None
_POINTS = None


def lb():
    """leaderboard/leaderboard.py: the module that runs `sizes` (it sets LB), else loaded by path."""
    global LB
    if LB is None:
        spec = importlib.util.spec_from_file_location("svgolf_leaderboard_sizes", os.path.join(HERE, "leaderboard.py"))
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        LB = mod
    return LB


def points():
    """score/points.py, for its reading of a proof's latency function (`latency_of`, `declared_latency`)."""
    global _POINTS
    if _POINTS is None:
        spec = importlib.util.spec_from_file_location("svgolf_points_sizes", POINTS_PY)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _POINTS = mod
    return _POINTS


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load_json(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def data_text(data):
    """The one file form: sorted keys, one-space indent, a final newline (as leaderboard/asap7/)."""
    return json.dumps(data, indent=1, sort_keys=True) + "\n"


def data_path(task_name, out_dir=OUT_DIR):
    return os.path.join(out_dir, f"{task_name}.json")


def _isnat(v, least=0):
    return isinstance(v, int) and not isinstance(v, bool) and v >= least


def _issha(v):
    return isinstance(v, str) and len(v) == 64 and all(c in "0123456789abcdef" for c in v)


def _get(d, path):
    for k in path:
        if not isinstance(d, dict):
            return None
        d = d.get(k)
    return d


# ---------------------------------------------------------------------------------------------------------------------
# sizes: the configuration, the task's range
# ---------------------------------------------------------------------------------------------------------------------

def param_order(task):
    """The task's parameter names in task.json's order (`scoring.params`, as tests/expected.json keys a point)."""
    return list((task.get("scoring") or {}).get("params") or {})


def size_key(params, order):
    """'N=16', 'W=5,P=11', 'N=4,W=8,AccW=32' (score/points.py's and tests/expected.json's keys)."""
    return ",".join(f"{k}={int(params[k])}" for k in order) or "default"


_RANGE_NODES = (ast.Expression, ast.Tuple, ast.Compare, ast.BinOp, ast.Name, ast.Constant, ast.Load,
                ast.Lt, ast.LtE, ast.Gt, ast.GtE, ast.Eq, ast.NotEq, ast.Add, ast.Sub, ast.Mult, ast.Pow, ast.FloorDiv)


def _eval_range(node, env):
    if isinstance(node, ast.Expression):
        return _eval_range(node.body, env)
    if isinstance(node, ast.Tuple):
        return all(_eval_range(e, env) for e in node.elts)
    if isinstance(node, ast.Compare):
        vals = [_eval_range(node.left, env)] + [_eval_range(c, env) for c in node.comparators]
        ops = {ast.Lt: int.__lt__, ast.LtE: int.__le__, ast.Gt: int.__gt__, ast.GtE: int.__ge__, ast.Eq: int.__eq__,
               ast.NotEq: int.__ne__}
        return all(ops[type(op)](a, b) for op, a, b in zip(node.ops, vals, vals[1:]))
    if isinstance(node, ast.BinOp):
        a, b = _eval_range(node.left, env), _eval_range(node.right, env)
        op = type(node.op)
        if op is ast.Add:
            return a + b
        if op is ast.Sub:
            return a - b
        if op is ast.Mult:
            return a * b
        if op is ast.Pow and 0 <= b <= 256:
            return a ** b
        if op is ast.FloorDiv and b:
            return a // b
        raise PlanError(f"a range computes {op.__name__} on {a}, {b}, which this reading does not take")
    if isinstance(node, ast.Name):
        if node.id not in env:
            raise PlanError(f"the range names {node.id}, which is not a parameter")
        return env[node.id]
    if isinstance(node, ast.Constant) and _isnat(node.value):
        return node.value
    raise PlanError(f"a range uses {type(node).__name__}, which this reading does not take")


def range_problems(task, params):
    """The task.json `parameters` ranges that `params` violates (strings; [] inside the range). A range string is read
    by Python's own parser (`ast`, mode "eval", `^` as power), and only integers, the parameters, + - * // ^ and
    comparisons are taken: anything else is a PlanError, never a guess."""
    out = []
    for p in task.get("parameters") or []:
        text = p.get("range")
        if not isinstance(text, str):
            raise PlanError(f"{task['name']}: parameter {p.get('name')} has no range")
        try:
            tree = ast.parse(text.replace("^", "**"), mode="eval")
        except SyntaxError as e:
            raise PlanError(f"{task['name']}: the range {text!r} cannot be read: {e}")
        if not all(isinstance(n, _RANGE_NODES) for n in ast.walk(tree)):
            raise PlanError(f"{task['name']}: the range {text!r} uses something other than integers, the parameters, "
                            "+ - * // ^ and comparisons")
        if _eval_range(tree, params) is not True:
            out.append(text)
    return out


def task_sizes(task, tcfg):
    """(sizes, series, scored key) of `task` from its sizes.json entry. Each size {key, params (task.json's order), label,
    scored}, ordered by the first series' parameter, then the parameters in task.json's order; each series {param,
    label, fixed, keys (ascending in `param`)}. PlanError for a configuration that is not
    well formed: a size outside the task's range, the scoring point not among the sizes, a series that names no
    parameter or whose `fixed` names another, a size on no series."""
    name = task["name"]
    order = param_order(task)
    if not order:
        raise PlanError(f"{name}: the task has no parameter, so it has no other size (sizes.json `left_out`)")
    scored = size_key(task["scoring"]["params"], order)
    sizes, labels = [], set()
    for s in tcfg.get("sizes") or []:
        params = s.get("params") if isinstance(s, dict) else None
        if not isinstance(params, dict) or set(params) != set(order) or not all(_isnat(v, 1) for v in params.values()):
            raise PlanError(f"{name}: size {s!r}: `params` must give every parameter {order} a positive integer")
        params = {k: int(params[k]) for k in order}
        bad = range_problems(task, params)
        if bad:
            raise PlanError(f"{name}: size {size_key(params, order)} is outside the task's range ({'; '.join(bad)}): "
                            "the proofs do not cover it")
        key = size_key(params, order)
        label = s.get("label")
        if label is not None and not (isinstance(label, str) and label.strip()):
            raise PlanError(f"{name}: size {key}: `label` must be a non-empty string")
        text = label or key
        if key in [x["key"] for x in sizes] or text in labels:
            raise PlanError(f"{name}: size {key} twice (or its label twice)")
        labels.add(text)
        sizes.append({"key": key, "params": params, "label": label, "scored": key == scored})
    if scored not in [x["key"] for x in sizes]:
        raise PlanError(f"{name}: the scoring point {scored} (task.json scoring.params) is not one of the sizes")
    series, on = [], set()
    for r in tcfg.get("series") or []:
        param, fixed = (r or {}).get("param"), (r or {}).get("fixed")
        if param not in order or not isinstance(fixed, dict) or param in fixed or not set(fixed) <= set(order) \
                or not isinstance(r.get("label"), str):
            raise PlanError(f"{name}: series {r!r}: needs `param` (a parameter), `label` and `fixed` (the others it holds)")
        mine = sorted((x for x in sizes if all(x["params"][k] == v for k, v in fixed.items())),
                      key=lambda x: x["params"][param])
        xs = [x["params"][param] for x in mine]
        if len(set(xs)) != len(xs) or scored not in [x["key"] for x in mine] or len(mine) < 2:
            raise PlanError(f"{name}: series along {param}: its sizes must differ in {param}, be at least two and "
                            "include the scoring point")
        on |= {x["key"] for x in mine}
        series.append({"param": param, "label": r["label"], "fixed": {k: int(fixed[k]) for k in order if k in fixed},
                       "keys": [x["key"] for x in mine]})
    if not series or on != {x["key"] for x in sizes}:
        raise PlanError(f"{name}: every size must lie on a series (off every series: "
                        f"{sorted({x['key'] for x in sizes} - on)})")
    first = series[0]["param"]                      # the selector's order: along the first series' parameter
    sizes.sort(key=lambda x: (x["params"][first],) + tuple(x["params"][k] for k in order))
    return sizes, series, scored


def config_problems(config, tasks):
    """What is wrong with leaderboard/sizes.json against the tasks (`tasks`: name -> task.json), as strings."""
    bad = []
    lim = config.get("limits")
    if not (isinstance(lim, dict) and set(lim) == {"timeout_s", "memory_gb"} and _isnat(lim["timeout_s"], 1)
            and _isnat(lim["memory_gb"], 1)):
        bad.append("`limits` must be {timeout_s, memory_gb}, positive integers")
    cfg, left = config.get("tasks") or {}, config.get("left_out") or {}
    for name in sorted(set(cfg) & set(left)):
        bad.append(f"{name}: both measured and left out")
    for name in sorted(set(tasks) - set(cfg) - set(left)):
        bad.append(f"{name}: neither measured at other sizes nor left out with a reason (sizes.json)")
    for name in sorted((set(cfg) | set(left)) - set(tasks)):
        bad.append(f"{name}: not a task")
    for name in sorted(set(cfg) & set(tasks)):
        try:
            task_sizes(tasks[name], cfg[name])
        except PlanError as e:
            bad.append(str(e))
        if not isinstance(cfg[name].get("why"), str) or not cfg[name]["why"].strip():
            bad.append(f"{name}: no `why` (the reason for its sizes)")
    for name, why in sorted(left.items()):
        if not (isinstance(why, str) and why.strip()):
            bad.append(f"{name}: left out without a reason")
    return bad


def limits_of(config):
    lim = config["limits"]
    return {"timeout_s": int(lim["timeout_s"]), "memory_gb": int(lim["memory_gb"])}


# ---------------------------------------------------------------------------------------------------------------------
# the designs: the records' design files, their latency
# ---------------------------------------------------------------------------------------------------------------------

def plan_designs(task, records, par_shas, lean_text=None, data_dir=None):
    """The design files of `task` that its pages show as records, by sha256: {sv_sha256: {sv_sha256, sv_name, records
    [{record_hash, player, sv_name}] (by hash), records_full (the records themselves), par (the file is par's design,
    leaderboard/par.json), latency (the `def lat` line, clocked tx/stream kinds; else None), lat (size params -> its
    value, or None), src (the first record's .sv path)}}. `records`: the intact records (`good_records`); those of other
    tasks or at another scoring point are not shown and are left out. `lean_text(rec)`: a record's proof text
    (default: its stored .lean). PlanError for two records of one file that disagree on the latency function."""
    L = lb()
    name, point = task["name"], L.scoring_point(task)
    order = param_order(task)
    kind = task.get("kind")
    data_dir = data_dir or L.DEFAULT_DATA
    out = {}
    for rec in sorted(records, key=lambda r: r["record_hash"]):
        if rec.get("task") != name or (rec.get("score") or {}).get("scoring_point") != point:
            continue
        sha = rec["files"]["sv"]["sha256"]
        d = out.setdefault(sha, {"sv_sha256": sha, "sv_name": rec["files"]["sv"]["name"], "records": [],
                                 "records_full": [], "par": sha in par_shas, "latency": None, "lat": None,
                                 "src": L.record_paths(data_dir, name, rec["record_hash"])[1]})
        d["records"].append({"record_hash": rec["record_hash"], "player": rec["player"],
                             "sv_name": rec["files"]["sv"]["name"]})
        d["records_full"].append(rec)
        if kind in LATENCY_KINDS:
            text = lean_text(rec) if lean_text else _read(L.record_paths(data_dir, name, rec["record_hash"])[2])
            line, at = points().latency_of(text, order)
            if line is None:
                raise PlanError(f"{name}: record {rec['record_hash'][:12]}: its proof has no `def lat` this reading "
                                "evaluates, so its cycles at other sizes are unknown")
            if d["latency"] is not None and d["latency"] != line:
                raise PlanError(f"{name}: the records of {sha[:12]} name two latency functions: {d['latency']!r} and "
                                f"{line!r}")
            d["latency"], d["lat"] = line, at
    return out


def _read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def cycles_at(task, design, params):
    """The cycles of `design` at `params`: its latency function (tx/stream kinds), 1 (the reactive kind: one decision
    per cycle, as check.py counts it), None (a combinational task)."""
    kind = task.get("kind")
    if kind in LATENCY_KINDS:
        n = design["lat"](params)
        if n is None:                   # never a crash, never a guess: the task fails loudly
            raise PlanError(f"{task['name']}: {design['sv_sha256'][:12]}: its latency function {design['latency']!r} "
                            f"does not evaluate at {params} (score/points.py `eval_nat`), so its cycles there are "
                            "unknown")
        return n
    if kind in REACT_KINDS or kind in lb().CLOCKED_KINDS:
        return 1
    return None


# ---------------------------------------------------------------------------------------------------------------------
# the pins: what makes the data comparable with a measurement made now
# ---------------------------------------------------------------------------------------------------------------------

def pins_now(task, limits):
    """The pins of a measurement of `task` made now (no Yosys run beyond `yosys -V`): the pinned flow of its kind, the
    sky130 identity with the task's input drive, the ASAP7 view's identity, the limits, ppa.py's sha256."""
    L = lb()
    sky = dict(L.ppa_identity() or {})
    sky["input_drive"] = L.ppa_setup_now(task).get("input_drive")
    return {"flow": L.current_flow(SVGOLF, L.task_flow(task)), "sky130": sky, "asap7": L.asap7_identity(),
            "limits": dict(limits), "ppa_script_sha256": sha256_file(PPA_PY)}


def stale_keys(old, now):
    """The pins (STALE_PINS) in which `old` differs from `now`; a flow key `now` leaves None (Yosys not runnable here) is
    not compared."""
    out = []
    for k in STALE_PINS:
        a, b = (old or {}).get(k), (now or {}).get(k)
        if k == "flow" and isinstance(a, dict) and isinstance(b, dict):
            if any(v is not None and a.get(kk) != v for kk, v in b.items()) or set(a) != set(b):
                out.append(k)
        elif a != b:
            out.append(k)
    return out


# ---------------------------------------------------------------------------------------------------------------------
# one run, under the limits
# ---------------------------------------------------------------------------------------------------------------------

_LIBPROC = None


def _footprint(pid):
    """The memory of one process in bytes: macOS's physical footprint (resident plus compressed: what a swap-full
    machine pays for; `ps` RSS hides the compressed part), Linux's VmRSS + VmSwap; 0 when it cannot be read."""
    global _LIBPROC
    try:
        if platform.system() == "Darwin":
            if _LIBPROC is None:
                _LIBPROC = ctypes.CDLL(ctypes.util.find_library("proc") or "/usr/lib/libproc.dylib")
            buf = ctypes.create_string_buffer(256)           # struct rusage_info_v0 (96 bytes)
            if _LIBPROC.proc_pid_rusage(int(pid), 0, buf) != 0:
                return 0
            return struct.unpack_from("<Q", buf.raw, 72)[0]  # ri_phys_footprint
        total = 0
        with open(f"/proc/{int(pid)}/status") as fh:
            for line in fh:
                if line.startswith(("VmRSS:", "VmSwap:")):
                    total += int(line.split()[1]) * 1024
        return total
    except (OSError, ValueError, AttributeError):
        return 0


def _tree(root):
    """The PIDs of `root` and of every process descending from it (by parent PID, transitively), and of every process
    still in its process group. Yosys runs in a session of its own (score.py runs it through check/sandbox, which
    starts each tool with start_new_session), so the process group alone would miss it."""
    try:
        out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,pgid="], capture_output=True, text=True, timeout=30).stdout
    except (OSError, subprocess.SubprocessError):
        return {root}
    kids, group = {}, set()
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and all(x.isdigit() for x in parts):
            pid, ppid, pgid = map(int, parts)
            kids.setdefault(ppid, []).append(pid)
            if pgid == root:
                group.add(pid)
    seen, todo = {root} | group, [root] + sorted(group)
    while todo:
        for c in kids.get(todo.pop(), []):
            if c not in seen:
                seen.add(c)
                todo.append(c)
    return seen


def _signal_all(pids, sig):
    for pid in sorted(pids):
        try:
            os.kill(pid, sig)
        except (ProcessLookupError, PermissionError):
            pass


def run_limited(cmd, timeout_s, memory_bytes, env=None):
    """Run `cmd` in a new process group of its own, its output to files (no pipe can fill). Every POLL_S seconds the
    memory of its process tree (`_tree`: it and its descendants) is summed (`_footprint`); when the sum passes
    `memory_bytes` or the run passes `timeout_s`, the tree is stopped (SIGSTOP, so nothing new is started), listed again
    and killed (SIGKILL to exactly those PIDs: this call's own processes). Returns {rc, out, err, seconds, limit (None,
    "time" or "memory"), peak_bytes}."""
    with tempfile.TemporaryFile() as fo, tempfile.TemporaryFile() as fe:
        t0 = time.monotonic()
        proc = subprocess.Popen(cmd, stdout=fo, stderr=fe, start_new_session=True, env=env)
        limit, peak = None, 0
        while True:
            try:
                proc.wait(timeout=POLL_S)
                break
            except subprocess.TimeoutExpired:
                pass
            mem = sum(_footprint(p) for p in _tree(proc.pid))
            peak = max(peak, mem)
            if mem > memory_bytes:
                limit = "memory"
            elif time.monotonic() - t0 > timeout_s:
                limit = "time"
            if limit:
                tree = _tree(proc.pid)
                _signal_all(tree, signal.SIGSTOP)
                tree |= _tree(proc.pid)
                _signal_all(tree, signal.SIGKILL)
                proc.wait()
                break
        secs = time.monotonic() - t0
        fo.seek(0)
        fe.seek(0)
        return {"rc": proc.returncode, "out": fo.read().decode("utf-8", "replace"),
                "err": fe.read().decode("utf-8", "replace"), "seconds": secs, "limit": limit, "peak_bytes": peak}


def _limit_reason(r, limits):
    if r["limit"] == "time":
        return f"the pinned flow did not finish within the limit of {limits['timeout_s']} s"
    return (f"the pinned flow's processes passed the memory limit of {limits['memory_gb']} GiB "
            f"(after {r['seconds']:.0f} s)")


def _flow_reason(r):
    try:
        res = json.loads(r["out"])
    except ValueError:
        res = {}
    first = str(res.get("error") or "").strip().splitlines() or (r["err"] or "").strip().splitlines()[-1:]
    return "the pinned flow refused it: " + (" ".join(first[0].split())[:300] if first else f"exit {r['rc']}")


def measure_one(task, design, size, cycles, pins, limits, env=None, log=None):
    """One design at one size: the sky130 run (the scoring flow at `size`), then the ASAP7 view's columns on its scored
    netlist. Returns the size's entry (`status` "measured" or "not measured"). PlanError when a run weighed under
    other pins than `pins` or at another point (infrastructure, never data)."""
    L = lb()
    clocked = L.is_clocked_task(task)
    mem = limits["memory_gb"] * GIB
    task_dir = os.path.join(SVGOLF, "tasks", task["name"])
    py = L.checker_python()
    env = dict(env or os.environ, PYTHONDONTWRITEBYTECODE="1")
    with tempfile.TemporaryDirectory(prefix="svgolf-sizes-") as work:
        net = os.path.join(work, "netlist.v")
        cmd = [py, PPA_PY, design["src"], "--task", task_dir, "--no-mapped", "--netlist", net] \
            + [a for k, v in size["params"].items() for a in ("--param", f"{k}={v}")] + (["--seq"] if clocked else [])
        r = run_limited(cmd, limits["timeout_s"], mem, env=env)
        secs = round(r["seconds"], 1)
        if log:
            log(r)
        if r["limit"]:
            return {"status": "not measured", "why": "limit", "reason": _limit_reason(r, limits), "seconds": secs}
        try:
            res = json.loads(r["out"])
        except ValueError:
            res = None
        if r["rc"] != 0 or not isinstance(res, dict) or "error" in res or "ppa" not in res:
            if r["rc"] == 1 and isinstance(res, dict) and "error" in res:
                return {"status": "not measured", "why": "flow", "reason": _flow_reason(r), "seconds": secs}
            raise PlanError(f"ppa.py ended without a result (exit {r['rc']}): {(r['err'] or r['out'])[-400:]}")
        p, s = res["ppa"], res["score"]
        if s.get("params") != size["params"]:
            raise PlanError(f"ppa.py scored at {s.get('params')}, not at {size['params']}")
        got_sky = {"ppa_version": p.get("ppa_version"), "ppa_pins_sha256": p.get("ppa_pins_sha256"),
                   "liberty_sha256": p.get("liberty_sha256"), "input_drive": (p.get("setup") or {}).get("input_drive")}
        if got_sky != pins["sky130"]:
            raise PlanError(f"weighed under another sky130 identity than now: {got_sky}")
        got_flow = {"yosys": s.get("yosys_version"), "canon_script_sha256": s.get("canon_script_sha256"),
                    "script_sha256": s.get("script_sha256"), "ge_table_sha256": s.get("ge_table_sha256")}
        diff = [k for k, v in got_flow.items() if pins["flow"].get(k) is not None and pins["flow"][k] != v]
        if diff:
            raise PlanError(f"run under another flow than now ({', '.join(diff)} differ)")
        if clocked != bool(p.get("sequential")):
            raise PlanError("the weighing's `sequential` does not match the task's kind")
        delay = p["delay_ps_sky130"]
        t = delay * cycles if clocked else delay
        row = {"status": "measured", "area_e4um2": p["area_e4um2_sky130"], "area_um2": p["area_um2_sky130"],
               "delay_ps": delay, "cycles": cycles if clocked else None, "time_ps": t,
               "area_x_time": L.combined.exact(p["area_e4um2_sky130"], t), "cells": p["cells_sky130"],
               "buffers": p["repair"]["buffers"], "unit_depth": p["unit_depth"], "area_mge": s["area_mge"],
               "depth": s["depth"], "num_gates": s["num_gates"], "flops": s.get("ffs") if clocked else None,
               "netlist_sha256": p["netlist_sha256"], "repaired_sha256": p["repair"]["netlist_sha256"],
               "rtlil_sha256": s["rtlil_sha256"], "seconds": secs}
        if sha256_file(net) != p["netlist_sha256"]:
            raise PlanError("the netlist ppa.py wrote is not the one it weighed")
        # the ASAP7 view's cells-only columns, on the very netlist (Python only: no second synthesis)
        r7 = run_limited([py, PPA_PY, "--netlist-in", net, "--task", task_dir, "--pdk", "asap7"],
                         limits["timeout_s"], mem, env=env)
        if r7["limit"]:
            row["asap7"] = {"status": "not measured", "why": "limit", "reason": _limit_reason(r7, limits)}
            return row
        try:
            res7 = json.loads(r7["out"])
        except ValueError:
            res7 = None
        if not isinstance(res7, dict) or r7["rc"] != 0 or "ppa" not in res7:
            if r7["rc"] == 1 and isinstance(res7, dict) and "error" in res7:
                row["asap7"] = {"status": "not measured", "why": "flow", "reason": _flow_reason(r7)}
                return row
            raise PlanError(f"ppa.py --pdk asap7 ended without a result (exit {r7['rc']}): {r7['err'][-400:]}")
        q = res7["ppa"]
        got7 = {"ppa_version": q.get("ppa_version"), "ppa_pins_sha256": q.get("ppa_pins_sha256"),
                "liberty_sha256": q.get("liberty_sha256"), "input_drive": (q.get("setup") or {}).get("input_drive")}
        if got7 != pins["asap7"] or q.get("pdk") != "asap7":
            raise PlanError(f"weighed under another ASAP7 identity than now: {got7}")
        if q.get("netlist_sha256") != p["netlist_sha256"]:
            raise PlanError("the ASAP7 weighing read another netlist than the sky130 one")
        d7 = q["delay_ps_asap7"]
        t7 = d7 * cycles if clocked else d7
        row["asap7"] = {"status": "measured", "area_e5um2": q["area_e5um2_asap7"], "area_um2": q["area_um2_asap7"],
                        "delay_ps": d7, "time_ps": t7, "area_x_time": L.combined.exact(q["area_e5um2_asap7"], t7),
                        "cells": q["cells_asap7"], "buffers": (q.get("repair") or {}).get("buffers"),
                        "repaired_sha256": (q.get("repair") or {}).get("netlist_sha256")}
        return row


# ---------------------------------------------------------------------------------------------------------------------
# the check (pure): a file against the plan, the records, the pins and the ASAP7 table
# ---------------------------------------------------------------------------------------------------------------------

def design_entry_head(d):
    """The part of a design's entry that the plan fixes (everything but `at`)."""
    return {"sv_sha256": d["sv_sha256"], "sv_name": d["sv_name"], "records": d["records"], "par": d["par"],
            "latency": d["latency"]}


def control_problems(task, entry, records, a7entry=None):
    """Where the scoring size's `entry` of a design differs from what its records store (CONTROL, CONTROL_CLOCKED, the
    product `combined.of_record`) and, with `a7entry` (its bound entry of the task's current ASAP7 table), from that
    entry (CONTROL_ASAP7). [] when every column is equal."""
    L = lb()
    out = []
    if entry.get("status") != "measured":
        return ["not measured at the scoring size"]
    clocked = L.is_clocked_task(task)
    for rec in records:
        h = rec["record_hash"][:12]
        for col, path in CONTROL + (CONTROL_CLOCKED if clocked else ()):
            want = _get(rec, path)
            if entry.get(col) != want:
                out.append(f"{col} {entry.get(col)!r}, record {h}'s {'.'.join(path)} {want!r}")
        if not clocked and entry.get("time_ps") != _get(rec, ("ppa", "delay_ps_sky130")):
            out.append(f"time_ps {entry.get('time_ps')!r}, record {h}'s delay {_get(rec, ('ppa', 'delay_ps_sky130'))!r}")
        want = L.combined.of_record(rec)
        if entry.get("area_x_time") != want:
            out.append(f"area_x_time {entry.get('area_x_time')!r}, record {h}'s product {want!r}")
    if a7entry is not None:
        a7 = entry.get("asap7") or {}
        if a7.get("status") != "measured":
            out.append("ASAP7: not measured at the scoring size, where the ASAP7 view has it")
        else:
            for col, key in CONTROL_ASAP7:
                if a7.get(col) != a7entry.get(key):
                    out.append(f"ASAP7 {col} {a7.get(col)!r}, the ASAP7 view's {a7entry.get(key)!r}")
            if entry.get("netlist_sha256") != a7entry.get("netlist_sha256"):
                out.append("the ASAP7 view's entry weighs another netlist")
    return out


def _measured_problems(where, e, clocked, cycles):
    p = []
    if set(e) != MEASURED_KEYS:
        return [f"{where}: keys must be exactly {', '.join(sorted(MEASURED_KEYS))}"]
    for k in ("area_e4um2", "delay_ps", "time_ps", "area_x_time", "cells", "buffers", "unit_depth", "area_mge", "depth",
              "num_gates"):
        if not _isnat(e[k]):
            p.append(f"{where}: {k} is not a non-negative integer")
    for k in ("netlist_sha256", "repaired_sha256", "rtlil_sha256"):
        if not _issha(e[k]):
            p.append(f"{where}: {k} is not a sha256")
    if not (isinstance(e["seconds"], (int, float)) and not isinstance(e["seconds"], bool) and e["seconds"] >= 0):
        p.append(f"{where}: seconds is not a non-negative number")
    if p:
        return p
    if not isinstance(e["area_um2"], (int, float)) or round(e["area_um2"] * 10_000) != e["area_e4um2"]:
        p.append(f"{where}: area_um2 {e['area_um2']!r} is not area_e4um2 / 10^4")
    if clocked:
        if not _isnat(e["cycles"], 1) or not _isnat(e["flops"]):
            p.append(f"{where}: a clocked size has positive integer cycles and integer flops")
        elif e["cycles"] != cycles:
            p.append(f"{where}: cycles {e['cycles']}, the design's latency at this size is {cycles}")
        elif e["time_ps"] != e["cycles"] * e["delay_ps"]:
            p.append(f"{where}: time_ps {e['time_ps']} is not cycles x period ({e['cycles'] * e['delay_ps']})")
    else:
        if e["cycles"] is not None or e["flops"] is not None:
            p.append(f"{where}: a combinational size has cycles and flops null")
        if e["time_ps"] != e["delay_ps"]:
            p.append(f"{where}: time_ps {e['time_ps']} is not the delay {e['delay_ps']}")
    if e["area_x_time"] != e["area_e4um2"] * e["time_ps"]:
        p.append(f"{where}: area_x_time is not area_e4um2 x time_ps")
    a = e["asap7"]
    if not isinstance(a, dict):
        p.append(f"{where}: asap7 is not an object")
    elif a.get("status") == "not measured":
        if set(a) != {"status", "why", "reason"} or a["why"] not in WHY or not (isinstance(a["reason"], str)
                                                                               and a["reason"].strip()):
            p.append(f"{where}: asap7: a not-measured block is exactly {{status, why ({'|'.join(WHY)}), reason}}")
    elif set(a) != ASAP7_KEYS or a.get("status") != "measured":
        p.append(f"{where}: asap7: keys must be exactly {', '.join(sorted(ASAP7_KEYS))}")
    else:
        if not all(_isnat(a[k]) for k in ("area_e5um2", "delay_ps", "time_ps", "area_x_time", "cells", "buffers")) \
                or not _issha(a["repaired_sha256"]):
            p.append(f"{where}: asap7: a column is not a non-negative integer or a sha256")
        else:
            if not isinstance(a["area_um2"], (int, float)) or round(a["area_um2"] * 100_000) != a["area_e5um2"]:
                p.append(f"{where}: asap7: area_um2 is not area_e5um2 / 10^5")
            want = a["delay_ps"] * (e["cycles"] if clocked and _isnat(e["cycles"], 1) else 1)
            if a["time_ps"] != want:
                p.append(f"{where}: asap7: time_ps {a['time_ps']} is not {'cycles x period' if clocked else 'the delay'}"
                         f" ({want})")
            if a["area_x_time"] != a["area_e5um2"] * a["time_ps"]:
                p.append(f"{where}: asap7: area_x_time is not area_e5um2 x time_ps")
    return p


def check_data(data, task, sizes, series, scored, designs, now, *, a7_table=None, a7_identity=None, text=None):
    """Check one task's sizes file. `sizes`, `series`, `scored`: `task_sizes`; `designs`: `plan_designs`; `now`:
    `pins_now`; `a7_table`: the task's ASAP7 view table (`read_asap7`) or None; `text`: the file's bytes as text, for
    the form. Returns (fails, notes): a FAIL is a
    malformed file, a size, series or design that differs from the plan, a column whose arithmetic is wrong, a
    scoring size that is missing or differs from the records (the control); a NOTE is staleness (pins that differ from
    now: the data is then not comparable, and the control is not run)."""
    L = lb()
    fails, notes = [], []
    name = task["name"]
    if not isinstance(data, dict):
        return [f"{name}: not a JSON object"], notes
    keys = {k for k in data if not k.startswith("_")}
    if keys != TOP_KEYS:
        return [f"{name}: top-level keys {sorted(keys ^ TOP_KEYS)} unexpected or missing"], notes
    if text is not None and text != data_text(data):
        fails.append(f"{name}: not in the deterministic form (sorted keys, one-space indent, final newline)")
    if data["schema"] != SCHEMA or data["task"] != name:
        fails.append(f"{name}: schema {data['schema']!r} or task {data['task']!r} is not {SCHEMA!r}, {name!r}")
    if data["kind"] != task.get("kind") or data["top"] != task.get("top"):
        fails.append(f"{name}: kind or top differ from task.json's")
    if data["scoring_point"] != L.scoring_point(task) or data["scored"] != scored:
        fails.append(f"{name}: the scoring point differs from task.json's")
    if data["sizes"] != sizes:
        fails.append(f"{name}: the sizes differ from leaderboard/sizes.json's (measure again)")
    if data["series"] != series:
        fails.append(f"{name}: the series differ from leaderboard/sizes.json's")
    pins = data["pins"]
    if not isinstance(pins, dict) or set(pins) != PIN_KEYS:
        fails.append(f"{name}: pins must be exactly {', '.join(sorted(PIN_KEYS))}")
        pins = {}
    stale = stale_keys(pins, now)
    if stale:
        notes.append(f"{name}: measured under other pins than now ({', '.join(stale)} differ): not comparable, measure "
                     "again with `sizes --write`")
    entries = data["designs"]
    if not isinstance(entries, list) or not all(isinstance(e, dict) for e in entries):
        return fails + [f"{name}: designs is not a list of objects"], notes
    shas = [e.get("sv_sha256") for e in entries]
    if shas != sorted(s for s in shas if isinstance(s, str)) or len(set(shas)) != len(shas):
        fails.append(f"{name}: designs are not in sv_sha256 order, or one is there twice")
    by = {e.get("sv_sha256"): e for e in entries}
    for sha in sorted(set(designs) - set(by)):
        fails.append(f"{name}: no sizes for the design {sha[:12]} of " +
                     ", ".join(r["record_hash"][:12] for r in designs[sha]["records"]) + " (run `sizes --write`)")
    for sha in sorted(s for s in set(by) - set(designs) if isinstance(s, str)):
        fails.append(f"{name}: sizes of {sha[:12]}, which is no record's design file now")
    a7_stale = a7_table is None or L.asap7_table_mismatch(a7_table, task, identity=a7_identity, flow=now.get("flow"))
    clocked = L.is_clocked_task(task)
    keys = [s["key"] for s in sizes]
    params = {s["key"]: s["params"] for s in sizes}
    for sha in sorted(set(designs) & set(by)):
        d, e = designs[sha], by[sha]
        who = f"{name}: {sha[:12]}"
        if set(e) != DESIGN_KEYS:
            fails.append(f"{who}: keys must be exactly {', '.join(sorted(DESIGN_KEYS))}")
            continue
        head = {k: e[k] for k in DESIGN_KEYS - {"at"}}
        if head != design_entry_head(d):
            diff = sorted(k for k in head if head[k] != design_entry_head(d)[k])
            fails.append(f"{who}: {', '.join(diff)} differ from the records' (measure again)")
        at = e["at"]
        if not isinstance(at, dict):
            fails.append(f"{who}: `at` is not an object")
            continue
        if sorted(at) != sorted(keys):
            fails.append(f"{who}: sizes {sorted(set(keys) - set(at))} missing, {sorted(set(at) - set(keys))} extra")
        for key in keys:
            if key not in at:
                continue
            x, where = at[key], f"{who} @ {key}"
            if not isinstance(x, dict):
                fails.append(f"{where}: not an object")
                continue
            if x.get("status") == "not measured":
                if set(x) != NOT_MEASURED_KEYS or x["why"] not in WHY or not (isinstance(x["reason"], str)
                                                                             and x["reason"].strip()):
                    fails.append(f"{where}: a not-measured size is exactly {{status, why ({'|'.join(WHY)}), reason, "
                                 "seconds}")
                if key == scored:
                    fails.append(f"{where}: the scoring size is never left unmeasured")
                continue
            if x.get("status") != "measured":
                fails.append(f"{where}: status must be `measured` or `not measured`")
                continue
            cyc = cycles_at(task, d, params[key]) if clocked else None
            fails += _measured_problems(where, x, clocked, cyc)
        if scored in at and not stale:
            a7e = None if a7_stale else L.asap7_entry(a7_table, sha)
            bad = control_problems(task, at[scored], d.get("records_full") or [], a7e)
            fails += [f"{who} @ {scored} (the scoring size): {b}" for b in bad]
    return fails, notes


# ---------------------------------------------------------------------------------------------------------------------
# the command
# ---------------------------------------------------------------------------------------------------------------------

def _context(args):
    """(config, {name: task}, the records) for the tasks named, or raises PlanError/OSError/ValueError."""
    L = lb()
    config = load_json(args.sizes_config)
    names = L.all_task_names(args.tasks_dir)
    tasks = {n: L.load_task(args.tasks_dir, n) for n in names}
    bad = config_problems(config, tasks)
    if bad:
        raise PlanError("leaderboard/sizes.json: " + "; ".join(bad))
    chosen = args.task or sorted(config["tasks"])
    unknown = [t for t in chosen if t not in config["tasks"]]
    if unknown:
        raise PlanError(f"no sizes for {', '.join(unknown)} (sizes.json: "
                        + "; ".join(f"{t}: {config.get('left_out', {}).get(t, 'not a task')}" for t in unknown) + ")")
    records = L.good_records(L.load_records(args.data_dir), warn=lambda m: print(m, file=sys.stderr))
    return config, {n: tasks[n] for n in chosen}, records


def task_plan(task, tcfg, records, tasks_dir, data_dir=None):
    L = lb()
    sizes, series, scored = task_sizes(task, tcfg)
    designs = plan_designs(task, records, L.par_names(tasks_dir, task), data_dir=data_dir)
    return sizes, series, scored, designs


def file_data(task, sizes, series, scored, designs, pins, at):
    """The file of `task`: its sizes and series, the pins, and per design file its `at` (size key -> entry)."""
    L = lb()
    return {"_comment": COMMENT, "schema": SCHEMA, "task": task["name"], "kind": task.get("kind"), "top": task.get("top"),
            "scoring_point": L.scoring_point(task), "scored": scored, "sizes": sizes, "series": series, "pins": pins,
            "designs": [dict(design_entry_head(designs[sha]), at=dict(sorted(at.get(sha, {}).items())))
                        for sha in sorted(designs)]}


def _write(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), prefix=".sizes-", suffix=".json")
    with os.fdopen(fd, "w", encoding="utf-8") as fh:
        fh.write(data_text(data))
    os.replace(tmp, path)


def cmd_check(args):
    L = lb()
    config, tasks, records = _context(args)
    status = 0
    a7_ident = L.asap7_identity()
    for name, task in tasks.items():
        sizes, series, scored, designs = task_plan(task, config["tasks"][name], records, args.tasks_dir, args.data_dir)
        path = data_path(name, args.sizes_dir)
        if not os.path.isfile(path):
            print(f"[FAIL] {name}: no {os.path.relpath(path, SVGOLF)}: `leaderboard.py sizes --write --task {name}` "
                  "measures it")
            status = 1
            continue
        text = _read(path)
        try:
            data = json.loads(text)
        except ValueError as e:
            print(f"[FAIL] {name}: not JSON: {e}")
            status = 1
            continue
        now = pins_now(task, limits_of(config))
        a7, _ = L.read_asap7(name, args.asap7_dir)
        fails, notes = check_data(data, task, sizes, series, scored, designs, now, a7_table=a7, a7_identity=a7_ident,
                                  text=text)
        n_at = sum(1 for e in data.get("designs") or [] for x in (e.get("at") or {}).values()
                   if isinstance(x, dict) and x.get("status") == "measured")
        n_not = sum(1 for e in data.get("designs") or [] for x in (e.get("at") or {}).values()
                    if isinstance(x, dict) and x.get("status") == "not measured")
        tag = "FAIL" if fails else ("stale" if notes else "ok")
        print(f"[{tag}] {name}: {len(designs)} design files x {len(sizes)} sizes: {n_at} measured, {n_not} not "
              "measured" + ("; the scoring size equals every record's own columns" if not fails and not notes else "")
              + ("".join(f"\n    {m}" for m in fails + notes)))
        status = status or (1 if fails else 0)
    return status


def liberty_problems():
    """Why score/ppa.py could not weigh here (the sky130 liberty or the ASAP7 files missing or not the pinned ones), as
    strings; [] when both load. Checked before anything is measured, so that a run that fails for want of a file is
    never recorded as the flow's refusal of a design."""
    spec = importlib.util.spec_from_file_location("svgolf_ppa_sizes", PPA_PY)
    ppa = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ppa)
    out = []
    for pdk in ("sky130", "asap7"):
        try:
            pins = ppa.Pins(ppa.pdk_paths(pdk)[0])
            ppa.Liberty(ppa.find_liberty(None, pins), pins)
        except (ppa.PpaError, OSError) as e:
            out.append(f"{pdk}: {' '.join(str(e).split())}")
    return out


def _write_state(args, name, task, config, records, limits, a7_ident):
    """The plan of one task for `--write`: its sizes and designs, the pins now, the entries an existing file under the
    same pins already has (kept), and the units (design, size) to measure: the scoring sizes first, then the others."""
    L = lb()
    sizes_, series, scored, designs = task_plan(task, config["tasks"][name], records, args.tasks_dir, args.data_dir)
    pins = pins_now(task, limits)
    if None in (pins["sky130"].get("ppa_version"), pins["asap7"], pins["flow"].get("yosys")):
        raise PlanError("the sky130 or ASAP7 pins cannot be read, or Yosys cannot be run")
    path = data_path(name, args.sizes_dir)
    at = {sha: {} for sha in designs}
    keys = {x["key"] for x in sizes_}
    if os.path.isfile(path):
        old = load_json(path)
        if isinstance(old, dict) and not stale_keys(old.get("pins"), pins):
            for e in old.get("designs") or []:
                if e.get("sv_sha256") in designs:
                    at[e["sv_sha256"]] = {k: v for k, v in (e.get("at") or {}).items() if k in keys}
        else:
            print(f"{name}: the existing file was made under other pins: measuring everything again", file=sys.stderr)
    a7, _ = L.read_asap7(name, args.asap7_dir)
    a7_ok = a7 is not None and not L.asap7_table_mismatch(a7, task, identity=a7_ident, flow=pins["flow"])

    def wanted(sha, x):
        return ((not args.size or x["key"] in args.size)
                and (not args.design or any(sha.startswith(p) or any(r["record_hash"].startswith(p)
                                                                     for r in designs[sha]["records"])
                                            for p in args.design)))
    todo = [(sha, x) for sha in sorted(designs) for x in sizes_ if x["key"] not in at[sha] and wanted(sha, x)]
    order = param_order(task)
    return {"name": name, "task": task, "sizes": sizes_, "series": series, "scored": scored, "designs": designs,
            "pins": pins, "path": path, "at": at, "a7": a7 if a7_ok else None, "failed": [],
            "first": [u for u in todo if u[1]["scored"]],
            # the others longest first (the product of the parameters as the guess), so that a long run overlaps
            # the short ones instead of running alone at the end
            "rest": sorted((u for u in todo if not u[1]["scored"]),
                           key=lambda u: (-_cost(u[1]["params"], order), u[0]))}


def cmd_write(args):
    """Measure what is missing for every task named, in ONE pool of `--jobs` runs (at most MAX_JOBS): each task's
    scoring sizes first (the control: a design whose scoring size differs from its records fails the task, and nothing
    more of it is measured), then its other sizes. The file is written after every run, so an interrupted run resumes."""
    L = lb()
    config, tasks, records = _context(args)
    bad = liberty_problems()
    if bad:
        raise PlanError("score/ppa.py cannot weigh here: " + "; ".join(bad))
    limits = limits_of(config)
    jobs = max(1, min(MAX_JOBS, args.jobs))
    lock = threading.Lock()
    a7_ident = L.asap7_identity()
    states = {name: _write_state(args, name, task, config, records, limits, a7_ident) for name, task in tasks.items()}
    for st in states.values():
        n = len(st["first"]) + len(st["rest"])
        print(f"{st['name']}: {len(st['designs'])} design files x {len(st['sizes'])} sizes; {n} to measure "
              f"({len(st['first'])} at the scoring size first), {jobs} at a time", file=sys.stderr, flush=True)
    timings = open(args.timings, "a", encoding="utf-8") if args.timings else None

    def one(st, unit):
        sha, x = unit
        d, task = st["designs"][sha], st["task"]
        cyc = cycles_at(task, d, x["params"]) if L.is_clocked_task(task) else None
        run = {}
        row = measure_one(task, d, x, cyc, st["pins"], limits, log=lambda r: run.update(r))
        msg = (f"  {st['name']} {sha[:12]} @ {x['key']}: " + (
            f"{row['area_um2']} um^2, {row['time_ps']} ps" if row["status"] == "measured"
            else f"not measured ({row['why']}): {row['reason']}")
            + f" [{run.get('seconds', 0):.1f} s, peak {run.get('peak_bytes', 0) / 1e9:.2f} GB]")
        if timings:
            with lock:
                timings.write(json.dumps({"task": st["name"], "design": sha, "size": x["key"], "status": row["status"],
                                          "seconds": round(run.get("seconds", 0), 2), "peak_bytes": run.get("peak_bytes"),
                                          "limit": run.get("limit")}, sort_keys=True) + "\n")
                timings.flush()
        return row, msg

    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
            futs = {}

            def submit(st, units):
                for u in units:
                    futs[pool.submit(one, st, u)] = (st, u)

            def fail(st, why):
                st["failed"].append(why)
                for f, (s2, _) in list(futs.items()):
                    if s2 is st:
                        f.cancel()

            for st in states.values():
                submit(st, st["first"] or st["rest"])
                st["first_left"] = len(st["first"])
            while futs:
                done, _ = concurrent.futures.wait(list(futs), return_when=concurrent.futures.FIRST_COMPLETED)
                for f in done:
                    st, (sha, x) = futs.pop(f)
                    if f.cancelled() or st["failed"]:
                        continue
                    try:
                        row, msg = f.result()
                    except PlanError as e:
                        fail(st, f"infrastructure: {e}")
                        continue
                    print(msg, file=sys.stderr, flush=True)
                    if x["scored"]:
                        a7e = L.asap7_entry(st["a7"], sha) if st["a7"] is not None else None
                        bad = control_problems(st["task"], row, st["designs"][sha]["records_full"], a7e)
                        if bad:
                            fail(st, f"{sha[:12]} @ {x['key']} (the scoring size) differs from its records: "
                                 + "; ".join(bad))
                            continue
                    with lock:
                        st["at"][sha][x["key"]] = row
                        _write(st["path"], file_data(st["task"], st["sizes"], st["series"], st["scored"],
                                                     st["designs"], st["pins"], st["at"]))
                    if x["scored"]:
                        st["first_left"] -= 1
                        if st["first_left"] == 0:
                            submit(st, st["rest"])
    finally:
        if timings:
            timings.close()
    status = 0
    for st in states.values():
        if st["failed"]:
            print(f"[FAIL] {st['name']}: " + "\n    ".join(st["failed"]), file=sys.stderr)
            status = 1
            continue
        _write(st["path"], file_data(st["task"], st["sizes"], st["series"], st["scored"], st["designs"], st["pins"],
                                     st["at"]))
        print(f"[ok] {st['name']}: wrote {os.path.relpath(st['path'], SVGOLF)}", file=sys.stderr, flush=True)
    return status


def _cost(params, order):
    """A rough order of cost (cheap first): the product of the parameters."""
    c = 1
    for k in order:
        c *= params[k]
    return c


def run(args, lb_module=None):
    """`leaderboard.py sizes`: check (default) or `--write`. Exit 0 good, 1 a check or a measurement failed, 2 usage
    or infrastructure."""
    global LB
    if lb_module is not None:
        LB = lb_module
    try:
        return cmd_write(args) if args.write else cmd_check(args)
    except PlanError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2
    except (OSError, ValueError) as e:
        print(f"error: {e}", file=sys.stderr)
        return 2


def add_parser(sub, common):
    """The `sizes` subcommand of leaderboard.py."""
    z = sub.add_parser("sizes", parents=[common],
                       help="the records' designs at other sizes (leaderboard/sizes/<task>.json; measured, not ranked): "
                       "check the files offline (default) or measure and write them (--write)")
    z.add_argument("--task", action="append", help="only this task (repeatable)")
    z.add_argument("--write", action="store_true",
                   help="measure what is missing (the pinned flow, under sizes.json's limits) and write the file(s); "
                   "every design's scoring size must equal its records' own columns")
    z.add_argument("--jobs", type=int, default=1, help=f"runs at a time with --write (at most {MAX_JOBS})")
    z.add_argument("--size", action="append", metavar="KEY", help="with --write: only this size (e.g. N=64; repeatable)")
    z.add_argument("--design", action="append", metavar="PREFIX",
                   help="with --write: only the design file whose sha256, or one of whose records' hash, starts so")
    z.add_argument("--timings", metavar="OUT.jsonl", help="with --write: append each run's wall time and peak memory")
    z.add_argument("--sizes-config", default=CONFIG, help=argparse.SUPPRESS)
    z.add_argument("--sizes-dir", default=OUT_DIR, help=argparse.SUPPRESS)
    return z
