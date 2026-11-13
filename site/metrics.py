"""The numbers a task page compares designs on: the combined score (leaderboard/combined.py), the
sky130 columns it is made of, and the other metrics a design has (area in GE, depth, gates, energy,
proof length). Standard library only; deterministic (every lookup is by content hash or by name).

Where the sky130 numbers come from, for a design at its task's scoring point:

  * a clocked task's scores in tests/expected.json carry them (`area_um2`, `period_ps`, `cycles`,
    `time_ps`: check.py's ranked pair);
  * a record's own `ppa` block, when it has one (`leaderboard.py add` writes it);
  * the sky130 goldens of score/tests/ppa/ (designs.json + expected_ppa.json, re-measured by
    score/test_ppa.py), matched by the sha256 of the design file (references, baselines) or by the
    canonical RTLIL hash (records) at the same parameters. Goldens of another `ppa_version` or
    liberty than score/ppa_pins.json pins are not used (a warning).

Energy and leakage come from tests/expected_sky130.json (`energy`, keyed `task/stem@point`). A
design with none of these simply lacks the metric: nothing is estimated.
"""

import hashlib
import importlib.util
import json
import os
import subprocess

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)


def _load_combined():
    spec = importlib.util.spec_from_file_location("svgolf_combined", os.path.join(SVGOLF, "leaderboard", "combined.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


combined = _load_combined()


class Metric:
    """One numeric column of a design: its key in the page data, a short label, the unit, one
    sentence saying what it is, and the decimals it is printed with."""

    def __init__(self, key, label, unit, what, digits=0):
        self.key, self.label, self.unit, self.what, self.digits = key, label, unit, what, digits

    def axis(self):
        return f"{self.label} ({self.unit})" if self.unit else self.label

    def fmt(self, v):
        """The value as text (charts.js's fmtMetric prints it the same way): the score by
        combined.fmt, else `digits` decimals, the whole part in thin-space groups from 10 000."""
        if v is None:
            return "–"
        if self.key == "adp":
            return combined.fmt(v)
        s = f"{v:.{self.digits}f}" if self.digits else f"{round(v)}"
        if abs(v) >= 10000:
            whole, dot, frac = s.partition(".")
            s = f"{int(whole):,}".replace(",", " ") + dot + frac
        return s

    def data(self):
        return {"key": self.key, "label": self.label, "unit": self.unit, "what": self.what, "digits": self.digits}


CELL_PREFIX = "sky130_fd_sc_hd__"


def input_drive(task, svgolf=SVGOLF):
    """The cell in front of every primary input of `task` in the ranked sky130 score (sky130_a0_v3): its
    task.json `input_drive`, else score/ppa_pins.json's `timing.input_drive.default` (score/ppa.py's
    `input_drive_of`); None if neither says."""
    if "input_drive" in task:
        return task["input_drive"]
    try:
        with open(os.path.join(svgolf, "score", "ppa_pins.json"), encoding="utf-8") as fh:
            return json.load(fh)["timing"]["input_drive"]["default"]
    except (OSError, ValueError, KeyError, TypeError):
        return None


def asap7_input_drive(svgolf=SVGOLF):
    """The cell in front of every primary input in the ASAP7 view (score/ppa_pins_asap7.json's default, as
    leaderboard.py's `asap7_identity` reads it), or None."""
    try:
        with open(os.path.join(svgolf, "score", "ppa_pins_asap7.json"), encoding="utf-8") as fh:
            return json.load(fh)["timing"]["input_drive"]["default"]
    except (OSError, ValueError, KeyError, TypeError):
        return None


ASAP7_SUFFIX = "_ASAP7_75t_R"


def metric_table(clocked, drive=None, latency=True, pdk="sky130"):
    """Every metric, in the order the explorer offers them. The time is the delay of a
    combinational design and cycles x period of a clocked one; `drive` is the task's input drive
    (`input_drive`), which the delay's sentence names. A clocked task without a latency (`latency`
    false: a reactive task, one decision per cycle) has the period as its time, so it has no
    separate period and no latency column. `pdk` "asap7": the ASAP7 view's (decided 2026-11-09): its area
    and time are the ASAP7 columns (`drive` then an ASAP7 cell; three decimals of µm²); the energy
    metrics are measured on sky130 alone, so an ASAP7 design does not carry them and that view has none."""
    cell = drive[len(CELL_PREFIX):] if isinstance(drive, str) and drive.startswith(CELL_PREFIX) else drive
    if isinstance(cell, str) and cell.endswith(ASAP7_SUFFIX):
        cell = cell[:-len(ASAP7_SUFFIX)]
    a7 = pdk in ("asap7", "asap7pnr")
    lib = "ASAP7" if a7 else "sky130"
    liberty = "the pinned ASAP7 liberty" if a7 else "the pinned liberty"
    if pdk == "asap7pnr":      # the routed course (decided 2026-11-11/12): the wires extracted from the layout count
        time = (Metric("time_ps", "Time", "ps", "Cycles × the clock period of the placed and routed netlist, wires "
                       "included (the period minus the worst setup slack).")
                if clocked and latency else
                Metric("time_ps", "Time", "ps", "The clock period of the placed and routed netlist, wires included, one "
                       "decision per cycle.")
                if clocked else
                Metric("time_ps", "Delay", "ps", "The critical-path delay of the placed and routed netlist, with the "
                       "wires extracted from the layout."))
    else:
        time = (Metric("time_ps", "Time", "ps", f"Cycles × the register-to-register period from {liberty}.")
                if clocked and latency else
                Metric("time_ps", "Time", "ps", f"The register-to-register period from {liberty}, one decision "
                       "per cycle.")
                if clocked else
                Metric("time_ps", "Delay", "ps", f"The critical-path delay of the {lib} netlist (static timing"
                       + (f", inputs driven by a {cell}" if cell else "") + ")."))
    area_what = ("The ASAP7 cell area of the placed and routed netlist (the cells the flow added included; tap and "
                 "fill cells not)." if pdk == "asap7pnr" else
                 f"The {lib} cell area of the scored netlist" + (", flip-flops included." if clocked
                                                                 else ", repaired by buffering."))
    per_cycle = [Metric("period_ps", "Clock period", "ps", "The register-to-register period."),
                 Metric("cycles", "Latency", "cycles", "The declared latency at the scoring point.")]
    return [
        Metric("adp", "Score", combined.UNIT, "Area × time, the ranked score: lower is better." if pdk != "asap7" else
               "Area × time, the score this view orders by: lower is better.", 0),
        Metric("area_um2", "Area", "µm²", area_what, 3 if a7 else 1),
        time,
        *(per_cycle if latency else []),
        Metric("ffs", "Flip-flops", "", "Flip-flops in the scored netlist."),
        Metric("energy_fj", "Energy", "fJ/op", "Energy per operation on random inputs, glitches counted."),
        Metric("energy_cycle_fj", "Energy", "fJ/cycle", "Energy per clock cycle, clock tree included."),
        Metric("leakage_nw", "Leakage", "nW", "Static leakage power of the cells."),
        Metric("area_ge", "Area", "GE", "The area in NAND2 gate equivalents of the pinned Yosys flow.", 3),
        Metric("depth", "Depth", "gates", "Gates on the longest path of the pinned Yosys netlist."),
        Metric("gates", "Gates", "", "Gates in the pinned Yosys netlist."),
        Metric("proof_lines", "Proof", "lines", "Code lines of the Lean proof."),
    ]


INTEGER = ("depth", "cycles", "ffs", "gates", "proof_lines")   # whole-number metrics: integer axes


def is_clocked(task):
    """A clocked task's score: flops included, time = cycles x the period (a reactive task: one cycle)."""
    return task.get("kind", "") in ("tx-family", "stream-family", "react-family")


LATENCY_KINDS = ("tx-family", "stream-family")      # check.py's: a clocked task whose Goal takes a latency


def has_latency(task):
    """Whether the task's score has a latency factor (check.py's LATENCY_KINDS): a combinational task has none
    to show, a reactive one makes one decision per cycle (cycles = 1, so the time is the period)."""
    return task.get("kind", "") in LATENCY_KINDS


def _params_key(params):
    return ",".join(f"{k}={params[k]}" for k in sorted(params))


def _sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


class Sky130:
    """The sky130 goldens (score/tests/ppa/), indexed by design file hash and by canonical RTLIL
    hash, each at its parameters; the energy goldens (tests/expected_sky130.json) by name."""

    def __init__(self, svgolf=SVGOLF, warn=None):
        self.by_file, self.by_rtlil, self.energy = {}, {}, {}
        self.version = None
        warn = warn or (lambda msg: None)
        ppa_dir = os.path.join(svgolf, "score", "tests", "ppa")
        try:
            with open(os.path.join(svgolf, "score", "ppa_pins.json"), encoding="utf-8") as fh:
                pins = json.load(fh)
            with open(os.path.join(ppa_dir, "designs.json"), encoding="utf-8") as fh:
                designs = json.load(fh)["designs"]
            with open(os.path.join(ppa_dir, "expected_ppa.json"), encoding="utf-8") as fh:
                gold = json.load(fh)
        except (OSError, ValueError, KeyError) as e:
            warn(f"the sky130 goldens cannot be read ({e}): no design has a sky130 score")
            designs, gold, pins = [], {"designs": {}}, {}
        if designs and (gold.get("ppa_version") != pins.get("ppa_version")
                        or gold.get("liberty_sha256") != (pins.get("liberty") or {}).get("sha256")):
            warn(f"score/tests/ppa/expected_ppa.json is {gold.get('ppa_version')}, the pins are "
                 f"{pins.get('ppa_version')}: its sky130 numbers are not used")
            designs = []
        self.version = gold.get("ppa_version")
        for d in sorted(designs, key=lambda d: d["name"]):
            g = gold["designs"].get(d["name"])
            src = os.path.join(svgolf, *d["src"].split("/"))
            if not g or not os.path.isfile(src):
                continue
            cols = {"area_e4um2": g["area_e4um2"], "delay_ps": g["delay_ps"], "cells": g.get("cells"),
                    "area_mge": round(g["area_ge"] * 1000), "depth": g.get("depth")}
            key = (d["task"], _params_key(d.get("params") or {}))
            self.by_file[key + (_sha256_file(src),)] = cols
            if g.get("rtlil_sha256"):
                self.by_rtlil[key + (g["rtlil_sha256"],)] = cols
        try:
            with open(os.path.join(svgolf, "tests", "expected_sky130.json"), encoding="utf-8") as fh:
                self.energy = json.load(fh).get("energy") or {}
        except (OSError, ValueError):
            self.energy = {}

    def of_file(self, task, params, path):
        return self.by_file.get((task, _params_key(params), _sha256_file(path)))

    def of_rtlil(self, task, params, rtlil):
        return self.by_rtlil.get((task, _params_key(params), rtlil)) if rtlil else None

    def energy_of(self, task, stem, point_key):
        return self.energy.get(f"{task}/{stem}@{point_key}")


MEASURED_SCHEMA = "svgolf-points/1"


def load_measured(task_name, identity, input_drive, svgolf=SVGOLF, warn=None):
    """score/measured/<task>.json (score/points.py): the task's designs measured by the pinned flow at every point of
    score/points.json, or None when there is none. Data weighed under another sky130 identity or input drive than now
    (`identity`: leaderboard.py's `ppa_identity()`, `input_drive`: the task's) is not used (a warning): measured, not
    ranked, but never stale."""
    path = os.path.join(svgolf, "score", "measured", f"{task_name}.json")
    if not os.path.isfile(path):
        return None
    warn = warn or (lambda msg: None)
    try:
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
    except (OSError, ValueError) as e:
        warn(f"score/measured/{task_name}.json cannot be read ({e}): no other points are shown")
        return None
    ident = data.get("identity") or {}
    if (data.get("schema") != MEASURED_SCHEMA or data.get("task") != task_name or identity is None
            or any(ident.get(k) != v for k, v in identity.items()) or ident.get("input_drive") != input_drive):
        warn(f"score/measured/{task_name}.json was measured under another sky130 identity, input drive or schema than "
             "now: its points are not shown (run score/points.py measure)")
        return None
    return data


def measured_metrics(row, *, proof_lines=None):
    """The metrics of one design at one measured point (a row of score/measured/<task>.json), as `design_metrics`
    names them, and its exact combined score."""
    exact = combined.of_columns(area_e4um2=row["area_e4um2"], time=row.get("time_ps"))
    m = {"area_um2": row["area_e4um2"] / 10000, "area_ge": row["area_mge"] / 1000, "depth": row["depth"],
         "gates": row["num_gates"]}
    for k in ("time_ps", "period_ps", "cycles", "ffs"):
        if row.get(k) is not None:
            m[k] = row[k]
    if exact is not None:
        m["adp"] = combined.um2ns(exact)
    if proof_lines is not None:
        m["proof_lines"] = proof_lines
    return m, exact


def design_metrics(score, *, sky=None, ppa=None, energy=None, proof_lines=None):
    """The metrics of one design at the scoring point, and its exact combined score (or None).
    `score`: the pinned flow's score (tests/expected.json, or a record's `score`); `sky`: a golden
    of Sky130 (comb); `ppa`: a record's own ppa block; `energy`: its energy golden."""
    m = {"area_ge": score["area_mge"] / 1000, "depth": score["depth"]}
    if score.get("num_gates") is not None:
        m["gates"] = score["num_gates"]
    exact = None
    if "time_ps" in score and "area_um2" in score:                   # a clocked score: check.py's ranked pair
        exact = combined.of_columns(area_um2=score["area_um2"], time=score["time_ps"])
        m.update(area_um2=score["area_um2"], time_ps=score["time_ps"])
        for k in ("period_ps", "cycles", "ffs"):
            if score.get(k) is not None:
                m[k] = score[k]
    elif isinstance(ppa, dict) and ppa.get("available") is True and ppa.get("area_e4um2_sky130") is not None:
        exact = combined.of_columns(area_e4um2=ppa["area_e4um2_sky130"], delay_ps=ppa.get("delay_ps_sky130"))
        m.update(area_um2=ppa["area_e4um2_sky130"] / 10000, time_ps=ppa.get("delay_ps_sky130"))
    elif sky and sky["area_mge"] == score["area_mge"] and sky["depth"] == score["depth"]:
        exact = combined.of_columns(area_e4um2=sky["area_e4um2"], delay_ps=sky["delay_ps"])
        m.update(area_um2=sky["area_e4um2"] / 10000, time_ps=sky["delay_ps"])
    if exact is not None:
        m["adp"] = combined.um2ns(exact)
    if energy:
        if energy.get("energy_glitch_sky130_v1") is not None:
            m["energy_fj"] = energy["energy_glitch_sky130_v1"]
        if energy.get("energy_cycle_sky130_v1") is not None:
            m["energy_cycle_fj"] = energy["energy_cycle_sky130_v1"]
        if energy.get("leakage_sky130_v1") is not None:
            m["leakage_nw"] = energy["leakage_sky130_v1"]
    if proof_lines is not None:
        m["proof_lines"] = proof_lines
    return {k: v for k, v in m.items() if v is not None}, exact


_DATES = {}


def commit_date(path):
    """The date (YYYY-MM-DD, the author date) of the last commit that changed the file `path`, or
    None outside a git checkout or for a file git does not track. A function of the repository's
    history, so two builds of one checkout agree."""
    if path not in _DATES:
        try:
            out = subprocess.run(["git", "-C", os.path.dirname(path), "log", "-1", "--format=%as", "--",
                                  os.path.basename(path)], capture_output=True, text=True, timeout=30,
                                 env=dict(os.environ, GIT_OPTIONAL_LOCKS="0"))
            d = out.stdout.strip() if out.returncode == 0 else ""
        except (OSError, subprocess.SubprocessError):
            d = ""
        _DATES[path] = d if len(d) == 10 else None
    return _DATES[path]
