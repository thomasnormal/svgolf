#!/usr/bin/env python3.12
"""The data of the record pages' schematic and critical-path sections, generated once and committed.

    nice -n 19 python3.12 site/gen_schematics.py --netlistsvg DIR [--task T ...]   # (re)generate
    python3.12 site/gen_schematics.py --check                                      # the committed files, no tools

Run from svgolf/ (any directory works). For every design that gets a page on the site (each proved reference of a
task with a display instance, which every listed task has: par's design has a page of its own, and another reference
is an entry whose page is its record's, the same file; and each record in leaderboard/data/<task>/; a design file
shared by several is done once) it writes
two files under site/schematics/<task>/, named by the first 16 hex digits of the design file's sha256:

  <key>.json   the scored point: score/ppa.py --path on the design at task.json's scoring point (the ranked area
               and delay, the cells, the repair and legality summary, and the critical path node by node with the
               driving cell, the arrival and the transition: ppa.py's `critical_path_timing`); and the display
               instance: the same design through the same pinned flow at the task's display parameters
               (site/schematics/display.json), its numbers, its critical path and what was drawn.
  <key>.svg    the schematic of the display instance's repaired A0' netlist (exactly what A0' weighs, at the
               small size), drawn by netlistsvg with svGolf's sky130 skin (site/schematics/sky130_skin.svg): one
               symbol per cell function, the cell printed above it, the instance and cell on hover, the critical
               path marked. Above display.json's `max_full_cells` cells (or with `draw: critical`) only the critical
               path is drawn, each net that enters or leaves it as a port named after the net, and the path's own
               nets marked.

The site build (site/build.py) only READS these files: it stays offline, needs no Yosys and no Node, and checks
that each file's scored numbers are the ones the page shows (a record's `ppa` block, or the golden of a reference
without a record); a missing or stale file is a warning (fatal under --strict), never a wrong number.

THE FLOW. Each design is run through `score/ppa.py SV --task tasks/<t> --no-mapped --path` twice, at the scoring
point and with `--param K=V ...` at the display instance (`--repaired-netlist` there), each in its own process, one
at a time (run the tool under `nice -n 19`); a design of a clocked task (check.py's CLOCKED_KINDS) with `--seq` too,
the clocked flow check.py scores it with, so the delay is the register-to-register period. The repaired netlist is read by the pinned Yosys against the pinned
liberty's cells as black boxes (`read_liberty -lib`, `read_verilog`, `write_json`), turned into netlistsvg's input
here, and drawn by `node netlistsvg.js IN.json --skin sky130_skin.svg`.

NETLISTSVG is pinned: version 1.0.2 with its layout engine elkjs 0.3.0 (the layout is elkjs's, so both are
checked, from their package.json files, before anything runs). Install it once, outside the repository:

    mkdir -p ~/.cache/svgolf-netlistsvg && cp site/schematics/npm/package.json site/schematics/npm/package-lock.json \\
        ~/.cache/svgolf-netlistsvg/ && (cd ~/.cache/svgolf-netlistsvg && npm ci --no-audit --no-fund)

(the lockfile pins every package; Node 25 was used) and pass `--netlistsvg ~/.cache/svgolf-netlistsvg/node_modules`
(or set $SVGOLF_NETLISTSVG). netlistsvg is MIT licensed and is not vendored; the skin is derived from its default
skin and keeps that notice (site/schematics/LICENSE-netlistsvg.txt, named in NOTICE).

DETERMINISM. Nothing in the output depends on the machine, the clock or a path: the SVG is rewritten here (the
skin's style replaced by one that reads the site's colour tokens, so that it follows the page's light and dark
themes; netlistsvg's own attributes, the per-cell classes and its black junction dots dropped; every coordinate
rounded to 0.1), the JSON has sorted keys and no wall time, and two runs give the same bytes (tested:
tests/site/test_schematics.py). The total size of the committed SVGs is bounded by display.json's
`max_total_bytes` (5 MB); a design whose drawing would pass it is skipped, with the reason in its JSON.

Exit status: 0 done (or --check passed), 1 a run or the check failed, 2 usage error.
"""

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET

sys.dont_write_bytecode = True
SITE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(SITE)
OUT = os.path.join(SITE, "schematics")
DISPLAY = os.path.join(OUT, "display.json")
SKIN = os.path.join(OUT, "sky130_skin.svg")
PPA_PY = os.path.join(SVGOLF, "score", "ppa.py")
TASKS = os.path.join(SVGOLF, "tasks")
RECORDS = os.path.join(SVGOLF, "leaderboard", "data")
SCHEMA = "svgolf-schematic/1"
NETLISTSVG = "1.0.2"
ELKJS = "0.3.0"
PREFIX = "sky130_fd_sc_hd__"
CLOCKED_KINDS = ("seq-family", "tx-family", "stream-family", "react-family")     # check.py's
SVG_NS = "http://www.w3.org/2000/svg"
NSVG_NS = "https://github.com/nturley/netlistsvg"
# sky130 cell function -> (skin symbol, {cell pin: skin pin}); the A0' table, the repair's buffers, the tie cell, the flop
CELLS = {
    "and2": ("and2", {"A": "A", "B": "B", "X": "Y"}),
    "nand2": ("nand2", {"A": "A", "B": "B", "Y": "Y"}),
    "or2": ("or2", {"A": "A", "B": "B", "X": "Y"}),
    "nor2": ("nor2", {"A": "A", "B": "B", "Y": "Y"}),
    "xor2": ("xor2", {"A": "A", "B": "B", "X": "Y"}),
    "xnor2": ("xnor2", {"A": "A", "B": "B", "Y": "Y"}),
    "inv": ("inv", {"A": "A", "Y": "Y"}),
    "buf": ("buf", {"A": "A", "X": "Y"}),
    "mux2": ("mux2", {"A0": "A", "A1": "B", "S": "S", "X": "Y"}),
    "nor2b": ("nor2b", {"A": "A", "B_N": "B", "Y": "Y"}),        # Y = !A & B_N: an AND with a bubble on A
    "nand2b": ("nand2b", {"A_N": "A", "B": "B", "Y": "Y"}),      # Y = A_N | !B: an OR with a bubble on B
    "dfxtp": ("dfxtp", {"D": "D", "CLK": "CLK", "Q": "Q"}),
    "conb": ("conb", {"HI": "HI", "LO": "LO"}),
}
# The style of every drawing: scoped to svg.sch (an inline SVG's style applies to the whole page) and in the site's
# colour tokens (style.css), each with a light fallback for the file viewed on its own.
STYLE = (
    "svg.sch{fill:none;stroke:var(--text-2,#57524a);stroke-width:1;font-family:var(--mono,monospace)}"
    "svg.sch text{fill:var(--text,#1b1916);stroke:none;font-size:8px}"
    "svg.sch .cellref{fill:var(--text-3,#6b6459);font-size:7px;text-anchor:middle}"
    "svg.sch .nodelabel{text-anchor:middle}"
    "svg.sch .inputPortLabel{text-anchor:end}"
    "svg.sch .splitjoinBody,svg.sch .j{fill:var(--text-2,#57524a)}"
    "svg.sch .flop{fill:var(--surface-2,#faf6ef)}"
    "svg.sch .bufc{fill:var(--sunken,#f0ebe1)}"
    "svg.sch .port path{fill:var(--surface-2,#faf6ef)}"
    "svg.sch .crit path,svg.sch .crit circle,svg.sch .crit rect,svg.sch line.crit"
    "{stroke:var(--accent,#eb6834);stroke-width:2}"
    "svg.sch circle.j.crit{fill:var(--accent,#eb6834)}"
    "svg.sch .crit .cellref{fill:var(--accent-ink,#b4461b)}"
)


class GenError(Exception):
    pass


def load_json(path):
    with open(path, encoding="utf-8") as fh:
        return json.load(fh)


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def json_text(obj):
    return json.dumps(obj, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def site_config():
    return load_json(os.path.join(SITE, "config.json"))


def reference_player():
    return site_config()["reference_player"]


def listed_tasks():
    """The tasks the site shows (site/config.json: tutorial or listed), in its order."""
    return [t for t, how in site_config()["tasks"].items() if how in ("tutorial", "listed")]


def drawn_tasks():
    """The tasks with a display instance (site/schematics/display.json), in its order: every listed task, and a
    task whose drawing is prepared before the site lists it (its files are generated and checked all the same)."""
    return list(load_json(DISPLAY)["tasks"])


def key_of(sha):
    return sha[:16]


def designs(task):
    """The designs of `task` that get a page: [{sha256, src (svgolf-relative), names}], by sha256. A reference's
    record has the reference's own file, so it is the same design; a design file shared by two entries is one."""
    tj = load_json(os.path.join(TASKS, task, "task.json"))
    out = {}

    def add(src, name):
        with open(os.path.join(SVGOLF, src), "rb") as fh:
            sha = sha256_bytes(fh.read())
        d = out.setdefault(sha, {"sha256": sha, "src": src, "names": []})
        if name not in d["names"]:
            d["names"].append(name)
    for ref in tj.get("references", []):
        add(f"tasks/{task}/{ref['sv']}", "reference " + os.path.splitext(os.path.basename(ref["sv"]))[0])
    rdir = os.path.join(RECORDS, task)
    for f in sorted(os.listdir(rdir)) if os.path.isdir(rdir) else []:
        if f.endswith(".json"):
            rec = load_json(os.path.join(rdir, f))
            add(f"leaderboard/data/{task}/{f[:-5]}.sv", "record " + rec["record_hash"])
    for d in out.values():
        d["names"].sort()
    return [out[k] for k in sorted(out)]


# ---------------------------------------------------------------------------
# the tools
# ---------------------------------------------------------------------------

def run(cmd, timeout, what):
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                          env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    if proc.returncode != 0:
        raise GenError(f"{what} exited {proc.returncode}: {(proc.stderr or proc.stdout).strip()[-600:]}")
    return proc.stdout


def is_clocked(task):
    """Whether `task` is scored by the clocked flow (check.py's CLOCKED_KINDS, score.py --seq)."""
    return load_json(os.path.join(TASKS, task, "task.json")).get("kind") in CLOCKED_KINDS


def run_ppa(src, task, params=None, repaired=None, timeout=1800):
    """score/ppa.py --path on the design at the scoring point (params None) or at `params`: its JSON result. A clocked
    task's design goes through the clocked flow (`--seq`, which is A0' only), as check.py scores it."""
    cmd = [sys.executable, PPA_PY, os.path.join(SVGOLF, src), "--task", os.path.join(TASKS, task), "--no-mapped", "--path"]
    if is_clocked(task):
        cmd.append("--seq")
    for k, v in (params or {}).items():
        cmd += ["--param", f"{k}={v}"]
    if repaired:
        cmd += ["--repaired-netlist", repaired]
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout,
                          env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
    try:
        res = json.loads(proc.stdout)
    except ValueError:
        raise GenError(f"ppa.py printed no JSON (exit {proc.returncode}): {(proc.stderr or proc.stdout).strip()[-400:]}")
    if proc.returncode != 0 or "error" in res:
        first = str(res.get("error", "")).strip().splitlines()
        raise GenError("the pinned flow failed: " + (first[0] if first else f"exit {proc.returncode}"))
    return res


_PPA = []


def ppa_module():
    """score/ppa.py as a module (for the pinned liberty: its path and its cells' areas)."""
    if not _PPA:
        spec = importlib.util.spec_from_file_location("svgolf_ppa", PPA_PY)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        lib, pins = mod.open_library()
        _PPA.append((mod, lib, pins))
    return _PPA[0]


def cell_areas(cells):
    """{cell (no prefix): its area in 1e-4 um^2, read from the pinned liberty (hash-checked by ppa.py)}. The clocked
    flow's flop is read as ppa.py reads it (`FlopTiming`: its CLK->Q arc is no combinational arc)."""
    mod, lib, pins = ppa_module()
    return {c: (mod.FlopTiming(lib, pins).area_e4 if c == mod.FLOP_CELL else lib.cell(pins.prefix + c).area_e4)
            for c in sorted(cells)}


def yosys_json(repaired, top, work):
    """The repaired netlist as Yosys JSON, its sky130 cells read from the pinned liberty as black boxes."""
    lib = ppa_module()[1].path
    out = os.path.join(work, "netlist.json")
    script = os.path.join(work, "read.ys")
    with open(script, "w") as fh:
        fh.write(f'read_liberty -lib "{lib}"\nread_verilog "{repaired}"\nhierarchy -top {top}\nwrite_json "{out}"\n')
    run([os.environ.get("SVGOLF_YOSYS", "yosys"), "-q", "-s", script], 600, "yosys")
    return load_json(out)


def node_tool(nsvg_dir):
    """The netlistsvg entry point under `nsvg_dir` (a node_modules directory), checked against the pins."""
    for pkg, want in (("netlistsvg", NETLISTSVG), ("elkjs", ELKJS)):
        pj = os.path.join(nsvg_dir, pkg, "package.json")
        if not os.path.isfile(pj):
            raise GenError(f"no {pkg} under {nsvg_dir} (see the install note in this file's docstring)")
        got = load_json(pj).get("version")
        if got != want:
            raise GenError(f"{pkg} {got} under {nsvg_dir}, not the pinned {want}")
    return os.path.join(nsvg_dir, "netlistsvg", "bin", "netlistsvg.js")


def yosys_version():
    return run([os.environ.get("SVGOLF_YOSYS", "yosys"), "-V"], 60, "yosys -V").strip()


# ---------------------------------------------------------------------------
# the drawing
# ---------------------------------------------------------------------------

def top_module(yj):
    tops = [m for m, v in yj["modules"].items() if not m.startswith(PREFIX) and not v.get("attributes", {}).get("blackbox")]
    if len(tops) != 1:
        raise GenError(f"the netlist has {len(tops)} non-cell modules: {tops}")
    return tops[0], yj["modules"][tops[0]]


def cell_kind(ctype):
    m = re.fullmatch(PREFIX + r"([a-z0-9]+?)_(\d+)", ctype)
    if not m or m.group(1) not in CELLS:
        raise GenError(f"cell {ctype} has no symbol in the skin")
    return m.group(1), f"{m.group(1)}_{m.group(2)}"


def bit_names(mod):
    """{bit: the net's name} (a vector bit as name[i]); names that Yosys made up ($...) only where nothing else names
    the bit."""
    out = {}
    for nn in sorted(mod["netnames"], key=lambda n: (n.startswith("$"), n)):
        n = mod["netnames"][nn]
        for i, b in enumerate(n["bits"]):
            if isinstance(b, int):
                name = nn if len(n["bits"]) == 1 else f"{nn}[{i + n.get('offset', 0)}]"
                out.setdefault(b, name.lstrip("\\"))
    return out


def bit_of_net(mod, name):
    """The Yosys bit of a net as ppa.py names it ('_22_', 'b[0]'), or None."""
    if name in mod["netnames"]:
        b = mod["netnames"][name]["bits"]
        return b[0] if len(b) == 1 else None
    m = re.fullmatch(r"(.+)\[(\d+)\]", name)
    if m and m.group(1) in mod["netnames"]:
        n = mod["netnames"][m.group(1)]
        k = int(m.group(2)) - n.get("offset", 0)
        return n["bits"][k] if 0 <= k < len(n["bits"]) else None
    return None


def path_marks(mod, path):
    """(the instances, the Yosys bits) of a `critical_path_timing` path."""
    cells = sorted({n["inst"] for n in path if n.get("inst")})
    missing = [c for c in cells if c not in mod["cells"]]
    if missing:
        raise GenError(f"critical-path instances {missing[:3]} are not in the repaired netlist")
    bits = sorted({b for b in (bit_of_net(mod, n["net"]) for n in path) if b is not None})
    return cells, bits


def critical_piece(mod, keep):
    """The cells `keep` as a module of their own: every net that enters the piece from outside becomes an input
    port, every net read outside it (or by an output port) an output port, each named after its net."""
    names = bit_names(mod)
    drv = {b: cn for cn, c in mod["cells"].items() for p, bs in c["connections"].items()
           if c["port_directions"][p] == "output" for b in bs if isinstance(b, int)}
    read_outside = set()
    for cn, c in mod["cells"].items():
        if cn not in keep:
            read_outside.update(b for p, bs in c["connections"].items() if c["port_directions"][p] == "input"
                                for b in bs if isinstance(b, int))
    for pt in mod["ports"].values():
        if pt["direction"] == "output":
            read_outside.update(b for b in pt["bits"] if isinstance(b, int))
    ins, outs = {}, {}
    for cn in sorted(keep):
        c = mod["cells"][cn]
        for p in sorted(c["connections"]):
            for b in c["connections"][p]:
                if not isinstance(b, int):
                    continue
                nm = names.get(b, f"n{b}")
                if c["port_directions"][p] == "input" and drv.get(b) not in keep:
                    ins.setdefault(nm, b)
                if c["port_directions"][p] == "output" and b in read_outside:
                    outs.setdefault(nm, b)
    ports = {nm: {"direction": "input", "bits": [b]} for nm, b in ins.items()}
    for nm, b in outs.items():
        ports[nm + " (out)" if nm in ports else nm] = {"direction": "output", "bits": [b]}
    return {"ports": dict(sorted(ports.items())), "cells": {cn: mod["cells"][cn] for cn in sorted(keep)},
            "netnames": {}}


def netlistsvg_input(name, mod):
    """netlistsvg's input: each sky130 instance under its own name as a cell of the skin's type for its function, its
    pins renamed to the skin's, the cell (with its drive strength) as the attribute `cell`; no net attributes (Yosys
    puts the netlist file's path there)."""
    cells = {}
    for cn in sorted(mod["cells"]):
        c = mod["cells"][cn]
        kind, cell = cell_kind(c["type"])
        skin, pins = CELLS[kind]
        cells[cn] = {"type": skin, "port_directions": {pins[p]: d for p, d in sorted(c["port_directions"].items())},
                     "connections": {pins[p]: bs for p, bs in sorted(c["connections"].items())},
                     "attributes": {"cell": cell}}
    nets = {nn: {"bits": n["bits"], "hide_name": n.get("hide_name", 0)} for nn, n in sorted(mod["netnames"].items())}
    return {"modules": {name: {"ports": mod["ports"], "cells": cells, "netnames": nets}}}


NUM = re.compile(r"-?\d+(?:\.\d+)?(?:e-?\d+)?")


def _round(text):
    def one(m):
        v = round(float(m.group(0)), 1)
        s = f"{v:.1f}".rstrip("0").rstrip(".")
        return "0" if s in ("-0", "") else s
    return NUM.sub(one, text)


def rewrite_svg(raw, *, cells, crit_cells, crit_bits, title):
    """netlistsvg's SVG, rewritten for the site (see the module docstring): returns the final text."""
    ET.register_namespace("", SVG_NS)
    root = ET.fromstring(raw)
    q = lambda t: f"{{{SVG_NS}}}{t}"                                   # noqa: E731
    crit_cells, crit_bits = set(crit_cells), {str(b) for b in crit_bits}

    def strip(el):
        for k in [k for k in el.attrib if k.startswith(f"{{{NSVG_NS}}}")]:
            del el.attrib[k]
        for child in list(el):
            if child.tag.startswith(f"{{{NSVG_NS}}}"):
                el.remove(child)
            elif child.tag == q("g") and not len(child) and not child.attrib.get("class") and not child.text:
                el.remove(child)                                         # a pin anchor of the skin
            else:
                strip(child)
    strip(root)
    for st in root.findall(q("style")):
        root.remove(st)
    for el in root.iter():
        cls = el.attrib.get("class")
        if cls is not None:
            kept = [c for c in cls.split() if not c.startswith(("cell_", "net_", "width_", "$"))]
            nets = [c[4:] for c in cls.split() if c.startswith("net_")]
            if el.tag in (q("line"), q("circle")) and nets:
                if el.tag == q("circle"):
                    kept.append("j")
                    el.attrib.pop("style", None)                        # netlistsvg's black dot: the style's colour
                if len(nets) == 1 and nets[0] in crit_bits:
                    kept.append("crit")
            if kept:
                el.set("class", " ".join(kept))
            else:
                del el.attrib["class"]
        for k in ("x", "y", "x1", "x2", "y1", "y2", "cx", "cy", "r", "width", "height", "transform", "d"):
            if k in el.attrib and el is not root:
                el.set(k, _round(el.attrib[k]))
    groups = [g for g in root.findall(q("g")) if g.attrib.get("id", "").startswith("cell_")]
    for g in groups:
        key = g.attrib.pop("id")[len("cell_"):]
        if key in cells:
            g.set("class", "c crit" if key in crit_cells else "c")
            g.set("data-inst", key)
            t = ET.Element(q("title"))
            t.text = f"{key} · {PREFIX}{cells[key]}"
            g.insert(0, t)
        else:
            kind = "port" if g.findall(q("path")) and not g.findall(q("rect")) else "sj"
            g.set("class", kind)
    w, h = _round(root.attrib["width"]), _round(root.attrib["height"])
    attrs = {"class": "sch", "viewBox": f"0 0 {w} {h}", "width": w, "height": h, "role": "img", "aria-label": title}
    root.attrib.clear()
    root.attrib.update(attrs)
    style = ET.Element(q("style"))
    style.text = STYLE
    root.insert(0, style)
    for el in root.iter():
        if el.text is not None and not el.text.strip():
            el.text = None
        if el.tail is not None:
            el.tail = None
    text = ET.tostring(root, encoding="unicode", short_empty_elements=True)
    return text.replace("><", ">\n<") + "\n"


def draw(name, mod, path, *, piece, nsvg, work, title):
    """(the SVG text, the number of cells drawn) of the display netlist `mod`: whole, or with `piece` the critical
    path's cells only."""
    crit_cells, crit_bits = path_marks(mod, path)
    if piece:
        # every cell drawn is on the path, so no cell is marked; the path's own nets are (the piece keeps the
        # netlist's bits), so that the chain from the first input to the endpoint can be followed through the
        # side inputs, which are ports
        mod = critical_piece(mod, set(crit_cells))
        crit_cells = []
    if not mod["cells"]:
        raise GenError("nothing to draw: the netlist has no cell")
    inp = os.path.join(work, "nsvg.json")
    with open(inp, "w") as fh:
        json.dump(netlistsvg_input(name, mod), fh, sort_keys=True)
    out = os.path.join(work, "nsvg.svg")
    run(["node", nsvg, inp, "-o", out, "--skin", SKIN], 600, "netlistsvg")
    with open(out, encoding="utf-8") as fh:
        raw = fh.read()
    cells = {cn: cell_kind(c["type"])[1] for cn, c in mod["cells"].items()}
    return rewrite_svg(raw, cells=cells, crit_cells=crit_cells, crit_bits=crit_bits, title=title), len(cells)


# ---------------------------------------------------------------------------
# one design
# ---------------------------------------------------------------------------

SCORED_KEYS = ("area_e4um2_sky130", "delay_ps_sky130", "cells_sky130", "unit_depth", "cell_hist_sky130", "critical",
               "legality", "repair", "setup", "netlist_sha256", "ppa_version", "ppa_pins_sha256", "liberty_sha256",
               "flops", "sequential")


def scored_block(res):
    p = res["ppa"]
    out = {k: p[k] for k in SCORED_KEYS if k in p}
    out["params"] = res["score"]["params"]
    out["path"] = p["critical_path_timing"]
    return out


def point_words(params):
    return ", ".join(f"{k} = {v}" for k, v in params.items()) or "its one size"


def one_design(task, d, display, *, nsvg, tools, budget_left, log=print):
    """The JSON (and the SVG text or None) of one design."""
    data = {"schema": SCHEMA, "task": task, "sv_sha256": d["sha256"], "tools": tools}
    tj = load_json(os.path.join(TASKS, task, "task.json"))
    data["scored"] = scored_block(run_ppa(d["src"], task))
    params = display["params"]
    with tempfile.TemporaryDirectory(prefix="svgolf-sch-") as work:
        repaired = os.path.join(work, "repaired.v")
        try:
            res = run_ppa(d["src"], task, params, repaired=repaired)
        except GenError as e:
            data["display"] = {"params": params, "drawn": None, "reason": f"does not run at {point_words(params)}: {e}"}
            data["cell_area_e4um2"] = cell_areas(data["scored"]["cell_hist_sky130"])
            return data, None
        p = res["ppa"]
        disp = {"params": params, "area_e4um2_sky130": p["area_e4um2_sky130"], "delay_ps_sky130": p["delay_ps_sky130"],
                "cells_sky130": p["cells_sky130"], "cell_hist_sky130": p["cell_hist_sky130"], "critical": p["critical"],
                "path": p["critical_path_timing"], "repaired_sha256": p["repair"]["netlist_sha256"]}
        piece = display.get("draw") == "critical" or p["cells_sky130"] > display["max_full_cells"]
        name, mod = top_module(yosys_json(repaired, tj["top"], work))
        what = ("the critical path and the nets that touch it" if piece else "the whole repaired netlist")
        title = (f"{task}: schematic of {what} at {point_words(params)} (a display instance; scored at "
                 f"{point_words(data['scored']['params'])})")
        svg, ncells = draw(name, mod, disp["path"], piece=piece, nsvg=nsvg, work=work, title=title)
    size = len(svg.encode("utf-8"))
    if size > budget_left:
        disp.update(drawn=None, reason=f"the drawing ({size:,} bytes) would pass the total size budget of the committed "
                                       "schematics")
        data["display"] = disp
        data["cell_area_e4um2"] = cell_areas(set(data["scored"]["cell_hist_sky130"]) | set(disp["cell_hist_sky130"]))
        return data, None
    disp.update(drawn="critical" if piece else "full", drawn_cells=ncells, svg_bytes=size,
                svg_sha256=sha256_bytes(svg.encode("utf-8")))
    data["display"] = disp
    data["cell_area_e4um2"] = cell_areas(set(data["scored"]["cell_hist_sky130"]) | set(disp["cell_hist_sky130"]))
    return data, svg


def task_dir(task):
    return os.path.join(OUT, task)


def committed_bytes(skip=()):
    total = 0
    for t in sorted(os.listdir(OUT)):
        d = os.path.join(OUT, t)
        if os.path.isdir(d) and t not in ("npm",):
            total += sum(os.path.getsize(os.path.join(d, f)) for f in os.listdir(d)
                         if f.endswith(".svg") and (t, f) not in skip)
    return total


def generate(tasks, nsvg_dir, log=print):
    display = load_json(DISPLAY)
    nsvg = node_tool(nsvg_dir)
    tools = {"netlistsvg": NETLISTSVG, "elkjs": ELKJS, "yosys": yosys_version(),
             "skin_sha256": sha256_bytes(open(SKIN, "rb").read())}
    for task in tasks:
        cfg = dict(display["tasks"][task], max_full_cells=display["max_full_cells"])
        os.makedirs(task_dir(task), exist_ok=True)
        want = set()
        for d in designs(task):
            k = key_of(d["sha256"])
            want |= {f"{k}.json", f"{k}.svg"}
            left = display["max_total_bytes"] - committed_bytes(skip={(task, f"{k}.svg")})
            log(f"{task} {k} ({', '.join(d['names'])}) ...")
            data, svg = one_design(task, d, cfg, nsvg=nsvg, tools=tools, budget_left=left, log=log)
            with open(os.path.join(task_dir(task), f"{k}.json"), "w", encoding="utf-8") as fh:
                fh.write(json_text(data))
            svg_path = os.path.join(task_dir(task), f"{k}.svg")
            if svg is None:
                if os.path.exists(svg_path):
                    os.remove(svg_path)
                log(f"  no drawing: {data['display']['reason']}")
            else:
                with open(svg_path, "w", encoding="utf-8") as fh:
                    fh.write(svg)
                dd = data["display"]
                log(f"  drawn ({dd['drawn']}): {dd['drawn_cells']} cells, {dd['svg_bytes']:,} bytes")
        for f in sorted(os.listdir(task_dir(task))):
            if f.endswith((".json", ".svg")) and f not in want:
                os.remove(os.path.join(task_dir(task), f))
                log(f"  removed {task}/{f} (no such design any more)")


# ---------------------------------------------------------------------------
# --check: the committed files, without any tool
# ---------------------------------------------------------------------------

FORBIDDEN = re.compile(r"/Users/|/home/|/private/|/tmp/|[A-Za-z]:\\\\|Generated by Yosys|<script|\bon[a-z]+=")


def check(tasks):
    """Problems with the committed files: every design of `tasks` has its JSON; a drawn one its SVG with the recorded
    hash; no stray file; no path, banner or script in an SVG; the total under the budget."""
    display = load_json(DISPLAY)
    probs = []
    for task in tasks:
        want = {}
        for d in designs(task):
            want[key_of(d["sha256"])] = d
        have = sorted(os.listdir(task_dir(task))) if os.path.isdir(task_dir(task)) else []
        for f in have:
            if os.path.splitext(f)[0] not in want:
                probs.append(f"{task}/{f}: no design of the task has this key")
        for k, d in sorted(want.items()):
            jp = os.path.join(task_dir(task), f"{k}.json")
            if not os.path.isfile(jp):
                probs.append(f"{task}/{k}.json: missing ({', '.join(d['names'])})")
                continue
            data = load_json(jp)
            if data.get("schema") != SCHEMA or data.get("sv_sha256") != d["sha256"] or data.get("task") != task:
                probs.append(f"{task}/{k}.json: not the schematic data of {d['src']}")
                continue
            if data["display"].get("params") != display["tasks"][task]["params"]:
                probs.append(f"{task}/{k}.json: drawn at {data['display'].get('params')}, display.json says "
                             f"{display['tasks'][task]['params']}")
            sp = os.path.join(task_dir(task), f"{k}.svg")
            if data["display"].get("drawn"):
                if not os.path.isfile(sp):
                    probs.append(f"{task}/{k}.svg: missing")
                    continue
                raw = open(sp, "rb").read()
                if sha256_bytes(raw) != data["display"]["svg_sha256"]:
                    probs.append(f"{task}/{k}.svg: not the drawing its JSON records")
                if FORBIDDEN.search(raw.decode("utf-8")):
                    probs.append(f"{task}/{k}.svg: a path, a tool banner or a script")
            elif os.path.isfile(sp):
                probs.append(f"{task}/{k}.svg: its JSON says it is not drawn")
    total = committed_bytes()
    if total > display["max_total_bytes"]:
        probs.append(f"the committed schematics are {total:,} bytes, over the budget of {display['max_total_bytes']:,}")
    return probs


def main(argv=None):
    ap = argparse.ArgumentParser(description="Generate the record pages' schematics and critical-path data.")
    ap.add_argument("--task", action="append", help="only this task (repeatable; default: every task with a display "
                    "instance in site/schematics/display.json)")
    ap.add_argument("--netlistsvg", default=os.environ.get("SVGOLF_NETLISTSVG"),
                    help="the node_modules directory holding netlistsvg 1.0.2 (default $SVGOLF_NETLISTSVG)")
    ap.add_argument("--check", action="store_true", help="check the committed files only (no tool runs)")
    args = ap.parse_args(argv)
    tasks = args.task or drawn_tasks()
    unknown = sorted(set(tasks) - set(load_json(DISPLAY)["tasks"]))
    if unknown:
        ap.error(f"no display instance in site/schematics/display.json for {unknown}")
    if args.check:
        probs = check(tasks)
        for p in probs:
            print(p, file=sys.stderr)
        print(f"schematics: {'OK' if not probs else f'{len(probs)} problems'} ({committed_bytes():,} bytes of SVG)")
        return 1 if probs else 0
    if not args.netlistsvg:
        ap.error("--netlistsvg DIR (or $SVGOLF_NETLISTSVG) is required to generate")
    if not shutil.which("node"):
        ap.error("node is not on PATH")
    try:
        generate(tasks, os.path.abspath(args.netlistsvg))
    except (GenError, subprocess.TimeoutExpired, OSError) as e:
        print(f"gen_schematics FAILED: {e}", file=sys.stderr)
        return 1
    probs = check(tasks)
    for p in probs:
        print(p, file=sys.stderr)
    return 1 if probs else 0


if __name__ == "__main__":
    sys.exit(main())
