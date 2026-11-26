#!/usr/bin/env python3.12
"""svGolf exploration check: an UNPROVED design of a stream task against the task's oracle, by simulation.

For a task of kind `explore-stream` (tasks/gemm) there is no trusted statement yet, so nothing here is a proof.
What the stage does, for each point of task.json `explore.points` (a point is the top module's parameters):

  build        Verilator compiles the design with the task's environment (tasks/<t>/env/tb.sv: the external
               memory, the activation source, the result sink) and the behavioural models of the SRAM catalogue;
               every register and memory word starts at a random value (`--x-initial unique`, a seed per run).
  results      per seed, a job list from the oracle with random pauses on every channel: every result beat
               exactly once with the reference's data, every request inside the job's image, no valid or payload
               dropped before its transfer, no read and write of one SRAM block in a cycle (oracle `check_trace`).
               A job list may be the oracle's `sweep`: one job per shift 0..63 of the output stage.
  independence the same run again on OTHER weights and activations, of another KIND for every job (the same jobs'
               sizes and layer parameters, the same pauses, the same power-up seed): the request stream, every
               valid and ready the design drives and the result positions must be equal cycle for cycle (oracle
               `control_trace`).
  cycles       identical jobs back to back at nominal timing (no pause, first beat exactly LAT cycles after the
               request): the cycles between consecutive jobs' last result beats must be steady and equal the
               entry's declared formula (`cycles`, in n, batch, e, lat), which the score evaluates at the scored
               job.
  scored job   at the point marked `scored_job` (the scored parameters): the SCORED JOB itself, twice back to back
               at nominal timing, with identity weights (the reference's sums are then the activations, so the
               job of 4096 x 4096 x 4096 can be judged): every result right, and the cycles from the first job's
               last result beat to the second's equal to the declared formula at the scored job. The score's
               cycle count is therefore a measured one, for these weights.
A point may name its own job lists (`shapes`, `cycle_shapes`): the point at the SCORED parameters runs the design
text as it is scored (16,384 cells in the plain array) on short jobs up to the largest layer, and the scored job.
  netlist      at the points marked `netlist`, the same `results` runs on the gate netlist the pinned passes
               write with the hierarchy kept, as for the score (SRAM blocks as their models): the scored cells'
               flow, not the source.

The declaration (`--declare FILE`, JSON): {"cycles": "<formula>", "layout": null | {...}}; the layout is the
oracle's (`check_layout`). A formula uses the names n, batch, e, lat, integers, + - * // %, parentheses, and
min(...), max(...), ceil_div(a, b).

    python3.12 check/explore.py tasks/gemm design.sv --declare design.json [--work DIR] [--no-scored-job]

Exit status 0: every check passed; 1: a check failed; 3: infrastructure. The result JSON goes to stdout.
"""
import argparse
import ast
import hashlib
import importlib.util
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(HERE)
for _p in (HERE, os.path.join(SVGOLF, "score")):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import postsynth  # noqa: E402
import sandbox  # noqa: E402

KIND = "explore-stream"
SRAM_TABLE = os.path.join(SVGOLF, "score", "sram_asap7.json")
TB_TOP = "gemm_tb"
SALT_ENV = "SVGOLF_POSTSYNTH_SALT"

MAIN_CPP = r"""
#include "VEXP.h"
#include "verilated.h"
int main(int argc, char** argv) {
  VerilatedContext* ctx = new VerilatedContext;
  ctx->commandArgs(argc, argv);
  VEXP* top = new VEXP{ctx};
  top->clk = 0;
  while (!ctx->gotFinish()) {
    top->clk = !top->clk;
    top->eval();
    ctx->timeInc(1);
  }
  top->final();
  delete top;
  delete ctx;
  return 0;
}
"""


class Reject(Exception):
    def __init__(self, msg, record=None):
        super().__init__(msg)
        self.msg, self.record = msg, record


class InfraError(Exception):
    pass


# ---------------------------------------------------------------------------------------- the SRAM catalogue
def sram_table(path=SRAM_TABLE):
    with open(path) as fh:
        return json.load(fh)


def sram_names(table=None):
    return [b["name"] for b in (table or sram_table())["blocks"]]


def sram_models(kind="sim", table=None):
    """The catalogue blocks as SystemVerilog modules. `sim`: the behavioural model (one port; a write stores,
    else a read latches the word on dataout; a read and a write in one cycle print a rule violation). `blackbox`:
    the ports only, for the synthesis runs, where a block stays an instance."""
    out = ["// The open ASAP7 SRAM catalogue (score/sram_asap7.json), "
           + ("behavioural models for simulation." if kind == "sim" else "ports only: a block stays an instance.")
           + "\n// Generated (check/explore.py `sram_models`); do not edit.\n"]
    for b in (table or sram_table())["blocks"]:
        ports = (f"  input  logic clk,\n  input  logic [{b['addr_bits'] - 1}:0] ADDRESS,\n"
                 f"  input  logic [{b['width'] - 1}:0] wd,\n  input  logic banksel, read, write,\n"
                 f"  output logic [{b['width'] - 1}:0] dataout\n")
        if kind == "blackbox":
            out.append(f"(* blackbox *)\nmodule {b['name']} (\n{ports});\nendmodule\n")
            continue
        out.append(
            f"module {b['name']} (\n{ports});\n"
            f"  logic [{b['width'] - 1}:0] mem [0:{b['words'] - 1}];\n"
            "  always @(posedge clk)\n"
            "    if (banksel) begin\n"
            "      if (read & write) $display(\"SRAM-RULE read and write in one cycle: %m\");\n"
            "      if (write) mem[ADDRESS] <= wd;\n"
            "      else if (read) dataout <= mem[ADDRESS];\n"
            "    end\n"
            "endmodule\n")
    return "\n".join(out)


# ------------------------------------------------------------------------------------------- the declaration
ALLOWED_NAMES = ("n", "batch", "e", "lat")


def _formula_fn(text):
    """The cycle formula as a function of (n, batch, e, lat). Raises ValueError on anything outside the grammar."""
    if not isinstance(text, str) or len(text) > 2000:
        raise ValueError("the cycle formula is a string of at most 2000 characters")
    tree = ast.parse(text, mode="eval")

    def ev(node, env):
        if isinstance(node, ast.Expression):
            return ev(node.body, env)
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            return node.value
        if isinstance(node, ast.Name) and node.id in ALLOWED_NAMES:
            return env[node.id]
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod)):
            a, b = ev(node.left, env), ev(node.right, env)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if b == 0:
                raise ValueError("division by zero in the cycle formula")
            return a // b if isinstance(node.op, ast.FloorDiv) else a % b
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -ev(node.operand, env)
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords
                and node.func.id in ("min", "max", "ceil_div")):
            args = [ev(a, env) for a in node.args]
            if node.func.id == "ceil_div":
                if len(args) != 2 or args[1] == 0:
                    raise ValueError("ceil_div(a, b) takes two arguments, b nonzero")
                return -(-args[0] // args[1])
            if len(args) < 2:
                raise ValueError(f"{node.func.id}(...) takes at least two arguments")
            return (min if node.func.id == "min" else max)(args)
        raise ValueError("the cycle formula uses the names n, batch, e, lat, integers, + - * // %, parentheses, "
                         "min(...), max(...) and ceil_div(a, b); not `" + ast.unparse(node)[:60] + "`")
    ev(tree, dict.fromkeys(ALLOWED_NAMES, 8))       # every node is checked once, before any use
    return lambda n, batch, e, lat: ev(tree, {"n": n, "batch": batch, "e": e, "lat": lat})


def load_declare(path, oracle):
    """The entry's declaration: (dict, None) or (None, why)."""
    if path is None:
        return {"cycles": None, "layout": None}, None
    try:
        with open(path) as fh:
            d = json.load(fh)
    except (OSError, ValueError) as e:
        return None, f"cannot read the declaration {os.path.basename(path)}: {e}"
    if not isinstance(d, dict) or set(d) - {"cycles", "layout", "note"}:
        return None, "the declaration is an object with the keys cycles, layout (and note)"
    if d.get("layout") is not None:
        why = oracle.check_layout(d["layout"])
        if why:
            return None, f"the declared layout: {why}"
    if d.get("cycles") is not None:
        try:
            _formula_fn(d["cycles"])
        except (ValueError, SyntaxError) as e:
            return None, f"the declared cycle formula: {e}"
    return {"cycles": d.get("cycles"), "layout": d.get("layout")}, None


def width_at(expr, params):
    """A port width of task.json at `params`: integers, the parameters' names, + - * //, parentheses and 2**x."""
    def ev(n):
        if isinstance(n, ast.Expression):
            return ev(n.body)
        if isinstance(n, ast.Constant) and isinstance(n.value, int) and not isinstance(n.value, bool):
            return n.value
        if isinstance(n, ast.Name) and n.id in params:
            return int(params[n.id])
        if isinstance(n, ast.BinOp) and isinstance(n.op, (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv)):
            a, b = ev(n.left), ev(n.right)
            return a + b if isinstance(n.op, ast.Add) else a - b if isinstance(n.op, ast.Sub) else \
                a * b if isinstance(n.op, ast.Mult) else a // b
        if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Pow) and ev(n.left) == 2 and 0 <= ev(n.right) <= 24:
            return 1 << ev(n.right)
        raise InfraError(f"task.json `ports`: the width {expr!r} is not an expression of the parameters")
    return ev(ast.parse(str(expr), mode="eval"))


def cycles_at(declare, point, lgn, batch):
    return _formula_fn(declare["cycles"])(1 << lgn, batch, 1 << point["LGE"], point["LAT"])


# ---------------------------------------------------------------------------------------------- the stimulus
def _hex(v, bits):
    return f"{v:0{(bits + 3) // 4}x}"


def write_stimulus(d, point, job_list, layout, stall_words, oracle, depth=None):
    """The files env/tb.sv reads, in directory `d`. Returns (images, result beats, memory beats, activation beats).
    Consecutive jobs on the SAME weights (one object) share one image in the memory file. `depth`: the
    environment's (memory beats, activation beats) at this point; a job list that needs more is the task's fault
    (task.json `mem_beats`, `x_beats`), said in words instead of a simulator abort."""
    lge = point["LGE"]
    memw = 16 << lge
    images, bases, stored, base = [], [], [], 0
    for k, j in enumerate(job_list):
        if k and j["W"] is job_list[k - 1]["W"] and j["lgn"] == job_list[k - 1]["lgn"]:
            images.append(images[-1])
            bases.append(bases[-1])
            continue
        images.append(oracle.image(j["W"], j["lgn"], lge, layout))
        bases.append(base)
        stored.append(images[-1])
        base += len(images[-1])
    xs = [oracle.x_beats(j, lge) for j in job_list]
    os.makedirs(d, exist_ok=True)
    with open(os.path.join(d, "jobs.hex"), "w") as fh:
        for j, img, x, at in zip(job_list, images, xs, bases):
            word = (j["lgn"] | j["batch"] << 8 | j["mul"] << 24 | j["shift"] << 40 | j["zp"] << 48 | j["lo"] << 64
                    | j["hi"] << 80 | at << 96 | len(img) << 128 | len(x) << 160)
            fh.write(_hex(word, 192) + "\n")
    with open(os.path.join(d, "mem.hex"), "w") as fh:
        for img in stored:
            fh.writelines(_hex(b, memw) + "\n" for b in img)
    with open(os.path.join(d, "x.hex"), "w") as fh:
        for x in xs:
            fh.writelines(_hex(b, memw) + "\n" for b in x)
    with open(os.path.join(d, "stall.hex"), "w") as fh:
        fh.writelines(_hex(w, 8) + "\n" for w in stall_words)
    nyb = sum(j["batch"] << (j["lgn"] - lge) for j in job_list)
    nx = sum(len(x) for x in xs)
    if depth is not None and (base > depth[0] or nx > depth[1]):
        raise InfraError(f"a job list needs {base} memory beats and {nx} activation beats under this layout; the "
                         f"environment at {point_text(point)} holds {depth[0]} and {depth[1]} (task.json `explore`: "
                         "`mem_beats`, `x_beats`)")
    return images, nyb, base, nx


# ------------------------------------------------------------------------------------------------ simulation
def build(work, tag, point, sources, tb, depth, timeout=900, netlist=False):
    """Compile the environment `tb` around `sources` at `point` into one executable. A Verilator diagnostic is
    about the design: (None, text). A failure of the C++ build raises InfraError. Returns (exe, None)."""
    vl = postsynth.verilator_info()[0]
    cxx = postsynth.cxx_path()
    make = postsynth.tool("make")
    d = os.path.join(work, f"{tag}_vl")
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    main = os.path.join(d, "main.cpp")
    with open(main, "w") as fh:
        fh.write(MAIN_CPP)
    obj = os.path.join(d, "obj")
    cmd = ([vl, "--cc", "--exe", "--prefix", "VEXP", "--top-module", TB_TOP, "--Mdir", obj, "--no-timing",
            "-CFLAGS", "-O1", "--x-assign", "unique", "--x-initial", "unique",
            "-Wno-fatal", "-Wno-lint", "-Wno-style", "-Wno-DECLFILENAME", "-Wno-UNOPTFLAT", "-Wno-MULTIDRIVEN"]
           + (["+define+GEMM_NETLIST"] if netlist else [])
           + [f"-G{k}={v}" for k, v in sorted(point.items())]
           + [f"-GMEMBEATS={depth[0]}", f"-GXBEATS={depth[1]}", f"-GMAXSTALL={depth[2]}", main, os.path.abspath(tb)]
           + [os.path.abspath(s) for s in sources])
    env = postsynth.vl_env()
    env["CXX"] = cxx
    vspec = mspec = None
    if sandbox.policy().active:
        env = sandbox.tool_env(d, {"OBJCACHE": "", "LC_ALL": "C", "CXX": cxx})
        reads = [os.path.abspath(s) for s in sources] + [os.path.abspath(tb), d]
        vspec = sandbox.tool_spec([vl], read=reads, write=[d], label="verilator")
        mspec = sandbox.tool_spec([make, cxx], read=[d], write=[d], label="make (C++ build)")
    try:
        c = postsynth.run_group(cmd, timeout, spec=vspec, label="verilator", env=env, cwd=d)
        if c.returncode != 0:
            return None, "verilator rejected it: " + postsynth.error_lines(c.stderr + c.stdout)
        m = postsynth.run_group([make, "-C", obj, "-f", "VEXP.mk", "-j", postsynth.VL_JOBS, "VEXP"], timeout,
                                spec=mspec, label="make (C++ build)", env=env)
    except subprocess.TimeoutExpired:
        raise InfraError(f"building the simulation model did not finish within {timeout:.0f} s")
    exe = os.path.join(obj, "VEXP")
    if m.returncode != 0 or not os.path.isfile(exe):
        raise InfraError("the C++ build of the simulation model failed (toolchain, not design): "
                         + postsynth.error_lines(m.stderr + m.stdout))
    return exe, None


def run_model(exe, d, njobs, nstall, nybeats, maxcyc, seed, oracle, timeout=900):
    """Run the model on the stimulus in `d`: (events, SRAM rule violations)."""
    cmd = [exe, f"+dir={d}", f"+njobs={njobs}", f"+nstall={nstall}", f"+nybeats={nybeats}", f"+maxcyc={maxcyc}",
           "+verilator+rand+reset+2", f"+verilator+seed+{seed % 2147483646 + 1}"]
    spec = None
    env = {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}
    if sandbox.policy().active:
        spec = sandbox.exec_spec(exe, read=[d], write=[d], label="model")
    try:
        r = postsynth.run_group(cmd, timeout, spec=spec, label="model", env=env, cwd=d)
    except subprocess.TimeoutExpired:
        raise Reject(f"the simulation did not finish within {timeout:.0f} s")
    postsynth.loader_failure(r)
    trace = os.path.join(d, "trace.txt")
    if r.returncode != 0 or not os.path.isfile(trace):
        raise InfraError(f"the simulation model failed (exit {r.returncode}): " + (r.stderr or r.stdout)[-600:])
    with open(trace) as fh:
        events = oracle.parse_trace(fh.read())
    rules = sorted({ln.strip() for ln in r.stdout.splitlines() if ln.startswith("SRAM-RULE")})
    return events, rules


def seed_rng(task, point, seed, what, salt=None):
    """A random source for one purpose of one seed's run, derived from sha256(salt, task, point, seed, purpose)."""
    salt = os.environ.get(SALT_ENV, "") if salt is None else salt
    text = "\0".join([salt, task, json.dumps(point, sort_keys=True), str(seed), what])
    return random.Random(int.from_bytes(hashlib.sha256(text.encode()).digest(), "big"))


def max_cycles(job_list, point, cfg):
    """A generous bound on a run's length (a design slower than this times out); the environment counts cycles in a
    32-bit integer."""
    work = sum((j["batch"] + 4) * (1 << 2 * (j["lgn"] - point["LGE"])) for j in job_list)
    return min(int(cfg.get("slack", 200)) * (work + 64) * (point["LAT"] + (1 << point["LGE"]) + 8), (1 << 31) - 1)


def shape_of(entry):
    """A job list of task.json: the oracle's word for one (`sweep`), or [scale, batch] / [scale, batch, shift] rows."""
    return entry if isinstance(entry, str) else [tuple(s) for s in entry]


def results_runs(task, point, exe, oracle, declare, cfg, work, tag, seeds, independence=True, shapes=None):
    """The `results` and `independence` checks of one build: a record, or Reject. `shapes`: the point's own job
    lists (None: the task's)."""
    name = task["name"]
    rec = {"seeds": [], "independence": independence}
    shapes = shapes or cfg["shapes"]
    for seed in seeds:
        shape = shape_of(shapes[seed % len(shapes)])
        ctl = lambda: seed_rng(name, point, seed, "ctl")                               # noqa: E731
        job_list = oracle.jobs(point, seed, shape, ctl(), seed_rng(name, point, seed, "data"))
        st = oracle.stalls(seed, cfg.get("stall_words", 4096), seed_rng(name, point, seed, "stall"))
        d = os.path.join(work, f"{tag}_s{seed}")
        images, nyb, _, _ = write_stimulus(d, point, job_list, declare["layout"], st, oracle, cfg.get("_depth"))
        maxc = max_cycles(job_list, point, cfg)
        puseed = seed_rng(name, point, seed, "powerup").getrandbits(30)
        events, rules = run_model(exe, d, len(job_list), len(st), nyb, maxc, puseed, oracle)
        bad = oracle.check_trace(point, job_list, images, events) + rules
        srec = {"seed": seed, "jobs": [j["tag"] for j in job_list], "cycles": events[-1][1] if events else 0,
                "result_beats": nyb}
        rec["seeds"].append(srec)
        if bad:
            tags = srec["jobs"]
            said = "jobs " + ", ".join(tags) if len(tags) <= 6 else f"{len(tags)} jobs, {tags[0]} to {tags[-1]}"
            raise Reject(f"{tag}, seed {seed} ({said}): " + "; ".join(bad[:4])
                         + (f" (and {len(bad) - 4} more)" if len(bad) > 4 else ""), rec)
        if independence:
            other = oracle.jobs(point, seed, shape, ctl(), seed_rng(name, point, seed, "data2"), data_shift=1)
            d2 = os.path.join(work, f"{tag}_s{seed}_b")
            images2, _, _, _ = write_stimulus(d2, point, other, declare["layout"], st, oracle, cfg.get("_depth"))
            ev2, rules2 = run_model(exe, d2, len(other), len(st), nyb, maxc, puseed, oracle)
            bad2 = oracle.check_trace(point, other, images2, ev2) + rules2
            if bad2:
                raise Reject(f"{tag}, seed {seed}, the second data set: " + "; ".join(bad2[:4]), rec)
            a, b = oracle.control_trace(events), oracle.control_trace(ev2)
            if a != b:
                k = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
                raise Reject(f"{tag}, seed {seed}: the schedule depends on the data: two runs that differ only in "
                             f"weights and activations part at cycle {(a + b)[k][1] if a or b else 0} "
                             f"({' '.join(map(str, a[k])) if k < len(a) else 'end'} against "
                             f"{' '.join(map(str, b[k])) if k < len(b) else 'end'})", rec)
    return rec


def cycles_runs(task, point, exe, oracle, declare, cfg, work, tag, shapes=None):
    """The `cycles` check of one build: identical jobs back to back at nominal timing. `shapes`: the point's own
    [scale, batch] list (None: the task's)."""
    name = task["name"]
    out = []
    for k, (q, batch) in enumerate(shapes or cfg["cycle_shapes"]):
        shape = [(q, batch)] * 4
        job_list = oracle.jobs(point, 1000 + k, shape, seed_rng(name, point, k, "cyc-ctl"),
                               seed_rng(name, point, k, "cyc-data"))
        for j in job_list[1:]:                                       # identical jobs: the first one's parameters
            for f in oracle.JOB_FIELDS:
                j[f] = job_list[0][f]
        st = oracle.stalls(0, 16, nominal=True)
        d = os.path.join(work, f"{tag}_c{k}")
        images, nyb, _, _ = write_stimulus(d, point, job_list, declare["layout"], st, oracle, cfg.get("_depth"))
        events, rules = run_model(exe, d, len(job_list), len(st), nyb, max_cycles(job_list, point, cfg), 7 + k,
                                  oracle)
        bad = oracle.check_trace(point, job_list, images, events) + rules
        if bad:
            raise Reject(f"{tag}, nominal timing, 4 jobs of N = E*{1 << q}, batch {batch}: " + "; ".join(bad[:4]))
        per = oracle.job_period(events, job_list, point["LGE"])
        row = {"lgn": point["LGE"] + q, "batch": batch, "measured": per}
        if len(per) != 3 or per[1] != per[2]:
            raise Reject(f"{tag}: the cycles per job are not steady at N = E*{1 << q}, batch {batch}: consecutive "
                         f"jobs' last result beats are {per} cycles apart")
        if declare.get("cycles") is not None:
            row["declared"] = cycles_at(declare, point, point["LGE"] + q, batch)
            if row["declared"] != per[2]:
                raise Reject(f"{tag}: the declared cycle formula gives {row['declared']} at N = {1 << row['lgn']}, "
                             f"batch {batch}, E = {1 << point['LGE']}, LAT = {point['LAT']}; the simulation measures "
                             f"{per[2]}")
        out.append(row)
    return out


def scored_job_run(task, point, exe, oracle, declare, cfg, work, tag, job=None, timeout=5400):
    """The SCORED JOB itself (task.json `scoring.job`; `job` overrides it in tests), twice back to back at nominal
    timing, with identity weights and random activations: every result right, and the cycles from the first job's
    last result beat to the second's equal to the declared formula there. Identity weights make the reference
    cheap (the sums are the activations), so the job the score is about is run, not extrapolated; what the run does
    not show is the arithmetic on dense weights at this size (the other runs show it on smaller jobs)."""
    name = task["name"]
    job = job or task["scoring"]["job"]
    q, batch = job["lgn"] - point["LGE"], job["batch"]
    first = oracle.jobs(point, 0, [(q, batch, 15)], seed_rng(name, point, 0, "scored-ctl"),
                        seed_rng(name, point, 0, "scored-data"))[0]
    if first["tag"].split("-")[0] != "identity":
        raise InfraError("the oracle's job at shift 15 is not an identity job (the scored-job run needs one)")
    job_list = [first, dict(first)]                                  # the same job again: the same weights and vectors
    st = oracle.stalls(0, 16, nominal=True)
    d = os.path.join(work, f"{tag}_scored")
    images, nyb, _, _ = write_stimulus(d, point, job_list, declare["layout"], st, oracle, cfg.get("_depth"))
    declared = cycles_at(declare, point, job["lgn"], batch) if declare.get("cycles") is not None else None
    # two jobs take about twice the declared count; a run that is not done after two and a half times it has failed
    maxc = min(2 * declared + declared // 2 + 100000, (1 << 31) - 1) if declared else max_cycles(job_list, point, cfg)
    events, rules = run_model(exe, d, len(job_list), len(st), nyb, maxc, 11, oracle, timeout=timeout)
    bad = oracle.check_trace(point, job_list, images, events) + rules
    if bad:
        raise Reject(f"{tag}, the scored job (N = {1 << job['lgn']}, batch {batch}, identity weights, nominal timing), "
                     "twice: " + "; ".join(bad[:4]))
    per = oracle.job_period(events, job_list, point["LGE"])
    row = {"lgn": job["lgn"], "batch": batch, "weights": "identity", "measured": per,
           "run_cycles": events[-1][1] if events else 0}
    if len(per) != 1:
        raise Reject(f"{tag}: the scored job's cycles could not be measured (two jobs, {len(per)} intervals)")
    if declared is not None:
        row["declared"] = declared
        if declared != per[0]:
            raise Reject(f"{tag}: the declared cycle formula gives {declared} at the scored job (N = {1 << job['lgn']}, "
                         f"batch {batch}, E = {1 << point['LGE']}, LAT = {point['LAT']}); the simulation of that job "
                         f"measures {per[0]}")
    return row


def point_text(point):
    return ",".join(f"{k}={v}" for k, v in sorted(point.items()))


def config(task):
    cfg = task.get("explore")
    if not isinstance(cfg, dict) or not cfg.get("points"):
        raise InfraError("task.json `explore` names no points")
    return cfg


def load_oracle(task_dir, task):
    path = os.path.join(task_dir, task.get("oracle") or "oracle.py")
    spec = importlib.util.spec_from_file_location(f"svgolf_explore_oracle_{task['name']}", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(task_dir, task, sv, declare, work, netlists=None, log=lambda *a: None, scored_job=True):
    """Every simulation check of the design `sv` (the canonical text) under `declare`. `scored_job` False leaves out
    the run of the scored job (minutes; it belongs to the score: check.py --no-score), and the record says so.

    `netlists`: {point text: path of the netlist the pinned passes wrote at that point} for the points marked
    `netlist` (None: the netlist runs are skipped, and the record says so). Returns the record; raises Reject
    (the design's fault) or InfraError."""
    cfg = config(task)
    oracle = load_oracle(task_dir, task)
    tb = os.path.join(task_dir, cfg.get("env", "env/tb.sv"))
    sram = os.path.join(work, "sram_models.sv")
    with open(sram, "w") as fh:
        fh.write(sram_models("sim"))
    rec = {"points": [], "verilator": postsynth.verilator_info()[1]}
    for k, pt in enumerate(cfg["points"]):
        point = dict(pt["params"])
        tag = f"p{k}"
        t0 = time.time()
        log(f"explore: {point_text(point)}: build")
        depth = (int(pt.get("mem_beats", cfg.get("mem_beats", 1 << 18))),          # a point may need a deeper memory
                 int(pt.get("x_beats", cfg.get("x_beats", 1 << 16))), int(cfg.get("stall_words", 4096)))
        cfg = dict(cfg, _depth=depth[:2])
        exe, why = build(work, tag, point, [sv, sram], tb, depth)
        if exe is None:
            raise Reject(f"at {point_text(point)}: {why}", rec)
        prec = {"params": point, "build_seconds": round(time.time() - t0, 1)}
        rec["points"].append(prec)
        seeds = list(range(int(pt.get("seeds", cfg.get("seeds", 4)))))
        try:
            prec["results"] = results_runs(task, point, exe, oracle, declare, cfg, work, tag, seeds,
                                           shapes=pt.get("shapes"))
            prec["cycles"] = cycles_runs(task, point, exe, oracle, declare, cfg, work, tag, pt.get("cycle_shapes"))
            if pt.get("scored_job") and not scored_job:
                prec["scored_job"] = {"skipped": "the scored job's run comes with the score"}
            elif pt.get("scored_job"):
                log(f"explore: {point_text(point)}: the scored job, twice (minutes)")
                prec["scored_job"] = scored_job_run(task, point, exe, oracle, declare, cfg, work, tag,
                                                    pt["scored_job"] if isinstance(pt["scored_job"], dict) else None)
        except Reject as r:
            raise Reject(f"at {point_text(point)}: {r.msg}", rec)
        if pt.get("netlist"):
            nl = (netlists or {}).get(point_text(point))
            if nl is None:
                prec["netlist"] = {"skipped": "no netlist was given (the score stage makes it)"}
            else:
                t1 = time.time()
                log(f"explore: {point_text(point)}: the netlist")
                nexe, why = build(work, tag + "n", point, [nl, postsynth.simcells(), sram], tb, depth, timeout=1800,
                                  netlist=True)
                if nexe is None:
                    raise InfraError(f"the scored netlist at {point_text(point)} does not compile: {why}")
                nseeds = seeds[:int(pt.get("netlist_seeds", 2))]
                try:
                    prec["netlist"] = results_runs(task, point, nexe, oracle, declare, cfg, work, tag + "n", nseeds,
                                                   independence=False, shapes=pt.get("shapes"))
                except Reject as r:
                    raise Reject(f"the scored netlist at {point_text(point)}: {r.msg}", rec)
                prec["netlist"]["build_seconds"] = round(time.time() - t1, 1)
        prec["seconds"] = round(time.time() - t0, 1)
        log(f"explore: {point_text(point)}: ok [{prec['seconds']} s]")
    return rec


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("task_dir")
    ap.add_argument("design")
    ap.add_argument("--declare")
    ap.add_argument("--work")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--no-scored-job", action="store_true", help="leave out the run of the scored job (minutes)")
    args = ap.parse_args(argv)
    with open(os.path.join(args.task_dir, "task.json")) as fh:
        task = json.load(fh)
    oracle = load_oracle(args.task_dir, task)
    declare, why = load_declare(args.declare, oracle)
    if declare is None:
        print(json.dumps({"ok": False, "error": why}, indent=2))
        return 1
    work = os.path.abspath(args.work) if args.work else tempfile.mkdtemp(prefix="svgolf-explore-")
    os.makedirs(work, exist_ok=True)
    try:
        rec = run(args.task_dir, task, args.design, declare, work, log=lambda *a: print(*a, file=sys.stderr, flush=True),
                  scored_job=not args.no_scored_job)
        print(json.dumps({"ok": True, "explore": rec}, indent=2))
        return 0
    except Reject as r:
        print(json.dumps({"ok": False, "error": r.msg, "explore": r.record}, indent=2))
        return 1
    except (InfraError, postsynth.InfraError) as e:
        print(json.dumps({"ok": False, "infrastructure": str(e)}, indent=2))
        return 3
    finally:
        if not (args.keep or args.work):
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
