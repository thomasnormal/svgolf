#!/usr/bin/env python3.12
"""The arbiter's mutation sweep: every generated mutant of the reference, killed by the task's checks, proved
equivalent to the reference, or a survivor (a finding).

    python3.12 tests/arbiter/mutants/classify.py gen    --work DIR
    python3.12 tests/arbiter/mutants/classify.py sim    --work DIR [--jobs J] [--cycles C]
    python3.12 tests/arbiter/mutants/classify.py formal --work DIR [--jobs J] [--timeout S]
    python3.12 tests/arbiter/mutants/classify.py check  --work DIR [--jobs J]
    python3.12 tests/arbiter/mutants/classify.py point  --work DIR [--jobs J]
    python3.12 tests/arbiter/mutants/classify.py merge  --work DIR [--out tests/arbiter/mutants/MANIFEST.json]
    python3.12 tests/arbiter/mutants/classify.py replay --work DIR ID N     (a counterexample, by Icarus)

Each step writes DIR/<step>/<id>.json and skips what is there (rerun a step by deleting its directory).

* `gen`: `tests/mutate.py` on `tasks/arbiter/reference/rr_mask.sv`, elaborated by pyslang at N = 1, 2, 3, 4,
  5, 8, the reset port `rst`.
* `sim`: the simulation statement, `tests/arbiter/sim.py`'s `run` (Icarus, `tb.sv`) at N = 1, 2, 3, 4, 5, 8,
  its stimulus modes (`sim.MODES`: four since 2026-11-07, sparse requests among them), each from a 0/1 power-up
  state (`sim.powerup`, 2026-11-07), `--cycles` (20000, sim.py's default): the checks that fire, per N.
* `check`: `check.py tasks/arbiter <mutant> --unproved --postsynth full --ppa off` (every stage that needs no
  proof): the stage that rejects, its first error line, and for `postsynth` the point it failed at. It runs
  Lean (the `trusted` and `design` stages): run it where the svGolf build is.
* `point`: the reactive post-synthesis check alone (`check/postsynth.py --point N=n --mode full`, the check
  check.py runs at N = 3, 5, 8 and stops at the first point that fails) at EVERY N of 1, 2, 3, 4, 5, 8: what
  the task's oracle sees at that N by itself. Informative (check.py's verdict is the family's); it needs
  the `svgolf-eval` build, not Lean.
* `formal`: at N = 1, 2, 3, 4, 8 (Yosys `read_verilog -sv; proc; flatten; setundef -undriven -anyconst;
  techmap; aigmap; write_aiger -zinit`, then ABC):
  - EQUIVALENCE with the reference: a miter of the two designs on one clock and the same `rst`/`req`, every
    flip-flop of both powering up FREE (`write_aiger -zinit`: an input gives each uninitialized flop its
    power-up value; an undriven variable is an `$anyconst`, txtask-v2's rule 2), a monitor bit `seen`
    (power-up 0, set by the first edge that samples `rst` = 1), and the bad state `seen && gnt_ref !=
    gnt_mut`: the outputs agree at every snapshot from the first reset entry on, under every later input
    (resets included). Proved UNBOUNDED by ABC `pdr` (IC3), confirmed by ABC `int` (interpolation); a
    falsification is ABC's counterexample (checked by ABC).
  - THE GUARANTEE G0 to G4 on the mutant alone, from every power-up state: the same flow with a monitor that
    registers the entry's `rst` and `req` beside the snapshot and counts each client's consecutive misses
    in the segment (oracle.py's counter), bad = G0 (a reset snapshot with a grant) or G1/G2/G3 (a snapshot
    of a released segment) or G4 (N misses in a row). Proved by `pdr` and `int`, or falsified (`replay`
    re-runs the counterexample on the RTL with Icarus and reads it with oracle.py).
  - the INTERFACE (pyslang: the ports and widths at N) and the OUTPUT DISCIPLINE (no comb process or
    continuous assignment writes `gnt`).
* `merge`: per mutant and per N in 1, 2, 3, 4, 8 the verdict KILLED (the simulation fired at N, or check.py
  rejected the design: a submission is the whole family), else EQUIVALENT (proved at N), else SURVIVOR,
  with the guarantee's verdict at N (CORRECT: proved; WRONG: falsified) beside it.
"""
import argparse, concurrent.futures as cf, glob, json, os, random, re, shutil, subprocess, sys, tempfile, time

sys.dont_write_bytecode = True       # it imports tasks/arbiter/oracle.py: no __pycache__ in the task directory

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.normpath(os.path.join(HERE, "..", "..", ".."))
TASK = os.path.join(SVGOLF, "tasks", "arbiter")
REF = os.path.join(TASK, "reference", "rr_mask.sv")
sys.path.insert(0, os.path.join(SVGOLF, "tests"))
sys.path.insert(0, os.path.join(SVGOLF, "tests", "arbiter"))
sys.path.insert(0, TASK)
import mutate  # noqa: E402
import sim  # noqa: E402  (tests/arbiter/sim.py: tb.sv's runner and its MODES)

GEN_POINTS = [1, 2, 3, 4, 5, 8]
SIM_POINTS = [1, 2, 3, 4, 5, 8]
FORMAL_POINTS = [1, 2, 3, 4, 8]
REPORT_POINTS = [1, 2, 3, 4, 8]
YOSYS = os.environ.get("YOSYS", "yosys")
ABC = os.environ.get("YOSYS_ABC", "yosys-abc")


def jdump(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(obj, fh, indent=1)
    os.replace(tmp, path)


def jload(path):
    with open(path) as fh:
        return json.load(fh)


def mutants(work):
    man = jload(os.path.join(work, "gen", "mutants.json"))
    return man, [r for r in man["mutants"] if r["file"]]


def mpath(work, mid):
    return os.path.join(work, "gen", f"{mid}.sv")


# ---------------------------------------------------------------- gen

def step_gen(a):
    with open(REF) as fh:
        text = fh.read()
    recs, texts = mutate.generate(text, [{"N": n} for n in GEN_POINTS], reset="rst")
    out = os.path.join(a.work, "gen")
    os.makedirs(out, exist_ok=True)
    for mid, t in texts.items():
        with open(os.path.join(out, f"{mid}.sv"), "w") as fh:
            fh.write(t)
    import hashlib, pyslang
    man = {"source": "tasks/arbiter/reference/rr_mask.sv", "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
           "pyslang": getattr(pyslang, "__version__", None), "points": [{"N": n} for n in GEN_POINTS], "reset": "rst",
           "generated": len(recs), "duplicates": sum(1 for r in recs if r["dup_of"]),
           "not_elaborating": sum(1 for r in recs if r["elaborates"] is False), "kept": len(texts), "mutants": recs}
    jdump(os.path.join(out, "mutants.json"), man)
    print(f"{len(recs)} generated, {man['duplicates']} duplicates, {man['not_elaborating']} do not elaborate, "
          f"{len(texts)} kept")


# ---------------------------------------------------------------- sim

def sim_one(work, mid, cycles):
    import sim
    res = {"id": mid, "cycles": cycles, "points": {}}
    with tempfile.TemporaryDirectory(prefix=f"msim-{mid}-") as w:
        for n in SIM_POINTS:
            fired, worst, err = set(), 0, None
            for mode in sim.MODES:
                r, e = sim.run([mpath(work, mid)], [], n, mode, cycles, w)
                if r is None:
                    err = e
                    break
                fired |= {c for c in sim.CHECKS if r[c] > 0}
                worst = max(worst, r["maxmiss"])
            res["points"][str(n)] = {"fired": sorted(fired), "maxmiss": worst, "error": err}
    return res


def step_sim(a):
    _, ms = mutants(a.work)
    todo = [r["id"] for r in ms if not os.path.isfile(os.path.join(a.work, "sim", f"{r['id']}.json"))]
    with cf.ProcessPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(sim_one, a.work, mid, a.cycles): mid for mid in todo}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "sim", f"{r['id']}.json"), r)
            print(r["id"], " ".join(f"N{n}:{'+'.join(p['fired']) or '-'}" + ("!ERR" if p["error"] else "")
                                    for n, p in r["points"].items()), flush=True)


# ---------------------------------------------------------------- check.py

def check_one(work, mid, extra):
    t0 = time.time()
    proc = subprocess.run([sys.executable, os.path.join(SVGOLF, "check.py"), TASK, mpath(work, mid), "--unproved",
                           "--postsynth", "full", "--ppa", "off"] + extra, capture_output=True, text=True,
                          cwd=SVGOLF)
    try:
        res = json.loads(proc.stdout)
    except json.JSONDecodeError:
        res = {"accepted": False, "stage": "crash", "errors": [proc.stdout[-2000:] + proc.stderr[-2000:]]}
    ps = (res.get("stages") or {}).get("postsynth") or {}
    failed_points = []
    for p in ps.get("points") or []:
        if p.get("mismatches"):
            failed_points.append(p.get("point"))
    if not failed_points and res.get("stage") == "postsynth":
        # the rejected point's record (run_clocked raised: the record of the failing point is the last one)
        pts = ps.get("points") or []
        failed_points = [pts[-1].get("point")] if pts else []
    out = {"id": mid, "stage": res.get("stage"), "accepted": res.get("accepted"),
           "unproved_ok": res.get("unproved_ok"), "exit": proc.returncode,
           "errors": [e[:1500] for e in (res.get("errors") or [])][:3], "warnings": (res.get("warnings") or [])[:3],
           "postsynth_failed_points": failed_points, "seconds": round(time.time() - t0, 1),
           "stage_seconds": {k: (v or {}).get("seconds") for k, v in (res.get("stages") or {}).items()
                             if isinstance(v, dict)}}
    return out


def step_check(a):
    _, ms = mutants(a.work)
    todo = [r["id"] for r in ms if not os.path.isfile(os.path.join(a.work, "check", f"{r['id']}.json"))]
    if a.only:
        todo = [m for m in todo if m in a.only.split(",")]
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(check_one, a.work, mid, []): mid for mid in todo}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "check", f"{r['id']}.json"), r)
            print(r["id"], r["stage"], r["seconds"], (r["errors"][0].splitlines()[0][:160] if r["errors"] else ""),
                  flush=True)


# ---------------------------------------------------------------- the reactive check alone, per point

POINT_POINTS = [1, 2, 3, 4, 5, 8]


def point_one(work, mid, ns=None):
    """The reactive post-synthesis check that check.py runs at N = 3, 5, 8 (`score_clocked`: the clocked
    Yosys flow at the point, then `postsynth.run_clocked`, full mode), run alone at every N of POINT_POINTS:
    does the task's oracle, at THAT N, reject the mutant?"""
    sys.path.insert(0, os.path.join(SVGOLF, "check"))
    sys.path.insert(0, os.path.join(SVGOLF, "score"))
    import envelope, postsynth, score
    task = envelope.load_task(TASK)
    mod = postsynth.clocked_oracle(postsynth.load_oracle(TASK, task), task["kind"])
    path = os.path.join(work, "point", f"{mid}.json")
    out = jload(path) if os.path.isfile(path) else {"id": mid, "points": {}}
    for n in (POINT_POINTS if ns is None else ns):
        if str(n) in out["points"]:
            continue
        pt = {"N": n}
        t0 = time.time()
        with tempfile.TemporaryDirectory(prefix=f"mpt-{mid}-") as w:
            try:
                ex = envelope.extract(mpath(work, mid), task["top"], [pt], os.path.join(w, "extract"))
                nl = os.path.join(w, "netlist.v")
                sres = score.score([ex["canonical"]], task["top"], pt, gate=False, netlist_out=nl, flow="seq")
                pw = os.path.join(w, "point")
                os.makedirs(pw)
                postsynth.run_clocked(task, ex["envelope"], nl, sres, pw, mod, pt, None, "full")
                r = {"verdict": "passes"}
            except postsynth.Reject as e:
                r = {"verdict": "rejects", "first": e.msg.splitlines()[0][:200],
                     "detail": [ln.strip() for ln in e.msg.splitlines()[1:4]]}
            except Exception as e:     # a refusal before the check (extraction, the flow): recorded as such
                r = {"verdict": "refused", "first": f"{type(e).__name__}: {str(e).splitlines()[0][:200] if str(e) else ''}"}
        r["seconds"] = round(time.time() - t0, 1)
        out["points"][str(n)] = r
    return out


def step_point(a):
    """Every mutant at every N of POINT_POINTS; with --where-sim-silent, only at the N where the simulation
    statement fired nothing (elsewhere the mutant is already killed at that N)."""
    _, ms = mutants(a.work)
    jobs = []
    for r in ms:
        mid = r["id"]
        if a.only and mid not in a.only.split(","):
            continue
        ns = list(POINT_POINTS)
        sp = os.path.join(a.work, "sim", f"{mid}.json")
        if a.where_sim_silent and os.path.isfile(sp):
            sim = jload(sp)["points"]
            ns = [n for n in POINT_POINTS if not (sim.get(str(n), {}).get("fired") or sim.get(str(n), {}).get("error"))]
        pp = os.path.join(a.work, "point", f"{mid}.json")
        have = set(jload(pp)["points"]) if os.path.isfile(pp) else set()
        ns = [n for n in ns if str(n) not in have]
        if ns or not os.path.isfile(pp):
            jobs.append((mid, ns))
    with cf.ProcessPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(point_one, a.work, mid, ns): mid for mid, ns in jobs}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "point", f"{r['id']}.json"), r)
            print(r["id"], " ".join(f"N{n}:{p['verdict'][0]}" for n, p in sorted(r["points"].items())), flush=True)


# ---------------------------------------------------------------- formal

EQV = """module eqv #(parameter int N = 8) (input logic clk, rst, input logic [N-1:0] req, output logic bad);
  logic [N-1:0] g_r, g_m;
  arb_ref #(.N(N)) R (.clk(clk), .rst(rst), .req(req), .gnt(g_r));
  arb_mut #(.N(N)) M (.clk(clk), .rst(rst), .req(req), .gnt(g_m));
  logic seen = 1'b0;
  always_ff @(posedge clk) seen <= seen | rst;
  assign bad = seen && (g_r != g_m);
endmodule
"""

PRP = """module prp #(parameter int N = 8) (input logic clk, rst, input logic [N-1:0] req, output logic bad);
  localparam int W = $clog2(N) + 1;
  logic [N-1:0] g;
  arb_mut #(.N(N)) M (.clk(clk), .rst(rst), .req(req), .gnt(g));
  // the entry of the snapshot shown by `g`, and the segment's state (power-up: no entry seen yet)
  logic seen = 1'b0, rs = 1'b0;
  logic [N-1:0] rq = '0;
  logic [N*W-1:0] cnt = '0;
  logic [N-1:0] miss, viol;
  always_comb begin
    for (int i = 0; i < N; i++) begin
      miss[i] = seen && !rs && rq[i] && !g[i];
      viol[i] = miss[i] && (cnt[i*W +: W] >= N - 1);
    end
  end
  always_ff @(posedge clk) begin
    seen <= seen | rst;
    rs <= rst;
    rq <= req;
    for (int i = 0; i < N; i++)
      cnt[i*W +: W] <= rs ? '0 : miss[i] ? ((cnt[i*W +: W] >= N - 1) ? cnt[i*W +: W] : cnt[i*W +: W] + 1'b1) : '0;
  end
  wire g0 = rs && (g != '0);
  wire g1 = seen && !rs && ((g & (g - 1'b1)) != '0);
  wire g2 = seen && !rs && ((g & ~rq) != '0);
  wire g3 = seen && !rs && (rq != '0) && (g == '0);
  wire g4 = viol != '0;
  assign bad = g0 || g1 || g2 || g3 || g4;
endmodule
"""


def yosys_aig(d, top, n, files):
    script = "\n".join([f'read_verilog -sv "{f}"' for f in files] + [
        f"chparam -set N {n} {top}", f"hierarchy -check -top {top}", "proc", "flatten",
        "setundef -undriven -anyconst", "opt_clean", "techmap", "opt_clean", "aigmap",
        "write_aiger -zinit -map map.txt x.aig"])
    with open(os.path.join(d, "x.ys"), "w") as fh:
        fh.write(script + "\n")
    p = subprocess.run([YOSYS, "-q", "-s", "x.ys"], cwd=d, capture_output=True, text=True, timeout=600)
    if p.returncode != 0:
        return (p.stdout + p.stderr).strip().splitlines()[-3:]
    return None


ABC_RE = re.compile(r"Property proved|was asserted in frame (\d+)|UNDECIDED|Reached timeout|timeout",
                    re.IGNORECASE)


def abc_run(d, engine, timeout):
    cmd = {"pdr": f"read_aiger x.aig; pdr -T {timeout}; write_cex -n cex_pdr.txt",
           "int": f"read_aiger x.aig; int -T {timeout}"}[engine]
    t0 = time.time()
    try:
        p = subprocess.run([ABC, "-c", cmd], cwd=d, capture_output=True, text=True, timeout=timeout + 60)
    except subprocess.TimeoutExpired:
        return {"engine": engine, "result": "timeout", "seconds": round(time.time() - t0, 2)}
    out = p.stdout + p.stderr
    m = ABC_RE.search(out)
    res = ("proved" if m and m.group(0).lower().startswith("property proved") else
           "falsified" if m and m.group(1) else "undecided")
    r = {"engine": engine, "result": res, "seconds": round(time.time() - t0, 2)}
    if res == "falsified":
        r["frame"] = int(m.group(1))
    if res == "undecided":
        r["tail"] = out.strip().splitlines()[-2:]
    return r


def parse_map(d):
    ins, inits = {}, {}
    with open(os.path.join(d, "map.txt")) as fh:
        for ln in fh:
            f = ln.split()
            if f[0] == "input":
                ins[int(f[1])] = (f[3], int(f[2]))
            elif f[0] == "init":
                inits[int(f[1])] = (f[3], int(f[2]))
    return ins, inits


def parse_cex(d, frame):
    """ABC's counterexample (write_cex -n): the power-up values {flop: int} and the entries [{rst, req}],
    frames 0 .. frame-1 (the state of frame `frame` is the bad snapshot)."""
    ins, inits = parse_map(d)
    vals = {}
    with open(os.path.join(d, "cex_pdr.txt")) as fh:
        for ln in fh:
            m = re.match(r"pi(\d+)@(\d+)=([01])", ln.strip())
            if m:
                vals[(int(m.group(1)), int(m.group(2)))] = int(m.group(3))
    init = {}
    for i, (name, bit) in inits.items():
        init[name] = init.get(name, 0) | (vals.get((i, 0), 0) << bit)
    entries = []
    for f in range(frame):
        e = {"rst": 0, "req": 0}
        for i, (name, bit) in ins.items():
            if name in e:
                e[name] |= vals.get((i, f), 0) << bit
        entries.append(e)
    return init, entries


def ports_at(text, n):
    import pyslang
    from pyslang import ast
    tree = mutate.parse(text)
    co = ast.CompilationOptions()
    co.paramOverrides = [f"N={n}"]
    comp = ast.Compilation(pyslang.Bag([co]))
    comp.addSyntaxTree(tree)
    inst = comp.getRoot().topInstances[0]
    return [(p.name, str(p.direction).split(".")[-1], p.type.bitWidth) for p in inst.body.portList]


def comb_writes(text, name):
    """Does a comb process or a continuous assignment write `name`? (the output discipline, syntactically)"""
    tree = mutate.parse(text)
    for n in mutate.walk_nodes(tree.root):
        if n.kind.name in ("AlwaysCombBlock", "ContinuousAssign", "AlwaysBlock", "AlwaysLatchBlock"):
            for m in mutate.walk_nodes(n):
                if m.kind.name in mutate.ASSIGN and m.left.kind.name == "IdentifierName" \
                        and m.left.identifier.valueText == name:
                    return True
    return False


def formal_one(work, mid, timeout, keep):
    with open(REF) as fh:
        ref = fh.read()
    text = ref if mid == "ref" else open(mpath(work, mid)).read()
    out = {"id": mid, "points": {}}
    want = lambda n: [("clk", "In", 1), ("rst", "In", 1), ("req", "In", n), ("gnt", "Out", n)]
    out["moore_syntactic"] = not comb_writes(text, "gnt")
    for n in FORMAL_POINTS:
        rec = {}
        ps = ports_at(text, n)
        rec["interface"] = ps == want(n)
        if not rec["interface"]:
            rec["ports"] = ps
        for kind, top, harness in (("equiv", "eqv", EQV), ("guarantee", "prp", PRP)):
            if not rec["interface"]:
                rec[kind] = {"result": "n/a (the interface differs)"}
                continue
            d = os.path.join(work, "formal_runs", mid, f"N{n}_{kind}")
            shutil.rmtree(d, ignore_errors=True)
            os.makedirs(d)
            files = []
            for name, src in (("arb_ref", ref), ("arb_mut", text)):
                if kind == "guarantee" and name == "arb_ref":
                    continue
                p = os.path.join(d, f"{name}.sv")
                with open(p, "w") as fh:
                    fh.write(mutate.rename_module(src, name))
                files.append(p)
            hp = os.path.join(d, f"{top}.sv")
            with open(hp, "w") as fh:
                fh.write(harness)
            err = yosys_aig(d, top, n, files + [hp])
            if err:
                rec[kind] = {"result": "yosys error", "error": err}
                continue
            r1 = abc_run(d, "pdr", timeout)
            r = {"result": r1["result"], "pdr": r1}
            if r1["result"] == "proved":
                r2 = abc_run(d, "int", timeout)
                r["int"] = r2
                if r2["result"] != "proved":
                    r["result"] = "undecided (pdr proved, int " + r2["result"] + ")"
            elif r1["result"] == "falsified":
                r["frame"] = r1["frame"]
                init, entries = parse_cex(d, r1["frame"])
                r["cex"] = {"init": init, "entries": entries}
            rec[kind] = r
            if not keep:
                shutil.rmtree(d, ignore_errors=True)
        out["points"][str(n)] = rec
    return out


def step_formal(a):
    ids = ["ref"] + [r["id"] for r in mutants(a.work)[1]]
    if a.only:
        ids = [m for m in ids if m in a.only.split(",")]
    todo = [m for m in ids if not os.path.isfile(os.path.join(a.work, "formal", f"{m}.json"))]
    with cf.ProcessPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(formal_one, a.work, mid, a.timeout, a.keep): mid for mid in todo}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "formal", f"{r['id']}.json"), r)
            print(r["id"], " ".join(
                f"N{n}:{'E' if p['equiv']['result'] == 'proved' else 'e' if p['equiv']['result'] == 'falsified' else '?'}"
                f"{'G' if p['guarantee']['result'] == 'proved' else 'g' if p['guarantee']['result'] == 'falsified' else '?'}"
                for n, p in r["points"].items()), flush=True)


# ---------------------------------------------------------------- replay a counterexample (Icarus + oracle.py)

def replay(text, n, init, entries, work):
    """The mutant's RTL from the power-up `init` ({flop: int}, hierarchical names M.x) on `entries`, by Icarus:
    the snapshots [gnt], and oracle.py's verdict on every segment."""
    import oracle
    d = tempfile.mkdtemp(prefix="replay-", dir=work)
    dut = mutate.rename_module(text, "arb_mut")
    sets = "\n".join(f"    dut.{k.split('.', 1)[1]} = {v};" for k, v in init.items() if k.startswith("M."))
    drive = "\n".join(f"    rst = {e['rst']}; req = {e['req']}; #1 clk = 1; #1 $display(\"S %0d\", gnt); clk = 0; #1;"
                      for e in entries)
    tb = (f"module tbr; logic clk = 0, rst = 0; logic [{n}-1:0] req = 0; wire [{n}-1:0] gnt;\n"
          f"  arb_mut #(.N({n})) dut (.clk(clk), .rst(rst), .req(req), .gnt(gnt));\n"
          f"  initial begin\n    #0;\n{sets}\n    #1;\n{drive}\n    $finish;\n  end\nendmodule\n")
    with open(os.path.join(d, "dut.sv"), "w") as fh:
        fh.write(dut)
    with open(os.path.join(d, "tbr.sv"), "w") as fh:
        fh.write(tb)
    p = subprocess.run(["iverilog", "-g2012", "-o", "a.vvp", "tbr.sv", "dut.sv"], cwd=d, capture_output=True,
                       text=True)
    if p.returncode:
        return {"error": p.stderr[-500:]}
    p = subprocess.run(["vvp", "-n", "a.vvp"], cwd=d, capture_output=True, text=True)
    snaps = [ln.split()[1] for ln in p.stdout.splitlines() if ln.startswith("S ")]
    snaps = [int(s) if s.isdigit() else s for s in snaps]
    viol = []
    starts = [i for i, e in enumerate(entries) if e["rst"]]
    for k, s in enumerate(starts):
        end = next((j for j in starts if j > s and entries[j - 1]["rst"] == 0), len(entries))
        # the segment: the LAST reset entry of a run of resets, then the entries until the next reset
        last = s
        while last + 1 < len(entries) and entries[last + 1]["rst"]:
            last += 1
        if last != s:
            continue
        stop = next((j for j in range(last + 1, len(entries)) if entries[j]["rst"]), len(entries))
        if any(isinstance(x, str) for x in snaps[last:stop]):
            viol.append((last, f"unknown snapshot {snaps[last:stop]}"))
            continue
        for j, why in oracle.grant_violations({"N": n}, snaps[last], [e["req"] for e in entries[last + 1:stop]],
                                              snaps[last + 1:stop]):
            viol.append((last + 1 + j if j >= 0 else last, why))
    shutil.rmtree(d, ignore_errors=True)
    return {"snapshots": snaps, "violations": viol}


def step_replay(a):
    r = jload(os.path.join(a.work, "formal", f"{a.id}.json"))
    g = r["points"][str(a.n)]["guarantee"]
    if "cex" not in g:
        print(f"{a.id} at N={a.n}: no counterexample ({g['result']})")
        return
    text = open(mpath(a.work, a.id)).read()
    out = replay(text, a.n, g["cex"]["init"], g["cex"]["entries"], a.work)
    print(json.dumps({"init": g["cex"]["init"], "entries": g["cex"]["entries"], **out}, indent=1))


# ---------------------------------------------------------------- merge

def verdicts(rec, simr, chk, frm, pts):
    """Per N, two views. FAMILY (the sweep's definition): KILLED when the simulation statement fired at N
    or check.py rejected the design (a submission is the whole family, so a rejection at one point rejects
    it at every N); else EQUIVALENT when the equivalence at N is proved; else SURVIVOR. LOCAL (what the
    checks see at N itself): KILLED when the simulation fired at N, the reactive check run alone at N
    (`point`) rejected, or check.py rejected at a stage that is not `postsynth` (source, extract, fourstate,
    clocked_rules, design, score: the design itself); else as above. Beside both: the statement at N
    (CORRECT: the interface and G0-G4 proved; WRONG: the interface differs or G0-G4 falsified)."""
    out = {}
    rejected = chk is not None and not chk.get("accepted") and chk.get("stage") != "unproved"
    for n in REPORT_POINTS:
        sp = (simr or {}).get("points", {}).get(str(n), {})
        fp = (frm or {}).get("points", {}).get(str(n), {})
        pp = (pts or {}).get("points", {}).get(str(n), {})
        fired = sp.get("fired") or []
        eq = (fp.get("equiv") or {}).get("result")
        gu = (fp.get("guarantee") or {}).get("result")
        sim_k = (["sim:" + ("+".join(fired) if fired else "error")] if fired or sp.get("error") else [])
        fam = list(sim_k)
        if rejected:
            where = chk.get("postsynth_failed_points") or []
            fam.append("check:" + chk["stage"] + (f"@{','.join(where)}" if where else ""))
        loc = list(sim_k)
        if rejected and chk["stage"] != "postsynth":
            loc.append("check:" + chk["stage"])
        if pp.get("verdict") in ("rejects", "refused"):
            loc.append(f"postsynth@N={n}:" + pp["verdict"])
        correct = ("CORRECT" if fp.get("interface") and gu == "proved" else
                   "WRONG" if (fp and not fp.get("interface")) or gu == "falsified" else "UNKNOWN")

        def v(k):
            return "KILLED" if k else "EQUIVALENT" if eq == "proved" else "SURVIVOR"
        out[str(n)] = {"verdict": v(fam), "killed_by": fam, "local_verdict": v(loc) if pts else None,
                       "local_killed_by": loc if pts else None, "equivalent": eq, "guarantee": gu,
                       "interface": fp.get("interface"), "statement_at_N": correct,
                       "postsynth_alone": pp.get("verdict")}
    return out


def step_merge(a):
    man, ms = mutants(a.work)
    rows = []
    for r in man["mutants"]:
        row = {k: r[k] for k in ("id", "op", "ctx", "line", "col", "orig", "repl")}
        if r["dup_of"]:
            row["dropped"] = f"duplicate of {r['dup_of']}"
            rows.append(row)
            continue
        if not r["file"]:
            row["dropped"] = "does not elaborate: " + "; ".join(r["errors"])[:200]
            rows.append(row)
            continue
        get = lambda step: (jload(p) if os.path.isfile(p := os.path.join(a.work, step, f"{r['id']}.json")) else None)
        simr, chk, frm, pts = get("sim"), get("check"), get("formal"), get("point")
        row["check"] = None if chk is None else {
            "stage": chk["stage"], "accepted": chk["accepted"], "unproved_ok": chk["unproved_ok"],
            "error": (scrub(chk["errors"][0].splitlines()[0])[:240] if chk["errors"] else None),
            "postsynth_failed_points": chk.get("postsynth_failed_points")}
        row["sim"] = None if simr is None else {n: p["fired"] or (["error"] if p["error"] else [])
                                                 for n, p in simr["points"].items()}
        row["moore_syntactic"] = None if frm is None else frm.get("moore_syntactic")
        row["per_N"] = verdicts(r, simr, chk, frm, pts)
        rows.append(row)
    out = {"source": man["source"], "source_sha256": man["source_sha256"], "pyslang": man["pyslang"],
           "method": {
               "sim": f"tests/arbiter/sim.py run(), tb.sv, Icarus, N = {SIM_POINTS}, modes {' '.join(map(str, sim.MODES))} "
                   f"from 0/1 power-up states, {a.cycles} cycles",
               "check": "check.py tasks/arbiter <mutant> --unproved --postsynth full --ppa off (one family verdict)",
               "point": f"the clocked post-synthesis check alone at N = {POINT_POINTS}, full mode, where the "
                        "simulation fired nothing at that N",
               "formal": f"N = {FORMAL_POINTS}: Yosys to AIGER (write_aiger -zinit: every power-up state), ABC "
                         "pdr, proofs confirmed by ABC int; equivalence with the reference from the first reset "
                         "entry on; the guarantee G0-G4 by a monitor; unbounded"},
           "generated": man["generated"], "duplicates": man["duplicates"],
           "not_elaborating": man["not_elaborating"], "kept": man["kept"], "mutants": rows}
    with open(a.out, "w") as fh:      # one mutant per line
        head = {k: v for k, v in out.items() if k != "mutants"}
        fh.write(json.dumps(head)[:-1] + ', "mutants": [\n'
                 + ",\n".join(json.dumps(r, separators=(",", ":")) for r in rows) + "\n]}\n")
    with open(os.path.splitext(a.out)[0] + ".txt", "w") as fh:
        fh.write(manifest_text(out))
    # the summary
    from collections import Counter
    for view in ("verdict", "local_verdict"):
        for n in REPORT_POINTS:
            c = Counter((row["per_N"][str(n)][view], row["per_N"][str(n)]["statement_at_N"])
                        for row in rows if "per_N" in row)
            print(f"{view:13s} N={n}: " + ", ".join(f"{k}/{w} {v}" for (k, w), v in sorted(c.items(), key=str)))
    stages = Counter((row["check"] or {}).get("stage") for row in rows if "per_N" in row)
    print("check.py stages:", dict(stages))
    for row in rows:
        if "per_N" not in row:
            continue
        for n in REPORT_POINTS:
            p = row["per_N"][str(n)]
            lv = p["local_verdict"] or p["verdict"]
            if lv == "SURVIVOR" or (lv == "KILLED" and p["statement_at_N"] == "CORRECT"):
                print(f"  {row['id']} N={n} {p['verdict']}/{lv} {row['op']} {row['line']}:{row['col']} {row['orig']!r} -> "
                      f"{row['repl']!r} equiv={p['equivalent']} guarantee={p['guarantee']} "
                      f"killed_by={p['killed_by']} local={p['local_killed_by']}")


def scrub(text):
    """A message without the machine's absolute paths (the work directories of the run): `<work>/name`."""
    return re.sub(r"(?<![\w.])/(?:[^\s:'\"/]+/)+", "<work>/", text) if text else text


def short(v):
    return ("-" if v is None or v.startswith("n/a") else {"proved": "P", "falsified": "F"}.get(v, "?"))


def manifest_text(out):
    """MANIFEST.txt: one line per generated mutant (the JSON's columns, compressed)."""
    lines = [f"# Mutants of {out['source']} (sha256 {out['source_sha256'][:16]}), tests/mutate.py with pyslang "
             f"{out['pyslang']}: {out['generated']} generated, {out['duplicates']} duplicates, "
             f"{out['not_elaborating']} do not elaborate, {out['kept']} kept.",
             "# Columns: id, operator, ctx, line:col, original -> replacement; check.py --unproved stage (@ the",
             "# postsynth point it failed at); per N = 1 2 3 4 8: the family verdict and the local verdict (K",
             "# killed, E equivalent, S survivor; `verdicts` in classify.py), then [equivalence, guarantee G0-G4]",
             "# as P proved / F falsified / - not applicable (the interface differs), the simulation checks that",
             "# fired at N, and the reactive check alone at N (p passes, r rejects). Full records: MANIFEST.json.",
             ""]
    for row in out["mutants"]:
        repl = row["repl"] if isinstance(row["repl"], str) else "(swap)"
        head = f"{row['id']} {row['op']:3s} {row['ctx']:6s} {row['line']}:{row['col']:<3d} {row['orig']!r} -> {repl!r}"
        if "per_N" not in row:
            lines.append(f"{head}  DROPPED: {row['dropped']}")
            continue
        chk = row["check"] or {}
        st = chk.get("stage") or "?"
        if chk.get("postsynth_failed_points"):
            st += "@" + ",".join(chk["postsynth_failed_points"])
        per = []
        for n in REPORT_POINTS:
            p = row["per_N"][str(n)]
            sim = "+".join((row["sim"] or {}).get(str(n), [])) or "-"
            loc = (p["local_verdict"] or "?")[0]
            per.append(f"N{n}:{p['verdict'][0]}{loc}[{short(p['equivalent'])}{short(p['guarantee'])}]"
                       f"{sim}/{(p['postsynth_alone'] or '-')[0]}")
        lines.append(f"{head}\n    check: {st}; " + " ".join(per))
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("step", choices=["gen", "sim", "check", "point", "formal", "merge", "replay"])
    ap.add_argument("id", nargs="?")
    ap.add_argument("n", nargs="?", type=int)
    ap.add_argument("--work", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--cycles", type=int, default=20000, help="sim: cycles per run (merge: the cycles recorded)")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--only")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--where-sim-silent", action="store_true", help="point: only at the N where sim fired nothing")
    ap.add_argument("--out", default=os.path.join(HERE, "MANIFEST.json"))
    a = ap.parse_args()
    {"gen": step_gen, "sim": step_sim, "check": step_check, "point": step_point, "formal": step_formal,
     "merge": step_merge, "replay": step_replay}[a.step](a)


if __name__ == "__main__":
    main()
