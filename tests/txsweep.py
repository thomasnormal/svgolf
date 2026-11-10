#!/usr/bin/env python3.12
"""The mutation sweep of a transaction task (tx-family `matmul`, stream-family `sorter`): every generated mutant of the
task's reference, KILLED by the task's checks, proved EQUIVALENT to the reference, proved CORRECT, or a SURVIVOR. The
arbiter's sweep (`tests/arbiter/mutants/classify.py`) is the model; this is its engine for the two latency kinds, and
`tests/{sorter,matmul}/mutants/classify.py` are its entry points (the task's configuration, below).

    python3.12 tests/{sorter,matmul}/mutants/classify.py gen    --work DIR
    python3.12 tests/{sorter,matmul}/mutants/classify.py check  --work DIR [--jobs J] [--latency L]
    python3.12 tests/{sorter,matmul}/mutants/classify.py formal --work DIR [--jobs J] [--timeout S]
    python3.12 tests/{sorter,matmul}/mutants/classify.py lean   --work DIR --only ID,ID,...   (check.py --unproved)
    python3.12 tests/{sorter,matmul}/mutants/classify.py merge  --work DIR [--out tests/<task>/mutants/MANIFEST.json]

Each step writes DIR/<step>/<id>.json and skips what is there (rerun a step by deleting its directory).

* `gen`: `tests/mutate.py` on the reference, elaborated by pyslang at the task's GEN points, the reset port `rst`.
* `check`: every stage of `check.py --unproved --postsynth full --ppa off` that runs no Lean, in check.py's order and
  with check.py's own functions: the source gate, the pinned extractor at the probe points (the parameters and the
  ports at every probe point), the banlist, `fourstate`, `clocked_rules`, then the clocked Yosys flow and the clocked
  post-synthesis check (`postsynth.run_clocked`, full mode, 8 seeds) at the scoring point and the task's postsynth
  points, scoring point first, stopping at the first that fails, as check.py does. NOT run: `trusted` and `design`
  (Lean: the `lean` step runs the real check.py on a sample). The declared latency: `--latency L` at every point (as
  an `--unproved` check.py run without `--latency-at`; a proved run takes the kernel's `lat p` at each point, decided
  2026-11-08), by default the task's LAT_BIG, a generous
  multiple of the reference's; a mutant that passes at LAT_BIG is run again at the reference's latency
  (`ref_latency`), so a mutant that is right but slower than the reference shows as such.
* `formal`: for the mutants `check` did not reject, at the task's FORMAL points (small points and the scoring point).
  First Yosys's own structural equivalence (`equiv_make; equiv_simple -seq 2; equiv_induct -seq 2; equiv_status
  -assert`: registers matched by name, the ordinary unconditional equivalence); where it does not prove, the
  EQUIVALENCE MITER under the task's rely, Yosys to AIGER (`read_verilog -sv; proc; flatten; setundef -undriven
  -anyconst; techmap; aigmap; write_aiger -zinit`) and ABC `pdr` (IC3; a pdr proof is replayed by ABC `int` for at
  most a minute, recorded beside it). The miter: both designs on one clock and the same inputs, every flip-flop of
  both powering up FREE (`-zinit`: an input gives each uninitialized flop its power-up value, txtask-v2's rule 2), and
  a protocol monitor that powers up in the unreset state and is reset by every entry with `rst` = 1: `seen` (a reset
  entry was sampled), the task's rely as a sticky flag `viol` (cleared by a reset entry), and the bad state `seen &&
  !viol && <a cared output of the snapshot differs>` (the TASK's cared outputs, the task's MITER), at the snapshots of
  the entries with `rst` = 0 (the claimed ones). So the outputs the statement cares about agree at every claimed
  snapshot, under every input that keeps the protocol, resets included: then the mutant meets the guarantee wherever
  the reference does, with the reference's latency (its rules 1 and 3 are structural; a mutant changes no process
  kind). Where the equivalence is not proved and the task has one, the GUARANTEE MITER (`miter_correct`): the mutant's
  cared outputs against the reference's results under the mutant's own rely, with a latency bound of its own (a
  correct design that is not equivalent: slower, or free where the statement asks nothing).
* `lean`: the real `check.py <task> <mutant> --unproved --latency <ref latency> --postsynth full --ppa off` through
  `$SVGOLF_LEAN_WRAP` (the `trusted` and `design` stages run Lean), for the ids given: the sample.
* `merge`: per mutant the verdict KILLED (check, or the sampled check.py, rejected it), else EQUIVALENT (the
  equivalence proved at every FORMAL point), else CORRECT (at every FORMAL point the equivalence or the guarantee
  miter proved), else EQUIVALENT-SMALL / CORRECT-SMALL (the same at every FORMAL point but the scoring point, the
  last, where nothing was decided within the time limit), else SURVIVOR; MANIFEST.json (one mutant per line) and
  MANIFEST.txt.
"""
import argparse, concurrent.futures as cf, hashlib, json, os, re, shutil, subprocess, sys, tempfile, time

sys.dont_write_bytecode = True       # it imports the tasks' oracle.py: no __pycache__ in a task directory

HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.normpath(os.path.join(HERE, ".."))
sys.path.insert(0, HERE)
import mutate  # noqa: E402

YOSYS = os.environ.get("YOSYS", "yosys")
ABC = os.environ.get("YOSYS_ABC", "yosys-abc")


def pstr(p):
    return ",".join(f"{k}={v}" for k, v in p.items())


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


def mpath(work, mid, cfg=None):
    if mid == "ref":
        return os.path.join(SVGOLF, cfg["ref"])
    return os.path.join(work, "gen", f"{mid}.sv")


def scrub(text):
    """A message without the machine's absolute paths (the work directories of the run): `<work>/name`."""
    return re.sub(r"(?<![\w.])/(?:[^\s:'\"/]+/)+", "<work>/", text) if text else text


# ---------------------------------------------------------------- gen

def step_gen(cfg, a):
    with open(os.path.join(SVGOLF, cfg["ref"])) as fh:
        text = fh.read()
    recs, texts = mutate.generate(text, cfg["gen_points"], reset="rst")
    out = os.path.join(a.work, "gen")
    os.makedirs(out, exist_ok=True)
    for mid, t in texts.items():
        with open(os.path.join(out, f"{mid}.sv"), "w") as fh:
            fh.write(t)
    import pyslang
    man = {"source": cfg["ref"], "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
           "pyslang": getattr(pyslang, "__version__", None), "points": cfg["gen_points"], "reset": "rst",
           "generated": len(recs), "duplicates": sum(1 for r in recs if r["dup_of"]),
           "not_elaborating": sum(1 for r in recs if r["elaborates"] is False), "kept": len(texts), "mutants": recs}
    jdump(os.path.join(out, "mutants.json"), man)
    print(f"{len(recs)} generated, {man['duplicates']} duplicates, {man['not_elaborating']} do not elaborate, "
          f"{len(texts)} kept")


# ---------------------------------------------------------------- check (check.py's stages that run no Lean)

_CP = []


def checkpy():
    """check.py as a module (its stage functions), loaded once per process."""
    if not _CP:
        import importlib.util
        spec = importlib.util.spec_from_file_location("svgolf_check_py_sweep", os.path.join(SVGOLF, "check.py"))
        mod = importlib.util.module_from_spec(spec)
        sys.modules["svgolf_check_py_sweep"] = mod
        spec.loader.exec_module(mod)
        _CP.append(mod)
    return _CP[0]


def nolean_check(task_dir, sv_path, latency, work):
    """check.py's stages that run no Lean, in its order (`check.py` main and `score_clocked`): {stage, error,
    failed_point, points: [{point, seeds, cycles, failures}]}; stage `unproved` when every one passed."""
    cp = checkpy()
    envelope, banlist, fourstate, clocked_rules, postsynth, score = (cp.envelope, cp.banlist, cp.fourstate,
                                                                     cp.clocked_rules, cp.postsynth, cp.score)
    task = envelope.load_task(task_dir)
    top, kind = task["top"], task["kind"]
    out = {"stage": None, "error": None, "failed_point": None, "points": []}

    def rej(stage, msg, point=None):
        out.update(stage=stage, error=scrub(msg)[:3000], failed_point=point)
        return out
    oracle = postsynth.clocked_oracle(postsynth.load_oracle(task_dir, task), kind)
    canon, findings = envelope.gate(sv_path, name="design.sv", clock=task["clock"])
    if findings:
        return rej("source", "\n".join(findings[:8]))
    sv = os.path.join(work, "design.sv")
    with open(sv, "w", newline="") as fh:
        fh.write(canon)
    env_path = os.path.join(work, "design.sv.json")
    probe_pts = cp.probe_points(task)
    proc, _ = envelope.run_extractor(sv, top, probe_pts, env_path)
    if proc.returncode != 0 or not os.path.exists(env_path):
        return rej("extract", "the extractor refused the design:\n" + cp.tail(proc.stderr + proc.stdout))
    envl = jload(env_path)
    mods = [m for m in envl["design"]["modules"] if m.get("name") == top]
    got = [p.get("name") for p in mods[0].get("params", []) if p.get("kind") == "ParameterDecl"] if mods else None
    if got != [p["name"] for p in task.get("parameters", [])]:
        return rej("extract", f"parameters {got}")
    bad = cp.port_problems(task, top, envl, envelope.sidecar_path(env_path) if probe_pts else None)
    if bad[0]:
        return rej("extract", "ports: " + "\n".join(bad[0][:8]))
    ops, points = banlist.task_banlist(task)
    front, diags = banlist.front_check([sv], top, ops, probe_pts + points)
    back = banlist.backstop_check([sv], top, ops, points)
    if front or back or diags:
        return rej("banlist", json.dumps((front + back + diags)[:6]))
    fs = fourstate.check_points([sv], top, cp.fourstate_points(task))
    if not fs["passed"]:
        return rej("fourstate", f"at {pstr(fs['failed_point'])}: " + "\n".join((fs["findings"] + fs["diagnostics"])[:8]),
                   pstr(fs["failed_point"]))
    cr = clocked_rules.check(env_path)
    if not cr["passed"]:
        return rej("clocked_rules", "\n".join(cr["findings"][:8]))
    # (check.py's `trusted` and `design` stages run Lean: not here)
    sparams = score.task_scoring_point(task)[1]
    pts = [{n: int(v) for n, v in pt.items()} for pt in postsynth.config(task)["points"] or []]
    pts = ([] if sparams in pts else [sparams]) + pts
    for k, pt in enumerate(pts):
        nl = os.path.join(work, f"netlist_{k}.v")
        try:
            pres = score.score([sv], top, pt, netlist_out=nl, flow="seq")
            cp.never_loaded(pres, sv, top, pt)
        except score.ScoreError as e:
            return rej("score", str(e), pstr(pt))
        except cp.Reject as r:
            return rej(r.stage, r.msg, pstr(pt))
        pw = os.path.join(work, f"point_{k}")
        os.makedirs(pw)
        try:
            rec = postsynth.run_clocked(task, env_path, nl, pres, pw, oracle, pt, latency, "full")
            out["points"].append({"point": pstr(pt), "seeds": len(rec.get("seeds") or []),
                                  "cycles": sum((s or {}).get("cycles") or 0 for s in rec.get("seeds") or [])})
        except postsynth.Reject as r:
            return rej("postsynth", r.msg, pstr(pt))
    out["stage"] = "unproved"
    return out


def check_one(cfg, work, mid, latency):
    t0 = time.time()
    res = {"id": mid, "latency": latency}
    with tempfile.TemporaryDirectory(prefix=f"mchk-{mid}-") as w:
        try:
            r = nolean_check(os.path.join(SVGOLF, cfg["task_dir"]), mpath(work, mid, cfg), latency, w)
        except Exception as e:      # an infrastructure error: recorded, never a verdict
            r = {"stage": "infra", "error": f"{type(e).__name__}: {str(e)[:1500]}"}
        res["big"] = r
        if r["stage"] == "unproved" and cfg["ref_latency"] != latency:
            with tempfile.TemporaryDirectory(prefix=f"mchk-{mid}-ref-") as w2:
                try:
                    res["ref"] = nolean_check(os.path.join(SVGOLF, cfg["task_dir"]), mpath(work, mid, cfg),
                                              cfg["ref_latency"], w2)
                except Exception as e:
                    res["ref"] = {"stage": "infra", "error": f"{type(e).__name__}: {str(e)[:1500]}"}
    res["seconds"] = round(time.time() - t0, 1)
    return res


def step_check(cfg, a):
    ids = ["ref"] + [r["id"] for r in mutants(a.work)[1]]
    if a.only:
        ids = [m for m in ids if m in a.only.split(",")]
    lat = a.latency or cfg["lat_big"]
    todo = [m for m in ids if not os.path.isfile(os.path.join(a.work, "check", f"{m}.json"))]
    with cf.ProcessPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(check_one, cfg, a.work, mid, lat): mid for mid in todo}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "check", f"{r['id']}.json"), r)
            b = r["big"]
            print(r["id"], b["stage"], b.get("failed_point") or "", r["seconds"],
                  (b.get("error") or "").splitlines()[0][:150] if b.get("error") else "",
                  ("| at the ref latency: " + r["ref"]["stage"]) if "ref" in r else "", flush=True)


# ---------------------------------------------------------------- formal

def yosys_aig(d, top, point, files):
    script = "\n".join([f'read_verilog -sv "{f}"' for f in files] + [
        *[f"chparam -set {k} {v} {top}" for k, v in point.items()], f"hierarchy -check -top {top}", "proc",
        "flatten", "setundef -undriven -anyconst", "opt_clean", "techmap", "opt_clean", "aigmap",
        "write_aiger -zinit -map map.txt x.aig"])
    with open(os.path.join(d, "x.ys"), "w") as fh:
        fh.write(script + "\n")
    p = subprocess.run([YOSYS, "-q", "-s", "x.ys"], cwd=d, capture_output=True, text=True, timeout=1800)
    if p.returncode != 0:
        return (p.stdout + p.stderr).strip().splitlines()[-3:]
    return None


ABC_RE = re.compile(r"Property proved|was asserted in frame (\d+)|UNDECIDED|Reached timeout|timeout",
                    re.IGNORECASE)


def abc_run(d, engine, timeout):
    cmd = {"pdr": f"read_aiger x.aig; pdr -T {timeout}", "int": f"read_aiger x.aig; int -T {timeout}"}[engine]
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


def yosys_equiv(d, point, ref_file, mut_file, gold, gate, timeout):
    """Yosys's unconditional structural equivalence of the two designs at `point` (registers matched by name)."""
    ps = " ".join(f"-set {k} {v}" for k, v in point.items())
    script = "\n".join([
        f'read_verilog -sv "{ref_file}"', f'read_verilog -sv "{mut_file}"',
        f"chparam {ps} {gold} {gate}", "proc", "opt_clean", f"rename {gold} gold", f"rename {gate} gate",
        "flatten", "equiv_make gold gate eq", "hierarchy -top eq", "equiv_simple -seq 2", "equiv_induct -seq 2",
        "equiv_status -assert"])
    with open(os.path.join(d, "eq.ys"), "w") as fh:
        fh.write(script + "\n")
    t0 = time.time()
    try:
        p = subprocess.run([YOSYS, "-q", "-s", "eq.ys"], cwd=d, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"engine": "equiv", "result": "timeout", "seconds": round(time.time() - t0, 2)}
    out = (p.stdout + p.stderr).strip()
    return {"engine": "equiv", "result": "proved" if p.returncode == 0 else "unproved",
            "seconds": round(time.time() - t0, 2), **({"tail": out.splitlines()[-2:]} if p.returncode else {})}


def miter_run(work, mid, pt, kind, harness, ref, text, timeout, keep):
    """One miter (`harness`, top module `eqv`) of the reference and the mutant at `pt`. For the equivalence miter,
    Yosys's structural equivalence first (registers matched by name: fast, and enough for most equivalent mutants);
    where it does not prove it, and for the guarantee miter, ABC pdr. A pdr proof is then replayed by ABC int with a
    short time limit, recorded beside it (a confirmation, not required)."""
    d = os.path.join(work, "formal_runs", mid, kind + "_" + pstr(pt).replace(",", "_").replace("=", ""))
    shutil.rmtree(d, ignore_errors=True)
    os.makedirs(d)
    files = []
    for name, src in (("d_ref", ref), ("d_mut", text)):
        p = os.path.join(d, f"{name}.sv")
        with open(p, "w") as fh:
            fh.write(mutate.rename_module(src, name))
        files.append(p)
    hp = os.path.join(d, "eqv.sv")
    with open(hp, "w") as fh:
        fh.write(harness)
    rec = {}
    if kind == "equiv":
        rec["equiv"] = yosys_equiv(d, pt, files[0], files[1], "d_ref", "d_mut", timeout)
    if rec.get("equiv", {}).get("result") != "proved":
        err = yosys_aig(d, "eqv", pt, files + [hp])
        if err:
            rec["pdr"] = {"result": "yosys error", "error": err}
        else:
            rec["pdr"] = abc_run(d, "pdr", timeout)
            if rec["pdr"]["result"] == "proved":
                rec["int"] = abc_run(d, "int", min(timeout, INT_CONFIRM_S))
    rec["result"] = ("proved" if rec.get("equiv", {}).get("result") == "proved" or
                     rec.get("pdr", {}).get("result") == "proved" else
                     "falsified" if rec.get("pdr", {}).get("result") == "falsified" else "undecided")
    if not keep:
        shutil.rmtree(d, ignore_errors=True)
    return rec


INT_CONFIRM_S = 60


def formal_one(cfg, work, mid, timeout, keep, points=None):
    """Per FORMAL point: the equivalence miter (`miter`), and where it is not proved the task's guarantee miter
    (`miter_correct`, when the task has one: the mutant's cared outputs against the reference's results, with its
    own latency bound; a correct design that is not equivalent, e.g. slower)."""
    with open(os.path.join(SVGOLF, cfg["ref"])) as fh:
        ref = fh.read()
    text = ref if mid == "ref" else open(mpath(work, mid)).read()
    path = os.path.join(work, "formal", f"{mid}.json")
    out = jload(path) if points is not None and os.path.isfile(path) else {"id": mid, "points": {}}
    for pt in (cfg["formal_points"] if points is None else points):
        rec = {"equiv": miter_run(work, mid, pt, "equiv", cfg["miter"], ref, text, timeout, keep)}
        if rec["equiv"]["result"] != "proved" and cfg.get("miter_correct"):
            rec["correct"] = miter_run(work, mid, pt, "correct", cfg["miter_correct"], ref, text, timeout, keep)
        rec["result"] = rec["equiv"]["result"]
        out["points"][pstr(pt)] = rec
    return out


def step_formal(cfg, a):
    ids = ["ref"] + [r["id"] for r in mutants(a.work)[1]]
    if a.only:
        ids = [m for m in ids if m in a.only.split(",")]
    elif not a.all:     # only where `check` did not reject
        keep = []
        for m in ids:
            p = os.path.join(a.work, "check", f"{m}.json")
            if os.path.isfile(p) and jload(p)["big"]["stage"] in ("unproved", "infra"):
                keep.append(m)
        ids = keep
    points = None
    if a.redo_small:     # again at the points before the scoring point, with this run's time limit; the rest kept
        points = cfg["formal_points"][:-1]
        todo = [m for m in ids if os.path.isfile(os.path.join(a.work, "formal", f"{m}.json"))]
    else:
        todo = [m for m in ids if not os.path.isfile(os.path.join(a.work, "formal", f"{m}.json"))]
    with cf.ProcessPoolExecutor(a.jobs) as ex:
        futs = {ex.submit(formal_one, cfg, a.work, mid, a.timeout, a.keep, points): mid for mid in todo}
        for f in cf.as_completed(futs):
            r = f.result()
            jdump(os.path.join(a.work, "formal", f"{r['id']}.json"), r)
            print(r["id"], " ".join(f"{n}:{p['equiv']['result']}" + (f"/correct:{p['correct']['result']}" if "correct" in p
                                                                         else "") for n, p in r["points"].items()),
                  flush=True)


# ---------------------------------------------------------------- lean (the real check.py, a sample)

def lean_one(cfg, work, mid):
    t0 = time.time()
    proc = subprocess.run([sys.executable, os.path.join(SVGOLF, "check.py"), os.path.join(SVGOLF, cfg["task_dir"]),
                           mpath(work, mid, cfg), "--unproved", "--latency", str(cfg["ref_latency"]),
                           "--postsynth", "full", "--ppa", "off"], capture_output=True, text=True, cwd=SVGOLF)
    try:
        res = json.loads(proc.stdout)
    except json.JSONDecodeError:
        res = {"accepted": False, "stage": "crash", "errors": [proc.stdout[-2000:] + proc.stderr[-2000:]]}
    return {"id": mid, "stage": res.get("stage"), "accepted": res.get("accepted"),
            "unproved_ok": res.get("unproved_ok"), "exit": proc.returncode,
            "errors": [scrub(e)[:1500] for e in (res.get("errors") or [])][:3],
            "seconds": round(time.time() - t0, 1),
            "stage_seconds": {k: (v or {}).get("seconds") for k, v in (res.get("stages") or {}).items()
                              if isinstance(v, dict)}}


def step_lean(cfg, a):
    if not a.only:
        sys.exit("lean: give the sample with --only ID,ID,...")
    for mid in a.only.split(","):
        if os.path.isfile(os.path.join(a.work, "lean", f"{mid}.json")):
            continue
        r = lean_one(cfg, a.work, mid)
        jdump(os.path.join(a.work, "lean", f"{mid}.json"), r)
        print(mid, r["stage"], r["seconds"], (r["errors"][0].splitlines()[0][:160] if r["errors"] else ""),
              flush=True)


# ---------------------------------------------------------------- merge

def verdict(chk, lean, frm, cfg):
    """KILLED when the no-Lean check (at LAT_BIG) rejected, or the sampled check.py did at a stage that does not
    depend on the declared latency (it declares the reference's); else EQUIVALENT when the
    equivalence is proved at every FORMAL point; else CORRECT when at every FORMAL point the equivalence or the
    guarantee miter is proved; else, when that holds at every FORMAL point but the scoring point (the last), where
    neither is falsified, EQUIVALENT-SMALL / CORRECT-SMALL (the scoring point's miter was not decided); else
    SURVIVOR."""
    killed = []
    if chk and chk["big"]["stage"] not in ("unproved", "infra"):
        b = chk["big"]
        killed.append(f"check:{b['stage']}" + (f"@{b['failed_point']}" if b.get("failed_point") else ""))
    # the sampled check.py declares the REFERENCE's latency: a `postsynth` rejection of a mutant that passes at
    # LAT_BIG says it is slower than the reference (`check_ref_latency` says the same), not that it is wrong
    if lean and not lean.get("accepted") and lean.get("stage") not in ("unproved", "crash", None) and (
            lean["stage"] != "postsynth" or killed):
        killed.append(f"check.py:{lean['stage']}")
    if killed:
        return "KILLED", killed
    pts = (frm or {}).get("points", {})
    if not pts:
        return "SURVIVOR", []
    got = [pts.get(pstr(p), {}) for p in cfg["formal_points"]]
    eq = lambda g: g.get("equiv", {}).get("result") == "proved"           # noqa: E731
    ok = lambda g: eq(g) or g.get("correct", {}).get("result") == "proved"  # noqa: E731
    if all(eq(g) for g in got):
        return "EQUIVALENT", []
    if all(ok(g) for g in got):
        return "CORRECT", []
    last = got[-1]
    if not ok(last) and last.get("correct", {}).get("result") != "falsified":
        if all(eq(g) for g in got[:-1]) and last.get("equiv", {}).get("result") != "falsified":
            return "EQUIVALENT-SMALL", []
        if all(ok(g) for g in got[:-1]):
            return "CORRECT-SMALL", []
    return "SURVIVOR", []


def step_merge(cfg, a):
    man, _ = mutants(a.work)
    rows = []
    get = lambda step, mid: (jload(p) if os.path.isfile(p := os.path.join(a.work, step, f"{mid}.json")) else None)
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
        chk, lean, frm = get("check", r["id"]), get("lean", r["id"]), get("formal", r["id"])
        v, by = verdict(chk, lean, frm, cfg)
        row["verdict"], row["killed_by"] = v, by
        if chk:
            b = chk["big"]
            row["check"] = {"latency": chk["latency"], "stage": b["stage"], "failed_point": b.get("failed_point"),
                            "error": (b["error"].splitlines()[0][:240] if b.get("error") else None)}
            if "ref" in chk:
                rr = chk["ref"]
                row["check_ref_latency"] = {"latency": cfg["ref_latency"], "stage": rr["stage"],
                                            "failed_point": rr.get("failed_point"),
                                            "error": (rr["error"].splitlines()[0][:240] if rr.get("error") else None)}
        if lean:
            row["check_py"] = {"stage": lean["stage"], "accepted": lean["accepted"],
                               "error": (lean["errors"][0].splitlines()[0][:240] if lean["errors"] else None)}
        if r["id"] in cfg.get("refuted", {}):
            row["kernel"] = cfg["refuted"][r["id"]]
        if frm:
            row["formal"] = {n: p["equiv"]["result"] + (f" (correct: {p['correct']['result']})" if "correct" in p else "")
                             for n, p in frm["points"].items()}
        rows.append(row)
    refchk = get("check", "ref")
    out = {"source": man["source"], "source_sha256": man["source_sha256"], "pyslang": man["pyslang"],
           "method": {
               "check": f"check.py's stages that run no Lean (source, extract, banlist, fourstate, clocked_rules, the "
                        f"clocked flow and postsynth.run_clocked full mode at {', '.join(cfg['postsynth_points'])}), "
                        f"declared latency {cfg['lat_big']} (and {cfg['ref_latency']}, the reference's, for a mutant "
                        "that passes)",
               "check_py": f"the real check.py --unproved --latency {cfg['ref_latency']} --postsynth full --ppa off, on "
                           "a sample (the rows with `check_py`)",
               "formal": f"at {', '.join(pstr(p) for p in cfg['formal_points'])}: Yosys equiv_make/equiv_induct "
                         "(unconditional, registers by name), else the equivalence miter under the rely from every "
                         "power-up (Yosys to AIGER, ABC pdr; a proof replayed by ABC int for a minute), else (where "
                         "the task has one) the guarantee miter: the mutant's cared outputs against the reference's "
                         "results, its own rely and latency bound"},
           "reference_check": None if refchk is None else refchk["big"]["stage"],
           "kernel_file": cfg.get("kernel_file"),
           "generated": man["generated"], "duplicates": man["duplicates"],
           "not_elaborating": man["not_elaborating"], "kept": man["kept"], "mutants": rows}
    with open(a.out, "w") as fh:      # one mutant per line
        head = {k: v for k, v in out.items() if k != "mutants"}
        fh.write(json.dumps(head)[:-1] + ', "mutants": [\n'
                 + ",\n".join(json.dumps(r, separators=(",", ":")) for r in rows) + "\n]}\n")
    with open(os.path.splitext(a.out)[0] + ".txt", "w") as fh:
        fh.write(manifest_text(out))
    from collections import Counter
    c = Counter(row.get("verdict") for row in rows if "verdict" in row)
    print("verdicts:", dict(c))
    print("check stages:", dict(Counter((row.get("check") or {}).get("stage") for row in rows if "verdict" in row)))
    for row in rows:
        if row.get("verdict") not in ("KILLED", "EQUIVALENT", None):
            print(f"  {row['verdict']} {row['id']} {row['op']} {row['line']}:{row['col']} {row['orig']!r} -> {row['repl']!r} "
                  f"formal={row.get('formal')} ref-latency={row.get('check_ref_latency', {}).get('stage')}")


def manifest_text(out):
    lines = [f"# Mutants of {out['source']} (sha256 {out['source_sha256'][:16]}), tests/mutate.py with pyslang "
             f"{out['pyslang']}: {out['generated']} generated, {out['duplicates']} duplicates, "
             f"{out['not_elaborating']} do not elaborate, {out['kept']} kept.",
             "# Columns: id, operator, ctx, line:col, original -> replacement; the verdict (KILLED / EQUIVALENT /",
             "# CORRECT / EQUIVALENT-SMALL / CORRECT-SMALL / SURVIVOR: `verdict` in tests/txsweep.py) and what killed",
             "# it: `check:<stage>@<point>` (check.py's stages that run no Lean, the big latency), `check.py:<stage>`",
             "# (the real check.py, sampled); `formal` per point: the equivalence (proved / falsified / undecided) and,",
             "# where it is not proved, the guarantee miter (`correct: ...`); `kernel:` a refutation of the statement in",
             f"# {out['kernel_file']}. Full records and the method: MANIFEST.json.", ""]
    for row in out["mutants"]:
        repl = row["repl"] if isinstance(row["repl"], str) else "(swap)"
        head = f"{row['id']} {row['op']:3s} {row['ctx']:6s} {row['line']}:{row['col']:<3d} {row['orig']!r} -> {repl!r}"
        if "verdict" not in row:
            lines.append(f"{head}  DROPPED: {row['dropped']}")
            continue
        extra = ""
        if row.get("check_py") and f"check.py:{row['check_py']['stage']}" not in row["killed_by"]:
            extra += f"; check.py: {row['check_py']['stage']}"
        if row.get("formal"):
            extra += "; formal: " + " ".join(f"{k}:{v}" for k, v in row["formal"].items())
        if row.get("check_ref_latency"):
            extra += f"; at the reference's latency: {row['check_ref_latency']['stage']}"
        if row.get("kernel"):
            extra += f"; kernel: {row['kernel']}"
        by = " ".join(row["killed_by"])
        lines.append(f"{head}\n    {row['verdict']}" + (f" {by}" if by else "") + extra)
    return "\n".join(lines) + "\n"


def main(cfg, here):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("step", choices=["gen", "check", "formal", "lean", "merge"])
    ap.add_argument("--work", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--latency", type=int)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--only")
    ap.add_argument("--all", action="store_true", help="formal: every mutant, not only those `check` passed")
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--redo-small", action="store_true",
                    help="formal: redo the points before the scoring point for the ids given (--only), keeping the rest")
    ap.add_argument("--out", default=os.path.join(here, "MANIFEST.json"))
    a = ap.parse_args()
    {"gen": step_gen, "check": step_check, "formal": step_formal, "lean": step_lean, "merge": step_merge}[a.step](cfg, a)
