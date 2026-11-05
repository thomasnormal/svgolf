#!/usr/bin/env python3
"""X7 preparation: heartbeats per theorem and per site of a svGolf reference proof on TODAY's route (the baseline that
E-derived lenses will be measured against; ARCH-NOTE §7 X7, §4.4 cost model).

    python3 x7_probe.py stage --repo REPO --task T --ref NAME --stage STAGE_DIR       # check.py --stage-dir (Lean via the slot)
    python3 x7_probe.py probe --repo REPO --task T --ref NAME --stage STAGE_DIR         # writes STAGE_DIR/Probe.lean
    (LEAN_PATH=STAGE_DIR/build $SLOT lake env lean STAGE_DIR/Probe.lean > STAGE_DIR/probe.out, from svgolf/)
    python3 x7_probe.py collect --stage STAGE_DIR --task T --ref NAME --repo REPO     # one JSON row
    python3 x7_probe.py slice-probe --env ENV.json --ref NAME --stage STAGE_DIR       # the probe of a sliced block
    python3 x7_probe.py report --stage STAGES --slices SLICES --out x7.json            # all rows, verdicts, slicer logs

The probe is the staged `Submission/Solution.lean` with two changes only, none of which touches a proof:
  * `set_option Elab.async false` (so a theorem's elaboration AND kernel check happen inside its own command);
  * every top-level declaration wrapped in `count_hb in` (defined in the probe from core Lean's
    `IO.getNumHeartbeats`, the counter `maxHeartbeats` limits), which prints `X7HB <line> <heartbeats>`;
  * nothing else: `count_hb in` goes before a declaration's doc comment, which stays part of the declaration.
It ends with `#eval`s printing the number of processes of the design at the task's scoring point (flat sites).

`slice-probe` writes the probe of a block sliced by x7_slice.py, which has no proof of its own: today's route written out
(`load_design_sv2`; `sv_structure` with the rank computed by `slice_rank`; `sv_equations` with every input known and the
references' closers), each command under `count_hb`, plus the verdict of the recognizer (`siteOfP?`) on EVERY site, not
only the first refusal the tactics report.
Template sites (what a lens is instantiated per, ARCH-NOTE §4.4) are counted from the envelope: one per continuous
assign / always_comb process in the top module's text, a generate body counted once.
"""
import argparse
import json
import os
import re
import subprocess
import sys

HB_CMD = '''
open Lean Elab Command in
elab "count_hb " "in " cmd:command : command => do
  let h0 ← IO.getNumHeartbeats
  elabCommand cmd
  let h1 ← IO.getNumHeartbeats
  let pos := (← getFileMap).toPosition (cmd.raw.getPos?.getD 0)
  logInfo m!"X7HB {pos.line} {h1 - h0}"
'''

DECL = re.compile(r"^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|example)\b")


def cmd_stage(a):
    sv = os.path.join(a.repo, "svgolf", "tasks", a.task, "reference", a.ref + ".sv")
    ln = os.path.join(a.repo, "svgolf", "tasks", a.task, "reference", a.ref + ".lean")
    env = dict(os.environ)
    env.pop("SVGOLF_LEAN_WRAP", None)
    r = subprocess.run([sys.executable, "check.py", os.path.join("tasks", a.task), sv, "--unproved", "--stage-dir",
                        a.stage, "--lean-wrap", a.slot, "--no-score", "--no-trusted-build", "--time-limit", "100000",
                        "--json", os.path.join(a.stage, "check.json")],
                       cwd=os.path.join(a.repo, "svgolf"), env=env, capture_output=True, text=True)
    print("check.py rc", r.returncode)


def cmd_probe(a):
    staged = os.path.join(a.stage, "Submission", "Solution.lean")
    if os.path.exists(staged):
        src = open(staged).read()
    else:   # a `check.py --unproved` stage: the reference proof itself
        src = open(os.path.join(a.repo, "svgolf", "tasks", a.task, "reference", a.ref + ".lean")).read()
    lines = src.split("\n")
    head, body = [], []
    i = 0
    while i < len(lines) and (lines[i].startswith("import ") or not lines[i].strip()):
        head.append(lines[i])
        i += 1
    body = lines[i:]
    out = []
    for k, ln in enumerate(body):
        if DECL.match(ln):
            # insert before the preceding attribute / `set_option ... in` lines and the declaration's doc comment
            j = len(out)
            while j > 0 and (out[j - 1].startswith("@[") or re.match(r"^set_option .* in\s*$", out[j - 1])):
                j -= 1
            e = j
            while e > 0 and not out[e - 1].strip():
                e -= 1
            if e > 0 and out[e - 1].rstrip().endswith("-/"):
                t = e - 1
                while t >= 0 and not out[t].lstrip().startswith("/-"):
                    t -= 1
                if t >= 0 and out[t].lstrip().startswith("/--"):
                    j = t
            out.insert(j, "count_hb in")
        out.append(ln)
    task = json.load(open(os.path.join(a.repo, "svgolf", "tasks", a.task, "task.json")))
    point = (task.get("scoring") or {}).get("params") or {}
    params = [p["name"] for p in task.get("parameters", [])]
    args = " ".join(str(point.get(p)) for p in params if p in point)
    sem = "Submission.design.sem" + ((" " + args) if args else "")
    tail = ['', '#eval IO.println s!"X7FLAT {(%s).processes.size}"' % sem]
    probe = "\n".join(head + ["import Lean", "", "set_option Elab.async false", HB_CMD] + out + tail) + "\n"
    open(os.path.join(a.stage, "Probe.lean"), "w").write(probe)
    print("wrote", os.path.join(a.stage, "Probe.lean"), "scoring point", point)


def template_sites(env_path):
    env = json.load(open(env_path))
    top = env["top"]
    mod = next(m for m in env["design"]["modules"] if m["name"] == top)
    n = 0

    def walk(x):
        nonlocal n
        if isinstance(x, dict):
            if x.get("kind") in ("Assign", "AlwaysComb"):
                n += 1
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(mod.get("processes", []))
    walk(mod.get("generates", []))
    return n


def cmd_collect(a):
    out = open(os.path.join(a.stage, "probe.out"), errors="replace").read()
    probe = open(os.path.join(a.stage, "Probe.lean")).read().split("\n")
    rows = []
    for m in re.finditer(r"X7HB (\d+) (\d+)", out):
        line, hb = int(m.group(1)), int(m.group(2))
        decl = probe[line - 1] if line - 1 < len(probe) else ""
        if decl.startswith("load_design_sv2"):
            rows.append({"decl": "load_design_sv2", "heartbeats": hb})
            continue
        k = line - 1
        while k < len(probe) and not DECL.match(probe[k]):
            k += 1
        decl = probe[k] if k < len(probe) else decl
        name = re.sub(r"^(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|example)\s*", "", decl)
        rows.append({"decl": name.split()[0] if name.split() else decl[:40], "heartbeats": hb})
    flat = re.search(r"X7FLAT (\d+)", out)
    errors = [ln for ln in out.split("\n") if ": error" in ln][:5]
    total = sum(r["heartbeats"] for r in rows)
    ts = template_sites(os.path.join(a.stage, "design.sv.json"))
    res = {"task": a.task, "ref": a.ref, "template_sites": ts, "flat_sites": int(flat.group(1)) if flat else None,
           "total_heartbeats": total, "decls": rows, "errors": errors,
           "per_template_site_kHB": round(total / 1000 / ts, 1) if ts else None,
           "per_flat_site_kHB": round(total / 1000 / int(flat.group(1)), 1) if flat else None}
    json.dump(res, open(os.path.join(a.stage, "x7row.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in res.items() if k != "decls"}))


def idents(x, acc):
    if isinstance(x, dict):
        if x.get("kind") == "Ident" and "name" in x:
            acc.add(x["name"])
        for v in x.values():
            idents(v, acc)
    elif isinstance(x, list):
        for v in x:
            idents(v, acc)
    return acc


def rw_sets(proc):
    """(written names, read names) of one envelope process: names under a `target` are written, the rest read;
    a name the process itself writes is not a read of another site (an always_comb body is lowered to one assign
    of its final values)."""
    w, r = set(), set()

    def go(x):
        if isinstance(x, dict):
            for k, v in x.items():
                (idents(v, w) if k == "target" else go(v))
            if x.get("kind") == "Ident" and "name" in x:
                r.add(x["name"])
        elif isinstance(x, list):
            for v in x:
                go(v)
    go(proc)
    return w, r - w


def slice_rank(env):
    """A rank for `Acyclic`, computed from the envelope: the depth of each site in the signal-level dependency graph
    (inputs at depth 0). Plain sites are the top module's processes in order (`SiteId.plain pos`,
    `PDesign.summaryG`); a generate-for site gets the depth of its block, by label."""
    mod = next(m for m in env["design"]["modules"] if m["name"] == env["top"])
    sites = [("plain", i, p) for i, p in enumerate(mod["processes"])]
    for g in mod.get("generates", []):
        for p in g.get("body", g.get("items", [])):
            if isinstance(p, dict) and p.get("kind") in ("Assign", "AlwaysComb"):
                sites.append((g.get("label", "?"), None, p))
    rw = [(lab, pos) + rw_sets(p) for lab, pos, p in sites]
    writer = {}
    for k, (_, _, w, _) in enumerate(rw):
        for n in w:
            writer.setdefault(n, set()).add(k)
    depth = {}

    def d(k, stack=()):
        if k in depth:
            return depth[k]
        if k in stack:
            raise SystemExit("signal-level cycle through site %s" % (rw[k][:2],))
        best = -1
        for n in rw[k][3]:
            for j in writer.get(n, ()):
                if j != k:
                    best = max(best, d(j, stack + (k,)))
        depth[k] = best + 1
        return depth[k]
    plain = [d(k) for k, x in enumerate(rw) if x[0] == "plain"]
    fams = {}
    for k, x in enumerate(rw):
        if x[0] != "plain":
            fams[x[0]] = max(fams.get(x[0], 0), d(k))
    return plain, fams


def cmd_slice_probe(a):
    """The Lean probe of a sliced block (x7_slice.py): today's route, each command wrapped in `count_hb`."""
    env = json.load(open(a.env))
    plain, fams = slice_rank(env)
    fam = "0"
    for lab, v in sorted(fams.items()):
        fam = 'if l = "%s" then %d else %s' % (lab, v, fam)
    ns = re.sub(r"\W", "_", a.ref)
    src = ["import LeanModels.Sv.Ingest2", "import LeanModels.Sv.CombViewTactic", "import LeanModels.Sv.CombProcTactic",
           "import LeanModels.Sv.CombEqTactic", "import Lean", "", "set_option Elab.async false",
           "set_option maxHeartbeats 10000000", HB_CMD,
           "open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq", "", "namespace X7.%s" % ns, "",
           "-- The rank of a site is its depth in the signal-level dependency graph (x7_probe.py slice_rank).",
           "count_hb in", "load_design_sv2 d from %s" % json.dumps(os.path.abspath(a.env)), "",
           "count_hb in",
           "theorem struct : ∃ d', d.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by",
           "  sv_structure (rank := rippleRank (fun p => %s.getD p 0) (fun l _ _ => %s))"
           % (json.dumps(plain).replace(",", ", "), fam),
           "  all_goals first | (intros; omega) | (intros; simp at * <;> omega) | decide", "",
           "count_hb in",
           "theorem eqs {d' : Design2} (hl : d.sem.lowerComb = some d') (hc : CombDesign d') (ha : Acyclic d')",
           "    (st : SvState) (heqs : CombEqs d' st) (hsh : StateShape d' st)"]
    # the inputs are known in the settled state (what a task's `HoldAll` on the inputs gives a reference proof)
    mod = next(m for m in env["design"]["modules"] if m["name"] == env["top"])
    ins = [(q["name"], q["width"]["resolved"]) for q in mod["ports"] if q["dir"] == "in"]
    for nm, w in ins:
        src.append("    {x_%s : BitVec %d} (hin_%s : SvState.lookup st \"%s\" = some (LVec.ofBitVec x_%s))"
                   % (nm, w, nm, nm, nm))
    src += ["    : True := by", "  sv_equations", "  all_goals first", "    | trivial", "    | (intros; omega)",
            "    | sv_cover"]
    src += ["    | (refine inKnown_ofBitVec hin_%s ?_; omega)" % nm for nm, _ in ins]
    src += [""]
    src += [
           '#eval IO.println s!"X7FLAT {d.sem.processes.size}"',
           "-- Every site's verdict under today's recognizer (`siteOfP?`, the `always_comb` arm included), not",
           "-- only the first refusal the tactics report.",
           "#eval show IO Unit from do",
           "  match declsOf? d.pdesign.decls with",
           '  | .error e => IO.println s!"X7SITE decls REFUSED {e}"',
           "  | .ok ds =>",
           "    let mut i := 0",
           "    for p in d.pdesign.processes do",
           "      match siteOfP? ds i p with",
           '      | .error e => IO.println s!"X7SITE plain#{i} REFUSED {e}"',
           '      | .ok _ => IO.println s!"X7SITE plain#{i} ok"',
           "      i := i + 1",
           "    match famsOfP? ds d.pdesign.generates with",
           '    | .error e => IO.println s!"X7SITE generates REFUSED {e}"',
           '    | .ok fs => IO.println s!"X7SITE generates ok ({fs.length})"',
           '    match d.pdesign.summaryP with',
           '    | .error e => IO.println s!"X7SUMMARY REFUSED {e}"',
           '    | .ok _ => IO.println "X7SUMMARY ok"',
           '#eval IO.println s!"X7LOAD unsupported={d.sem.hasUnsupported}"', "#print axioms struct", "#print axioms eqs",
           "", "end X7.%s" % ns, ""]
    os.makedirs(a.stage, exist_ok=True)
    open(os.path.join(a.stage, "Probe.lean"), "w").write("\n".join(src))
    open(os.path.join(a.stage, "design.sv.json"), "w").write(open(a.env).read())
    print("wrote", os.path.join(a.stage, "Probe.lean"), "depth", plain, "fams", fams)


REFS = [("add", "add_n"), ("mul", "mul_n"), ("clmul", "clmul_n"), ("mul", "mul_wallace"), ("fdivp", "fdivp"),
        ("fdiv16", "fdiv16"), ("aes_sbox", "sbox_bp")]
SLICE_STAGES = [("ibex_cs_registers@csrop", "slice_csrop"), ("ibex_alu@accepted", "slice_alu_accepted"),
                ("ibex_alu@rv32bnone", "slice_alu"), ("ibex_alu@pkgonly", "slice_alu_pkgonly")]


def cmd_report(a):
    """x7.json: the reference rows, the slice rows (cost, per-site verdicts) and the slicer's transformation logs."""
    out = {"schema": "x7/1", "references": [], "slices": []}
    for task, ref in REFS:
        p = os.path.join(a.stage, ref, "x7row.json")
        out["references"].append(json.load(open(p)) if os.path.exists(p) else {"task": task, "ref": ref, "missing": True})
    for variant, st in SLICE_STAGES:
        d = os.path.join(a.stage, st)
        row = {"variant": variant}
        if os.path.exists(os.path.join(d, "x7row.json")):
            row.update(json.load(open(os.path.join(d, "x7row.json"))))
        po = os.path.join(d, "probe.out")
        if os.path.exists(po):
            txt = open(po, errors="replace").read()
            row["site_verdicts"] = [{"site": int(i), "verdict": v} for i, v in re.findall(r"X7SITE plain#(\d+) (.*)", txt)]
            g = re.search(r"X7SITE generates (.*)", txt)
            row["generates_verdict"] = g.group(1) if g else None
            sm = re.search(r"X7SUMMARY (.*)", txt)
            row["summary"] = sm.group(1) if sm else None
            row["heartbeats_by_command"] = [{"line": int(l), "heartbeats": int(h)}
                                            for l, h in re.findall(r"X7HB (\d+) (\d+)", txt)]
            row["axioms"] = re.findall(r"'(X7\.[^']+)' depends on axioms: \[([^\]]*)\]", txt)
        tj = os.path.join(a.slices, variant, "transforms.json")
        if os.path.exists(tj):
            sj = json.load(open(tj))
            for t in sj["transforms"]:   # keep generate block labels only: no third-party source text in the repository
                if "nested_generate_blocks_dropped" in t:
                    t["nested_generate_blocks_dropped"] = [m.group(1) for l in t["nested_generate_blocks_dropped"]
                                                           for m in [re.search(r":\s*(\w+)\s*$", l)] if m]
            row["slicer"] = sj
        out["slices"].append(row)
    json.dump(out, open(a.out, "w"), indent=1)
    print("wrote", a.out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["stage", "probe", "collect", "slice-probe", "report"])
    ap.add_argument("--slices")
    ap.add_argument("--out")
    ap.add_argument("--env")
    ap.add_argument("--repo")
    ap.add_argument("--task")
    ap.add_argument("--ref")
    ap.add_argument("--stage")
    ap.add_argument("--slot", default=os.environ.get("SLOT"))
    a = ap.parse_args()
    {"stage": cmd_stage, "probe": cmd_probe, "collect": cmd_collect, "slice-probe": cmd_slice_probe,
     "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    main()
