#!/usr/bin/env python3
"""X2: the comb rows of the Xcelium goldens, and the report of X2Preempt.lean over them (ARCH-NOTE §7 X2).

    python3 x2_rows.py batch --repo REPO --out BATCH.json        # the candidate rows, with their pinned Xcelium cycles
    (cd REPO && $SLOT lake env lean --run svgolf/design/architecture/measure/X2Preempt.lean BATCH.json > OUT.txt)
    python3 x2_rows.py report --out-txt OUT.txt --json x2.json   # the per-row table

A candidate row has a pinned Xcelium trace (`harness/sv/xcelium_golden.json`, status ok), a case in
`harness/sv/cases2.json`, a committed envelope, one module (no instance), and only continuous assigns and `always_comb`
in its top module (generate bodies included). Whether E-core-0 LOADS it is decided by the Lean side.
"""
import argparse
import collections
import json
import os


def walk_kinds(x, acc):
    if isinstance(x, dict):
        k = x.get("kind")
        if k in ("Assign", "AlwaysComb", "AlwaysFF", "AlwaysPosedge", "Always", "AlwaysLatch", "Initial",
                 "AlwaysFFR", "AlwaysPlain", "Unsupported", "Instance"):
            acc[k] += 1
        for v in x.values():
            walk_kinds(v, acc)
    elif isinstance(x, list):
        for v in x:
            walk_kinds(v, acc)


def cmd_batch(a):
    g = json.load(open(os.path.join(a.repo, "harness/sv/xcelium_golden.json")))["rows"]
    cases = {c["name"]: c for c in json.load(open(os.path.join(a.repo, "harness/sv/cases2.json")))["cases"]}
    stat = collections.Counter()
    rows = []
    for name in sorted(g):
        row = g[name]
        c = cases.get(name)
        if c is None:
            stat["no case"] += 1
            continue
        if row.get("status") != "ok":
            stat["golden status " + str(row.get("status"))] += 1
            continue
        fb = c.get("file", c["top"])
        envp = os.path.join(a.repo, "Examples", "system-verilog", c["example"], fb + ".sv.json")
        if not os.path.exists(envp):
            stat["no envelope"] += 1
            continue
        env = json.load(open(envp))
        mods = env["design"]["modules"]
        top = next(m for m in mods if m["name"] == env["top"])
        kinds = collections.Counter()
        for p in top["processes"]:
            kinds[p["kind"]] += 1
        walk_kinds(top.get("generates", []), kinds)
        if len(mods) > 1 or kinds.get("Instance"):
            stat["hierarchical"] += 1
            continue
        ks = set(kinds)
        if not ks:
            stat["no process"] += 1
            continue
        if not ks <= {"Assign", "AlwaysComb"}:
            stat["other process kinds: " + ",".join(sorted(ks - {"Assign", "AlwaysComb"}))] += 1
            continue
        stat["candidate, assign only" if "AlwaysComb" not in ks else "candidate, with always_comb"] += 1
        rows.append({"name": name, "envelope": os.path.abspath(envp), "params": c.get("params"),
                     "signals": c["signals"], "stimulus": c["stimulus"], "golden": row["cycles"],
                     "always_comb_in_source": kinds.get("AlwaysComb", 0)})
    json.dump(rows, open(a.out, "w"))
    print(len(g), "golden rows:", dict(stat.most_common()))
    print("wrote", a.out, len(rows), "rows")


def cmd_batch_svgolf(a):
    """The svGolf records (leaderboard) and, separately labelled, the task reference designs: each extracted with the
    repository's extractor into the work directory, at the task's scoring point, with 8 cycles of deterministic
    pseudo-random 2-state stimulus (seeded by the file name). There is no simulator trace: the observation compared is
    E-core-0's own, atomic against preemptive."""
    import glob
    import random
    import subprocess
    import sys
    os.makedirs(a.workdir, exist_ok=True)
    rows, stat = [], collections.Counter()
    srcs = [("record", f) for f in sorted(glob.glob(os.path.join(a.repo, "svgolf/leaderboard/data/*/*.sv")))]
    srcs += [("reference", f) for f in sorted(glob.glob(os.path.join(a.repo, "svgolf/tasks/*/reference/*.sv")))]
    here = os.path.dirname(os.path.abspath(__file__))
    for kind, f in srcs:
        task = f.split(os.sep)[-2] if kind == "record" else f.split(os.sep)[-3]
        t = json.load(open(os.path.join(a.repo, "svgolf/tasks", task, "task.json")))
        params = (t.get("scoring") or {}).get("params") or {}
        name = "%s:%s/%s" % (kind, task, os.path.basename(f)[:-3][:16])
        envp = os.path.join(a.workdir, "%s__%s.sv.json" % (task, os.path.basename(f)[:-3][:16]))
        r = subprocess.run([sys.executable, "-I", os.path.join(here, "run_extract.py"), "--repo", a.repo, "--",
                            "--top", t["top"], f, "-o", envp], capture_output=True, text=True)
        if r.returncode != 0 or not os.path.exists(envp):
            stat[kind + ": extract failed"] += 1
            continue
        env = json.load(open(envp))
        mods = env["design"]["modules"]
        top = next(m for m in mods if m["name"] == env["top"])
        kinds = collections.Counter()
        for p in top["processes"]:
            kinds[p["kind"]] += 1
        walk_kinds(top.get("generates", []), kinds)
        if len(mods) > 1 or kinds.get("Instance"):
            stat[kind + ": hierarchical"] += 1
            continue
        if not set(kinds) <= {"Assign", "AlwaysComb"}:
            stat[kind + ": other process kinds"] += 1
            continue
        width = lambda e: int(eval(str(e), {"__builtins__": {}}, dict(params)))  # trusted task.json width expressions
        rng = random.Random(os.path.basename(f))
        ins = [(p["name"], width(p["width"])) for p in t["ports"]["inputs"]]
        stim = [{n: format(rng.getrandbits(w), "0%db" % w) for n, w in ins} for _ in range(8)]
        sig = [n for n, _ in ins] + [p["name"] for p in t["ports"]["outputs"]]
        stat[kind + (": candidate, with always_comb" if kinds.get("AlwaysComb") else ": candidate, assign only")] += 1
        rows.append({"name": name, "envelope": os.path.abspath(envp), "params": params or None, "signals": sig,
                     "stimulus": stim, "golden": [], "always_comb_in_source": kinds.get("AlwaysComb", 0)})
    json.dump(rows, open(a.out, "w"))
    print(dict(stat.most_common()))
    print("wrote", a.out, len(rows), "rows")


def load_rows(paths):
    """X2ROW lines of several runs; a later run's row replaces an earlier one of the same name."""
    rows = {}
    for p in paths:
        for ln in open(p, errors="replace"):
            if ln.startswith("X2ROW "):
                r = json.loads(ln[6:])
                rows[r["row"]] = r
    return list(rows.values())


def summarize(rows, cases=None):
    loaded = [r for r in rows if r.get("load") == "ok"]
    refused_load = [r for r in rows if r.get("load") != "ok"]
    run_refused = [r for r in loaded if r.get("refused")]
    ran = [r for r in loaded if not r.get("refused")]
    s = {
        "rows_run": len(rows), "loaded": len(loaded), "load_refused": len(refused_load),
        "load_refusals": collections.Counter(r["load"][:70] for r in refused_load).most_common(),
        "run_refused": len(run_refused),
        "run_refusals": collections.Counter(r["refused"][:70] for r in run_refused).most_common(),
    }
    if cases is not None:
        agree = [r for r in ran if r["golden_agree"]]
        dis = [r for r in ran if not r["golden_agree"]]
        why = collections.Counter()
        dis_rows = []
        for r in dis:
            c = cases.get(r["row"], {})
            od = c.get("oracle_disagreement") or {}
            if od and od.get("sim") == "xcelium":
                k = "declared Xcelium disagreement: " + od.get("id", "?")
            elif od:
                k = "undeclared against Xcelium (the row declares a %s disagreement: %s)" % (od.get("sim"), od.get("id"))
            elif c.get("refusal"):
                k = "declared refusal: " + c["refusal"]
            else:
                k = "undeclared"
            why[k] += 1
            dis_rows.append({"row": r["row"], "class": k})
        s["golden"] = {"ran": len(ran), "agree": len(agree), "disagree": len(dis), "disagree_by_class": why.most_common(),
                       "disagree_rows": dis_rows}
    for pol in ("stmt", "eval"):
        s[pol] = {}
        for grp, pick in (("all", lambda r: True), ("assign_only", lambda r: r["combs"] == 0),
                          ("with_always_comb", lambda r: r["combs"] > 0),
                          ("with_always_comb_fed_by_another_process", lambda r: r["fed_combs"] > 0),
                          ("with_always_comb_none_fed", lambda r: r["combs"] > 0 and r["fed_combs"] == 0)):
            sub = [r for r in ran if pick(r)]
            s[pol][grp] = {"rows": len(sub), **collections.Counter(r[pol] for r in sub)}
    s["changed_rows"] = [{"row": r["row"], "combs": r["combs"], "fed_combs": r["fed_combs"], "stmt": r["stmt"],
                          "eval": r["eval"], "witness": r["witness"], "proc_desc": r["proc_desc"]}
                         for r in ran if r["stmt"] not in ("invariant", "no-statement")
                         or r["eval"] not in ("invariant", "no-statement")]
    s["fed_rows"] = [{"row": r["row"], "combs": r["combs"], "fed_combs": r["fed_combs"], "stmt": r["stmt"],
                      "eval": r["eval"]} for r in ran if r["fed_combs"] > 0]
    return s


def cmd_report(a):
    cases = {c["name"]: c for c in json.load(open(os.path.join(a.repo, "harness/sv/cases2.json")))["cases"]}
    golden = load_rows(a.out_txt)
    svg = load_rows(a.svgolf_txt) if a.svgolf_txt else []
    def slim(r):   # the model's cycles only where they differ from Xcelium; the procedure list only with an always_comb
        r = dict(r)
        if r.get("golden_agree"):
            r.pop("model_cycles", None)
        if r.get("combs", 0) == 0:
            r.pop("proc_desc", None)
        return r
    out = {"schema": "x2/1", "golden_summary": summarize(golden, cases), "svgolf_summary": summarize(svg),
           "golden_rows": [slim(r) for r in golden], "svgolf_rows": [slim(r) for r in svg]}
    json.dump(out, open(a.json, "w"), indent=1)
    for k in ("golden_summary", "svgolf_summary"):
        print(k, json.dumps({x: y for x, y in out[k].items() if x not in ("changed_rows", "fed_rows")}, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["batch", "batch-svgolf", "report"])
    ap.add_argument("--workdir")
    ap.add_argument("--repo")
    ap.add_argument("--out")
    ap.add_argument("--out-txt", nargs="*")
    ap.add_argument("--svgolf-txt", nargs="*")
    ap.add_argument("--json")
    a = ap.parse_args()
    {"batch": cmd_batch, "batch-svgolf": cmd_batch_svgolf, "report": cmd_report}[a.cmd](a)


if __name__ == "__main__":
    main()
