#!/usr/bin/env python3.12
"""X6, multi-point elaboration divergence, step 1 (Python): choose parameter points and run the extractor's
multi-point probes (ARCH-NOTE §7 X6, §4.1 "slang a multi-point witness"; EXECUTION-PLAN WS4 Days 2-3).

    python3.12 -I x6_extract.py --repo REPO --census CENSUS_OUT_DIR --src RB0_SRC --out OUT_DIR [--only ID,..] [-j 2]

Population: (a) every RB0 census envelope (CENSUS_OUT_DIR/<id>.env.json, the census's own extraction) whose top has at
least one `ParameterDecl` with an integer default; its sources are the envelope's own `source_files` (sha256-checked),
its include directories the corpus.json ones of its base block under RB0_SRC/files/<project>; (b) every registered svGolf reference whose top has a parameter (in-repo).

Points (deterministic, at most MAX_POINTS per design): for each integer parameter with default v, alone, the values
v//2, v+1, 2*v and 1 (distinct, != v, 0 <= x <= 1024); for a 1-bit parameter, 1-v; plus, with two or more integer
parameters, one point with every integer parameter doubled. Combinations a design does not accept are kept: slang's
rejection is itself recorded (`frontend_errors`), and the Lean side reports it as `frontendRejects`, never as agreement.

For each design: `extract.py --top T SOURCES -I ... -o OUT/<id>.sv.json --probe-points "<points>"` through
run_extract.py (python3.12 -I). Output: the envelope, its `.probes.json` sidecar, and OUT/index.json (one row per
design: id, kind, top, parameters with defaults, points, extractor status). Step 2 is X6Batch.lean (the Lean
cross-check `probeReportString` over every row), step 3 x6_report.py.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MAX_POINTS = 12


def int_params(env):
    top = env["top"]
    mods = env["design"]["modules"]
    m = next((x for x in mods if x["name"] == top), mods[0])
    out = []
    for p in m.get("params", []):
        if p.get("kind") != "ParameterDecl":
            continue
        v = p.get("resolved")
        if not isinstance(v, int) or isinstance(v, bool):
            continue
        t = p.get("type") or {}
        bit = isinstance(t, dict) and t.get("resolved") == 1 and t.get("packed") == []
        out.append({"name": p["name"], "default": v, "bit": bool(bit)})
    return out


def choose_points(params):
    pts = []
    for p in params:
        v = p["default"]
        if p["bit"]:
            cand = [1 - v] if v in (0, 1) else []
        else:
            cand = [v // 2, v + 1, 2 * v, 1]
        seen = set()
        for c in cand:
            if c == v or c in seen or c < 0 or c > 1024:
                continue
            seen.add(c)
            pts.append([(p["name"], c)])
    ints = [p for p in params if not p["bit"]]
    if len(ints) >= 2:
        joint = [(p["name"], 2 * p["default"]) for p in ints if 0 <= 2 * p["default"] <= 1024]
        if joint:
            pts.append(joint)
    return pts[:MAX_POINTS]


def spec(points):
    return ";".join(",".join("%s=%d" % kv for kv in pt) for pt in points)


def census_rows(census_dir, repo, src_root):
    rb0 = os.path.join(repo, "svgolf", "design", "real-world-sv", "rb0")
    cj = json.load(open(os.path.join(rb0, "census.json")))
    meta = {b["id"]: b for b in cj["blocks"]}
    corpus = {b["id"]: b for b in json.load(open(os.path.join(rb0, "corpus.json")))}
    rows = []
    for f in sorted(os.listdir(census_dir)):
        if not f.endswith(".env.json"):
            continue
        bid = f[:-len(".env.json")]
        envp = os.path.join(census_dir, f)
        try:
            env = json.load(open(envp))
        except Exception:  # noqa: BLE001
            continue
        ps = int_params(env)
        if not ps:
            continue
        srcs = [s["path"] for s in env["source_files"]]
        ok = all(os.path.exists(s) and hashlib.sha256(open(s, "rb").read()).hexdigest() == x["sha256"]
                 for s, x in zip(srcs, env["source_files"]))
        b = meta.get(bid, {})
        base = corpus.get(bid.split("@")[0], {})
        # include directories: the base block's, under the fetched project tree (variants keep them: census_extract.py)
        proj_dir = os.path.join(src_root, "files", base.get("project", b.get("project", "")))
        incs = [os.path.join(proj_dir, d) for d in (base.get("incdirs") or [])]
        rows.append({"id": bid, "kind": "census", "top": env["top"], "sources": srcs, "incdirs": incs,
                     "sources_ok": ok, "params": ps, "loader": (b.get("lean") or {}).get("loader"),
                     "status": b.get("status")})
    return rows


def reference_rows(repo):
    rows = []
    tdir = os.path.join(repo, "svgolf", "tasks")
    for task in sorted(os.listdir(tdir)):
        tj = os.path.join(tdir, task, "task.json")
        if not os.path.exists(tj):
            continue
        t = json.load(open(tj))
        for r in t.get("references", []):
            sv = os.path.join(tdir, task, r["sv"])
            rows.append({"id": "ref:%s/%s" % (task, os.path.basename(sv)[:-3]), "kind": "reference", "top": t["top"],
                         "sources": [sv], "incdirs": [], "sources_ok": True, "params": None,
                         "task_points": t.get("probe_points") or []})
    return rows


def run_one(row, repo, out):
    stem = os.path.join(out, row["id"].replace("/", "__").replace(":", "_"))
    envp = stem + ".sv.json"
    res = dict(row)
    if row["params"] is None:
        # a reference: read its parameters from a plain extraction first
        cmd = [sys.executable, "-I", os.path.join(HERE, "run_extract.py"), "--repo", repo, "--", "--top", row["top"]]
        cmd += row["sources"] + ["-o", envp]
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=900)
        if p.returncode != 0:
            res.update(extract_rc=p.returncode, extract_err=p.stderr[-400:])
            return res
        res["params"] = int_params(json.load(open(envp)))
        if not res["params"]:
            res["extract_rc"] = None
            res["skipped"] = "no integer parameter"
            return res
    pts = choose_points(res["params"])
    if row["kind"] == "reference":
        # the task's own probe points first (they are what the checker runs), then the generated ones
        tp = [[tuple(a.split("=")) for a in s.split(",")] for s in row.get("task_points", [])]
        tp = [[(n, int(v)) for n, v in pt] for pt in tp if all(n in {q["name"] for q in res["params"]} for n, _ in pt)]
        seen, merged = set(), []
        for pt in tp + pts:
            k = tuple(pt)
            if k not in seen:
                seen.add(k)
                merged.append(pt)
        pts = merged[:MAX_POINTS]
    res["points"] = [dict(pt) for pt in pts]
    if not pts:
        res["skipped"] = "no point"
        return res
    cmd = [sys.executable, "-I", os.path.join(HERE, "run_extract.py"), "--repo", repo, "--", "--top", row["top"]]
    for d in row["incdirs"]:
        cmd += ["-I", d]
    cmd += row["sources"] + ["-o", envp, "--probe-points", spec(pts)]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
        res["extract_rc"] = p.returncode
        if p.returncode != 0:
            res["extract_err"] = p.stderr[-600:]
    except subprocess.TimeoutExpired:
        res["extract_rc"] = "timeout"
    res["envelope"] = envp if os.path.exists(envp) else None
    side = envp[:-len(".json")] + ".probes.json"
    res["sidecar"] = side if os.path.exists(side) else None
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--census", required=True)
    ap.add_argument("--src", required=True, help="the RB0 fetch root (its files/<project>/ trees)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--only")
    ap.add_argument("-j", type=int, default=2)
    a = ap.parse_args()
    repo = os.path.abspath(a.repo)
    os.makedirs(a.out, exist_ok=True)
    rows = census_rows(a.census, repo, os.path.abspath(a.src)) + reference_rows(repo)
    if a.only:
        keep = set(a.only.split(","))
        rows = [r for r in rows if r["id"] in keep]
    rows = [r for r in rows if r["sources_ok"]]
    results = []
    prev = {}
    if a.only and os.path.exists(os.path.join(a.out, "index.json")):
        prev = {r["id"]: r for r in json.load(open(os.path.join(a.out, "index.json")))}
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.j) as ex:
        for r in ex.map(lambda r: run_one(r, repo, a.out), rows):
            results.append(r)
            print(r["id"], r.get("extract_rc"), len(r.get("points") or []), r.get("skipped", ""), flush=True)
    prev.update({r["id"]: r for r in results})
    json.dump(sorted(prev.values(), key=lambda r: r["id"]), open(os.path.join(a.out, "index.json"), "w"), indent=1)


if __name__ == "__main__":
    main()
