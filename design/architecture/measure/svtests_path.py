#!/usr/bin/env python3.12
"""Day 6: a census of the SYMBOLIC proof path over sv-tests (ARCH-NOTE §3.2 caveat and §7: "a census of the symbolic
proof path over sv-tests" is owed before any tier is priced).

    python3.12 -I svtests_path.py extract --corpus SV_TESTS/tests --repo REPO --out OUT [-j 3]
    python3.12 -I run_py.py REPO/svgolf/design/real-world-sv/rb0/census_lean.py gen --out OUT/rec --lean-dir OUT/lean --wt REPO
    $SLOT bash OUT/lean/batchAB.sh ; $SLOT bash OUT/lean/batchC.sh
    python3.12 -I run_py.py REPO/svgolf/design/real-world-sv/rb0/census_lean.py parse --out OUT/rec --lean-dir OUT/lean
    python3.12 -I svtests_path.py report --out OUT --json svtests_path.json

The symbolic path is the one svGolf and the sv_comb tactics use (NOT the self-check path SStmt that
docs/sv-construct-census.json measures): `extract.py --top T` (symbolic envelope) -> `load_design_sv2` -> the design at
its default point has no Unsupported node -> for a flat design of continuous assigns and `always_comb` only, the
structure tactic `sv_structure?` (`CombDesign` / the lowered `CombDesign d'`) and the equation tactic `sv_equations?`.
Steps 2-4 are the RB0 census's own Lean driver (census_lean.py), reused unchanged on records in its format.

Population: every `.sv` file under SV_TESTS/tests/chapter-*/ (public chipsalliance/sv-tests, the `sv-tests` corpus of
extractors/sv/census.py). A file is classified, in funnel order:
  should-fail    its header has `:should_fail_because:` (a negative test: the right answer is a rejection)
  include        it uses `include (multi-file; census.py's skip rule)
  slang-errors   pyslang reports an error
  no-top / multi-top   no module instance at the top, or several and no `:top_module:` header
  extract-fail / extract-loud / extract-clean   the extractor's verdict (Unsupported nodes in the envelope)
then the Lean verdicts of census_lean.py (LOADED / REFUSED, lowered design loud or clean, tactic RECOGNIZED / REFUSED).
The sources are read under `python3.12 -I` and never executed.
"""
import argparse
import concurrent.futures
import glob
import json
import os
import re
import subprocess
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def header(text):
    h = {}
    for k in ("name", "should_fail_because", "top_module", "type", "tags"):
        m = re.search(r"^:%s:\s*(.*)$" % k, text, re.M)
        if m:
            h[k] = m.group(1).strip()
    return h


def slang_tops(path):
    import slang_env
    comp, root, errors, sm = slang_env.compile_files([path])
    return [i.name for i in root.topInstances if i.isModule], errors


def one(path, corpus, repo, out):
    rel = os.path.relpath(path, corpus)
    bid = rel.replace("/", "__")[:-3]
    text = open(path, errors="replace").read()
    h = header(text)
    rec = {"id": bid, "path": rel, "chapter": rel.split("/")[0], "header": h}
    if "should_fail_because" in h:
        rec["stage"] = "should-fail"
        return rec
    if re.search(r"^\s*`include\b", text, re.M):
        rec["stage"] = "include"
        return rec
    try:
        tops, errors = slang_tops(path)
    except Exception as exc:  # noqa: BLE001
        rec.update(stage="slang-exception", error=str(exc)[:200])
        return rec
    rec["slang"] = {"n_errors": len(errors), "errors": errors[:3]}
    if errors:
        rec["stage"] = "slang-errors"
        return rec
    top = h.get("top_module") if h.get("top_module") in tops else (tops[0] if len(tops) == 1 else None)
    if top is None:
        rec["stage"] = "no-top" if not tops else "multi-top"
        rec["tops"] = tops[:5]
        return rec
    rec["top"] = top
    envp = os.path.join(out, bid + ".env.json")
    try:
        p = subprocess.run([sys.executable, "-I", os.path.join(HERE, "run_extract.py"), "--repo", repo, "--",
                            "--top", top, path, "-o", envp], capture_output=True, text=True, timeout=180,
                           cwd=out)
        rc = p.returncode
        err = p.stderr[-300:]
    except subprocess.TimeoutExpired:
        rc, err = "timeout", ""
    rec["extract"] = {"rc": rc, "stderr": err}
    if rc != 0 or not os.path.exists(envp):
        rec["stage"] = "extract-fail"
        return rec
    env = json.load(open(envp))
    kinds = Counter()

    def walk(x):
        if isinstance(x, dict):
            if x.get("kind") in ("Unsupported", "unsupported"):
                kinds[x.get("sv_kind") or x.get("svKind") or "?"] += 1
            for v in x.values():
                walk(v)
        elif isinstance(x, list):
            for v in x:
                walk(v)
    walk(env)
    rec["env_bytes"] = os.path.getsize(envp)
    rec["n_unsupported"] = sum(kinds.values())
    rec["unsupported"] = [{"sv_kind": k, "count": c} for k, c in kinds.most_common()]
    rec["stage"] = "extract-loud" if kinds else "extract-clean"
    return rec


def cmd_extract(a):
    corpus = os.path.abspath(a.corpus)
    files = sorted(glob.glob(os.path.join(corpus, "chapter-*", "**", "*.sv"), recursive=True))
    rec_dir = os.path.join(a.out, "rec")
    os.makedirs(rec_dir, exist_ok=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.j) as ex:
        recs = list(ex.map(lambda f: one(f, corpus, os.path.abspath(a.repo), rec_dir), files))
    for r in recs:
        json.dump(r, open(os.path.join(rec_dir, r["id"] + ".json"), "w"), indent=1)
    print(Counter(r["stage"] for r in recs))


def cmd_report(a):
    rec_dir = os.path.join(a.out, "rec")
    recs = [json.load(open(f)) for f in sorted(glob.glob(os.path.join(rec_dir, "*.json")))
            if not f.endswith(".env.json") and not os.path.basename(f).startswith("lean")]
    lean = {}
    lp = os.path.join(rec_dir, "lean.json")
    if os.path.exists(lp):
        lean = json.load(open(lp))
    rows = []
    for r in recs:
        st = r["stage"]
        lv = lean.get(r["id"], {}) if st == "extract-clean" or st == "extract-loud" else {}
        fin = st
        if st == "extract-clean":
            ld = lv.get("loader")
            if ld == "LOADED":
                fin = "loads, lowered design loud" if lv.get("unsupported") else "loads clean"
                tac = lv.get("tactic") or {}
                if fin == "loads clean" and tac:
                    s = str(tac.get("structure") or tac.get("structure-lowered") or "")
                    e = str(tac.get("equations") or tac.get("equations-lowered") or "")
                    s = "RECOGNIZED" if s.startswith("RECOGNIZED") else "REFUSED"
                    e = "RECOGNIZED" if e.startswith("RECOGNIZED") else "REFUSED"
                    fin = "flat comb design: sv_structure? %s, sv_equations? %s" % (s, e)
                elif fin == "loads clean":
                    fin = "loads clean, not a flat comb design (edge process, hierarchy or initial-only: no tactic)"
            elif ld:
                fin = "extract-clean, loader " + ld
            else:
                fin = "extract-clean, not loaded"
        rows.append({"id": r["id"], "chapter": r.get("chapter"), "stage": st, "final": fin,
                     "unsupported": [u["sv_kind"] for u in r.get("unsupported", [])][:5]})
    funnel = Counter(x["final"] for x in rows)
    by_ch = {}
    for x in rows:
        by_ch.setdefault(x["chapter"], Counter())[x["final"]] += 1
    loud = Counter()
    for r in recs:
        if r["stage"] == "extract-loud":
            for u in r["unsupported"]:
                loud[u["sv_kind"]] += 1
    out = {"schema": "ws4-svtests-path/1", "files": len(rows), "funnel": dict(funnel.most_common()),
           "by_chapter": {k: dict(v) for k, v in sorted(by_ch.items())},
           "extractor_blockers_files": dict(loud.most_common(30)), "rows": rows}
    json.dump(out, open(a.json, "w"), indent=1)
    print(json.dumps({k: out[k] for k in ("files", "funnel")}, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cmd", choices=["extract", "report"])
    ap.add_argument("--corpus")
    ap.add_argument("--repo")
    ap.add_argument("--out", required=True)
    ap.add_argument("--json")
    ap.add_argument("-j", type=int, default=3)
    a = ap.parse_args()
    (cmd_extract if a.cmd == "extract" else cmd_report)(a)


if __name__ == "__main__":
    main()
