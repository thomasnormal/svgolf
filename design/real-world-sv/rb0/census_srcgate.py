#!/usr/bin/env python3.12
"""WP-RB0 census: the verdict of svGolf's SOURCE GATE (svgolf/score/srcgate.py) on each block's PRIMARY file
as it is written (the checker reads exactly one file and refuses every directive but `timescale and
`default_nettype, attributes, unique/priority, pragma comments, x/z literals, host access).

    python3.12 census_srcgate.py --src SRCROOT --out OUTDIR [--blocks corpus.json] [--repo REPO_ROOT]

Writes OUTDIR/srcgate.json: id -> {primary, ok, n_findings, categories{...}, first}. This is NOT part of the
ls-sv question (ls-sv's own extractor takes several files and -I); it measures the svGolf path's
"one file, one design, no directives" contract on real code.
"""
import argparse
import collections
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def category(msg):
    m = msg.lower()
    for key, pat in (("directive/macro/include", r"compiler directive|macro|preprocessor-skipped"),
                     ("attribute", r"attribute"), ("unique/priority", r"qualifier"),
                     ("x/z literal", r"x/z|literal"), ("pragma comment", r"pragma"),
                     ("host access", r"host access|escaped identifier|dpi"),
                     ("encoding", r"not utf|character|outside a comment")):
        if re.search(pat, m):
            return key
    return "other"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--blocks", default=os.path.join(HERE, "corpus.json"))
    ap.add_argument("--repo", default=os.path.abspath(os.path.join(HERE, "..", "..", "..", "..")))
    a = ap.parse_args()
    sys.path.insert(0, os.path.join(a.repo, "svgolf", "score"))
    import srcgate
    res = {}
    for b in json.load(open(a.blocks)):
        prim = b["files"][-1]
        p = os.path.join(a.src, "files", b["project"], prim)
        if not os.path.exists(p):
            continue
        if os.path.getsize(p) > 1_000_000:       # the gate's Python scanner is quadratic-ish: a 9.5 MB file ran > 7 min
            res[b["id"]] = {"primary": prim, "ok": None, "skipped": "primary file > 1 MB (not measured)"}
            continue
        canon, findings = srcgate.gate_file(p, name=os.path.basename(prim))
        cats = collections.Counter(category(f) for f in findings)
        res[b["id"]] = {"primary": prim, "ok": canon is not None, "n_findings": len(findings),
                        "categories": dict(cats), "first": findings[0][:200] if findings else None}
    json.dump(res, open(os.path.join(a.out, "srcgate.json"), "w"), indent=1, sort_keys=True)
    print(sum(1 for v in res.values() if v["ok"]), "of", sum(1 for v in res.values() if v["ok"] is not None), "measured primary files pass the source gate as written")
    tot = collections.Counter()
    for v in res.values():
        for k in v.get("categories", {}):
            tot[k] += 1
    print(dict(tot))


main()
