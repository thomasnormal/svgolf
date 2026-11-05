#!/usr/bin/env python3
"""X6 step 3: aggregate the Lean batch output into x6.json and the report tables.

    python3 x6_report.py --index OUT/index.json --tsv 'OUT/lean_*.tsv' --out x6.json

Units: a DESIGN (census block or reference), a POINT (one parameter assignment), an ENTRY (one probe verdict: the top at
the point, or one instance of the hierarchy at the overrides it receives there). Verdict kinds are Probe2.lean's
(`agree`, `differ`, `unconfirmed`, `metaDiffer`, `frontendRejects`, `refused`) plus `parseError` (the Lean envelope parser
rejects the envelope itself: no point is examined). A DIVERGENCE is `differ` or `metaDiffer`: Lean's elaboration at the
point and slang's at the point disagree on a value (a width, a sign, an enum or constant value, a declaration, a
generate count). `refused` is a coverage gap of the Lean elaborator, `frontendRejects` a point slang itself rejects.
"""
import argparse
import glob
import json
import re
from collections import Counter, defaultdict

DIVERGE = ("differ", "metaDiffer")


def classify(kind, msg):
    m = msg
    if kind == "differ":
        if "resize" in m:
            return "context width (a resize the default point does not need)"
        if "declaration count" in m:
            return "declaration count"
        if re.search(r"decl(aration)? '[^']*'.*width|width", m):
            return "declared width"
        if "signed" in m.lower() or "scmp" in m or "resizeSigned" in m:
            return "signedness"
        if "lit" in m:
            return "constant value"
        return "other value"
    if kind == "metaDiffer":
        if "generate" in m:
            return "generate count"
        if "localparam" in m:
            return "localparam value"
        if "param" in m:
            return "parameter value"
        if "decl" in m:
            return "declared width"
        return "other metadata"
    if kind == "refused":
        mm = re.sub(r"'[^']*'", "'X'", m)
        mm = re.sub(r"[0-9]+", "N", mm)
        return mm[:110]
    if kind == "parseError":
        return re.sub(r'"[^"]*"', '"X"', m.split(": ")[-1])[:110]
    return ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--index", required=True)
    ap.add_argument("--tsv", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    idx = {r["id"]: r for r in json.load(open(a.index))}
    entries = []
    for f in sorted(glob.glob(a.tsv)):
        for line in open(f, encoding="utf-8", errors="replace"):
            parts = line.rstrip("\n").split("\t")
            if len(parts) < 4 or parts[0] != "X6":
                continue
            _, did, label, kind = parts[:4]
            msg = parts[4] if len(parts) > 4 else ""
            point, _, entry = label.partition(" ")
            entries.append({"design": did, "point": point, "entry": entry or "-", "kind": kind,
                            "class": classify(kind, msg), "msg": msg[:400]})
    seen = {e["design"] for e in entries}
    designs = [r for r in idx.values() if r.get("sidecar")]
    missing = sorted(r["id"] for r in designs if r["id"] not in seen)
    by_design = defaultdict(list)
    for e in entries:
        by_design[e["design"]].append(e)

    def dsum(rows):
        kinds = Counter(e["kind"] for e in rows)
        pts = defaultdict(set)
        for e in rows:
            pts[e["point"]].add(e["kind"])
        return kinds, pts
    per = []
    for d, rows in sorted(by_design.items()):
        kinds, pts = dsum(rows)
        r = idx.get(d, {})
        per.append({"design": d, "kind": r.get("kind"), "census_loader": r.get("loader"), "status": r.get("status"),
                    "params": r.get("params") or [], "points": len(r.get("points") or []),
                    "point_list": r.get("points") or [],
                    "entries": dict(kinds),
                    "points_diverging": sorted(p for p, ks in pts.items() if ks & set(DIVERGE)),
                    "points_all_agree": sorted(p for p, ks in pts.items() if ks == {"agree"})})
    def point_outcome(rows):
        ks = {e["kind"] for e in rows}
        tops = {e["kind"] for e in rows if e["entry"] == "top"}
        if ks & set(DIVERGE):
            return "diverges"
        if ks == {"agree"}:
            return "agrees (top and every instance)"
        if "frontendRejects" in tops:
            return "slang rejects the point"
        if "refused" in tops:
            return "Lean cannot bring the envelope to the point (refused)"
        if "unconfirmed" in ks:
            return "unconfirmed (one side loud)"
        if "agree" in tops:
            return "top agrees, an instance refused/rejected"
        return "other: " + ",".join(sorted(ks))
    point_rows = defaultdict(list)
    for e in entries:
        if e["kind"] != "parseError":
            point_rows[(e["design"], e["point"])].append(e)
    parse_err = {e["design"] for e in entries if e["kind"] == "parseError"}
    pts_by = {"census": Counter(), "reference": Counter()}
    for (d, pt), rows in point_rows.items():
        pts_by[idx.get(d, {}).get("kind", "census")][point_outcome(rows)] += 1
    for d in parse_err:
        pts_by[idx.get(d, {}).get("kind", "census")]["envelope not parsed by Lean (all its points)"] += \
            len(idx.get(d, {}).get("points") or [])
    summary = {
        "points_by_outcome": {k: dict(v) for k, v in pts_by.items()},
        "designs_by_kind": dict(Counter(r.get("kind") for r in designs)),
        "designs_extracted": len(designs),
        "designs_with_lean_output": len(by_design),
        "designs_missing_lean_output": missing,
        "points_probed": sum(len(r.get("points") or []) for r in designs),
        "entries": len(entries),
        "entries_by_kind": dict(Counter(e["kind"] for e in entries)),
        "designs_by_outcome": dict(Counter(
            "parseError" if p["entries"].get("parseError") else
            "diverges at some point" if p["points_diverging"] else
            "all examined points agree" if p["points_all_agree"] and not any(
                k not in ("agree",) for k in p["entries"]) else
            "agree where examined, refused/rejected elsewhere" if p["points_all_agree"] else
            "no point examined (refused / rejected everywhere)" for p in per)),
        "divergence_classes": dict(Counter(e["class"] for e in entries if e["kind"] in DIVERGE)),
        "refusal_classes": dict(Counter(e["class"] for e in entries if e["kind"] == "refused").most_common(25)),
        "parse_error_classes": dict(Counter(e["class"] for e in entries if e["kind"] == "parseError")),
        "loaded_at_default_but_diverging": sorted(p["design"] for p in per
                                                  if p["census_loader"] == "LOADED" and p["points_diverging"]),
    }
    json.dump({"schema": "ws4-x6/1", "summary": summary, "designs": per,
               "divergences": [e for e in entries if e["kind"] in DIVERGE],
               "entries_compact": [[e["design"], e["point"], e["entry"], e["kind"], e["class"]] for e in entries]},
              open(a.out, "w"), indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
