"""List every `Unsupported` node of an ls-sv envelope (and its probe sidecar), by module.

usage: python3.12 -I census.py ENVELOPE.json [--json OUT]
Prints: module, file basename, line:col, sv_kind, first line of the text. Also counts by sv_kind.
"""
import collections
import json
import os
import sys


def walk(x, out, mod):
    if isinstance(x, dict):
        if x.get("kind") == "Unsupported":
            sp = x.get("span") or {}
            t = (x.get("text") or "").strip().splitlines()
            out.append({"module": mod, "line": sp.get("line"), "col": sp.get("col"),
                        "sv_kind": x.get("sv_kind"), "text": (t[0] if t else "")[:90]})
        for v in x.values():
            walk(v, out, mod)
    elif isinstance(x, list):
        for v in x:
            walk(v, out, mod)


def main():
    env = json.load(open(sys.argv[1]))
    out = []
    for m in env["design"]["modules"]:
        walk(m, out, m.get("name"))
    for p in env.get("packages") or []:
        if isinstance(p, dict):
            walk(p, out, "pkg:" + str(p.get("name")))
    seen = set()
    rows = []
    for r in out:
        key = (r["module"], r["line"], r["col"], r["sv_kind"])
        if key in seen:
            continue
        seen.add(key)
        rows.append(r)
    for r in rows:
        print(f"  {r['module']}:{r['line']}:{r['col']}  {r['sv_kind']}  | {r['text']}")
    c = collections.Counter(r["sv_kind"] for r in rows)
    print("  BY KIND:", dict(c.most_common()))
    print("  TOTAL distinct:", len(rows))
    if "--json" in sys.argv:
        json.dump(rows, open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1)


main()
