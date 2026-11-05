#!/usr/bin/env python3.12
"""Probe runner: extractor (symbolic mode) + yosys on one .sv file. Writes only under the scratchpad."""
import sys, os, json, subprocess, re
REPO=os.environ["LEAN_SURFACES"]
SP=os.path.join(os.environ["SCRATCH"], "probes")
def unsup(node, acc):
    if isinstance(node, dict):
        if node.get("kind")=="Unsupported" or str(node.get("kind","")).startswith("Unsupported"):
            acc.append((node.get("construct") or node.get("reason") or node.get("slang_kind") or node.get("what"), str(node.get("text") or node.get("source") or "")[:80], {k:v for k,v in node.items() if k not in ("span",)}))
        for v in node.values(): unsup(v, acc)
    elif isinstance(node, list):
        for v in node: unsup(v, acc)
def main(path, top):
    out = os.path.join(SP, os.path.basename(path)+".json")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    r = subprocess.run(["python3.12", REPO+"/extractors/sv/extract.py", "--top", top, path, "-o", out], cwd=REPO, capture_output=True, text=True, env=env)
    ext = "EXTRACT-ERR: "+r.stderr.strip()[:400] if r.returncode else "extract ok"
    uns=[]
    if not r.returncode:
        j=json.load(open(out)); unsup(j, uns)
    y = subprocess.run(["yosys","-q","-p","read_verilog -sv %s; hierarchy -top %s; proc; opt_clean; stat" % (path, top)], capture_output=True, text=True)
    ys = "yosys ok" if y.returncode==0 else "YOSYS-ERR: "+ (y.stderr.strip().splitlines() or y.stdout.strip().splitlines() or [""])[-1][:300]
    print("%-28s %s | %s" % (os.path.basename(path), ext, ys))
    seen=set()
    for u in uns:
        key=str(u[0])+"|"+str(u[2].get('reason') or '')
        if key in seen: continue
        seen.add(key)
        print("      UNSUP:", json.dumps(u[2])[:300])
if __name__=="__main__":
    main(sys.argv[1], sys.argv[2])
