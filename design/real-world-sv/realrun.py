#!/usr/bin/env python3.12
import sys, os, re, json, subprocess, glob, collections, concurrent.futures as cf
REPO=os.environ["LEAN_SURFACES"]
SP=os.path.dirname(os.path.abspath(__file__))
OUT=SP+"/realout"; os.makedirs(OUT,exist_ok=True)
files=[]
for d in ["clmul","arx","fpdiv","sbox","hashround","bitops","arith","alu"]:
    for f in sorted(glob.glob(f"{SP}/realworld/{d}/*")):
        if f.endswith((".sv",".v",".vh",".svh")) and not f.endswith(".err"):
            files.append((d,f))
def modules(path):
    try: txt=open(path,encoding="utf-8",errors="replace").read()
    except Exception: return []
    txt=re.sub(r"//[^\n]*","",txt); txt=re.sub(r"/\*.*?\*/","",txt,flags=re.S)
    return re.findall(r"^\s*module\s+(?:automatic\s+)?([A-Za-z_][A-Za-z0-9_$]*)",txt,flags=re.M)
def collect(node, acc):
    if isinstance(node, dict):
        if node.get("kind")=="Unsupported": acc.append(node.get("sv_kind") or "?")
        for v in node.values(): collect(v, acc)
    elif isinstance(node, list):
        for v in node: collect(v, acc)
def run(item):
    d,f=item; mods=modules(f); base=os.path.basename(f)
    if not mods: return (d,base,"nomodule",[],None)
    last=None
    for m in mods[-1:]+mods[:-1]:   # try the last module first (usually the top), then the others
        out=f"{OUT}/{d}__{base}__{m}.json"
        try:
            r=subprocess.run(["python3.12",REPO+"/extractors/sv/extract.py","--top",m,f,"-o",out],cwd=REPO,capture_output=True,text=True,timeout=90,env=dict(os.environ,PYTHONDONTWRITEBYTECODE="1"))
        except subprocess.TimeoutExpired:
            last="timeout"; continue
        if r.returncode==0:
            try: j=json.load(open(out))
            except Exception: last="badjson"; continue
            acc=[]; collect(j,acc)
            return (d,base,"ok:"+m,acc,len(mods))
        last=(r.stderr.strip().splitlines() or ["?"])[-1][:160]
    return (d,base,"fail",[],last)
res=[]
with cf.ThreadPoolExecutor(4) as ex:
    for r in ex.map(run,files): res.append(r)
json.dump(res,open(SP+"/realres.json","w"))
print(len(res))
