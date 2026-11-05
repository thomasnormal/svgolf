#!/usr/bin/env python3.12
"""Reach of the WP-PROC lowerings on the survey's 241 reduced probes (extractor-level, same tier model as reach_refined.py)."""
import json, os, subprocess, sys, glob, collections, re, concurrent.futures as cf
W=os.path.dirname(os.path.abspath(__file__))+'/'
P=W+'wt/svgolf/design/real-world-sv/probes/'
files=sorted(glob.glob(P+'*.sv'))
def tops(path):
    t=open(path,encoding='utf-8',errors='replace').read()
    t=re.sub(r"//[^\n]*","",t); t=re.sub(r"/\*.*?\*/","",t,flags=re.S)
    return re.findall(r"^\s*module\s+(?:automatic\s+)?([A-Za-z_][A-Za-z0-9_$]*)",t,flags=re.M)
def kinds(j):
    acc=[]; out={'localdecl':0,'packednull':0}
    def w(n):
        if isinstance(n,dict):
            if n.get('kind')=='Unsupported': acc.append(n.get('sv_kind') or '?')
            if n.get('kind')=='LocalDecl': out['localdecl']+=1
            if isinstance(n.get('width'),dict) and n['width'].get('kind')=='PackedType' and n['width'].get('packed') is None and n.get('kind') in ('Var','Net','Port'): out['packednull']+=1
            for v in n.values(): w(v)
        elif isinstance(n,list):
            for v in n: w(v)
    w(j); return set(acc),out
def run(f):
    m=tops(f)
    if not m: return (f,None,'nomodule')
    out=W+'ex/probe_'+os.path.basename(f)+'.json'
    r=subprocess.run(['python3.12',W+'wt/extractors/sv/extract.py','--top',m[-1],f,'-o',out],cwd=W+'wt',capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
    if r.returncode: return (f,None,'extract-fail: '+r.stderr.strip()[-80:])
    k,o=kinds(json.load(open(out)))
    sc=subprocess.run(['python3.12',W+'scan_proc.py',f,m[-1]],capture_output=True,text=True,cwd=W)
    s=None
    if sc.returncode==0:
        try: s=json.loads(sc.stdout.strip().splitlines()[-1])
        except Exception: pass
    return (f,(k,o,s),'ok')
with cf.ThreadPoolExecutor(4) as ex: res=list(ex.map(run,files))
json.dump([(os.path.basename(f),[sorted(d[0]),d[1],d[2]] if d else None,st) for f,d,st in res],open(W+'probe_scan.json','w'))
print(len(res), collections.Counter(st.split(':')[0] for f,d,st in res))
