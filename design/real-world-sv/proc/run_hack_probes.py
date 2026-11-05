#!/usr/bin/env python3.12
"""run_hack_probes.py EXTRACTOR.py : extractor-level clean count over the 241 probes (symbolic mode, last module as top)."""
import json, os, subprocess, sys, re, glob, collections, concurrent.futures as cf
W=os.path.dirname(os.path.abspath(__file__))+'/'
P=W+'wt/svgolf/design/real-world-sv/probes/'
EXT=sys.argv[1]
OUT=W+'hackout_probes/'; os.makedirs(OUT,exist_ok=True)
def tops(path):
    t=open(path,encoding='utf-8',errors='replace').read()
    t=re.sub(r"//[^\n]*","",t); t=re.sub(r"/\*.*?\*/","",t,flags=re.S)
    return re.findall(r"^\s*module\s+(?:automatic\s+)?([A-Za-z_][A-Za-z0-9_$]*)",t,flags=re.M)
def kinds(j):
    acc=collections.Counter(); out={'localdecl':0,'packednull':0}
    def w(n):
        if isinstance(n,dict):
            if n.get('kind')=='Unsupported': acc[n.get('sv_kind') or '?']+=1
            if n.get('kind')=='LocalDecl': out['localdecl']+=1
            if isinstance(n.get('width'),dict) and n['width'].get('kind')=='PackedType' and n['width'].get('packed') is None and n.get('kind') in ('Var','Net','Port'): out['packednull']+=1
            for v in n.values(): w(v)
        elif isinstance(n,list):
            for v in n: w(v)
    w(j); return acc,out
def one(f):
    m=tops(f)
    if not m: return os.path.basename(f),None
    out=OUT+os.path.basename(f)+'.json'
    r=subprocess.run(['python3.12',EXT,'--top',m[-1],f,'-o',out],cwd=W+'wt',capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),timeout=120)
    if r.returncode: return os.path.basename(f),None
    a,o=kinds(json.load(open(out))); return os.path.basename(f),(dict(a),o)
with cf.ThreadPoolExecutor(4) as ex: res=list(ex.map(one,sorted(glob.glob(P+'*.sv'))))
G2={'ForLoopStatement','SubroutineSymbol:Subroutine','CallExpression','ExpressionStatement:CallExpression'}
def n(pred): return sum(1 for f,v in res if v and pred(v))
print(sys.argv[1].split('/')[-3] if len(sys.argv[1].split('/'))>3 else sys.argv[1])
print(' probes',len(res),'extracted',n(lambda v:True))
print(' clean (no Unsupported, LocalDecl, packed:null):',n(lambda v:not v[0] and not v[1]['localdecl'] and not v[1]['packednull']))
print(' + LocalDecl allowed:',n(lambda v:not v[0] and not v[1]['packednull']))
print(' + loop/function kinds allowed (upper bound):',n(lambda v:set(v[0])<=G2 and not v[1]['packednull']))
json.dump(res,open(W+'hack_probes_'+os.path.basename(os.path.dirname(os.path.dirname(EXT)))+'.json','w'))
