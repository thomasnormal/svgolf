#!/usr/bin/env python3.12
"""run_hack2.py EXTRACTOR : survey files with HACK_ITERS per file; unsupported 'VariableSymbol:signed' declarations of recorded iterators dropped."""
import json, os, subprocess, sys, re, collections, concurrent.futures as cf
S=os.environ["SCRATCH"] + "/"
W=S+'wpproc/'; EXT=sys.argv[1]; OUT=W+'hackout2/'; os.makedirs(OUT,exist_ok=True)
def kinds(j, iters):
    acc=[]; out={'localdecl':0,'packednull':0}
    def w(n):
        if isinstance(n,dict):
            if n.get('kind')=='Unsupported':
                k=n.get('sv_kind') or '?'
                if k=='VariableSymbol:signed' and (n.get('text') or '').strip() in iters: pass
                else: acc.append(k)
            if n.get('kind')=='LocalDecl': out['localdecl']+=1
            if isinstance(n.get('width'),dict) and n['width'].get('kind')=='PackedType' and n['width'].get('packed') is None and n.get('kind') in ('Var','Net','Port'): out['packednull']+=1
            for v in n.values(): w(v)
        elif isinstance(n,list):
            for v in n: w(v)
    w(j); return acc,out
def one(item):
    tag,path,top=item
    out=OUT+tag.replace('/','_')+'.json'; it=out+'.iters'
    if os.path.exists(it): os.remove(it)
    r=subprocess.run(['python3.12',EXT,'--top',top,path,'-o',out],cwd=W+'wt',capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',HACK_ITERS=it),timeout=120)
    if r.returncode: return tag,None
    iters=set(open(it).read().split()) if os.path.exists(it) else set()
    acc,o=kinds(json.load(open(out)),iters); return tag,(acc,o)
res=json.load(open(S+'realres.json'))
items=[]
bad2=lambda k: any(s in k for s in ('Uninstantiated','Invalid','invalid-compilation','unresolved','ModuleDefinition'))
for d,base,st,acc,_ in res:
    if not st.startswith('ok:') or any(bad2(k) for k in acc): continue
    items.append(('surv/'+d+'/'+base,S+f'realworld/{d}/{base}',st.split(':',1)[1]))
with cf.ThreadPoolExecutor(4) as ex: r1=list(ex.map(one,items))
json.dump({'kinds':{t:v for t,v in r1}},open(W+'hack2_survey.json','w'))
G2={'ForLoopStatement','SubroutineSymbol:Subroutine','CallExpression','ExpressionStatement:CallExpression'}
def n(pred): return sum(1 for t,v in r1 if v and pred(v))
print('clean:',n(lambda v:not v[0] and not v[1]['localdecl'] and not v[1]['packednull']),
      ' +localdecl:',n(lambda v:not v[0] and not v[1]['packednull']),
      ' +loop/function kinds allowed:',n(lambda v:set(v[0])<=G2 and not v[1]['packednull']))
kc=collections.Counter()
for t,v in r1:
    if v:
        for k in set(v[0]): kc[k]+=1
print(kc.most_common(10))
