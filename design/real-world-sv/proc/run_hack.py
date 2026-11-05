#!/usr/bin/env python3.12
"""Run the HACKED scratch extractor (G1-style upper-bound hack, never committed) over the survey files and the probes; count the
files that come out with no Unsupported node, no LocalDecl and no packed:null declaration."""
import json, os, subprocess, sys, re, glob, collections, concurrent.futures as cf
S=os.environ["SCRATCH"] + "/"
W=S+'wpproc/'
EXT=W+'hack_extractors/sv/extract.py' if len(sys.argv)<2 else sys.argv[1]
OUT=W+'hackout/'; os.makedirs(OUT,exist_ok=True)
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
    w(j); return acc,out
def one(item):
    tag,path,top=item
    out=OUT+tag.replace('/','_')+'.json'
    r=subprocess.run(['python3.12',EXT,'--top',top,path,'-o',out],cwd=W+'wt',capture_output=True,text=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),timeout=120)
    if r.returncode: return tag,None
    acc,o=kinds(json.load(open(out)))
    return tag,(acc,o)
def main():
    items=[]
    res=json.load(open(S+'realres.json'))
    ok=[x for x in res if x[2].startswith('ok:')]
    bad2=lambda k: any(s in k for s in ('Uninstantiated','Invalid','invalid-compilation','unresolved','ModuleDefinition'))
    for d,base,st,acc,_ in ok:
        if any(bad2(k) for k in acc): continue
        items.append(('surv/'+d+'/'+base,S+f'realworld/{d}/{base}',st.split(':',1)[1]))
    with cf.ThreadPoolExecutor(4) as ex: r1=list(ex.map(one,items))
    clean=[t for t,v in r1 if v and not v[0] and not v[1]['localdecl'] and not v[1]['packednull']]
    nounsup=[t for t,v in r1 if v and not v[0]]
    print('survey files',len(items),'extracted',sum(1 for t,v in r1 if v),'no Unsupported',len(nounsup),'clean (no Unsupported/LocalDecl/packednull)',len(clean))
    kc=collections.Counter()
    for t,v in r1:
        if v:
            for k in set(v[0]): kc[k]+=1
    print(kc.most_common(15))
    json.dump({'clean':clean,'kinds':{t:v for t,v in r1}},open(W+'hack_survey.json','w'))

if __name__=='__main__':
    main()
