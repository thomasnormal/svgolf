import json, glob, os, sys, collections
def scan(path):
    j=json.load(open(path)); out={'localdecl':0,'packednull':0,'unsup':collections.Counter()}
    def w(n):
        if isinstance(n,dict):
            if n.get('kind')=='LocalDecl': out['localdecl']+=1
            if n.get('kind')=='Unsupported': out['unsup'][n.get('sv_kind')]+=1
            if isinstance(n.get('width'),dict) and n['width'].get('kind')=='PackedType' and n['width'].get('packed') is None and n.get('kind') in ('Var','Net','Port'): out['packednull']+=1
            for v in n.values(): w(v)
        elif isinstance(n,list):
            for v in n: w(v)
    w(j); return out
def run(d):
    res={}
    for f in sorted(glob.glob(d+'/*.json')):
        if f.endswith('.env.json'): continue
        r=json.load(open(f)); i=r['id']
        if '@' in i: continue
        ok = r['extract']['rc']==0 and r['slang']['n_errors']==0 if 'slang' in r else False
        env=f[:-5]+'.env.json'
        if r['extract']['rc']!=0 or not os.path.exists(env): res[i]=('FAIL',None); continue
        s=scan(env)
        res[i]=('ok' if r['slang']['n_errors']==0 else 'slangerr',s)
    return res
a=run(sys.argv[1]); 
def clean(v): 
    return v[0]=='ok' and not v[1]['unsup'] and not v[1]['localdecl'] and not v[1]['packednull']
print(sys.argv[1],'blocks',len(a),'extracted',sum(1 for v in a.values() if v[1]),'clean',sum(1 for v in a.values() if clean(v)),
      'no-unsupported(any slang)',sum(1 for v in a.values() if v[1] and not v[1]['unsup'] and not v[1]['packednull']))
json.dump({k:(v[0],{'localdecl':v[1]['localdecl'],'packednull':v[1]['packednull'],'unsup':dict(v[1]['unsup'])} if v[1] else None) for k,v in a.items()},open(sys.argv[1]+'_summary.json','w'))
