#!/usr/bin/env python3.12
import json, subprocess, sys, os, concurrent.futures as cf
S=os.environ["SCRATCH"] + "/"
W=S+'wpproc/'
r=json.load(open(S+'realres.json'))
ok=[x for x in r if x[2].startswith('ok:')]
bad2=lambda k: any(s in k for s in ('Uninstantiated','Invalid','invalid-compilation','unresolved','ModuleDefinition'))
sc=[x for x in ok if not any(bad2(k) for k in x[3])]
def run(x):
    d,base,st,acc,_=x; top=st.split(':',1)[1]
    p=f"{S}realworld/{d}/{base}"
    try:
        o=subprocess.run(['python3.12',W+'scan_proc.py',p,top],capture_output=True,text=True,timeout=120,cwd=W)
        if o.returncode: return {'file':base,'topic':d,'error':o.stderr[-200:]}
        j=json.loads(o.stdout.strip().splitlines()[-1]); j['topic']=d; j['file']=base; return j
    except Exception as e:
        return {'file':base,'topic':d,'error':str(e)[:200]}
with cf.ThreadPoolExecutor(4) as ex: res=list(ex.map(run,sc))
json.dump(res,open(W+'scan_survey.json','w'))
print(len(res), sum(1 for x in res if 'error' in x))
