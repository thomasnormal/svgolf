#!/usr/bin/env python3
"""Concatenate tasks/fdivp/{DpM,DpQ,DpR,DpS,DpT,DpU}.lean into one file (imports merged) so ONE Lean run reports every error."""
import os, re
W=os.path.join(os.environ["SCRATCH"], 'wph3/wt/svgolf/tasks/fdivp/')
mods=['DpM','DpQ','DpR','DpS','DpT','DpU']
imports=['import tasks.fdivp.CertF','import tasks.fdivp.DpN','import tasks.fdivp.Spec']
body=''
for m in mods:
    s=open(W+m+'.lean').read()
    s=re.sub(r'^import .*\n','',s,flags=re.M)
    body+=f'\n/- ===== {m} ===== -/\n'+s
open(W+'DpAll.lean','w').write('\n'.join(imports)+'\n'+body)
print(len(body.split('\n')),'lines')
