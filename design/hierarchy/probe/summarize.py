# WP-I probe helper: list the modules, the instances and every Unsupported node of an sv-0.2 envelope.
# usage: python3 summarize.py ENVELOPE.json
import json,sys
d=json.load(open(sys.argv[1]))
ms=d['design']['modules']
def find(o,pred,path='',acc=None):
    if acc is None: acc=[]
    if isinstance(o,dict):
        if pred(o): acc.append((path,o))
        for k,v in o.items(): find(v,pred,path+'/'+k,acc)
    elif isinstance(o,list):
        for i,v in enumerate(o): find(v,pred,path+f'[{i}]',acc)
    return acc
print("modules:",[m['name'] for m in ms],"others:",d['design'].get('others'))
for m in ms:
    for p,o in find(m,lambda o:o.get('kind')=='Unsupported'):
        print(f"  [{m['name']}] UNSUPPORTED {p}: {o.get('sv_kind')} | {str(o.get('text'))[:90]}")
    for p,o in find(m,lambda o:o.get('kind')=='Instance'):
        print(f"  [{m['name']}] INSTANCE {o['name']} of {o['module']} params={[ (q['name']) for q in o.get('params',[])]} nconns={len(o.get('ports',[]))}")
    if m.get('others'): print(f"  [{m['name']}] others:", json.dumps(m['others'])[:300])
