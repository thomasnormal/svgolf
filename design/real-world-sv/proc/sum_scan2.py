import json, collections, sys
res=[x for x in json.load(open(sys.argv[1])) if 'error' not in x]
def adm_loop(sh):
    return sh['start'] in('literal','param') and sh['bound'] in('literal','param') and sh['cond'] in('LessThan','LessThanEqual','NotEqual','GreaterThan','GreaterThanEqual') and sh['step'] in('inc','dec')
files_loop=0; files_all=0; files_comb=0
detail=[]
for x in res:
    loops=[]; bad=[]
    for b in x['blocks']+x['subs']:
        c=b['counts']
        for n in b['notes']:
            if n[0]=='for': loops.append((n[1],b))
    if not loops: continue
    files_loop+=1
    allok=True; why=set()
    for sh,b in loops:
        c=b['counts']
        if not adm_loop(sh): allok=False; why.add('shape:%s/%s/%s/%s'%(sh['start'],sh['bound'],sh['cond'],sh['step']))
        if c.get('stmt:BreakStatement'): allok=False; why.add('break')
        if c.get('stmt:ReturnStatement'): why.add('return')       # allowed only in functions (Yosys cannot read return anyway)
        if c.get('stmt:WhileLoopStatement') or c.get('stmt:RepeatLoopStatement'): allok=False; why.add('while/repeat')
        if c.get('stmt:TimedStatement'): why.add('timed')
        if c.get('assign:nba'): why.add('nba(seq)')
        if c.get('call:user') or c.get('usercall_expr'): why.add('usercall')
    # styles of the blocks holding loops
    styles=set(b.get('style','function') for sh,b in loops)
    if allok: files_all+=1
    detail.append((x['topic'],x['file'],len(loops),sorted(styles),sorted(why),allok))
print('files with for loops:',files_loop,' all loops admitted-shape and no break/while:',files_all)
sty=collections.Counter()
for d in detail:
    for s in d[3]: sty[s]+=1
print('block styles holding loops (files):',sty)
comb=[d for d in detail if all(s in ('AlwaysComb','always@ImplicitEventControl','gen:AlwaysComb') or s.startswith('gen:Always') for s in d[3])]
print('files whose loops are all in comb-style blocks (always_comb/@*/function/gen always):',len(comb))
import itertools
for d in detail[:70]:
    print(d)
