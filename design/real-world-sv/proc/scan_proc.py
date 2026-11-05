#!/usr/bin/env python3.12
"""scan_proc.py FILE.sv [TOP]: statement census of every procedural block / subroutine of TOP's hierarchy (pyslang, default point).
Prints one JSON line. Used for the WP-PROC reach measurement; read-only."""
import sys, os, re, json, collections
import pyslang
from pyslang import ast, syntax

def tops(text):
    t=re.sub(r"//[^\n]*","",text); t=re.sub(r"/\*.*?\*/","",t,flags=re.S)
    return re.findall(r"^\s*module\s+(?:automatic\s+)?([A-Za-z_][A-Za-z0-9_$]*)",t,flags=re.M)

def compile_(path, top, incdirs=()):
    sm=pyslang.SourceManager()
    for d in incdirs: sm.addUserDirectories(d)
    text=open(path,encoding="utf-8",errors="replace").read()
    tree=syntax.SyntaxTree.fromText(text, sm, os.path.realpath(path))
    opts=ast.CompilationOptions(); opts.topModules={top}
    comp=ast.Compilation(pyslang.Bag([opts])); comp.addSyntaxTree(tree)
    errs=[d for d in comp.getAllDiagnostics() if d.isError()]
    return comp, errs

class Census:
    def __init__(self): self.c=collections.Counter(); self.notes=[]
    def add(self,k): self.c[k]+=1

_COMP=[None]
_SCOPE=[None]
def const_val(e):
    try:
        if type(e).__name__=='IntegerLiteral':
            return int(e.value)
        cv=e.constant
        if cv is None and _SCOPE[0] is not None:
            cv=e.eval(ast.EvalContext(_SCOPE[0]))
        if cv is not None and cv.isInteger(): return int(cv.value)
    except Exception: pass
    return None

def expr_kind(e): return type(e).__name__

def mentions_param(e):
    out=[False]
    def f(n):
        if type(n).__name__=='NamedValueExpression':
            try:
                if str(n.symbol.kind).endswith('Parameter'): out[0]=True
            except Exception: pass
    try: e.visit(f)
    except Exception: pass
    return out[0]

def strip_conv(x):
    while expr_kind(x) in ('ConversionExpression',): x=x.operand
    return x

def classify_for(s, cen):
    """Normalized loop shape: var name, start (literal|param|other), cond op, bound (literal|param|other), step (inc|dec|stride|other)."""
    var=None; init=None; declared=False
    try: lv=list(s.loopVars)
    except Exception: lv=[]
    inits=list(s.initializers)
    if lv:
        declared=True; var=lv[0].name
        ini=getattr(lv[0],'initializer',None)
        init=ini
    elif len(inits)==1 and expr_kind(inits[0])=='AssignmentExpression':
        l=strip_conv(inits[0].left)
        if expr_kind(l)=='NamedValueExpression': var=l.symbol.name; init=inits[0].right
    def cls(e):
        if e is None: return 'none'
        e=strip_conv(e)
        cv=const_val(e)
        if cv is not None: return 'param' if mentions_param(e) else 'literal'
        return 'param' if mentions_param(e) else 'other'
    shape={'declared_var':declared,'ninit':len(lv)+len(inits)}
    shape['start']=cls(init) if var else 'other'
    shape['start_val']=const_val(strip_conv(init)) if init is not None else None
    cond=s.stopExpr; cf='other'; bound='other'
    if cond is not None and expr_kind(strip_conv(cond))=='BinaryExpression':
        c=strip_conv(cond); op=str(c.op).split('.')[-1]
        def isvar(x):
            x=strip_conv(x); return expr_kind(x)=='NamedValueExpression' and x.symbol.name==var
        if isvar(c.left) and op in ('LessThan','LessThanEqual','NotEqual','GreaterThan','GreaterThanEqual'):
            cf=op; bound=cls(c.right)
        elif isvar(c.right): cf='rev:'+op; bound=cls(c.left)
    shape['cond']=cf; shape['bound']=bound
    steps=list(s.steps); sf='other'
    if len(steps)==1:
        st=steps[0]; k=expr_kind(st)
        if k=='UnaryExpression':
            sf={'Postincrement':'inc','Preincrement':'inc','Postdecrement':'dec','Predecrement':'dec'}.get(str(st.op).split('.')[-1],'other')
        elif k=='AssignmentExpression':
            l=strip_conv(st.left)
            if expr_kind(l)=='NamedValueExpression' and l.symbol.name==var:
                if st.isCompound:
                    op=str(st.op).split('.')[-1]; cv=const_val(st.right)
                    sf=('inc' if (op=='Add' and cv==1) else 'dec' if (op=='Subtract' and cv==1) else 'stride') if cv is not None else 'other'
                else:
                    r=strip_conv(st.right)
                    if expr_kind(r)=='BinaryExpression':
                        op=str(r.op).split('.')[-1]; a,b=strip_conv(r.left),strip_conv(r.right)
                        va=expr_kind(a)=='NamedValueExpression' and a.symbol.name==var
                        vb=expr_kind(b)=='NamedValueExpression' and b.symbol.name==var
                        other=b if va else a if vb else None
                        cv=const_val(other) if other is not None else None
                        if (va or vb) and cv is not None:
                            sf='inc' if (op=='Add' and cv==1) else 'dec' if (op=='Subtract' and cv==1 and va) else 'stride'
    shape['step']=sf
    shape['uses_break']=False
    return shape

def walk_stmt(s, cen, ctx):
    if s is None: return
    k=type(s).__name__
    cen.add('stmt:'+k)
    if k=='BlockStatement':
        walk_stmt(s.body, cen, ctx)
    elif k=='StatementList':
        for x in s.list: walk_stmt(x, cen, ctx)
    elif k=='ForLoopStatement':
        sh=classify_for(s, cen)
        cen.notes.append(('for',sh))
        walk_stmt(s.body, cen, ctx+['for'])
    elif k in ('ConditionalStatement',):
        walk_stmt(s.ifTrue, cen, ctx); walk_stmt(s.ifFalse, cen, ctx)
    elif k=='CaseStatement':
        for it in s.items: walk_stmt(it.stmt, cen, ctx)
        walk_stmt(s.defaultCase, cen, ctx)
    elif k in ('WhileLoopStatement','DoWhileLoopStatement','RepeatLoopStatement','ForeverLoopStatement','ForeachLoopStatement'):
        walk_stmt(s.body, cen, ctx+[k])
    elif k=='TimedStatement':
        walk_stmt(s.stmt, cen, ctx)
    elif k=='ExpressionStatement':
        e=s.expr; ek=expr_kind(e)
        if ek=='AssignmentExpression':
            cen.add('assign:'+('compound' if e.isCompound else ('nba' if e.isNonBlocking else 'blocking')))
            cen.add('lhs:'+expr_kind(e.left))
        elif ek=='CallExpression':
            sub=e.subroutine
            cen.add('call:'+('system' if e.isSystemCall else 'user'))
        elif ek=='UnaryExpression':
            cen.add('incdec')
        else: cen.add('expr:'+ek)
    elif k=='VariableDeclStatement':
        cen.add('localdecl')
    elif k=='ReturnStatement':
        cen.add('return')

def collect_calls(e, cen):
    def f(n):
        if type(n).__name__=='CallExpression' and not n.isSystemCall:
            cen.add('usercall_expr')
    try: e.visit(f)
    except Exception: pass

def scan_instance(inst, out):
    body=inst.body
    _SCOPE[0]=body
    for m in body:
        k=str(m.kind).split('.')[-1]
        if k=='ProceduralBlock':
            cen=Census(); pk=str(m.procedureKind).split('.')[-1]
            st=m.body
            style=pk
            if pk=='Always' and type(st).__name__=='TimedStatement':
                tn=type(st.timing).__name__
                style='always@'+tn
                walk_stmt(st.stmt, cen, [])
            else:
                walk_stmt(st, cen, [])
            out['blocks'].append({'style':style,'counts':dict(cen.c),'notes':cen.notes})
        elif k=='Subroutine':
            cen=Census()
            walk_stmt(m.body, cen, [])
            out['subs'].append({'name':m.name,'kind':str(m.subroutineKind).split('.')[-1],'counts':dict(cen.c),'notes':cen.notes,
                                'nargs':len(list(m.arguments)),
                                'argdirs':sorted(set(str(a.direction).split('.')[-1] for a in m.arguments)),
                                'automatic':str(m.defaultLifetime).split('.')[-1]})
        elif k in ('Net',):
            out['nets']+=1
        elif k=='Instance':
            scan_instance(m, out)
        elif k in ('GenerateBlock',):
            scan_scope(m, out)
        elif k=='GenerateBlockArray':
            for e in m.entries: scan_scope(e,out)

def scan_scope(blk, out):
    for m in blk:
        k=str(m.kind).split('.')[-1]
        if k=='ProceduralBlock':
            cen=Census(); walk_stmt(m.body, cen, []); out['blocks'].append({'style':'gen:'+str(m.procedureKind).split('.')[-1],'counts':dict(cen.c),'notes':cen.notes})
        elif k=='Instance': scan_instance(m,out)
        elif k=='GenerateBlock': scan_scope(m,out)
        elif k=='GenerateBlockArray':
            for e in m.entries: scan_scope(e,out)

def main():
    path=sys.argv[1]; text=open(path,encoding="utf-8",errors="replace").read()
    top=sys.argv[2] if len(sys.argv)>2 else tops(text)[-1]
    incd=[os.path.dirname(os.path.abspath(path))]
    comp,errs=compile_(path, top, incd); _COMP[0]=comp
    out={'file':path,'top':top,'nerr':len(errs),'blocks':[],'subs':[],'nets':0}
    for ti in comp.getRoot().topInstances:
        scan_instance(ti, out)
    print(json.dumps(out))
if __name__=='__main__': main()
