import sys
sys.path.insert(0, '../probe')
from model import *
res = parse(open(sys.argv[1] if len(sys.argv) > 1 else 'xrun5.out').read())
def tn(x): return x
def expect(name, s):
    g = s.get
    if name == 'wpg_if_x':
        c, a, b, v = g('c'), g('a'), g('b'), g('v')
        return dict(y1=a if cond_true(c) else b, y2=a if cond_true(v) else b,
                    y3=a if cond_true(lnot(c)) else b, y4=b if cond_true(c) else a,
                    y5=a if cond_true(bnot(c)) else b)
    if name == 'wpg_if_chain':
        c1, c2, a, b, d = g('c1'), g('c2'), g('a'), g('b'), g('d')
        return dict(y=a if cond_true(c1) else (b if cond_true(c2) else d),
                    z=(a if cond_true(c2) else b) if cond_true(c1) else d,
                    w=a if cond_true(c1) else '0',
                    u=a if cond_true(c1) else b, v=b if cond_true(c1) else a)
    if name == 'wpg_tern_x':
        c, v, a, b, d, e = g('c'), g('v'), g('a'), g('b'), g('d'), g('e')
        return dict(t1=ternary(c, a[-1], b[-1]), t4=ternary(c, a, b), tv=ternary(v, a, b),
                    tn=ternary(c, a[-1], ternary(d, b[-1], e)), tp=ternary(c, a, b))
    if name == 'wpg_not':
        a, v = g('a'), g('v')
        return dict(n1=lnot(a), b1=bnot(a), n4=zext(lnot(a), 4), b4=bnot(zext(a, 4)),
                    nl=lnot(v), nb=bnot(v), nl4=zext(lnot(v), 4), nb4=bnot(zext(v, 4)),
                    nn=lnot(lnot(v)), nr=lnot(bnot(v)))
    if name == 'wpg_tern_ctx':
        return dict(y=ternary(g('c'), bnot(zext(g('a'), 4)), '0000'))
    if name == 'wpg_order':
        t = bxor(g('a'), g('b')); return dict(y=g('b'), z=band(t, g('c')))
    if name == 'wpg_carry':
        p, c, a = g('p'), g('c'), g('a')
        co = c if cond_true(p) else a
        return dict(co=co, s=bxor(p, c), co1=co)
    if name == 'wpg_local':
        t = bxor(g('a'), g('b')); return dict(y=band(t, g('c')))
    if name == 'wpg_red':
        v = g('v')
        ro = red_or(v); ra = red_and(v); rx = red_xor(v)
        return dict(ro=ro, ra=ra, rx=rx, rno=bnot(ro), rna=bnot(ra), rnx=bnot(rx))
    if name == 'wpg_logic':
        a, b, v, w = g('a'), g('b'), g('v'), g('w')
        nb = lnot(b)
        return dict(la=land(a, b), lo=lor(a, b), lva=land(v, w), lvo=lor(v, w), lm=land(a, nb), ln=lnot(lor(a, b)))
    raise KeyError(name)
bad = tot = 0
for name, rows in res.items():
    if name == 'wpg_partial':
        exps = run_partial(rows)
        for k, (kv, e) in enumerate(zip(rows, exps)):
            tot += 1
            if kv['y'] != e['y']: bad += 1; print('MISMATCH', name, k, kv, e)
        continue
    for k, kv in enumerate(rows):
        e = expect(name, kv)
        tot += 1
        for o, val in e.items():
            if kv[o] != val: bad += 1; print('MISMATCH', name, k, o, 'xc', kv[o], 'model', val, kv)
print(tot, 'cycles', bad, 'mismatches')
