#!/usr/bin/env python3
"""rank table for design/fdiv-param/h2/fdiv16_t0.sv: depth of every plain site (module-level assign / always_comb),
the generate loop g_div hand-coded (rem[i] chain). prints Lean `pr` as a List and the loop rank rule."""
import re, sys
src = open(sys.argv[1]).read()
src = re.sub(r'//[^\n]*', '', src)
# remove the generate loop, remember it
loop = re.search(r'for \(genvar i.*?\n  end\n', src, re.S)
src_noloop = src.replace(loop.group(0), '')
sites = []   # (targets, reads)
ident = re.compile(r'[A-Za-z_]\w*')
kw = set('assign always_comb begin end if else q logic input output module endmodule localparam integer'.split())
decl_names = set(re.findall(r'\b(?:logic)\s*(?:\[[^\]]*\](?:\[[^\]]*\])?)?\s*([A-Za-z_][\w, ]*);', src_noloop))
body = src_noloop
# statements: assigns
stmts = re.findall(r'assign\s+([A-Za-z_]\w*)(?:\[[^\]]*\])?\s*=\s*([^;]*);', body)
# always_comb is last: target q, reads all names in the block
ac = re.search(r'always_comb begin(.*?)\n  end\n', body, re.S)
names_sig = set()
for m in re.finditer(r'logic\s*(?:\[[^\]]*\]\s*)*([^;]*);', body):
    for n in re.split(r'\s*,\s*', m.group(1).strip()):
        names_sig.add(n.strip())
names_sig |= {'a','b','q','rem','qq','dif'}
def reads_of(expr):
    return {n for n in ident.findall(re.sub(r"\d+'[sS]?[bdhBDH][0-9a-fA-F_]+", ' ', expr)) if n in names_sig}
plain = []
for t, e in stmts:
    if t == 'q' and False: pass
    plain.append((t, reads_of(e)))
acr = reads_of(ac.group(1).replace('q =', ' '))
plain.append(('q', acr))
writers = {}   # signal -> list of plain idx
for k, (t, r) in enumerate(plain):
    writers.setdefault(t, []).append(k)
depth = {}
LOOPW = {'rem', 'qq', 'dif'}
def D(k):
    if k in depth: return depth[k]
    depth[k] = -1
    t, r = plain[k]
    d = 0
    for s in r:
        for w in writers.get(s, []):
            if w != k: d = max(d, D(w) + 1)
        if s in LOOPW and t not in LOOPW: d = max(d, LOOPBASE + 27) if LOOPBASE is not None else d
    depth[k] = d
    return d
# loop base = depth of rem[0] and nb12 (rem[0] writer) : two passes
LOOPBASE = None
for k in range(len(plain)): depth.clear() if False else None
# first pass without loop influence to find base = max(rank(rem[0]), rank(nb12)) + 1
LOOPBASE = None
depth.clear()
for k in range(len(plain)): D(k)
def idx(name): return [k for k,(t,_) in enumerate(plain) if t == name]
base = max(depth[k] for k in idx('rem') + idx('nb12')) 
LOOPBASE = base
depth.clear()
for k in range(len(plain)): D(k)
print("plain sites:", len(plain), " loop base:", LOOPBASE)
print("pr =", [depth[k] for k in range(len(plain))])
for k,(t,r) in enumerate(plain): print(k, t, depth[k], sorted(r))
print("fr: g_div#0,#1[i] = base+2i+1 ; g_div#2[i] = base+2i+2 with base =", LOOPBASE)
