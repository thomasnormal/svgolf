import sys, itertools
cnt = itertools.count()
lines = []; xors = 0; ands = 0
def new():
    return f"n{next(cnt)}"
def emit(name, expr):
    lines.append(f"  assign {name} = {expr};")
def xor(a, b):
    global xors; xors += 1
    n = new(); emit(n, f"{a} ^ {b}"); return n
def and_(a, b):
    global ands; ands += 1
    n = new(); emit(n, f"{a} & {b}"); return n
def xor_list(ts):
    # balanced tree
    ts = list(ts)
    while len(ts) > 1:
        nxt = []
        for i in range(0, len(ts) - 1, 2): nxt.append(xor(ts[i], ts[i + 1]))
        if len(ts) % 2: nxt.append(ts[-1])
        ts = nxt
    return ts[0]
def school(a, b):
    n = len(a); cols = [[] for _ in range(2 * n - 1)]
    for i in range(n):
        for j in range(n): cols[i + j].append(and_(a[i], b[j]))
    return [xor_list(c) for c in cols]
def kara(a, b, base):
    n = len(a)
    if n <= base: return school(a, b)
    m = n // 2   # assume n = 2m or handle odd: low part size m, high size n-m
    aL, aH = a[:m], a[m:]; bL, bH = b[:m], b[m:]
    # pad shorter high part (odd n): n-m >= m
    hs = n - m
    L = kara(aL, bL, base) if m > 0 else []
    H = kara(aH, bH, base)
    aS = [xor(aL[i], aH[i]) if i < m else aH[i] for i in range(hs)]
    bS = [xor(bL[i], bH[i]) if i < m else bH[i] for i in range(hs)]
    M = kara(aS, bS, base)
    # result bits: L (len 2m-1) + x^m (M^L^H) + x^2m H ; (len of M,H = 2hs-1)
    out = [[] for _ in range(2 * n - 1)]
    for i, t in enumerate(L): out[i].append(t)
    for i, t in enumerate(H): out[2 * m + i].append(t)
    for i, t in enumerate(M): out[m + i].append(t)
    for i, t in enumerate(L): out[m + i].append(t)
    for i, t in enumerate(H): out[m + i].append(t)
    return [xor_list(c) if c else "1'b0" for c in out]
def build(N, mode, base=1):
    global lines, xors, ands, cnt
    lines = []; xors = 0; ands = 0; cnt = itertools.count()
    a = [f"a[{i}]" for i in range(N)]; b = [f"b[{i}]" for i in range(N)]
    p = school(a, b) if mode == "school" else kara(a, b, base)
    decl = ", ".join(f"n{i}" for i in range(next(cnt)))
    hdr = f"module clmul(input logic [{N-1}:0] a, b, output logic [{2*N-1}:0] p);\n  logic {decl};\n"
    body = "\n".join(lines) + "\n"
    outs = "".join(f"  assign p[{i}] = {t};\n" for i, t in enumerate(p)) + f"  assign p[{2*N-1}] = 1'b0;\n"
    return hdr + body + outs + "endmodule\n", ands, xors
if __name__ == "__main__":
    N = int(sys.argv[1]); mode = sys.argv[2]; base = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    sv, a, x = build(N, mode, base)
    open(sys.argv[4], "w").write(sv)
    print(f"N={N} {mode} base={base}: AND={a} XOR={x}")
