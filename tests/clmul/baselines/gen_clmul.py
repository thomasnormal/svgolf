#!/usr/bin/env python3
"""Generate carry-less multipliers for ONE width N as flat SystemVerilog (bitwise operators only): a
schoolbook design with a balanced XOR tree per output column, and Karatsuba recursions with a schoolbook
base. Each module keeps the task header (`parameter int N`) but is only correct at the width it was
generated for; it is a scoring baseline, not a proved entry.

    python3 tests/clmul/baselines/gen_clmul.py school N          > d.sv
    python3 tests/clmul/baselines/gen_clmul.py kara N BASE       > d.sv   # BASE = 1: all the way down
    python3 tests/clmul/baselines/gen_clmul.py --write           # regenerate the committed files
    python3 tests/clmul/baselines/gen_clmul.py --check           # exit 1 unless they are up to date

The committed outputs live next to this script (`OUTPUTS`); `tests/run.py` runs `--check`.

The designs (the experiment of the week-2 task study, `design/tasks-week2/experiments/clmul_gen.py`, with
the bit `p[2N-2]` as the last output instead of a constant-zero `p[2N-1]`):

* `school(a, b)`: all N^2 partial products `a[i] & b[j]`, then column k = i + j summed by a balanced tree
  of XORs (pairing neighbours level by level; an odd one out is carried up).
* `kara(a, b, base)`: with m = n // 2 (low half), hs = n - m (high half, m or m + 1 bits), the three
  products  L = aL (x) bL,  H = aH (x) bH,  M = (aL + aH) (x) (bL + bH)  (sums are XORs; an odd split pads
  the short operand with its missing bit absent), then p = L + x^m (M + L + H) + x^2m H, each column a
  balanced XOR tree of the (up to three) terms that land on it. Below `base` bits the product is `school`.

THE EMISSION ORDER IS THE CANON: ABC's result for a flat netlist depends on the order of its assigns
(tasks/aes_sbox/README.md, Findings), so the files here are the generator's output byte for byte and the
scores in tests/expected.json are for exactly that order.
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# The committed outputs: file name -> (kind, N, base).
OUTPUTS = {
    "school_tree_8.sv": ("school", 8, 0),
    "school_tree_16.sv": ("school", 16, 0),
    "school_tree_32.sv": ("school", 32, 0),
    "kara_b4_8.sv": ("kara", 8, 4),
    "kara_b4_16.sv": ("kara", 16, 4),
    "kara_b4_32.sv": ("kara", 32, 4),
    "kara_b2_16.sv": ("kara", 16, 2),
    "kara_b8_16.sv": ("kara", 16, 8),
    "kara_full_16.sv": ("kara", 16, 1),
}


class Net:
    def __init__(self):
        self.cnt = itertools.count()
        self.lines = []
        self.ands = 0
        self.xors = 0

    def new(self):
        return f"w[{next(self.cnt)}]"

    def and_(self, x, y):
        n = self.new()
        self.lines.append(f"  assign {n} = {x} & {y};")
        self.ands += 1
        return n

    def xor(self, x, y):
        n = self.new()
        self.lines.append(f"  assign {n} = {x} ^ {y};")
        self.xors += 1
        return n

    def xor_tree(self, ts):
        ts = list(ts)
        while len(ts) > 1:
            nxt = [self.xor(ts[i], ts[i + 1]) for i in range(0, len(ts) - 1, 2)]
            if len(ts) % 2:
                nxt.append(ts[-1])
            ts = nxt
        return ts[0]

    def school(self, a, b):
        n = len(a)
        cols = [[] for _ in range(2 * n - 1)]
        for i in range(n):
            for j in range(n):
                cols[i + j].append(self.and_(a[i], b[j]))
        return [self.xor_tree(c) for c in cols]

    def kara(self, a, b, base):
        n = len(a)
        if n <= base or n == 1:
            return self.school(a, b)
        m = n // 2
        hs = n - m
        aL, aH, bL, bH = a[:m], a[m:], b[:m], b[m:]
        L = self.kara(aL, bL, base)
        H = self.kara(aH, bH, base)
        aS = [self.xor(aL[i], aH[i]) if i < m else aH[i] for i in range(hs)]
        bS = [self.xor(bL[i], bH[i]) if i < m else bH[i] for i in range(hs)]
        M = self.kara(aS, bS, base)
        out = [[] for _ in range(2 * n - 1)]
        for i, t in enumerate(L):
            out[i].append(t)
            out[m + i].append(t)
        for i, t in enumerate(H):
            out[2 * m + i].append(t)
            out[m + i].append(t)
        for i, t in enumerate(M):
            out[m + i].append(t)
        return [self.xor_tree(c) for c in out]


def emit(kind, N, base):
    net = Net()
    a = [f"a[{i}]" for i in range(N)]
    b = [f"b[{i}]" for i in range(N)]
    p = net.school(a, b) if kind == "school" else net.kara(a, b, base)
    assert len(p) == 2 * N - 1
    title = ("schoolbook array with a balanced XOR tree per column" if kind == "school"
             else "Karatsuba recursion, schoolbook below " + (
                 "2 bits (all the way down)" if base == 1 else f"{base + 1} bits (base {base})"))
    out = [f"// Carry-less multiplier generated for N = {N}: {title}.",
           f"// {net.ands} AND, {net.xors} XOR before synthesis.",
           "// Scoring baseline only: correct at this N, NOT a parametric or proved entry.",
           f"module clmul_n #(parameter int N = {N}) (",
           "  input  logic [N-1:0]   a, b,",
           "  output logic [2*N-2:0] p",
           ");",
           f"  logic [{next(net.cnt) - 1}:0] w;"]
    out += net.lines
    out += [f"  assign p[{i}] = {t};" for i, t in enumerate(p)]
    out.append("endmodule")
    return "\n".join(out) + "\n", net.ands, net.xors


def render(name):
    kind, n, base = OUTPUTS[name]
    return emit(kind, n, base)[0]


def main(argv):
    if argv and argv[0] == "--write":
        for name in OUTPUTS:
            with open(os.path.join(HERE, name), "w") as fh:
                fh.write(render(name))
            print("wrote", name)
        return 0
    if argv and argv[0] == "--check":
        bad = [n for n in OUTPUTS if not os.path.isfile(os.path.join(HERE, n))
               or open(os.path.join(HERE, n)).read() != render(n)]
        extra = sorted(f for f in os.listdir(HERE) if f.endswith(".sv") and f not in OUTPUTS)
        if bad or extra:
            print("out of date:", bad, "not generated:", extra)
            return 1
        print(f"{len(OUTPUTS)} baselines up to date")
        return 0
    if len(argv) >= 2 and argv[0] in ("school", "kara"):
        kind, n = argv[0], int(argv[1])
        base = int(argv[2]) if kind == "kara" else 0
        sys.stdout.write(emit(kind, n, base)[0])
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
