#!/usr/bin/env python3
"""Generate a Dadda-tree multiplier for one width N as flat SystemVerilog
(bitwise operators only). The module keeps the task header (`parameter int N`)
but is only correct at the width it was generated for; it is a scoring
baseline, not a proved entry.

    python3 tests/mul/baselines/gen_dadda.py N [--final ripple|ks] > d.sv
    python3 tests/mul/baselines/gen_dadda.py --write   # regenerate the committed files
    python3 tests/mul/baselines/gen_dadda.py --check   # exit 1 unless they are up to date

The committed outputs live next to this script: `dadda_rc_<N>.sv` (ripple
final adder) and `dadda_ks_<N>.sv` (Kogge-Stone final adder) for N = 8, 16, 32
(`OUTPUTS`); `tests/run.py` runs `--check`.
"""
import contextlib
import io
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# The committed outputs: file name -> (N, final adder).
OUTPUTS = {f"dadda_{tag}_{n}.sv": (n, final)
           for tag, final in (("rc", "ripple"), ("ks", "ks")) for n in (8, 16, 32)}


def emit(N, final):
    lines = []
    wires = []
    cnt = [0]
    def new(prefix):
        cnt[0] += 1
        n = f"{prefix}{cnt[0]}"
        wires.append(n)
        return n
    W = 2 * N
    cols = [[] for _ in range(W + 1)]
    for i in range(N):
        for j in range(N):
            w = new("pp")
            lines.append(f"  assign {w} = a[{j}] & b[{i}];")
            cols[i + j].append(w)
    # Dadda heights
    d = [2]
    while d[-1] < N:
        d.append(int(d[-1] * 3 // 2))
    targets = [h for h in reversed(d) if h < max(len(c) for c in cols)]
    def fa(x, y, z):
        s, c = new("s"), new("c")
        lines.append(f"  assign {s} = {x} ^ {y} ^ {z};")
        lines.append(f"  assign {c} = ({x} & {y}) | ({z} & ({x} ^ {y}));")
        return s, c
    def ha(x, y):
        s, c = new("s"), new("c")
        lines.append(f"  assign {s} = {x} ^ {y};")
        lines.append(f"  assign {c} = {x} & {y};")
        return s, c
    for tgt in targets:
        new_cols = [[] for _ in range(W + 1)]
        carry_in = [0] * (W + 1)
        for k in range(W):
            col = list(cols[k])
            # height of this column after the stage = remaining + carries from k-1
            out = []
            # carries produced into column k by column k-1 already placed in new_cols[k]
            while len(col) + len(new_cols[k]) > tgt:
                excess = len(col) + len(new_cols[k]) - tgt
                if excess >= 2 and len(col) >= 3:
                    s, c = fa(col.pop(0), col.pop(0), col.pop(0))
                elif len(col) >= 2:
                    s, c = ha(col.pop(0), col.pop(0))
                else:
                    break
                new_cols[k].append(s)
                new_cols[k + 1].append(c)
            new_cols[k].extend(col)
        cols = new_cols
    assert all(len(c) <= 2 for c in cols), [len(c) for c in cols]
    # final two-row addition
    x = [c[0] if len(c) > 0 else "1'b0" for c in cols[:W]]
    y = [c[1] if len(c) > 1 else "1'b0" for c in cols[:W]]
    if final == "ripple":
        carry = "1'b0"
        for k in range(W):
            s = new("f")
            lines.append(f"  assign {s} = {x[k]} ^ {y[k]} ^ {carry};")
            lines.append(f"  assign p[{k}] = {s};")
            if k < W - 1:
                cn = new("fc")
                lines.append(f"  assign {cn} = ({x[k]} & {y[k]}) | ({carry} & ({x[k]} ^ {y[k]}));")
                carry = cn
    else:  # Kogge-Stone
        g = [None] * W; pr = [None] * W
        for k in range(W):
            g[k] = new("g"); pr[k] = new("q")
            lines.append(f"  assign {g[k]} = {x[k]} & {y[k]};")
            lines.append(f"  assign {pr[k]} = {x[k]} ^ {y[k]};")
        G = list(g); P = list(pr)
        dist = 1
        while dist < W:
            G2, P2 = list(G), list(P)
            for k in range(dist, W):
                ng, np_ = new("G"), new("P")
                lines.append(f"  assign {ng} = {G[k]} | ({P[k]} & {G[k - dist]});")
                lines.append(f"  assign {np_} = {P[k]} & {P[k - dist]};")
                G2[k], P2[k] = ng, np_
            G, P = G2, P2
            dist *= 2
        for k in range(W):
            cin = "1'b0" if k == 0 else G[k - 1]
            lines.append(f"  assign p[{k}] = {pr[k]} ^ {cin};")
    print(f"// Dadda-tree multiplier generated for N = {N} (final adder: {final}).")
    print("// Scoring baseline only: correct at this N, NOT a parametric or proved entry.")
    print("module mul_n #(parameter int N = %d) (" % N)
    print("  input  logic [N-1:0]   a, b,")
    print("  output logic [2*N-1:0] p")
    print(");")
    for w in wires:
        print(f"  logic {w};")
    print("\n".join(lines))
    print("endmodule")


def generate(N, final):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        emit(N, final)
    return buf.getvalue()


def main(argv):
    if argv[:1] in (["--write"], ["--check"]):
        stale = []
        for name, (n, final) in OUTPUTS.items():
            path = os.path.join(HERE, name)
            text = generate(n, final)
            if argv[0] == "--write":
                with open(path, "w") as fh:
                    fh.write(text)
            else:
                try:
                    with open(path) as fh:
                        same = fh.read() == text
                except OSError:
                    same = False
                if not same:
                    stale.append(name)
        if stale:
            print("gen_dadda: out of date (regenerate with --write): " + ", ".join(stale))
            return 1
        print(f"gen_dadda: {len(OUTPUTS)} files {'written' if argv[0] == '--write' else 'up to date'}")
        return 0
    if not argv or (len(argv) not in (1, 3)) or (len(argv) == 3 and argv[1] != "--final"):
        print(__doc__, file=sys.stderr)
        return 2
    sys.stdout.write(generate(int(argv[0]), argv[2] if len(argv) == 3 else "ripple"))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
