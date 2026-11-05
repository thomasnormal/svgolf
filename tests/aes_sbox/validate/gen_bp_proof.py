#!/usr/bin/env python3.12
"""Generate (or check) `tasks/aes_sbox/reference/sbox_bp.lean`, the proof of the Boyar-Peralta reference.

    python3.12 tests/aes_sbox/validate/gen_bp_proof.py --check     # exit 1 unless the file is up to date
    python3.12 tests/aes_sbox/validate/gen_bp_proof.py --write     # rewrite it

The proof is mostly TABLES about the 113 gates of `tasks/aes_sbox/reference/sbox_bp.sv`: the gate list, the
net each environment index stands for, the rank (each gate's depth), the stable names that take the 113
equations out of `sv_equations`.
Those are generated from the netlist and substituted into the fixed text `sbox_bp.lean.tmpl` next to this
script (placeholders `@@NAME@@`); everything else, the structure proof, the lemmas and the 256-input
kernel check, is that template. Pure Python, no Lean (`tests/run.py`, step `layout`, runs `--check`).
"""

import argparse
import os
import re
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SVGOLF = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
SV = os.path.join(SVGOLF, "tasks", "aes_sbox", "reference", "sbox_bp.sv")
LEAN = os.path.join(SVGOLF, "tasks", "aes_sbox", "reference", "sbox_bp.lean")
TMPL = os.path.join(HERE, "sbox_bp.lean.tmpl")
NGATES = 113


def sig(s):
    m = re.fullmatch(r"(\w+)\[(\d+)\]", s)
    return (m.group(1), int(m.group(2))) if m else (s, 0)


def parse(path=SV):
    """The gates in source order: dict(k, lhs=(net, bit), op, a=(net, bit), b=(net, bit), depth)."""
    code = re.sub(r"//[^\n]*", "", open(path).read())
    gates, depth = [], {("x", i): 0 for i in range(8)}
    for lhs, rhs in re.findall(r"assign\s+(\S+)\s*=\s*([^;]*);", code):
        t = rhs.split()
        if len(t) == 3 and t[1] == "^":
            op = "xor"
        elif len(t) == 3 and t[1] == "&":
            op = "and"
        elif len(t) == 5 and t[1] == "^" and t[3] == "^" and t[4] == "1'b1":
            op = "xnor"
        else:
            raise ValueError(f"not a gate: {rhs!r}")
        g = dict(k=len(gates), lhs=sig(lhs), op=op, a=sig(t[0]), b=sig(t[2]))
        g["depth"] = depth[g["lhs"]] = 1 + max(depth[g["a"]], depth[g["b"]])
        gates.append(g)
    assert len(gates) == NGATES, len(gates)
    return gates


def fill(g):
    idx = {("x", i): i for i in range(8)}
    for x in g:
        idx[x["lhs"]] = 8 + x["k"]
    prog = [(x["op"], idx[x["a"]], idx[x["b"]]) for x in g]
    locs = [("x", i) for i in range(8)] + [x["lhs"] for x in g]
    ysite = {x["lhs"][1]: x["k"] for x in g if x["lhs"][0] == "y"}
    assert sorted(ysite) == list(range(8))
    ygate = [ysite[j] for j in range(8)]
    op = {"xor": ".xor", "and": ".and", "xnor": ".xnor"}
    sub = {}
    sub["PROG"] = ",\n   ".join(", ".join(f"⟨{op[o]}, {a}, {b}⟩" for o, a, b in prog[i:i + 4])
                               for i in range(0, len(prog), 4))
    sub["LOCS"] = ",\n   ".join(", ".join(f'("{n}", {b})' for n, b in locs[i:i + 6])
                                for i in range(0, len(locs), 6))
    sub["YGATE"] = ", ".join(str(k) for k in ygate)
    sub["RANK"] = ", ".join(str(x["depth"]) for x in g)

    # `sv_equations` names the equation of each gate after its target net and the ordinal (from 1, in source
    # order) of the assign among those writing that net: `eq_<net>_<k>`, and likewise `known_<net>_<k>`
    ordinal, seen = {}, {}
    for x in g:
        seen[x["lhs"][0]] = seen.get(x["lhs"][0], 0) + 1
        ordinal[x["k"]] = seen[x["lhs"][0]]

    def alias(kind, k):
        return f"{kind}_{g[k]['lhs'][0]}_{ordinal[k]}"
    names = [alias("eq", x["k"]) for x in g]
    sub["GOKNAMES"] = "\n".join("        " + " ".join(names[i:i + 6]) for i in range(0, NGATES, 6))
    sub["KNOWN4"] = alias("known", ysite[4])
    sub["HKCASES"] = "\n".join(f"        | {j}, _ => ({alias('known', ysite[j])}).2" for j in range(8))
    return sub


def build():
    text = open(TMPL).read()
    for name, val in fill(parse()).items():
        assert f"@@{name}@@" in text, name
        text = text.replace(f"@@{name}@@", val)
    assert "@@" not in text
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--check", action="store_true")
    g.add_argument("--write", action="store_true")
    args = ap.parse_args()
    text = build()
    rel = os.path.relpath(LEAN, SVGOLF)
    if args.write:
        with open(LEAN, "w") as fh:
            fh.write(text)
        print(f"gen_bp_proof: wrote {rel} ({len(text.splitlines())} lines)")
        return 0
    have = open(LEAN).read() if os.path.exists(LEAN) else None
    if have == text:
        print(f"gen_bp_proof: {rel} up to date ({len(text.splitlines())} lines)")
        return 0
    print(f"gen_bp_proof: {rel} differs from the generator's output "
          "(python3.12 tests/aes_sbox/validate/gen_bp_proof.py --write)", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
