#!/usr/bin/env python3.12
"""Cut the 9-cell subset (INV, BUF, NAND2, NOR2, AND2, OR2, XOR2, XNOR2, MUX2; all X1) out of
the pinned Nangate45 liberty, byte for byte, so that `abc -liberty` maps onto exactly the gate
kinds of the present `abc -g` flow (minus ANDNOT/ORNOT, which have no cell). The result is a
DERIVED ARTIFACT of the pinned file (same license question as the parent); it is generated, never
vendored.

  python3.12 mklib8.py            # -> .cache/svgolf8.lib
"""
import os, re, sys
import fetch_lib

CELLS = ["INV_X1", "BUF_X1", "NAND2_X1", "NOR2_X1", "AND2_X1", "OR2_X1", "XOR2_X1", "XNOR2_X1", "MUX2_X1"]


def extract(text, name):
    m = re.search(r"^\s*cell \(" + re.escape(name) + r"\) \{", text, re.M)
    i = text.index("{", m.start())
    depth, j = 0, i
    while True:
        c = text[j]
        depth += c == "{"
        depth -= c == "}"
        j += 1
        if depth == 0:
            break
    return text[m.start():j]


def main():
    text = open(fetch_lib.lib_path()).read()
    first = re.search(r"^\s*(/\*[^*]*\*+(?:[^/*][^*]*\*+)*/\s*)?cell \(", text, re.M)
    head = text[:re.search(r"^\s*cell \(", text, re.M).start()]
    # drop the comment block that introduces the first cell, if any, from the header tail
    head = head[: head.rfind("/*")] if head.rstrip().endswith("*/") else head
    body = "\n".join(extract(text, c) for c in CELLS)
    out = os.path.join(fetch_lib.CACHE, "svgolf8.lib")
    with open(out, "w") as fh:
        fh.write(head + "\n" + body + "\n}\n")
    print(out, os.path.getsize(out), "bytes")


if __name__ == "__main__":
    main()
