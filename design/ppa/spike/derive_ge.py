#!/usr/bin/env python3.12
"""Derive score/ge.json from the pinned Nangate45 liberty and diff it against the committed table.

  python3.12 derive_ge.py
"""
import json, os, sys
import fetch_lib
import liberty as L

HERE = os.path.dirname(os.path.abspath(__file__))
GE_JSON = os.path.join(HERE, "..", "..", "..", "score", "ge.json")
# Yosys gate type -> (liberty cells that realise it, note)
REAL = {
    "NOT": (["INV_X1"], ""), "BUF": (["BUF_X1"], "ge.json prices BUF at 0: `abc -g` should never emit one"),
    "NAND": (["NAND2_X1"], ""), "NOR": (["NOR2_X1"], ""), "AND": (["AND2_X1"], ""), "OR": (["OR2_X1"], ""),
    "XOR": (["XOR2_X1"], ""), "XNOR": (["XNOR2_X1"], ""), "MUX": (["MUX2_X1"], ""),
    "ANDNOT": (["INV_X1", "NOR2_X1"], "A & ~B = NOR2(~A, B): no single cell; cheapest 2-cell form"),
    "ORNOT": (["INV_X1", "NAND2_X1"], "A | ~B = NAND2(~A, B): no single cell; cheapest 2-cell form"),
}

lib = L.Liberty.load(fetch_lib.lib_path())
nand = lib.cell("NAND2_X1").area
ge = {k: v for k, v in json.load(open(GE_JSON)).items() if not k.startswith("_")}
print(f"NAND2_X1 = {nand} um^2 = 1 GE\n")
print(f"{'type':7s} {'cells':20s} {'um^2':>7s} {'derived GE':>11s} {'ge.json':>8s}  note")
bad = 0
for k in sorted(REAL, key=lambda k: ge[k]):
    cells, note = REAL[k]
    a = sum(lib.cell(c).area for c in cells)
    d = a / nand
    same = abs(d - ge[k]) < 0.0006
    bad += not same
    print(f"{k:7s} {'+'.join(cells):20s} {a:7.3f} {d:11.4f} {ge[k]:8.3f}  {'' if same else 'DIFFERS: '}{note}")
print(f"\n{len(REAL) - bad} of {len(REAL)} types agree with score/ge.json to 3 decimals")
