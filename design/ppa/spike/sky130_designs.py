"""The design list of the sky130 study (WP-X1): WP-X0's 12 add/mul designs at their scoring point N = 16
(`designs.py`, reused unchanged) plus the two aes_sbox candidates of the task study (no parameter, 8-bit in/out).
`mul_n_byhand.sv` is byte-identical to `mul_n.sv` (cmp), so the five proved mul references are four sources.
"""
import os

import designs as D

SBOX_DIR = os.path.join(D.SVGOLF, "design", "tasks-week2", "aes_sbox", "reference")
CACHE = os.path.join(D.HERE, ".cache", "sky130")      # git-ignored: canonical RTLIL, netlists, Yosys logs
DATA = os.path.join(D.HERE, "data", "sky130")         # committed: small result JSON / Markdown


def all_designs(n=16, extra_n=None):
    out = []
    for d in D.designs():
        src = os.path.join(D.SVGOLF, d["src"].format(N=n))
        if not os.path.exists(src):
            continue
        out.append(dict(name=d["name"], task=d["task"], src=src, top=d["top"], params={"N": n},
                        banned=d["banned"], tag=f"{d['name']}_N{n}"))
    for name, f, top in (("sbox_bp", "sbox_bp.sv", "sbox_bp"), ("sbox_table", "sbox_table.sv", "sbox_table")):
        out.append(dict(name=name, task="sbox", src=os.path.join(SBOX_DIR, f), top=top, params={},
                        banned=False, tag=name))
    return out


def get(name, n=16):
    for d in all_designs(n):
        if d["name"] == name:
            return d
    raise KeyError(name)
